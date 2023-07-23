Attach("g2-jac.m");
load "JSearch.m";
load "even_away_contribs.m";

load "mws_nf_qc.m";  // Mordell-Weil sieve implementation




PR<x> := PolynomialRing(RationalField());

function MakeIsZero(R)
  if (Type(R) eq RngSerLaur) then
    if ((R!1) - (R!1) eq 0) then
      return func< z | z eq 0 or RelativePrecision(z) eq 0 >;
    else
      return func< z | z eq 0 or Valuation(z) ge prec > 
                                    where prec := AbsolutePrecision(R!1);
    end if;
  elif Type(R) eq FldPad then
    return func< z | IsWeaklyZero(z)>;
  else
    return func< z | z eq R!0 >;
  end if;
end function;

function number_of_non_unit_roots(f)
// f is a p-adic polynomial in 1 variable with integral coeffs
// Find the number of non-unit roots of f, including roots over 
// extension fields.
    count := 0; // count contains the number of non-unit roots
    fact := Factorisation(f);
    for t in fact do
        if Valuation(ConstantCoefficient(t[1])) gt 0 then 
            // else disregard t
            if Degree(t[1]) eq 1 then 
                // linear factor with non-unit root
                count +:= t[2];
            else
                n := Degree(t[1]);
                A := AllExtensions(BaseRing(f), n);
                done := false;
                i := 1;
                while not done do
                    assert i le #A;
                    K := A[i];
                    fK := ChangeRing(t[1], K);
                    if not IsIrreducible(fK) then
                        //fK splits, recurse
                        count +:= t[2]*number_of_non_unit_roots(fK);
                        done := true;
                    end if;
                    i +:=1;
                end while;
            end if;
        end if;
    end for;
    return count;
end function;




function is_good_split_ordinary(C, p)
// C is a hyperelliptic curve over a number field, p is a prime
// Check if C is good and ordinary at all primes above p
//
// This is really stupid and slow, but it works
// TODO: Replace!
    F := BaseRing(C);
    g := Genus(C);
    fact := Factorisation(p*Integers(F));
    if Degree(F) ne #fact then return false; end if;
    f, h := HyperellipticPolynomials(C);
    assert h eq 0;
    prec := 30;
    for p in [t[1] : t in fact] do
      if Valuation(Discriminant(C), p) ne 0 then
          // C has bad reduction at p
          return false;
      end if;
      k, phi := ResidueClassField(p);
      fp := Polynomial(k, [phi(c) : c in Coefficients(f)]);
      Cp := HyperellipticCurve(fp);
      pol := ReciprocalPolynomial(Numerator(ZetaFunction(Cp)));
      // pol is the characteristic poly of Frobenius
      try 
        K := pAdicField(p, prec);
      // now lift pol to K
        pol_lifted := ChangeRing(pol, K);
      // C is ordinary iff half of the roots of the char poly of Frobenius
      // are units.
        if number_of_non_unit_roots(pol_lifted) ne g then
          return false;
        end if;
      catch e;
        prec +:= 10; 
      end try;
    end for;
    return true;
end function;
    

function find_qc_primes(C : qc_primes_bound := 100, mws_primes_bound := 1000, ordinary := true, groups := [], printlevel := 0, mws_quot_bd := 10); 
  // C is a genus 2 curve over a number field
  // Find good primes for quadratic Chabauty / Mordell-Weil sieve combination
  //
  // * ordinary: if true, only allow ordinary primes for qc 
  // * mws_quot_bd controls the allowed quality of the mws-primes, 
  // i.e. the probability
  //   that we'll get nontrivial information from them
  //
  assert Genus(C) eq 2;
  f,h := HyperellipticPolynomials(C);
  assert IsZero(h);
  J := Jacobian(C);
  
  qc_primes := [p : p in PrimesInInterval(1, qc_primes_bound) 
                                | is_good_split_ordinary(C, p)];
  g_p := good_primes(C, mws_primes_bound);
  if #groups eq 0 then
    for q in g_p do
      kq, piq := ResidueClassField(q);
      fq := Polynomial([piq(c) : c in Coefficients(f)]);
      Append(~groups, AbelianGroup(Jacobian(HyperellipticCurve(fq))));
    end for;
  end if;
  mws_primes := []; 
  prime_quality := []; 
  for p in qc_primes do
    if printlevel gt 0 then "p", p; end if;
    mws_primes_p, quots := spnf(p^10, g_p, groups, mws_quot_bd);
    Append(~mws_primes, mws_primes_p);
    Append(~prime_quality, quots);
  end for;

  // TODO: Sort in a more meaningful way. 
  //ParallelSort(~prime_quality, ~qc_primes);
  prime_exponents := [Max([Valuation(Exponent(G), p) : G in groups]) : p in qc_primes];
    
  return qc_primes, groups, g_p, prime_quality, mws_primes, prime_exponents;
end function;



function rationalize(D)
  rat_div := [ChangeUniverse(Eltseq(P), Rationals()) : P in D];
  return [[P[1], P[2]] : P in rat_div];
end function;


function splits_over_Qp(f, Qp)
  fact := Factorisation(ChangeRing(f, Qp));
  if #fact eq 0 then return false; end if;
  return &+[t[2] : t in fact] eq Degree(f);
end function;


function is_pointwise_Qp_rational(P, completion_maps)
  // P is a point on J
  // for now assume all pts in L are affine.
  // potential problem for g=3, deg=8
  P_lists := [];
  for i in [1..#completion_maps] do
    // For each prime of K over p, check
    // if the canonical divisor rep splits over the completion
    phi := completion_maps[i];  
    K := Codomain(phi);
    a := Polynomial(K, [phi(c) : c in Coefficients(P[1])]);
    fact := Factorisation(a);
    if #fact eq 0 or &+[t[2] : t in fact] ne Degree(a) then
      return false, _;
    end if;
    roots := Roots(a);
    P_list := [];
    for t in roots do
      xx := t[1];
      b := Polynomial(K, [phi(c) : c in Coefficients(P[2])]);
      yy := Evaluate(b, xx);
      P_list cat:= [[xx, yy] : i in [1..t[2]]];
    end for;
    Append(~P_lists, P_list);
  end for;
  return true, P_lists;
end function;


function bch(A,p)
// Series representation of p-adic number, suitable for Sage input
    //if Valuation(A) gt 10 then A; end if;    
  if IsWeaklyZero(A) then
    S:= "O(";
    S:=S cat IntegerToString(p);
    S:=S cat "^";
    S:=S cat IntegerToString(Precision(Parent(A)));
    S:=S cat ")";
    return S;
  end if;

  v:=Valuation(A);//	if v lt 0 then
  a:=Integers()!(A*p^(-v));//	end if;
  if a lt 0 then
    a+:=p^AbsolutePrecision(A);
  end if;
  b0:=a mod p;
  i:=1;
  bb0:=a;
  L:=[b0];//	b:=(Parent(x)!b0)*x^v;
  while p^i-1 lt Abs(a) do
    bb1:=(bb0-b0) div p;
    b1:= bb1 mod p;
    b0:=b1;
    bb0:=bb1;
    Append(~L,b0);//		b+:=b0*x^(i+v);
    i+:=1;
  end while;
  S:="";
  for i:=1 to #L do
    if L[i] ne 0 then
    S:= S cat IntegerToString(L[i]);
    if i+v-1 ne 0 then
    S:= S cat "*";
    S:= S cat IntegerToString(p);
    S:=S cat "^";
    S:=S cat IntegerToString(i+v-1);
    end if;
    S:=S cat " + ";
    end if;
  end for;
  S:=S cat "O(";
  S:=S cat IntegerToString(p);
  S:=S cat "^";
  S:=S cat IntegerToString(RelativePrecision(A));
  S:=S cat ")";
  return S; 
end function;



function sage_padic_points(D, curve_name)
  // D is a sequence of p-adic points on a hyperelliptic curve C
  // return the points in D in series representation, 
  // suitable for input into Sage.
  p := Prime(Parent(D[1,1]));
  series_list := "[";
  series_list := []; 
  lp := []; 
  for i in [1..#D] do
    Append(~series_list, curve_name cat "( " cat bch(D[i,1], p) 
                              cat " , " cat bch(D[i,2], p) cat " )") ;
  end for;
  //series_list := Prune(Prune(series_list)) cat "]\n";
  return series_list;
end function;


function has_good_multiple_rep(P, p :  N := 10, multiple_bound := 10, 
                                                      curve_names := ["C"])
// - P is a point in J(K), where J is the Jacobian of a genus 2 curve C over
// a number field K, given by a monic sextic model.
// - p is a prime of good reduction, split in K: p*OK = p_1*p_2
//
// Computes a multiple n*P such that n*P is represented by a reduced divisor
// D - D_lambda, s.t. 
// - D>=0, D=P1+P2 splits over Qp;
// - D_lambda = div_0(x-lambda) splits over Qp;
// - we can use our code to compute h_p(D-D_lambda, infty- - infty+).
//
// Returns:
// - bool: true iff there is a suitable n<=multiple_bound
// - n*P
// - [P1, P2]
// - lambda
// - [P1,P2] as strings, suitable for Sage input
// - [f1,f2] as strings, suitable for Sage input, where C/K_{p_i}: y^2=fi)
// - the sum of local heights h_v(D-D_lambda, infty- - infty+) away from p
// - n
//
// Optional parameters:      
// - N is the working p-adic precision
// - curve_names: String used for Sage input

  J := Parent(P);
  C := Curve(J);
  f,h := HyperellipticPolynomials(C);
  assert h eq 0;
  assert Degree(f) eq 6; // TODO: Generalize
  assert Coefficient(f, 6) eq 1;                      
  assert &and[IsIntegral(c) : c in Coefficients(f)];

  K := BaseRing(C);
  Qp := pAdicField(p, N);
  g := Genus(C);
  completion_maps := [**]; // maps to Qp
  completed_curves := [];
  factorpK := Factorisation(p*Integers(K));
  assert #factorpK eq 2;
  for factor in factorpK do
    k, pi := ResidueClassField(factor[1]);
    Kp, phi := Completion(K, factor[1]);
    Kp`DefaultPrecision := N;
    fcomp := Polynomial(Kp, [phi(c) : c in Coefficients(f)]);
    Append(~completion_maps, phi);
    Ccomp := HyperellipticCurve(fcomp);
    Append(~completed_curves, Ccomp);
  end for;

  // First find all good possible lambdas for this prime.
  good_lambdas := [];
  pi_lift := Inverse(pi);
  lifts := [K!pi_lift(a) : a in k];
  for lambda in lifts do
    // need lambda <> 0 because of transformation below.
    if not IsZero(lambda) and not IsZero(Evaluate(f, lambda)) then 
      if &and[IsSquare(Evaluate(Polynomial(Codomain(phi), 
                  [phi(c) : c in Coefficients(f)]), phi(lambda)))
                          : phi in completion_maps] then
        Append(~good_lambdas, lambda);
      end if;
    end if;
  end for;
  error if #good_lambdas lt 1, "No good lambda for this prime";
  lambda := good_lambdas[1];

  inf_pts := PointsAtInfinity(C);
  // Make sure that we take inf pts in the right order.
  assert inf_pts[1,2] eq -1;
  inf := inf_pts[1] - inf_pts[2];
  

  for n in [1..multiple_bound] do
    Q := n*P;
    // check if pointwise K_q-rational for all q above p
    try
      bool, DQs := is_pointwise_Qp_rational(Q, completion_maps);
      if bool then
        // check if support not in infinite disks over both K_pi
        a := Q[1];
        b := Q[2];
        if Degree(a) eq g and &and [Denominator(Norm(c)) mod p ne 0 
                          : c in Coefficients(a) cat Coefficients(b)] then
          // Local (cyclotomic!) heights away from p
          intersections := 0;
          away_heights := 0;
          //try 
          //  ints := LocalIntersectionData(Q, inf : lambda := lambda, mu := 0);
          //catch e;
            // Move to affine piece Z=1 to avoid issue in int_wih_spec_fib
          D, trans := Transformation(C, [0,1,1,0]);
          inftrans := Evaluate(trans, inf);
          Qtrans := Evaluate(trans, Q);
          ints := LocalIntersectionData(inftrans, Qtrans : 
                                          lambda := 0, mu := 1/lambda);
          assert &and[IsOne(t[3]) : t in ints]; 
          intersections := [<t[1], t[2]> : t in ints | not 
                                IsDivisibleBy(Norm(t[1]), p) and t[2] ne 0];
          if #intersections ne 0 then 
            // TODO: generalize this for non-cycl. heights. 
            away_heights := &+[Qp!(t[2])*Log(Qp!Norm(t[1])) 
                                                    : t in intersections];
          end if;

          fs_sage := [];
          for k in [1..#completion_maps] do
            fk := HyperellipticPolynomials(completed_curves[k]);
            fk_string := "0";
            for i := 0 to Degree(fk) do
              if not IsWeaklyZero(Coefficient(fk,i)) then
                ithterm := bch(Coefficient(fk,i), p) ;
                if i gt 0 then
                  ithterm := " + (" cat ithterm cat ")*x^"
                        cat IntegerToString(i);
                end if;
                fk_string cat:= ithterm;
              end if;
            end for;
            Append(~fs_sage, fk_string);
          end for;
          
          DQ_sage := [sage_padic_points(DQs[i], curve_names[i]) 
                                                    : i in [1..#DQs]];
     
          return true, Q, DQs, lambda, DQ_sage, fs_sage, away_heights, n;
        end if; // Degree(a) eq g ...
      end if; // bool
    catch e;
      continue;
    end try;
  end for;
  return false, _, _,_, _, _, _,_;
end function;

function make_sage_input(C, p : name := "", bas := [], prec := 10, final_prec := prec, multiple_bound := 8)
// - C is a genus 2 curve over a number field K, given by a monic sextic 
//   model such that J=Jac(C) has rank 3 over K
// - p is a prime of good reduction, split in K: p*OK = p_1*p_2
//
// Computes the following data for QC+MWS:
// - Ds_sage: sequence of [P1,P2] (see doc for has_good_muliple_rep) for
//   each member of bas.
// - can_x: lambda (see doc for has_good_muliple_rep)
// - away_hts: sum_v h_v(D-D_lambda, infty- - infty+) of local heights 
//   away from p, for each member of bas, where D and D_lambda are as in
//   the doc for has_good_multiple_rep.
// - vals: all possible values of sum_{v}h_v(P-P_0, infty- - infty_+),
//   where P is an integral point, P_0 is  chosen integral base point (here
//   integral_pts[1]) and the sum is over all primes v away from p.
// - integral_pts: all integral points in C(K) of height <= 100.
// - ptsC: all rational points on C of height <= 100.
//
// More importantly, this data is written to a .sage file in sage format.
//
// Optional parameters:      
// - name: String used for Sage input
// - bas is a sequence of generators of a finite index subgroup of J(K)
// - prec is the working p-adic precision
// - final_prec is the desired p-adic precision of the coefficients of the
//   `extra` QC roots in terms of bas
// - multiple_bound is the largest allowed multiple in has_good_multiple_rep
// - the sum of all local heights h_v(D-D_lambda, infty- - infty+) away from p

  J := Jacobian(C);
  f,h := HyperellipticPolynomials(C);
  K := BaseRing(C);
  assert h eq 0;
  assert Degree(f) eq 6; // TODO: Generalize
  assert Coefficient(f, 6) eq 1;                      
  assert &and[IsIntegral(c) : c in Coefficients(f)];

  assert #Factorisation(p*Integers(K)) eq 2;
  if #bas eq 0 then 
    bas, bastors, fun, ptsC := pseudoBasis(J);
  end if;
    
  assert independentModTorsion(bas) and #bas eq 3;

  ptsC := Points(C:Bound:=100);
  integral_pts := [P : P in ptsC | P[3] eq 1 and 
                      IsIntegral(P[1]) and IsIntegral(P[2])];

  Ds_sage := [];
  away_hts := [];
  Ds := [];
  multiples := [];
  for P in bas do
    bool, Q, DQs, lambda, DQs_sage, fs_sage, away_height, n 
      := has_good_multiple_rep(P, p : multiple_bound := multiple_bound, 
                                N := prec, curve_names := ["Cp1", "Cp2"]); 
    assert bool;
    Append(~Ds_sage, DQs_sage);
    Append(~away_hts, away_height);
    Append(~Ds, DQs);
    Append(~multiples, n);
  end for;
  base_pt := integral_pts[1];
  contribs := away_contribs(C : int_pt := base_pt);
  assert #contribs le 1;
  Qp := pAdicField(p, prec);
  if #contribs eq 0 then
    vals := [Qp!0];
  else
    vals := [t*Log(Qp!Norm(contribs[1,1])) : t in contribs[1,2]];
  end if;

  file := "input" cat name cat ".sage";
  Write(file, "d =" cat Sprint(Basis(BaseRing(C))[2]^2): Overwrite := true);
  Write(file, "p =" cat Sprint(p));
  Write(file, "prec =" cat Sprint(prec));
  Write(file, "K.<w> = QuadraticField(d)");
  Write(file, "Kt.<t> = K['t']");
  Write(file, "f =" cat Sprint(f));
  Write(file, "C =  HyperellipticCurve(f)");
  Write(file, "Q_p = pAdicField(p,prec)");
  Write(file, "Qpx.<x> = Q_p['x']");
  Write(file, "Cp1 =  HyperellipticCurve(" cat Sprint(fs_sage[1]) cat ")");
  Write(file, "Cp2 =  HyperellipticCurve(" cat Sprint(fs_sage[2]) cat ")");
  Write(file, "generators =" cat Sprint(Ds_sage));
  Write(file, "away_hts_generators =" cat Sprint(away_hts));
  Write(file, "can_x =" cat Sprint(lambda));
  Write(file, "final_prec =" cat Sprint(final_prec));
  Write(file, "vals =" cat Sprint(vals));
  Write(file, Sprintf("base_change_matrix = diagonal_matrix(%o)^(-1)", 
                                                                multiples));
  N := #integral_pts;
  Write(file, "\nintegral_pts = [");
  for i in [1..N-1] do
    Write(file, "C(" cat Sprint(integral_pts[i,1]) cat "," 
                                    cat Sprint(integral_pts[i,2]) cat "),");
  end for;
  Write(file, "C(" cat Sprint(integral_pts[N,1]) cat "," 
                                    cat Sprint(integral_pts[N,2]) cat ")]");
  return Ds_sage, lambda, away_hts, multiples, vals, integral_pts, ptsC;
end function; 

