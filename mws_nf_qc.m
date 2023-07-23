// Code for the Mordell-Weil sieve for a hyperelliptic curve over a number
// field.
// Mostly copied from an earlier version of magma's Mordell-Weil sieve, due to Michael Stoll.
// Some tweaks added for use with quadratic Chabauty, but not optimised.
//
// Idea: Given a set of cosets c of M*J(K) in J(K), where M>1 is a modulus,
// show that no P in C(K) maps into  c using reduction modulo primes q 
// of good reduction. I.e. show that C(k_q) misses the image of c in
// J(k_q)/MJ(k_q). 
//
// Here M = aux_int*p1^e1*...*pk^ek, where 
// - p1,...,pk are (quadratic) Chabauty primes 
// - aux_int is an auxiliary integers.
//
// The main function MWsieve works inside the abstract abelian group 
// generated by a sequence bas of independent elements of J(K).
//
// 
Attach("g2-jac.m");

function MakeInjNF(Cp, Bp)
// Construct the injection C(F_p) --> J(F_p) --> G
// given by P |--> [P - B], B = rational base point
// G is an abstract abelian group isomorphic with J(F_p)
  //Cp := BaseChange(C, Bang(Rationals(), k));
  return func<pt | Cp![(c) : c in Eltseq(pt)] - Bp>;
end function;

function my_mod(a, N)
  return Integers()!(Integers(N)!a);
end function;


// given: Abelian group G, bijective map G -> X, X some structure
// #G smooth (so that for groups of order p^f|#G, lookup is feasible)

// MakeDL(G, m)
//     m : G -> X is the map (Map), * and + defined on X

function MakeLookup1(G, m)
  return pmap<Codomain(m) -> G| [<m(g), g> : g in G]>;
end function;

function MakeDLp1(G, m, p)
  // G a p-group
  if #G le 25 then
    return MakeLookup1(G, m);
  end if;
  invs := Invariants(G);
  // printf "MakeDLp: Invariants(G) = %o\n", invs;
  pp := ExactQuotient(invs[#invs], p);
  if pp eq 1 then
    return MakeLookup1(G, m);
  end if;
  // printf "MakeDLp: pp = %o\n", pp;
  h := hom<G -> G | [pp*G.i : i in [1..#invs]]>;
  G1 := Image(h);
  // printf "MakeDLp: Invariants(Image(h)) = %o\n", Invariants(G1);
  m1 := map<G1 -> Codomain(m) | x:->m(x)>;
  f1 := MakeLookup1(G1, m1);
  G2 := Kernel(h);
  // printf "MakeDLp: Invariants(Kernel(h)) = %o\n", Invariants(G2);
  m2 := map<G2 -> Codomain(m) | x:->m(x)>;
  f2 := MakeDLp1(G2, m2, p);
  return pmap<Codomain(m) -> G |
               x :-> f2(x - m(a)) + a where a := f1(pp*x) @@ h>;
end function;

function MakeDL(G, m) 
// Given bijection  m : G -> X, where X has group structure, compute the
//  inverse of m. Assumes that #G is smooth.
  n := #Invariants(G);
  f := Factorization(#G);
  cofs := [&*[Integers()|f[i,1]^f[i,2] : i in [1..#f] | i ne j] : j in [1..#f]];
  _, refs := XGCD(cofs);
  assert &+[Integers()|refs[i]*cofs[i] : i in [1..#f]] eq 1;
  DLs := [**];
  for i := 1 to #f do
    p := f[i,1];
    hp := hom<G -> G | [cofs[i]*G.j : j in [1..n]]>;
    Gp := Image(hp);
    mp := map<Gp -> Codomain(m) | x:->m(x)>;
    DLp := MakeDLp1(Gp, mp, p);
    Append(~DLs, DLp);
  end for;
  return pmap<Codomain(m) -> G
               | x :-> &+[G|refs[i]*G!(DLs[i](cofs[i]*x)) : i in [1..#f]]>;
end function;


function MWSieve(J, sieving_primes, modulus, bas, base_pt, fake_coeffs :
  SmoothBound := 10000, satknown := {}, excluded :=
  {}, satunknown := {}, known_rat_coeffs := {},
  bool_list := [true : i in [1..#fake_coeffs]], unsat := [], printlevel := 0) 
  // Updated implementation, following 
  // https://github.com/steffenmueller/QCMod/blob/main/mws_qc.m

  bp := Seqset(BadPrimes(J)) join {p : p in excluded};
  C := Curve(J);
  assert #unsat lt 2;
  for p in sieving_primes do
    if p notin bp then
      Jp, redbas := reduceModP(J, bas, p);
      oG := #Jp;
      if Max(PrimeDivisors(oG)) lt SmoothBound then
        Cp := Curve(Jp);
        pts := Points(Cp);
        G, m := AbelianGroup(Jp);
        if printlevel gt 0 then        printf " GroupInfo: p = %o...\n", p; end if;
        I := Invariants(G);
        if printlevel gt 0 then        printf "   #C(F_p) = %o, Invariants(G) = %o\n", #pts, I; end if;
        fI := Factorization(I[#I]);
        if printlevel gt 0 then        printf  "   Exponent = %o\n", fI; end if;
        if printlevel gt 0 then        printf  "   Group Structure = %o\n", G; end if;

        scalar := #unsat eq 0 select 1 else unsat[1]^Valuation(I[#I], unsat[1]);
        if printlevel gt 1 then        printf  "   Look at %o-multiples \n", scalar; end if;

        Fp, redp := ResidueClassField(p);
        base_pt_p := Cp![redp(c) : c in Eltseq(base_pt)];
        inj := MakeInjNF(Cp, base_pt_p); 
        if printlevel gt 1 then        "make DL"; end if;
        DL := MakeDL(G, m); 
        
        if printlevel gt 1 then        "starting DL of generators"; end if;
        imbas := [DL(P) : P in redbas]; // ... @@ m
        if printlevel gt 1 then        "finished DL of generators"; end if;
        orders := [Order(g) : g in imbas];
        lcm_orders := LCM(orders);

        // We assume saturation has been checked at primes dividing the torsion order.
        // Find new primes at which saturation is known
        // (all primes q such that image of ptJ (= bas[1]) is not in q*J(F_p)).
        satknown join:= {a[1] : a in fI | imbas[1] notin a[1]*G};
        // Find primes where saturation needs to be checked
        // (all prime divisors of #J(F_p) for which saturation is not yet known).
        satunknown join:= {a[1] : a in fI};
        satunknown diff:= satknown;

        if printlevel gt 0 then        "starting DL of points on curve over F_p"; end if;
        imC := {DL(inj(pt)) : pt in pts};
        if printlevel gt 0 then        "finished DL"; end if;
        imC := {scalar*pt : pt in imC}; 
        Gsub := sub<G | imbas>;
        imC := {Gsub | pt : pt in imC | pt in Gsub};

        imbas := ChangeUniverse(imbas, Gsub);
        e1 := GCD(modulus, lcm_orders);
        if e1 lt lcm_orders then
          // throw away the part that we don't need
          Gq, qmap := quo<Gsub | [e1*g : g in Generators(Gsub)]>;
          imbas := [qmap(b) : b in imbas];
          imC := {qmap(c) : c in imC};
        end if; // e1 lt LCM(orders)
        G := Parent(imbas[1]);
        M := GCD(modulus, Exponent(G));
        assert IsOne(Exponent(G) div M);
        Cv_q := [P : P in SetToSequence(imC)];
        // If error: need scalar?
        assert &and[ &+[imbas[i]*scalar*t[i] : i in [1..#imbas]]  in Cv_q : t in known_rat_coeffs];
        old_left := #[b : b in bool_list | b];
        for i in [1..#bool_list] do
          if bool_list[i] then
            bool_list[i] := &+[imbas[j]*(scalar*fake_coeffs[i][j] mod M) : j in [1..#imbas]] in Cv_q;
          end if;
        end for;
        left := #[b : b in bool_list | b];
        if left lt old_left then 
          //printf "  %o cosets eliminated at v = %o\n", old_left - left, p; 
          printf "        %o cosets remaining after v=%o\n", left, p;
        end if;
        if not &or bool_list then
           return true, satknown, satunknown, [];
        end if; 
 
      end if; // Max(PrimeDivisors(oG)) lt SmoothBound
    end if; // IsPrime(p) and p notin bp
  end for; // p
  return false, satknown, satunknown, 
    [fake_coeffs[i] : i in [1..    #fake_coeffs] | bool_list[i]];
end function;


// Suppose that for each p=primes[i], fake_as[i,j] contains the local solutions to
// rho_p(z) = T[j] which do not appear to come from an integral point.
// integral_as[i,j] contains the local solutions to
// rho_p(z) = T[j] which do come from an integral point.
//
function coeffs_CRT(coeffs, primes, exponents)
  // TODO: Rewrite -- this is embarassingly stupid. But for now it works.
    assert #primes eq #exponents;
    assert #coeffs eq #primes;
    order_of_T := #coeffs[1];
    assert &and [#a eq order_of_T : a in coeffs];
    coeffs_mod_M := [];
    moduli := [primes[i]^exponents[i] : i in [1..#primes]];

    error if #primes gt 5, 
        "The case of %n primes is not implemented yet!", #primes;
    if #primes eq 1 then
        coeffs_mod_M := &cat coeffs[1]; 
    elif #primes eq 2 then 
        rank := #coeffs[1, 1, 1]; 
        for j := 1 to order_of_T do
            for i := 1 to #coeffs[1, j] do
                for k := 1 to #coeffs[2, j] do
                    Append(~coeffs_mod_M, [CRT([coeffs[1, j, i, l], coeffs[2, j, k, l]], 
                                moduli) : l in [1..rank]]);
                end for;
            end for;
        end for;
    elif #primes eq 3 then 
        rank := #coeffs[1, 1, 1]; 
        for j := 1 to order_of_T do
            for i := 1 to #coeffs[1, j] do
                for k := 1 to #coeffs[2, j] do
                    for m := 1 to #coeffs[3, j] do
                        Append(~coeffs_mod_M, [CRT([coeffs[1, j, i, l], coeffs[2, j, k, l], 
                                    coeffs[3, j, m, l]], moduli) : l in [1..rank]]);
                    end for;
                end for;
            end for;
        end for;
    elif #primes eq 4 then 
        rank := #coeffs[1, 1, 1]; 
        for j := 1 to order_of_T do
            for i := 1 to #coeffs[1, j] do
                for k := 1 to #coeffs[2, j] do
                    for m := 1 to #coeffs[3, j] do
                      for n := 1 to #coeffs[4, j] do
                          Append(~coeffs_mod_M, [CRT([coeffs[1, j, i, l], coeffs[2, j, k, l], 
                                      coeffs[3, j, m, l], coeffs[4, j, n, l]], moduli) : l in [1..rank]]);
                      end for;
                    end for;
                end for;
            end for;
        end for;
    elif #primes eq 5 then 
        rank := #coeffs[1, 1, 1]; 
        for j := 1 to order_of_T do
            for i := 1 to #coeffs[1, j] do
                for k := 1 to #coeffs[2, j] do
                    for m := 1 to #coeffs[3, j] do
                      for n := 1 to #coeffs[4, j] do
                        for o := 1 to #coeffs[4, j] do
                          Append(~coeffs_mod_M, [CRT([coeffs[1, j, i, l], coeffs[2, j, k, l], 
                                      coeffs[3, j, m, l], coeffs[4, j, n, l], coeffs[5, j, o, l]], moduli) : l in [1..rank]]);
                        end for;
                      end for;
                    end for;
                end for;
            end for;
        end for;
    end if;
    return coeffs_mod_M;
end function;

function all_coeffs(N, g)
    // return all lists a = [a_1,...,a_g], where a_i = 0,...,N-1
    coeffs := [[j] : j in [0..N-1]];
    for i := 1 to g-1 do
        old_coeffs := coeffs;
        coeffs := [];
        for a in old_coeffs do
            for j := 0 to N-1 do
                Append(~coeffs, a cat [j]);
            end for;
        end for;
    end for;
    return coeffs;
end function;



function combine_fake_good(fake_coeffs_mod_M, M, N)
    // fake_as_mod_M contains all solutions mod M.
    // N is a prime power for which we have no information where 
    // the rational points could lie.
    as := [];
    rank := #fake_coeffs_mod_M[1];
    as_mod_N := all_coeffs(N, rank);
    for i in [1..#fake_coeffs_mod_M] do
        for j in [1..#as_mod_N] do
            Append(~as, [CRT([fake_coeffs_mod_M[i,l], as_mod_N[j,l]], 
                        [M, N]) : l in [1..rank]]);
        end for;
    end for;
    return as;
end function;




function orders(J, lower_bound, upper_bound)
    disc := Integers()!Discriminant(Curve(J));
    good_primes := [v : v in PrimesInInterval(lower_bound, upper_bound) |
                           not IsDivisibleBy(disc, v)]; 
    return good_primes, [Order(BaseChange(J, GF(v))) : v in good_primes];
end function;

function spnf(M, good_primes, groups, bound)
    s_primes := [];
    quots := [];
    for i := 1 to #good_primes do
        v := good_primes[i];
        A := groups[i];
        approx_number_pts := #ResidueClassField(v) + 1;
        if GCD(M, #A) ne 1 then
          MA := sub<A | [M*g : g in Generators(A)]>;
          QA := A/MA;
          if approx_number_pts lt #QA*bound then 
         //    <v, FactoredOrder(A)>;
            Append(~s_primes, v);
            Append(~quots, (#ResidueClassField(v)+1.)/#QA );
          end if;
        end if;
    end for;
    // now sort according to quotient
    //ParallelSort(~quotients, ~s_primes);
    return s_primes, quots;
end function;


function orders(C, bd, good_primes)
  // C is a hyperelliptic curve defined over a number field K, bd is a positive real bound
  // good_primes contains primes which we'd like to divide the orders.
  // return good_orders and primes_and_orders, where primes_and orders contains
  // all primes v of K dividing a prime at most bd and, for all such primes, the order of 
  // J(F_v), where J is the Jacobian of C and F_v is the residue field at v.
  // good_orders contains all non-trivial GCDs of the elements of good_primes
  // with any of these orders.
  // TODO: general curves -- don't use discriminant.
  primes := PrimesInInterval(2, bd);
  disc := Discriminant(C);
  K := BaseRing(C);
  O := Integers(K);
  primes_and_orders := [];
  good_orders := [];
  for p in primes do
    dec :=  Decomposition(O, p);
    for pair in dec do
      if disc notin pair[1] then // want good reduction
        q := pair[1];
        k, pi := ResidueClassField(q);
        Ck := ChangeRing(C, k);
        Jk := Jacobian(Ck);
        ord := Order(Jk); 
        Append(~primes_and_orders, <q, ord>);
        if &or[GCD(ord, v) gt 1 : v in good_primes] then
          Append(~good_orders, <q, Factorisation(GCD(ord, &*good_primes))>);
        end if;
      end if;
    end for;    
  end for;    
  return good_orders, primes_and_orders;
end function;

function good_primes(C, bd)
  primes := PrimesInInterval(2, bd);
  disc := Discriminant(C);
  K := BaseRing(C);
  O := Integers(K);
  g_p := [];
  for p in primes do
    dec :=  Decomposition(O, p);
    for pair in dec do
      if disc notin pair[1] then // want good reduction
        Append(~g_p, pair[1]);
      end if;
    end for;
  end for;
  return g_p;
end function;



function torsion_bound(J, bd)
  C := Curve(J);
  g_p := good_primes(C, bd);
  ord := #BaseChange(J, ResidueClassField(g_p[1]));
  for p in g_p do
    ord_p := #BaseChange(J, ResidueClassField(p));
    ord := GCD(ord, ord_p);
    if IsOne(ord) then return 1; end if;
  end for;
  return ord;
end function;
  
  
function is_saturated_at_p(bas, torsion_bas, torsion_orders, p)
  A := AbelianGroup([0 : b in bas] cat torsion_orders);
  bool := isSaturatedAtp(A, bas cat torsion_bas, p);
  return bool;
end function;


