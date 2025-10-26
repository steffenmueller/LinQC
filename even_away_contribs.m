// This is code for computing the possible contributions away from p for even degree 
// hyperelliptic curves of the form
//   h_q(inf1 - inf2 , P - Q), P, Q integral, 
//       or of the form
//   h_q(inf1 - inf2 , P - int_pt), P integral and int_pt fixed and
//   integral.
//

function pseudoinverse(A)
  //A must be square  
  k := Nrows(A);
  K := FieldOfFractions(BaseRing(A));
  S := Matrix(K, k, [K ! (1 / k) : i in [1..k^2]]);
  return (A + S)^(-1) - S;
end function;

function my_change_ring(f, q)
  assert &and[IsIntegral(c) : c in Coefficients(f)];
  k, pi := ResidueClassField(q);
  O := Domain(pi);
  kt<t> := PolynomialRing(k);
  fk := kt!0;
  for i := 0  to Degree(f) do
    fk +:= pi(O!Coefficient(f, i))*t^i;
  end for;
  return fk;
end function;



function away_contribs(C : int_pt := 0, primes := [])
  // C is a hyperelliptic curve given as y^2 = f(x).
  // int_pt is an optional integral point on C
  //
  //
//  Compute pairs <v, (P-P_0, infty- - infty_+)_v>, where 
//  - P runs through the integral points;
//  - P_0 is int_pt (if given); else P_0 runs through all integral points
//  - v runs through all finite primes s.t (P-P_0, infty- - infty_+)_v
//    can be nonzero.
//  - (P-P_0, infty- - infty_+)_v is a rational number s.t. 
//    the local height h_v(P-P_0, infty- - infty_+)_v at v is 
//      (P-P_0, infty- - infty_+)_v * chi_v(pi_v),
//    where pi_v is a uniformizer and chi_v is the local component of the
//    idele class character in the definition of the global height.

  g := Genus(C);
  f, h := HyperellipticPolynomials(C);
  assert IsZero(h);
  lcf := LeadingCoefficient(f);
  K := BaseRing(C);
  assert Type(K) in [FldRat, FldNum, FldQuad]; 
  if not IsSquare(lcf) then
    K<s> := ext<Rationals() | Polynomial([-lcf,0,1])>;
  end if;
  C := ChangeRing(C, K);
  inf_pts := PointsAtInfinity(C);
  assert #inf_pts eq 2;
  O1, O2 := Explode([inf_pts[1], inf_pts[2]]);
  if Integers()!O1[2] gt 0 then // swap
    O := O2; O2 := O1; O1 := O;
  end if;
  int_pt_given := Type(int_pt) eq PtHyp select true else false;

  nf := K ne Rationals();  
  OK := Integers(K);
  disc := OK!(2*Discriminant(C)); 
  if nf then
    sing := Support(disc * OK);
    divs_lcf := Support(lcf*OK);
  else 
    sing := PrimeDivisors(disc);
    divs_lcf := PrimeDivisors(Integers()!lcf);
  end if;
  bad_primes := [q: q in sing| Valuation(disc, q) gt 1];  
  // if v_q(disc) = 1, then the contribution at q is trivial.
  very_bad_primes := [q: q in divs_lcf | Valuation(lcf, q) gt 1];  
  for q in bad_primes do
    if IsEven(Norm(q)) or IsSquare(my_change_ring(f, q)) then 
      // Added primes above 2 -- jsm, 26/20/25
      Append(~very_bad_primes, q);
    end if;
  end for; 
  very_bad_primes := SetToSequence(SequenceToSet(very_bad_primes));
  if #primes gt 0 then
    // Only take primes above these given ones into account.
    very_bad_primes := [q : q in very_bad_primes | 
          &or[IsDivisibleBy(Norm(q), p) : p in primes]];
  end if;
  contribs := [];
  for q in very_bad_primes do
    model := RegularModel(C, q);
    M := ChangeRing(IntersectionMatrix(model), Rationals());
    r := Nrows(M); 
    if r gt 1 then  // else trivial
      // Find out which component O1 and O2 map to
      
      inf_comp1 := Index(model`regular_fibres_indices, 
      [PointOnRegularModel(model, (model`C)!Eltseq(O1))`component_indices]);
      inf_comp2 := Index(model`regular_fibres_indices, 
      [PointOnRegularModel(model, (model`C)!Eltseq(O2))`component_indices]);
      if inf_comp1 ne inf_comp2 then  // else trivial
        cpts := Components(model);
        mults := Multiplicities(model);
        N := pseudoinverse(M);
        // list all possible intersection vectors arising from horizontal divisors of
        // degree 1 
        mult1_cpts := [i : i in [1..Nrows(M)] | mults[i] eq 1];        
        zero_seq := [0 : i in [1..r]];
        inf_seq := zero_seq;  inf_seq[inf_comp1] +:= 1; inf_seq[inf_comp2] -:= 1; 
        inf_vec := Matrix(Rationals(), 1, inf_seq);  
        // This is the vector of intersections between O1 - O2 and the irred. component
        q_contribs := [];
        if int_pt_given then
            int_pt_comp := Index(model`regular_fibres_indices, 
                            [PointOnRegularModel(model, 
                              (model`C)!Eltseq(int_pt))`component_indices]);
        end if;

        for i in mult1_cpts do
          v_seq := zero_seq;
          v_seq[i] +:= 1; 
          if int_pt_given then
            v_seq[int_pt_comp] -:= 1;
            v_vec := Matrix(Rationals(), 1, v_seq);
            Include(~q_contribs, (Transpose(inf_vec)*N*v_vec)[1,1]);
          else  // TODO: Find action of hyp inv to cut down this number
            for j in mult1_cpts do
              if i ne j then  // else trivial
                v_seq[j] -:= 1;
                v_vec := Matrix(Rationals(), 1, v_seq);
                Include(~q_contribs, (Transpose(inf_vec)*N*v_vec)[1,1]);
              end if;
            end for;
          end if; // int_pt_given
        end for; // i in mult1_cpts
        if q_contribs[2] ne 0 then
          Append(~contribs, <q, q_contribs>);
        end if;
      end if; // inf_comp1 ne inf_comp2 
    end if; // r gt 1
  end for; // q in very_bad_primes
  return contribs;
end function;    


