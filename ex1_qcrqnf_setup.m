
load "qc_init_nf.m";

d := 7; K<w> := QuadraticField(d);
PK<t> := PolynomialRing(K);
SetClassGroupBounds("GRH");
f := t^6 + t^5 - w*t^4 + (-w + 1)*t^3 + t^2 + w*t + w;

C := HyperellipticCurve(f);
J := Jacobian(C);

// Uncomment the following to see that p=3 is a promising QC prime
// and that we only need the coset coefficients modulo p^5
// qc_primes, groups, g_p, prime_quality, mws_primes, prime_exponents :=
//    find_qc_primes(C : qc_primes_bound := 100, mws_primes_bound := 2500, 
//                       groups := [], printlevel := 1, mws_quot_bd := 2); 

// Linear combination of result of pseudoBasis, precomputed.
// Has the property that multiples of these points can be used for
// height computations, i.e. the canonical representatives are "good".
//
bas := [elt<J|[t-1, t^3-3], 2>, elt<J| [t^2-1, t+1], 2>, 
        elt<J | [t^2 + 1/81*(43*w + 125)*t + 1/567*(197*w + 28), 
        1/45927*(40337*w + 121513)*t + 1/45927*(23797*w + 85001)], 2>];

// These are independent mod torsion
assert independentModTorsion(bas);

// Find input for Sage code to compute local heights at p
// and compute local heights away from p.
Ds_sage, can_x, away_hts, multiples, contribs, integral_pts, ptsC 
  := make_sage_input(C, 3 : name := "ex1p3", prec := 10, 
        final_prec := 5, bas := bas); 

