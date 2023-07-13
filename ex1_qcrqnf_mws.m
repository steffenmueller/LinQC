load "qc_init_nf.m";
load "ex1_qcrqnf_setup.m";

//primes := [qc_primes[1]];
//exponents := [prime_exponents[1]];
primes := [3];
exponents := [5];
// MWS modulus 
M := &*[primes[i]^exponents[i] : i in [1..#primes]];  
torsion_bas := []; // computed earlier
base_pt := integral_pts[1];
rat_coeffs := [];
// find coeffs of known rational points in terms of bas.
// (change bound "2" for other examples or do sth. smarter)
for P in ptsC do
  for i,j,k in [-2..2] do 
    if i*bas[1]+j*bas[2]+k*bas[3] eq P -base_pt then 
      Append(~rat_coeffs, [i,j,k]); 
    end if; 
  end for;
end for;
assert #rat_coeffs eq #ptsC;

load "coeffsex1p3.m";
rat_coeffs_modpN := [ChangeUniverse(tuple, Integers(M)) 
                                    : tuple in rat_coeffs];
// sanity check: coeffs of integral points computed using abelian logs
// are among rat_coeffs.
assert &and[ChangeUniverse(tuple, Integers(M)) in rat_coeffs_modpN 
                                    : tuple in int_coeffs[1,1]];


time qc_fake_coeffs_mod_M := coeffs_CRT(fake_coeffs, primes, exponents);
"number of cosets", #qc_fake_coeffs_mod_M;
aux_int := 2;
printf "adding information modulo %o\n", aux_int;
time fake_coeffs_mod_M := combine_fake_good(qc_fake_coeffs_mod_M, M, aux_int);
M *:= aux_int; // modulus
"number of cosets", #fake_coeffs_mod_M;
O<u> := Integers(K);
sieving_primes := [ ideal<O | gens> : 
                gens in [[2017, u+845], [37, u+28], [29, u+6]]];

done, sat_known, sat_unknown := MWSieve(J, sieving_primes, 
     M, bas, base_pt, fake_coeffs_mod_M : known_rat_coeffs := rat_coeffs);

// check if done and saturated
assert done and &and[is_saturated_at_p(bas, [], [], v) : v in sat_unknown];
"This proves that the points on", C, "defined over the ring of integers of", K, "are precisely", integral_pts;

// Uncomment the following for more generic (but longer) MWS run, 
// where we don't know the sieving primes in advance.
// Requires earlier run of find_qc_primes
//
/*
"generating cosets";
time qc_fake_coeffs_mod_M := coeffs_CRT(fake_coeffs, primes, exponents);
"number of cosets", #qc_fake_coeffs_mod_M;
qc_M := &*[primes[i]^exponents[i] : i in [1..#primes]];  // modulus
aux_int := 0;
repeat
  M := qc_M; 
  aux_int +:= 1;
  printf "adding information modulo %o\n", aux_int;
  time fake_coeffs_mod_M := combine_fake_good(qc_fake_coeffs_mod_M, qc_M, aux_int);
  M := qc_M*aux_int; // modulus
  "number of cosets", #fake_coeffs_mod_M;
  sieving_primes := spnf(M, g_p, groups, 5); // compute sieving primes
  done, sat_known, sat_unknown := 
    MWSieve(J, sieving_primes, M, bas, base_pt, fake_coeffs_mod_M :
  //unsat = unsat, satunknown = satunknown, 
  known_rat_coeffs := rat_coeffs);
done;
until done or aux_int gt 20;
// check if saturated
assert done and &and[is_saturated_at_p(bas, [], [], v) : v in sat_unknown];
*/
