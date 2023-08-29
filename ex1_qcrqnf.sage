
load("LinQCRQF.sage")
load("Solve_p-adic_systems.sage")
load("ex1_qcrqnf_setup.m")
load("inputex1p3.sage")


# find embeddings
sigmas = [K.hom([r[0]]) for r in Qpx(K.defining_polynomial()).roots()]
[Cps, sigmas] = QCRQF_Qp_curves(f, x, sigmas)
if Cps[0] == Cp2:
    # swap sigmas if not same order as magma
    sigmas = [sigmas[1], sigmas[0]]
    Cps = [Cp1, Cp2]

# Find common roots of quadratic Chabauty functions 
# and write their images under Abel-Jacobi in terms of generators.
coeffs, int_coeffs, unclearroots, roots, int_pts_pairs = QCRQF_MWS(C, p, integral_pts, generators, can_x,  integral_pts[0], away_hts_generators, prec, final_prec = 5, base_change_matrix = base_change_matrix, embeddings = sigmas, Xps = Cps, vals = vals)

# Check that all roots were determined
assert len(unclearroots) == 0

# write coefficients of QC roots in terms of bas as magma input
file = open('coeffsex1p3.m','w')
file.write("fake_coeffs := [[")
file.write(str(coeffs))
file.write("]];\n")
file.write("int_coeffs := [[")
file.write(str(int_coeffs))
file.write("]];")
file.close()

# run the Mordell-Weil sieve on `extra` roots
load("ex1_qcrqnf_mws.m")
