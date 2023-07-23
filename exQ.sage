
"""
Compute the integral points on the genus 2 curve in §4.4 of "Linear
quadratic Chabauty"

AUTHORS: Stevan Gajović and Steffen Müller
"""

load("LinQCQ.sage")
p = 7
prec = 10
K = pAdicField(p, prec)
x = polygen(K)
f = (x^6 + 2*x^5 - 7*x^4 - 18*x^3 + 2*x^2 + 20*x + 9)
X = HyperellipticCurve(f)
Q = X(-1,1)
Q0 = X(0,3)
Q1 = X(1,3)
L = [[[Q0], [Q]], [[Q1], [Q]]]
M = psi_omega_for_infinities(X, prec)
hts = [0,0]
alpha = QCQ_alpha(X, M, L, hts, prec)
hts_away = [0]
int_coords = [[0, 3], [0,-3], [1, 3], [1,-3], [-1, 1], [-1,-1], [-2, 3], [-2,-3], [-4, 37], [-4,-37]]
int_pts = [X(P) for P in int_coords]
print("known integral points", int_coords)
affresdiscs = QCQ_affine_residue_discs(f, p)
print("There is a unique integral point in every affineresidue disc:", affresdiscs)
rhos = [QCQ_rho(X, M, alpha, Q, P, prec) for P in int_pts]
# Using Strassmann's theorem, one checks that these all have exactly one
# root of positive valuation, at z=0.
# Hence the known integral points are the only ones.
# Let's compute the roots explicitly.
all_roots = [QCQ_roots_of_rho(X, M, alpha, Q, P, [0], prec) for P in int_pts]
int_roots = [[r for r in all_roots[i] if r.valuation() >= 0] for i in range(len(all_roots))]
print("positive valuation roots of rho in all residue discs", int_roots)
print("Hence the known integral points are the only ones")
# Alternatively, we can explicitly compute the roots of rhos using our more
# general algorithm, as follows:
roots = QCQ_all_roots(X, M, alpha, hts_away, Q, prec)
assert len(roots) == 10
