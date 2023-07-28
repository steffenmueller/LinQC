load("phts_hyp.sage")

"""
    The functions in this file use quadratic Chabauty to compute a finite set of p-adic points containing
    the integral points on a hyperelliptic curve y^2=f(x), where f is a
    polynomial over the integers that is  monic and squarefree and has even degree.

    AUTHORS: Stevan Gajović and Steffen Müller

    TO DO:
    - incorporate precision analysis
    - add double roots case
    - add algorithm for input for MW sieve (see code for number fields), not
    necessary for our example.
    - allow nontrivial local contributions away from p.
"""

def Q_lift(CK, Q, p):
    r"""
    Compute a point lifting a given affine point over `GF(p)`.
    INPUT:
    - ``CK`` -- a hyperelliptic curve over `\\QQ_p`.
    - ``Q`` -- a point in `CK(GF(p))`.
    - ``p`` -- the prime of the first two input items.
    OUTPUT: The point `P` on `CK` lifting `Q` and such that
    `x(P)\\in \ZZ`,`0 <= x(P) <= p-1` if `y(Q) != 0`,
    and `y(P) = 0` if `y(Q) = 0`.
    """
    xQ = Integers()(Q[0])
    yQ = Integers()(Q[1])
    if yQ == 0:
        r = CK.hyperelliptic_polynomials()[0].roots()
        Q_lift = CK(exists(r, lambda a : (Integers()(a[0])-xQ) % p == 0)[1][0],0)
    else:
        K = CK.base_ring()
        xQ = K(xQ)
        lifts = CK.lift_x(xQ, all=True)
        for i in range(len(lifts)):
            if (Integers()(lifts[i][1])-yQ) % p == 0:
                Q_lift = lifts[i]
    return Q_lift


def Coleman_integral_first_point_residuedisc_to_z(C, P, Q, prec):
    """
    Computes Coleman integrals on basis from fixed Q to P(z), where P(z) is a point in the residue disc of P, uses known integrals from Q to P and tiny integrals on basis from P to P(z)
    """
    return [C.coleman_integrals_on_basis(Q,P)[i] + C.tiny_integrals_on_basis_to_z(P)[i] for i in range(len(C.coleman_integrals_on_basis(Q,P)))]


def QCQ_affine_residue_discs(f, p):
    """
    Returns all affine residue discs modulo p 
    """
    K = f.base_ring()
    a = K.gens()[0]
    Fp = K.residue_field()
    t = polygen(Fp)
    f1 = sum(t^i*Fp(f[i]) for i in range(f.degree()+1))
    X1 = HyperellipticCurve(f1)
    L1 = X1.points()
    return L1[1:len(L1)]

def QCQ_basis_Coleman_integrals(Xp, L, prec):
    """L is a basis of J(Q) (or a finite-index subgroup) L=[D1,...,Dg] (QC assumption r=g), whose elements Di are represented as degree zero divisors, i.e., elements P1i + ... + Pki - Q1i - ... - Qki are represented as [[P1i, ... , Pki], [Q1i, ..., Qki]]. So, the length of L is g, whereas we allow the length of L[i] to differ for all i, as long as L[i] represents a degree zero divisor in the required shape. This function returns Coleman integrals over the basis elements as a gxg matrix M: M_{ij} = \int_{Di}\omega_j."""
    g = Xp.genus()
    Col_ints = matrix(Xp.base_ring(),g,g)
    for i in range(g):
        ListIntegrals = [coleman_integrals_on_basis_modified(L[i][1][k], L[i][0][k]) for k in range(len(L[i][0]))]
        for j in range(g):
            Col_ints[i,j] = sum(ListIntegrals[k][j] for k in range(len(L[i])/2))
    return Col_ints

def QCQ_heights(Xp, M, L, hts, prec):
    """L is a basis of J(Q) (or a finite-index subgroup) L=[D1,...,Dg] (QC assumption r=g), whose elements Di are represented as degree zero divisors, i.e., elements P1i + ... + Pki - Q1i - ... - Qki are represented as [[P1i, ... , Pki], [Q1i, ..., Qki]]. So, the length of L is g, whereas we allow the length of L[i] to differ for all i, as long as L[i] represents a degree zero divisor in the required shape. The list hts contains the contribution away from p for h(\infty_- - \infty_+, Di), i=1,...,g, multiplied by -1 -> we compute this part in Magma, and the contribution at p here in Sage, and whence the whole height. This function returns an 1xg matrix M: M_{1i} = h(\infty_- - \infty_+, Di)."""
    g = Xp.genus()
    heights_p = matrix(Xp.base_ring(),g,1)
    for i in range(g):
        heights_p[i,0] = sum(height_infinities(L[i][0][k], L[i][1][k], prec, M) for k in range(len(L[i][0]))) - hts[i]
    return heights_p

def QCQ_alpha(Xp, M, L, hts, prec):
    """Our assumption is that we can express the linear map J(Q) --> Qp given by the height D |--> h(\infty_- - \infty_+, D) as a linear combination of Coleman integrals:
    h(\infty_- - \infty_+, D) = alpha_0 \int_{D}\omega_0 + ... + alpha_{g-1} \int_{D}\omega_{g-1}. 
    This function computes the coefficients alpha and stores them as a 1xg matrix."""
    BasisColInts = QCQ_basis_Coleman_integrals(Xp, L, prec)
    heights_p = QCQ_heights(Xp, M, L, hts, prec)
    alpha = BasisColInts^(-1)*heights_p
    return alpha

def QCQ_rho(Xp, M, alpha, base_pt, P, prec):
    """This function computes the power series locally in a residue disc of P (so the point is P(z), in terms of a parameter z, well-behaved uniformiser at P) rho(z) = alpha_0 \int_{base_pt}^{P(z)}\omega_0 + ... + alpha_{g-1} \int_{base_pt}^{P(z)}\omega_{g-1} - hp(\infty_- - \infty_+, P(z)-base_pt)."""
    g = Xp.genus()
    p = Xp.base_ring().prime()
    QQp = pAdicField(p, prec)
    tadicprec = prec+10 #TODO: Fix!
    S.<z1> = PowerSeriesRing(QQp, tadicprec)
    Colemanintegrals = coleman_integrals_on_basis_modified(base_pt, P)
    Tinyintegrals = tiny_integrals_on_basis_parametric(P, p*z1, tadicprec)
    rho = sum(alpha[i][0]*(Colemanintegrals[i] + Tinyintegrals[i]) for i in range(g)) - height_infinities_first_point_residuedisc_parametric(P, base_pt, p*z1, prec, tadicprec, M)
    return rho


def QCQ_roots_of_rho(Xp, M, alpha, base_pt, P, hts_away, prec):
    """Returns all the roots of equations rho(z) = hts_away[i], where hts_away is the list of potential contributions of h(\infty_- - \infty_+, P-Q) away from p for integral points P and Q."""
    p = Xp.base_ring().prime()
    rho = QCQ_rho(Xp, M, alpha, base_pt, P, prec)
    # Note that polrootspadic sometimes has issues with double roots.
    roots = []
    for ha in hts_away:
        roots = roots + sage.libs.pari.convert_sage.gen_to_sage(pari.polrootspadic((rho-ha).truncate(),p,prec))
    return roots

def QCQ_all_roots(Xp, M, alpha, hts_away, base_pt, prec):
    """
    Returns a finite subset S of Xp(Qp) which contains the integral points on Xp.
    """
    f = Xp.hyperelliptic_polynomials()[0]
    listofroots = []
    unclearroots = []
    affresdiscs = QCQ_affine_residue_discs(f, p)
    for Fppts in affresdiscs:
        #print("Residue disc ", Fppts)
        P = Q_lift(Xp, Fppts, p)
        #roots, doubleroots = QCQ_roots_of_rho(Xp, M, alpha, base_pt, P, hts_away, prec)
        roots = QCQ_roots_of_rho(Xp, M, alpha, base_pt, P, hts_away, prec)
        #print("Roots ", roots)
        if len(roots) != 0:
            for z in roots:
                if (valuation(z) >= 0):
                    x1, y1 = Xp.local_coord(P)
                    RootPoint = Xp(x1.truncate()(p*z),y1.truncate()(p*z))
                    listofroots = listofroots + [RootPoint]
        #if doubleroots != 0:
        #    unclearroots = unclearroots + [[P1, P2], [rho1, rho2]]
    #return listofroots, unclearroots
    return listofroots

