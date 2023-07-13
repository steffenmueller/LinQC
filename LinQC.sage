load("phts_hyp.sage")


def embed_point(P, Xps, sigmas):
    assert P[2] == 1
    #K = P.scheme().base_ring()
    #p = Xps[0].base_ring().prime()
    #sigmas = embeddings(K,p,prec)
    return [Xps[i](sigmas[i](P[0]), sigmas[i](P[1])) for i in range(len(Xps))]



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

def QCRQF_pairs_of_affine_residue_discs(f, p):
    K = f.base_ring()
    a = K.gens()[0]
    d = ZZ(a^2)
    P1 = K.ideal(p).factor()[0][0]
    Fp1 = K.residue_field(P1)
    P2 = K.ideal(p).factor()[1][0]
    Fp2 = K.residue_field(P2)
    t1 = polygen(Fp1)
    f1 = sum(t1^i*Fp1(f[i]) for i in range(f.degree()+1))
    X1 = HyperellipticCurve(f1)
    L1 = X1.points()
    t2 = polygen(Fp2)
    f2 = sum(t2^i*Fp2(f[i]) for i in range(f.degree()+1))
    X2 = HyperellipticCurve(f2)
    L2 = X2.points()
    return [[Q1, Q2] for Q1 in L1[1:len(L1)] for Q2 in L2[1:len(L2)]]

#def QCRQF_Qp_curves(f, p, prec):
def QCRQF_Qp_curves(f, t, sigmas):
    K = f.base_ring()
    a = K.gens()[0]
    d = ZZ(a^2)
    #QQp = pAdicField(p, prec)
    P1 = K.ideal(p).factor()[0][0]
    Fp1 = K.residue_field(P1)
    #psi = embeddings(K,p,prec)
    #t = polygen(QQp)
    if (Fp1(sigmas[0](a))==Fp1(a)):
        fp1 = sum(t^i*sigmas[0](f[i]) for i in range(f.degree()+1))
        fp2 = sum(t^i*sigmas[1](f[i]) for i in range(f.degree()+1))
    else:
        fp2 = sum(t^i*sigmas[0](f[i]) for i in range(f.degree()+1))
        fp1 = sum(t^i*sigmas[1](f[i]) for i in range(f.degree()+1))
        sigmas = [sigmas[1], sigmas[0]]
    Xp1 = HyperellipticCurve(fp1)
    Xp2 = HyperellipticCurve(fp2)
    return [[Xp1, Xp2], sigmas]



def QCRQF_basis_Coleman_integrals(Xps, L, T, hts, prec):
    Col_ints = matrix(Xps[0].base_ring(),4,4) #4=2*g
    for i in range(3):
        for j in range(2):
            for l in range(2): #TODO: improve, need to reverse order of loops (k&l)
                Col_ints[i,2*l+j] = sum(coleman_integrals_on_basis2(Xps[j],T[j][k],L[i][j][k])[l] for k in range(2))
    Col_ints[3,0]=0
    Col_ints[3,1]=0
    Col_ints[3,2]=0
    Col_ints[3,3]=1
    return Col_ints
    #return Col_ints, (Col_ints^(-1)).determinant()

def QCRQF_heights(Xps, L, T, hts, prec):
    heights_p = matrix(Xps[0].base_ring(),4,1)
    for i in range(3):
        heights_p[i,0] = sum(height_infinities(Xps[j], L[i][j][k], T[j][k], prec) for k in range(2) for j in range(2)) - hts[i]
    heights_p[3,0] = 1
    return heights_p

def QCRQF_beta_alpha(Xps, L, T, hts, prec):
    BasisColInts = QCRQF_basis_Coleman_integrals(Xps, L, T, hts, prec)
    beta = BasisColInts^(-1)*matrix([[0], [0], [0], [1]])
    heights_p = QCRQF_heights(Xps, L, T, hts, prec)
    alpha = BasisColInts^(-1)*heights_p
    return [beta, alpha]

def QCRQF_rhos(Ms, betaalpha, base_pts, Ps, prec):
    Xps = [b.scheme() for b in base_pts]
    beta = betaalpha[0]
    alpha = betaalpha[1]
    p = Xps[0].base_ring().prime()
    QQp = pAdicField(p, prec)
    S.<z1,z2> = PowerSeriesRing(QQp, prec+10)
    S1, S2 = base_pts
    P1, P2 = Ps
    M1, M2 = Ms
    ColemanintegralsS1P1 = coleman_integrals_on_basis2(Xps[0], S1, P1)
    ColemanintegralsS2P2 = coleman_integrals_on_basis2(Xps[1], S2, P2)
    TinyintegralsP1 = tiny_integrals_on_basis_parametric(Xps[0], P1, p*z1)
    TinyintegralsP2 = tiny_integrals_on_basis_parametric(Xps[1], P2, p*z2)
    rho1 = beta[0][0]*(ColemanintegralsS1P1[0] + TinyintegralsP1[0]) + beta[1][0]*(ColemanintegralsS2P2[0] + TinyintegralsP2[0]) + beta[2][0]*(ColemanintegralsS1P1[1] + TinyintegralsP1[1]) + beta[3][0]*(ColemanintegralsS2P2[1] + TinyintegralsP2[1])
    rho2 = alpha[0][0]*(ColemanintegralsS1P1[0] + TinyintegralsP1[0]) + alpha[1][0]*(ColemanintegralsS2P2[0] + TinyintegralsP2[0]) + alpha[2][0]*(ColemanintegralsS1P1[1] + TinyintegralsP1[1]) + alpha[3][0]*(ColemanintegralsS2P2[1] + TinyintegralsP2[1]) - height_infinities_first_point_residuedisc_parametric_withM(Xps[0], M1, P1, S1, prec, p*z1) - height_infinities_first_point_residuedisc_parametric_withM(Xps[1], M2, P2, S2, prec, p*z2)
    return [rho1, rho2]


def QCRQF_roots_of_rhos(Ms, betaalpha, base_pts, Ps, prec, vals = [0]):
    Xps = [b.scheme() for b in base_pts]
    p = Xps[0].base_ring().prime()
    [rho1, rho2] = QCRQF_rhos(Ms, betaalpha, base_pts, Ps, prec)
    R = Zp(p,prec+10)
    PolRing.<T1,T2> = PolynomialRing(R)
    coeffsh1 = rho1.coefficients()
    coeffsh2 = rho2.coefficients()
    vpolh1 = min([v.valuation() for (k,v) in coeffsh1.items()])
    vpolh2 = min([v.valuation() for (k,v) in coeffsh2.items()])
    polrho1 = PolRing(sum(T1^(k.exponents()[0][0])*T2^(k.exponents()[0][1])*v*p^(-vpolh1) for (k,v) in coeffsh1.items()))
    polrho2 = PolRing(sum(T1^(k.exponents()[0][0])*T2^(k.exponents()[0][1])*v*p^(-vpolh2) for (k,v) in coeffsh2.items()))
    commonroots = [] 
    doubleroots = 0
    for val in vals:
        # TODO: Is there a smarter way?
        crts, drts = hensel_lift_n([polrho1, polrho2- p^(-vpolh2)*R(val)], p,min(prec-vpolh1,prec-vpolh2))
        if drts == 0:
            commonroots += crts
        else: # more general solver, but slower 
            crts2, drts2 = two_variable_padic_system_solver(polrho1, polrho2- p^(-vpolh2)*R(val), p, min(prec-vpolh1,prec-vpolh2), min(prec-vpolh1,prec-vpolh2))
            commonroots += crts2
            doubleroots += drts2
    return [commonroots, doubleroots, rho1, rho2]

def QCRQF_all_roots(f, Ms, betaalpha, base_pts, prec, vals = [0]):
    """
    NOT! Returns points that are "extra", solutions of the p-adic power series systems, but not in the set of known integral points
    """
    Xps = [b.scheme() for b in base_pts]
    listofroots = []
    unclearroots = []
    affresdiscs = QCRQF_pairs_of_affine_residue_discs(f, p)
    for Fppts in affresdiscs:
        P1 = Q_lift(Xps[0], Fppts[0], p)
        P2 = Q_lift(Xps[1], Fppts[1], p)
        [commonroots, doubleroots, rho1, rho2] = QCRQF_roots_of_rhos(Ms, betaalpha, base_pts, [P1,P2], prec, vals)
        if doubleroots == 0 and len(commonroots) != 0:
            for root in commonroots:
                z1 = root[0][0]
                z2 = root[1][0]
                x1, y1 = Xps[0].local_coord(P1)
                x2, y2 = Xps[1].local_coord(P2)
                RootPoint1 = Xps[0](x1.truncate()(p*z1),y1.truncate()(p*z1))
                RootPoint2 = Xps[1](x2.truncate()(p*z2),y2.truncate()(p*z2))
                listofroots = listofroots + [[RootPoint1, RootPoint2]]
                #print("listofroots", len(listofroots))
        if doubleroots != 0:
            unclearroots = unclearroots + [[P1, P2], [rho1, rho2]]
    return [listofroots, unclearroots]



def QCRQF_MWS_coefficients(Colemanbasisintegrals, CandidatesPoints, IntPoints, base_pts, prec = None):
    # TODO: Arbitrary genus
    # prec: desired output precision
    minorbasis = Colemanbasisintegrals.submatrix(0,0,3,3)
    minorbasis2 = Colemanbasisintegrals.submatrix(1,0,3,3)
    valdet = minorbasis.determinant().valuation()
    valdet2 = minorbasis2.determinant().valuation() 
    flag = false
    if valdet2 < valdet:
        minorbasis = minorbasis2
        valdet = valdet2
        flag = true
    minorbasisinv = minorbasis^(-1)
    coeffs = []
    int_coeffs = []
    Xps = [b.scheme() for b in base_pts]
    n = len(Xps)
    K = Xps[0].base_ring()
    p = K.prime()
    if prec is not None: # lower precision
        if prec+valdet <= K.precision_cap():
            K = Qp(p, prec+valdet)
            Xps = [X.change_ring(K) for X in Xps]
            CandidatesPoints = [[P.change_ring(K) for P in pair] for pair in CandidatesPoints]
            IntPoints = [[P.change_ring(K) for P in pair] for pair in IntPoints]
            base_pts = [P.change_ring(K) for P in base_pts]
    for P in IntPoints:
        # every integral point arises as a root of the rho-functions
        # exactly once to given precision
        assert CandidatesPoints.count(P) == 1
    for P in CandidatesPoints:
        integrals = [coleman_integrals_on_basis2(Xps[i], base_pts[i], P[i]) for i in range(n)]
        CandidatesIntegrals1 = matrix(K,4,1)
        CandidatesIntegrals1[0,0] = integrals[0][0]
        CandidatesIntegrals1[1,0] = integrals[0][1]
        CandidatesIntegrals1[2,0] = integrals[1][0]
        CandidatesIntegrals1[3,0] = integrals[1][1]
        if flag:
           minor = CandidatesIntegrals1.submatrix(1,0,3,1)
        else:
           minor = CandidatesIntegrals1.submatrix(0,0,3,1)
        coord = minorbasisinv*minor
        coord = [mod(coord[i][0], p**prec) for i in range(3)]
        if P in IntPoints:
            int_coeffs.append(coord)
        else:
            coeffs.append(coord)
            
    return coeffs, int_coeffs

def QCRQNF_MWS(X, p, integral_pts, generators, hts_away, can_x, base_pt, prec, final_prec = None, base_change_matrix = None, embeddings = None, Xps = None, vals = [0]):
    K = X.base_ring()
    g = X.genus()
    f, h = X.hyperelliptic_polynomials()
    assert h == 0
    assert K.degree() == 2
    if final_prec == None:
        final_prec = prec

    if embeddings == None:
        Q_p = pAdicField(p,prec) 
        OK = K.maximal_order()
        pOK = factor(p*OK)
        assert len(pOK) == 2  # only split p, for now
        R = Q_p['x']
        embeddings = [K.hom([r[0]]) for r in R(K.defining_polynomial()).roots()]
    if Xps == None:
        Xps = QCRQF_Qp_curves(f, x, embeddings)
    pts = [Xp.lift_x(can_x) for Xp in Xps]
    can_divs = [[pts[i], opposite_affine_point(Xps[i], pts[i])] for i in range(g)] 
    betaalpha = QCRQF_beta_alpha(Xps, generators, can_divs, hts_away, prec)
    basis_col_ints = matrix(Xps[0].base_ring(),4,3)
    for i in range(2):
        for j in range(2):
            for l in range(3):
                basis_col_ints[2*i+j,l] = sum(coleman_integrals_on_basis2(Xps[i],can_divs[i][k],generators[l][i][k])[j] for k in range(2))

    Ms = [psi_omega_for_infinities_mixed_basis(Xp, prec) for Xp in Xps]
    base_pts = embed_point(base_pt, Xps, embeddings)
    [roots, unclearroots] = QCRQF_all_roots(f, Ms, betaalpha, base_pts, prec, vals)
    int_pts_pairs = [embed_point(P, Xps, embeddings) for P in integral_pts]
    if base_change_matrix != None:
        basis_col_ints = basis_col_ints*base_change_matrix
    coeffs, int_coeffs = QCRQF_MWS_coefficients(basis_col_ints, roots, int_pts_pairs, base_pts, prec = final_prec)

    return coeffs, int_coeffs, unclearroots, roots, int_pts_pairs

    
    
