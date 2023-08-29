load("phts_hyp.sage")
"""
    This runs the quadratic Chabauty method for OK-integral points described in 
    ``Linear quadratic Chabauty'' on a sextic genus 2 curve $X:y^2=f(x)$ 
    defined over a real quadratic field K. We use a split prime p of good 
    reduction.

    AUTHORS: Stevan Gajović and Steffen Müller

    Throughout, let $\sigma_1, \sigma_2$ be the completions $K\rightarrow \mathbb{Q}_p$ and
    let $X_1,X_2$ be the respective base-changed curves.


    TODO: incorporate precision analysis
"""

def embed_point(P, Xps, sigmas):
    """
    Embed a K-rational point P into the two completions of X at p.
    """
    assert P[2] == 1
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
    """
    Find all pairs (D1, D2) of affine residue discs on (X1, X2).
    """
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


def QCRQF_Qp_curves(f, t, sigmas):
    """
    Find the base-changed curves $X_1,X_2$ and the maps
    $\sigma_i:X\rightarrow X_i$. Here $X:y^2=f(x)$, $t$ is the
    indeterminate of a polynomial ring over $\mathbb{Q}_p$ and sigmas are 
    the completions $K\rightarrow \Q_p$.
    """
    K = f.base_ring()
    a = K.gens()[0]
    d = ZZ(a^2)
    P1 = K.ideal(p).factor()[0][0]
    Fp1 = K.residue_field(P1)
    if (Fp1(sigmas[0](a))==Fp1(a)):
        # Correct order, don't swap
        fp1 = sum(t^i*sigmas[0](f[i]) for i in range(f.degree()+1))
        fp2 = sum(t^i*sigmas[1](f[i]) for i in range(f.degree()+1))
    else:
        # Swap order
        fp2 = sum(t^i*sigmas[0](f[i]) for i in range(f.degree()+1))
        fp1 = sum(t^i*sigmas[1](f[i]) for i in range(f.degree()+1))
        sigmas = [sigmas[1], sigmas[0]]
    Xp1 = HyperellipticCurve(fp1)
    Xp2 = HyperellipticCurve(fp2)
    return [[Xp1, Xp2], sigmas]


def QCRQF_basis_Coleman_integrals(Xps, L, T, prec):
    """
    Compute the Coleman integrals between the points in T and L
    """
    Col_ints = matrix(Xps[0].base_ring(),4,4) #4=2*g
    for i in range(3):
        for j in range(2):
            for l in range(2):
                Col_ints[i,2*l+j] = sum(coleman_integrals_on_basis_modified(T[j][k],L[i][j][k])[l] for k in range(2))
    Col_ints[3,0]=0
    Col_ints[3,1]=0
    Col_ints[3,2]=0
    Col_ints[3,3]=1
    return Col_ints


def QCRQF_beta_alpha(Xps, L, T, hts_away, prec, Ms):
    """
    Returns the beta and alpha coefficients in the description of the
    functions rho_k in Theorem 4.1 of LQC. Here
    - the alphas are the coefficients of the linear functional 
      P -> h(inf- - inf+ , P) in terms of products of abelian logs
    - the betas are linear relations between abelian logs, as in Sikseks's
      work
    INPUT:
    - Xps = [X1,X2], the base changed curves over Qp
    - L: A list of 3 pairs of lists of 2 points on X1, X2, encoding the
      images of 3 global divisors of degree 2.
    - T: A pair of lists of 2 points on X1, X2, encoding the
      images of a global divisor of degree 2.
    - hts_away: the heights h_q(inf- - inf+, D-E), where D runs through the
      divisors encoded in L and E is the divisor encoded in T.
    - prec: precision
    - Ms = psi(x^gdx/2y) on X1 and X2

    """
    # Compute single integrals of abasis of holomorphic differentials 
    # between points in L and points in T.
    BasisColInts = QCRQF_basis_Coleman_integrals(Xps, L, T, prec)
    beta = BasisColInts^(-1)*matrix([[0], [0], [0], [1]])

    heights = matrix(Xps[0].base_ring(),4,1)
    for i in range(3):
        heights[i,0] = sum(height_infinities(L[i][j][k], T[j][k], prec, Ms[j]) for k in range(2) for j in range(2)) - hts_away[i]
    heights[3,0] = 1
    # heights contains the global p-adic heights h(inf- - inf+, D-E), where
    # D runs through L and E runs through T

    alpha = BasisColInts^(-1)*heights
    return [beta, alpha]


def QCRQF_rhos(Ms, betaalpha, base_pts, Ps, prec):
    """
    Compute power series expansions of the quadratic Chabauty functions 
    rho1 and rho2 in a residue disc, see Theorem 4.1 of LinQC. 
    INPUT:
    - Ms = psi(x^gdx/2y) on X1 and X2
    - betaalpha: the coefficients beta and alpha
    - base_pts: the images on X1, X2 of the integral base point
    - Ps: a pair of points (P1,P2) in (X1,X2), used as centers of residue
      discs.
    - prec: the p-adic working precision
    OUTPUT:
    - the power series expansions of rho1 and rho2
    """
    Xps = [b.scheme() for b in base_pts]
    beta = betaalpha[0]
    alpha = betaalpha[1]
    p = Xps[0].base_ring().prime()
    QQp = pAdicField(p, prec)
    S.<z1,z2> = PowerSeriesRing(QQp, prec+10) 
    S1, S2 = base_pts 
    P1, P2 = Ps  
    M1, M2 = Ms
    ColemanintegralsS1P1 = coleman_integrals_on_basis_modified(S1, P1)
    ColemanintegralsS2P2 = coleman_integrals_on_basis_modified(S2, P2)
    TinyintegralsP1 = tiny_integrals_on_basis_parametric(P1, p*z1)
    TinyintegralsP2 = tiny_integrals_on_basis_parametric(P2, p*z2)
    rho1 = beta[0][0]*(ColemanintegralsS1P1[0] + TinyintegralsP1[0]) + beta[1][0]*(ColemanintegralsS2P2[0] + TinyintegralsP2[0]) + beta[2][0]*(ColemanintegralsS1P1[1] + TinyintegralsP1[1]) + beta[3][0]*(ColemanintegralsS2P2[1] + TinyintegralsP2[1])
    rho2 = alpha[0][0]*(ColemanintegralsS1P1[0] + TinyintegralsP1[0]) + alpha[1][0]*(ColemanintegralsS2P2[0] + TinyintegralsP2[0]) + alpha[2][0]*(ColemanintegralsS1P1[1] + TinyintegralsP1[1]) + alpha[3][0]*(ColemanintegralsS2P2[1] + TinyintegralsP2[1]) - height_infinities_first_point_residuedisc_parametric(P1, S1, p*z1, prec, M=M1) - height_infinities_first_point_residuedisc_parametric(P2, S2, p*z2, prec, M=M2)
    return [rho1, rho2]


def QCRQF_roots_of_rhos(Ms, betaalpha, base_pts, Ps, prec, vals = [0]):
    """
    Compute the roots of rho1 and of rho2-t in a residue multidisc, 
    where t runs through the set T of values that rho2 can take on
    integral points, for the quadratic 
    Chabauty functions rho1 and rho2 as in Theorem 4.1 of LinQC. The roots 
    are computed using code due to Francesca Bianchi.
    INPUT:
    - Ms = psi(x^gdx/2y) on X1 and X2
    - betaalpha: the coefficients beta and alpha
    - base_pts: the images on X1, X2 of the integral base point
    - Ps: a pair of points (P1,P2) in (X1,X2), used as centers of residue
      discs.
    - prec: the p-adic working precision
    - vals: the values T that rho2 can take on integral points
    OUTPUT:
    - the list of common roots of rho1=0 and rho2 in T on the pair of discs
      around (P1, P2) 
    - the list of double roots to precision prec
    - the expansions of rho1 and rho2
    """

    Xps = [b.scheme() for b in base_pts]
    p = Xps[0].base_ring().prime()
    [rho1, rho2] = QCRQF_rhos(Ms, betaalpha, base_pts, Ps, prec)
    R = Zp(p,prec+10)
    PolRing.<T1,T2> = PolynomialRing(R)
    # Now scale rho1 and rho2 to have coefficients that are integral 
    # and don't all reduce to 0.
    coeffsh1 = rho1.coefficients()
    coeffsh2 = rho2.coefficients()
    vpolh1 = min([v.valuation() for (k,v) in coeffsh1.items()])
    vpolh2 = min([v.valuation() for (k,v) in coeffsh2.items()])
    polrho1 = PolRing(sum(T1^(k.exponents()[0][0])*T2^(k.exponents()[0][1])*v*p^(-vpolh1) for (k,v) in coeffsh1.items()))
    polrho2 = PolRing(sum(T1^(k.exponents()[0][0])*T2^(k.exponents()[0][1])*v*p^(-vpolh2) for (k,v) in coeffsh2.items()))
    commonroots = [] 
    doubleroots = 0
    for val in vals:
        # First try computing the roots using a naive approach. Requires
        # that the roots are simple mod p.
        crts, drts = hensel_lift_n([polrho1, polrho2- p^(-vpolh2)*R(val)], p,min(prec-vpolh1,prec-vpolh2))
        if drts == 0:
            commonroots += crts
        else: # more general solver, but slower. Combines naive lifting
              # with Conrad's multivariable Hensel lemma
            crts2, drts2 = two_variable_padic_system_solver(polrho1, polrho2- p^(-vpolh2)*R(val), p, min(prec-vpolh1,prec-vpolh2), min(prec-vpolh1,prec-vpolh2))
            commonroots += crts2
            doubleroots += drts2
    return [commonroots, doubleroots, rho1, rho2]


def QCRQF_all_roots(f, Ms, betaalpha, base_pts, prec, vals = [0]):
    """
    Compute the roots of rho1 and of rho2 in T for the quadratic Chabauty 
    functions rho1 and rho2 as in Theorem 4.1 of LinQC. The roots are
    computed using code due to Francesca Bianchi.
    INPUT:
    - f: the polynomial such that X:y^2=f(x)
    - Ms = psi(x^gdx/2y) on X1 and X2
    - betaalpha: the coefficients beta and alpha
    - base_pts: the images on X1, X2 of the integral base point
    - prec: the p-adic working precision
    - vals: the values T that rho2 can take on integral points
    OUTPUT:
    - a list containing
        - the list of common roots of rho1=0 and rho2 in T on the pair of 
          discs around (P1, P2) 
        - the list of double roots to precision prec
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
                # find points in (X1,X2) corresponding to root
                z1 = root[0][0]
                z2 = root[1][0]
                x1, y1 = Xps[0].local_coord(P1)
                x2, y2 = Xps[1].local_coord(P2)
                RootPoint1 = Xps[0](x1.truncate()(p*z1),y1.truncate()(p*z1))
                RootPoint2 = Xps[1](x2.truncate()(p*z2),y2.truncate()(p*z2))
                listofroots = listofroots + [[RootPoint1, RootPoint2]]
        if doubleroots != 0:
            unclearroots = unclearroots + [[P1, P2], [rho1, rho2]]
    return [listofroots, unclearroots]


def QCRQF_MWS_coefficients(Colemanbasisintegrals, QCPoints, IntPoints, base_pts, prec = None):
    """
    Write the roots of the quadratic Chabauty equations rho1=0 and rho2 in
    T, as well as the known integral points, as linear combinations of the 
    generators, modulo p^prec. Use linearity of Coleman integrals of
    basis differentials for this.
    INPUT:
    - Colemanbasisintegrals: a 4x3 matrix of Coleman integrals of the basis
      differentials along images of representative of a $\mathbb{Q}$-basis
      of J(K) on (X1,X2)
    - QCPoints: a list of pairs of points on (X1,X2) (in our application
      these arise from roots of the QC equations)
    - IntPoints: a list of pairs of points on (X1,X2) (in our application,
      the images of the known integral points)
    - base_pts: the images on X1, X2 of the integral base pointThe 
    - prec: the working precision 
    OUTPUT:
    - the coefficients of QCPoints in terms of the Q-basis
    - the coefficients of IntPoints in terms of the Q-basis

    """
    minorbasis = Colemanbasisintegrals.submatrix(0,0,3,3)
    minorbasis2 = Colemanbasisintegrals.submatrix(1,0,3,3)
    # Could use either minorbasis or minorbasis2 to solve for the
    # coefficients because of dependency between integrals. 
    # Choose the one that leads to smaller precision loss.
    valdet = minorbasis.determinant().valuation()
    valdet2 = minorbasis2.determinant().valuation() 
    flag = false
    if valdet2 < valdet:
        minorbasis = minorbasis2
        valdet = valdet2
        flag = true
    minorbasisinv = minorbasis^(-1)
    extra_coeffs = []
    int_coeffs = []
    Xps = [b.scheme() for b in base_pts]
    n = len(Xps)
    K = Xps[0].base_ring()
    p = K.prime()
    if prec is not None: # lower precision
        if prec+valdet <= K.precision_cap():
            K = Qp(p, prec+valdet)
            Xps = [X.change_ring(K) for X in Xps]
            QCPoints = [[P.change_ring(K) for P in pair] for pair in QCPoints]
            IntPoints = [[P.change_ring(K) for P in pair] for pair in IntPoints]
            base_pts = [P.change_ring(K) for P in base_pts]
    for P in IntPoints:
        # check that every integral point arises as a root of the 
        # rho-functions exactly once to given precision
        assert QCPoints.count(P) == 1
    for P in QCPoints:
        integrals = [coleman_integrals_on_basis_modified(base_pts[i], P[i]) for i in range(n)]
        QCIntegrals1 = matrix(K,4,1)
        QCIntegrals1[0,0] = integrals[0][0]
        QCIntegrals1[1,0] = integrals[0][1]
        QCIntegrals1[2,0] = integrals[1][0]
        QCIntegrals1[3,0] = integrals[1][1]
        # Choose correct set of integrals according to choice of minorbasis
        if flag:
           minor = QCIntegrals1.submatrix(1,0,3,1)
        else:
           minor = QCIntegrals1.submatrix(0,0,3,1)
        coord = minorbasisinv*minor
        coord = [mod(coord[i][0], p**prec) for i in range(3)]
        if P in IntPoints:
            int_coeffs.append(coord)
        else:
            extra_coeffs.append(coord)
    return extra_coeffs, int_coeffs


def QCRQF_MWS(X, p, integral_pts, generators, can_x, base_pt, hts_away,  prec, final_prec = None, base_change_matrix = None, embeddings = None, Xps = None, vals = [0]):
    r"""
    Run the quadratic Chabauty method for integral points on even degree
    genus 2 curves over real quadratic number fields.
    AUTHORS:
            - Stevan Gajović, Steffen Müller
    INPUT: 
    - ``X`` -- A genus 2 curve `y^2=f(x)` defined over a real quadratic
      number field `K` such that `f` is integral, monic and sextic and 
      such that the Jacobian of `X` has Mordell--Weil rank 3.
    - ``p`` -- a prime of good reduction for `X` that splits in `K`
    - ``integral_pts`` -- a list of known `O_K`-integral points on `X`
    - ``generators`` -- a list of 3 independent points in `J(K)`, given as
      pairs of lists of 2 points on the base changed curves over
      `Qp(p,prec)` (using the isomorphism Pic^0->Pic^2 given by 
      D -> D - canonical divisor).
    - ``can_x`` -- the x-coordinate of a point `(x,y)` in `X(K)` 
    - ``base_pt`` -- an integral point in `X(K)` 
    - ``hts_away`` -- the local heights `h_q(\infty_- -\infty_+, D-D_x)` 
      where q is not above p, D runs through generators and D_x is the 
      canonical divisor `D_x = (x,y) - (x,-y)`.
    - ``prec`` -- the p-adic working precision
    - ``final_prec`` -- the desired output precision
    - ``base_change_matrix`` -- diagonal 3x3 matrix, expressing generators
       in terms of the original pseudo-basis (called bas in
       ex1_qcrqnf_setup.m)
    - ``embeddings`` -- list of the two embeddings of K into Q_p
    - ``Xps`` -- list of the base changed curves X1,X2 over Q_p
    - ``vals`` -- the list T of values that rho2 can take on integral points
    
    OUTPUT:
    - `extra_coeffs`` -- coefficients of images of common roots of QC 
      functions that are not among the known integral points under
      Abel-Jacobi wrt base_pt in terms of generators.
    - `int_coeffs`` -- coefficients of known integral points under
      Abel-Jacobi wrt base_pt in terms of generators.
    - `unclearroots` -- double roots to precision prec
    - `roots` -- all roots
    - `int_pts_pairs` -- images of known integral points on (X1,X2)

    """
    K = X.base_ring()
    g = X.genus()
    f, h = X.hyperelliptic_polynomials()
    assert h == 0
    assert K.degree() == 2
    if final_prec == None:
        final_prec = prec
    if embeddings == None: # Compute the embeddings K -> Q_p
        Q_p = pAdicField(p,prec) 
        OK = K.maximal_order()
        if len(factor(p*OK)) < 2:
            raise NotImplementedError('Only implemented for split primes')
        R = Q_p['x']
        embeddings = [K.hom([r[0]]) for r in R(K.defining_polynomial()).roots()]
    if Xps == None: # Compute the based changed curves X1, X2 over Q_p
        L = QCRQF_Qp_curves(f, x, embeddings)
        Xps = L[0]
    pts = [Xp.lift_x(can_x) for Xp in Xps]  
    #  pts = [(sigma1(can_x),y1), (sigma2(can_x),y2)]
    can_divs = [[pts[i], opposite_affine_point(pts[i])] for i in range(g)] 
    # images of canonical divisor D_x with x-coordinates can_x on (X1,X2)
    Ms = [psi_omega_for_infinities(Xp, prec) for Xp in Xps]
    # M_i = psi(x^gdx/2y) on X_i, used repeatedly for heights.
    betaalpha = QCRQF_beta_alpha(Xps, generators, can_divs, hts_away, prec, Ms)
    # betaalpha contains the  beta and alpha coefficients in Theorem 4.1
    basis_col_ints = matrix(Xps[0].base_ring(),4,3)
    for i in range(2):
        for j in range(2):
            for l in range(3):
                basis_col_ints[2*i+j,l] = sum(coleman_integrals_on_basis_modified(can_divs[i][k],generators[l][i][k])[j] for k in range(2))

    # basis_col_ints: the Coleman integrals of the basis differentials 
    # between the divisors D-D_x
    base_pts = embed_point(base_pt, Xps, embeddings)
    [roots, unclearroots] = QCRQF_all_roots(f, Ms, betaalpha, base_pts, prec, vals)
    # roots of quadratic Chabauty equations rho1=0, rho2 in T
    int_pts_pairs = [embed_point(P, Xps, embeddings) for P in integral_pts]
    # images of known integral points on (X1,X2)
    if base_change_matrix != None:
        basis_col_ints = basis_col_ints*base_change_matrix
    extra_coeffs, int_coeffs = QCRQF_MWS_coefficients(basis_col_ints, roots, int_pts_pairs, base_pts, prec = final_prec)

    return extra_coeffs, int_coeffs, unclearroots, roots, int_pts_pairs
    

