

"""
This SageMath code computes the local cyclotomic p-adic (Coleman--Gross) height
$h_p$ on a hyperelliptic curve $C:y^2=f(x)$ over $\mathbb{Q}_p$ with good 
reduction. 
More precisely, it computes $h_p(P-Q,R-S)$ for
$P,Q,R,S\in C(\mathbb{Q}_p)$ satisfying the following conditions:
- $f$ is monic (one can use move_to_monic1 or move_to_monic2 if this is not
  satisfied);
- the residue discs $D(P)$ and $D(Q)$ of $P$ and $Q$ are distinct from
  $D(R)$, $D(\iota(R))$, $D(S)$ and $D(\iota(S))$, where $\iota$ is the
  hyperelliptic involution.

*Dependencies*
Jennifer Balakrishnan's code for even degree Coleman integrals is required.
Download it from https://github.com/jbalakrishnan/AWS and follow the 
instructions given there.

*Main functions*
- height_infinities(P, Q, prec) computes $h_p(\infty_- - \infty_+, P-Q)$
  for even degree models to precision prec. 
- height_four_affine_points(P, Q, R, S, prec) computes $h_p(P-Q, R-S)$ for
  affine $P,Q,R,S$ to precision prec.
- height_divisors(D1, D2) computes $h_p(D_1, D_2)$ for two degree 0
  divisors $D_1,D_2$ on $C$ with disjoint an pointwise $\Q_p$-rational 
- height_infinities_residuedisc_to_z(P) computes $h_p(\infty_- - \infty_+,
  P(z)-P)$, where $P(z)$ is a parametric point in the residue disc of $P$ 
  (used for quadratic Chabauty).
  support.

*Auxiliary choices*
The local height $h_p$ depends on the choice of 
- a continuous homomorphism $\chi_p\colon \mathbb{Q}_p^{\ast} \rightarrow
  \Q_p$: in our case $\chi_p$ is the branch of the $p$-adic logarithm that
  satisfies $\log_p(p)=0$;
- a subspace $W$ of $H^1_{dR}(C)$, complementary to the image of the space
  of holomorphic forms. We also assume that $W$ is isotropic with respect 
  to the cup product, so that $h_p$ is symmetric.

Our code constructs a basis $\langle[\eta_0],\ldots,[\eta_{2g-1}]\rangle$ of
H^1_{dR}(C)$ such that $\eta_0,\dlots,\eta_{g-1}$ are holomorphic.
If $p$ is a prime of good ordinary reduction, there is a natural choice for
$W$, namely the unit root subspace with respect to Frobenius, which is
generated modulo $p^{prec}$ by 
$Frob^{prec}(\eta_g),\ldots, Frob^{prec}(\eta_{2g-1})$, see the function
"changebasistounitroot". This case is particularly important because it appears 
in the $p$-adic version of the Birch and Swinnerton-Dyer conjecture; hence
it is the default subspace in our code. However, our algorithm works for any 
isotropic complementary subspace $W$. For instance our function 
"symplectic_h1dr_basis" computes a complementary subspace whose basis 
extends $[\eta_0],\ldots,[\eta_{g-1}]$ to a symplectic basis with respect to
the cup product. Other subspaces can be specified by the user using the 
optional parameter "W". 

If several heights of the form $h_p(\infty_--\infty_+, P-Q)$ on the same
curve have to be computed, then it makes sense to precompute
$\psi(x^gdx/y)$ using "psi_omega_for_infinities" and to pass it to
"height_infinities" (or "tiny_height_infinities") via the parameter "M", 
since this is needed in all of these computations.

*Precision*
Several functions have an optional parameter prec. This is the target
precision; the precision of the result may be lower, but the result is 
guaranteed to be correct to its precision.
However, the precision of the result cannot exceed the precision of 
the curve $C$; to get higher precision of the result, increase the precision
of $C$.

"""

def is_ordinary(C, p):
    """
    For a hyperelliptic curve $C$ with good reduction at $p$, determine whether
    the Jacobian of $C$ has ordinary reduction at $p$.
    """
    pol = C.change_ring(GF(p)).zeta_function().numerator().reverse()
    g = C.genus()
    slopes = pol.newton_slopes(p)
    if slopes.count(0) == g:
        return True
    return False


def local_coordinates_at_infinity_even(C, prec = 20, name = 't'):
    """
    For an even degree model, gives a local coordinate above $\\infty_+$
    """
    g = C.genus()
    pol1,pol2 = C.hyperelliptic_polynomials()
    if not pol2 == 0:
        raise NotImplementedError('Need a model y^2=f(x)')
    if not is_even(pol1.degree()):
        raise ValueError('Need an even degree model')
    K = LaurentSeriesRing(C.base_ring(), name, prec+2)
    t = K.gen()
    L = PolynomialRing(K,'x')
    x = L.gen()
    i = 0
    x = t**-1
    f = pol1(x)
    y = (pol1.leading_coefficient()).sqrt()*t**-(g+1)
    for i in range((RR(log(prec)/log(2))).ceil()):
        y = (y + f/y)/2
    return (x+O(t**(prec+2)) , y+O(t**(prec+2)))


def h1dr_basis(C):
    """
    Extract a basis of $H^1_{dR}(C)$ from $H^1_{MW}(U)$.
    """
    g = C.genus()
    f = C.hyperelliptic_polynomials()[0]
    if f.degree() == 2*g+1:
        x,y = C.monsky_washnitzer_gens()
        w = C.invariant_differential()
        return [x^i*w for i in range(2*g)]
    if f.degree() == 2*g+2:
        x,y = local_coordinates_at_infinity_even(C, prec=2*g+1)
        wg = (x^g)*x.derivative()/(2*y)
        c = wg.residue()
        L = []
        xx,yy = C.monsky_washnitzer_gens()
        w = C.invariant_differential()
        wg_xxyy = xx^(g)*w
        for i in range(g+1,2*g+1):
            diff = x^i*x.derivative()/(2*y)
            r = diff.residue()
            diff_xxyy = xx^i*w
            L = L + [(diff_xxyy-r/c *wg_xxyy)]
        return [xx^i*w for i in range(g)] + L


def matrix_of_frobenius_on_h1mw_h1dr(C, p, prec=20):
    """
    Computes the matrix of Frobenius action on $H^1_{dR}(C)$ from Frobenius action on $H^1_{MW}(U)$ (doing standard linear algebra) and returns both.
    """
    g = C.genus()
    basis = h1dr_basis(C)
    X = C.change_ring(QQ)
    F = X.matrix_of_frobenius(p,prec)
    if not is_even(C.hyperelliptic_polynomials()[0].degree()):
        FH = F
    if is_even(C.hyperelliptic_polynomials()[0].degree()):
        FH = matrix(C.base_ring(), 2*g,2*g)
        for i in range(g):
            for j in range(g):
                FH[i,j] = F[i,j]
        for i in range(g):
            for j in range(g,2*g):
                FH[i,j] = F[i,j+1] + basis[j].coeffs()[0][0][g]*F[i,g]
        for i in range(g,2*g):
            for j in range(g):
                FH[i,j] = F[i+1,j]
        for i in range(g,2*g):
            for j in range(g,2*g):
                FH[i,j] = F[i+1,j+1] + basis[j].coeffs()[0][0][g]*F[i+1,g]
    return F, FH


def cup_product_matrix(C, basis):
    """
    Computes the cup product matrix on $H^1_{dR}(C)$ with respect to an odd basis.
    """
    g = C.genus()
    f = C.hyperelliptic_polynomials()[0]
    if f.degree() == 2*g+1:
        x,y = C.local_coordinates_at_infinity(prec=2*(2*g-1))
    if f.degree() == 2*g+2:
        x,y = local_coordinates_at_infinity_even(C, prec=2*g+1)
        #Warning: Sage sees only one point above infinity
    xprime = x.derivative()
    w = [0 for i in range(2*g)]
    for i in range(2*g):
        coeffs = basis[i].coeffs()[0][0]  # x-coefficients of the ith basis element
        w[i] = sum([coeffs[j]*x^j for j in range(len(coeffs))])*xprime/(2*y)  # Replace by local x-coord at infinity
    wint = [(w[i]).integral() for i in range(2*g)]
    # Residue at \infty_- and \infty_+ is the same, so we can compute 
    # only one and multiply by two
    return (f.degree()-2*g)*matrix(C.base_ring(), 2*g,2*g, [(w[j]*wint[i]).residue() for i in range(2*g) for j in range(2*g)])


def maxranksubmatrices(N):
    """
    Extracts the sequence of quadratic submatrices of the standard cup product matrix of the maximal rank, used to obtain a symplectic basis w.r.t. the cup product.
    """
    d = N.dimensions()[1]
    if d == 1:
        if N[0][0] != 0:
            return [N.delete_rows([1]), 1]
        if N[1][0] != 0:
            return [N.delete_rows([0]), 0]
    for i in range(d+1):
        N1 = N.delete_rows([i])
        if N1.rank() == d:
            N2 = N1.delete_columns([d-1])
            return [N1, i] + maxranksubmatrices(N2)


def correctorder(L):
    """
    Counts in which order rows "survive" from maxranksubmatrices().
    """
    d = len(L)
    ind = [i for i in range(d+1)]
    for i in range(d):
        c = ind[L[i]]
        ind.remove(ind[L[i]])
        L[i] = c
    return L + ind


def indicesofrows(L):
    """
    From maxranksubmatrices(), extracts the sequence of indices of holomorphic forms used in obtaining a symplectic basis w.r.t. the cup product.
    """
    d = len(L)
    L2 = [L[2*i+1] for i in range(d/2)]
    L3 = correctorder(L2)
    L3.reverse()
    return L3


def symplectic_h1dr_basis(C):
    """
    Linear change of a basis of $H^1_{dR}(C)$ so that the complement of holomorphic 
    differentials completes a symplectic basis w.r.t. the cup product.
    """
    g = C.genus()
    basis = h1dr_basis(C)
    CPM = cup_product_matrix(C, basis)
    newbasis = [basis[i] for i in range(g+1)]
    N = matrix(CPM.submatrix(0,g,g,g-1))
    fullrankmatrices = maxranksubmatrices(N)
    Lind = indicesofrows(fullrankmatrices)
    newcoeffs = matrix(g,2*g)
    for i in range(g):
        newcoeffs[i,g+i] = 1
    for i in range(g-1):
        M = matrix(CPM.submatrix(g,g+1+i,i+1,1))
        for j in range(i):
            M[j+1,0] =  M[j+1][0] - sum(newcoeffs[j+1][k]*CPM[g+1+i][k] for k in range(g))
        L = matrix(i+1,i+1)
        for j in range(i+1):
            for k in range(i+1):
                L[j,k] = CPM[Lind[k]][g+j]
        C = L^(-1)*M
        el = basis[g+1+i]
        for j in range(i+1):
            newcoeffs[i+1,Lind[j]] = C[j][0]
            el = el + C[j][0]*basis[Lind[j]]
        newbasis = newbasis + [el]
    for i in range(g):
        for j in range(i):
            newbasis[g+i] = newbasis[g+i] + CPM[g+i][g-1-j]*newbasis[g+j]
            for k in range(2*g):
                newcoeffs[i,k] = newcoeffs[i][k] + CPM[g+i][g-1-j]*newcoeffs[j][k]
        newbasis[g+i] = newbasis[g+i]/CPM[g-1-i][g+i]
        for k in range(2*g):
                newcoeffs[i,k] = newcoeffs[i][k]/CPM[g-1-i][g+i]
    return newbasis, newcoeffs


def changebasistosymplectic(C):
    """
    Returns a matrix that changes our basis of $H^1_{dR}(C)$ to a
    symplectic basis w.r.t to the cup product; leaving holomorphic
    differentials unchanged
    """
    g = C.genus()
    newbasis, newcoeffs = symplectic_h1dr_basis(C)
    F2 = newcoeffs.list()
    I = identity_matrix(2*g).matrix_from_rows(range(g)).list()
    M = matrix(2*g,2*g, I + F2)
    return M


def changebasistounitroot(C, prec=20):
    """
    Returns a matrix that changes the basis of $H^1_{dR}(C)$: holomorphic 
    differentials stay the same and the complement becomes a basis of the 
    unit-root subspace ($p$ good ordinary) 
    (This subspace is used by default, see "psi_omega_for_infinities" and 
    "psi_forP_mixed_basis").
    """
    K = C.base_ring()
    p = K.prime()
    if not is_ordinary(C, p):
        raise ValueError('Need ordinary reduction for the unit root subspace.')
    g = C.genus()
    FrMW, Fr = matrix_of_frobenius_on_h1mw_h1dr(C, p, prec)
    F = Fr^prec
    F2 = (F.transpose()).matrix_from_rows(range(g,2*g)).list()
    I = identity_matrix(2*g).matrix_from_rows(range(g)).list()
    M = matrix(2*g,2*g, I + F2)
    return M


def opposite_affine_point(P):
    """
    For $P=(x,y)$ on $C$ returns $\iota(P)=(x,-y)$.
    """
    C = P.scheme()
    if P == C(0,1,0):
        return false
    else:
        return C(P[0],-P[1])


def psi_omega_for_infinities(C, prec=20, BasisW = None):
    """
    Computes $\psi(x^gdx/y)$ in the basis consisting of $g$ holomorphic forms 
    $\eta_0,...,\eta_{g-1}$ and the basis of the chosen complementary subspace 
    $W$; BasisW is the matrix of that base change from 
    $\eta_0,...,\eta_{2g-1}$. If BasisW = None and $p$ ordinary, 
    assumes that $W$ is the unit-root subspace with the basis 
    $Frob^{prec}(\eta_g)$,...,$Frob^{prec}(\eta_{2g-1})$.
    """
    K = C.base_ring()
    if not is_even(C.hyperelliptic_polynomials()[0].degree()):
        raise ValueError('Need an even degree model')
    p = K.prime()
    g = C.genus()
    FrMW, Fr = matrix_of_frobenius_on_h1mw_h1dr(C, p, prec)
    M = matrix(C.base_ring(),2*g,1)
    for i in range(g):
        M[i,0] = 2*FrMW[i][g]
    for i in range(g,2*g):
        M[i,0] = 2*FrMW[i+1][g]
    M1 = (Fr-p*identity_matrix(2*g))^(-1) * M
    if BasisW == None:
        if not is_ordinary(C, p):
            raise ValueError('Need ordinary reduction for the unit root subspace.')
        BasisW = changebasistounitroot(C, prec)
    return (BasisW.transpose())^(-1) * M1


def tiny_height_infinities(P, Q, prec=20, M=None, BasisW=None):
    """
    Only works for even degree model. If $P$ and $Q$ are in the same residue disc 
    of an even degree hyperelliptic curve $C$, computes 
    $h_p(\infty_- - \infty_+, P-Q)=\int_{Q}^P x^gdx/y -
      \sum_{i=0}^{g-1} c_i \int_{Q}^P x^i dx/y$, 
    where the integrals are tiny, $c_i$'s are such that 
      $psi(x^gdx/y-\sum_{i=0}^{g-1} c_i x^i dx/y)\in W$.

    HINT: If we want to compute many heights of the shape 
      $h_p(\infty_- - \infty_+, P-Q)$ for various $P,Q\in C(\mathbb{Q}_p)$ 
      (e.g., in quadratic Chabauty), then we always compute an integral of the 
      same differential. Therefore, to save time and memory, one can pass
      the precomputed matrix M that gives the coordinates of $\psi(x^gdx/y)$ 
      in the basis of of $H^1_{dR}(C)$ consisting of
      $\eta_0,...,\eta_{g-1}$ and the given basis of the complementary subspace.
      If we give M as a parameter, we don't need to specify W.

    If we don't give M as a parameter, then we can specify BasisW, 
    which is the matrix of the base change of $H^1_{dR}(C)$ from 
    $\eta_0,...,\eta_{2g-1}$ to $\langle\eta_0,...,\eta_{g-1}\rangle \oplus W$ 
    for any complementary subspace $W$ isotropic w.r.t. the cup product pairing. 
    Then M will be computed with respect to this decomposition of $H^1_{dR}(C)$.

    If BasisW = None, then we assume that $p$ is ordinary and 
    $W$ = the unit root subspace.
    """
    C = P.scheme()
    if not is_even(C.hyperelliptic_polynomials()[0].degree()):
        raise ValueError('Need an even degree model')
    if P == Q:
        return 0
    f = C.hyperelliptic_polynomials()[0]
    g = C.genus()
    if M is None:
        M = psi_omega_for_infinities(C, prec, BasisW)
    PI = C.tiny_integrals_on_basis(Q,P)
    s = 2*PI[g]
    for i in range(g):
        s = s - M[i][0]*PI[i]
    return s


def height_infinities(P, Q, prec=20, M=None, BasisW=None):
    """
    Only works for even degree model. For $P, Q$ on an even degree hyperelliptic 
    curve, this computes
      $h_p(\infty_- - \infty_+, P-Q)=\int_{Q}^P x^gdx/y -
        \sum_{i=0}^{g-1} c_i \int_{Q}^P x^i dx/y$, 
    where $c_i$'s are such that $psi(x^gdx/y-\sum_{i=0}^{g-1} c_i x^i dx/y)\in W$.
    HINT: If we want to compute many heights of the shape 
      $h_p(\infty_- - \infty_+, P-Q)$ for various $P,Q\in C(\mathbb{Q}_p)$ 
      (e.g., in quadratic Chabauty), then we always compute an integral of the 
      same differential. Therefore, to save time and memory, one can pass
      the precomputed matrix M that gives the coordinates of $\psi(x^gdx/y)$ 
      in the mixed basis we choose. If we give M as a parameter, we don't 
      need to specify BasisW.

    If we don't give M as a parameter, then we can specify BasisW, 
    which is the matrix of the base change of $H^1_{dR}(C)$ from 
    $\eta_0,...,\eta_{2g-1}$ to $\langle\eta_0,...,\eta_{g-1}\rangle \oplus W$ 
    for any complementary subspace $W$ isotropic w.r.t. the cup product pairing. 
    Then M will be computed with respect to this decomposition of $H^1_{dR}(C)$.

    If BasisW = None, then we assume that $p$ is ordinary and 
    $W$ = the unit root subspace.

    """
    C = P.scheme()
    if P == Q:
        return 0
    f = C.hyperelliptic_polynomials()[0]
    if not is_even(f.degree()):
        raise ValueError('Need an even degree model')
    if P[0].valuation() < 0 or Q[0].valuation() < 0:
        raise NotImplementedError('This case is not implemented yet. Please let us know if this would be useful for you.')
    if M is None:
        M = psi_omega_for_infinities(C, prec, BasisW)
    g = C.genus()
    PI = coleman_integrals_on_basis_modified(Q,P)
    s = 2*PI[g]
    for i in range(g):
        s = s - M[i][0]*PI[i]
    return s


def height_infinities_residuedisc_to_z(P, prec=20, M=None, BasisW=None):
    """
    Only works for even degree model. Computes $h_p(\infty_- - \infty_+, P(z)-P)$ 
    where $P(z)$ is a parametric point in the residue disc of $P$.
    See above for usage of M and BasisW.
    """
    C = P.scheme()
    f = C.hyperelliptic_polynomials()[0]
    if not is_even(f.degree()):
        raise ValueError('Need an even degree model')
    if P[0].valuation() < 0:
        raise NotImplementedError('This case is not implemented yet. Please let us know if this would be useful for you.')
    g = C.genus()
    if M is None:
        M = psi_omega_for_infinities(C, prec, BasisW)
    PI = C.tiny_integrals_on_basis_to_z(P)
    s = 2*PI[g]
    for i in range(g):
        s = s - M[i][0]*PI[i]
    return s


def height_infinities_first_point_residuedisc_to_z(P, Q, prec=20, M = None, BasisW=None):
    """
    Only works for even degree model. Computes 
    $h_p(\infty_- - \infty_+, P(z)-Q)
     = h_p(\infty_- - \infty_+, P(z)-P)+h_p(\infty_- - \infty_+, P-Q)$,
    where $P(z)$ is a parametric point in the residue disc of $P$.
    See above for usage of M and BasisW.
    """
    C = P.scheme()
    f = C.hyperelliptic_polynomials()[0]
    if not is_even(f.degree()):
        raise ValueError('Need an even degree model')
    if P[0].valuation() < 0 or Q[0].valuation() < 0:
        raise NotImplementedError('This case is not implemented yet. Please let us know if this would be useful for you.')
    return height_infinities_residuedisc_to_z(P, prec, M, BasisW) + height_infinities(P, Q, prec, M, BasisW)


def tiny_integrals_on_basis_parametric(b, z, tadicprec=20):
    """
    Returns all tiny integrals on basis to a parameter z
    AUTHOR:
            - Jennifer Balakrishnan
    """
    C = b.scheme()
    x,y = C.local_coord(b,prec=tadicprec)
    d = C.hyperelliptic_polynomials()[0].degree()
    return [((x**i)*x.derivative()/(2*y)).integral()(z) for i in range(d-1)]


def height_infinities_residuedisc_parametric(P, z, prec=20, tadicprec=20, M=None, BasisW=None):
    """
    Only works for even degree model. Computes $h_p(\infty_- - \infty_+, P(z)-P)$,
    where $P(z)$ is a point in the residue disc of $P$ in the parameter z.
    """
    C = P.scheme()
    f = C.hyperelliptic_polynomials()[0]
    if not is_even(f.degree()):
        raise ValueError('Need an even degree model')
    if P[0].valuation() < 0:
        raise NotImplementedError('This case is not implemented yet. Please let us know if this would be useful for you.')
    g = C.genus()
    PI = tiny_integrals_on_basis_parametric(P, z, tadicprec)
    s = 2*PI[g]
    if M is None:
        M = psi_omega_for_infinities(C, prec, BasisW)
    for i in range(g):
        s = s - M[i][0]*PI[i]
    return s


def height_infinities_first_point_residuedisc_parametric(P, Q, z, prec=20, tadicprec=20, M=None, BasisW=None):
    """
    Only works for even degree model. Computes 
    $h_p(\infty_- - \infty_+, P(z)-Q)
      =h_p(\infty_- - \infty_+, P(z)-P)+h_p(\infty_- - \infty_+, P-Q)$, 
    where $P(z)$ is a point in the residue disc of $P$ in the parameter z.
    """
    C = P.scheme()
    f = C.hyperelliptic_polynomials()[0]
    if not is_even(f.degree()):
        raise ValueError('Need an even degree model')
    if P[0].valuation() < 0 or Q[0].valuation() < 0:
        raise NotImplementedError('This case is not implemented yet. Please let us know if this would be useful for you.')
    return height_infinities_residuedisc_parametric(P, z, prec, tadicprec, M, BasisW) + height_infinities(P, Q, prec, M, BasisW)


def weierstrass_point_in_disc(P):
    """
    For a point $P$ in a Weierstrass disc, returns the Weierstrass point 
    in that disc.
    """
    C = P.scheme()
    K = C.base_ring()
    p = K.prime()
    if mod(P[1],p) != 0:
        raise ValueError('Point not in a Weierstrass disc')
    for Q in C.weierstrass_points():
        if (Q != C(0,1,0)) & (mod(P[0]-Q[0],p) == 0):
            return Q


def is_in_weierstrass_disc2(P):
    """
    Checks whether $P\in C(\mathbb{Q}_p)$ is in a Weierstrass disc.
    """
    C = P.scheme()
    f = C.hyperelliptic_polynomials()[0]
    if mod(f.degree(),2) == 1:
        return C.is_in_weierstrass_disc(P)
    K = C.base_ring()
    p = K.prime()
    if (P[0].valuation() < 0):
        return false
    return C.is_in_weierstrass_disc(P)


def coleman_integrals_on_basis_modified(Q, P):
    """
    Same as coleman_integrals_on_basis, except that it allows endpoints to be in 
    Weierstrass residue discs.
    """
    C = P.scheme()
    if is_in_weierstrass_disc2(P):
        W = weierstrass_point_in_disc(P)
        col_ints = C.coleman_integrals_on_basis(Q,W)
        tiny_ints = C.tiny_integrals_on_basis(W,P)
        return col_ints + tiny_ints
    if is_in_weierstrass_disc2(Q):
        W = weierstrass_point_in_disc(Q)
        col_ints = C.coleman_integrals_on_basis(W,P)
        tiny_ints = C.tiny_integrals_on_basis(Q,W)
        return col_ints + tiny_ints
    return C.coleman_integrals_on_basis(Q,P)


def psi_forP_H1dR(P):
    """
    Computes $\psi(y(P)/(x-x(P))dx/y)$ in our $H^1_{dR}(C)$ basis for a 
    non-Weierstrass point $P$.
    """
    C = P.scheme()
    g = C.genus()
    basis = h1dr_basis(C)
    f = C.hyperelliptic_polynomials()[0]
    N = cup_product_matrix(C, basis)
    NP = opposite_affine_point(P)
    PI = coleman_integrals_on_basis_modified(NP,P)
    M = matrix(C.base_ring(),2*g,1)
    w = [0 for i in range(2*g)]
    for i in range(2*g):
        coeffs = basis[i].coeffs()[0][0]  # x-coefficients of the ith basis element
        M[i,0] = 0
        for j in range(f.degree()-1):
            if coeffs[j] != 0:
                M[i,0] = M[i,0] + coeffs[j]*PI[j]
    return N^(-1)*M


def psi_forP_mixed_basis(P, prec=20, BasisW = None):
    """
    Computes $\psi(y(P)/(x-x(P))dx/y)$ in the mixed basis of holomorphic forms 
    and a basis for $W$ = the complementary space to the holomorphic forms
    specified by the base change matrix BasisW. If no such
    matrix is specified and $p$ is good ordinary, assumes $W$ = the unit root 
    subspace with basis $Frob^{prec}(\eta_g),...,Frob^{prec}(\eta_{2g-1})$.
    """
    C = P.scheme()
    g = C.genus()
    K = C.base_ring()
    p = K.prime()
    M = psi_forP_H1dR(P)
    f = C.hyperelliptic_polynomials()[0]
    if BasisW is None:
        if not is_ordinary(C, p):
            raise ValueError('Need ordinary reduction for the unit root subspace.')
        BasisW = changebasistounitroot(C, prec)
    return (BasisW.transpose())^(-1) * M


def Coleman_Integral_third_kind_antisymmetric(P, R, S):
    """
    Computes the Coleman integral from $S$ to $R$ of 
    $\omega_P=y(P)/(x-x(P))dx/y$ by changing variables to another curve where 
    the differential we integrate becomes $x^gdx/y$.
    """
    C = P.scheme()
    if C.is_weierstrass(P):
         return 0
    else:
        K = C.base_ring()
        f = C.hyperelliptic_polynomials()[0]
        g = C.genus()
        x = polygen(K)
        T = (x^(2*g+2) * f(P[0]+1/x) * 1/P[1]^2)
        T.reduce()
        # T is guaranteed to be squarefree, so we don't check this,
        # to avoid known sage bugs.
        X = HyperellipticCurve(x.parent()(T), check_squarefree = false)
        R1 = X(1/(R[0]-P[0]), (-1)* R[1]/(P[1]*(R[0]-P[0])^(g+1)))
        S1 = X(1/(S[0]-P[0]), (-1)* S[1]/(P[1]*(S[0]-P[0])^(g+1)))
        return 2*X.coleman_integrals_on_basis(S1,R1)[g]


def height_both_antisymmetric_infinity_disc(P, R, prec=20, BasisW=None):
    """
    Computes $h_p(P-\iota(P), R-\iota(R))$ if $R$ is
    (1) in $\infty$ residue disc if $C$ is odd degree;
    (2) in $\infty_-$ residue disc if $C$ is even degree
    (IMPORTANT: does not work if $P$ is in the disc of $\infty_+$).
    """
    if P[0].valuation() < 0:
        raise NotImplementedError('This case is not implemented yet. Please let us know if this would be useful for you.')
    if R[0].valuation() >= 0:
        raise ValueError('R must be in a disc at infinity')
    p = P.base_ring().prime()
    C = P.scheme()
    NP = opposite_affine_point(P)
    g = C.genus()
    N = psi_forP_mixed_basis(P, prec, BasisW)
    f = C.hyperelliptic_polynomials()[0]
    tadicprec = prec
    while tadicprec+1-floor(log(tadicprec+1, p)) < prec:
        tadicprec = tadicprec + 1
    if f.degree() == 2*g+1:
        x, y = C.local_coordinates_at_infinity(prec=tadicprec)
    if f.degree() == 2*g+2:
        if mod(R[0]^(g+1)/R[1],p) != -1:
            raise ValueError('R must be in the disc of infty_-, not infty_+')
        x, y = local_coordinates_at_infinity_even(C, prec=tadicprec)
        y = -y
    w = P[1]*x.derivative()/((x-P[0])*y)
    F = w.integral()
    if f.degree() == 2*g+1:
        residueintegral = F(R[0]^g/R[1])-F(-R[0]^g/R[1])
        holomorphicintegral = 0
        for i in range(g):
            Fi = (x^i*x.derivative()/(2*y)).integral()
            holomorphicintegral = holomorphicintegral + N[i][0]*(Fi(R[0]^g/R[1])-Fi(-R[0]^g/R[1]))
        return residueintegral - holomorphicintegral
    if f.degree() == 2*g+2:
        M = psi_omega_for_infinities(C, prec, BasisW)
        residueintegral = F(1/R[0])
        holomorphicintegral = sum(N[i][0]*(((x^i*x.derivative()/(2*y)).integral())(1/R[0])) for i in range(g))
        return 2*(residueintegral - holomorphicintegral) + height_infinities(P, NP, prec, M, BasisW)

def same_or_opposite_residue_disc(P,Q):
    """
    For two affine points $P$ and $Q$, returns if they are in same or the 
    opposite residue disc (w.r.t. the hyperelliptic involution).
    """
    p = P.base_ring().prime()
    if (P[0].valuation() < 0) & (Q[0].valuation() < 0):
        return true
    if (P[0].valuation() >= 0) & (Q[0].valuation() >= 0):
        if (mod(P[0]-Q[0], p) == 0):
            return true
        return false
    return false

def height_both_antisymmetric(P, R, prec=20, BasisW=None):
    """
    Computes $h_p(P-\iota(P), R-\iota(R))$.
    """
    if same_or_opposite_residue_disc(P,R):
        raise NotImplementedError('This case is not implemented yet. Please let us know if this would be useful for you.')
    p = P.base_ring().prime()
    C = P.scheme()
    f = C.hyperelliptic_polynomials()[0]
    g = C.genus()
    if (f.degree() == 2*g+1) & (R[0].valuation() < 0):
        return height_both_antisymmetric_infinity_disc(P, R, prec, BasisW)
    if is_in_weierstrass_disc2(P) & (is_in_weierstrass_disc2(R) == false):
        return height_both_antisymmetric(R, P, prec, BasisW)
    if P[0].valuation() < 0:
        return height_both_antisymmetric(R, P, prec, BasisW)
    if R[0].valuation() < 0:
        if mod(R[0]^(g+1)/R[1],p) == -1:
            return height_both_antisymmetric_infinity_disc(P, R, prec, BasisW)
        if mod(R[0]^(g+1)/R[1],p) == 1:
            NR = opposite_affine_point(R)
            return (-1)*height_both_antisymmetric_infinity_disc(P, NR, prec, BasisW)
    NR = opposite_affine_point(R)
    N = psi_forP_mixed_basis(P, prec, BasisW)
    if is_in_weierstrass_disc2(R):
        tadicprec = prec
        while tadicprec+1-floor(log(tadicprec+1, p)) < prec:
            tadicprec = tadicprec + 1
        TinyIntegralsR = C.tiny_integrals_on_basis(NR,R)
        W = weierstrass_point_in_disc(R)
        x, y = C.local_coord(W, prec=tadicprec)
        w = P[1]*x.derivative()/((x-P[0])*y)
        F = w.integral()
        return F(R[1]) - F(NR[1]) - sum(N[i][0]*TinyIntegralsR[i] for i in range(g))
    IntegralsR = C.coleman_integrals_on_basis(NR,R)
    return Coleman_Integral_third_kind_antisymmetric(P, R, NR) - sum(N[i][0]*IntegralsR[i] for i in range(g))


def height_first_antisymmetric(P, R, S, prec=20, BasisW=None):
    """
    Computes $h_p(P-\iota(P), R-S)$.
    """
    if same_or_opposite_residue_disc(P,R) | same_or_opposite_residue_disc(P,S):
        raise NotImplementedError('This case is not implemented yet. Please let us know if this would be useful for you.')
    C = P.scheme()
    if C.is_in_weierstrass_disc(P) or C.is_in_weierstrass_disc(R) or  C.is_in_weierstrass_disc(S):
        hpr = height_both_antisymmetric(P, R, prec, BasisW)
        hps = height_both_antisymmetric(P, S, prec, BasisW)
        return 1/2 * hpr - 1/2 * hps
    g = C.genus()
    IntegralRS = C.coleman_integrals_on_basis(S,R)
    N = psi_forP_mixed_basis(P, prec, BasisW)
    colintPRS = Coleman_Integral_third_kind_antisymmetric(P, R, S)
    return colintPRS - sum(N[i][0]*IntegralRS[i] for i in range(g))

def height_four_affine_points(P, Q, R, S, prec=20, BasisW=None):
    """
    Computes $h_p(P-Q, R-S)$ using the symmetric-antisymmetric decomposition of
    the first divisor to reduce to the previous cases. When necessary, we use other 
    properties, such as symmetry, or tiny integrals, to reduce the computation of 
    $h_p(P-Q, R-S)$ to the cases implemented above.
    Condition: $P$ and $Q$ belong to different residue discs than those of $R$, 
    $\iota(R)$, $S$ and $\iota(S)$.
    We recall here: BasisW is the matrix of the base change of 
    $H^1_{dR}(C)$ from $\eta_0,...,\eta_{2g-1}$ to 
    $\langle\eta_0,...,\eta_{g-1}\rangle \oplus W$ for a complementary
    subspace $W$, isotropic w.r.t. the cup product pairing. 
    Then M will be computed with respect to this decomposition of $H^1_{dR}(C)$.
    If BasisW = None, then we assume that $p$ is ordinary and 
    $W$ = the unit root subspace.


    Precision: prec is the target precision; the precision of the result 
    may be lower, but the result is guaranteed to be correct to its 
    precision. However, the precision of the result cannot exceed the 
    precision of the curve $C$; to get higher precision of the result, 
    increase the precision of $C$.
    """
    if P in [R,S] or Q in [R,S]:
        raise ValueError('Need disjoint support')
    if P == Q or R == S:
        return 0
    if same_or_opposite_residue_disc(P,R) | same_or_opposite_residue_disc(P,S) | same_or_opposite_residue_disc(Q,R) | same_or_opposite_residue_disc(Q,S):
        raise NotImplementedError('This case is not implemented yet. Please let us know if this would be useful for you.')
    C = P.scheme()
    K = C.base_ring()
    b = (R[0]-P[0]) * (R[0]-Q[0])^(-1) * (S[0]-Q[0]) * (S[0]-P[0])^(-1)
    logsympart = K(b).log(p_branch=0)
    hasp = height_first_antisymmetric(P, R, S, prec, BasisW)
    hasq = height_first_antisymmetric(Q, R, S, prec, BasisW)
    return 1/2 * (logsympart + hasp - hasq)


def height_infinity_three_affine_points(Q, R, S, prec=20, BasisW=None):
    """
    For an odd degree hyperelliptic curve $C$, computes $h_p(\infty-Q, R-S)$ 
    using a symmetric-antisymmetric decomposition of the first divisor.
    """
    if R == S:
        return 0
    if R[0].valuation() < 0 | S[0].valuation() < 0 | same_or_opposite_residue_disc(Q,R) | same_or_opposite_residue_disc(Q,S):
        raise NotImplementedError('This case is not implemented yet. Please let us know if this would be useful for you.')
    C = Q.scheme()
    f = C.hyperelliptic_polynomials()[0]
    if not is_odd(f.degree()):
        raise ValueError('Need an odd degree model')
    K = C.base_ring()
    b = (S[0]-Q[0]) * (R[0]-Q[0])^(-1)
    logsympart = K(b).log(p_branch=0)
    return 1/2 * (logsympart - height_first_antisymmetric(Q, R, S, prec, BasisW))


def height_infinity_minus_three_affine_points(Q, R, S, prec=20, BasisW=None):
    """
    For an even degree hyperelliptic curve $C$, computes $h_p(\infty_- -Q, R-S)$ 
    using a symmetric-antisymmetric decomposition of the first divisor.
    """
    if R == S:
        return 0
    if R[0].valuation() < 0 | S[0].valuation() < 0 | same_or_opposite_residue_disc(Q,R) | same_or_opposite_residue_disc(Q,S):
        raise NotImplementedError('This case is not implemented yet. Please let us know if this would be useful for you.')
    C = Q.scheme()
    f = C.hyperelliptic_polynomials()[0]
    if not is_even(f.degree()):
        raise ValueError('Need an even degree model')
    K = C.base_ring()
    b = (S[0]-Q[0]) * (R[0]-Q[0])^(-1)
    logsympart = K(b).log(p_branch=0)
    return 1/2 * (logsympart + height_infinities(R, S, prec, BasisW) - height_first_antisymmetric(Q, R, S, prec, BasisW))


def height_infinity_plus_three_affine_points(Q, R, S, prec=20, BasisW=None):
    """
    For an even degree hyperelliptic curve $C$, computes 
    $h_p(\infty_+ -Q, R-S)$ by reducing to 
    $h_p(\infty_- -\iota(Q), \iota(R)-\iota(S))$.
    """
    if R == S:
        return 0
    if R[0].valuation() < 0 | S[0].valuation() < 0 | same_or_opposite_residue_disc(Q,R) | same_or_opposite_residue_disc(Q,S):
        raise NotImplementedError('This case is not implemented yet. Please let us know if this would be useful for you.')
    C = Q.scheme()
    f = C.hyperelliptic_polynomials()[0]
    if not is_even(f.degree()):
        raise ValueError('Need an even degree model')
    NQ = opposite_affine_point(Q)
    NR = opposite_affine_point(R)
    NS = opposite_affine_point(S)
    return height_infinity_minus_three_affine_points(NQ, NR, NS, prec, BasisW)


def SplitDivisorsDegreeZero(div):
    """
    Represents div = divisor of degree zero as a sum of $(P-Q)$.
    """
    n = len(div)
    k = sum(div[i][0] for i in range(n))
    if k != 0:
        return "Works only for divisors of degree zero!"
    if n == 2 and div[0][0] == 1 and div[1][0] == -1:
        return [div]
    elif n == 2 and div[0][0] == -1 and div[1][0] == 1:
        return [[div[1], div[0]]]
    else:
        i = 0
        while div[0][0]*div[i][0] > 0:
            i = i + 1
        L = SplitDivisorsDegreeZero([(sgn(div[0][0]),div[0][1]),(sgn(div[i][0]),div[i][1])])
        di = list(div[i])
        di[0] = div[i][0]-sgn(div[i][0])
        if di[0] == 0:
            div.remove(div[i])
        else:
            div[i] = tuple(di)
        d0 = list(div[0])
        d0[0] = div[0][0]-sgn(div[0][0])
        if d0[0] == 0:
            div.remove(div[0])
        else:
            div[0] = tuple(d0)
        return L + SplitDivisorsDegreeZero(div)


def height_divisors(D1, D2, prec=20, BasisW=None):
    """
    Computes $h_p(D1, D2)$ of two divisors of degree zero with disjoint 
    affine support.
    """
    C = D1[0][1].scheme()
    f = C.hyperelliptic_polynomials()[0]
    L1 = SplitDivisorsDegreeZero(D1)
    L2 = SplitDivisorsDegreeZero(D2)
    return sum(height_four_affine_points(L1[i][0][1], L1[i][1][1], L2[j][0][1], L2[j][1][1], prec, BasisW) for i in range(len(L1)) for j in range(len(L2)))


def pair_out(A, B):
    """
    For two lists of the same number of points returns a divisor A-B (of degree zero).
    """
    if len(A) == len(B):
        return [(1, A[i]) for i in range(len(A))] + [(-1, B[j]) for j in range(len(B))]
    else:
        return false


def move_to_monic1(C, L):
    """
    This function works only for even models $C:y^2=f(x)$. It checks if the leading 
    coefficient of $f$ is a square in $\mathbb{Q}_p$. If it is, we return an 
    monic curve $X$ isomorphic to $C$. 
    The other input is a list of lists of points $[[P_{i,j}]]$ on $C$. We return 
    the list $L'=[[P'_{i,j}]]$ of their images on $X$ under the isomorphism
    from $C$ to $X$.
    In practice, we do that in the following cases: (here we abuse notation for 
    points at infinity for non-monic models with obvious meaning):
    * $L = [[P_1,Q_1],\ldots,[P_n,Q_n]]$ and we want to compute 
      $h_p(\infty_- - \infty_+, P_1-Q_1), \ldots , h_p(\infty_- - \infty_+, P_n-Q_n)$ 
      on $C$. Instead, we can compute 
      $h_p(\infty_- - \infty_+, P'_1-Q'_1), \ldots , h_p(\infty_- - \infty_+, P'_n-Q'_n)$ 
      on $X$.
    * $L = [[P_1,Q_1,R_1,S_1],\ldots,[P_n,Q_n,R_n,S_n]] and we want to compute 
      $h_p(P_1-Q_1, R_1-S_1), \ldots , h_p(P_n-Q_n, R_n-S_n)$ on $C$. 
      Instead, we can compute 
      $h_p(P'_1-Q'_1, R'_1-S'_1), \ldots , h_p(P'_n-Q'_n, R'_n-S'_n)$ on $X$.
    * $L = [[Q_1,R_1,S_1],\ldots,[Q_n,R_n,S_n]]$ and we want to compute 
      $h_p(\infty_- -Q_1, R_1-S_1), \ldots , h_p(\infty_- -Q_n, R_n-S_n)$ on $C$. 
      Instead, we can compute 
      $h_p(\infty_- -Q'_1, R'_1-S'_1), \ldots , h_p(\infty_- -Q'_n, R'_n-S'_n)$ on $X$.
    * Any other situation for computing hp using the functions above.
    """
    K = C.base_ring()
    f = C.hyperelliptic_polynomials()[0]
    g = C.genus()
    if K(f[2*g+2]).is_square() is false:
        raise NotImplementedError('The leading coefficient of f has to be a square in Qp for this implementation.')
    x = polygen(K)
    X = HyperellipticCurve(sum(f[i]*f[2*g+2]^(2*g+1-i)*x^i for i in range(2*g+3)))
    Lnew = [[X(L[i][j][0]*f[2*g+2], L[i][j][1]*sqrt(K(f[2*g+2]))^(2*g+1)) for j in range(len(L[i]))] for i in range(len(L))]
    return X, Lnew


def move_to_monic2(C, P, L):
    """
    This function returns a monic even model of $C$ by using the same 
    transformation used in "Coleman_Integral_third_kind_antisymmetric" and
    the images of the points in the list L. 
    The change of variables is made with respect to $P\in C(\mathbb{Q}_p)$, 
    which is not in a Weierstrass disc, nor at infinity discs.
    """
    if C.is_in_weierstrass_disc(P):
         raise NotImplementedError('P must be in a non-Weierstrass disc')
    else:
        K = C.base_ring()
        f = C.hyperelliptic_polynomials()[0]
        g = C.genus()
        x = polygen(K)
        T = (x^(2*g+2) * f(P[0]+1/x) * 1/P[1]^2)
        T.reduce()
        # T is guaranteed to be squarefree, so we don't check this,
        # to avoid known sage bugs.
        X = HyperellipticCurve(x.parent()(T), check_squarefree = false)
        Lnew = [[X(1/(L[i][j][0]-P[0]), (-1)* L[i][j][1]/(P[1]*(L[i][j][0]-P[0])^(g+1))) for j in range(len(L[i]))] for i in range(len(L))]
        return X, Lnew   










