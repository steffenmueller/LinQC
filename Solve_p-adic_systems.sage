def hensel_lift_n(flist, p, prec):
    r"""
    Multivariable Hensel lifter for roots that are simple
    modulo `p`.
    This is essentially the code from [S15] with some minor
    modifications.
    AUTHOR:
            - Francesca Bianchi
    INPUT:
    - ``flist`` -- A list of `n` polynomials in `n` variables
      over a `p`-adic field. Each polynomial should have coefficients in
      `\ZZ_p` and be normalised so that the minimal valaution of its
      coefficients is `0`.
    - ``p`` -- the prime number of the first input item.
    - ``prec`` -- `p`-adic precision. In order for the output to be given
      modulo `p^{prec}`, the coefficients of the polynomials in `flist`
      should be known at least modulo `p^{prec}`.
    OUTPUT:
    A tuple consisting of:
    - A list `L` of common roots in `Qp(p, prec)` of the polynomials in `flist`
      (each root is returned as an `(n x 1)`-matrix, where the `i`-th row
      corresponds to the `i`-th variable).
      Each root in this list lift uniquely to a root in `\QQ_p`.
    - An integer: the number of roots modulo `p` of `flist` for which the
      determinant of the Jacobian matrix vanishes modulo `p`. If this is zero,
      then the `L` contains all the roots of `flist`.
    EXAMPLES:
    An example with no double roots modulo `p`::
        sage: _.<s, t> = PolynomialRing(Qp(5, 10))
        sage: f1 = s + t - 2*s*t
        sage: f2 = s - t
        sage: a, b = hensel_lift_n([f1, f2], 5, 10)
        sage: print a
        [[0]
        [0], [1 + O(5^10)]
        [1 + O(5^10)]]
        sage: print b
        0
    An example with only double roots modulo `p`::
        sage: _.<s,t> = PolynomialRing(Qp(5,10))
        sage: f1 = s - 11* t + 5*s*t
        sage: f2 = s - t
        sage: a, b = hensel_lift_n([f1, f2], 5, 10)
        sage: print a
        []
        sage: print b
        5
    REFERENCES:
    - [S15]: \B. Schmidt, "Solutions to Systems of Multivariate p-adic Power Series".
      Oxford MSc Thesis, 2015.
    """
    precvec = []
    k = 0
    for F in flist:
        R1 = flist[k].parent()
        F1 = R1.base_ring()
        if F1.is_exact():
            precision1 = prec
        else:
            precision1 = F1.precision_cap()
            if prec > F1.precision_cap():
                print('Cannot get %s digits of precision due to precision of inputs of f1; raise precision of inputs' %prec)
            if prec < F1.precision_cap():
                precision1 = prec
        precvec.append(precision1)
        k = k+1
    precision = min(precvec);
    #print 'Precision is', precision
    slist = list(var('s%d' % i) for i in (1..len(flist)))
    s = ''
    for i in range(len(flist)):
        s += str(slist[i])+','
    a = s[0:len(s)-1]
    R = pAdicField(p, precision,'capped-rel')[a]
    flistnew = []
    for F in flist:
        F = R(F)
        flistnew.append(F)
    Jlist=[]
    for F in flistnew:
        for cars in list(flistnew[0].parent().gens()):
            Jlist.append(F.derivative(cars))
    J = matrix(len(flistnew), len(flistnew), Jlist)
    M = J.determinant()
    from itertools import product
    lists = []
    for i in range(len(flistnew)):
        lists.append([j for j in range(p)])
    coords = []
    for items in product(*lists):
        coords.append(items)
    roots = []
    roots_info = []
    nonroots = 0
    for i in range(len(coords)):
        valuesval = [(F(*coords[i]).valuation()) for F in flistnew]
        min_valuesval = min(valuesval)
        ord_det_J = (M(*coords[i])).valuation()
        #if min_valuesval > 2*ord_det_J: #FB: changed this
        if min(valuesval) > 0 and M(*coords[i]).valuation() == 0:
            roots.append(coords[i])
            roots_info.append([min_valuesval - 2*ord_det_J, ord_det_J])
        elif min_valuesval > 0 :
            nonroots += 1

    #print 'Roots =', roots
    actual_roots = []
    for r in roots:
        ind_roots = roots.index(r)
        rt_info = roots_info[ind_roots]
        if rt_info[0] == infinity:
            actual_roots.append(matrix(len(flist), 1, r))
        else:
            variables = []
            k = 0
            i_l = matrix(len(flist), 1, r)
            Jeval = matrix(len(flistnew), len(flistnew), [f(*r) for f in Jlist])

            B = (Jeval.transpose() * Jeval)
            while k < ceil(log(RR((prec-rt_info[1])/rt_info[0]))/log(2.)) + 1 and (Jeval.transpose()*Jeval).determinant() != 0: #FB:changed this
                A = matrix(len(flistnew), 1, [-f(*r) for f in flistnew]);
                i_l = i_l + ~B*Jeval.transpose()*A #NB: ~B*Jeval.transpose() == Jeval.inverse()
                for i in (0..len(flist)-1):
                    variables.append(i_l[i, 0])
                r = variables
                variables = []
                k = k+1;
                Jeval = matrix(len(flistnew), len(flistnew), [f(*r) for f in Jlist])
                #FB: added the following line
                B = (Jeval.transpose() * Jeval)
            actual_roots.append(i_l)

    return actual_roots, nonroots


def two_variable_padic_system_solver(G, H, p, prec1, prec2):
    r"""
    Solve systems of two `p`-adic polynomials in two variables
    by combining naive lifting of roots with the multivariable
    Hensel's lemma. See Appendix A, Algorithm 1 (4) of [BBBM19].
    AUTHOR:
            - Francesca Bianchi
    INPUT:
    - ``G``, ``H`` -- polynomials over `\ZZ_p`, normalised so
      that the minimal valuation of the coefficients is `0`.
    - ``p`` -- the prime of the first input.
    - ``prec1`` -- precision for initial naive lifting.
    - ``prec2`` -- the `p`-adic precision at which we would like to
      compute the roots of `G` and `H`. `prec2` should be at most
      equal to the precision of the coefficients of `G` and `H`.
    OUTPUT:
    A tuple consisting of:
    - A list `L` of common roots in `Qp(p, prec2')^2` of `G` and `H`
      (each root is returned as a `2`-tuple, where the `i`-th entry
      corresponds to the `i`-th variable; prec2' is an integer `\le prec2`).
    - an integer `n`: the number of roots in `L` which might not lift to
      a root in `\QQ_p^2` or might not lift uniquely. In particular, if `n`
      is zero, then there is a bijection between `L` and the common roots of
      `G` and `H`.
      If `n` is positive, then the roots in `L` which force `n` to be
      positive are returned modulo `p^{prec1-3}`.
    EXAMPLES:
    An example with no double roots modulo `p` (the same example as `hensel_lift_n`)::
        sage: _.<s, t> = PolynomialRing(Qp(5, 10))
        sage: f1 = s + t - 2*s*t
        sage: f2 = s - t
        sage: a, b = two_variable_padic_system_solver(f1,f2, 5, 4, 10)
        sage: print a
        [(1 + O(5^10), 1 + O(5^10)), (0, 0)]
        sage: print b
        0
    An example with double roots modulo `p` (the same example as `hensel_lift_n`)::
        sage: _.<s, t> = PolynomialRing(Qp(5, 10))
        sage: f1 = s - 11* t + 5*s*t
        sage: f2 = s - t
        sage: a, b = two_variable_padic_system_solver(f1, f2, 5, 6, 10)
        sage: print a
        [(2 + O(5^5), 2 + O(5^5)), (0, 0)]
        sage: print b
        0
    An example of an actual double root::
        sage: _.<s, t> = PolynomialRing(Qp(5, 10))
        sage: f1 = s*t
        sage: f2 = s - t
        sage: a, b = two_variable_padic_system_solver(f1, f2, 5, 6, 10)
        sage: print a
        [(O(5^3), O(5^3))]
        sage: print b
        1
    """
    K = Qp(p, prec2)
    sols = []
    x,y = G.variables()
    Zxy.<x,y> = PolynomialRing(ZZ)
    gprec = Zxy(G)
    hprec = Zxy(H)

    #Find roots modulo p^prec1 by naive lifting
    for i in range(1, prec1 + 1):
        modulus_one_less = p^(i-1)
        tempsols = []
        temp_new_list = []
        temp_fct_list = []
        if i == 1:
            for k in range(p):
                x1 = GF(p)(k)
                for j in range(p):
                    y1 = GF(p)(j)
                    if gprec(x1, y1) % p == 0:
                        if hprec(x1, y1) % p == 0:
                            tempsols.append(vector([ZZ(x1), ZZ(y1)]))
                            temp_fct_list.append([gprec, hprec])
                            temp_new_list.append(vector([ZZ(x1), ZZ(y1)]))
            sols = tempsols
            fct_list = temp_fct_list
            new_list = temp_new_list
        else:
            for ind in range(len(sols)):
                gnew = Zxy(fct_list[ind][0](sols[ind][0] + p*x, sols[ind][1] + p*y)/p)
                hnew = Zxy(fct_list[ind][1](sols[ind][0] + p*x, sols[ind][1] + p*y)/p)
                for k in range(p):
                    x1 = GF(p)(k)
                    for j in range(p):
                        y1 = GF(p)(j)
                        one = gnew(x1, y1)
                        if one % p == 0:
                            two = hnew(x1, y1)
                            if two % p == 0:
                                xnew = new_list[ind][0] + k*modulus_one_less
                                ynew = new_list[ind][1] + j*modulus_one_less
                                tempsols.append(vector([ZZ(x1), ZZ(y1)]))
                                temp_fct_list.append([gnew, hnew])
                                temp_new_list.append([xnew, ynew])
            sols = tempsols
            fct_list = temp_fct_list
            new_list = temp_new_list

    #Reduce the roots modulo prec1-3 to avoid spurious sols
    sols = [(K(x) + O(p^(prec1-3)), K(y) + O(p^(prec1-3))) for (x,y) in new_list]
    sols = sorted(set(sols))

    #Now apply multivariable Hensel on the roots that are
    #simple modulo prec1-3
    flist = [G,H]
    precvec = []
    k = 0
    for F in flist:
        R1 = flist[k].parent()
        F1 = R1.base_ring()
        if F1.is_exact():
            precision1 = prec2
        else:
            precision1 = F1.precision_cap()
            if prec2 > F1.precision_cap():
                print('Cannot get %s digits of precision due to precision of inputs of f1; raise precision of inputs' %prec)
            if prec2 < F1.precision_cap():
                precision1 = prec2
        precvec.append(precision1)
        k = k+1
    precision = min(precvec);
    #print 'Precision is', precision
    slist = list(var('s%d' % i) for i in (1..len(flist)))
    s = ''
    for i in range(len(flist)):
        s += str(slist[i])+','
    a = s[0:len(s)-1]
    R = Qp(p,precision,'capped-rel')[a]
    flistnew=[]
    for F in flist:
        F = R(F)
        flistnew.append(F)
    Jlist=[]
    for F in flistnew:
        for cars in list(flistnew[0].parent().gens()):
            Jlist.append(F.derivative(cars))
    J = matrix(len(flistnew), len(flistnew), Jlist)
    M = J.determinant()
    from itertools import product
    roots = []
    roots_info = []
    roots2 = []
    for i in range(len(sols)):
        valuesval = [(F(*sols[i]).valuation()) for F in flistnew]
        min_valuesval = min(valuesval)
        ord_det_J = (M(*sols[i])).valuation()
        if min_valuesval > 2*ord_det_J:
            roots.append(sols[i])
            roots_info.append([min_valuesval - 2*ord_det_J,ord_det_J])
        else:
            roots2.append(sols[i])

    actual_roots = list(roots2)
    for r in roots:
        ind_roots = roots.index(r)
        rt_info = roots_info[ind_roots]
        if rt_info[0] == infinity:
            actual_roots.append((K(ZZ(r[0])),K(ZZ(r[1]))))
        else:
            ind_roots = roots.index(r)
            rt_info = roots_info[ind_roots]
            variables = []
            k = 0
            r = [ZZ(r[0]),ZZ(r[1])]
            i_l = matrix(len(flist),1,r)
            Jeval = matrix(len(flistnew),len(flistnew),[f(*r) for f in Jlist])

            B=(Jeval.transpose() * Jeval)
            while k < ceil(log(RR((prec2-rt_info[1])/rt_info[0]))/log(2.))+1 and (Jeval.transpose()*Jeval).determinant() != 0:
                A = matrix(len(flistnew),1,[-f(*r) for f in flistnew]);
                i_l = i_l + ~B*Jeval.transpose()*A
                for i in (0..len(flist)-1):
                    variables.append(i_l[i,0])
                r = variables
                variables = []
                k = k+1;
                Jeval = matrix(len(flistnew), len(flistnew), [f(*r) for f in Jlist])
                #FB: added the following line
                B = (Jeval.transpose() * Jeval)
            actual_roots.append((K(i_l[0][0]), K(i_l[1][0])))

    return actual_roots, len(roots2)
