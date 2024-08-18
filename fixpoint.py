# from logic_robdd import F
from logic import F
from buta import BUTA, term, TRS
from itertools import product
from functools import reduce

def unify(A, R:TRS, t, q, L):
    """
    :param A:
    :param R:
    :param t:
    :param q:
    :param L: living states
    :return: U^t_X
    """
    # print("sols", A.name, R, t, X)
    f, *st = t
    def useful(X, Y): return X==Y or {X,Y} & L
    if not(st): # atom
        if f in A.Q:
            return [(F.Eq(q, f), {})] if useful(q, f) else []
        elif evals := A(t):
            return [(F.Eq(q, Y), {}) for Y in evals if useful(q, Y)]
        elif f in R.vars:
            # return [ (F.Eq(p, q), {f:p}) for p in A.Q ] # Adrien breaks everything :-D
            return [(F.T, {f:q})]
        else:
            return [] # particular case of evals; don't think we need FALSE explicitly
            # return [(F.F, {})]
    else: # not atom
        clauses = []
        for (g,*Xk, Y) in A.Δ:
            if g==f: # rule matches
                clauses += product(*([[(F.Eq(q, Y), {})]] + [unify(A, R, ti, Xi, L) for (ti, Xi) in zip(st, Xk)])) if useful(q, Y) else []
        # print("CL", t, X, clauses)
        # print("CLAUSE", clauses)
        def combine(s1,s2):
            (α1,σ1), (α2,σ2) = s1, s2
            assert not set(σ1) & set(σ2)
            return (α1 & α2, σ1 | σ2)
        return [ reduce(combine,c) for c in clauses ]

def commutativity(X): return \
    F.And_( F.Eq(x, y) // F.Eq(y, x) for x, y in product(X, repeat=2) if x < y)

def transitivity(X): return \
    F.And_(
        (F.Eq(x, y) & F.Eq(y, z)) >> F.Eq(x, z)
        for x, y, z in product(X, repeat=3) if x < z and x != y != z
    )

def only_live(A, L):
    return F.And_( -F.Eq(p,q) for p,q in product(A.Q - L, repeat=2) if p < q )

def φ_FP(A : BUTA, R, L=None):
    """
    :param A:
    :param R:
    :param L: Live states
    :return:
    """
    if L is None: L = A.Q
    # trsvars = set.union(*( l.leaves() for l,_ in R.rules )) - { a for a in A.Σ if A.Σ[a] == 0 }
    # print(trsvars)
    # AR = A.copy(); AR.add_rules( (x,q) for x in trsvars for q in A.Q )
    # # print(AR)
    # for l, r in R.rules: print(l, AR(l))
    return F.And_(
        α >> F.Or_(β for β,_ in unify(A, R, r.substitute(σ), X, L))
        for l,r in R.rules
        for X in A.Q
        # for X in AR(l)
        for α,σ in unify(A, R, l, X, L)
        ) & commutativity(A.Q) & transitivity(A.Q) #& only_live(A,L)

def φ_BAD(A:BUTA, B:BUTA):
    P = (A&B)#.print()
    return -F.Or_(  F.V(Qf) for Qf in P.F ) & \
    F.And_(
        F.V(Q) // ( F.Or_( F.Eq(Q[0],Y[0]) & F.And_( F.V(x) for x in X )
                    for (f,*X,Y) in P.Δ if Y[1]==Q[1] ))
    for Q in P.Q
    )