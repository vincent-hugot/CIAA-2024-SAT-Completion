from dataclasses import dataclass
from functools import reduce
from itertools import chain
from toolkit import fset, fresh_gen, base_case_gen, elapsed, disjoint_sets



@dataclass(frozen=True)
class MultOp:
    l: list

class And_(MultOp): pass
class Or_ (MultOp): pass

@dataclass(frozen=True)
class BinOp:
    l: object
    r: object

class And       (BinOp):
    symb = "∧"; lsymb = r"\land"
class Or        (BinOp):
    symb = "∨"; lsymb = r"\lor"
class Implies   (BinOp):
    symb = "⇒"; lsymb = r"\simplies"
class Equiv     (BinOp):
    symb = "⇔"; lsymb = r"\iff"
@dataclass(frozen=True)
class Not:
    f: object

##f = Not(Implies("x", Or("y", "z")))
##print(f)

class Atom: pass

@dataclass(frozen=True)
class Eq (Atom):
    x:str
    y:str
    def __str__(s): return f"{s.x}={s.y}"
    def latex(s,t): return rf"{t(s.x)} \approx {t(s.y)}"

class ATRUE(Atom):
    def __str__(s): return "⊤"
    def latex(s, t): return r"\top"

TRUE = ATRUE()

class AFALSE(Atom):
    def __str__(s): return "⊥"
    def latex(s, t): return r"\bot"

FALSE = AFALSE()

@dataclass(frozen=True)
class Var(Atom): # mostly for Tseytin
    x: object
    def __str__(s): return str(s.x)
    def latex(s, t): return t(s.x)

def unflatten(f):
    def z(f):
        match f:
            case And_(l): return z(reduce(And, base_case_gen(l,TRUE)))
            case Or_ (l): return z(reduce(Or , base_case_gen(l,FALSE)))
            case BinOp(l, r): return type(f)(z(l), z(r))
            case Not(l): return Not(z(l))
            case Atom(): return f
            case _: assert False, f
    return z(f)

def fstr(f):
    match f:
        case BinOp(l,r):    return f"({npfstr(l,f)} {f.symb} {npfstr(r,f)})"
        case Not(f):        return f"¬{fstr(f)}"
        case Atom():        return str(f)
        case MultOp():      return fstr(unflatten(f))
        case _:             raise ValueError(f)

def latex_table(x):
    if isinstance(x, tuple): return rf"\pa{{{','.join(map(latex_table, x))}}}"
    if not isinstance(x, str): return latex_table(str(x))
    return  {
     '0': "p_0", 'q⊥': r"q_\bot", "qf": "q_f"
    }.get(x, x)

def latex(f, tab=latex_table):
    z = latex
    match f:
        case BinOp(l,r):    return f"({npfstr(l,f,z)} {f.lsymb} {npfstr(r,f,z)})"
        case Not(f):        return fr"\neg{z(f)}"
        case Atom():        return f.latex(tab)
        case MultOp():      return z(unflatten(f))
        case _:             raise ValueError(f)

def strip_parenths(s): return s[1:-1] if s[0]=="(" and s[-1]==")" else s

def npfstr(f,parent, fun=fstr):
    return strip_parenths(fun(f)) if type(f) is type(parent) and type(f) in [And, Or] else fun(f)

def leval(f, v):
    """evaluate given valuation:
    v: collection of True variables"""
    def x(var): return True if var in v else False
    def z(f):
        match f:
            case And(l,r): return z(l) and z(r)
            case Or(l,r): return z(l) or z(r)
            case Implies(l,r): return z(r) if z(l) else True
            case Equiv(l,r): return z(l) == z(r)
            case Not(l): return not z(l)
            case Var() | Eq(): return x(f)
            case ATRUE(): return True
            case AFALSE(): return False
            case MultOp(): return z(unflatten(f))
            case _: assert False, f
    return z(f)


def rmimp(f):
    match f:
        case Equiv(l,r):
            rl, rr = rmimp(l), rmimp(r)
            return And( Or(Not(rl), rr) , Or(Not(rr), rl) )
        case Implies(l,r):  return Or(Not(rmimp(l)), rmimp(r))
        case BinOp(l,r):    return type(f)(rmimp(l), rmimp(r))
        case Not(f):        return Not(rmimp(f))
        case Atom():        return f
        case MultOp():      return rmimp(unflatten(f))
        case _:             raise ValueError(f, type(f))

def size(f):
    z = size
    match f:
        case MultOp(l):     return 1 + sum(z(e) for e in l)
        case BinOp(l,r):    return 1 + z(l) + z(r)
        case Not(f):        return 1 + z(f)
        case Atom():        return 1
        case _:             raise ValueError(f)


def subformulae(f):
    "generates subformulae in postorder, no duplicates"
    seen = set()
    def z(f):
        match f:
            case BinOp(l,r):    yield from z(l) ; yield from z(r)
            case Not(g):        yield from z(g)
            case Atom():        pass
            case _:             raise ValueError(f)
        if f not in seen:
            seen.add(f)
            yield f
    yield from z(f)

def substitute_dict(f, d):
    "in f, substitute outermost occurences of g in d by d[g]"
    def z(f):
        if f in d: return d[f]
        match f:
            case BinOp(l,r): return type(f)(z(l), z(r))
            case Not(x):     return Not(z(x))
            case Atom():     return f
            case _:          raise ValueError(f)
    return z(f)

def Tseytin_var(i): return Var(f"τ{i}")

def is_Tseytin_var(f):
    match f:
        case Var(s) if s.startswith("τ"): return True
        case _: return False

def _Tseytin_subformulae(f):
    "return {subformula : Tseytin variable}"
    d = {}; dt = {} # raw- and T- subformulae
    i = 0
    def z(f):
        nonlocal i
        match f:
            case BinOp(l,r):    z(l) ; z(r)
            case Not(g):        z(g)
            case Atom():        return
            case _:             raise ValueError(f)
        if f not in d:
            v = Tseytin_var(i)
            i += 1
            dt[substitute_dict(f, d)] = v
            d[f] = v

    z(f); return dt

def Tseytin_dedup(f):
    "assumes no Tseytin variables in formula"
    d = _Tseytin_subformulae(f)
    last = d[next(reversed(d))]
    return And( last, reduce(And, ( Equiv(v,f) for f,v in d.items() )) )


def Tseytin(f):
    g = map(Tseytin_var,fresh_gen([0]))
    def get_var(f):
        if isinstance(f, Atom): return f,[]
        v = next(g)
        return v, [z(f, v)]
    def z(f, i):
        match f:
            case BinOp(l,r):
                (vl,X) , (vr,Y) = get_var(l), get_var(r)
                yield Equiv(i, type(f)(vl, vr))
                for x in X+Y: yield from x
            case Not(l):
                v,X = get_var(l)
                yield Equiv(i, Not(v))
                for x in X: yield from x
            case Atom(): yield f
            case _: assert False, f
    start = next(g)
    return And(start, reduce(And, z(f,start)))

def to_sclauses(f):
    """formula -> solvers [[int]] CNF clauses list, int -> varname, tvars set
    Implements Tseytsin directly and brutally
    """
    g = fresh_gen((0,))
    vT, vF = next(g), next(g) # variables for TRUE and FALSSE
    tvars = {vT, vF} # Tseytin and structural variables
    vars = {} # variable -> int
    def register(var):
        if var in vars: return vars[var]
        i = next(g); vars[var] = i; return i

    def get_var(f): # subformula -> int, [generators for below]
        match f:
            case Not() | BinOp() | MultOp(): i = next(g); return i, [z(f, i)]
            case Var() | Eq(): return register(f),[]
            case ATRUE(): return vT, []
            case AFALSE(): return vF, []
            case _: assert False, f

    def z(f, i):
        tvars.add(i)
        match f:
            case BinOp(l, r):
                (l, L), (r, R) = get_var(l), get_var(r)
                match f:  # CNF clauses
                    case And():     yield from [[-i, l], [-i, r], [i, -l, -r]]
                    case Or():      yield from [[-i, l, r], [-l, i], [-r, i]]
                    case Implies(): yield from [[-i, -l, r], [i, l], [-r, i]]
                    case Equiv():   yield from [[-i, -l, r], [-i, l, -r], [i, l, r], [i, -l, -r]]
                for x in L + R: yield from x

            case Not(l):
                l, L = get_var(l)
                yield from [[-i, -l], [i, l]]
                for x in L: yield from x

            case Atom():
                v,_ = get_var(f)
                yield from [ [-i, v], [i, -v] ]

            case And_(l): #yield from z(unflatten(f), i)
                vars, recs = zip(*map(get_var,l))
                yield [i]+[ -v for v in vars]
                yield from ( [-i,v] for v in vars )
                for [x] in (e for e in recs if e): yield from x

            case Or_(l):  #yield from z(unflatten(f), i)
                vars, recs = zip(*map(get_var, l))
                yield [-i] + list(vars)
                yield from ([i, -v] for v in vars)
                for [x] in (e for e in recs if e): yield from x

            case _: assert False, f

    return [[vT], [-vF], [start := next(g)]] + list(z(f,start)), vars, tvars



def fixpoint(f, e):
    res = f(e)
    if res != e: return fixpoint(f, res)
    return res


def simp(f):
    f = unflatten(f)
    def z(f):
        match f:
            case Eq(x,y) if x==y:                   return TRUE
            # case Eq(x,y) if x>y:                    return Eq(y,x) # triangle simplification
            case And(ATRUE(), g) | And(g, ATRUE()): return z(g)
            case Equiv(ATRUE(), g) | Equiv(g, ATRUE()): return z(g)
            case Or(ATRUE(), g) | Or(g, ATRUE()):   return TRUE
            case And(AFALSE(), g) | And(g, AFALSE()): return FALSE
            case Or(AFALSE(), g) | Or(g, AFALSE()):   return z(g)
            case Implies(ATRUE(), g):               return z(g)
            case Implies(g, ATRUE()):               return TRUE
            case BinOp(l, r):                       return type(f)(z(l), z(r))
            case Not(ATRUE()):                      return FALSE
            case Not(AFALSE()):                     return TRUE
            case Not(f):                            return Not(z(f))
            case _:                                 return f
    return fixpoint(z, f)

def nnf(f):
    f = rmimp(f)
    morgan = {And:Or, Or:And}
    def z(f):
        match f:
            case Not(Not(f)):   return z(f)
            case Not(BinOp(l,r) as g):
                return morgan[type(g)](z(Not(l)), z(Not(r)))
            case BinOp(l,r):    return type(f)(z(l), z(r))
            case Not(f):        return Not(z(f))
            case Atom():        return f # curious: z(f) does not raise exception !
            case _:             raise ValueError(f)
    return z(f)

def cnf(f):
    f = nnf(simp(f))
    def z(f): # distribute
        match f:
            case Or(f, And(g, h)):  return And( z(Or(f,g)), z(Or(f, h)) )
            case Or(And(f, g), h):  return And( z(Or(f,h)), z(Or(g, h)) )
            case BinOp(l,r):        return type(f)(z(l), z(r))
            case Not(f):            return Not(z(f))
            case Atom():            return f
            case _:                 raise ValueError(f)
    return fixpoint(z,f)


def _cnf_matrix(f):
    def clauses(f):
        match f:
            case And(f,g): return clauses(f) + clauses(g)
            case _: return [f]
    trans = {} # atom -> int
    i = 0
    def register(lit):
        nonlocal trans,i
        match lit:
            case Eq(_,_) | Var(_):           sign = 1; atom = lit
            case Not(Eq(_,_) | Var(_) as a): sign = -1; atom = a
            case _ : assert False, repr(lit)
        try: return sign*trans[atom]
        except KeyError:
            i += 1
            trans[atom] = i
            return sign*i
    def lits(c): # literals
        match c:
            case Or(f,g): return lits(f) | lits(g)
            case lit: return fset([register(lit)])

    # for c in clauses(f): print("CLAUSE", F(c))
    return { lits(c) for c in clauses(f) }, trans

# def solve_slow(f,v=True):
#     # print("SLOW Input size =", size(f))
#     forig = f
#     # f = cnf(simp(f))
#     with elapsed("SLOW Tseytin time:",v=0):
#         f = simp(cnf(Tseytin(simp(f))))
#     # print("SLOW Tseytin size =", size(f))
#     m, t = _cnf_matrix(f)
#     # print("END CNF MATRIX")
#     def pmod(m):
#         rt = { v:k for (k,v) in t.items() }
#         # return m
#         return [ a for i in m if i > 0 for a in [rt[i]] if not is_Tseytin_var(a) ]
#
#     from pysat.formula import CNF
#     from pysat.solvers import Solver
#
#     with Solver(bootstrap_with=CNF(from_clauses=m)) as solver:
#         with elapsed("SLOW Solver time:",v=0):
#             # print("BEGIN EXTERNAL SOLVER CALL")
#             if not solver.solve(): return None
#             mod = solver.get_model()
#     valuation = pmod(mod)
#     assert leval(forig, valuation), valuation
#     return list(map(F, valuation))

def solve(f, v=False, all=False, allkey=len):
    if v:print("Input size =", size(f))
    with elapsed("Tseytin/to solver clauses time:",v):
        m, vars, tvars = to_sclauses(f)
    if v:print("SClauses size =", sum( len(l) for l in m) )
    def extract_valuation(m):
        rt = {v:k for (k, v) in vars.items()} # reverse transformation int -> var
        return [ rt[i] for i in m if i > 0 if not i in tvars ]

    from pysat.solvers import Solver
    with elapsed("Bootstrap+Solver time:", v):
        with Solver(bootstrap_with=m) as solver:
            with elapsed("Solver time:",v):
                if not solver.solve(): return None
            if all:
                vals = [] # can't make genererator because of solver garbage collection
                for mod in solver.enum_models():
                    val = extract_valuation(mod)
                    assert leval(f, val), val
                    vals.append( list(map(F,val)) )
                return vals if allkey is None else sorted(vals, key=allkey)
            else:
                val = extract_valuation(solver.get_model())
                assert leval(f,val), val
                return list(map(F,val))



def disp(op,s,o): # type dispatch
    if isinstance(o,F): return F(op(s.f, o.f))
    return F(op(s.f, o))

def rdisp(op,s,o):
    if isinstance(o,F): return F(op(o.f, s.f))
    return F(op(o, s.f))

class F:  # object wrapper
    def __init__(s,f):
        assert not isinstance(f,F), f
        s.f  = f
    def __repr__(s):        return npfstr(s.f, s.f)
    def latex(s):           return npfstr(s.f, s.f, latex)
    def __and__(s,o):       return disp(And, s, o)
    def __rand__(s, o):     return rdisp(And, s, o)
    def __or__(s,o):        return disp(Or, s, o)
    def __ror__(s, o):      return rdisp(Or, s, o)
    def __rshift__(s,o):    return disp(Implies, s, o)
    def __rrshift__(s, o):  return rdisp(Implies, s, o)
    def __floordiv__(s, o): return disp(Equiv, s, o)
    def __rfloordiv__(s, o):return rdisp(Equiv, s, o)
    def __neg__(s):         return F(Not(s.f))

    def __eq__(s, o): return s.f == o.f
    def __hash__(s):  return hash(s.f)

    # def __lt__(s,o):return hash(s.f) < hash(o.f)

    @staticmethod
    def unlock_recursion(v=False):
        import resource, sys
        if v:print ("SYS:", resource.getrlimit(resource.RLIMIT_STACK), sys.getrecursionlimit())
        resource.setrlimit(resource.RLIMIT_STACK, [10**9, resource.RLIM_INFINITY])
        sys.setrecursionlimit(10**9)
        if v:print ("SYS:", resource.getrlimit(resource.RLIMIT_STACK), sys.getrecursionlimit())

    @staticmethod
    def And(l):
        return reduce(F.__and__, base_case_gen(l,F.T))

    @staticmethod
    def And_(l):
        l = list(map(F.raw,l))
        if not l: return F.T
        return F( And_(l) ) if len(l) >= 2 else F(l[0])

    @staticmethod
    def Or_(l):
        l = list(map(F.raw, l))
        if not l: return F.F
        return F(Or_(l)) if len(l) >= 2 else F(l[0])

    @staticmethod
    def Or(l):      return reduce(F.__or__, l)

    @staticmethod
    def Eq(x, y):
        if x == y: return F.T
        # if x > y: return F.Eq(y, x)
        return F( Eq(x,y) )

    @staticmethod
    def V(x):       return F( Var(x) )

    def raw(s):     return s.f
    def simp(s):    return F( simp(s.f) )
    def cnf(s):     return F( cnf(s.f) )
    def nnf(s):     return F( nnf(s.f) )
    @property
    def size(s):    return size(s.f)
    def rmimp(s):   return F( rmimp(s.f) )
    def solve_slow(s):  return solve_slow(s.f)
    def eval(s,val):    return leval(s.f, set(map(F.raw, val)))
    def solve(s, *a, **k):      return solve(s.f, *a, **k)
    def subformulae(s):         return (F(f) for f in subformulae(s.f))
    def substitute_dict(s, d):  return F(substitute_dict(s.f, { k.f:v.f for k,v in d.items() } ))
    def Tseytin(s):             return F( Tseytin(s.f) )
    def Tseytin_dedup(s):       return F( Tseytin_dedup(s.f) )
    def to_sclauses(s):         return to_sclauses(s.f)

    @staticmethod
    def eq_classes(sol):
        "given solver solution on x=y type vars, return tuple of eq classes"
        DS = disjoint_sets()
        for e in sol:
            match e.f:
                case Eq(x,y):
                    DS.union(x,y)
        return DS.classes() # tuple -> set, set -> frozenset

    @staticmethod
    def eq_classes_(sols):
        "given list of solver solutions on x=y vars, return list of tuples of eq classes"
        if sols is None: return set()
        return sorted(set(map(F.eq_classes, sols)), key=lambda s: (len(s[0]), len(s)) if s else (0,0))


F.T = F(TRUE)
F.F = F(FALSE)

