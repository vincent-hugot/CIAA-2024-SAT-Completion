import re
from buta import *
from fixpoint import φ_FP, φ_BAD
from tabulate import tabulate
from logic import to_sclauses
from pysat.solvers import Solver
from dataclasses import dataclass
import numpy as np, matplotlib, matplotlib.pyplot as plt, matplotlib.cm as cm

# matplotlib.use("pgf")
# matplotlib.rcParams.update({
#     "pgf.texsystem": "pdflatex",
#     'font.family': 'serif',
#     'text.usetex': True,
#     'pgf.rcfonts': False,
# })

# Af0 = BUTA.spec("""
# qf
# ⊥ q⊥
# f q⊥ qf
# ""","f(⊥)")
# Rfx     = TRS.spec("f(x) -> x")
# Rfax    = TRS.spec("f(x) -> f(a(x))")


def Alist(n):
    """lists of {e1,...,en}"""
    return BUTA({"ql"}, { ("⊥", "ql") } |
                { r for k in map(str,range(n)) for r in [("f", k, "ql", "ql"), (k, k)] },
                name=f"lst({n})")

Rlist = TRS.spec("f(x, y) -> f(y,x)")
Bbottom = BUTA.of_set(["⊥"])

def Adisco(n): return BUTA.of_set(map(str,range(n))).named(f"disco({n})")

def Rlist_d(n, vars=1): # depth
    l = T("f(x, y)")
    r = T("f(y, x)")
    for i in range(n):
        x = f"x{i}" if vars else "0"
        l,r = ("f", x, l), ("f", r, x)
    return TRS( [ (l,r) ])

# print(Rlist_d(2), Rlist_d(2, 0))

def Rlist_m(m): # multiples
    return TRS([ ( ("f", f"x{i}", f"y{i}"), ("f", f"y{i}", f"x{i}") ) for i in range(m) ])

# print(Rlist_m(2))

def mktree(d, ar=2, f="f"):
    return (f, t := mktree(d-1,ar,f), t) if d>1 else (f, "0", "1")

def Rtree(d): return TRS([(l:=mktree(d), l)])
def Rtree(d): return TRS([(l:=mktree(d), ("f", "0", "1"))])
def Rtree(d): return TRS([(("f", "0", "1"), mktree(d) )])

print(Rtree(2))

headers = "Name |A| |R| |B| depthR " \
          "tFP sFP tB sB tF sF " \
          "tCNF sCNF tSolve tTot".split()

def stress(A, R, B=BUTA(), v=0, name=""):
    gc.collect()
    with elapsed() as tTot:
        with elapsed() as tF:
            with elapsed() as tFP: fp = φ_FP(A, R)
            with elapsed() as tB:  fb = φ_BAD(A, B)
            f = fp & fb
            if v: print("F=", f, "\n", "size = ", f.size)
        with elapsed() as tcnf: m,_,_ = to_sclauses(f.f)
        sCNF = sum(len(l) for l in m)
        with elapsed() as tSolve:
            with Solver(bootstrap_with=m) as solver: solver.solve()

    return [name if name else A.name, A.size, R.size, B.size, None,
              tFP(), fp.size, tB(), fb.size, tF(), f.size,
              tcnf(), sCNF, tSolve(), tTot()]

def perform(name, argsgen, tlim = 10, nlim=65):
    import json
    file = Path(name + ".data")
    try:
        r = json.load(open(file))
        print("LOADED", name, len(r)-1, "lines")
    except:
        r = [headers]
        print("RESTART")
    if len(r)-1 < nlim:
        for n,a in enumerate(argsgen):
            if n > nlim or n <= len(r)-1: continue
            r += [ t:=stress(*a) ]
            print("PERFORM:", name, a, t[-1])
            if file.exists(): file.rename(f"{file}.save")
            with open(file, "w") as fi: json.dump(r, fi, indent=1)
            if t[-1] > tlim or n > nlim: break
    globals()[name] = r



def col(tab, vid):
    return transpose(tab)[headers.index(vid)][1:]

def project(tab, *vid):
    return (zip( *(col(tab, i) for i in vid)))

def fun_of_expr(e):
    vars = sorted(set( v for v in re.findall(r"([|A-Za-z]+)", e) if v in headers ))
    return vars, eval(f"lambda {','.join(vars)} : {e}".replace("|","_"))

@dataclass
class FUN: e:str

def plot(tab, xaxis, *y_fmt_s,
         y1lbl="", y2lbl="", y1scl="linear", y2scl="linear",
         title="", fname=""):
    plt.rcParams.update({"font.size": 20, "figure.autolayout":1})  # I need glasses, OK?
    fig, ax1 = plt.subplots(figsize=(12,5)) # 14 12 12
    ax = ax1; ax2 = None
    x = col(tab, xaxis)
    ax1.set_xlabel(xaxis); ax1.set_yscale(y1scl); ax1.set_ylabel(y1lbl)
    fmtcst = "o-"; lw = 2; lblpref= "< " if None in y_fmt_s else ""
    cycler = cycle(cm.tab10.colors)
    for id in y_fmt_s:
        match id:
            case None:
                ax2 = ax1.twinx(); ax=ax2; fmtcst ="s:"; lw=3
                ax2.set_yscale(y2scl); ax2.set_ylabel(y2lbl)
                lblpref = "> "; continue
            # case str():
            #     fmt = fmtcst if len(s := id.split()) == 1 else s[1]
            #     ax.plot(x, col(tab, s[0]), fmt,
            #         color=next(cycler), label=lblpref+s[0], linewidth=lw)
            case (str() as e) | FUN(e):
                vs, f = fun_of_expr(e)
                y = f(*(np.array(col(tab, v), dtype=np.longdouble) for v in vs))
                ax.plot(x, y, fmtcst, #markersize=1,
                        color=next(cycler), label=lblpref + e, linewidth=lw)
            case _: raise ValueError(id)
    plt.title(title)
    h1, l1 = ax1.get_legend_handles_labels()
    h2, l2 = ax2.get_legend_handles_labels() if ax2 else ([],[])
    ax1.legend(h1 + h2, l1 + l2, loc="best")
    # plt.axvline(0); plt.axhline(0) # draw abscissa and ordinate axes
    (figs := Path("paper-formula/figs")).mkdir(parents=1, exist_ok=1)
    if fname: plt.savefig(PP(f"{figs}/{fname}.pdf"), transparent=True, bbox_inches='tight', pad_inches=0)
    plt.show()


def do_plots(tabn, xaxis="|A|", y1scl="log", y2scl="log"):
    tab = globals()[tabn]
    plot(tab, xaxis,
         # "|A|", "1.2 ** np.sqrt(|A|)",
         "tF", "tCNF", "tSolve", "tTot",
         None, "sF", "sCNF",
         y1lbl="s", y2lbl="",
         y1scl=y1scl, y2scl=y2scl,
         title=f"Formulae Computation Times & Sizes ({tabn})",
         fname=f"{tabn}_times")
    plot(tab, xaxis,
         "sCNF / sF", "(sCNF / tCNF) / 1e6",
         None, "tTot / tSolve",
         title=f"Some Useful Ratios ({tabn})",
         fname=f"{tabn}_ratios")

MAX_LINES = 100

import gc

if 0 and __name__ == "__main__":
    perform("tl", ((Alist(k), Rlist) for k in range(1000)), 100, MAX_LINES)
    perform("tl_imp", ((Alist(k), Rlist, Bbottom) for k in range(1000)), 100, MAX_LINES)
    perform("tl2_Rdepth", ((Alist(2), Rlist_d(k)) for k in range(1000)), 100, 8)
    perform("tl3_Rdepth", ((Alist(3), Rlist_d(k)) for k in range(1000)), 100, 5)
    perform("tl2_RdepthXY", ((Alist(2), Rlist_d(k, 0)) for k in range(1000)), 100, 8)
    perform("tl3_RdepthXY", ((Alist(3), Rlist_d(k, 0)) for k in range(1000)), 100, 5)
    perform("tl2_Rm", ((Alist(2), Rlist_m(100*k+1)) for k in range(1000)), 100, MAX_LINES)
    perform("tl_bigbad", ((Alist(2), Rlist, Alist(k)) for k in range(1000)), 100, MAX_LINES)
    perform("td", ((Adisco(k), Rlist) for k in range(1000)), 100, MAX_LINES)
    perform("tl2_Rtree", ((Alist(2), Rtree(k)) for k in range(1000)), 100, 4)
    do_plots("tl", y1scl="linear", y2scl="linear")
    do_plots("tl_imp")
    do_plots("tl2_Rdepth", xaxis="|R|")
    do_plots("tl3_Rdepth", xaxis="|R|")
    do_plots("tl2_RdepthXY", xaxis="|R|")
    do_plots("tl3_RdepthXY", xaxis="|R|")
    do_plots("tl2_Rm", xaxis="|R|", y1scl="linear", y2scl="linear")
    do_plots("tl_bigbad", xaxis="|B|", y1scl="linear", y2scl="linear")
    do_plots("td")
    do_plots("tl2_Rtree", xaxis="|R|")

if __name__ == "__main__":
    perform("tl", ((Alist(k), Rlist) for k in range(1000)), 100, MAX_LINES)
    plot(tl, "|A|","sF", "4 * |A|**3 - 3*|A|**2 - |A|")
    for A,R in ((Alist(k), Rlist) for k in range(3)):
        print(A, R, "", sep="\n")
        stress(A, R, v=1)
        print("="*100)

# print(tabulate(project(tab_list, "|A|", "sCNF")))

# print("\n".join( f"{k}\t{v}" for k,v in project(tab_list, "|A|", "sCNF")))

# print(
# list(
# zip(col(tab_list, "|A|"), ( round(100*n,2) for n in col(tab_list, "tTot")))
# )[:10]
# )