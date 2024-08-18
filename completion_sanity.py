from fixpoint import *
import stress_test

def test(A:BUTA, R:TRS, steps=1, closed=1, prnt_phi=0, avoid=None, avsols=1):
    print("=" * 100)
    print(R)
    A.print()
    Ac = A.complete(R, steps).print()
    live = Ac.Q - A.Q
    print("live states:", live)
    φ = φ_FP(Ac, R, live)
    if prnt_phi: print(x := φ.simp(), "\n", x.latex())
    sols = F.eq_classes_(φ.solve(all=1))
    print(len(sols), "solutions", sols)
    if closed:
        assert sols
        if avoid: AV = avoid if isinstance(avoid, BUTA) else BUTA.of_set(avoid)
        AVcompat = set()
        for n, sol in enumerate(sols,1):
            print(f"~~ FSOL {n}/{len(sols)}", sol)
            Asol = Ac.collapse(sol)
            if avoid:
                if (Asol & AV).is_empty():
                    print("AVOID compatible!")
                    AVcompat.add(sol)
            Asol.print()
            assert Asol.is_complete(R), Asol.completed_rules(R)  # two ways of testing completeness
            assert all( (x:=t) in Asol for t in R.closure(set(A[:10]), tlim=0.01)), x
    else: assert not sols
    ##################################"
    if closed and avoid:
        print("### AVOID:", avoid.name if isinstance(avoid, BUTA) else avoid)
        AV.print()
        # ψB = ψBad(AV, Ac)
        # print("YB φ_BAD =", ψB)
        ψ = φ_BAD(Ac, AV)
        if prnt_phi: print("φ_BAD =", x := ψ.simp(), "\n", x.latex())
        # print("AVcompats:", len(AVcompat), AVcompat)
        sols2 = F.eq_classes_((φ & ψ).solve(all=1))
        print( f"{len(sols2)} of {len(sols)} suitable solutions", sols2)
        assert AVcompat == set(sols2), set(sols2) ^ AVcompat
        assert len(sols2) == avsols, len(sols2)
        for n, sol in enumerate(sols2, 1):
            print(f"** BSOL {n}/{len(sols2)} /{len(sols)}", sol)
            Asol = Ac.collapse(sol).print()
            for t in AV[:100]: assert t not in Asol, t
            for t in Asol[:100]: assert t not in AV, t




Af0 = BUTA.spec("""
qf
⊥ q⊥
f q⊥ qf
""","f(⊥)")
Rfx     = TRS.spec("f(x) -> x")
Rfax    = TRS.spec("f(x) -> f(a(x))")
Rfaax   = TRS.spec("f(x) -> f(a(a(x)))")
Rchain  = TRS.spec("⊥ -> a; a->b; b->c; f(c) -> done")

Aas0 = BUTA.spec("""
q
⊥ q
a q q
""","a*⊥")

Aa = BUTA.spec("""
q
a q
""","a")
Rab     = TRS.spec("a -> b")

Af00 = BUTA.spec("""
qf
⊥ q⊥
f q⊥ q⊥ qf
""","f(⊥,⊥)")
Rfxyab  = TRS.spec("f(x,y) -> f(a(x),b(y))")
Runrea = TRS.spec("f(x,y) -> f(s(x),s(y)); f(s(x),s(y)) -> f(x,y); f(⊥,s(x)) -> a; f(s(x),⊥) -> a")

Af002 = BUTA.spec("""
qf
⊥ q⊥1
⊥ q⊥2
f q⊥1 q⊥2 qf
""","f(⊥,⊥)2")

Afbsas = BUTA.spec("""
qf
⊥ q⊥
a q⊥ qa
b q⊥ qb

a qa qa
b qa qa
b qa qb

a qb qb
a qb qa
b qb qb

f qb qa qf
""","f(.b.,.a.)")

Afbsas = Afbsas | BUTA.of_set(["⊥"])
Afbsas2 = Afbsas | BUTA.of_set(["a(⊥)", "b(⊥)", "f(b(⊥), ⊥)", "f(⊥, a(⊥))", "f(a(⊥), ⊥)", "f(⊥, b(⊥))"])


tests = [
# dict(A=Af0,     R=Rfx), # TODO: fix and add epsilon transitions !!
dict(A=Af00,    R=Runrea,   avoid=["a"], steps=2, closed=0),
dict(A=Af0,     R=Rfax,     avoid=["⊥"]),
dict(A=Af0,     R=Rfax,     avoid=Aas0),
dict(A=Af0,     R=Rfaax,    avoid=["⊥", "f(a(⊥))", "a(⊥)"]),
dict(A=Af002,   R=Rfxyab,   avoid=Afbsas, steps=1),
dict(A=Af00,    R=Rfxyab,   avoid=Afbsas2, steps=2),
dict(A=Aa,      R=Rab,      steps=0, closed=0),
dict(A=Aa,      R=Rab),
dict(A=Af0,     R=Rchain,   steps=3, closed=0),
dict(A=Af0,     R=Rchain,   steps=4, avoid=["⊥"]),
dict(A=stress_test.Alist(1), R=stress_test.Rlist, avoid=["0"]),
dict(A=stress_test.Alist(1), R=stress_test.Rlist, avoid=["⊥"], avsols=0),
]

curated_tests = tests
# curated_tests = [ tests[i] for i in [0] ]

for t in curated_tests: test(**t)