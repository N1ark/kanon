# usage: pad.py N  -> writes Exp/P{N}/{Lang,Step,Closed,Generic}.lean from Exp/L1 with N extra unary int nodes
import sys, re, os
N = int(sys.argv[1]); R = os.path.dirname(os.path.abspath(__file__)); P = f"P{N}"
os.makedirs(f"{R}/Exp/{P}", exist_ok=True)
for f in ["Lang", "Step", "Closed", "Generic"]:
    s = open(f"{R}/Exp/L1/{f}.lean").read()
    s = s.replace("Exp.L1", f"Exp.{P}").replace("L1.", f"{P}.").replace("l1_", f"p{N}_")
    if f == "Lang":
        s = s.replace("  | OfBool : Term → Kind\n", "  | OfBool : Term → Kind\n" + "".join(f"  | Pad{i} : Term → Kind\n" for i in range(N)))
        s = s.replace("  | .mk (.OfBool a) t => a.ty = .TBool ∧ t = .TInt ∧ a.WT\n",
            "  | .mk (.OfBool a) t => a.ty = .TBool ∧ t = .TInt ∧ a.WT\n" + "".join(f"  | .mk (.Pad{i} a) t => a.ty = .TInt ∧ t = .TInt ∧ a.WT\n" for i in range(N)))
        s = s.replace("  | .mk (.OfBool a) _ => pofbool .int Val.toBool (ev ρ a)\n",
            "  | .mk (.OfBool a) _ => pofbool .int Val.toBool (ev ρ a)\n" + "".join(f"  | .mk (.Pad{i} a) _ => pneg .int Val.toInt (ev ρ a)\n" for i in range(N)))
    if f == "Step":
        s = s.replace("  | .mk (.OfBool _) t, v, w, e => by\n    simp only [ev, Term.WT, pnot, peq, padd, plt, pofbool,",
            "  | .mk (.OfBool _) t, v, w, e" + "".join(f" | .mk (.Pad{i} _) t, v, w, e" for i in range(N)) + " => by\n    simp only [ev, Term.WT, pnot, peq, padd, plt, pofbool, pneg,")
    if f == "Closed":
        s = s.replace("plt, pofbool,", "plt, pofbool, pneg,")
    open(f"{R}/Exp/{P}/{f}.lean", "w").write(s)
