import ast,itertools,json,sys,urllib.request
from pathlib import Path
from math import lcm
from scipy.optimize import linprog
from sympy import Matrix,Rational as R
import numpy as np
SOURCE="https://raw.githubusercontent.com/google/or-tools/ed3741de6401c6f95bbcd30686409f87e17d1b68/ortools/linear_solver/samples/stigler_diet.py"
def source_data():
    path=Path(sys.argv[1]); tree=ast.parse(path.read_text())
    fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=="main")
    vals={}
    for n in ast.walk(fn):
        if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id in ("data","nutrients"):
            vals[n.targets[0].id]=ast.literal_eval(n.value)
    assert len(vals["data"])==77 and len(vals["nutrients"])==9
    return [[R(str(food[k+3])) for food in vals["data"]] for k in range(9)],[R(str(a[1])) for a in vals["nutrients"]]
def solve(A,b,banned):
    cols=[j for j in range(77) if j not in banned]
    mat=np.array([[float(A[i][j]) for j in cols] for i in range(9)])
    r=linprog(np.ones(len(cols)),A_ub=-mat,b_ub=-np.array(list(map(float,b))),bounds=(0,None),method="highs")
    assert r.success,r.message
    pos=[cols[k] for k,v in enumerate(r.x) if v>1e-8]
    tight=[i for i in range(9) if abs(float((mat@r.x)[i]-float(b[i])))<3e-7]
    for z in itertools.combinations(tight,len(pos)):
        H=Matrix([[A[i][j] for j in pos] for i in z])
        if H.det()==0:continue
        v=H.inv()*Matrix([b[i] for i in z]);d=H.T.inv()*Matrix([R(1)]*len(pos))
        if any(t<=0 for t in v) or any(t<0 for t in d):continue
        x={j:v[k] for k,j in enumerate(pos)};y=[R(0)]*9
        for i,t in zip(z,d):y[i]=t
        if any(sum(A[i][j]*y[i] for i in range(9))>1 for j in cols):continue
        if any(sum(A[i][j]*x[j] for j in pos)<b[i] for i in range(9)):continue
        if sum(x.values())!=sum(b[i]*y[i] for i in range(9)):continue
        return x,y
    raise RuntimeError("exact witness reconstruction failed")
def arr(xs):return "["+",".join(map(str,xs))+"]"
def emit(A,b,banned,x,y,index,good,out):
    Aint=[[int(t*10) for t in row] for row in A]; bi=[int(v*10) for v in b]
    E=lcm(*(int(t.q) for t in y));yi=[int(t*E) for t in y]
    D=lcm(*(int(t.q) for t in x.values()));xi=[int(x.get(j,R(0))*D) for j in range(77)]
    assert all(sum(Aint[i][j]*xi[j] for j in range(77))>=bi[i]*D for i in range(9))
    assert all(sum(Aint[i][j]*yi[i] for i in range(9))<=10*E for j in range(77) if j not in banned)
    head=f"""import ExactRepairCheckerV1
namespace Stigler{index:02}
open InsacermoExactRepair
def mat : List (List Nat) := {arr([arr(a) for a in Aint])}
def rhs : List Nat := {arr(bi)}
def banned : List Nat := {arr(sorted(banned))}
def a : Nat → Nat → Nat := fun i j => ((mat[i]?).getD [])[j]?.getD 0
def req : Nat → Nat := fun i => (rhs[i]?).getD 0
def allowed : Nat → Bool := fun j => !(banned.contains j)
def yw : List Nat := {arr(yi)}
def y : Nat → Nat := fun i => (yw[i]?).getD 0
def E : Nat := {E}
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
theorem shape : mat.length = 9 ∧ rhs.length = 9 ∧ mat.all (fun row => row.length == 77) = true := by
  decide +kernel
"""
    if good:
        assert 365*sum(xi)<=40*D
        tail=f"""def xw : List Nat := {arr(xi)}
def x : Nat → Nat := fun j => (xw[j]?).getD 0
def D : Nat := {D}
theorem primal_ok : checkPrimal 9 77 a req allowed x D = true := by
  decide +kernel
theorem price_ok : 365 * sumN 77 x ≤ 40 * D := by
  decide +kernel
theorem feasible : PrimalValid (m := 9) (n := 77) a req allowed x D ∧ 365 * sumN 77 x ≤ 40 * D :=
  ⟨checked_primal_sound 9 77 a req allowed x D primal_ok, price_ok⟩
"""
    else:
        assert 40*10*E<365*sum(bi[i]*yi[i] for i in range(9))
        tail="""theorem dual_ok : checkDual 9 77 a allowed y E = true := by
  decide +kernel
theorem gap : 40 * (10 * E) < 365 * sumN 9 (fun i => req i * y i) := by
  decide +kernel
theorem no_plan (D : Nat) (hD : D > 0) (x : Nat → Nat)
    (hp : PrimalValid (m := 9) (n := 77) a req allowed x D) :
    ¬ (365 * sumN 77 x ≤ 40 * D) :=
  checked_budget_impossible 9 77 a req allowed y E dual_ok gap D hD x hp
"""
    (out/f"Stigler{index:02}.lean").write_text(head+tail+f"end Stigler{index:02}\n")
def main():
    A,b=source_data()
    baseline,_=solve(A,b,set());special=sorted(baseline)
    assert special==[0,29,45,51,68],special
    out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
    cases=[]
    for k in range(6):
        for subset in itertools.combinations(special,k):
            banned=set(special)-set(subset);x,y=solve(A,b,banned)
            cost=sum(x.values())
            cases.append((k,subset,banned,x,y,cost))
    assert len(cases)==32
    impossible=[c for c in cases if c[0]<=3]
    feasible=[c for c in cases if c[0]==4 and 365*c[5]<=40]
    assert len(impossible)==26 and len(feasible)==1
    assert all(365*c[5]>40 for c in impossible)
    for i,(_,_,banned,x,y,_) in enumerate(impossible+feasible):
        emit(A,b,banned,x,y,i,i==26,out)
    print("REAL RAW-TO-PROOF: 77 foods, 9 nutrients, 32 audited, 27 Lean witnesses emitted")
    print("Annual cost of feasible 4-repair:",float(365*feasible[0][5]))
if __name__=="__main__": main()
