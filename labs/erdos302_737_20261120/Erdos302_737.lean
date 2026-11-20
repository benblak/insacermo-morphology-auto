import Lean

/-!
INSACERMO — ONE finite theorem about Erdős Problem 302.
For n=737, show no distinct positive a<c<737 satisfy
  1/a = 1/c + 1/737.
Clearing denominators gives
  (737-a)*c = 737*a.
The necessary exact-divisibility test is exhaustively checked for a=1..736.
The extremal corollary f(737)=f(736)+1 follows mathematically since
737 is in no forbidden triple on {1,...,737}.
This is a local finite result, NOT the open asymptotic Erdős conjecture.
-/
namespace INSACERMO.Erdos302

def canComplete (a : Nat) : Bool :=
  let denom := 737 - a
  0 < a && a < 737 &&
  (737*a) % denom == 0 &&
  a < (737*a)/denom &&
  (737*a)/denom < 737

def anyTripleWithLargest737 : Bool :=
  (List.range 736).any (fun k => canComplete (k+1))

theorem no_forbidden_triple_using_737 :
    anyTripleWithLargest737 = false := by
  decide +kernel

-- Independent factor certificate:
-- 737 = 11 * 67, 737² has no divisors strictly between 737/2 and 737.
-- This certifies the same absence without searching over all triples.
def properGapDivisor : Bool :=
  ((List.range 368).map (fun k => k+369)).any
    (fun d => 737*737 % d == 0)

theorem divisor_gap_737 :
    properGapDivisor = false := by
  decide +kernel

end INSACERMO.Erdos302
