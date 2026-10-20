import Extension734

/-! Exact finite witness, unchanged 608-element set from GitHub witness734.json.
    Excluded values are its complement in 1..734. -/
namespace Erdos302Witness735
open Erdos302Finite Erdos302Extension734
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

def excluded : List Nat := [
  6,10,12,18,20,23,26,28,34,36,40,42,48,50,56,60,66,68,70,72,
  76,78,84,88,90,96,100,102,108,110,112,114,120,124,126,128,
  130,132,134,138,140,142,144,146,148,150,154,156,158,162,164,
  166,168,172,174,176,178,180,182,184,186,188,190,194,195,198,
  200,202,204,206,208,210,212,214,216,218,220,222,226,228,234,
  236,238,240,244,246,247,252,258,260,264,270,272,276,282,286,
  288,294,300,308,318,320,323,330,336,342,348,352,354,366,378,
  442,460,462,480,510,560,580,588,600,630,660,680,690,726,728]

def W (x : Nat) : Bool := decide (0 < x ∧ x ≤ 734 ∧ x ∉ excluded)

theorem W_294 : W 294 = false := by decide +kernel

theorem W_cardinal : fullCardinal W = 608 := by decide +kernel

theorem W_bound (x : Nat) (hx : W x) : 0 < x ∧ x ≤ 734 := by
  have h : 0 < x ∧ x ≤ 734 ∧ x ∉ excluded := by simpa [W] using hx
  exact ⟨h.1, h.2.1⟩


def forbiddenPair (b c : Nat) : Prop :=
  b < c ∧ W b ∧ W c ∧
    (b + c) ∣ b * c ∧
    W (b * c / (b + c)) ∧
    b * c / (b + c) < b

end Erdos302Witness735
