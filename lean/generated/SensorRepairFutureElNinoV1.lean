import FiniteContractCoverKernelV1

namespace INSACERMO.SensorRepairFuture
open INSACERMO.FiniteContractCover
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exactly the formerly indistinguishable pairs at 2C, each mask marking
which 1C ADDITIONAL readings resolve it. Old readings remain retained.
These clauses were exported from 61 historical El Nino rows, 1950-2010. -/
def today : List (List Nat) :=
  [537,1908,792,1920,777,774,79].map
    (fun mask => (List.range 11).filter fun j => mask.testBit j)

def future : List (List Nat) :=
  [110,18,1963,537,1273,820].map
    (fun mask => (List.range 11).filter fun j => mask.testBit j)

/-- JAN and OCT is a two-instrument minimal repair for the present. -/
theorem today_two_upgrades_minimal :
    certifyMinimum 11 today (2^0+2^9) = true := by decide +kernel

theorem today_one_upgrade_impossible :
    certifyCapacityImpossible 11 1 today = true := by decide +kernel

/-- APR, MAY and SEP is a minimum three-instrument repair preserving both
the current DEC>=22 and future DEC>=23 historical decisions. -/
theorem tomorrow_three_upgrades_minimal :
    certifyMinimum 11 (today ++ future) (2^3+2^4+2^8) = true := by decide +kernel

theorem tomorrow_two_upgrades_impossible :
    certifyCapacityImpossible 11 2 (today ++ future) = true := by decide +kernel

end INSACERMO.SensorRepairFuture
