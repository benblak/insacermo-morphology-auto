import FiniteContractCoverKernelV1
import Std

/-!
INSACERMO - independent Lean verification of exact finite historical
sensor-discrimination certificates on 61 El Nino monthly SST rows (1950-2010).
11 observable months Jan-Nov; DEC is target. YEAR excluded as identity key.
Resolution affects the semantics of sensors, not trained coefficients.

Input conflict masks were derived from the SHA256-pinned CSV
ecb07dea0e8b6dd7d1fd10825913624dc8daedcb069a563dd6829c074e9e38da
using exact decimal rounding; independent brute-force enumeration checks
the raw rows. Lean checks only the exported clauses, not the CSV parser.
-/
namespace INSACERMO.ElNinoResolution
open INSACERMO.FiniteContractCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def clauses (masks : List Nat) : List (List Nat) :=
  masks.map (fun mask => (List.range 11).filter (fun bit => mask.testBit bit))

def exactMasks : List Nat := [1535,1791,1919,2015,2031,2039,2045,2046]

def quarterMasks : List Nat := [605,1357,1358,1583,847,971,253,749,1837,1933,1961,478,862,1466,892,1215,1247,1743,1991,1469,1017,1726,1018,2034,2012,2028,959,1527,1975,1787,1915,2037]

def halfMasks : List Nat := [73,140,1792,277,271,124,187,725,1337,1582,378,1714,1567,247,1459,979,1269,1765,1009,862,762]

def oneMasks : List Nat := [3,65,10,66,516,72,1032,28,140,268,784,1792,649,1665,178,562,1074,674,184,904,736,1189]

def one23Masks : List Nat := [18,132,769,42,548,896,581,169,201,649,1073,1297,225,705,780,680,840,1808,1603,117,1802,1826,1760,1699,1272]

def twoMasks : List Nat := [0]

/-- Recorded unquantized values: February alone suffices for the
    1950-2010 catalogue, no inference to unseen years. -/
theorem recorded_precision_one_sensor_minimal :
    certifyMinimum 11 (clauses exactMasks) 4 = true := by
  decide +kernel

theorem quarter_degree_two_sensors_minimal :
    certifyMinimum 11 (clauses quarterMasks) 136 = true := by
  decide +kernel

theorem half_degree_three_sensors_minimal :
    certifyMinimum 11 (clauses halfMasks) 521 = true := by
  decide +kernel

theorem one_degree_four_sensors_minimal :
    certifyMinimum 11 (clauses oneMasks) 523 = true := by
  decide +kernel

theorem one_degree_second_contract_four_sensors_minimal :
    certifyMinimum 11 (clauses one23Masks) 643 = true := by
  decide +kernel

theorem one_degree_future_contract_five_sensors_minimal :
    certifyMinimum 11 (clauses (oneMasks ++ one23Masks)) 651 = true := by
  decide +kernel

theorem two_degrees_cannot_certify :
    certifyImpossible 11 (clauses twoMasks) = true := by
  decide +kernel

theorem budget_four_refuses_combined_contract :
    certifyCapacityImpossible 11 4 (clauses (oneMasks ++ one23Masks)) = true := by
  decide +kernel

end INSACERMO.ElNinoResolution
