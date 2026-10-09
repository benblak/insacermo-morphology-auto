import FiniteContractCoverKernelV1

namespace INSACERMO.IrisFiniteCertificate
open INSACERMO.FiniteContractCover

/-!
Finite Iris contract certificates. The three available sensors, in order:
0=petal_width, 1=sepal_length, 2=sepal_width (petal_length is hidden target).
The conflict clauses are the DISTINCT clauses recomputed on 150 historical
Iris rows; duplicate multiplicities are not necessary for set coverage.
This proof is conditional on the clause computation and exact finite scope.
-/

def iris_2_0 : List (List Nat) := [[0,1],[0,1,2],[0,2]]
def iris_3_5 : List (List Nat) := [[0,1],[0,1,2],[0,2],[1],[1,2],[2]]
def iris_4_5 : List (List Nat) := [[],[0],[0,1],[0,1,2],[0,2],[1],[1,2],[2]]
def iris_5_5 : List (List Nat) := [[0],[0,1],[0,1,2],[0,2],[1],[1,2],[2]]

-- 0b001 = petal_width only
theorem iris_2_0_one_measure_exact :
    certifyMinimum 3 iris_2_0 1 = true := by decide +kernel

-- 0b110 = sepal_length + sepal_width
theorem iris_3_5_two_measures_exact :
    certifyMinimum 3 iris_3_5 6 = true := by decide +kernel

theorem iris_4_5_impossible :
    certifyImpossible 3 iris_4_5 = true := by decide +kernel

theorem iris_5_5_three_measures_exact :
    certifyMinimum 3 iris_5_5 7 = true := by decide +kernel

theorem iris_5_5_two_sensors_never_sufficient :
    certifyCapacityImpossible 3 2 iris_5_5 = true := by decide +kernel

theorem iris_3_5_one_sensor_never_sufficient :
    certifyCapacityImpossible 3 1 iris_3_5 = true := by decide +kernel

theorem iris_2_0_no_sensor_insufficient :
    certifyCapacityImpossible 3 0 iris_2_0 = true := by decide +kernel

theorem iris_4_5_even_full_set_fails :
    covers iris_4_5 7 = false := by decide +kernel

end INSACERMO.IrisFiniteCertificate
