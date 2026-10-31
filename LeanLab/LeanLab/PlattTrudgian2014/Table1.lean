/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1404.5669v2 page 8 Table 1.
The analytic claims are named Props, not proofs of the table's computations.
-/
import LeanLab.PlattTrudgian2014.Lambda

namespace LeanLab.PlattTrudgian2014

structure TableRow where
  label : String
  c : ℚ
  oldLambda : ℚ
  newLambda : ℚ
  oldK : ℕ
  newK : ℕ
  onGRH : Bool
  deriving DecidableEq

def tableRows : List TableRow :=
  [⟨"A", 3/4, 0.887167, 0.8844473, 46, 45, false⟩,
   ⟨"B", 3/4, 0.887167, 0.8844473, 35, 34, false⟩,
   ⟨"C", 19/21, 0.965411, 0.9642399, 341, 330, false⟩,
   ⟨"D", 113/126, 0.961917, 0.9606646, 106, 102, false⟩,
   ⟨"E", 53/63, 0.935746, 0.9339489, 211, 205, false⟩,
   ⟨"F", 109/126, 0.947313, 0.9457435, 161, 156, false⟩,
   ⟨"G", 109/154, 0.862327, 0.8594000, 63, 62, false⟩,
   ⟨"G", 1/2, 0.716344, 0.7163436, 31, 31, true⟩,
   ⟨"H", 3/4, 0.887167, 0.8844473, 142, 138, false⟩,
   ⟨"I", 19/21, 0.965411, 0.9642399, 1432, 1319, false⟩,
   ⟨"J", 3/4, 0.887167, 0.8844473, 332, 323, false⟩]

/-- The table's numerical large values claims in the existing repaired normalization. -/
def TableLambdaClaims : Prop :=
  ∀ row ∈ tableRows, LambdaOK (row.c : ℝ) (row.newLambda : ℝ)

theorem tableRows_length : tableRows.length = 11 := rfl

theorem table_lambda_decreases : ∀ row ∈ tableRows, row.newLambda < row.oldLambda := by
  norm_num [tableRows]

theorem table_K_nonincreasing : ∀ row ∈ tableRows, row.newK ≤ row.oldK := by
  decide +kernel

theorem table_parameter_ranges :
    ∀ row ∈ tableRows, 0 < row.c ∧ row.c < 1 ∧ 0 < row.newLambda ∧ row.newLambda < 1 := by
  norm_num [tableRows]

#print axioms tableRows_length
#print axioms table_lambda_decreases
#print axioms table_K_nonincreasing
#print axioms table_parameter_ranges

end LeanLab.PlattTrudgian2014
