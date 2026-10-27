import LeanLab.ChenDoubleSieve.SigmaIntegral

/-!
# A rational certificate for the normalizing integral

Source: https://arxiv.org/pdf/0705.1652, page 14, the definition of sigma0.
This certificate bounds sigma 3 5 4. It does not certify the remaining Table 1 integrals.
AI wrote the Lean code. Binary Goldbach is open.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable section
open Finset
namespace LeanLab.ChenDoubleSieve.Wu04Integral

/-- Rational counterpart of the logarithm lower bound. -/
def logLowerQ (n : ℕ) (y : ℚ) : ℚ :=
  2 * ∑ j ∈ range n, ((y - 1) / (y + 1)) ^ (2 * j + 1) / (2 * j + 1)

/-- Rational counterpart of the logarithm upper bound. -/
def logUpperQ (n : ℕ) (y : ℚ) : ℚ :=
  logLowerQ n y + 2 * ((y - 1) / (y + 1)) ^ (2 * n + 1) /
    (1 - ((y - 1) / (y + 1)) ^ 2)

@[simp] theorem logLowerQ_cast (n : ℕ) (y : ℚ) :
    (logLowerQ n y : ℝ) = logLower n (y : ℝ) := by
  simp [logLowerQ, logLower]

@[simp] theorem logUpperQ_cast (n : ℕ) (y : ℚ) :
    (logUpperQ n y : ℝ) = logUpper n (y : ℝ) := by
  simp [logUpperQ, logUpper, logLowerQ_cast]

/-- The partition has 32 panels of width 1/16. -/
def gridQ (j : ℕ) : ℚ := 3 + j / 16

/-- Integer bounds with scale one million for the endpoint integrands. -/
def lowerTable : List ℤ := [231049, 216285, 202407, 189344, 177035, 165423, 154458, 144093, 134286, 124999, 116196, 107846, 99918, 92385, 85223, 78409, 71920, 65738, 59844, 54222, 48856, 43731, 38834, 34152, 29673, 25387, 21284, 17353, 13587, 9975, 6512, 3189, 0]
def upperTable : List ℤ := [231050, 216286, 202408, 189345, 177036, 165424, 154459, 144094, 134287, 125000, 116197, 107847, 99919, 92386, 85224, 78410, 71921, 65739, 59845, 54223, 48857, 43732, 38835, 34153, 29674, 25388, 21285, 17354, 13588, 9976, 6513, 3190, 0]

def lowerQ (j : ℕ) : ℚ := (lowerTable[j]?.getD 0 : ℚ) / 1000000
def upperQ (j : ℕ) : ℚ := (upperTable[j]?.getD 0 : ℚ) / 1000000

/-- All endpoint certificates use rational arithmetic in the kernel. -/
theorem endpoint_certificate : ∀ j ∈ range 33,
    lowerQ j ≤ logLowerQ 8 (4 / (gridQ j - 1)) / gridQ j ∧
    logUpperQ 8 (4 / (gridQ j - 1)) / gridQ j ≤ upperQ j := by
  decide +kernel

/-- Exact addition of the panel bounds. -/
theorem sum_certificate :
    (16 / 100 : ℚ) ≤ ∑ j ∈ range 32, (1 / 16 : ℚ) * lowerQ (j + 1) ∧
    (∑ j ∈ range 32, (1 / 16 : ℚ) * upperQ j) ≤ 18 / 100 := by
  decide +kernel

/-- A rigorous enclosure of the denominator integral. -/
theorem sigma_3_5_4_bounds : (16 / 100 : ℝ) ≤ sigma 3 5 4 ∧ sigma 3 5 4 ≤ 18 / 100 := by
  let x : ℕ → ℝ := fun j => (gridQ j : ℝ)
  have hx (j : ℕ) : x j = 3 + (j : ℝ) / 16 := by simp [x, gridQ]
  have hpart := sigma_partition x 32 8
    (fun j hj => by rw [hx j, hx (j + 1)]; push_cast; constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) j])
    (c := 4) (fun j hj => by
      rw [hx (j + 1)]
      have hj' : (j : ℝ) ≤ 31 := by exact_mod_cast (show j ≤ 31 by omega)
      push_cast
      linarith)
  have endpoints (j : ℕ) (hj : j < 33) :
      (lowerQ j : ℝ) ≤ logLower 8 (4 / (x j - 1)) / x j ∧
      logUpper 8 (4 / (x j - 1)) / x j ≤ (upperQ j : ℝ) := by
    have h := endpoint_certificate j (mem_range.mpr hj)
    have hlo : (lowerQ j : ℝ) ≤ ((logLowerQ 8 (4 / (gridQ j - 1)) / gridQ j : ℚ) : ℝ) := by exact_mod_cast h.1
    have hhi : ((logUpperQ 8 (4 / (gridQ j - 1)) / gridQ j : ℚ) : ℝ) ≤ (upperQ j : ℝ) := by exact_mod_cast h.2
    push_cast at hlo hhi
    rw [logLowerQ_cast] at hlo
    rw [logUpperQ_cast] at hhi
    push_cast at hlo hhi
    exact ⟨hlo, hhi⟩
  have hL : (∑ j ∈ range 32, (1 / 16 : ℝ) * (lowerQ (j + 1) : ℝ)) ≤
      ∑ j ∈ range 32, (x (j + 1) - x j) * (logLower 8 (4 / (x (j + 1) - 1)) / x (j + 1)) := by
    apply sum_le_sum
    intro j hj
    have he : x (j + 1) - x j = 1 / 16 := by rw [hx (j + 1), hx j]; push_cast; ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (endpoints (j + 1) (by have := mem_range.mp hj; omega)).1 (by norm_num)
  have hU : (∑ j ∈ range 32, (x (j + 1) - x j) * (logUpper 8 (4 / (x j - 1)) / x j)) ≤
      ∑ j ∈ range 32, (1 / 16 : ℝ) * (upperQ j : ℝ) := by
    apply sum_le_sum
    intro j hj
    have he : x (j + 1) - x j = 1 / 16 := by rw [hx (j + 1), hx j]; push_cast; ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (endpoints j (by have := mem_range.mp hj; omega)).2 (by norm_num)
  have hsL : (16 / 100 : ℝ) ≤ ∑ j ∈ range 32, (1 / 16 : ℝ) * (lowerQ (j + 1) : ℝ) := by
    have hh : ((16 / 100 : ℚ) : ℝ) ≤ ((∑ j ∈ range 32, (1 / 16 : ℚ) * lowerQ (j + 1) : ℚ) : ℝ) := by exact_mod_cast sum_certificate.1
    push_cast at hh
    exact hh
  have hsU : (∑ j ∈ range 32, (1 / 16 : ℝ) * (upperQ j : ℝ)) ≤ 18 / 100 := by
    have hh : ((∑ j ∈ range 32, (1 / 16 : ℚ) * upperQ j : ℚ) : ℝ) ≤ ((18 / 100 : ℚ) : ℝ) := by exact_mod_cast sum_certificate.2
    push_cast at hh
    exact hh
  have hx0 : x 0 = 3 := by rw [hx]; norm_num
  have hx32 : x 32 = 5 := by rw [hx]; norm_num
  rw [hx0, hx32] at hpart
  exact ⟨hsL.trans (hL.trans hpart.1), hpart.2.trans (hU.trans hsU)⟩

/-- The normalizing denominator is strictly positive. -/
theorem sigma_denominator_bounds :
    (82 / 100 : ℝ) ≤ 1 - sigma 3 5 4 ∧ 1 - sigma 3 5 4 ≤ 84 / 100 := by
  obtain ⟨hlo, hhi⟩ := sigma_3_5_4_bounds
  constructor <;> linarith

/-- The division defining sigma0 has a nonzero denominator. -/
theorem sigma_denominator_ne_zero : 1 - sigma 3 5 4 ≠ 0 := by
  have h := sigma_denominator_bounds.1
  linarith

end LeanLab.ChenDoubleSieve.Wu04Integral

#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.logLowerQ_cast
#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.logUpperQ_cast
#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.endpoint_certificate
#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.sum_certificate
#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.sigma_3_5_4_bounds
#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.sigma_denominator_bounds
#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.sigma_denominator_ne_zero
