/-
Kai's Goldbach scaffolding: the four mod 30 bands of the truncated singular series.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.KaiScaffolding

/-- The odd part of the Hardy-Littlewood singular product truncated at modulus 30:
the product over `p ∈ {3, 5}` dividing `n` of `(p - 1) / (p - 2)`, without the factor `C₂`. -/
def S30 (n : ℕ) : ℚ :=
  ∏ p ∈ ({3, 5} : Finset ℕ).filter (· ∣ n), ((p : ℚ) - 1) / ((p : ℚ) - 2)

theorem S30_eq (n : ℕ) :
    S30 n = (if 3 ∣ n then 2 else 1) * (if 5 ∣ n then 4 / 3 else 1) := by
  unfold S30
  by_cases h3 : 3 ∣ n <;> by_cases h5 : 5 ∣ n <;>
    simp [Finset.filter_insert, Finset.filter_singleton, h3, h5] <;> norm_num

/-- The truncated product depends only on `n mod 30`. -/
theorem S30_mod (n : ℕ) : S30 n = S30 (n % 30) := by
  rw [S30_eq, S30_eq]
  have e3 : 3 ∣ n ↔ 3 ∣ n % 30 := by omega
  have e5 : 5 ∣ n ↔ 5 ∣ n % 30 := by omega
  simp only [e3, e5]

/-- Kai's four bands: the truncated product takes exactly the values `1, 4/3, 2, 8/3`. -/
theorem S30_bands (n : ℕ) : S30 n = 1 ∨ S30 n = 4 / 3 ∨ S30 n = 2 ∨ S30 n = 8 / 3 := by
  rw [S30_eq]
  by_cases h3 : 3 ∣ n <;> by_cases h5 : 5 ∣ n <;> simp [h3, h5] <;> norm_num

end LeanLab.KaiScaffolding
