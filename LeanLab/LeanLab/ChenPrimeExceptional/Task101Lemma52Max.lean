/-
AI wrote this Lean code for CODEX task101.
The finite maxima in P0039 Lemma 5.2, page 29.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task101Lemma52

open Finset Real

namespace LeanLab.ChenPrimeExceptional.Task101

noncomputable section

/-- The maximum absolute interval-prefix sum through N, including the empty prefixes. -/
def prefixMaximum (q N : ℕ) (a : ℕ → ℂ) : ℝ :=
  (range (N + 1)).sup' (by simp) (fun ξ => ‖∑ j ∈ Ioc q ξ, a j‖)

/-- Every interval-prefix sum is bounded by its finite maximum. -/
theorem prefix_le_maximum (q N : ℕ) (a : ℕ → ℂ) {ξ : ℕ} (hξ : ξ ≤ N) :
    ‖∑ j ∈ Ioc q ξ, a j‖ ≤ prefixMaximum q N a := by
  exact Finset.le_sup' (fun ξ => ‖∑ j ∈ Ioc q ξ, a j‖) (by simp; omega)

/-- The finite prefix maximum is nonnegative. -/
theorem prefixMaximum_nonneg (q N : ℕ) (a : ℕ → ℂ) : 0 ≤ prefixMaximum q N a := by
  exact (norm_nonneg _).trans (prefix_le_maximum q N a (Nat.zero_le N))

/-- Empty prefixes do not alter the maximum over a nonempty natural interval. -/
theorem prefixMaximum_eq_interval (q N : ℕ) (a : ℕ → ℂ) (hq : q < N) :
    prefixMaximum q N a = (Icc (q + 1) N).sup' (by simp; omega)
      (fun ξ => ‖∑ j ∈ Ioc q ξ, a j‖) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro ξ hξ
    by_cases hlow : ξ ≤ q
    · have hz : Ioc q ξ = ∅ := Ioc_eq_empty_of_le hlow
      rw [hz, sum_empty, norm_zero]
      exact (norm_nonneg _).trans
        (Finset.le_sup' (fun ξ => ‖∑ j ∈ Ioc q ξ, a j‖) (show q + 1 ∈ Icc (q + 1) N by simp; omega))
    · exact Finset.le_sup' (fun ξ => ‖∑ j ∈ Ioc q ξ, a j‖)
        (show ξ ∈ Icc (q + 1) N by simp only [mem_range] at hξ; simp; omega)
  · apply Finset.sup'_le
    intro ξ hξ
    exact prefix_le_maximum q N a (mem_Icc.mp hξ).2

/-- Lemma 5.2 in its finite maximum form, with both implied constants explicit. -/
theorem lemma52_maximum (N : ℕ) (hN : 2 ≤ N) (a : ℕ → ℂ) {f f' : ℝ → ℂ}
    {c W C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hf : ∀ t ∈ Set.Icc (sqrt (N : ℝ)) N, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Set.Icc (sqrt (N : ℝ)) N, ‖f' t‖ ≤ C / t)
    (hlo : ∀ t ∈ Set.Icc (sqrt (N : ℝ)) N, c * log N ≤ ‖f t‖)
    (hhi : ∀ t ∈ Set.Icc (sqrt (N : ℝ)) N, ‖f t‖ ≤ W * log N) :
    ‖∑ j ∈ Ioc ⌊sqrt (N : ℝ)⌋₊ N, f j * a j‖ ≤
      (W + C) * log N * prefixMaximum ⌊sqrt (N : ℝ)⌋₊ N a ∧
    ‖∑ j ∈ Ioc ⌊sqrt (N : ℝ)⌋₊ N, a j‖ ≤
      ((1 / c + C / c ^ 2) / log N) * prefixMaximum ⌊sqrt (N : ℝ)⌋₊ N (fun j => f j * a j) := by
  exact lemma52_interval N hN a hc hC hf hbound hlo hhi
    (fun ξ hξ => prefix_le_maximum _ _ _ hξ)
    (fun ξ hξ => prefix_le_maximum _ _ _ hξ)

end
end LeanLab.ChenPrimeExceptional.Task101

#print axioms LeanLab.ChenPrimeExceptional.Task101.prefix_le_maximum
#print axioms LeanLab.ChenPrimeExceptional.Task101.prefixMaximum_nonneg
#print axioms LeanLab.ChenPrimeExceptional.Task101.prefixMaximum_eq_interval
#print axioms LeanLab.ChenPrimeExceptional.Task101.lemma52_maximum
