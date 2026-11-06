/-
P0093 page 168 equation 10.7. Bridge a fresh coarse major arc input.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp376d
import LeanLab.Linnik1951.SPLIT_major_to_truncated357

namespace LeanLab.Linnik1951

/-- P0093 page 168 equation 10.7. Exact major_error_remainder357
statement from the existing stronger major_to_truncated_decomposed376
bridge. The additional nonnegative tail is unnecessary to the bound.
CONDITIONAL on the unchanged major expansion and relative correction. -/
theorem major_error_remainder_decomposed435 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280)
    (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N| ≤
        ε / 2 * scale111 k N + C * (N : ℝ) / Real.log N := by
  obtain ⟨Na, ha⟩ := major_to_truncated_decomposed376 hG hM k hk (ε / 2) (by positivity)
  refine ⟨1, by norm_num, max 1 Na, ?_⟩
  intro N hev hN
  have hNa : Na < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hN1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN1)
  have htail : 0 ≤ (1 : ℝ) * N / Real.log N := by positivity
  exact (ha N hev hNa).trans (le_add_of_nonneg_right htail)

end LeanLab.Linnik1951
