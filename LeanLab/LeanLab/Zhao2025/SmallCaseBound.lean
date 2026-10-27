import LeanLab.Zhao2025.SmallCaseInputs

/-!
Derive display 4.5 from the named zero estimates, without assuming a square sum bound.
Source: Zhao 2025, displays 4.1 to 4.5, pages 13 and 14.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56

/-- CONDITIONAL ON SmallCaseZeroEstimates, which contains only 4.1, 4.3 and 4.4. -/
theorem small_case_square_bound (n : ℕ) (l : ℝ) (S : ℕ → ℝ)
    (hl : 0 < l) (hu : l ≤ 0.01) (h : SmallCaseZeroEstimates n l S) :
    (∑ i ∈ Finset.range (n + 1), S i ^ 2) ≤
      Real.exp (-(20 / 3) * l) + 202 * Real.exp (-2.22 * smallCaseCutoff l) := by
  obtain ⟨T, hT0, hT, hsum, hS0, hS⟩ := h
  let a := Real.exp (-(10 / 3 * l))
  let r := a - Real.exp (-(10 / 3 * smallCaseCutoff l))
  let b := 100 * Real.exp (-2.22 * smallCaseCutoff l)
  have hcut := small_case_cutoff_spec l hl
  have hla : l ≤ smallCaseCutoff l := by linarith [hcut.1]
  have ha : 0 ≤ a := (Real.exp_pos _).le
  have ha1 : a ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hr0 : 0 ≤ r := sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have hra : r ≤ a := sub_le_self _ (Real.exp_pos _).le
  have hr1 : r ≤ 1 := hra.trans ha1
  have ht0 : 0 ≤ T 0 := hT0 0 (by simp)
  have htb : T 0 ≤ b := hT 0 (by simp)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hsq : (∑ i ∈ Finset.range (n + 1), T i ^ 2) ≤ b * 0.02 := by
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), b * T i := by
        apply Finset.sum_le_sum
        intro i hi
        have hi0 := hT0 i hi
        have hib : T i ≤ b := hT i hi
        nlinarith
      _ = b * ∑ i ∈ Finset.range (n + 1), T i := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum hb
  have hcross : r * T 0 ≤ b :=
    (mul_le_mul_of_nonneg_right hr1 ht0).trans (by simpa using htb)
  have hr2 : r ^ 2 ≤ a ^ 2 := by nlinarith
  have henergy : (∑ i ∈ Finset.range (n + 1), S i ^ 2) =
      r ^ 2 + 2 * r * T 0 + ∑ i ∈ Finset.range (n + 1), T i ^ 2 := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hs : (∑ i ∈ Finset.range n, S (i + 1) ^ 2) =
        ∑ i ∈ Finset.range n, T (i + 1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hS i (Finset.mem_range.mp hi)]
    rw [hs, hS0]
    dsimp [r, a]
    ring
  have ha2 : a ^ 2 = Real.exp (-(20 / 3) * l) := by
    dsimp [a]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [henergy, ← ha2]
  dsimp [b] at hsq hcross
  nlinarith

#print axioms small_case_square_bound
end LeanLab.Zhao2025.Task56
