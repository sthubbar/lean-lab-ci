import LeanLab.ExceptionalSet.Feed1122_majorant_origin_narrow524

/-!
Feed of `LeanLab.ExceptionalSet.Decomp524a.leaf_majorant_origin_wide524`,
burst-20261122 session S90.

Finding: the leaf is FALSE as written. By `feed1122_two_w_le_const`, proved in
`Feed1122_majorant_origin_narrow524`, an even cosine majorant of the indicator
of `[0, w)` has constant term at least `2 * w`, while the leaf allows at most
`w + 4 / (H + 1)`. At `w = 1 / 3`, `H = 100` every hypothesis holds and
`2 / 3 > 1 / 3 + 4 / 101`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp524a

open Real Finset

/-- FALSE finding for `leaf_majorant_origin_wide524`: its universal closure
fails at `w = 1 / 3`, `H = 100`. -/
theorem leaf_majorant_origin_wide524_false :
    ¬ (∀ (w : ℝ) (H : ℕ), 0 < w → 1 / 6 < w → w ≤ 1 / 3 → 4 ≤ H →
      w + 4 / ((H : ℝ) + 1) < 1 →
      (w + 4 / ((H : ℝ) + 1)) * (1 + cos (π * w)) < 1 →
      ∃ c₀ : ℝ, ∃ A : ℕ → ℝ,
        c₀ ≤ w + 4 / ((H : ℝ) + 1) ∧
        (∀ h ∈ Icc 1 H, |A h| ≤ 4 / (h : ℝ)) ∧
        ∀ x : ℝ, (if 0 ≤ Int.fract x ∧ Int.fract x < w then (1 : ℝ) else 0) ≤
          c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * x))) := by
  intro hall
  have hcast : ((100 : ℕ) : ℝ) = 100 := by norm_num
  obtain ⟨c₀, A, hc₀, -, hdom⟩ := hall (1 / 3) 100 (by norm_num) (by norm_num) le_rfl
    (by norm_num) (by rw [hcast]; norm_num)
    (by rw [hcast]; nlinarith [cos_le_one (π * (1 / 3))])
  have := feed1122_two_w_le_const (1 / 3) 100 (by norm_num) (by norm_num) c₀ A hdom
  rw [hcast] at hc₀
  linarith

end LeanLab.ExceptionalSet.Decomp524a
