/-
Split of `leaf_zeta_no_low_zero508` of `LEAF_feed1122_zero_reciprocal508` into one smaller
cited leaf and a proved symmetry reduction.

Source: P0029 page 11 display 3.7, the zeta part of the low zero gap, with the classical
fact that the first zero of zeta has ordinate about `14.13`, Titchmarsh chapter 15. The
reduction uses the two symmetries of the zeros in the critical strip, both proved: the
functional equation, `zeta_one_sub_eq_zero` of PNTPort ZetaZeros Sym, which sends a zero
`ρ` to `1 - ρ`, and the conjugation symmetry `riemannZeta_conj` of Mathlib. Together they
move every strip zero with `|Im ρ| ≤ 1` into the closed quarter box `1/2 ≤ Re ρ < 1`,
`0 ≤ Im ρ ≤ 1`, so only that box is left as a leaf.

AI wrote the Lean code. Goldbach is open.
-/
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import LeanLab.PNTPort.ZetaZeros.Sym

namespace LeanLab.BhowmikGrimmelt2026

open Complex

/-- LEAF: P0029 page 11 display 3.7, the zeta case of the low zero gap, reduced by the
functional equation and conjugation to the quarter box: zeta has no zero with
`1/2 ≤ Re s < 1` and `0 ≤ Im s ≤ 1`. Classical, Titchmarsh chapter 15, the first zero
having ordinate about `14.13`; a proof needs an explicit numerical nonvanishing argument,
for instance an Euler Maclaurin approximation with a Lipschitz grid over the box. Class
HARD. -/
theorem leaf_zeta_quarter_box508 :
    ∀ s : ℂ, 1 / 2 ≤ s.re → s.re < 1 → 0 ≤ s.im → s.im ≤ 1 → riemannZeta s ≠ 0 := by
  sorry

/-- The quarter box gives the whole strip at height at most one, by the functional
equation and conjugation symmetry. CONDITIONAL ON `leaf_zeta_quarter_box508`. -/
theorem zeta_no_low_zero_from_box508 :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 1 < |ρ.im| := by
  intro ρ hρ h0 h1
  by_contra hle
  push_neg at hle
  -- conjugate if needed so that the imaginary part is nonnegative
  have hpos : ∀ w : ℂ, riemannZeta w = 0 → 1 / 2 ≤ w.re → w.re < 1 → |w.im| ≤ 1 → False := by
    intro w hw hw0 hw1 hwi
    rcases le_total 0 w.im with him | him
    · exact leaf_zeta_quarter_box508 w hw0 hw1 him (le_of_abs_le hwi) hw
    · have hc : riemannZeta ((starRingEnd ℂ) w) = 0 := by
        rw [riemannZeta_conj, hw, map_zero]
      refine leaf_zeta_quarter_box508 ((starRingEnd ℂ) w) (by simpa using hw0)
        (by simpa using hw1) (by simpa using him) ?_ hc
      simp only [conj_im]
      linarith [neg_abs_le w.im, abs_le.mp hwi]
  rcases le_or_gt (1 / 2) ρ.re with hh | hh
  · exact hpos ρ hρ hh h1 hle
  · have hz := LeanLab.PNTPort.ZetaZeros.zeta_one_sub_eq_zero h0 h1 hρ
    refine hpos (1 - ρ) hz ?_ ?_ ?_
    · simp; linarith
    · simp; linarith
    · simpa [abs_neg] using hle

end LeanLab.BhowmikGrimmelt2026
