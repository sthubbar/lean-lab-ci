/-
Re-split of `leaf_exceptional_count_from_saving` of `SPLIT_mv_no_siegel150.lean`, the open
leaf under `mv_no_siegel150`, Theorem 5.1 part one of P0029, page 18 and Section 5.

QUESTION on the existing leaf: its conclusion takes `K` and `X₀` before `ϑ`, so one threshold
must serve every `ϑ` in `(0, 1/5)`, while its hypothesis `hsaving` gives a threshold `Xh`
that depends on `ϑ`. As `ϑ` tends to zero the hypothesis gives nothing at a fixed `X`, and
the conclusion there is a bound of size `X e^(-2 sqrt (c log X))` that needs an outside
input such as the Montgomery and Vaughan power saving. The paper, and the assembly
`mv_no_siegel150_split`, use the count at one fixed `ϑ` only.

This file states the same count at one fixed level, `ϑ` given first and `K`, `X₀` after
it, which is what the circle method of Section 5 produces from the saving of Proposition
5.2 part one at that level, and proves the parent assembly from it with the statement of
`mv_no_siegel150_split` unchanged. The existing leaf and the existing file are untouched.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.SPLIT_mv_no_siegel150

namespace LeanLab.BhowmikGrimmelt2026

open LeanLab.ExceptionalSet (PowerSaving)
open ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-- LEAF: P0029 Section 5, proof of Theorem 5.1 part one, page 18: at one fixed level
`R = X ^ ϑ` with `0 < ϑ < 1/5`, the saving `C exp (-(c / ϑ))` of Proposition 5.2 part one on
the primitive character sum of interval maxima, valid for `X` beyond a threshold, together
with the Gallagher second moment on the minor arcs, leaves at most
`K exp (-(c / ϑ)) X ^ (1 - ϑ) (log X) ^ 8` even numbers of `[X / 2, X]` with no
representation as a sum of two primes, for `X` beyond a threshold depending on `ϑ`. The
level gain `N / R` gives the power `1 - ϑ`. This is the circle method count of the paper
at a single level; the constant and threshold may depend on `c`, `C` and `ϑ`. Class HARD,
a real analytic step. -/
theorem leaf_exceptional_count_fixed_level150 (c C : ℝ) (hc : 0 < c)
    (hGallagher : GallagherStandard) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ5 : ϑ < 1 / 5)
    (hsaving : ∃ Xh : ℝ, ∀ X : ℝ, 2 ≤ X → Xh ≤ X →
      (¬ ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        SiegelZero (X ^ ϑ) r χ β) →
      primSum (X ^ ϑ) (fun _ _ χ => intervalMax ⌈X⌉₊ (X ^ ϑ)
        (fun n => (vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0)) ≤
        C * Real.exp (-(c / ϑ))) :
    ∃ K X₀ : ℝ, 0 ≤ K ∧ ∀ X : ℝ, 2 ≤ X → X₀ ≤ X →
      (¬ ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        SiegelZero (X ^ ϑ) r χ β) →
      (Edy X : ℝ) ≤ K * Real.exp (-(c / ϑ)) * X ^ (1 - ϑ) * (Real.log X) ^ 8 := by
  sorry

/-- The no Siegel zero half of Theorem 5.1, the statement of `mv_no_siegel150_split`
unchanged, assembled from the fixed level count above and the proved leaves
`leaf_prop52_part_one`, `leaf_interval_max_saving_at_level`, `leaf_log_loss_absorbed` of
`SPLIT_mv_no_siegel150`. CONDITIONAL ON `leaf_exceptional_count_fixed_level150`; it does
not use `leaf_exceptional_count_from_saving`. -/
theorem mv_no_siegel150_split_fixed_level (h52 : Prop52) (hGallagher : GallagherStandard) :
    ∃ ϑ₀ : ℝ, 0 < ϑ₀ ∧ ∀ ϑ : ℝ, 0 < ϑ → ϑ < ϑ₀ → ϑ < 1 / 5 →
      ∃ C X₀ : ℝ, ∀ X : ℝ, 2 ≤ X → X₀ ≤ X →
        (¬ ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
          SiegelZero (X ^ ϑ) r χ β) →
        (Edy X : ℝ) ≤ C * X ^ (1 - ϑ / 2) := by
  obtain ⟨c, C, hc, hbound⟩ := leaf_prop52_part_one h52
  refine ⟨1 / 5, by norm_num, ?_⟩
  intro ϑ hϑ _ hϑ5
  obtain ⟨K, X₁, hK, hcount⟩ :=
    leaf_exceptional_count_fixed_level150 c (max C 0) hc hGallagher ϑ hϑ hϑ5
      (leaf_interval_max_saving_at_level c C hc hbound ϑ hϑ hϑ5)
  obtain ⟨C', X₂, hC', habs⟩ := leaf_log_loss_absorbed K ϑ 8 hK hϑ
  refine ⟨C', max X₁ X₂, ?_⟩
  intro X hX hX0 hns
  have hX₁ : X₁ ≤ X := le_trans (le_max_left X₁ X₂) hX0
  have hX₂ : X₂ ≤ X := le_trans (le_max_right X₁ X₂) hX0
  have hcount' := hcount X hX hX₁ hns
  have hexp : Real.exp (-(c / ϑ)) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hpos : 0 < c / ϑ := div_pos hc hϑ
    linarith
  have hstep : K * Real.exp (-(c / ϑ)) * X ^ (1 - ϑ) * (Real.log X) ^ 8
      ≤ K * X ^ (1 - ϑ) * (Real.log X) ^ 8 := by
    have hXnn : (0 : ℝ) ≤ X := by linarith
    have hpow : (0 : ℝ) ≤ X ^ (1 - ϑ) := Real.rpow_nonneg hXnn _
    have hlog : (0 : ℝ) ≤ (Real.log X) ^ 8 := by positivity
    have hfac : (0 : ℝ) ≤ K * X ^ (1 - ϑ) * (Real.log X) ^ 8 :=
      mul_nonneg (mul_nonneg hK hpow) hlog
    have hrw : K * Real.exp (-(c / ϑ)) * X ^ (1 - ϑ) * (Real.log X) ^ 8
        = (K * X ^ (1 - ϑ) * (Real.log X) ^ 8) * Real.exp (-(c / ϑ)) := by ring
    rw [hrw]
    calc (K * X ^ (1 - ϑ) * (Real.log X) ^ 8) * Real.exp (-(c / ϑ))
        ≤ (K * X ^ (1 - ϑ) * (Real.log X) ^ 8) * 1 :=
          mul_le_mul_of_nonneg_left hexp hfac
      _ = K * X ^ (1 - ϑ) * (Real.log X) ^ 8 := by ring
  exact hcount'.trans (hstep.trans (habs X hX hX₂))

end LeanLab.BhowmikGrimmelt2026
