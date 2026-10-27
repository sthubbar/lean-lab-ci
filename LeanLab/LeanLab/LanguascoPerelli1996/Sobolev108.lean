import Mathlib

/-!
The elementary Sobolev step in P0071 page 355 display 12.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Sobolev108
open intervalIntegral

/-- LEAF. Page 355 display 12. A nonnegative continuously differentiable
function at zero is bounded by its mass and total variation on minus one to one.
This proves the standard Sobolev input from Montgomery reference 13 Lemma 1.1. -/
theorem point_le_mass_add_variation {g g' : ℝ → ℝ}
    (hg : Continuous g) (hg' : Continuous g')
    (hd : ∀ v, HasDerivAt g (g' v) v) (hpos : ∀ v, 0 ≤ g v) :
    g 0 ≤ (∫ v in (-1 : ℝ)..1, g v) + (∫ v in (-1 : ℝ)..1, |g' v|) := by
  have hp : ∀ v ∈ Set.Icc (0 : ℝ) 1,
      g 0 ≤ g v + ∫ t in (-1 : ℝ)..1, |g' t| := by
    intro v hv
    have heq : (∫ t in (0 : ℝ)..v, g' t) = g v - g 0 :=
      integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hg'.intervalIntegrable _ _)
    have habs := abs_integral_le_integral_abs (f := g') (μ := MeasureTheory.volume) hv.1
    rw [heq] at habs
    have hsub : (∫ t in (0 : ℝ)..v, |g' t|) ≤ ∫ t in (-1 : ℝ)..1, |g' t| :=
      integral_mono_interval (by norm_num) hv.1 hv.2
        (Filter.Eventually.of_forall fun t => abs_nonneg (g' t))
        (hg'.abs.intervalIntegrable _ _)
    linarith [neg_le_abs (g v - g 0)]
  have hint := integral_mono_on (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1) (by norm_num)
    (continuous_const.intervalIntegrable _ _)
    ((hg.add continuous_const).intervalIntegrable _ _) hp
  simp only [Pi.add_apply] at hint
  simp only [integral_add (hg.intervalIntegrable (0 : ℝ) 1)
    (continuous_const.intervalIntegrable (0 : ℝ) 1), integral_const, sub_zero,
    one_smul] at hint
  have hmass : (∫ v in (0 : ℝ)..1, g v) ≤ ∫ v in (-1 : ℝ)..1, g v :=
    integral_mono_interval (by norm_num) (by norm_num) le_rfl
      (Filter.Eventually.of_forall hpos) (hg.intervalIntegrable _ _)
  linarith

end LeanLab.LanguascoPerelli1996.Sobolev108
