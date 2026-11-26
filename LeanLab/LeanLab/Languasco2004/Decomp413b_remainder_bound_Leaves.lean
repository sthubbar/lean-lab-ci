/-
Split of Decomp413b.remainder_bound, Perelli and Pintz 1993 page 46,
displays 9 to 13. Source https://doi.org/10.1112/jlms/s2-47.1.41.
The remainder coefficient of page 45 display 7 is the sum of three product
terms. Each term gets its own mean square leaf, and the linearity of the
rational arc integral is a separate routine leaf.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.MajorData413

namespace LeanLab.Languasco2004.Decomp413bRemainderLeaves
open Finset Real MeasureTheory Decomp279b Decomp413b
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF: page 45 display 7, linearity of the rational arc integral over the
three product terms that make up the remainder coefficient.
Class MEDIUM. PROVED S154. Each integrand is a finite sum of continuous phases, so it is
integrable on the bounded arc set and the integral splits. -/
theorem remainder_linear (N Y H B : ℝ) (m : ℕ) :
    remainderCoefficient N Y H B m =
      rationalIntegral N Y H B m (fun q a t =>
        rationalWeight q * firstModel N Y t * secondRemainder Y q a t) +
      rationalIntegral N Y H B m (fun q a t =>
        rationalWeight q * secondModel Y t * firstRemainder N Y q a t) +
      rationalIntegral N Y H B m (fun q a t =>
        firstRemainder N Y q a t * secondRemainder Y q a t) := by
  have hphase : Continuous phase := by unfold phase; fun_prop
  have hfS : ∀ (q a : ℕ), Continuous (fun t : ℝ => firstSum N Y ((a : ℝ) / q + t)) := by
    intro q a; unfold firstSum
    exact continuous_finsetSum _ (fun h _ => continuous_const.mul
      (hphase.comp (continuous_const.mul (continuous_const.add continuous_id))))
  have hsS : ∀ (q a : ℕ), Continuous (fun t : ℝ => secondSum Y ((a : ℝ) / q + t)) := by
    intro q a; unfold secondSum
    exact continuous_finsetSum _ (fun h _ => continuous_const.mul
      (hphase.comp (continuous_const.mul (continuous_const.add continuous_id))))
  have hfM : Continuous (fun t : ℝ => firstModel N Y t) := by
    unfold firstModel
    exact continuous_finsetSum _ (fun h _ => hphase.comp (continuous_const.mul continuous_id))
  have hsM : Continuous (fun t : ℝ => secondModel Y t) := by
    unfold secondModel
    exact continuous_finsetSum _ (fun h _ => hphase.comp (continuous_const.mul continuous_id))
  have hfR : ∀ q a : ℕ, Continuous (fun t => firstRemainder N Y q a t) := by
    intro q a; unfold firstRemainder; exact (hfS q a).sub (continuous_const.mul hfM)
  have hsR : ∀ q a : ℕ, Continuous (fun t => secondRemainder Y q a t) := by
    intro q a; unfold secondRemainder; exact (hsS q a).sub (continuous_const.mul hsM)
  have hph : ∀ (q a : ℕ), Continuous (fun t : ℝ => phase (-(m : ℝ) * ((a : ℝ) / q + t))) :=
    fun q a => hphase.comp (continuous_const.mul (continuous_const.add continuous_id))
  -- integrability on the bounded arc set
  have hint : ∀ (q a : ℕ) (c : ℝ) (f : ℝ → ℂ), Continuous f →
      IntegrableOn f {t : ℝ | |t| < c ∧ (a : ℝ) / q + t ∈ period H} := by
    intro q a c f hf
    refine (hf.integrableOn_Icc (a := -c) (b := c)).mono_set ?_
    intro t ht
    have := abs_lt.mp ht.1
    exact ⟨this.1.le, this.2.le⟩
  unfold remainderCoefficient rationalIntegral
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl (fun q _ => ?_)
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl (fun a _ => ?_)
  have h1 := hint q a (Real.log N ^ (2 * B) / ((q : ℝ) * Y))
    (fun t => rationalWeight q * firstModel N Y t * secondRemainder Y q a t *
      phase (-(m : ℝ) * ((a : ℝ) / q + t)))
    (((continuous_const.mul hfM).mul (hsR q a)).mul (hph q a))
  have h2 := hint q a (Real.log N ^ (2 * B) / ((q : ℝ) * Y))
    (fun t => rationalWeight q * secondModel Y t * firstRemainder N Y q a t *
      phase (-(m : ℝ) * ((a : ℝ) / q + t)))
    (((continuous_const.mul hsM).mul (hfR q a)).mul (hph q a))
  have h3 := hint q a (Real.log N ^ (2 * B) / ((q : ℝ) * Y))
    (fun t => firstRemainder N Y q a t * secondRemainder Y q a t *
      phase (-(m : ℝ) * ((a : ℝ) / q + t)))
    (((hfR q a).mul (hsR q a)).mul (hph q a))
  beta_reduce
  rw [← integral_add h1 h2, ← integral_add ?_ h3]
  · congr 1
    funext t
    ring
  · exact h1.add h2

/-- LEAF: page 46 displays 9 to 13, the mean square of the term with the
principal model T1 and the S2 remainder, controlled by the ordinary
Siegel Walfisz estimate for S2.
Class HARD. -/
theorem first_cross_bound :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∑ m ∈ window N η,
        ‖rationalIntegral N (localization N η) (windowLength N η) (arcExponent η A) m
          (fun q a t => rationalWeight q * firstModel N (localization N η) t *
            secondRemainder (localization N η) q a t)‖ ^ 2 ≤
        C * windowLength N η * localization N η ^ 2 / Real.log N ^ A := by sorry

/-- LEAF: page 46 displays 9 to 13, the mean square of the term with the
principal model T2 and the S1 remainder, controlled by the short interval
Siegel Walfisz estimate of display 6 for S1.
Class HARD. -/
theorem second_cross_bound :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∑ m ∈ window N η,
        ‖rationalIntegral N (localization N η) (windowLength N η) (arcExponent η A) m
          (fun q a t => rationalWeight q * secondModel (localization N η) t *
            firstRemainder N (localization N η) q a t)‖ ^ 2 ≤
        C * windowLength N η * localization N η ^ 2 / Real.log N ^ A := by sorry

/-- LEAF: page 46 displays 9 to 13, the mean square of the product of the
S1 remainder and the S2 remainder, controlled by both Siegel Walfisz estimates.
Class HARD. -/
theorem double_remainder_bound :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∑ m ∈ window N η,
        ‖rationalIntegral N (localization N η) (windowLength N η) (arcExponent η A) m
          (fun q a t => firstRemainder N (localization N η) q a t *
            secondRemainder (localization N η) q a t)‖ ^ 2 ≤
        C * windowLength N η * localization N η ^ 2 / Real.log N ^ A := by sorry

/-- Elementary inequality for three complex numbers. -/
private lemma norm_add3_sq (x y z : ℂ) :
    ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have h := norm_add₃_le (a := x) (b := y) (c := z)
  have h0 : 0 ≤ ‖x + y + z‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖y‖ - ‖z‖), sq_nonneg (‖x‖ - ‖z‖),
    norm_nonneg x, norm_nonneg y, norm_nonneg z]

/-- Page 46 displays 9 to 13 give the exact statement of
Decomp413b.remainder_bound. CONDITIONAL ON the four leaves above. -/
theorem remainder_bound_from_leaves :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∑ m ∈ window N η,
        ‖remainderCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m‖ ^ 2 ≤
        C * windowLength N η * localization N η ^ 2 / Real.log N ^ A := by
  obtain ⟨e₁, he₁, h1⟩ := first_cross_bound
  obtain ⟨e₂, he₂, h2⟩ := second_cross_bound
  obtain ⟨e₃, he₃, h3⟩ := double_remainder_bound
  refine ⟨min e₁ (min e₂ e₃), lt_min he₁ (lt_min he₂ he₃), ?_⟩
  intro η A hη he hA
  obtain ⟨C₁, N₁, g₁⟩ := h1 η A hη (he.trans_le (min_le_left _ _)) hA
  obtain ⟨C₂, N₂, g₂⟩ := h2 η A hη
    (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hA
  obtain ⟨C₃, N₃, g₃⟩ := h3 η A hη
    (he.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hA
  refine ⟨3 * (C₁ + C₂ + C₃), max N₁ (max N₂ N₃), ?_⟩
  intro N hN
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN2 : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN3 : N₃ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  set Y := localization N η
  set H := windowLength N η
  set B := arcExponent η A
  set F₁ : ℕ → ℂ := fun m => rationalIntegral N Y H B m (fun q a t =>
    rationalWeight q * firstModel N Y t * secondRemainder Y q a t)
  set F₂ : ℕ → ℂ := fun m => rationalIntegral N Y H B m (fun q a t =>
    rationalWeight q * secondModel Y t * firstRemainder N Y q a t)
  set F₃ : ℕ → ℂ := fun m => rationalIntegral N Y H B m (fun q a t =>
    firstRemainder N Y q a t * secondRemainder Y q a t)
  have hp : ∀ m ∈ window N η, ‖remainderCoefficient N Y H B m‖ ^ 2 ≤
      3 * (‖F₁ m‖ ^ 2 + ‖F₂ m‖ ^ 2 + ‖F₃ m‖ ^ 2) := by
    intro m _
    rw [remainder_linear N Y H B m]
    exact norm_add3_sq _ _ _
  calc _ ≤ ∑ m ∈ window N η, 3 * (‖F₁ m‖ ^ 2 + ‖F₂ m‖ ^ 2 + ‖F₃ m‖ ^ 2) :=
        sum_le_sum hp
    _ = 3 * ((∑ m ∈ window N η, ‖F₁ m‖ ^ 2) + (∑ m ∈ window N η, ‖F₂ m‖ ^ 2) +
        ∑ m ∈ window N η, ‖F₃ m‖ ^ 2) := by
      rw [← mul_sum, sum_add_distrib, sum_add_distrib]
    _ ≤ 3 * (C₁ * H * Y ^ 2 / Real.log N ^ A + C₂ * H * Y ^ 2 / Real.log N ^ A +
        C₃ * H * Y ^ 2 / Real.log N ^ A) := by
      gcongr
      · exact g₁ N hN1
      · exact g₂ N hN2
      · exact g₃ N hN3
    _ = _ := by ring

#print axioms remainder_linear
#print axioms first_cross_bound
#print axioms second_cross_bound
#print axioms double_remainder_bound
#print axioms remainder_bound_from_leaves
end
end LeanLab.Languasco2004.Decomp413bRemainderLeaves
