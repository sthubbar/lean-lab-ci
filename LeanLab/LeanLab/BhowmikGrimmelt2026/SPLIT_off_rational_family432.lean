/-
Split of `off_rational_family432` into smaller leaves.

The off rational coefficient is `continuousTail405` minus the selected central alias
coefficient, so its smoothing family moment is controlled by the two separate family
moments plus the triangle inequality `coefficient_split328`.  The analytic work is
entirely in the continuous family leaf; the selected alias family leaf is the weaker
logarithm power five form of the already established logarithm power one bound.  The
third leaf collects the arithmetic consequences of the hypothesis set that any worker
on the first leaf needs.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp432a
import LeanLab.BhowmikGrimmelt2026.SPLIT_continuous_tail_family405

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- LEAF. Elementary arithmetic consequences of the hypothesis set of the split target.

Step: from the scale condition `10 * (X ^ theta) ^ 2 <= eta * X` together with
`eta <= 1` one gets `X >= 10`, hence a logarithm of `X` which is at least one, and
every logarithm power one bound of the family estimates is upgraded to logarithm power
five.  The same hypotheses bound `X ^ theta` by `X`.  Nothing here touches the weights;
this is the range bookkeeping every worker on the continuous family leaf needs. -/
theorem leaf_off_eta_range_arithmetic432 {ϑ : ℝ} (hϑ : 0 < ϑ)
    {X : ℕ} (hX : 2 ≤ X) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hscale : 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X) :
    (10 : ℝ) ≤ X ∧ (X : ℝ) ^ ϑ ≤ X ∧ 1 ≤ Real.log X ∧
      Real.log X ≤ 16 * Real.log X ^ 5 := by
  have hX2 : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hXϑ1 : 1 ≤ (X : ℝ) ^ ϑ := Real.one_le_rpow (by linarith) hϑ.le
  have hsq : (X : ℝ) ^ ϑ ≤ ((X : ℝ) ^ ϑ) ^ 2 := by nlinarith
  have hηX : η * X ≤ X := by nlinarith
  have h10 : (10 : ℝ) ≤ X := by nlinarith
  have hXϑ : (X : ℝ) ^ ϑ ≤ X := by nlinarith
  have hlog : 1 ≤ Real.log X := by
    have he : Real.exp 1 ≤ X := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log X := Real.log_le_log (Real.exp_pos 1) he
  refine ⟨h10, hXϑ, hlog, ?_⟩
  have h5 : Real.log X ≤ Real.log X ^ 5 := by
    calc Real.log X = Real.log X ^ 1 := (pow_one _).symm
      _ ≤ Real.log X ^ 5 := pow_le_pow_right₀ hlog (by norm_num)
  linarith

/-- LEAF. The continuous off rational family has the logarithm power five moment bound.

Step: the pure continuous remainder `continuousTail405`, that is the central discrete
Poisson translate minus the full continuous rational model on the major arcs, satisfies
the squared norm sum bound with logarithm power five for `X ^ theta` at least two and
`eta` below `X` to theta minus one half.  This is the real analytic estimate: the full
rational sum aliases and the selected central alias have already been removed from it,
and it is strictly weaker than the split target because no selected alias term is
subtracted.  Page 26 displays 7.4 to 7.7 and page 27 the major part of 7.8. -/
theorem leaf_off_continuous_tail_family432 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∀ η : ℝ, 0 < η → η ≤ 1 → η < (X : ℝ) ^ (ϑ - 1 / 2) →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖continuousTail405 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C, hC, h⟩ := continuous_tail_family405_split hϕ hG ϑ hϑ hϑ'
  exact ⟨C, hC, fun X hX _ η hη hη1 _ hscale ↦ h X hX η hη hη1 hscale⟩

/-- LEAF. The selected central alias family has the logarithm power five moment bound.

Step: the selected central alias coefficients, one term per smoothing scale `N`, obey
the squared norm sum bound with logarithm power five on the same range.  This is the
smoothing family moment of a single bounded major arc multiplier, so it is weaker than
the logarithm power one bound already available for it; the leaf records the exponent
the split needs.  Page 27 major contribution. -/
theorem leaf_off_central_alias_family432 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∀ η : ℝ, 0 < η → η ≤ 1 → η < (X : ℝ) ^ (ϑ - 1 / 2) →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖centralAlias432 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C, hC, hb⟩ := central_alias_family432 hϕ hG ϑ hϑ
  refine ⟨16 * C, by positivity, ?_⟩
  intro X hX hR η hη hη1 hsmall hscale
  have hlog := Real.log_natCast_nonneg X
  have hhalf : (1 / 2 : ℝ) ≤ Real.log X := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ X by exact_mod_cast hX)
    linarith [Real.log_two_gt_d9]
  have hlog5 : Real.log (X : ℝ) ≤ 16 * Real.log X ^ 5 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf 4
    have hh := mul_le_mul_of_nonneg_right hp hlog
    norm_num at hh
    nlinarith only [hh]
  have hh := hb X hX η hη hη1 hscale
  have hup := mul_le_mul_of_nonneg_left hlog5
    (by positivity : 0 ≤ C * η ^ 4 * (X : ℝ) ^ 3)
  nlinarith only [hh, hup]

/-- The split assembly: the exact sealed statement of `off_rational_family432`, proved
from the three leaves above through the coefficient triangle inequality and no sorry. -/
theorem off_rational_family432_split {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∀ η : ℝ, 0 < η → η ≤ 1 → η < (X : ℝ) ^ (ϑ - 1 / 2) →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖offRational432 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₀, hC₀, h₀⟩ := leaf_off_continuous_tail_family432 hϕ hG ϑ hϑ hϑ'
  obtain ⟨C₁, hC₁, h₁⟩ := leaf_off_central_alias_family432 hϕ hG ϑ hϑ hϑ'
  refine ⟨2 * (C₀ + C₁), by positivity, ?_⟩
  intro X hX hR η hη hη1 hηsmall hscale
  have harith := leaf_off_eta_range_arithmetic432 hϑ hX hη hη1 hscale
  have hcont := h₀ X hX hR η hη hη1 hηsmall hscale
  have hcent := h₁ X hX hR η hη hη1 hηsmall hscale
  have hsplit := coefficient_split328 (Finset.Icc 1 X)
    (fun N => offRational432 ϕ G X N ϑ η) (fun N => continuousTail405 ϕ G X N ϑ η)
  have hdiff : ∀ N ∈ Finset.Icc 1 X,
      ‖offRational432 ϕ G X N ϑ η - continuousTail405 ϕ G X N ϑ η‖ ^ 2 =
        ‖centralAlias432 ϕ G X N ϑ η‖ ^ 2 := by
    intro N _
    have h : offRational432 ϕ G X N ϑ η - continuousTail405 ϕ G X N ϑ η =
        -centralAlias432 ϕ G X N ϑ η := by
      unfold offRational432
      ring
    rw [h, norm_neg]
  rw [Finset.sum_congr rfl hdiff] at hsplit
  have hΘ : (0 : ℝ) ≤ η ^ 4 * (X : ℝ) ^ 3 * Real.log (X : ℝ) ^ 5 := by positivity
  have hsum : (∑ N ∈ Finset.Icc 1 X, ‖continuousTail405 ϕ G X N ϑ η‖ ^ 2) +
      ∑ N ∈ Finset.Icc 1 X, ‖centralAlias432 ϕ G X N ϑ η‖ ^ 2 ≤
        (C₀ + C₁) * (η ^ 4 * (X : ℝ) ^ 3 * Real.log (X : ℝ) ^ 5) := by
    nlinarith only [hcont, hcent]
  nlinarith only [hsplit, hsum]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.leaf_off_eta_range_arithmetic432
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_off_continuous_tail_family432
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_off_central_alias_family432
#print axioms LeanLab.BhowmikGrimmelt2026.off_rational_family432_split
