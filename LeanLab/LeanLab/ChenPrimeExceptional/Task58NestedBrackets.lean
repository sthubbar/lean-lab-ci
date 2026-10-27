/-
AI wrote this Lean code for CODEX task58.
Tight bounds for the actual two nested integrals of the P0039 lab model.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task58OuterWeights
import LeanLab.ChenPrimeExceptional.Task58IntegralBounds

open Real Finset intervalIntegral MeasureTheory Set

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

def j1Approx (w : ℝ) : ℝ := Happrox w * j1WeightPoly w

def j2Approx (w : ℝ) : ℝ := (1 + Happrox w) * j2WeightPoly w

def j1True (w : ℝ) : ℝ := H (2 + w) / (3 + w)

def j2True (w : ℝ) : ℝ := (1 + H (2 + w)) / ((2 - w) * (3 + w))

theorem continuous_from_terms {f : ℝ → ℝ} {ts : Terms}
    (he : ∀ z : ℝ, evalTerms ts z = f (z + 1 / 2)) : Continuous f := by
  have h : Continuous (fun w : ℝ => evalTerms ts (w - 1 / 2)) :=
    (evalTerms_continuous _).comp (continuous_id.sub continuous_const)
  convert h using 1
  ext w
  rw [he]
  congr 1
  ring

theorem approx_continuous : Continuous j1Approx ∧ Continuous j2Approx := by
  have hh : Continuous Happrox := continuous_from_terms centeredHTerms_eval
  have h1 : Continuous j1WeightPoly := continuous_from_terms j1WeightTerms_eval
  have h2 : Continuous j2WeightPoly := continuous_from_terms j2WeightTerms_eval
  exact ⟨hh.mul h1, (continuous_const.add hh).mul h2⟩

theorem true_continuous : ContinuousOn j1True (Set.Icc (0 : ℝ) 1) ∧
    ContinuousOn j2True (Set.Icc (0 : ℝ) 1) := by
  have hh : ContinuousOn (fun w : ℝ => H (2 + w)) (Set.Icc 0 1) :=
    H_continuous.comp (continuousOn_const.add continuousOn_id) (by
      intro w hw
      change (2 + w : ℝ) ∈ Set.Icc 2 3
      constructor <;> linarith [hw.1, hw.2])
  constructor
  · exact hh.div (continuousOn_const.add continuousOn_id) (by
      intro w hw
      change 3 + w ≠ 0
      linarith [hw.1])
  · apply (continuousOn_const.add hh).div
      ((continuousOn_const.sub continuousOn_id).mul (continuousOn_const.add continuousOn_id))
    intro w hw
    change (2 - w) * (3 + w) ≠ 0
    exact mul_ne_zero (by linarith [hw.2]) (by linarith [hw.1])

theorem product_error {A A' B B' M εA εB C : ℝ}
    (hA : |A| ≤ M) (hAe : |A - A'| ≤ εA) (hBe : |B - B'| ≤ εB) (hB : |B'| ≤ C) :
    |A * B - A' * B'| ≤ M * εB + εA * C := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hA
  have hεA : 0 ≤ εA := (abs_nonneg _).trans hAe
  have he : A * B - A' * B' = A * (B - B') + (A - A') * B' := by ring
  rw [he]
  calc
    _ ≤ |A * (B - B')| + |(A - A') * B'| := abs_add_le _ _
    _ = |A| * |B - B'| + |A - A'| * |B'| := by rw [abs_mul, abs_mul]
    _ ≤ _ := add_le_add (mul_le_mul hA hBe (abs_nonneg _) hM)
      (mul_le_mul hAe hB (abs_nonneg _) hεA)

theorem j1Approx_error {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    |j1Approx w - j1True w| ≤ (3 / 1000000000 : ℝ) := by
  have h := product_error (Happrox_bounds hw).1 (Happrox_error hw)
    (j1WeightPoly_error hw) (outer_reciprocal_bounds hw).1
  have he : j1Approx w - j1True w = Happrox w * j1WeightPoly w -
      H (2 + w) * (1 / (3 + w)) := by unfold j1Approx j1True; ring
  rw [he]
  exact h.trans (by norm_num)

theorem j2Approx_error {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    |j2Approx w - j2True w| ≤ (3 / 1000000000 : ℝ) := by
  have herr : |(1 + Happrox w) - (1 + H (2 + w))| ≤ (1 / 1000000000 : ℝ) := by
    simpa only [add_sub_add_left_eq_sub] using Happrox_error hw
  have h := product_error (Happrox_bounds hw).2 herr
    (j2WeightPoly_error hw) (outer_reciprocal_bounds hw).2
  have he : j2Approx w - j2True w = (1 + Happrox w) * j2WeightPoly w -
      (1 + H (2 + w)) * (1 / ((2 - w) * (3 + w))) := by unfold j2Approx j2True; ring
  rw [he]
  exact h.trans (by norm_num)

theorem j1Approx_mass : (∫ w in (0 : ℝ)..1, j1Approx w) = (j1MassQ : ℝ) := by
  have he : ∀ z : ℝ, evalTerms (mulTerms centeredHTerms j1WeightTerms) z = j1Approx (z + 1 / 2) := by
    intro z
    rw [evalTerms_mul, centeredHTerms_eval, j1WeightTerms_eval]
    rfl
  have h := integral_evalTerms (mulTerms centeredHTerms j1WeightTerms) (-1 / 2) (1 / 2)
  rw [integral_congr (fun z _ => he z), integral_comp_add_right] at h
  norm_num [j1MassQ] at h ⊢
  exact h

theorem j2Approx_mass : (∫ w in (0 : ℝ)..1, j2Approx w) = (j2MassQ : ℝ) := by
  have he : ∀ z : ℝ, evalTerms (mulTerms ((1, 0) :: centeredHTerms) j2WeightTerms) z = j2Approx (z + 1 / 2) := by
    intro z
    rw [evalTerms_mul, evalTerms_cons, centeredHTerms_eval, j2WeightTerms_eval]
    norm_num [j2Approx]
  have h := integral_evalTerms (mulTerms ((1, 0) :: centeredHTerms) j2WeightTerms) (-1 / 2) (1 / 2)
  rw [integral_congr (fun z _ => he z), integral_comp_add_right] at h
  norm_num [j2MassQ] at h ⊢
  exact h

theorem J1_unit : U1435.J1 = ∫ w in (0 : ℝ)..1, j1True w := by
  change (∫ t in (3 : ℝ)..4, j1Kernel t) = _
  have he : ∀ w : ℝ, j1Kernel (3 + w) = j1True w := by
    intro w
    unfold j1Kernel j1True
    congr 2
    ring
  calc
    _ = ∫ w in (0 : ℝ)..1, j1Kernel (3 + w) := by
      simpa only [add_zero, show (3 : ℝ) + 1 = 4 by norm_num] using
        (integral_comp_add_left (a := (0 : ℝ)) (b := (1 : ℝ)) j1Kernel 3).symm
    _ = _ := integral_congr (fun w _ => he w)

theorem J2_unit : U1435.J2 = ∫ w in (0 : ℝ)..1, j2True w := by
  have he : ∀ t ∈ Set.Icc (1 / 10 : ℝ) (1 / 5), j2Kernel t = 10 * j2True (-10 * t + 2) := by
    intro t ht
    have hs : 5 - 10 * t ∈ Set.Icc (3 : ℝ) 4 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hy0 : 5 - 10 * t ≠ 0 := by linarith [ht.2]
    unfold j2Kernel j2True
    rw [Fn_on hs]
    have ha : (5 : ℝ) - 10 * t - 1 = 2 + (-10 * t + 2) := by ring
    rw [ha]
    have hb : (2 : ℝ) - (-10 * t + 2) = 10 * t := by ring
    have hc : (3 : ℝ) + (-10 * t + 2) = 5 - 10 * t := by ring
    rw [hb, hc]
    field_simp [ht0, hy0, show (5 : ℝ) - t * 10 ≠ 0 by linarith [ht.2]]
    <;> ring
  change (∫ t in (1 / 10 : ℝ)..(1 / 5), j2Kernel t) = _
  rw [integral_congr (fun t ht => he t (by
    rw [Set.uIcc_of_le (show (1 / 10 : ℝ) ≤ 1 / 5 by norm_num)] at ht
    exact ht))]
  rw [intervalIntegral.integral_const_mul, integral_comp_mul_add j2True (by norm_num : (-10 : ℝ) ≠ 0) 2]
  norm_num
  rw [integral_symm]
  ring

theorem unit_integral_error {f g : ℝ → ℝ} {e : ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (hg : ContinuousOn g (Set.Icc 0 1))
    (he : ∀ w ∈ Set.Icc (0 : ℝ) 1, |f w - g w| ≤ e) :
    |(∫ w in (0 : ℝ)..1, f w) - ∫ w in (0 : ℝ)..1, g w| ≤ e := by
  have hfi : IntervalIntegrable f volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hf
  have hgi : IntervalIntegrable g volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hg
  have h := norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (1 : ℝ)) (C := e)
    (f := fun w => f w - g w) (by
      intro w hw
      rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hw
      rw [Real.norm_eq_abs]
      exact he w ⟨hw.1.le, hw.2⟩)
  rw [integral_sub hfi hgi, Real.norm_eq_abs] at h
  simpa using h

theorem J1_polynomial_error : |U1435.J1 - (j1MassQ : ℝ)| ≤ (3 / 1000000000 : ℝ) := by
  have h := unit_integral_error approx_continuous.1.continuousOn true_continuous.1
    (fun w hw => j1Approx_error hw)
  rw [j1Approx_mass, ← J1_unit, abs_sub_comm] at h
  exact h

theorem J2_polynomial_error : |U1435.J2 - (j2MassQ : ℝ)| ≤ (3 / 1000000000 : ℝ) := by
  have h := unit_integral_error approx_continuous.2.continuousOn true_continuous.2
    (fun w hw => j2Approx_error hw)
  rw [j2Approx_mass, ← J2_unit, abs_sub_comm] at h
  exact h

theorem J1_bracket_unconditional : (0.014886 : ℝ) ≤ U1435.J1 ∧ U1435.J1 ≤ 0.014887 := by
  have hl : ((0.01488633 : ℚ) : ℝ) ≤ (j1MassQ : ℝ) := Rat.cast_le.mpr j1MassQ_bounds.1
  have hu : (j1MassQ : ℝ) ≤ ((0.01488637 : ℚ) : ℝ) := Rat.cast_le.mpr j1MassQ_bounds.2
  norm_num at hl hu
  have he := J1_polynomial_error
  rw [abs_le] at he
  constructor <;> linarith

theorem J2_bracket_unconditional : (0.208074 : ℝ) ≤ U1435.J2 ∧ U1435.J2 ≤ 0.208075 := by
  have hl : ((0.20807491 : ℚ) : ℝ) ≤ (j2MassQ : ℝ) := Rat.cast_le.mpr j2MassQ_bounds.1
  have hu : (j2MassQ : ℝ) ≤ ((0.20807495 : ℚ) : ℝ) := Rat.cast_le.mpr j2MassQ_bounds.2
  norm_num at hl hu
  have he := J2_polynomial_error
  rw [abs_le] at he
  constructor <;> linarith

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.continuous_from_terms
#print axioms LeanLab.ChenPrimeExceptional.Task58.approx_continuous
#print axioms LeanLab.ChenPrimeExceptional.Task58.true_continuous
#print axioms LeanLab.ChenPrimeExceptional.Task58.product_error
#print axioms LeanLab.ChenPrimeExceptional.Task58.j1Approx_error
#print axioms LeanLab.ChenPrimeExceptional.Task58.j2Approx_error
#print axioms LeanLab.ChenPrimeExceptional.Task58.j1Approx_mass
#print axioms LeanLab.ChenPrimeExceptional.Task58.j2Approx_mass
#print axioms LeanLab.ChenPrimeExceptional.Task58.J1_unit
#print axioms LeanLab.ChenPrimeExceptional.Task58.J2_unit
#print axioms LeanLab.ChenPrimeExceptional.Task58.unit_integral_error
#print axioms LeanLab.ChenPrimeExceptional.Task58.J1_polynomial_error
#print axioms LeanLab.ChenPrimeExceptional.Task58.J2_polynomial_error
#print axioms LeanLab.ChenPrimeExceptional.Task58.J1_bracket_unconditional
#print axioms LeanLab.ChenPrimeExceptional.Task58.J2_bracket_unconditional
