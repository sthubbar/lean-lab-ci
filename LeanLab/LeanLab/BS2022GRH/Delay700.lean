/- AI wrote this Lean code for CODEX task700. Goldbach is open.
An elementary geometric majorant for BJS arXiv 2207.09452v6
p. 6 displays 15 to 18 and p. 7 Lemma 8.
https://arxiv.org/abs/2207.09452v6 -/
import Mathlib

namespace LeanLab.BS2022GRH.Delay700
open Real MeasureTheory Set
noncomputable section

/-- Auxiliary exponential weight for the convergence argument in BJS Lemma 8. -/
def weight (s : ℝ) : ℝ :=
  if s ≤ 2 then exp (-2) else if s ≤ 4 then exp (-s) else 3 / 4 * exp (-s)

/-- The auxiliary weight is positive. -/
theorem weight_pos (s : ℝ) : 0 < weight s := by
  unfold weight
  split_ifs <;> positivity

/-- The shifted weight lies below a single exponential on the integration domain. -/
theorem weight_shift_le (t : ℝ) (_ht : 2 ≤ t) : weight (t - 1) ≤ exp (1 - t) := by
  unfold weight
  split_ifs with h2 h4
  · exact exp_le_exp.mpr (by linarith)
  · rw [show -(t - 1) = 1 - t by ring]
  · rw [show -(t - 1) = 1 - t by ring]
    nlinarith [exp_pos (1 - t)]

/-- The shifted weight is integrable on every required upper half line. -/
theorem weight_shift_integrable (a : ℝ) (ha : 2 ≤ a) :
    IntegrableOn (fun t => weight (t - 1)) (Ioi a) := by
  have hi : IntegrableOn (fun t : ℝ => exp (1-t)) (Ioi a) := by
    simp_rw [show ∀ t : ℝ, 1-t=1+-t by intro; ring, exp_add]
    exact (integrableOn_exp_neg_Ioi a).const_mul _
  have hm : Measurable (fun t : ℝ => weight (t-1)) := by
    unfold weight
    exact measurable_const.ite (measurableSet_le (by fun_prop) measurable_const)
      ((by fun_prop : Measurable (fun t : ℝ => exp (-(t-1)))).ite
        (measurableSet_le (by fun_prop) measurable_const) (by fun_prop))
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (weight_pos _)]
  exact weight_shift_le t (by linarith [Set.mem_Ioi.mp ht])

/-- Integral of the single shifted exponential. -/
theorem exp_shift_integral (a : ℝ) :
    (∫ t : ℝ in Ioi a, exp (1 - t)) = exp (1 - a) := by
  simp_rw [show ∀ t : ℝ, 1-t=1+-t by intro; ring, exp_add]
  rw [integral_const_mul, integral_exp_neg_Ioi]

/-- The shifted weight has an elementary exponential tail bound. -/
theorem weight_tail_le (a : ℝ) (ha : 2 ≤ a) :
    (∫ t : ℝ in Ioi a, weight (t - 1)) ≤ exp (1 - a) := by
  rw [← exp_shift_integral]
  apply setIntegral_mono_of_nonneg
  · intro t _; exact (weight_pos _).le
  · intro t ht; exact weight_shift_le t (by linarith [Set.mem_Ioi.mp ht])
  · simp_rw [show ∀ t : ℝ, 1-t=1+-t by intro; ring, exp_add]
    exact (integrableOn_exp_neg_Ioi a).const_mul _

/-- The integral at three retains the strict saving in the far tail. -/
theorem weight_tail_three :
    (∫ t : ℝ in Ioi 3, weight (t - 1)) = exp (-2) - exp (-4) / 4 := by
  have hi5 : IntegrableOn (fun t : ℝ => weight (t - 1)) (Ioi 5) :=
    weight_shift_integrable 5 (by norm_num)
  have htail : (∫ t : ℝ in Ioi 5, weight (t - 1)) = 3 / 4 * exp (-4) := by
    calc
      _ = ∫ t : ℝ in Ioi 5, 3 / 4 * exp (1-t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simp only [weight, ite_eq_right (by linarith [Set.mem_Ioi.mp ht] : ¬ t-1 ≤ 2),
          ite_eq_right (by linarith [Set.mem_Ioi.mp ht] : ¬ t-1 ≤ 4)]
        congr 2; ring
      _ = _ := by rw [integral_const_mul, exp_shift_integral]; norm_num
  have hmid : (∫ t : ℝ in (3 : ℝ)..5, weight (t-1)) = exp (-2) - exp (-4) := by
    calc
      _ = ∫ t : ℝ in (3 : ℝ)..5, exp (1-t) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with t
        intro ht
        rw [uIoc_of_le (by norm_num : (3 : ℝ) ≤ 5)] at ht
        have h2 : ¬ t-1 ≤ 2 := by linarith [ht.1]
        have h4 : t-1 ≤ 4 := by linarith [ht.2]
        simp [weight, h2, h4]
      _ = _ := by
        have hd (t : ℝ) : HasDerivAt (fun t : ℝ => -exp (1-t)) (exp (1-t)) t := by
          convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).exp).neg using 1 <;> first | (ext x; rfl) | (dsimp; ring)
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
          ((by fun_prop : Continuous (fun t : ℝ => exp (1-t))).intervalIntegrable 3 5)]
        norm_num
        ring
  have hh := intervalIntegral.integral_interval_add_Ioi
    (weight_shift_integrable 3 (by norm_num)) hi5
  rw [hmid, htail] at hh
  linarith

/-- Exact integral in the low range needed for the contraction. -/
theorem weight_tail_low (a : ℝ) (ha : 2 ≤ a) (hb : a ≤ 3) :
    (∫ t : ℝ in Ioi a, weight (t-1)) = (4-a) * exp (-2) - exp (-4) / 4 := by
  have hmid : (∫ t : ℝ in a..3, weight (t-1)) = (3-a) * exp (-2) := by
    calc
      _ = ∫ t : ℝ in a..3, exp (-2) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hb] at ht
        simp [weight, show t-1 ≤ 2 by linarith [ht.2]]
      _ = _ := by simp [intervalIntegral.integral_const, smul_eq_mul]
  have hh := intervalIntegral.integral_interval_add_Ioi
    (weight_shift_integrable a ha) (weight_shift_integrable 3 (by norm_num))
  rw [hmid, weight_tail_three] at hh
  linarith

/-- The weighted exponential decreases above one. -/
theorem antitone_mul_exp_neg : AntitoneOn (fun s : ℝ => s * exp (-s)) (Ici 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 1)
    (by fun_prop) (f' := fun s => (1-s)*exp (-s))
  · intro s _
    apply HasDerivAt.hasDerivWithinAt
    convert (hasDerivAt_id s).mul ((hasDerivAt_id s).neg.exp) using 1 <;> first | (ext x; rfl) | (dsimp; ring)
  · intro s hs
    have hs' : 1 ≤ s := (interior_subset hs)
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (exp_pos _).le

/-- The low range scalar inequality in the geometric contraction. -/
theorem low_scalar (s : ℝ) (hs : 2 ≤ s) :
    (4-s) * exp (-2) ≤ s * exp (-s) := by
  have hd (x : ℝ) (hx : 2 ≤ x) :
      HasDerivAt (fun x : ℝ => (4-x)*exp (x-2)/x)
        (-exp (x-2)*(x-2)^2/x^2) x := by
    have hx0 : x ≠ 0 := by linarith
    convert (((hasDerivAt_const x (4 : ℝ)).sub (hasDerivAt_id x)).mul
      ((hasDerivAt_id x).sub_const 2).exp).div (hasDerivAt_id x) hx0 using 1
    · rfl
    · dsimp
      field_simp
      ring
  have hm : AntitoneOn (fun x : ℝ => (4-x)*exp (x-2)/x) (Ici 2) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 2)
      ((by fun_prop : Continuous (fun x : ℝ => (4-x)*exp (x-2))).continuousOn.div
        continuous_id.continuousOn (fun x hx => by dsimp; linarith [Set.mem_Ici.mp hx]))
      (f' := fun x => -exp (x-2)*(x-2)^2/x^2)
    · intro x hx
      exact (hd x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith [exp_pos (x-2)]) (sq_nonneg _))
        (sq_nonneg _)
  have hb := hm (by simp : (2 : ℝ) ∈ Ici 2) hs hs
  norm_num at hb
  have hb' := (div_le_iff₀ (by linarith : 0 < s)).mp hb
  have hh := mul_le_mul_of_nonneg_right hb' (exp_pos (-s)).le
  have he : exp (s-2)*exp (-s) = exp (-2) := by rw [← exp_add]; congr 1; ring
  nlinarith [he]

/-- The far tail saving is larger than one percent of the global envelope. -/
theorem tail_saving : exp (-1) / 100 ≤ exp (-4) / 4 := by
  have he : exp 1 ≤ 11/4 := le_trans exp_one_lt_d9.le (by norm_num)
  have he3 : exp 3 ≤ 25 := by
    calc
      exp 3 = (exp 1)^3 := by rw [← exp_nat_mul]; norm_num
      _ ≤ (11/4 : ℝ)^3 := pow_le_pow_left₀ (exp_pos _).le he 3
      _ ≤ 25 := by norm_num
  have hx : exp (-1) = exp 3 * exp (-4) := by rw [← exp_add]; norm_num
  rw [hx]
  nlinarith [exp_pos (-4)]

/-- The majorant contracts by 99/100 on the even domain. -/
theorem weight_contraction (s : ℝ) (hs : 2 ≤ s) :
    (∫ t : ℝ in Ioi s, weight (t-1)) ≤ (99/100 : ℝ) * s * weight s := by
  by_cases h3 : s ≤ 3
  · rw [weight_tail_low s hs h3]
    have hw : weight s = exp (-s) := by
      by_cases h2 : s ≤ 2
      · have he : s=2 := by linarith
        subst s; simp [weight]
      · simp [weight, h2, show s ≤ 4 by linarith]
    rw [hw]
    have hl := low_scalar s hs
    have hu := mul_exp_neg_le_exp_neg_one s
    have hd := tail_saving
    nlinarith
  · have hu := weight_tail_le s hs
    have he : exp (1-s) = exp 1 * exp (-s) := by rw [← exp_add]; congr 1
    have hb : exp 1 ≤ (99/100 : ℝ)*3 := le_trans exp_one_lt_d9.le (by norm_num)
    rw [he] at hu
    apply hu.trans
    unfold weight
    rw [ite_eq_right (by linarith : ¬s ≤ 2)]
    split_ifs with h4
    · nlinarith [exp_pos (-s)]
    · have hsl : 4 ≤ s := le_of_not_ge h4
      nlinarith [exp_pos (-s)]

/-- The same contraction holds at the fixed odd integration endpoint. -/
theorem weight_contraction_odd (s : ℝ) (hs : 1 ≤ s) :
    (∫ t : ℝ in Ioi (max s 3), weight (t-1)) ≤ (99/100 : ℝ)*s*weight s := by
  by_cases h3 : s ≤ 3
  · rw [max_eq_right h3, weight_tail_three]
    have hl : exp (-2) ≤ s*weight s := by
      by_cases h2 : s ≤ 2
      · simp only [weight, ite_eq_left h2]
        nlinarith [exp_pos (-2)]
      · have hm := antitone_mul_exp_neg (show s ∈ Ici 1 from hs)
          (by norm_num : (3 : ℝ) ∈ Ici 1) h3
        have he : exp (-2) = exp 1 * exp (-3) := by rw [← exp_add]; norm_num
        rw [weight, ite_eq_right h2, ite_eq_left (by linarith : s ≤ 4)]
        rw [he]
        have hb : exp 1 ≤ 3 := le_trans exp_one_lt_d9.le (by norm_num)
        nlinarith [exp_pos (-3)]
    have hb : exp (-2) ≤ exp (-1) := exp_le_exp.mpr (by norm_num)
    have hd := tail_saving
    nlinarith
  · rw [max_eq_left (le_of_not_ge h3)]
    exact weight_contraction s (by linarith)

end
end LeanLab.BS2022GRH.Delay700

#print axioms LeanLab.BS2022GRH.Delay700.weight_pos
#print axioms LeanLab.BS2022GRH.Delay700.weight_shift_le
#print axioms LeanLab.BS2022GRH.Delay700.weight_shift_integrable
#print axioms LeanLab.BS2022GRH.Delay700.exp_shift_integral
#print axioms LeanLab.BS2022GRH.Delay700.weight_tail_le
#print axioms LeanLab.BS2022GRH.Delay700.weight_tail_three
#print axioms LeanLab.BS2022GRH.Delay700.weight_tail_low
#print axioms LeanLab.BS2022GRH.Delay700.antitone_mul_exp_neg
#print axioms LeanLab.BS2022GRH.Delay700.low_scalar
#print axioms LeanLab.BS2022GRH.Delay700.tail_saving
#print axioms LeanLab.BS2022GRH.Delay700.weight_contraction
#print axioms LeanLab.BS2022GRH.Delay700.weight_contraction_odd
