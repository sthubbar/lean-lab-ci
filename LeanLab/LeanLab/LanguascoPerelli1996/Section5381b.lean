import LeanLab.LanguascoPerelli1996.Section5381
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
P0071 page 360 display 25 at modulus one.
Extend the reciprocal arc width from Q at least two to Q at least one.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Section5381b
open Real MeasureTheory intervalIntegral

/-- Page 360 display 25. The damped character sum is continuous for positive N. -/
theorem continuous_dampedSum {N : ℝ} (hN : 0 < N) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : Continuous (fun η => Section5108.dampedSum N η χ) := by
  have he (x : ℝ) : ‖e x‖ = 1 := by
    unfold e
    rw [Complex.norm_exp]
    simp
  have hs := (Section5108.dampedSum_summable hN 0 χ).norm
  unfold Section5108.dampedSum
  have hc (n : ℕ) : Continuous (fun η : ℝ =>
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) *
        (Real.exp (-(n : ℝ) / N) : ℂ) * e ((n : ℝ) * η)) := by
    unfold e
    fun_prop
  exact continuous_tsum hc hs (fun n η => by
    simp only [norm_mul, he, mul_one]
    exact le_rfl)

/-- Page 360 display 25. Integer frequencies make the damped sum periodic
with period one, for every character. -/
theorem periodic_dampedSum (N : ℝ) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : Function.Periodic (fun η => Section5108.dampedSum N η χ) 1 := by
  intro η
  unfold Section5108.dampedSum
  apply tsum_congr
  intro n
  have he : e ((n : ℝ) * (η + 1)) = e ((n : ℝ) * η) := by
    unfold e
    have harg : (2 * Real.pi * Complex.I * (((n : ℝ) * (η + 1) : ℝ) : ℂ)) =
        2 * Real.pi * Complex.I * (((n : ℝ) * η : ℝ) : ℂ) +
          (n : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
    rw [harg, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  rw [he]

/-- Pages 359 and 360. The reciprocal principal term has squared mass
at most N on every symmetric interval when N is positive. -/
theorem principal_mass_le {N ξ : ℝ} (hN : 0 < N) (hξ : 0 ≤ ξ) :
    (∫ η in (-ξ)..ξ, ‖1 / Section5108.laplaceParameter N η‖ ^ 2) ≤ N := by
  have hn : N⁻¹ ≠ 0 := inv_ne_zero hN.ne'
  have he (η : ℝ) : ‖1 / Section5108.laplaceParameter N η‖ ^ 2 =
      ((N⁻¹) ^ 2 + (2 * Real.pi * η) ^ 2)⁻¹ := by
    rw [one_div, norm_inv, inv_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    unfold Section5108.laplaceParameter
    simp <;> congr 1 <;> ring
  simp_rw [he]
  rw [integral_comp_mul_left (fun t : ℝ => ((N⁻¹) ^ 2 + t ^ 2)⁻¹)
    (show 2 * Real.pi ≠ 0 by positivity), integral_inv_sq_add_sq hn]
  simp only [smul_eq_mul, inv_inv]
  have ha := Real.arctan_lt_pi_div_two (2 * Real.pi * ξ / N⁻¹)
  have hb := Real.neg_pi_div_two_lt_arctan (2 * Real.pi * -ξ / N⁻¹)
  have hscale : 0 < (2 * Real.pi)⁻¹ * N := by positivity
  have hh := mul_le_mul_of_nonneg_left (show
      Real.arctan (2 * Real.pi * ξ / N⁻¹) -
        Real.arctan (2 * Real.pi * -ξ / N⁻¹) ≤ Real.pi by linarith) hscale.le
  have hp : (2 * Real.pi)⁻¹ * N * Real.pi = N / 2 := by field_simp
  nlinarith

/-- Page 360 display 25, periodic mass bookkeeping for its widest arcs.
Two adjacent periods have twice the mass of the centered unit period. -/
theorem double_period_mass {g : ℝ → ℝ} (hg : Continuous g) (hp : Function.Periodic g 1) :
    (∫ t in (-1 : ℝ)..1, g t) = 2 * (∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), g t) := by
  rw [← integral_add_adjacent_intervals (hg.intervalIntegrable (-1) 0)
    (hg.intervalIntegrable 0 1)]
  have h1 := hp.intervalIntegral_add_eq (-1) (-(1 / 2 : ℝ))
  have h2 := hp.intervalIntegral_add_eq 0 (-(1 / 2 : ℝ))
  norm_num only [neg_add_cancel, zero_add, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h1 h2
  rw [h1, h2]
  ring

/-- Page 360 display 25 for modulus one, integer N at least four and
all 1 at most Q at most N. CONDITIONAL ON RiemannHypothesis alone.
The interval below Q equal to two follows by periodicity and the
explicit integral bound for the principal term. -/
theorem estimate25_mod_one_all_Q (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N → ∀ Q : ℝ, 1 ≤ Q → Q ≤ N →
      (∫ η in (-(1 / Q))..(1 / Q),
        ‖Section5108.dampedSum (N : ℝ) η (1 : DirichletCharacter ℂ 1) -
          1 / Section5108.laplaceParameter (N : ℝ) η‖ ^ 2) ≤
        C * (N : ℝ) * Real.log N ^ 2 / Q := by
  obtain ⟨C, hC, hm⟩ := Section5381.estimate25_mod_one hRH
  refine ⟨8 * C + 20, by positivity, ?_⟩
  intro N hN Q hQ hQN
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hQ0 : 0 < Q := by linarith
  by_cases hQ2 : 2 ≤ Q
  · refine (hm N hN Q hQ2 hQN).trans ?_
    gcongr
    linarith
  have hQlt : Q < 2 := lt_of_not_ge hQ2
  let S := fun t => Section5108.dampedSum (N : ℝ) t (1 : DirichletCharacter ℂ 1)
  let Z := fun t => 1 / Section5108.laplaceParameter (N : ℝ) t
  have hSc : Continuous S := continuous_dampedSum hN0 _
  have hZc : Continuous Z := by
    apply continuous_const.div
    · unfold Section5108.laplaceParameter
      fun_prop
    · exact fun t => Section5108.laplaceParameter_ne_zero hN0 t
  have hRc : Continuous (fun t => ‖S t - Z t‖ ^ 2) := ((hSc.sub hZc).norm.pow 2)
  have hnorm (z u : ℂ) : ‖z - u‖ ^ 2 ≤ 2 * (‖z‖ ^ 2 + ‖u‖ ^ 2) := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le z u) 2
    nlinarith [sq_nonneg (‖z‖ - ‖u‖)]
  have hback (t : ℝ) : ‖S t‖ ^ 2 ≤ 2 * (‖S t - Z t‖ ^ 2 + ‖Z t‖ ^ 2) := by
    simpa only [sub_neg_eq_add, sub_add_cancel, norm_neg] using hnorm (S t - Z t) (-Z t)
  have hM0 := hm N hN 2 (by norm_num) (by linarith)
  change (∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), ‖S t - Z t‖ ^ 2) ≤
    C * (N : ℝ) * Real.log N ^ 2 / 2 at hM0
  have hZS : (∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), ‖Z t‖ ^ 2) ≤ N :=
    principal_mass_le hN0 (by norm_num)
  have hZF : (∫ t in (-1 : ℝ)..1, ‖Z t‖ ^ 2) ≤ N := principal_mass_le hN0 (by norm_num)
  have hS0 := integral_mono_on (μ := volume) (a := (-(1 / 2 : ℝ))) (b := (1 / 2 : ℝ))
    (by norm_num) ((hSc.norm.pow 2).intervalIntegrable _ _)
    ((continuous_const.mul (hRc.add (hZc.norm.pow 2))).intervalIntegrable _ _)
    (fun t _ => hback t)
  simp only [Pi.mul_apply, Pi.add_apply] at hS0
  rw [intervalIntegral.integral_const_mul, integral_add (hRc.intervalIntegrable _ _)
    ((hZc.norm.pow 2).intervalIntegrable _ _)] at hS0
  have hperiod : Function.Periodic (fun t => ‖S t‖ ^ 2) 1 := by
    intro t
    change ‖S (t + 1)‖ ^ 2 = ‖S t‖ ^ 2
    rw [show S (t + 1) = S t from periodic_dampedSum (N : ℝ) (1 : DirichletCharacter ℂ 1) t]
  have hSF := double_period_mass (hSc.norm.pow 2) hperiod
  have hRF := integral_mono_on (μ := volume) (a := (-1 : ℝ)) (b := 1) (by norm_num)
    (hRc.intervalIntegrable _ _)
    ((continuous_const.mul ((hSc.norm.pow 2).add (hZc.norm.pow 2))).intervalIntegrable _ _)
    (fun t _ => hnorm (S t) (Z t))
  simp only [Pi.mul_apply, Pi.add_apply] at hRF
  rw [intervalIntegral.integral_const_mul, integral_add ((hSc.norm.pow 2).intervalIntegrable _ _)
    ((hZc.norm.pow 2).intervalIntegrable _ _)] at hRF
  simp only [Pi.pow_apply] at hS0 hSF hRF
  have hlogN : 1 ≤ Real.log N := by
    have h4 : (1 : ℝ) ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith [Real.log_two_gt_d9]
    exact h4.trans (Real.log_le_log (by norm_num) hN4)
  have hl2 : 1 ≤ Real.log N ^ 2 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hlogN 2
  have hfull : (∫ t in (-1 : ℝ)..1, ‖S t - Z t‖ ^ 2) ≤
      (4 * C + 10) * (N : ℝ) * Real.log N ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hl2 (show (0 : ℝ) ≤ N by positivity)]
  have hxi : 1 / Q ≤ (1 : ℝ) := (div_le_one hQ0).2 hQ
  have hxi0 : 0 ≤ 1 / Q := by positivity
  have hmono : (∫ t in (-(1 / Q))..(1 / Q), ‖S t - Z t‖ ^ 2) ≤
      ∫ t in (-1 : ℝ)..1, ‖S t - Z t‖ ^ 2 :=
    integral_mono_interval (by linarith) (by linarith) hxi
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hRc.intervalIntegrable _ _)
  refine hmono.trans (hfull.trans ?_)
  apply (le_div_iff₀ hQ0).2
  have hp : 0 ≤ (4 * C + 10) * (N : ℝ) * Real.log N ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hQlt.le hp]

end LeanLab.LanguascoPerelli1996.Section5381b

#print axioms LeanLab.LanguascoPerelli1996.Section5381b.continuous_dampedSum
#print axioms LeanLab.LanguascoPerelli1996.Section5381b.periodic_dampedSum
#print axioms LeanLab.LanguascoPerelli1996.Section5381b.principal_mass_le

#print axioms LeanLab.LanguascoPerelli1996.Section5381b.double_period_mass
#print axioms LeanLab.LanguascoPerelli1996.Section5381b.estimate25_mod_one_all_Q
