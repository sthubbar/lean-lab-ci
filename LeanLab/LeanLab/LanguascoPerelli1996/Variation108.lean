import LeanLab.LanguascoPerelli1996.FiniteEnergy108

/-!
A coefficient norm route to P0071 page 355 display 13.
The bound keeps the sum of coefficient norms. It does not prove the required
bound in terms of the maximum correlation alone.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Variation108
open Real Complex intervalIntegral
open scoped ContDiff

/-- Page 355 display 13, a weaker bound for a finite exponential sum.
Frequencies of absolute value at most T give total variation at most
4 T times the square of the sum of coefficient norms on minus one to one. -/
theorem finite_variation_l1 {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ)
    {T : ℝ} (hT : 0 ≤ T) (hγ : ∀ i ∈ s, |γ i| ≤ T) :
    (∫ v in (-1 : ℝ)..1,
      |deriv (fun t : ℝ => ‖∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * t)‖ ^ 2) v|) ≤
        4 * T * (∑ i ∈ s, ‖c i‖) ^ 2 := by
  classical
  let f : ℝ → ℂ := fun v => ∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * v)
  let d : ℝ → ℂ := fun v => ∑ i ∈ s, c i *
    (Complex.exp (Complex.I * γ i * v) * (Complex.I * γ i))
  let L : ℝ := ∑ i ∈ s, ‖c i‖
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hcast : ContDiff ℝ ∞ (fun v : ℝ => (v : ℂ)) := Complex.ofRealCLM.contDiff
  have hfc : ContDiff ℝ ∞ f := by dsimp [f]; fun_prop
  have hd (v : ℝ) : HasDerivAt f (d v) v := by
    have hbase : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) v := by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using! Complex.ofRealCLM.hasDerivAt
    have hi (i : ι) : HasDerivAt (fun t : ℝ => c i * Complex.exp (Complex.I * γ i * t))
        (c i * (Complex.exp (Complex.I * γ i * v) * (Complex.I * γ i))) v := by
      simpa only [mul_one] using ((hbase.const_mul (Complex.I * γ i)).cexp.const_mul (c i))
    exact HasDerivAt.fun_sum (u := s) (fun i _ => hi i)
  have he (i : ι) (v : ℝ) : ‖Complex.exp (Complex.I * γ i * v)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hfbound (v : ℝ) : ‖f v‖ ≤ L := by
    dsimp [f, L]
    calc
      _ ≤ ∑ i ∈ s, ‖c i * Complex.exp (Complex.I * γ i * v)‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, he, mul_one]
  have hdbound (v : ℝ) : ‖d v‖ ≤ T * L := by
    dsimp [d, L]
    calc
      _ ≤ ∑ i ∈ s, ‖c i * (Complex.exp (Complex.I * γ i * v) * (Complex.I * γ i))‖ :=
        norm_sum_le _ _
      _ = ∑ i ∈ s, ‖c i‖ * |γ i| := by
        simp only [norm_mul, he, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
      _ ≤ ∑ i ∈ s, ‖c i‖ * T := Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hγ i hi) (norm_nonneg _)
      _ = T * ∑ i ∈ s, ‖c i‖ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  have hp (v : ℝ) : |deriv (fun t : ℝ => ‖f t‖ ^ 2) v| ≤ 2 * T * L ^ 2 := by
    rw [(hd v).norm_sq.deriv, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hh := norm_inner_le_norm (𝕜 := ℝ) (f v) (d v)
    simp only [Real.norm_eq_abs] at hh
    calc
      _ ≤ 2 * (‖f v‖ * ‖d v‖) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ ≤ 2 * (L * (T * L)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul (hfbound v) (hdbound v) (norm_nonneg _) hL
      _ = _ := by ring
  have hcont : Continuous (fun v => |deriv (fun t : ℝ => ‖f t‖ ^ 2) v|) :=
    ((hfc.norm_sq ℂ).continuous_deriv (by simp)).abs
  have hint := integral_mono_on (μ := MeasureTheory.volume) (a := (-1 : ℝ)) (b := 1)
    (by norm_num) (hcont.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _) (fun v _ => hp v)
  simpa only [integral_const, sub_neg_eq_add, one_add_one_eq_two, smul_eq_mul,
    show (2 : ℝ) * (2 * T * L ^ 2) = 4 * T * L ^ 2 by ring] using hint

end LeanLab.LanguascoPerelli1996.Variation108
