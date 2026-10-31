import LeanLab.Zhao2025.BIntegral

/-!
The kernels in the printed Laplace representation are nonnegative.
Source: Zhao 2025, displays 2.22 and 2.24, page 6.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- The split Laplace representation is nonnegative and antitone in its parameter. -/
theorem BLaplace_order (t l L l0 : ℝ) (ht : 0 ≤ t) (h0 : 0 < l0) (hl : l ≤ L) :
    0 ≤ BLaplace t l l0 ∧ BLaplace t L l0 ≤ BLaplace t l l0 := by
  let k1 : ℝ → ℝ := fun u => 1 - Real.exp (-l0 * u)
  let k2 : ℝ → ℝ := fun u => Real.exp (-(2 * l0 * (u - t))) - Real.exp (-l0 * u)
  have hc1 : Continuous k1 := by dsimp [k1]; fun_prop
  have hc2 : Continuous k2 := by dsimp [k2]; fun_prop
  have hk1 : ∀ u ∈ Set.Icc 0 t, 0 ≤ k1 u := by
    intro u hu
    apply sub_nonneg.mpr
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg h0.le hu.1]
  have hk2 : ∀ u ∈ Set.Icc t (2 * t), 0 ≤ k2 u := by
    intro u hu
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg h0.le (sub_nonneg.mpr hu.2)]
  have hm0 := weighted_integral_antitone (fun _ => 1) 0 (2 * t) (l + l0) (L + l0)
    le_rfl (by linarith) (by linarith) continuous_const (fun _ _ => by norm_num)
  simp only [one_mul] at hm0
  have hm1 := weighted_integral_antitone k1 0 t l L le_rfl ht hl hc1 hk1
  have hm2 := weighted_integral_antitone k2 t (2 * t) l L ht (by linarith) hl hc2 hk2
  have hp0 : 0 ≤ ∫ u in 0..(2 * t), Real.exp (-(l + l0) * u) :=
    intervalIntegral.integral_nonneg_of_forall (by linarith) (fun _ => (Real.exp_pos _).le)
  have hp1 : 0 ≤ ∫ u in 0..t, k1 u * Real.exp (-l * u) :=
    intervalIntegral.integral_nonneg ht (fun u hu => mul_nonneg (hk1 u hu) (Real.exp_pos _).le)
  have hp2 : 0 ≤ ∫ u in t..(2 * t), k2 u * Real.exp (-l * u) :=
    intervalIntegral.integral_nonneg (by linarith)
      (fun u hu => mul_nonneg (hk2 u hu) (Real.exp_pos _).le)
  have hm0' := mul_le_mul_of_nonneg_left hm0 (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hm12 := mul_le_mul_of_nonneg_left (add_le_add hm1 hm2)
    (by positivity : (0 : ℝ) ≤ 1 / l0)
  change 0 ≤ 1 / 6 * _ + 1 / l0 * (_ + _) ∧ _
  constructor
  · exact add_nonneg (mul_nonneg (by norm_num) hp0)
      (mul_nonneg (by positivity) (add_nonneg hp1 hp2))
  · unfold BLaplace
    dsimp [k1, k2] at hm12
    linarith

#print axioms BLaplace_order

end LeanLab.Zhao2025.Task56
