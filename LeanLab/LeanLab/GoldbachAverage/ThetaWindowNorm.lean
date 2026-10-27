import LeanLab.GoldbachAverage.ThetaGallagher

/-!
An elementary instance of the weighted window input at exponent theta equals two.
This bound is too weak for Corollary 2. It verifies that the window input has instances.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.ThetaLayers
open Complex Finset
open LeanLab.PNTPort.Gallagher LeanLab.PNTPort.Selberg

/-- The square window norm is bounded by L times the square of the coefficient mass. -/
theorem sum_win_sq_le_mass (a : ℕ → ℂ) (M L : ℕ) :
    ∑ m ∈ range (M + L), ‖win a M L m‖ ^ 2 ≤
      L * (∑ n ∈ range M, ‖a n‖) ^ 2 := by
  set S := ∑ n ∈ range M, ‖a n‖ with hS
  set mass := fun m => ∑ n ∈ (range M).filter (fun n => n ≤ m ∧ m < n + L), ‖a n‖ with hmass
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => norm_nonneg _
  have hm0 : ∀ m, 0 ≤ mass m := fun _ => sum_nonneg fun _ _ => norm_nonneg _
  have hmS : ∀ m, mass m ≤ S := fun m =>
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => norm_nonneg _)
  have hn : ∀ m, ‖win a M L m‖ ≤ mass m := fun _ => norm_sum_le _ _
  have hsq : ∀ m, ‖win a M L m‖ ^ 2 ≤ S * mass m := by
    intro m
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hn m) 2
    have h2 := mul_le_mul_of_nonneg_right (hmS m) (hm0 m)
    nlinarith only [h1, h2]
  have htotal : ∑ m ∈ range (M + L), mass m = L * S := by
    simp only [hmass, sum_filter]
    rw [sum_comm]
    calc ∑ n ∈ range M, ∑ m ∈ range (M + L), (if n ≤ m ∧ m < n + L then ‖a n‖ else 0)
        = ∑ n ∈ range M, (L : ℝ) * ‖a n‖ := by
          apply sum_congr rfl
          intro n hn
          have hnM := mem_range.mp hn
          have he : (range (M + L)).filter (fun m => n ≤ m ∧ m < n + L) = Ico n (n + L) := by
            ext m
            simp only [mem_filter, mem_range, mem_Ico]
            omega
          rw [← sum_filter, he, sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul]
      _ = _ := by rw [← mul_sum]
  calc _ ≤ ∑ m ∈ range (M + L), S * mass m := sum_le_sum fun m _ => hsq m
    _ = S * (L * S) := by rw [← mul_sum, htotal]
    _ = _ := by ring

/-- A finite coefficient mass estimate with an explicit constant. -/
theorem weightedCoeff_mass_le (N M : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ range M, ‖weightedCoeff N n‖ ≤ 4 * (N : ℝ) ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set q := Real.exp (-(1 / (N : ℝ))) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    have := one_div_pos.mpr hN0
    linarith
  have h1q : 0 < 1 - q := by linarith
  have hn : ∀ n, ‖weightedCoeff N n‖ ≤ q ^ n * ((n : ℝ) + 1) := by
    intro n
    have he : Real.exp (-(n / N)) = q ^ n := by
      rw [hq, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [weightedCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), he]
    exact mul_le_mul_of_nonneg_left (norm_lam1_le_succ n) (by positivity)
  have hm := geom_moment 1 M hq0.le hq1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at hm
  have hterm : 0 ≤ q ^ M * (M : ℝ) := by positivity
  have hs : (1 - q) * (∑ n ∈ range M, q ^ n * ((n : ℝ) + 1)) ≤ 1 / (1 - q) := by
    rw [mul_sum]
    simpa only [mul_assoc] using (le_trans (le_add_of_nonneg_right hterm) hm)
  have hsum : (∑ n ∈ range M, q ^ n * ((n : ℝ) + 1)) ≤ (1 / (1 - q)) ^ 2 := by
    apply (mul_le_mul_iff_right₀ h1q).mp
    nlinarith [show (1 / (1 - q)) ^ 2 * (1 - q) = 1 / (1 - q) by field_simp]
  have hi : 1 / (1 - q) ≤ 2 * N := one_sub_exp_neg_inv hN1
  calc _ ≤ ∑ n ∈ range M, q ^ n * ((n : ℝ) + 1) := sum_le_sum fun n _ => hn n
    _ ≤ (1 / (1 - q)) ^ 2 := hsum
    _ ≤ (2 * (N : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hi 2
    _ = _ := by ring

/-- A concrete unconditional variance instance at theta equals two. -/
theorem theta_weighted_variance_two : ThetaWeightedVariance 2 := by
  refine ⟨16, by norm_num, fun N L M hN hL hLN => ?_⟩
  have hmass := weightedCoeff_mass_le N M (by omega)
  have hmass0 : 0 ≤ ∑ n ∈ range M, ‖weightedCoeff N n‖ := sum_nonneg fun _ _ => norm_nonneg _
  have hsq := pow_le_pow_left₀ hmass0 hmass 2
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hf : 1 ≤ (1 + Real.log N) ^ 4 := one_le_pow₀ (by linarith)
  have hb := sum_win_sq_le_mass (weightedCoeff N) M L
  have h1 := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) L)
  have h2 := mul_le_mul_of_nonneg_left hf (show 0 ≤ 16 * (L : ℝ) * (N : ℝ) ^ 4 by positivity)
  have hb0 : (∑ m ∈ range (M + L), ‖win (weightedCoeff N) M L m‖ ^ 2) ≤
      16 * (L : ℝ) * (N : ℝ) ^ 4 * (1 + Real.log N) ^ 4 := by
    calc _ ≤ (L : ℝ) * (∑ n ∈ range M, ‖weightedCoeff N n‖) ^ 2 := hb
      _ ≤ (L : ℝ) * (4 * (N : ℝ) ^ 2) ^ 2 := h1
      _ = 16 * (L : ℝ) * (N : ℝ) ^ 4 := by ring
      _ ≤ 16 * (L : ℝ) * (N : ℝ) ^ 4 * (1 + Real.log N) ^ 4 := by simpa using h2
  convert hb0 using 1 <;> norm_num

/-- A concrete unconditional instance of the local mean square input. -/
theorem theta_lemma1_two : ThetaLemma1 2 :=
  theta_lemma1_of_weighted_variance 2 (by norm_num) theta_weighted_variance_two

end LeanLab.GoldbachAverage.ThetaLayers
