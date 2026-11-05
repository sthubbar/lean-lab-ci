/-
P0093 page 167 equation 10.1. The remaining minor contribution.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357h

namespace LeanLab.Linnik1951

open MeasureTheory

/-- P0093 page 167 equation 10.1. Factor k minus two powers of T from
the arc norm and compare its remaining square integral with the full circle. -/
theorem arc_abs_le_mixed_mass357 (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N)
    (s : Set ℝ) (hs : s ⊆ Set.Icc 0 1) (hms : MeasurableSet s)
    (B : ℝ) (hB : 0 ≤ B) (hT : ∀ α ∈ s, ‖powerFourier111 N α‖ ≤ B) :
    |arcContribution280 k N s| ≤ Real.exp 1 * B ^ (k - 2) *
      (∫ α in Set.Icc (0 : ℝ) 1, ‖primeFourier111 N α * powerFourier111 N α‖ ^ 2) := by
  have hS := continuous_prime_fourier111 N hN
  have hP := continuous_power_fourier111 N hN
  have hF : Continuous (fun α : ℝ => primeFourier111 N α ^ 2 *
      powerFourier111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) := by fun_prop
  have hInt : IntegrableOn (fun α : ℝ => primeFourier111 N α ^ 2 *
      powerFourier111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) s :=
    hF.integrableOn_Icc.mono_set hs
  have hMix : IntegrableOn (fun α : ℝ => ‖primeFourier111 N α * powerFourier111 N α‖ ^ 2)
      (Set.Icc (0 : ℝ) 1) := ((hS.mul hP).norm.pow 2).integrableOn_Icc
  unfold arcContribution280
  rw [abs_mul, abs_of_pos (Real.exp_pos 1)]
  calc
    _ ≤ Real.exp 1 * ‖∫ α in s, primeFourier111 N α ^ 2 *
        powerFourier111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (Real.exp_pos 1).le
    _ ≤ Real.exp 1 * (∫ α in s, ‖primeFourier111 N α ^ 2 *
        powerFourier111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Real.exp_pos 1).le
    _ ≤ Real.exp 1 * (∫ α in s, B ^ (k - 2) *
        ‖primeFourier111 N α * powerFourier111 N α‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
      apply setIntegral_mono_on hInt.norm ((hMix.mono_set hs).const_mul _) hms
      intro α hα
      simp only [norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, mul_one]
      have hp : ‖powerFourier111 N α‖ ^ k =
          ‖powerFourier111 N α‖ ^ 2 * ‖powerFourier111 N α‖ ^ (k - 2) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hp, mul_pow]
      calc
        _ ≤ ‖primeFourier111 N α‖ ^ 2 *
            (‖powerFourier111 N α‖ ^ 2 * B ^ (k - 2)) := by gcongr; exact hT α hα
        _ = _ := by ring
    _ = Real.exp 1 * B ^ (k - 2) * (∫ α in s,
        ‖primeFourier111 N α * powerFourier111 N α‖ ^ 2) := by rw [integral_const_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_mono_set hMix (ae_of_all _ (fun α => sq_nonneg _)) (ae_of_all _ hs)) (by positivity)

/-- P0093 page 167 equation 10.1. A fixed power of a bounded additive
logarithmic error costs at most two once the logarithm is sufficiently large. -/
theorem additive_power_le_twice357 (r : ℕ) (t : ℝ) (ht : 0 < t)
    (hlarge : 2 * (r : ℝ) ≤ t * Real.log 2) : (t + 2) ^ r ≤ 2 * t ^ r := by
  have hbase : 1 + 2 / t ≤ Real.exp (2 / t) := by
    simpa only [add_comm] using Real.add_one_le_exp (2 / t)
  have he : (1 + 2 / t) ^ r ≤ Real.exp ((r : ℝ) * (2 / t)) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + 2 / t) hbase r
  have hcut : (r : ℝ) * (2 / t) ≤ Real.log 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ ht).mpr
    nlinarith
  have htwo : (1 + 2 / t) ^ r ≤ 2 := by
    have h := he.trans (Real.exp_le_exp.mpr hcut)
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  have hid : (t + 2) ^ r = t ^ r * (1 + 2 / t) ^ r := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [hid, mul_comm 2]
  exact mul_le_mul_of_nonneg_left htwo (by positivity)

/-- P0093 page 167 equation 10.1. Exact minor_error280 statement.
The pointwise complementary bound, clean Lemma 3 and dyadic growth suffice. -/
theorem minor_error_proved357 (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hT : ∀ N : ℕ, ∀ α : ℝ, α ∈ goodMinorArcs280 N η →
      ‖powerFourier111 N α‖ ≤ (1 - η) * ‖powerFourier111 N 0‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 3 ≤ k → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 < N →
        |arcContribution280 k N (goodMinorArcs280 N η)| ≤
          C * scale111 k N * (1 - η) ^ (k - 2) := by
  obtain ⟨C0, hC0, hL3⟩ := lemma_three_proved357
  refine ⟨2 * Real.exp 1 * C0, by positivity, ?_⟩
  intro k hk
  let r := k - 2
  obtain ⟨M, hM⟩ := exists_nat_gt (Real.exp (2 * (r : ℝ) + Real.log 2))
  refine ⟨max 2 M, ?_⟩
  intro N hev hN
  have h2 : 2 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hMN : M < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hnR : (M : ℝ) < (N : ℝ) := by exact_mod_cast hMN
  have hlog : 2 * (r : ℝ) + Real.log 2 ≤ Real.log N := by
    have h := Real.log_le_log (Real.exp_pos _) (hM.trans hnR).le
    simpa only [Real.log_exp] using h
  let t := Real.log N / Real.log 2
  have ht : 0 < t := div_pos (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
    (Real.log_pos (by norm_num))
  have hlarge : 2 * (r : ℝ) ≤ t * Real.log 2 := by
    dsimp [t]
    rw [div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hp := additive_power_le_twice357 r t ht hlarge
  have hms : MeasurableSet (goodMinorArcs280 N η) :=
    measurableSet_Icc.diff ((measurable_major357 N).union (measurable_exceptional357 N (by omega) η))
  have hb := arc_abs_le_mixed_mass357 k N (by omega) (by omega)
    (goodMinorArcs280 N η) Set.diff_subset hms
    ((1 - η) * (t + 2)) (by positivity) (fun α hα =>
      (hT N α hα).trans (mul_le_mul_of_nonneg_left (power_abs_le_log357 N (by omega) 0) (by linarith)))
  have hm : (∫ α in Set.Icc (0 : ℝ) 1, ‖primeFourier111 N α * powerFourier111 N α‖ ^ 2) ≤ C0 * N := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hL3 N (by omega)).le
  calc
    _ ≤ Real.exp 1 * ((1 - η) * (t + 2)) ^ r * (C0 * N) :=
      hb.trans (mul_le_mul_of_nonneg_left hm (by positivity))
    _ ≤ Real.exp 1 * ((1 - η) ^ r * (2 * t ^ r)) * (C0 * N) := by
      rw [mul_pow]
      gcongr
    _ = _ := by unfold scale111; dsimp [t, r]; ring

end LeanLab.Linnik1951
