import LeanLab.Romanov.HalfOrder
import LeanLab.HeathBrownPuchta.C2Inputs

/-!
# The mean of h on Mersenne numbers

AI wrote the Lean code. Known mathematics. HBP arXiv math/0201299v2, page 21,
displays 34 and 35. The square root order series controls the floor errors.
Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.Romanov

open Finset Real
open LeanLab.HeathBrownPuchta.Lemma8Const

/-- The elementary floor estimate used immediately before HBP display 34. -/
theorem floor_error_le_sqrt {t : ℝ} (ht : 0 ≤ t) :
    |(⌊t⌋₊ : ℝ) - t| ≤ sqrt t := by
  have hlo : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
  have hhi : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hf0 : (0 : ℝ) ≤ ⌊t⌋₊ := by positivity
  rw [abs_of_nonpos (by linarith)]
  by_cases h : t ≤ 1
  · have hroot : t ≤ sqrt t := Real.le_sqrt_of_sq_le (by nlinarith)
    linarith
  · have hroot : 1 ≤ sqrt t := Real.one_le_sqrt.mpr (by linarith)
    linarith

/-- The defining series for C2 is convergent, independently of its explicit bound. -/
theorem hbp_C2_summable : Summable (fun d : ℕ => (k d : ℝ) / eps d) := by
  apply Summable.of_nonneg_of_le (fun d => div_nonneg (by exact_mod_cast k_nonneg d) (by positivity))
    (fun d => ?_) hbp_36_summable
  by_cases he : eps d = 0
  · simp [he]
  have he1 : (1 : ℝ) ≤ eps d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr he
  have hs : 0 < sqrt (eps d) := sqrt_pos.mpr (by linarith)
  apply div_le_div_of_nonneg_left (by exact_mod_cast k_nonneg d) hs
  exact sqrt_le_self_iff.mpr (Or.inr he1)

/-- The divisor sum of h as a finitely supported order indicator series. -/
theorem hbp_divisor_series (j : ℕ) (hj : 1 ≤ j) :
    Summable (fun d : ℕ => if eps d ∣ j then (k d : ℝ) else 0) ∧
      ∑' d : ℕ, (if eps d ∣ j then (k d : ℝ) else 0) = (h (2 ^ j - 1) : ℝ) := by
  have hn : 2 ^ j - 1 ≠ 0 := two_pow_sub_one_ne_zero hj
  have hz : ∀ d ∉ (2 ^ j - 1).divisors,
      (if eps d ∣ j then (k d : ℝ) else 0) = 0 := by
    intro d hd
    split_ifs with he
    · exact False.elim (hd (Nat.mem_divisors.mpr
        ⟨(LeanLab.HeathBrownPuchta.C2Inputs.dvd_iff_eps_dvd d j).mpr he, hn⟩))
    · rfl
  refine ⟨summable_of_ne_finset_zero hz, ?_⟩
  rw [tsum_eq_sum hz]
  have hh : (h (2 ^ j - 1) : ℝ) = ∑ d ∈ (2 ^ j - 1).divisors, (k d : ℝ) := by
    exact_mod_cast LeanLab.HeathBrownPuchta.C2Inputs.h_eq_sum_k (2 ^ j - 1) hn
  rw [hh]
  apply sum_congr rfl
  intro d hd
  exact ite_eq_left ((LeanLab.HeathBrownPuchta.C2Inputs.dvd_iff_eps_dvd d j).mp
    (Nat.mem_divisors.mp hd).1)

/-- The exact floor sum identity before HBP display 34. -/
theorem hbp_h_mean_eq (J : ℕ) :
    ∑ j ∈ Icc 1 J, (h (2 ^ j - 1) : ℝ) =
      ∑' d : ℕ, (k d : ℝ) * (J / eps d : ℕ) := by
  have hseries : ∀ j ∈ Icc 1 J,
      Summable (fun d : ℕ => if eps d ∣ j then (k d : ℝ) else 0) := by
    intro j hj
    exact (hbp_divisor_series j (mem_Icc.mp hj).1).1
  calc ∑ j ∈ Icc 1 J, (h (2 ^ j - 1) : ℝ)
      = ∑ j ∈ Icc 1 J, ∑' d : ℕ, (if eps d ∣ j then (k d : ℝ) else 0) := by
        apply sum_congr rfl
        intro j hj
        exact (hbp_divisor_series j (mem_Icc.mp hj).1).2.symm
    _ = ∑' d : ℕ, ∑ j ∈ Icc 1 J, (if eps d ∣ j then (k d : ℝ) else 0) :=
        (Summable.tsum_finsetSum hseries).symm
    _ = ∑' d : ℕ, (k d : ℝ) * (J / eps d : ℕ) := by
        apply tsum_congr
        intro d
        rw [← sum_filter, sum_const, nsmul_eq_mul]
        have hi : Icc 1 J = Ioc 0 J := by
          ext n
          simp only [mem_Icc, mem_Ioc]
          omega
        rw [hi, Nat.Ioc_filter_dvd_card_eq_div]
        ring

/-- The floor series is summable by comparison with the defining C2 series. -/
theorem hbp_floor_summable (J : ℕ) :
    Summable (fun d : ℕ => (k d : ℝ) * (J / eps d : ℕ)) := by
  apply Summable.of_nonneg_of_le (fun d => mul_nonneg (by exact_mod_cast k_nonneg d) (by positivity))
    (fun d => ?_) (hbp_C2_summable.mul_right (J : ℝ))
  calc (k d : ℝ) * (J / eps d : ℕ) ≤ (k d : ℝ) * ((J : ℝ) / eps d) :=
        mul_le_mul_of_nonneg_left Nat.cast_div_le (by exact_mod_cast k_nonneg d)
    _ = ((k d : ℝ) / eps d) * J := by ring

/-- Each weighted floor error is bounded by the square root order summand. -/
theorem hbp_floor_term_error (J d : ℕ) :
    |(k d : ℝ) * (J / eps d : ℕ) - ((k d : ℝ) / eps d) * J| ≤
      sqrt (J : ℝ) * ((k d : ℝ) / sqrt (eps d)) := by
  have hk : (0 : ℝ) ≤ k d := by exact_mod_cast k_nonneg d
  have hf := floor_error_le_sqrt (t := (J : ℝ) / eps d) (by positivity)
  rw [Nat.floor_div_eq_div] at hf
  calc |(k d : ℝ) * (J / eps d : ℕ) - ((k d : ℝ) / eps d) * J|
      = (k d : ℝ) * |(J / eps d : ℕ) - (J : ℝ) / eps d| := by
        rw [show (k d : ℝ) * (J / eps d : ℕ) - ((k d : ℝ) / eps d) * J =
          (k d : ℝ) * ((J / eps d : ℕ) - (J : ℝ) / eps d) by ring,
          abs_mul, abs_of_nonneg hk]
    _ ≤ (k d : ℝ) * sqrt ((J : ℝ) / eps d) := mul_le_mul_of_nonneg_left hf hk
    _ = sqrt (J : ℝ) * ((k d : ℝ) / sqrt (eps d)) := by
        rw [Real.sqrt_div (by positivity)]
        ring

/-- HBP display 34, with an explicit absolute error constant. -/
theorem hbp_h_mean_error (J : ℕ) :
    |(∑ j ∈ Icc 1 J, (h (2 ^ j - 1) : ℝ)) - C2 * J| ≤
      (16 * log 2 * exp 27) * sqrt (J : ℝ) := by
  have hs := hbp_floor_summable J
  have hm := hbp_C2_summable.mul_right (J : ℝ)
  have hg := hbp_36_summable.mul_left (sqrt (J : ℝ))
  rw [hbp_h_mean_eq, C2, ← tsum_mul_right, ← hs.tsum_sub hm]
  have hb : ‖∑' d : ℕ, ((k d : ℝ) * (J / eps d : ℕ) - ((k d : ℝ) / eps d) * J)‖ ≤
      ∑' d : ℕ, sqrt (J : ℝ) * ((k d : ℝ) / sqrt (eps d)) :=
    tsum_of_norm_bounded hg.hasSum (fun d => by
      simpa only [Real.norm_eq_abs] using hbp_floor_term_error J d)
  calc |∑' d : ℕ, ((k d : ℝ) * (J / eps d : ℕ) - ((k d : ℝ) / eps d) * J)|
      ≤ ∑' d : ℕ, sqrt (J : ℝ) * ((k d : ℝ) / sqrt (eps d)) := by
        simpa only [Real.norm_eq_abs] using hb
    _ = sqrt (J : ℝ) * ∑' d : ℕ, (k d : ℝ) / sqrt (eps d) := by rw [tsum_mul_left]
    _ ≤ sqrt (J : ℝ) * (16 * log 2 * exp 27) :=
        mul_le_mul_of_nonneg_left hbp_36_tsum_le (sqrt_nonneg _)
    _ = (16 * log 2 * exp 27) * sqrt (J : ℝ) := by ring

end LeanLab.Romanov
