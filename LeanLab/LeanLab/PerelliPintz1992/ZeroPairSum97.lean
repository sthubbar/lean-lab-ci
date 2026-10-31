/-
P0070, p. 366, the finite zero pair sum behind equation 32.
Coefficients can include zero multiplicities and increment factors.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.ZeroIncrement97

namespace LeanLab.PerelliPintz1992.Section6
open Real Set MeasureTheory

/-- LEAF. Equation 32, p. 366: sum the normalized kernel over finite zero parameters,
retaining arbitrary complex coefficients and all diagonal pairs. -/
theorem finite_zero_pair_sum_bound (Z : Finset ℂ) (a : ℂ → ℂ) {N : ℝ} (hN : 0 < N)
    (hZ : ∀ ρ ∈ Z, 0 ≤ ρ.re ∧ ρ.re ≤ 1) :
    ‖(1 / (N : ℂ)) * ∑ ρ ∈ Z, ∑ ρ' ∈ Z,
      (a ρ * star (a ρ')) * ∫ x : ℝ in N / 2..3 * N, (x : ℂ) ^ (ρ + star ρ' - 2)‖ ≤
      10 * ∑ ρ ∈ Z, ∑ ρ' ∈ Z,
        ‖a ρ‖ * ‖a ρ'‖ * N ^ (ρ.re + ρ'.re - 2) / max 1 |ρ.im - ρ'.im| := by
  have hp : ∀ ρ ∈ Z, ∀ ρ' ∈ Z,
      ‖(1 / (N : ℂ)) * ((a ρ * star (a ρ')) *
        ∫ x : ℝ in N / 2..3 * N, (x : ℂ) ^ (ρ + star ρ' - 2))‖ ≤
      10 * (‖a ρ‖ * ‖a ρ'‖ * N ^ (ρ.re + ρ'.re - 2) / max 1 |ρ.im - ρ'.im|) := by
    intro ρ hρ ρ' hρ'
    have hh := zero_pair_kernel hN (hZ ρ hρ).1 (hZ ρ hρ).2 (hZ ρ' hρ').1 (hZ ρ' hρ').2
    have he : (1 / (N : ℂ)) * ((a ρ * star (a ρ')) *
        ∫ x : ℝ in N / 2..3 * N, (x : ℂ) ^ (ρ + star ρ' - 2)) =
        (a ρ * star (a ρ')) * ((1 / (N : ℂ)) *
          ∫ x : ℝ in N / 2..3 * N, (x : ℂ) ^ (ρ + star ρ' - 2)) := by ring
    rw [he, norm_mul, norm_mul, norm_star]
    exact (mul_le_mul_of_nonneg_left hh (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq
      (by ring)
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  calc
    _ ≤ ∑ ρ ∈ Z, ‖∑ ρ' ∈ Z, (1 / (N : ℂ)) * ((a ρ * star (a ρ')) *
        ∫ x : ℝ in N / 2..3 * N, (x : ℂ) ^ (ρ + star ρ' - 2))‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ Z, ∑ ρ' ∈ Z,
        10 * (‖a ρ‖ * ‖a ρ'‖ * N ^ (ρ.re + ρ'.re - 2) / max 1 |ρ.im - ρ'.im|) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun ρ' hρ' => hp ρ hρ ρ' hρ'))
    _ = _ := rfl


/-- LEAF. Equation 32, p. 366: the mean square of a finite weighted zero power sum
is bounded by the actual double sum with the imaginary gap kernel, including its diagonal. -/
theorem finite_zero_mean_square_bound (Z : Finset ℂ) (a : ℂ → ℂ) {N : ℝ} (hN : 0 < N)
    (hZ : ∀ ρ ∈ Z, 0 ≤ ρ.re ∧ ρ.re ≤ 1) :
    (1 / N) * (∫ x : ℝ in N / 2..3 * N, ‖∑ ρ ∈ Z, a ρ * (x : ℂ) ^ (ρ - 1)‖ ^ 2) ≤
      10 * ∑ ρ ∈ Z, ∑ ρ' ∈ Z,
        ‖a ρ‖ * ‖a ρ'‖ * N ^ (ρ.re + ρ'.re - 2) / max 1 |ρ.im - ρ'.im| := by
  have hab : N / 2 ≤ 3 * N := by linarith
  have hexpand : ∀ x : ℝ, 0 < x →
      ((‖∑ ρ ∈ Z, a ρ * (x : ℂ) ^ (ρ - 1)‖ ^ 2 : ℝ) : ℂ) =
      ∑ ρ ∈ Z, ∑ ρ' ∈ Z,
        (a ρ * star (a ρ')) * (x : ℂ) ^ (ρ + star ρ' - 2) := by
    intro x hx
    have hconj : ∀ ρ : ℂ, star ((x : ℂ) ^ (ρ - 1)) = (x : ℂ) ^ (star ρ - 1) := by
      intro ρ
      have harg : (x : ℂ).arg ≠ Real.pi := by
        rw [Complex.arg_ofReal_of_nonneg hx.le]
        exact Real.pi_ne_zero.symm
      have hh := Complex.cpow_conj (x : ℂ) (ρ - 1) harg
      simpa only [Complex.star_def, Complex.conj_ofReal, map_sub, map_one] using hh.symm
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro ρ hρ
    apply Finset.sum_congr rfl
    intro ρ' hρ'
    rw [map_mul]
    change (a ρ * (x : ℂ) ^ (ρ - 1)) * (star (a ρ') * star ((x : ℂ) ^ (ρ' - 1))) = _
    rw [hconj]
    rw [show ρ + star ρ' - 2 = (ρ - 1) + (star ρ' - 1) by ring,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
    ring
  have hint : ∀ ρ ρ' : ℂ, IntervalIntegrable (fun x : ℝ =>
      (a ρ * star (a ρ')) * (x : ℂ) ^ (ρ + star ρ' - 2)) volume (N / 2) (3 * N) := by
    intro ρ ρ'
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    apply ContinuousOn.const_mul
    intro x hx
    exact (Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (by linarith [hx.1]))).continuousWithinAt
  have hid : (∫ x : ℝ in N / 2..3 * N,
      ((‖∑ ρ ∈ Z, a ρ * (x : ℂ) ^ (ρ - 1)‖ ^ 2 : ℝ) : ℂ)) =
      ∑ ρ ∈ Z, ∑ ρ' ∈ Z,
        (a ρ * star (a ρ')) * ∫ x : ℝ in N / 2..3 * N, (x : ℂ) ^ (ρ + star ρ' - 2) := by
    calc
      _ = ∫ x : ℝ in N / 2..3 * N, ∑ ρ ∈ Z, ∑ ρ' ∈ Z,
          (a ρ * star (a ρ')) * (x : ℂ) ^ (ρ + star ρ' - 2) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hab] at hx
        exact hexpand x (by linarith [hx.1])
      _ = _ := by
        rw [intervalIntegral.integral_finsetSum
          (f := fun ρ x => ∑ ρ' ∈ Z, (a ρ * star (a ρ')) * (x : ℂ) ^ (ρ + star ρ' - 2))
          (fun ρ hρ => by
            convert IntervalIntegrable.sum Z (fun ρ' hρ' => hint ρ ρ') using 1
            ext x
            rw [Finset.sum_apply])]
        apply Finset.sum_congr rfl
        intro ρ hρ
        rw [intervalIntegral.integral_finsetSum (fun ρ' hρ' => hint ρ ρ')]
        apply Finset.sum_congr rfl
        intro ρ' hρ'
        rw [intervalIntegral.integral_const_mul]
  have hnonneg : 0 ≤ ∫ x : ℝ in N / 2..3 * N,
      ‖∑ ρ ∈ Z, a ρ * (x : ℂ) ^ (ρ - 1)‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hab (fun x => sq_nonneg _)
  have hh := finite_zero_pair_sum_bound Z a hN hZ
  rw [← hid, intervalIntegral.integral_ofReal] at hh
  simpa only [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hN, abs_of_nonneg hnonneg] using hh

end LeanLab.PerelliPintz1992.Section6
