/-
P0069 page 21, consequences of the nonresonant discretization supply and the integral estimate.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Decomp343c
import LeanLab.BakerHarmanPintz1997.DecompJ883

namespace LeanLab.BakerHarmanPintz1997.Principal343
open Finset Decomp343c MeasureTheory intervalIntegral

/-- Page 21 local consequence. Separate the principal integral and the uniform discretization error. -/
theorem principal_nonresonant_bound (N N1 t : ℝ) (hN : 1 ≤ N) (hNN1 : N ≤ N1)
    (hN1 : N1 ≤ 2 * N) (ht : |t| ≤ N) :
    ‖∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, critical t n‖ ≤
      67 * N ^ (-1 / 2 : ℝ) + 5 * N ^ (1 / 2 : ℝ) / (1 + |t|) := by
  have hN0 : 0 < N := by linarith
  have hI : ‖∫ y in N..N1, critical t y‖ ≤ 5 * N ^ (1 / 2 : ℝ) / (1 + |t|) := by
    have hh := DecompJ883.fgm_integral_bound N N1 hN hNN1 hN1 t
    have heq : (∫ y in N..N1, critical t y) = ∫ y in N..N1,
        (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le hNN1] at hy
      exact critical_eq_product t (hN0.trans_le hy.1)
    rwa [heq]
  calc
    _ = ‖((∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, critical t n) -
        (∫ y in N..N1, critical t y)) + (∫ y in N..N1, critical t y)‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖(∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, critical t n) -
        (∫ y in N..N1, critical t y)‖ + ‖∫ y in N..N1, critical t y‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (real_discretization N N1 t hN hNN1 hN1 ht) hI

/-- Page 21 local consequence. Frequencies between N over two and N give an inverse square root sum. -/
theorem principal_upper_frequency_bound (N N1 t : ℝ) (hN : 1 ≤ N) (hNN1 : N ≤ N1)
    (hN1 : N1 ≤ 2 * N) (htlow : N / 2 ≤ |t|) (ht : |t| ≤ N) :
    ‖∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, critical t n‖ ≤ 77 * N ^ (-1 / 2 : ℝ) := by
  have hN0 : 0 < N := by linarith
  have hp : 0 ≤ N ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hN0.le _
  have hpow : N ^ (-1 / 2 : ℝ) * N = N ^ (1 / 2 : ℝ) := by
    calc
      _ = N ^ (-1 / 2 : ℝ) * N ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = N ^ ((-1 / 2 : ℝ) + 1) := (Real.rpow_add hN0 _ _).symm
      _ = _ := by norm_num
  have hI : 5 * N ^ (1 / 2 : ℝ) / (1 + |t|) ≤ 10 * N ^ (-1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 1 + |t|)).mpr
    have hh := mul_nonneg hp (show 0 ≤ 2 * |t| - N by linarith)
    nlinarith
  exact (principal_nonresonant_bound N N1 t hN hNN1 hN1 ht).trans (by linarith)

example : ‖∑ n ∈ Ioc ⌊(4 : ℝ)⌋₊ ⌊(8 : ℝ)⌋₊, critical 4 n‖ ≤
    77 * (4 : ℝ) ^ (-1 / 2 : ℝ) :=
  principal_upper_frequency_bound 4 8 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Page 21 diagnostic. Taking absolute values before integration loses a factor of N
at the admissible frequency t equal to N. This is an obstruction to that proof route. -/
theorem absolute_derivative_budget_lower (N : ℝ) (hN : 1 ≤ N) :
    (N / 4) * N ^ (-1 / 2 : ℝ) ≤ ∫ y in N..2 * N, ‖criticalDeriv N y‖ := by
  have hN0 : 0 < N := by linarith
  have hNN : N ≤ 2 * N := by linarith
  have hS : N ≤ ‖(-1 / 2 : ℂ) - (N : ℂ) * Complex.I‖ := by
    have hh := Complex.abs_im_le_norm ((-1 / 2 : ℂ) - (N : ℂ) * Complex.I)
    simpa [abs_of_pos hN0] using hh
  have hpow : N ^ (-3 / 2 : ℝ) * N = N ^ (-1 / 2 : ℝ) := by
    calc
      _ = N ^ (-3 / 2 : ℝ) * N ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = N ^ ((-3 / 2 : ℝ) + 1) := (Real.rpow_add hN0 _ _).symm
      _ = _ := by norm_num
  have htwo : (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (-3 / 2 : ℝ) := by
    calc
      (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hpoint : ∀ y ∈ Set.Icc N (2 * N),
      (1 / 4 : ℝ) * N ^ (-1 / 2 : ℝ) ≤ ‖criticalDeriv N y‖ := by
    intro y hy
    have hy0 : 0 < y := hN0.trans_le hy.1
    have hbase : (2 * N) ^ (-3 / 2 : ℝ) ≤ y ^ (-3 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hy0 hy.2 (by norm_num)
    rw [criticalDeriv_norm N hy0]
    calc
      _ = (1 / 4 : ℝ) * (N ^ (-3 / 2 : ℝ) * N) := by rw [hpow]
      _ ≤ (2 : ℝ) ^ (-3 / 2 : ℝ) * (N ^ (-3 / 2 : ℝ) * N) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = N * (2 * N) ^ (-3 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hN0.le]
        ring
      _ ≤ _ := mul_le_mul hS hbase (by positivity) (norm_nonneg _)
  have hcont : ContinuousOn (fun y : ℝ => ‖criticalDeriv N y‖) (Set.uIcc N (2 * N)) := by
    intro y hy
    rw [Set.uIcc_of_le hNN] at hy
    exact (criticalDeriv_continuousAt N (hN0.trans_le hy.1)).norm.continuousWithinAt
  have hh := intervalIntegral.integral_mono_on hNN
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (1 / 4 : ℝ) * N ^ (-1 / 2 : ℝ)) volume N (2 * N))
    hcont.intervalIntegrable hpoint
  convert hh using 1 <;> simp only [intervalIntegral.integral_const, smul_eq_mul] <;> ring

/-- Page 21 diagnostic. No uniform inverse square root bound controls the absolute
first derivative integral, even within the sealed nonresonant range. -/
theorem absolute_derivative_budget_not_uniform :
    ¬ ∃ C : ℝ, ∀ N : ℝ, 1 ≤ N → ∀ t : ℝ, |t| ≤ N →
      (∫ y in N..2 * N, ‖criticalDeriv t y‖) ≤ C * N ^ (-1 / 2 : ℝ) := by
  rintro ⟨C, hC⟩
  let N : ℝ := max 1 (4 * C + 1)
  have hN : 1 ≤ N := le_max_left _ _
  have hN0 : 0 < N := by linarith
  have hbig : 4 * C < N := by dsimp [N]; linarith [le_max_right 1 (4 * C + 1)]
  have hlower := absolute_derivative_budget_lower N hN
  have hupper := hC N hN N (by rw [abs_of_pos hN0])
  have hp : 0 < N ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hc : N / 4 ≤ C := (mul_le_mul_iff_left₀ hp).mp (hlower.trans hupper)
  linarith

#print axioms absolute_derivative_budget_lower
#print axioms absolute_derivative_budget_not_uniform
#print axioms principal_nonresonant_bound
#print axioms principal_upper_frequency_bound
end LeanLab.BakerHarmanPintz1997.Principal343
