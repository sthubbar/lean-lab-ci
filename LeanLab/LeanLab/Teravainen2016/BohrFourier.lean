/-
P0076, Proposition 2.1, page 8. The smooth Bohr cutoff Fourier estimate.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.CyclicConvolution

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

theorem eC_norm (x : ℝ) : ‖eC x‖ = 1 := by
  simp [eC, Complex.norm_exp]

theorem eC_sub_int (x : ℝ) (m : ℤ) : eC (x - m) = eC x := by
  unfold eC
  have h := Complex.exp_int_mul_two_pi_mul_I (-m)
  have he : 2 * (Real.pi : ℂ) * Complex.I * ((x - m : ℝ) : ℂ) =
      2 * Real.pi * Complex.I * (x : ℂ) + ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_add, h, mul_one]

/-- The distance to an integer controls the character error. -/
theorem eC_neg_error (x : ℝ) : ‖1 - eC (-x)‖ ≤ 2 * Real.pi * distInt x := by
  rw [← eC_sub_int (-x) (-round x), norm_sub_rev]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(2 * Real.pi * (x - round x)))
  have he : eC (-x - (-round x : ℤ)) =
      Complex.exp (Complex.I * ((-(2 * Real.pi * (x - round x)) : ℝ) : ℂ)) := by
    unfold eC
    congr 1
    push_cast
    ring
  rw [he]
  convert h using 1
  simp [distInt, abs_mul, mul_assoc]

/-- The Fourier coefficient of a nonnegative function is bounded by its mean. -/
theorem fhat_norm_le_mean (N : ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (ξ : ℕ) :
    ‖fhat N f ξ‖ ≤ (N : ℝ)⁻¹ * ∑ n ∈ range N, f n := by
  unfold fhat
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ n ∈ range N, ‖(f n : ℂ) * eC (-((ξ : ℝ) * n / N))‖ := norm_sum_le _ _
    _ = _ := by
      apply sum_congr rfl
      intro n _
      rw [norm_mul, eC_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf n)]

/-- The lower mass bound in display 2.1 is strictly positive. -/
theorem chiNorm_pos {N : ℕ} {Ω : Finset ℕ} {η : ℝ} {χ : ℤ → ℝ}
    (hη : 0 < η) (hχ : ChiProps N Ω η χ) : 0 < chiNorm N χ :=
  lt_of_lt_of_le (by positivity) hχ.2.2.2.2.2

/-- The normalized cutoff has Fourier coefficients of norm at most one. -/
theorem chi_fourier_norm_le {N : ℕ} {Ω : Finset ℕ} {η : ℝ} {χ : ℤ → ℝ}
    (hη : 0 < η) (hχ : ChiProps N Ω η χ) (ξ : ℕ) :
    ‖fhat N (fun n => χ n) ξ / (chiNorm N χ : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (chiNorm_pos hη hχ),
    div_le_one (chiNorm_pos hη hχ)]
  exact fhat_norm_le_mean N _ (fun n => hχ.1 n) ξ

/-- The small tail of the cutoff is at most eta over four times its mass. -/
theorem chi_tail_ratio {k : ℕ} (hk : k ≠ 0) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    (η ^ 2 / 8) ^ k ≤ (η / 2) ^ k * (η / 4) := by
  have he : (η ^ 2 / 8) ^ k = (η / 2) ^ k * (η / 4) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_of_le_one (by positivity) (by linarith) hk

/-- The cutoff estimate quoted on page 8, with its printed constant 30. -/
theorem chi_fourier_defect {N : ℕ} (hN : 0 < N) {Ω : Finset ℕ} {η : ℝ} {χ : ℤ → ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hχ : ChiProps N Ω η χ) {ξ : ℕ} (hξ : ξ ∈ Ω) :
    ‖1 - fhat N (fun n => χ n) ξ / (chiNorm N χ : ℂ)‖ ≤ 30 * η := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := chiNorm_pos hη hχ
  have hmc : (chiNorm N χ : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hk : Ω.card ≠ 0 := (card_pos.mpr ⟨ξ, hξ⟩).ne'
  set a := (η ^ 2 / 8) ^ Ω.card
  have ha0 : 0 ≤ a := by positivity
  have ha : a ≤ chiNorm N χ * (η / 4) :=
    (chi_tail_ratio hk hη hη1).trans
      (mul_le_mul_of_nonneg_right hχ.2.2.2.2.2 (by positivity))
  have he : (chiNorm N χ : ℂ) - fhat N (fun n => χ n) ξ =
      (N : ℂ)⁻¹ * ∑ n ∈ range N, (χ n : ℂ) * (1 - eC (-((ξ : ℝ) * n / N))) := by
    unfold chiNorm fhat
    push_cast
    rw [← mul_sub, ← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro n _
    ring
  have hp : ∀ n ∈ range N, χ n * ‖1 - eC (-((ξ : ℝ) * n / N))‖ ≤
      4 * Real.pi * η * χ n + 2 * a := by
    intro n hn
    have hc := hχ.1 (n : ℤ)
    by_cases hB : n ∈ Bohr N Ω (2 * η)
    · have hd := (eC_neg_error ((ξ : ℝ) * n / N)).trans
        (mul_le_mul_of_nonneg_left (hB ξ hξ) (by positivity))
      have : χ n * ‖1 - eC (-((ξ : ℝ) * n / N))‖ ≤ χ n * (2 * Real.pi * (2 * η)) :=
        mul_le_mul_of_nonneg_left hd hc
      nlinarith
    · have ht : χ n ≤ a := hχ.2.2.2.2.1 n (mem_range.mp hn) hB
      have hd : ‖1 - eC (-((ξ : ℝ) * n / N))‖ ≤ 2 := by
        calc _ ≤ ‖(1 : ℂ)‖ + ‖eC (-((ξ : ℝ) * n / N))‖ := norm_sub_le _ _
             _ = 2 := by rw [norm_one, eC_norm]; norm_num
      have : 0 ≤ 4 * Real.pi * η * χ n := by positivity
      nlinarith
  have hbound : ‖(chiNorm N χ : ℂ) - fhat N (fun n => χ n) ξ‖ ≤
      4 * Real.pi * η * chiNorm N χ + 2 * a := by
    rw [he, norm_mul, norm_inv, Complex.norm_natCast]
    calc
      _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ range N, ‖(χ n : ℂ) * (1 - eC (-((ξ : ℝ) * n / N)))‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ = (N : ℝ)⁻¹ * ∑ n ∈ range N, χ n * ‖1 - eC (-((ξ : ℝ) * n / N))‖ := by
        congr 1
        apply sum_congr rfl
        intro n _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ.1 n)]
      _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ range N, (4 * Real.pi * η * χ n + 2 * a) :=
        mul_le_mul_of_nonneg_left (sum_le_sum hp) (by positivity)
      _ = _ := by
        rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
        unfold chiNorm
        field_simp
  have h30 : ‖(chiNorm N χ : ℂ) - fhat N (fun n => χ n) ξ‖ ≤
      30 * η * chiNorm N χ := by
    have hpilt := Real.pi_lt_four
    have hηm : 0 ≤ η * chiNorm N χ := by positivity
    nlinarith
  rw [show (1 : ℂ) - fhat N (fun n => χ n) ξ / (chiNorm N χ : ℂ) =
      ((chiNorm N χ : ℂ) - fhat N (fun n => χ n) ξ) / (chiNorm N χ : ℂ) by
        field_simp [hmc], norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
    div_le_iff₀ hm]
  exact h30

example : ‖1 - fhat 1 (fun _ => 1) 0 / (chiNorm 1 (fun _ => 1) : ℂ)‖ ≤
    30 * (1 / 100 : ℝ) := by
  apply chi_fourier_defect (Ω := {0}) (χ := fun _ => 1) (by decide) (by norm_num)
    (by norm_num) (chiProps_satisfiable (by norm_num) (by norm_num))
  simp

#print axioms eC_norm
#print axioms eC_sub_int
#print axioms eC_neg_error
#print axioms fhat_norm_le_mean
#print axioms chiNorm_pos
#print axioms chi_fourier_norm_le
#print axioms chi_tail_ratio
#print axioms chi_fourier_defect

end LeanLab.Teravainen2016
