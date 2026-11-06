/-
P0093 page 162 equation 7.7. Separate dyadic truncation from binary entropy.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Shift412

namespace LeanLab.Linnik1951

open Finset

/-- P0093 page 162 equation 7.7. The finite damped polynomial contains
exactly the positive powers of two at most N. -/
noncomputable def powerTrunc412 (N : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ range (Nat.log 2 N),
    (Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)

/-- P0093 page 162 passage from equation 7.5 to 7.7 and page 161
7.2. The discarded dyadic tail has uniformly bounded norm. Ten is a
conservative constant from the proved first moment bound. -/
theorem power_trunc_error412 (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    ‖powerFourier111 N α - powerTrunc412 N α‖ ≤ 10 := by
  let L := Nat.log 2 N
  let a : ℕ → ℝ := fun m => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  let w : ℕ → ℝ := fun m => ((2 ^ (m + 1) : ℕ) : ℝ) * a m
  let f : ℕ → ℂ := fun m => (a m : ℂ) *
    Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hf : Summable f := power_fourier_summable111 N hN α
  have hw : Summable w := weighted_power_summable412 N hN
  have hcut : (N : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) N).le
  have hterm (j : ℕ) : ‖f (j + L)‖ ≤ w (j + L) / N := by
    have hfreq : (N : ℝ) ≤ ((2 ^ (j + L + 1) : ℕ) : ℝ) := by
      apply hcut.trans
      push_cast
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    dsimp [f, w, a]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_exp_ofReal_mul_I, mul_one]
    apply (le_div_iff₀ hNp).mpr
    nlinarith [Real.exp_pos (-((2 ^ (j + L + 1) : ℕ) : ℝ) / N)]
  have htail : (∑' j : ℕ, w (j + L)) ≤ ∑' j : ℕ, w j := by
    rw [← hw.sum_add_tsum_nat_add L]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun j hj => by dsimp [w, a]; positivity))
  have heq : powerFourier111 N α - powerTrunc412 N α = ∑' j : ℕ, f (j + L) := by
    change (∑' j, f j) - ∑ j ∈ range L, f j = _
    rw [← hf.sum_add_tsum_nat_add L]
    ring
  rw [heq]
  calc
    _ ≤ ∑' j : ℕ, ‖f (j + L)‖ := norm_tsum_le_tsum_norm
      (hf.comp_injective (add_left_injective L)).norm
    _ ≤ ∑' j : ℕ, w (j + L) / N :=
      Summable.tsum_le_tsum hterm (hf.comp_injective (add_left_injective L)).norm
        ((hw.comp_injective (add_left_injective L)).div_const N)
    _ = (∑' j : ℕ, w (j + L)) / N := tsum_div_const
    _ ≤ (∑' j : ℕ, w j) / N := div_le_div_of_nonneg_right htail hNp.le
    _ ≤ (10 * (N : ℝ)) / N := div_le_div_of_nonneg_right (weighted_power_bound412 N hN) hNp.le
    _ = 10 := by field_simp

/-- P0093 page 162 equation 7.7. At zero every retained damping
weight is at least exp of negative one. Thus the finite polynomial grows
at least linearly in the integer base two logarithm of N. -/
theorem power_trunc_zero_lower412 (N : ℕ) (hN : 1 ≤ N) :
    Real.exp (-1) * Nat.log 2 N ≤ ‖powerTrunc412 N 0‖ := by
  let a : ℕ → ℝ := fun m => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have heq : powerTrunc412 N 0 = ((∑ m ∈ range (Nat.log 2 N), a m : ℝ) : ℂ) := by
    simp [powerTrunc412, a, Complex.ofReal_sum]
  rw [heq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg (fun m hm => (Real.exp_pos _).le))]
  calc
    _ = ∑ _m ∈ range (Nat.log 2 N), Real.exp (-1) := by simp [mul_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro m hm
      apply Real.exp_le_exp.mpr
      have hp : 2 ^ (m + 1) ≤ N :=
        (Nat.pow_le_pow_right (by norm_num) (Finset.mem_range.mp hm)).trans
          (Nat.pow_log_le_self 2 (show N ≠ 0 by omega))
      rw [neg_div]
      apply neg_le_neg
      exact (div_le_one hNp).mpr (by exact_mod_cast hp)

/-- P0093 page 162 equation 7.7. A fixed large value margin absorbs
the bounded discarded tail once the finite polynomial at zero is large.
Only the finite polynomial remains on the right side. -/
theorem large_value_to_trunc412 (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ α : ℝ,
      (1 - η / 2) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖ →
      (1 - η) * ‖powerTrunc412 N 0‖ < ‖powerTrunc412 N α‖ := by
  obtain ⟨M, hM⟩ := exists_nat_gt (20 / (η * Real.exp (-1)))
  refine ⟨max 1 (2 ^ M), ?_⟩
  intro N hN α hlarge
  have h1 : 1 ≤ N := by have := le_max_left 1 (2 ^ M); omega
  have hpow : 2 ^ M ≤ N := by have := le_max_right 1 (2 ^ M); omega
  have hlog : M ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) hpow
  have hL : (M : ℝ) ≤ Nat.log 2 N := by exact_mod_cast hlog
  have hbig : 20 < η * ‖powerTrunc412 N 0‖ := by
    have hm := (div_lt_iff₀ (mul_pos hη (Real.exp_pos _))).mp hM
    have hb := power_trunc_zero_lower412 N h1
    have hbη := mul_le_mul_of_nonneg_left hb hη.le
    have hLη := mul_le_mul_of_nonneg_left hL (mul_pos hη (Real.exp_pos (-1))).le
    nlinarith
  have hzero : ‖powerTrunc412 N 0‖ ≤ ‖powerFourier111 N 0‖ := by
    let a : ℕ → ℝ := fun m => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
    have hi : Function.Injective (fun m : ℕ => 2 ^ (m + 1)) :=
      (Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))).comp (add_left_injective 1)
    have ha : Summable a := (damping_summable111 N h1).comp_injective hi
    have heq : powerFourier111 N 0 = ((∑' m, a m : ℝ) : ℂ) := by
      unfold powerFourier111
      rw [Complex.ofReal_tsum]
      apply tsum_congr
      intro m
      simp [a]
    rw [heq]
    simp only [powerTrunc412, mul_zero, zero_mul, neg_zero, Complex.ofReal_zero,
      Complex.exp_zero, mul_one, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (Finset.sum_nonneg (fun m hm => (Real.exp_pos _).le)),
      abs_of_nonneg (tsum_nonneg (fun m => (Real.exp_pos _).le))]
    exact ha.sum_le_tsum _ (fun m hm => (Real.exp_pos _).le)
  have hdiff := power_trunc_error412 N h1 α
  have hnorm := norm_sub_norm_le (powerFourier111 N α) (powerTrunc412 N α)
  have hz := mul_le_mul_of_nonneg_left hzero (show 0 ≤ 1 - η / 2 by linarith)
  nlinarith

end LeanLab.Linnik1951
