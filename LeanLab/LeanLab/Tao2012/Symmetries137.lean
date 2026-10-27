/-
Tao 2012, arXiv 1201.6656v4, pages 16 and 17, basic prime sum identities.
CODEX task137, track T1. AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Tao2012.Decomp1555a

namespace LeanLab.Tao2012.Symmetries137
open Real Finset
open scoped ComplexConjugate
open LeanLab.Tao2012.Decomp1555

/-- Tao 2012, page 17, equation 4.5. Real coefficients give self adjointness. -/
theorem S_neg (η : ℝ → ℝ) (q : ℕ) (x α : ℝ) : S η q x (-α) = conj (S η q x α) := by
  unfold S
  rw [map_sum]
  apply sum_congr rfl
  intro n hn
  simp only [map_mul, Complex.conj_ofReal]
  congr 1
  unfold ee
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_natCast]
  ring

/-- Tao 2012, page 17, equation 4.6. An even coprimality modulus forces odd indices. -/
theorem S_half_shift (η : ℝ → ℝ) (q : ℕ) (hq : Even q) (x α : ℝ) :
    S η q x (α + 1 / 2) = -S η q x α := by
  unfold S
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro n hn
  by_cases hcop : n.Coprime q
  · have hnodd : Odd n := (hcop.of_dvd_right hq.two_dvd).odd_of_right
    have hee : ee ((α + 1 / 2) * n) = -ee (α * n) := by
      obtain ⟨k, hk⟩ := hnodd
      have hsplit : (2 * π * Complex.I * (((α + 1 / 2) * n : ℝ) : ℂ)) =
          2 * π * Complex.I * ((α * n : ℝ) : ℂ) + (k : ℂ) * (2 * π * Complex.I) + π * Complex.I := by
        rw [hk]
        push_cast
        ring
      unfold ee
      rw [hsplit, Complex.exp_add, Complex.exp_add]
      have hkexp : Complex.exp ((k : ℂ) * (2 * π * Complex.I)) = 1 := by
        simpa only [Int.cast_natCast] using Complex.exp_int_mul_two_pi_mul_I (k : ℤ)
      rw [hkexp, Complex.exp_pi_mul_I]
      ring
    rw [hee]
    ring
  · simp [coef, hcop]

/-- Tao 2012, page 16, equation 4.2. The triangle inequality bounds the prime sum by its zero frequency value. -/
theorem S_norm_le_zero (η : ℝ → ℝ) (hη : ∀ t, 0 ≤ η t) (q : ℕ) (x α : ℝ) :
    ‖S η q x α‖ ≤ (S η q x 0).re := by
  have hcn (n : ℕ) : 0 ≤ coef η q x n := by
    unfold coef
    have := hη (n / x)
    have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    split_ifs <;> positivity
  have hee (t : ℝ) : ‖ee t‖ = 1 := by
    simp [ee, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  unfold S
  calc ‖∑ n ∈ range (⌊x⌋₊ + 1), (coef η q x n : ℂ) * ee (α * n)‖ ≤
      ∑ n ∈ range (⌊x⌋₊ + 1), ‖(coef η q x n : ℂ) * ee (α * n)‖ := norm_sum_le _ _
    _ = ∑ n ∈ range (⌊x⌋₊ + 1), coef η q x n := by
      apply sum_congr rfl
      intro n hn
      rw [norm_mul, hee, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hcn n)]
    _ = _ := by simp [ee]

/-- Tao 2012, page 15, equation 4.1 and the frequency space R modulo Z. -/
theorem S_periodic (η : ℝ → ℝ) (q : ℕ) (x : ℝ) : Function.Periodic (S η q x) 1 := by
  intro α
  unfold S
  apply sum_congr rfl
  intro n hn
  congr 1
  unfold ee
  have hsplit : (2 * π * Complex.I * (((α + 1) * n : ℝ) : ℂ)) =
      2 * π * Complex.I * ((α * n : ℝ) : ℂ) + (n : ℂ) * (2 * π * Complex.I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add]
  have hnexp : Complex.exp ((n : ℂ) * (2 * π * Complex.I)) = 1 := by
    simpa only [Int.cast_natCast] using Complex.exp_int_mul_two_pi_mul_I (n : ℤ)
  rw [hnexp, mul_one]

end LeanLab.Tao2012.Symmetries137
