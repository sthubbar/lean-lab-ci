import LeanLab.LZCesaroShort.Decomp245a

/-!
AI wrote the Lean code. Binary Goldbach is open.
Source: https://arxiv.org/abs/1606.00869v2 page 2, equation 3.
The H equal to one endpoint follows from Chebyshev without RH.
This does not prove the full legacy Theorem2b.
-/

namespace LeanLab.LZCesaroShort

open Finset
open scoped ArithmeticFunction.vonMangoldt Chebyshev

/-- At H equal to one only the central term of the full weighted sum survives. -/
lemma wsum_one {N : ℕ} (hN : 1 ≤ N) :
    wsum N 1 1 = Real.exp (-1) * (R N - (2 * ψ (N : ℝ) - N)) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  unfold wsum
  rw [sum_eq_single N]
  · simp [w, hN0]
  · intro n hn hne
    have hn' := (mem_filter.mp hn).1
    rw [mem_Icc] at hn'
    have : n = N - 1 ∨ n = N + 1 := by omega
    rcases this with rfl | rfl
    · simp [w, Nat.cast_sub hN]
    · simp [w]
  · intro h
    exfalso
    apply h
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    simp

/-- The H equal to one weighted discrepancy is at most an explicit constant times N log N.
This strengthens the printed endpoint in equation 3 and uses no RH input. -/
theorem theorem2b_legacy_H1 {N : ℕ} (hN : 2 ≤ N) :
    |wsum N 1 1| ≤ (5 * (Real.log 4 + 4) + 2) * N * Real.log N := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hLhalf : (1 / 2 : ℝ) ≤ Real.log (N : ℝ) := by
    have h1 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hNr
    norm_num at h1
    linarith
  have hNL : (N : ℝ) ≤ 2 * (N * Real.log N) := by nlinarith
  have hR := R_le_chebyshev N
  have hψ := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α := ℝ) N)
  have hR0 := R_nonneg N
  have hψ0 := Chebyshev.psi_nonneg (N : ℝ)
  have hC0 : 0 ≤ Real.log 4 + 4 := by positivity
  have hraw : |R N - (2 * ψ (N : ℝ) - N)| ≤ R N + 2 * ψ (N : ℝ) + N := by
    rw [abs_le]
    constructor <;> linarith
  have hraw0 : 0 ≤ R N + 2 * ψ (N : ℝ) + N := by positivity
  have hexp : Real.exp (-1) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
  rw [wsum_one (by omega), abs_mul, Real.abs_exp]
  calc
    _ ≤ 1 * (R N + 2 * ψ (N : ℝ) + N) :=
      mul_le_mul hexp hraw (abs_nonneg _) zero_le_one
    _ ≤ (5 * (Real.log 4 + 4) + 2) * N * Real.log N := by
      have hC := mul_le_mul_of_nonneg_left hNL hC0
      nlinarith

end LeanLab.LZCesaroShort
