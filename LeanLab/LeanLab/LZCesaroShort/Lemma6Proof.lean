import LeanLab.LZCesaroShort.Theorem2aFull

/-!
# The printed form of P0058 Lemma 6

AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1606.00869v2, page 5, Lemma 6 and equation 14.
The estimate is unconditional. The existing I2 estimate supplies every input.
The square root form equals the printed product of the three square roots.
-/

namespace LeanLab.LZCesaroShort

open Finset MeasureTheory
open scoped Chebyshev

/-- Lemma 6 holds with constant 25 above the threshold ten to the twentieth power. -/
theorem lemma6_explicit {N H : ℕ} {y : ℝ}
    (hN : (10 : ℝ) ^ 20 ≤ N) (hHN : H ≤ N) :
    ‖(∫ α in (-(1 / 2 : ℝ))..(1 / 2),
        TH N H y (-α) * (St N α - 1 / zz N α) * (1 / zz N α))
      - ∑ n ∈ Fy N H y,
        ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ)‖
      ≤ 25 * Real.sqrt ((H : ℝ) ^ 3 * N * Real.log N) := by
  have hN2 : (2 : ℝ) ≤ N := le_trans (by norm_num) hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hHr : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have hlog : 1 ≤ Real.log N := by
    apply (Real.le_log_iff_exp_le (by linarith)).mpr
    have h3 : (3 : ℝ) ≤ N := le_trans (by norm_num) hN
    linarith [Real.exp_one_lt_d9]
  have h1 : Real.sqrt ((H : ℝ) ^ 3 * (4 * N * Real.log N))
      = 2 * Real.sqrt ((H : ℝ) ^ 3 * N * Real.log N) := by
    rw [show (H : ℝ) ^ 3 * (4 * N * Real.log N) =
      4 * ((H : ℝ) ^ 3 * N * Real.log N) by ring,
      Real.sqrt_mul (by norm_num)]
    norm_num
  have h2 : Real.sqrt ((H : ℝ) ^ 3 * (1 + N / 2))
      ≤ Real.sqrt ((H : ℝ) ^ 3 * N * Real.log N) := by
    apply Real.sqrt_le_sqrt
    have hsmall : 1 + (N : ℝ) / 2 ≤ N * Real.log N := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hsmall (pow_nonneg hH0 3)
    nlinarith
  have h3 : (H : ℝ) ^ 2 ≤ Real.sqrt ((H : ℝ) ^ 3 * N * Real.log N) := by
    have hlarge : (H : ℝ) ≤ N * Real.log N := by nlinarith
    calc
      (H : ℝ) ^ 2 = Real.sqrt (((H : ℝ) ^ 2) ^ 2) :=
        (Real.sqrt_sq (sq_nonneg (H : ℝ))).symm
      _ ≤ Real.sqrt ((H : ℝ) ^ 3 * N * Real.log N) := by
        apply Real.sqrt_le_sqrt
        have hm := mul_le_mul_of_nonneg_left hlarge (pow_nonneg hH0 3)
        nlinarith
  have hb := I2_boundY_full (y := y) hN hHN
  rw [show (2 : ℂ) *
      (∫ α in (-(1 / 2 : ℝ))..(1 / 2),
        TH N H y (-α) * (St N α - 1 / zz N α) * (1 / zz N α)) -
      2 * (∑ n ∈ Fy N H y,
        ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ)) =
      2 * ((∫ α in (-(1 / 2 : ℝ))..(1 / 2),
        TH N H y (-α) * (St N α - 1 / zz N α) * (1 / zz N α)) -
        ∑ n ∈ Fy N H y,
          ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ)) by ring,
    norm_mul, Complex.norm_ofNat, h1] at hb
  nlinarith

/-- Lemma 6 on the paper's stated range, with no cited or RH hypothesis. -/
theorem lz_lemma6_proved : (∃ K : ℝ, ∃ N₀ : ℕ, ∀ N H : ℕ, N₀ ≤ N → 1 ≤ H → H ≤ N →
    ∀ y : ℝ, -(H : ℝ) ≤ y → y < H →
      ‖(∫ α in (-(1 / 2 : ℝ))..(1 / 2),
          TH N H y (-α) * (St N α - 1 / zz N α) * (1 / zz N α))
        - ∑ n ∈ Fy N H y,
          ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ)‖
        ≤ K * Real.sqrt ((H : ℝ) ^ 3 * N * Real.log N)) := by
  refine ⟨25, 10 ^ 20, fun N H hN _ hHN y _ _ => ?_⟩
  apply lemma6_explicit (hHN := hHN)
  exact_mod_cast hN

end LeanLab.LZCesaroShort
