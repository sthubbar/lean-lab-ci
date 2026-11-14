/-
Split of the sealed principal convolution estimate principal_convolution491 of
Decomp491b. The target statement stays exactly as it is; this file adds four leaves
and one assembly. Every leaf is one of the case steps of the original argument and
is strictly weaker than the target.

The argument. The principal square integral on the short arc of a reduced fraction
is compared with the exactly damped logarithmic convolution. Three things can be
separated without changing the statement: the size of the square integral on the
arc, taken in absolute value and with no main term subtracted; the unit modulus,
where the principal character series is the full prime series and the arc is the
longest admissible one; and the general modulus, split into the moduli below the
one twentieth power of N, where the arc is still long compared with the unit one,
and the moduli above it, where the arc is short and the reciprocal length term is
the smaller of the two errors. At a residual at most three the convolution is an
empty sum, so only the size of the integral is used there, and that case is closed
below from the size leaf alone, with no extra leaf.

The assembly only splits on the residual, on the modulus equal to one, and on the
size of the modulus, adds the four constants and folds the four error sizes into
the single printed one. No analytic input is invented here.
-/
import LeanLab.Linnik1951.Decomp491b

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- LEAF. The size step. The principal square integral over the short arc, taken in
absolute value, is bounded by the two printed error sizes alone: the reciprocal of
the arc length and the reciprocal of the square root of the arc length, both times N
and the thirteenth power of the logarithm. Nothing is subtracted from the integral,
no character twist occurs, and the residual may be any integer at most N. -/
theorem principal_integral_amplitude491 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
        ‖principalIntegral491 N q n‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- LEAF. The unit modulus step. At modulus one the reduced residue set is the single
residue zero, the principal character series is the full prime Fourier series, and
the arc is the longest one the parameter range allows. For every residual from four
up to N the square integral differs from the exactly damped logarithmic convolution
by at most the two printed error sizes. -/
theorem principal_convolution_unit_modulus491 (hG : LeanLab.DERZ1997.GRH)
    (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → q = 1 → ∀ n : ℤ, 4 ≤ n → n ≤ N →
        ‖principalIntegral491 N q n -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- LEAF. The intermediate modulus step. For a modulus between two and the one
twentieth power of N, a reduced residue twist is present but the arc is still long,
so both printed error sizes are needed. For every residual from four up to N the
square integral differs from the exactly damped logarithmic convolution by at most
the two printed error sizes. -/
theorem principal_convolution_intermediate_modulus491 (hG : LeanLab.DERZ1997.GRH)
    (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        2 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) → ∀ n : ℤ, 4 ≤ n → n ≤ N →
        ‖principalIntegral491 N q n -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- LEAF. The large modulus step. For a modulus at least the one twentieth power of N
the arc is short and the reciprocal length term is the smaller of the two printed
error sizes, while the square root term and the thirteenth power of the logarithm are
the ones that survive. For every residual from four up to N the square integral
differs from the exactly damped logarithmic convolution by at most the two printed
error sizes. -/
theorem principal_convolution_large_modulus491 (hG : LeanLab.DERZ1997.GRH)
    (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        2 ≤ q → (N : ℝ) ^ (1 / 20 : ℝ) ≤ (q : ℝ) → ∀ n : ℤ, 4 ≤ n → n ≤ N →
        ‖principalIntegral491 N q n -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- Folding a constant into a larger one, at a fixed nonnegative error size. -/
private theorem scale_const_le491 {c d N lg L : ℝ} (hcd : c ≤ d) (hN : 0 ≤ N)
    (hlg : 0 ≤ lg) (hL : 0 ≤ L) : c * N * lg * L ≤ d * N * lg * L := by
  have hE : 0 ≤ N * lg * L := mul_nonneg (mul_nonneg hN hlg) hL
  have h1 : c * (N * lg * L) ≤ d * (N * lg * L) := mul_le_mul_of_nonneg_right hcd hE
  calc c * N * lg * L = c * (N * lg * L) := by ring
    _ ≤ d * (N * lg * L) := h1
    _ = d * N * lg * L := by ring

/-- The principal convolution estimate, assembled from the four case steps. The
statement is the sealed one, unchanged. At a residual at most three the convolution
is the empty sum, so the size step alone suffices; above three the four modulus cases
cover every positive modulus, and the constants are added. -/
theorem principal_convolution491_split (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
        ‖principalIntegral491 N q n -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨C1, hC1, N1, h1⟩ := principal_integral_amplitude491 hG hM
  obtain ⟨C2, hC2, N2, h2⟩ := principal_convolution_unit_modulus491 hG hM
  obtain ⟨C3, hC3, N3, h3⟩ := principal_convolution_intermediate_modulus491 hG hM
  obtain ⟨C4, hC4, N4, h4⟩ := principal_convolution_large_modulus491 hG hM
  refine ⟨C1 + C2 + C3 + C4, by positivity,
    max 8 (max N1 (max (max N2 N3) N4)), ?_⟩
  intro N hN q hq hqQ n hn
  have hrest : max N1 (max (max N2 N3) N4) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hrest
  have htail : max (max N2 N3) N4 < N := lt_of_le_of_lt (le_max_right _ _) hrest
  have hN2 : N2 < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) htail
  have hN3 : N3 < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) htail
  have hN4 : N4 < N := lt_of_le_of_lt (le_max_right _ _) htail
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1r : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hpow : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNr _
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1r
  have hL : 0 ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
      1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    have hA : (0 : ℝ) < 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
    have hB : (0 : ℝ) < 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
    linarith
  rcases le_or_gt n 3 with hn3 | hn4
  · have hb := h1 N hN1 q hq hqQ n hn
    have hv : n.toNat ≤ 3 := Int.toNat_le.mpr hn3
    have hz : logConvolution1622 n.toNat = 0 := logConvolution_vanish491 n.toNat hv
    have hsimp : ‖principalIntegral491 N q n -
        ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ =
        ‖principalIntegral491 N q n‖ := by
      rw [hz]
      simp
    rw [hsimp]
    exact hb.trans (scale_const_le491 (by linarith : C1 ≤ C1 + C2 + C3 + C4)
      hNr.le (pow_nonneg hlog 13) hL)
  · have hn4' : (4 : ℤ) ≤ n := by omega
    rcases eq_or_lt_of_le hq with hq1 | hq2
    · subst hq1
      have hb := h2 N hN2 1 (le_refl 1) hqQ rfl n hn4' hn
      exact hb.trans (scale_const_le491 (by linarith : C2 ≤ C1 + C2 + C3 + C4)
        hNr.le (pow_nonneg hlog 13) hL)
    · have hq2' : 2 ≤ q := by omega
      rcases le_or_gt (q : ℝ) ((N : ℝ) ^ (1 / 20 : ℝ)) with hsmall | hbig
      · have hb := h3 N hN3 q hq hqQ hq2' hsmall n hn4' hn
        exact hb.trans (scale_const_le491 (by linarith : C3 ≤ C1 + C2 + C3 + C4)
          hNr.le (pow_nonneg hlog 13) hL)
      · have hb := h4 N hN4 q hq hqQ hq2' hbig.le n hn4' hn
        exact hb.trans (scale_const_le491 (by linarith : C4 ≤ C1 + C2 + C3 + C4)
          hNr.le (pow_nonneg hlog 13) hL)

end LeanLab.Linnik1951
