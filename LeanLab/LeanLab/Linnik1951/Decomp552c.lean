/-
P0093 pages 155 and 161. Signed Ramanujan sinc expansion.
The exact arithmetic kernel retains all frequencies, including small residual tails.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp552b
import LeanLab.Linnik1951.Decomp520a

namespace LeanLab.Linnik1951
open MeasureTheory Finset

/-- P0093 page 155 equation 3.1 and page 161 equation 6.4.
The reduced residue phase at a signed integer equals the existing natural
Ramanujan sum at its absolute value. -/
theorem signed_ramanujan_abs552 (q : ℕ) (hq : 1 ≤ q) (n : ℤ) :
    signedRamanujan520 q n = LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.natAbs := by
  by_cases hn : 0 ≤ n
  · simpa only [show n.toNat = n.natAbs by omega] using signedRamanujan_toNat520 q n hn
  · have hn' : 0 ≤ -n := by omega
    have he := signedRamanujan_toNat520 q (-n) hn'
    have hconj : (starRingEnd ℂ) (signedRamanujan520 q (-n)) = signedRamanujan520 q n := by
      unfold signedRamanujan520
      simp only [map_sum]
      apply sum_congr rfl
      intro a ha
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    rw [he, Complex.conj_eq_iff_im.mpr (ramanujan_im_zero520 _ _ hq)] at hconj
    simpa only [show (-n).toNat = n.natAbs by omega] using hconj.symm

/-- P0093 page 161 equation 6.3. Multiplication by the centred window
kernel preserves absolute summability, since sinc has modulus at most one. -/
theorem kernel_series_summable552 (a : ℕ → ℂ) (ha : Summable a) (r : ℝ) (hr : 0 ≤ r) (c w : ℝ) :
    Summable (fun k : ℕ => a k *
      Complex.exp ((((w - 2 * Real.pi * k) * c : ℝ) : ℂ) * Complex.I) *
      ((2 * r * Real.sinc ((w - 2 * Real.pi * k) * r) : ℝ) : ℂ)) := by
  apply Summable.of_norm_bounded (ha.norm.mul_right (2 * r))
  intro k
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ = (‖a k‖ * (2 * r)) * |Real.sinc ((w - 2 * Real.pi * k) * r)| := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) (Real.abs_sinc_le_one _)


/-- P0093 pages 155 and 161 equations 3.1 and 6.3. Finite residue
summation of a squared summable series gives the signed Ramanujan sum
at each convolution frequency, multiplied by its exact window kernel. -/
theorem rational_square_window552 (a : ℕ → ℂ) (ha : Summable a)
    (q : ℕ) (n : ℤ) (r : ℝ) (hr : 0 ≤ r) :
    (∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
      ∫ z in -r..r, (∑' k : ℕ, a k *
        Complex.exp ((-(2 * Real.pi * ((b : ℝ) / q + z) * k) : ℝ) * Complex.I)) ^ 2 *
          Complex.exp (((2 * Real.pi * (n : ℝ) * ((b : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) =
    ∑' k : ℕ, (∑ m ∈ range (k + 1), a m * a (k - m)) *
      signedRamanujan520 q (n - (k : ℤ)) *
      ((2 * r * Real.sinc (2 * Real.pi * ((n : ℝ) - k) * r) : ℝ) : ℂ) := by
  simp_rw [square_symmetric_integral552 a ha r hr]
  have hconv : Summable (fun k => ∑ m ∈ range (k + 1), a m * a (k - m)) :=
    (summable_norm_sum_mul_range_of_summable_norm ha.norm ha.norm).of_norm
  have hp (k : ℕ) : 2 * Real.pi * (n : ℝ) - 2 * Real.pi * k =
      2 * Real.pi * ((n : ℝ) - k) := by ring
  have hs (b : ℕ) (_hb : b ∈ (range q).filter (fun b => Nat.Coprime b q)) :
      Summable (fun k : ℕ => (∑ m ∈ range (k + 1), a m * a (k - m)) *
        Complex.exp (((2 * Real.pi * ((n : ℝ) - k) * ((b : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
        ((2 * r * Real.sinc (2 * Real.pi * ((n : ℝ) - k) * r) : ℝ) : ℂ)) := by
    simpa only [hp] using kernel_series_summable552 _ hconv r hr ((b : ℝ) / q)
      (2 * Real.pi * n)
  rw [← Summable.tsum_finsetSum hs]
  apply tsum_congr
  intro k
  rw [← sum_mul, ← mul_sum]
  congr 2
  unfold signedRamanujan520
  apply sum_congr rfl
  intro b hb
  congr 1
  push_cast
  ring

/-- P0093 page 155 equation 3.1. Exact local prime square expansion in
natural Ramanujan sums and sinc factors. The absolute value belongs to
the signed frequency difference, not to the residual alone. -/
theorem local_arc_ramanujan_kernel552 (N : ℕ) (hN : 1 ≤ N)
    (q : ℕ) (hq : 1 ≤ q) (n : ℤ) :
    localArc1622 N q n =
    ∑' k : ℕ, ((primePairCount552 k : ℂ) * (Real.exp (-(k : ℝ) / N) : ℂ)) *
      LeanLab.Perelli1996.Ramanujan103.ramanujanSum q (n - (k : ℤ)).natAbs *
      ((2 * (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) *
        Real.sinc (2 * Real.pi * ((n : ℝ) - k) *
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) : ℝ) : ℂ) := by
  unfold localArc1622
  simp_rw [prime_series_nat552]
  rw [rational_square_window552 _ (prime_coefficients_summable552 N hN) q n _ (by positivity)]
  simp_rw [prime_coefficient_convolution552, signed_ramanujan_abs552 q hq]

end LeanLab.Linnik1951
