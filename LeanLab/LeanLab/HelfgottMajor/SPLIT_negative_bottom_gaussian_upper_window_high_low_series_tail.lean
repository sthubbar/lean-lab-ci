import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_upper_window_high_low_series_compare
import LeanLab.HelfgottMajor.Decomp454e

/-!
Split of `negative_bottom_gaussian_upper_window_high_low_series_tail` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_upper_window_high_low_series_compare`,
burst-20261124, agent S2G8, KEEP GOING.

The complex tail is bounded termwise by a real majorant, which is PROVED here from the proved
bound `|Γ(s)| ≤ Γ(Re s)` of `Decomp454e`. What remains are two real LEAFs about the majorant
`(3 π / 2)^n / n! 2^(n/2 - 3/4) Γ(n/2 + 1/4)`: that it is summable, and that its tail after seventy
terms is at most one thousandth, numerically 0.000364. Both are statements about one explicit real
series with no parameter left.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real

/-- PROVED. Termwise majorant for the power series in the twist parameter of the Gaussian Mellin
transform, Helfgott P0014 section 4: for `|δ| ≤ 3/4` and real part one half, the `n`th term has
modulus at most `(3 π / 2)^n / n! 2^(n/2 - 3/4) Γ(n/2 + 1/4)`, from `|Γ(σ + i τ)| ≤ Γ(σ)`, which is
`Decomp454e.norm_Gamma_le_real`, and `|2^z| = 2^(Re z)`. -/
theorem s2g8_series_term_norm_le (δ : ℝ) (hδ : |δ| ≤ 3 / 4) (s : ℂ) (hs : s.re = 1 / 2) (n : ℕ) :
    ‖(2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((s + n) / 2 - 1) * Complex.Gamma ((s + n) / 2))‖ ≤
      (3 * π / 2) ^ n / (n.factorial : ℝ) *
        ((2 : ℝ) ^ ((n : ℝ) / 2 - 3 / 4) * Real.Gamma ((n : ℝ) / 2 + 1 / 4)) := by
  have hre1 : ((s + n) / 2 - 1).re = (n : ℝ) / 2 - 3 / 4 := by
    simp [hs]; ring
  have hre2 : ((s + n) / 2).re = (n : ℝ) / 2 + 1 / 4 := by
    simp [hs]; ring
  have hpos : 0 < ((s + n) / 2).re := by rw [hre2]; positivity
  have hG := LeanLab.HelfgottMajor.Decomp454e.norm_Gamma_le_real _ hpos
  rw [hre2] at hG
  have h2 : ‖(2 : ℂ) ^ ((s + n) / 2 - 1)‖ = (2 : ℝ) ^ ((n : ℝ) / 2 - 3 / 4) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) ((s + n) / 2 - 1)
    rw [hre1] at this
    simpa using this
  have hb : ‖2 * (π : ℂ) * (δ : ℂ) * Complex.I‖ ≤ 3 * π / 2 := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Complex.norm_ofNat, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  rw [norm_mul, norm_mul _ (Complex.Gamma _), h2, norm_div, norm_pow, Complex.norm_natCast]
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h20 : 0 ≤ (2 : ℝ) ^ ((n : ℝ) / 2 - 3 / 4) := by positivity
  apply mul_le_mul _ (mul_le_mul_of_nonneg_left hG h20) (by positivity) (by positivity)
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hb n) hf.le

/-- LEAF: the real majorant series of the tail step is summable, the ratio of consecutive terms
being of order `3 π / (2 sqrt (2 n))` by Stirling for `Γ(n/2 + 1/4) / n!`; the majorant of the power
series in the twist parameter of the Gaussian Mellin transform, Helfgott P0014 section 4. MEDIUM. -/
theorem s2g8_maj_summable :
    Summable (fun n : ℕ => (3 * π / 2) ^ n / (n.factorial : ℝ) *
        ((2 : ℝ) ^ ((n : ℝ) / 2 - 3 / 4) * Real.Gamma ((n : ℝ) / 2 + 1 / 4))) := by
  sorry

/-- LEAF: the tail after seventy terms of the real majorant series is at most one thousandth;
numerically it is 0.000364, mpmath at 30 digits, S2G8. The majorant of the power series in the
twist parameter of the Gaussian Mellin transform, Helfgott P0014 section 4. MEDIUM. -/
theorem s2g8_maj_tail :
    ∑' n : ℕ, (3 * π / 2) ^ (n + 70) / ((n + 70).factorial : ℝ) *
        ((2 : ℝ) ^ (((n + 70 : ℕ) : ℝ) / 2 - 3 / 4) * Real.Gamma (((n + 70 : ℕ) : ℝ) / 2 + 1 / 4)) ≤
      1 / 1000 := by
  sorry

/-- Assembly of `negative_bottom_gaussian_upper_window_high_low_series_tail`, exactly its statement,
from the PROVED termwise majorant and the two real LEAFs, by `tsum_of_norm_bounded`. -/
theorem negative_bottom_gaussian_upper_window_high_low_series_tail_split (δ : ℝ) (hδ : |δ| ≤ 3 / 4)
    (s : ℂ) (hs : s.re = 1 / 2) :
    ‖(∑' n : ℕ, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((s + n) / 2 - 1) * Complex.Gamma ((s + n) / 2))) -
        ∑ n ∈ Finset.range 70, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((s + n) / 2 - 1) * Complex.Gamma ((s + n) / 2))‖ ≤ 1 / 1000 := by
  have hb := s2g8_series_term_norm_le δ hδ s hs
  have hm := s2g8_maj_summable
  have hf : Summable (fun n : ℕ => (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((s + n) / 2 - 1) * Complex.Gamma ((s + n) / 2))) :=
    Summable.of_norm_bounded hm hb
  rw [← hf.sum_add_tsum_nat_add 70, add_sub_cancel_left]
  have hm70 := (summable_nat_add_iff 70).mpr hm
  refine (tsum_of_norm_bounded hm70.hasSum (fun i => ?_)).trans s2g8_maj_tail
  have := hb (i + 70)
  push_cast at this ⊢
  exact this

end LeanLab.HelfgottMajor.Decomp431a
