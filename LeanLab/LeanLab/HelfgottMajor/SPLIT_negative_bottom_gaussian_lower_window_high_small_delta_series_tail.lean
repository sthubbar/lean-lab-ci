import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_high_small_delta_series_compare
import LeanLab.HelfgottMajor.Decomp454e

/-!
Split of `negative_bottom_gaussian_lower_window_high_small_delta_series_tail` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_high_small_delta_series_compare`.

Source: P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 43, the proof of
display 4.43, small parameter power series of the twisted Gaussian Mellin transform.

The termwise majorant is proved: for `|δ| ≤ 1/2` and real part one half the n th term has norm at
most `π^n / n! * 2^((n + 1/2)/2 - 1) * Γ((n + 1/2)/2)`, from `|Γ(s)| ≤ Γ(Re s)`, proved as
`Decomp454e.norm_Gamma_le_real`, and `|2^w| = 2^(Re w)`. The remaining leaf is the real statement
that this majorant is summable with sum from forty on at most one ten thousandth; numerically
the sum is 2.892e-5. Summability and the tail bound for the series follow by comparison.

The leaf is OPEN. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- PROVED: termwise majorant of the small parameter series, P0014 page 43, proof of display 4.43,
by `|Γ(s)| ≤ Γ(Re s)` and `|2^w| = 2^(Re w)`, for `|δ| ≤ 1/2` and real part one half. -/
theorem negative_bottom_gaussian_lower_window_high_small_delta_series_term_le (δ : ℝ)
    (hδ : |δ| ≤ 1 / 2) {S : ℂ} (hS : S.re = 1 / 2) (m : ℕ) :
    ‖(2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) *
        ((2 : ℂ) ^ ((S + m) / 2 - 1) * Complex.Gamma ((S + m) / 2))‖ ≤
      π ^ m / (m.factorial : ℝ) * ((2 : ℝ) ^ (((1 / 2 : ℝ) + m) / 2 - 1) *
        Real.Gamma (((1 / 2 : ℝ) + m) / 2)) := by
  have hre : ((S + m) / 2).re = ((1 / 2 : ℝ) + m) / 2 := by
    simp [hS]
  have hpos : 0 < ((S + m) / 2).re := by rw [hre]; positivity
  have hG := Decomp454e.norm_Gamma_le_real ((S + m) / 2) hpos
  rw [hre] at hG
  have h2 : ‖(2 : ℂ) ^ ((S + m) / 2 - 1)‖ = (2 : ℝ) ^ (((1 / 2 : ℝ) + m) / 2 - 1) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    simp [hS]
  have hb : ‖(2 * (π : ℂ) * (δ : ℂ) * Complex.I)‖ ≤ π := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2n]
    nlinarith [Real.pi_pos, abs_nonneg δ]
  rw [norm_mul, norm_div, norm_pow, norm_mul ((2 : ℂ) ^ ((S + m) / 2 - 1)), h2,
    Complex.norm_natCast]
  have hf : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hp : ‖(2 * (π : ℂ) * (δ : ℂ) * Complex.I)‖ ^ m ≤ π ^ m :=
    pow_le_pow_left₀ (norm_nonneg _) hb m
  have h2p : (0 : ℝ) ≤ (2 : ℝ) ^ (((1 / 2 : ℝ) + m) / 2 - 1) := by positivity
  gcongr

/-- LEAF: the real majorant series, P0014 page 43, proof of display 4.43: the series with terms
`π^n / n! * 2^((n + 1/2)/2 - 1) * Γ((n + 1/2)/2)` is summable and its sum from forty on is at most
one ten thousandth. MEDIUM: the ratio of consecutive terms is
`π √2 Γ((n + 3/2)/2) / ((n + 1) Γ((n + 1/2)/2))`, at most `π √2 √((n + 1/2)/2) / (n + 1)` by
Wendel's inequality `Γ(x + 1/2) ≤ √x Γ(x)`, which is below one half from forty on, so the tail is at
most twice the term at forty; numerically the tail is 2.892e-5 and the term at forty is 1.505e-5. -/
theorem negative_bottom_gaussian_lower_window_high_small_delta_series_majorant_tail :
    Summable (fun n : ℕ => π ^ n / (n.factorial : ℝ) * ((2 : ℝ) ^ (((1 / 2 : ℝ) + n) / 2 - 1) *
        Real.Gamma (((1 / 2 : ℝ) + n) / 2))) ∧
      ∑' n : ℕ, π ^ (n + 40) / ((n + 40).factorial : ℝ) *
          ((2 : ℝ) ^ (((1 / 2 : ℝ) + ((n + 40 : ℕ) : ℝ)) / 2 - 1) *
            Real.Gamma (((1 / 2 : ℝ) + ((n + 40 : ℕ) : ℝ)) / 2)) ≤ 1 / 10000 := by
  sorry

/-- The statement of `negative_bottom_gaussian_lower_window_high_small_delta_series_tail`, by
comparison with the real majorant. -/
theorem negative_bottom_gaussian_lower_window_high_small_delta_series_tail_split (δ : ℝ)
    (hδ : |δ| ≤ 1 / 2) {S : ℂ} (hS : S.re = 1 / 2) :
    Summable (fun n : ℕ => (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
        ((2 : ℂ) ^ ((S + n) / 2 - 1) * Complex.Gamma ((S + n) / 2))) ∧
      ‖∑' n : ℕ, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ (n + 40) / ((n + 40).factorial : ℂ) *
          ((2 : ℂ) ^ ((S + ((n + 40 : ℕ) : ℂ)) / 2 - 1) *
            Complex.Gamma ((S + ((n + 40 : ℕ) : ℂ)) / 2))‖ ≤ 1 / 10000 := by
  obtain ⟨hsum, htail⟩ := negative_bottom_gaussian_lower_window_high_small_delta_series_majorant_tail
  have hterm := negative_bottom_gaussian_lower_window_high_small_delta_series_term_le δ hδ hS
  refine ⟨Summable.of_norm_bounded hsum hterm, ?_⟩
  have hs40 := (summable_nat_add_iff 40).mpr hsum
  exact (tsum_of_norm_bounded hs40.hasSum (fun n => hterm (n + 40))).trans htail

end LeanLab.HelfgottMajor.Decomp431a
