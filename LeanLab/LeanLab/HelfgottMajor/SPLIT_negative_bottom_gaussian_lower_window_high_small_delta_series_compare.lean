import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_high_small_delta

/-!
Split of `negative_bottom_gaussian_lower_window_high_small_delta_series_compare` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_high_small_delta`, into the two
steps named in that leaf: an explicit tail bound and a certified evaluation of finitely many terms.

Source: P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 43, the proof of
display 4.43; the small parameter expansion of the Mellin transform of the twisted Gaussian
`e^(-t^2/2) e(δ t)` in powers of `δ`, with coefficients `2^((s+n)/2 - 1) Γ((s+n)/2)` from the proved
closed form at `δ = 0`.

The series is cut after forty terms. For `|δ| ≤ 1/2` and real part one half the n th term has norm
at most `π^n / n! * 2^((n + 1/2)/2 - 1) Γ((n + 1/2)/2)`, by `|Γ(σ + i τ)| ≤ Γ(σ)` and
`|2^w| = 2^(Re w)`; the sum of these bounds from forty on is 2.892e-5, under one ten thousandth.
The finite comparison then has slack one ten thousandth on both sides.

Numerics, mpmath at thirty digits, δ in steps of one two hundredth on `[-1/2, 1/2]`, six ordinates on
the window: the norm of the partial sum at `1/2 - i` is at least 0.0583, and the ratio of the
partial sums is at most 0.960; the slack in the finite leaf is at least 0.0917.

Both leaves are OPEN. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF: tail of the small parameter power series of the twisted Gaussian Mellin transform,
P0014 page 43, proof of display 4.43, through `|Γ(σ + i τ)| ≤ Γ(σ)` for `σ > 0`,
`|2^w| = 2^(Re w)` and the explicit real majorant `π^n / n! * 2^((n + 1/2)/2 - 1) Γ((n + 1/2)/2)`,
whose sum from forty on is 2.892e-5 numerically. MEDIUM: summability and a tail bound for
`|δ| ≤ 1/2` at real part one half. -/
theorem negative_bottom_gaussian_lower_window_high_small_delta_series_tail (δ : ℝ)
    (hδ : |δ| ≤ 1 / 2) {S : ℂ} (hS : S.re = 1 / 2) :
    Summable (fun n : ℕ => (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
        ((2 : ℂ) ^ ((S + n) / 2 - 1) * Complex.Gamma ((S + n) / 2))) ∧
      ‖∑' n : ℕ, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ (n + 40) / ((n + 40).factorial : ℂ) *
          ((2 : ℂ) ^ ((S + ((n + 40 : ℕ) : ℂ)) / 2 - 1) *
            Complex.Gamma ((S + ((n + 40 : ℕ) : ℂ)) / 2))‖ ≤ 1 / 10000 := by
  sorry

/-- LEAF: certified evaluation of the first forty terms of the small parameter series, P0014 page
43, proof of display 4.43: for `|δ| ≤ 1/2` and ordinates from minus eleven eighths to minus five
quarters, the partial sum at `1/2 + i t` plus one ten thousandth is at most twice the partial sum
at `1/2 - i` minus one ten thousandth. HARD: a polynomial of degree thirty nine in `δ` with complex
Gamma values on a short vertical segment, by interval evaluation; numerically the ratio of the
partial sums is at most 0.960 and the reference partial sum is at least 0.0583. -/
theorem negative_bottom_gaussian_lower_window_high_small_delta_series_finite_compare (δ : ℝ)
    (hδ : |δ| ≤ 1 / 2) {t : ℝ} (hlo : -(11 / 8) ≤ t) (hhi : t ≤ -(5 / 4)) :
    ‖∑ n ∈ Finset.range 40, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2 - 1) *
            Complex.Gamma ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2))‖ + 1 / 10000 ≤
      2 * (‖∑ n ∈ Finset.range 40, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) - Complex.I) + n) / 2 - 1) *
            Complex.Gamma ((((1 / 2 : ℂ) - Complex.I) + n) / 2))‖ - 1 / 10000) := by
  sorry

/-- The series minus its first forty terms is the tail, so it has norm at most one ten
thousandth, from the tail leaf. Supporting step for the assembly. -/
theorem negative_bottom_gaussian_lower_window_high_small_delta_series_trunc (δ : ℝ)
    (hδ : |δ| ≤ 1 / 2) {S : ℂ} (hS : S.re = 1 / 2) :
    ‖(∑' n : ℕ, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((S + n) / 2 - 1) * Complex.Gamma ((S + n) / 2))) -
        ∑ n ∈ Finset.range 40, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((S + n) / 2 - 1) * Complex.Gamma ((S + n) / 2))‖ ≤ 1 / 10000 := by
  obtain ⟨hsum, ht⟩ := negative_bottom_gaussian_lower_window_high_small_delta_series_tail δ hδ hS
  rw [← hsum.sum_add_tsum_nat_add 40, add_sub_cancel_left]
  exact ht

/-- The statement of `negative_bottom_gaussian_lower_window_high_small_delta_series_compare`,
assembled from the tail bound and the finite comparison by the triangle inequality. -/
theorem negative_bottom_gaussian_lower_window_high_small_delta_series_compare_split (δ : ℝ)
    (hδ : |δ| ≤ 1 / 2) {t : ℝ} (hlo : -(11 / 8) ≤ t) (hhi : t ≤ -(5 / 4)) :
    ‖∑' n : ℕ, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2 - 1) * Complex.Gamma ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2))‖ ≤
      2 * ‖∑' n : ℕ, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) - Complex.I) + n) / 2 - 1) * Complex.Gamma ((((1 / 2 : ℂ) - Complex.I) + n) / 2))‖ := by
  have h1 := negative_bottom_gaussian_lower_window_high_small_delta_series_trunc δ hδ
    (S := (1 / 2 : ℂ) + (t : ℝ) * Complex.I) (by simp)
  have h2 := negative_bottom_gaussian_lower_window_high_small_delta_series_trunc δ hδ
    (S := (1 / 2 : ℂ) - Complex.I) (by simp)
  have hf := negative_bottom_gaussian_lower_window_high_small_delta_series_finite_compare δ hδ hlo hhi
  have t1 := norm_le_norm_sub_add
    (∑' n : ℕ, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2 - 1) * Complex.Gamma ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2)))
    (∑ n ∈ Finset.range 40, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2 - 1) * Complex.Gamma ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2)))
  have t2 := norm_le_norm_sub_add
    (∑ n ∈ Finset.range 40, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) - Complex.I) + n) / 2 - 1) * Complex.Gamma ((((1 / 2 : ℂ) - Complex.I) + n) / 2)))
    (∑' n : ℕ, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) - Complex.I) + n) / 2 - 1) * Complex.Gamma ((((1 / 2 : ℂ) - Complex.I) + n) / 2)))
  rw [norm_sub_rev] at t2
  linarith

end LeanLab.HelfgottMajor.Decomp431a
