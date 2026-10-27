/-
R-0002, T3 MOONSHOT, run 20261019T0202Z-9877, unit U-1004: the binary Liouville reflection
correlation `c(N) = Σ_{a+b=N} λ(a) λ(b)`, the parity-sensitive quantity that sieve bounds for
`r(N)` leave behind.

The route: parity-breaking information for binary Goldbach would follow from `c(N) = o(N)`
for every large `N`, with sieve weights attached. This file proves the averaged form on
`ZMod M` from a uniform sup bound on the Fourier transform, the Davenport-type input:
if `|Φ̂(k)| ≤ U` for every `k`, then `#{n : |M Σ_j Φ(j) Φ(n - j)| ≥ T} · T² ≤ M² U² Σ |Φ|²`.
With `Φ = λ` on `[1, x]`, `M > 2x`, `U = δ M`-normalized as `δ x` and `T = ε M x`, at most
`δ² x / ε²` values `n` have `|c(n)| ≥ ε x`. So `c(N) = o(N)` for all but `o(x)` values `N ≤ x`
once `δ → 0`, which Davenport's theorem gives with `δ = (log x)^{-A}`. A single `N` is out of
reach: the bound only controls the mean square, the same L² barrier as R-0001.

KNOWN mathematics: the averaged statement is folklore from Davenport's bound; nothing here is
new. AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN, and
nothing here is progress on it.
-/
import LeanLab.ExceptionalSet.MVMinorL4

open ZMod Finset

namespace LeanLab.Routes.R0002
open LeanLab.Routes.R0001 LeanLab.ExceptionalSet.MV

variable {M : ℕ} [NeZero M]

/-- The whole-circle part is the full convolution: `minorPart Φ univ n = M Σ_j Φ j Φ (n - j)`. -/
theorem minorPart_univ (Φ : ZMod M → ℂ) (n : ZMod M) :
    minorPart Φ univ n = (M : ℂ) * ∑ j, Φ j * Φ (n - j) := by
  unfold minorPart
  exact sum_dft_sq Φ n

/-- **Large convolution values are rare under a uniform Fourier bound.** For `T ≥ 0` and
`|Φ̂(k)| ≤ U` for every `k`: `#{n : T ≤ |M (Φ * Φ)(n)|} · T² ≤ M · U² · M Σ |Φ|²`. -/
theorem card_large_conv_le (Φ : ZMod M → ℂ) {U T : ℝ} (hT : 0 ≤ T)
    (hU : ∀ k, ‖𝓕 Φ k‖ ≤ U) :
    ((univ.filter fun n => T ≤ ‖(M : ℂ) * ∑ j, Φ j * Φ (n - j)‖).card : ℝ) * T ^ 2
      ≤ (M : ℝ) * (U ^ 2 * ((M : ℝ) * ∑ j, ‖Φ j‖ ^ 2)) := by
  classical
  have hset : (univ.filter fun n => T ≤ ‖(M : ℂ) * ∑ j, Φ j * Φ (n - j)‖)
      = univ.filter fun n => T ≤ ‖minorPart Φ univ n‖ := by
    refine Finset.filter_congr fun n _ => ?_
    rw [minorPart_univ]
  rw [hset]
  refine (card_large_minor_le Φ univ T hT).trans ?_
  gcongr
  exact minor_L4_le_sup Φ univ fun k _ => hU k

/-- **The normalized count.** If `Σ |Φ|² ≤ x`, `|Φ̂(k)| ≤ δ x` for every `k`, `x > 0`, `ε > 0`,
then at most `δ² x / ε²` values `n` have `|Σ_j Φ(j) Φ(n - j)| ≥ ε x`. -/
theorem card_large_corr_le (Φ : ZMod M → ℂ) {x δ ε : ℝ} (hx : 0 < x) (hε : 0 < ε)
    (h2 : ∑ j, ‖Φ j‖ ^ 2 ≤ x) (hU : ∀ k, ‖𝓕 Φ k‖ ≤ δ * x) :
    ((univ.filter fun n => ε * x ≤ ‖∑ j, Φ j * Φ (n - j)‖).card : ℝ) ≤ δ ^ 2 * x / ε ^ 2 := by
  classical
  have hM : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hT : 0 ≤ (M : ℝ) * (ε * x) := by positivity
  have h := card_large_conv_le Φ hT hU
  have hset : (univ.filter fun n => (M : ℝ) * (ε * x) ≤ ‖(M : ℂ) * ∑ j, Φ j * Φ (n - j)‖)
      = univ.filter fun n => ε * x ≤ ‖∑ j, Φ j * Φ (n - j)‖ := by
    refine Finset.filter_congr fun n _ => ?_
    rw [norm_mul, Complex.norm_natCast]
    constructor
    · intro hh; exact le_of_mul_le_mul_left hh hM
    · intro hh; exact mul_le_mul_of_nonneg_left hh hM.le
  rw [hset] at h
  set c := ((univ.filter fun n => ε * x ≤ ‖∑ j, Φ j * Φ (n - j)‖).card : ℝ)
  have hR : (M : ℝ) * ((δ * x) ^ 2 * ((M : ℝ) * ∑ j, ‖Φ j‖ ^ 2))
      ≤ (M : ℝ) * ((δ * x) ^ 2 * ((M : ℝ) * x)) := by gcongr
  have key : c * ((M : ℝ) * (ε * x)) ^ 2 ≤ ((M : ℝ) * (ε * x)) ^ 2 * (δ ^ 2 * x / ε ^ 2) := by
    have e : ((M : ℝ) * (ε * x)) ^ 2 * (δ ^ 2 * x / ε ^ 2)
        = (M : ℝ) * ((δ * x) ^ 2 * ((M : ℝ) * x)) := by field_simp
    rw [e]; linarith
  have hpos : 0 < ((M : ℝ) * (ε * x)) ^ 2 := by positivity
  rw [mul_comm] at key
  exact le_of_mul_le_mul_left key hpos

/-- Vacuity test: the zero function meets every hypothesis with `δ = 0`, and then no `n`
qualifies; for `Φ = λ` on `[1, x]` the hypotheses are Davenport's theorem and `Σ |λ|² ≤ x`. -/
example : ((univ.filter fun n : ZMod 5 =>
      (1 : ℝ) * 1 ≤ ‖∑ j : ZMod 5, (fun _ => (0 : ℂ)) j * (fun _ => (0 : ℂ)) (n - j)‖).card : ℝ)
    ≤ 0 ^ 2 * 1 / 1 ^ 2 :=
  card_large_corr_le (M := 5) (fun _ => (0 : ℂ)) (x := 1) (δ := 0) (ε := 1)
    one_pos one_pos (by simp) (fun k => by simp [dft_apply])

#print axioms minorPart_univ
#print axioms card_large_conv_le
#print axioms card_large_corr_le

end LeanLab.Routes.R0002
