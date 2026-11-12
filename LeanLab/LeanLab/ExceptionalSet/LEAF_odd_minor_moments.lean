import Mathlib
import LeanLab.ExceptionalSet.OddSupplyJ200
import LeanLab.ExceptionalSet.LEAF_display29_steps
import LeanLab.ExceptionalSet.State1539

/-!
The two minor arc second moments (29) and (30) of P0082, open leaves for
`DecompJ200.leaf_major_odd_moment`.
Source: P0082, J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378, https://doi.org/10.5802/aif.1621, pages 366 to 369.

Page 367 defines `𝒩_e = {n : N/2 < n ≤ N, ν_n ≡ 0 mod 2}` and `𝒩_o = {n : N/2 < n ≤ N,
ν_n ≡ 1 mod 2}` and states `Σ_{n ∈ 𝒩_e} |R₂(ν_n + 1)|² ≪ N X² ℰ^{-1/3}`, display (29), and
`Σ_{n ∈ 𝒩_o} |R₂(ν_n)|² ≪ N X² ℰ^{-1/3}`, display (30). The paper proves (29) on pages 367 to
369 through Lemma 1 with the kernel `W_e` of (31), the boundary count of Lemma 4, Lemma 9 and
Vinogradov's minor arc bound for `S`, and gets (30) by replacing `W_e(α)` by `W_e(-α)`.

Here both are stated on the lab window `n ≤ 2N` with `X/2 < ν_n ≤ X`, `X = F(N)`, written
literally so that it is definitionally `DecompJ200.window`, which this file cannot import.
That window lies inside the paper's range `N/2 < n ≤ N` once `N ≥ 16`, `Decomp371a`, so with
nonnegative terms each leaf here follows from the paper's display. The endpoint difference is a
QUESTION in research/burst-20261112/ExceptionalSet-leaf_major_odd_moment.md.

`P = X^{6δ}` and `ℰ = exp(κ (log N)^{3-2γ})` as on pages 357 and 359. The paper fixes one `κ`
for sections 4 to 7; the leaves say "there is some `κ₀`" after `δ` is fixed, which is weaker.

AI wrote this Lean code. Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.OddMinorMoments

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE)
open LeanLab.ExceptionalSet.OddSupplyJ200 (R2)

/-- LEAF. P0082 page 367, display (29), proved on pages 367 to 369: the second moment over
`n` with `ν_n` even of the minor arc coefficient `R₂(ν_n + 1)` is `≪ N X² ℰ^{-1/3}`.
The paper sums over `N/2 < n ≤ N`; the sum here is over the lab window `X/2 < ν_n ≤ X`,
`n ≤ 2N`, which is contained in it for `N ≥ 16`. Proved from displays (32) and (33) and the
leaf `Display29Steps.leaf_even_kernel_moment`, CONDITIONAL ON Lemma 4, `U1539.lemma4`. -/
theorem leaf_even_minor_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ ((Finset.range (2 * N + 1)).filter
              (fun n => F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N)).filter
                (fun n => Even (nu γ n)),
            ‖R2 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) :=
  Display29Steps.even_minor_moment_of_steps U1539.lemma4 γ h1 h2

/-- LEAF. P0082 page 367, display (30), proved on page 369 as the cognate of (29) with
`W_e(α)` replaced by `W_e(-α)`: the second moment over `n` with `ν_n` odd of the minor arc
coefficient `R₂(ν_n)` is `≪ N X² ℰ^{-1/3}`. Same window remark as for (29). Proved from the
cognates of (32) and (33) and the leaf `Display29Steps.leaf_odd_kernel_moment`, CONDITIONAL ON
Lemma 4, `U1539.lemma4`. -/
theorem leaf_odd_minor_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ ((Finset.range (2 * N + 1)).filter
              (fun n => F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N)).filter
                (fun n => ¬ Even (nu γ n)),
            ‖R2 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) :=
  Display29Steps.odd_minor_moment_of_steps U1539.lemma4 γ h1 h2

end LeanLab.ExceptionalSet.OddMinorMoments
