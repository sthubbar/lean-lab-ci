import Mathlib
import LeanLab.ExceptionalSet.State1539Data264

/-!
The odd cognate of Lemma 9 of P0082, J. Bruedern and A. Perelli, Goldbach numbers in sparse
sequences, Ann. Inst. Fourier 48 (1998) 353-378, https://doi.org/10.5802/aif.1621.

Page 369, after display (39): "To deduce (30) one merely has to replace `w_e(α)` with
`w_o(α) = w_e(-α)` in the above argument." That argument uses Lemma 9 for the sum `Φ_e` of
display (36); for display (30) it needs the same statement for
`Φ_o(α) = Σ_{N/2 < n ≤ N, ν_n odd} e(αF(n))`. The paper states Lemma 9 for `Φ_e` only and
proves it in its section 7, pages 369 and 370, by removing the parity condition with the
Fourier technique of display (41): `ν_n` is even iff `{F(n)/2} ≤ 1/2`, and the indicator is
smoothed by `ψ(α) = Σ_k w_e(k - 2α) = Σ_h c_h e(hα)` with `c_h ≪ min(1, Δ^{-1} h^{-2})`.
For the odd class one uses `ψ(α - 1/2)`, whose coefficients are `c_h e(-h/2) = (-1)^h c_h`,
of the same size, so (41) holds with `Φ_o` and the rest of section 7, Theorem 2 away from
`α + h/2`, is unchanged. The statement below is the exact shape of `U1539.Lemma9` with `Φ_e`
replaced by `Φ_o`.

A numerical sanity check is recorded in
`research/burst-20261112/ExceptionalSet-leaf_odd_kernel_moment.md`.

AI wrote this Lean code. Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.Lemma9Odd

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (eC nu calE)

/-- `Φ_o(α) = Σ_{N/2 < n ≤ N, ν_n odd} e(αF(n))`, the odd cognate of `U1539.Phie`, display (36)
of P0082 page 368 with the parity reversed, as page 369 needs for display (30). -/
noncomputable def Phio (γ : ℝ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => ¬ Even (nu γ n)), eC (α * F γ n)

/-- Lemma 9 of P0082 page 368 for `Φ_o` in place of `Φ_e`: the exact shape of `U1539.Lemma9`
with `Phie` replaced by `Phio`. -/
def Lemma9odd : Prop :=
  ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ, |α| ≤ F γ N ^ δ →
      N * calE γ κ N ^ (-(1 / 3 : ℝ)) < ‖Phio γ N α‖ →
      ∃ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (2 / 3 : ℝ) ∧ |α - h / 2| ≤ F γ N ^ (δ - 1)

/-- LEAF. Lemma 9 of P0082 for the odd class, used on page 369 for display (30):
"To deduce (30) one merely has to replace `w_e(α)` with `w_o(α) = w_e(-α)`". The paper's
section 7 proof, pages 369 and 370, removes the parity condition `ν_n ≡ 0 (mod 2)` by a Fourier
technique, display (41), that works for either residue class: for `ν_n` odd use `ψ(α - 1/2)`,
whose Fourier coefficients `(-1)^h c_h` obey the same bound (40). Then Theorem 2 bounds
`Φ(α + h/2)` unless `α` is within `X^{δ-1}` of some `-h/2`, `|h| ≤ ℰ^{2/3}`.
Open, the odd cognate of the open statement `U1539.lemma9`. -/
theorem lemma9_odd : Lemma9odd := by
  sorry

end LeanLab.ExceptionalSet.Lemma9Odd
