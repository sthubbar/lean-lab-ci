/-
P0057 J. Kim, arXiv 2412.19975 v1, Section 1.3: the main term M*(2n) for 2n in (X, X + H].
`KimMainTerm.lean` proves the upper bound `M*(m) ≤ X + H + 1 - m` and `M*(X + H) = 1`.
Here the matching lower bound, so `M*(m) = X + H + 1 - m` exactly for `X < m ≤ X + H`, `H ≤ X`.
Consequence: `M*(m) ≥ H / 2` exactly on the lower half `m ≤ X + H/2 + 1`, and `M*(m)` drops
linearly to `1` at the top. So `M*(2n) ≍ H` holds uniformly on `(X, X + (1 - δ) H]` for every
fixed `δ > 0`, with constant `δ`, and fails only in the top `δ H`. This settles the open part
of the PROGRESS question for the main term counting factor; the singular series factor is not
treated.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.MissingDigit.KimMainTerm

namespace LeanLab.MissingDigit

open Finset

/-- Lower bound: for `X < m`, `H ≤ X`, `M*(m) ≥ X + H + 1 - m`. -/
theorem Mstar_ge {X H m : ℕ} (hm : X < m) (hHX : H ≤ X) : X + H + 1 - m ≤ Mstar X H m := by
  unfold Mstar
  have hsub : (Icc (m - X) H).image (fun k => (m - k, k)) ⊆
      ((Ioc (X - H) X ×ˢ Ioc 0 H).filter (fun p => p.1 + p.2 = m)) := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rw [Finset.mem_Icc] at hk
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ioc]
    omega
  have hinj : Set.InjOn (fun k => (m - k, k)) ↑(Icc (m - X) H) := by
    intro a _ b _ h
    exact congrArg Prod.snd h
  calc X + H + 1 - m ≤ H + 1 - (m - X) := by omega
    _ = (Icc (m - X) H).card := (Nat.card_Icc _ _).symm
    _ = ((Icc (m - X) H).image (fun k => (m - k, k))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Exact value: `M*(m) = X + H + 1 - m` for `X < m` and `H ≤ X`. -/
theorem Mstar_eq {X H m : ℕ} (hm : X < m) (hHX : H ≤ X) : Mstar X H m = X + H + 1 - m :=
  le_antisymm (Mstar_le hm) (Mstar_ge hm hHX)

/-- Uniform lower bound away from the top: if `X < m` and `m + d ≤ X + H + 1`, then
`M*(m) ≥ d`. With `d = ⌈δ H⌉` this is `M*(m) ≥ δ H` on `(X, X + (1 - δ) H]`. -/
theorem Mstar_ge_of_gap {X H m d : ℕ} (hm : X < m) (hHX : H ≤ X) (hd : m + d ≤ X + H + 1) :
    d ≤ Mstar X H m := by
  rw [Mstar_eq hm hHX]; omega

/-- The real form of the uniform bound on `(X, X + (1 - δ) H]`, for `δ ≥ 0`. -/
theorem Mstar_ge_delta {X H m : ℕ} (hm : X < m) (hHX : H ≤ X) {δ : ℝ} (hδ : 0 ≤ δ)
    (htop : (m : ℝ) ≤ X + (1 - δ) * H) : δ * H ≤ Mstar X H m := by
  rw [Mstar_eq hm hHX]
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have h1 : m ≤ X + H + 1 := by
    have : (m : ℝ) ≤ X + H + 1 := by nlinarith
    exact_mod_cast this
  rw [Nat.cast_sub h1]
  push_cast
  linarith

/-- And the converse at the top: if `m > X + (1 - δ) H` then `M*(m) < δ H + 1`. -/
theorem Mstar_lt_delta {X H m : ℕ} (hm : X < m) (hHX : H ≤ X) {δ : ℝ} (hδ : 0 ≤ δ)
    (htop : (X : ℝ) + (1 - δ) * H < m) : (Mstar X H m : ℝ) < δ * H + 1 := by
  rw [Mstar_eq hm hHX]
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  rcases le_or_gt m (X + H + 1) with h1 | h1
  · rw [Nat.cast_sub h1]; push_cast; linarith
  · rw [Nat.sub_eq_zero_of_le h1.le]
    push_cast
    nlinarith

/-- Kernel check of the formula: `X = 100`, `H = 10`, `m = 105` gives `M* = 6`. -/
theorem Mstar_100_10_105 : Mstar 100 10 105 = 6 := by decide +kernel

end LeanLab.MissingDigit
