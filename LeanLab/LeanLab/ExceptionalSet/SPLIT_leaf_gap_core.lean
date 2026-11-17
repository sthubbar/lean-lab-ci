/-
Split of the LEAF statement `leaf_gap_core` of `LeanLab.ExceptionalSet.SPLIT_lemma9`.

`leaf_gap_core_split` below has exactly the type of that statement and is proved here from the
two LEAF inputs of this file, with no gap of its own.  The split is the shape recorded
for this statement: the parity condition is removed by the identity that twice the even
parity projection is the full exponential sum plus the parity signed exponential sum; the
full sum is small as soon as `α` is not trapped at the origin; and the parity signed sum,
the truncated Fourier expansion step, can only be large within `F γ N ^ (δ - 1)` of a
half-integer.  The case `|α| ≤ F γ N ^ (δ - 1)` needs no analysis at all, the integer zero
already being the required half-integer multiple, and the parameter bookkeeping is carried
out in the assembly below.

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_lemma9

namespace LeanLab.ExceptionalSet.U1539

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### The parity identity -/

/-- Twice the even parity projection is the full exponential sum plus the parity signed
exponential sum.  This is the exact parity filter before smoothing: a pointwise parity
split, proved in full here, and not an analytic estimate. -/
private theorem two_mul_phie_eq (γ : ℝ) (N : ℕ) (α : ℝ) :
    2 * Phie γ N α =
      (∑ n ∈ Finset.Ioc (N / 2) N, eC (α * F γ n)) +
        ∑ n ∈ Finset.Ioc (N / 2) N, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n) := by
  classical
  rw [Phie, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [neg_one_zpow_eq_ite]
  split_ifs <;> ring

/-! ### The two leaf estimates -/

/-- LEAF 1 of the split of `leaf_gap_core`: the full exponential sum is small once `α` is
away from the origin.  For `1 < γ < 3/2` and `0 < δ < 1`, if `F γ N ^ (δ - 1) < |α|` and
`|α| ≤ F γ N ^ δ` then the full sum `Σ_{N/2 < n ≤ N} e(α F(n))` is at most one eighth of
`N ℰ ^ (-1/3)`, uniformly in every sufficiently small `κ`.  This is the exponential sum
estimate away from the major arc at the origin; it carries no parity condition at all. -/
theorem leaf_full_sum_minor_arc (γ δ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ,
        F γ N ^ (δ - 1) < |α| → |α| ≤ F γ N ^ δ →
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (α * F γ n)‖
          ≤ (N : ℝ) * calE γ κ N ^ (-(1 / 3 : ℝ)) / 8 := by
  sorry

/-- LEAF 2 of the split of `leaf_gap_core`: the parity signed sum localizes at the
half-integers.  For `1 < γ < 3/2` and `0 < δ < 1`, a value of the parity signed sum
`Σ_{N/2 < n ≤ N} (-1)^{ν_n} e(α F(n))` above the `N ℰ ^ (-1/3)` threshold, with
`|α| ≤ F γ N ^ δ`, forces `α` to lie within `F γ N ^ (δ - 1)` of a half-integer `h/2`,
uniformly in every sufficiently small `κ`.  This is the truncated Fourier expansion step:
the frequencies of the even parity projection sit at the translates `α + h/2`, and only a
translate carrying a half-integer can hold mass at this height. -/
theorem leaf_signed_sum_localizes (γ δ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ,
        |α| ≤ F γ N ^ δ →
          N * calE γ κ N ^ (-(1 / 3 : ℝ))
              < ‖∑ n ∈ Finset.Ioc (N / 2) N, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)‖ →
        ∃ h : ℤ, |α - h / 2| ≤ F γ N ^ (δ - 1) := by
  sorry

/-! ### Assembly -/

/-- `leaf_gap_core` from the two leaves and the parity identity. -/
theorem leaf_gap_core_split :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ,
        |α| ≤ F γ N ^ δ → N * calE γ κ N ^ (-(1 / 3 : ℝ)) < ‖Phie γ N α‖ →
        ∃ h : ℤ, |α - h / 2| ≤ F γ N ^ (δ - 1) := by
  intro γ hγ₁ hγ₂
  refine ⟨1, one_pos, ?_⟩
  intro δ hδpos hδ₁
  obtain ⟨κ₁, hκ₁pos, hunif₁⟩ := leaf_full_sum_minor_arc γ δ hγ₁ hγ₂ hδpos hδ₁
  obtain ⟨κ₂, hκ₂pos, hunif₂⟩ := leaf_signed_sum_localizes γ δ hγ₁ hγ₂ hδpos hδ₁
  have hκpos : 0 < min κ₁ κ₂ := lt_min hκ₁pos hκ₂pos
  obtain ⟨N₁, hN₁⟩ := hunif₁ (min κ₁ κ₂) hκpos (min_le_left κ₁ κ₂)
  obtain ⟨N₂, hN₂⟩ := hunif₂ (min κ₁ κ₂) hκpos (min_le_right κ₁ κ₂)
  refine ⟨min κ₁ κ₂, hκpos, max (max N₁ N₂) 1, ?_⟩
  intro N hN α hα hlarge
  have hN₁' : N₁ ≤ N := le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ 1)) hN
  have hN₂' : N₂ ≤ N := le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ 1)) hN
  by_cases hnear : ∃ h : ℤ, |α - h / 2| ≤ F γ N ^ (δ - 1)
  · exact hnear
  · exfalso
    have hgap : ∀ h : ℤ, F γ N ^ (δ - 1) < |α - h / 2| := by
      intro h
      by_contra hcon
      exact hnear ⟨h, le_of_not_gt hcon⟩
    have hS₀ : ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (α * F γ n)‖
        ≤ (N : ℝ) * calE γ (min κ₁ κ₂) N ^ (-(1 / 3 : ℝ)) / 8 :=
      hN₁ N hN₁' α (by simpa using hgap 0) hα
    have htri : 2 * ‖Phie γ N α‖
        ≤ ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (α * F γ n)‖
          + ‖∑ n ∈ Finset.Ioc (N / 2) N, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)‖ := by
      have h2 : 2 * ‖Phie γ N α‖ = ‖(2 : ℂ) * Phie γ N α‖ := by
        rw [norm_mul, Complex.norm_ofNat]
      rw [h2, two_mul_phie_eq]
      exact norm_add_le _ _
    have hS₁ : N * calE γ (min κ₁ κ₂) N ^ (-(1 / 3 : ℝ))
        < ‖∑ n ∈ Finset.Ioc (N / 2) N, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)‖ := by
      have hN1 : (0 : ℝ) < (N : ℝ) := by
        have h1N : 1 ≤ N := le_trans (le_max_right _ 1) hN
        exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one h1N
      have hEc : 0 < calE γ (min κ₁ κ₂) N := by
        rw [calE]
        exact Real.exp_pos _
      have hTpos : 0 < (N : ℝ) * calE γ (min κ₁ κ₂) N ^ (-(1 / 3 : ℝ)) :=
        mul_pos hN1 (Real.rpow_pos_of_pos hEc _)
      linarith
    exact hnear (hN₂ N hN₂' α hα hS₁)

end LeanLab.ExceptionalSet.U1539
