import LeanLab.ExceptionalSet.DecompF1253
import LeanLab.ExceptionalSet.SPLIT_leaf_coprime_odd_index

/-!
Wiring of `leaf_coprime_F1253_odd` of `LeanLab.ExceptionalSet.DecompF1253`, burst-20261122
feed1122, session S89. Source P0082, Brudern and Perelli 1998, page 363 case ii a.

`leaf_coprime_F1253_odd` is verbatim the statement of `leaf_coprime_odd_index` of
`SPLIT_leaf_coprime_selected`, which `SPLIT_leaf_coprime_odd_index` already splits in `leaf_coprime_odd_index_split`. The duplicate is
derived from that split with no new sorry.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

/-- Assembly of `leaf_coprime_F1253_odd` from the existing split `leaf_coprime_odd_index_split`. No sorry in this
file. -/
theorem leaf_coprime_F1253_odd_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, ¬ Even (nu γ n) →
              ((nu γ n + 1 : ℤ) : ℝ) ≤ F γ N →
              r ≠ 1 → Int.gcd (nu γ n + 1) r = 1 →
                c * F γ N ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re := by
  exact leaf_coprime_odd_index_split γ h1 h2 a ha

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
