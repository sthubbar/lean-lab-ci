import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_coprime_odd_low_half

/-!
Split of `leaf_coprime_odd_high_large_conductor` of `LeanLab.ExceptionalSet.SPLIT_leaf_coprime_odd_index`,
burst-20261122 feed1122, session S89. Source P0082, Brudern and Perelli 1998, page 363 case ii a.

No new leaf: the statement is `coprime_odd_full_feed1122` of
`SPLIT_feed1122_leaf_coprime_odd_low_half` with the range and conductor hypotheses unused, so
it rests on the four leaves of `SPLIT_feed1122_leaf_even_index_coefficient_domination`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- Assembly of `leaf_coprime_odd_high_large_conductor`: the whole odd statement with the range and conductor hypotheses
unused. No sorry in this file. -/
theorem leaf_coprime_odd_high_large_conductor_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, ¬ Even (nu γ n) →
              ((nu γ n + 1 : ℤ) : ℝ) ≤ F γ N →
              r ≠ 1 → Int.gcd (nu γ n + 1) r = 1 →
                3 * F γ N < 4 * ((nu γ n + 1 : ℤ) : ℝ) →
                  F γ N ^ (3 * δ) < (r : ℝ) →
                  c * F γ N ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re := by
  obtain ⟨δ₀, hδ₀, H⟩ := coprime_odd_full_feed1122 γ h1 h2 a ha
  refine ⟨δ₀, hδ₀, fun δ hδ hδs => ?_⟩
  obtain ⟨κ₀, hκ₀, H⟩ := H δ hδ hδs
  refine ⟨κ₀, hκ₀, fun κ hκ hκs => ?_⟩
  obtain ⟨c, hc, N₀, H⟩ := H κ hκ hκs
  exact ⟨c, hc, N₀, fun N hN r hr hrP hs n hn hodd hm hr1 hgcd _ _ =>
    H N hN r hr hrP hs n hn hodd hm hr1 hgcd⟩

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
