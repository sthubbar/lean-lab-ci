import LeanLab.ExceptionalSet.SPLIT_leaf_near_zero_odd_index
import LeanLab.ExceptionalSet.Feed1122_near_zero_even_large_prime_long

/-!
Feed for `leaf_near_zero_odd_large_prime_short` of
`LeanLab.ExceptionalSet.SPLIT_leaf_near_zero_odd_index`.

Paper: Brüdern and Perelli 1998, P0082, Lemma 3 page 358, display 10 page 358 and the proof of
Lemma 7, cases ii b to ii d, pages 363 and 364.

The frequency is the even upper neighbour `nu γ n + 1` of an odd floor value. The argument is
the one of the even feed: the two leaves `leaf_exceptional_main_term_lower`, HARD, and
`leaf_exceptional_zero_page_bound`, MEDIUM, are stated generically in the frequency in
`Feed1122_near_zero_even_large_prime_long`, and the proved helper
`feed1122_large_prime_core` there is applied with `m = nu γ n + 1`. The bound
`r ≤ ℰ^(1/7)` alone suffices, so the position of `r` against `ℰ^(1/14)` is not used.

AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- Assembly, statement copied verbatim from `leaf_near_zero_odd_large_prime_short`. -/
theorem leaf_near_zero_odd_large_prime_short_feed (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p) →
            (r : ℝ) ≤ calE γ κ N ^ (1 / 14 : ℝ) →
            ∀ n ∈ window γ N, ¬ Even (nu γ n) →
              ((nu γ n + 1 : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n + 1) r →
                (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + 1) →
                (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
                c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) := by
  obtain ⟨δ₀, hδ₀, H⟩ := feed1122_large_prime_core γ h1 h2 a ha
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδs
  obtain ⟨c, A, hc, hA, N₀, K⟩ := H δ hδ hδs
  refine ⟨1, one_pos, ?_⟩
  intro κ hκ _
  refine ⟨c, A, hc, hA, N₀, ?_⟩
  intro N hN r hr hrP hsel hbig _ n hn hodd hm hgcd hnop hrE
  have hwin := (Finset.mem_filter.mp hn).2.1
  have heven : Even (nu γ n + 1) := (Int.not_even_iff_odd.mp hodd).add_one
  have hwin' : F γ N / 2 < ((nu γ n + 1 : ℤ) : ℝ) := by push_cast; linarith
  exact K N hN κ hκ r hr hrP hsel (feed1122_ne_one_of_big_prime r hbig) (nu γ n + 1) heven
    hwin' hm hgcd hnop hrE

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
