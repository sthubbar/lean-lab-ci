import LeanLab.ExceptionalSet.SPLIT_leaf_coprime_odd_index
import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_even_index_coefficient_domination

/-!
Split of `leaf_coprime_odd_low_half` of `LeanLab.ExceptionalSet.SPLIT_leaf_coprime_odd_index`,
burst-20261122 feed1122, session S89. Source P0082, Brudern and Perelli 1998, page 363 case ii a.

No new leaf. The four leaves of `SPLIT_feed1122_leaf_even_index_coefficient_domination`, the
three cited inputs of page 358 and page 362 and the vanishing of the envelopes of displays 14
and 15, feed the proved conditional assembly `leaf_coprime_selected_of_hyps` at the shift
`j = 1`. That gives the whole odd frequency statement `coprime_odd_full_feed1122` on every
frequency of the window, and each of the three range pieces of
`SPLIT_leaf_coprime_odd_index` is that statement with one or two extra hypotheses unused.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected (leaf_coprime_selected_of_hyps)

/-- The whole odd frequency coprime statement, the statement of `leaf_coprime_odd_index`, from
the four leaves of the even feed1122 split through the proved case ii a assembly at `j = 1`. -/
theorem coprime_odd_full_feed1122 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
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
  obtain ⟨δ₀, hδ₀, H⟩ := leaf_coprime_selected_of_hyps leaf_even_bp_lemma3
    leaf_even_sing_series_lower leaf_even_landau_real_zero γ h1 h2 a ha
  refine ⟨min δ₀ (1 / 100), lt_min hδ₀ (by norm_num), ?_⟩
  intro δ hδ hδs
  obtain ⟨κ₀, hκ₀, H⟩ := H δ hδ (lt_of_lt_of_le hδs (min_le_left _ _))
  refine ⟨κ₀, hκ₀, ?_⟩
  intro κ hκ hκs
  obtain ⟨c, A, hc, hA, N₀, H⟩ := H κ hκ hκs
  obtain ⟨N₁, hD⟩ := leaf_even_divisor_error_vanishes γ h1 h2 (c / (2 * A)) (by positivity)
    δ hδ (lt_of_lt_of_le hδs (min_le_right _ _))
  refine ⟨c / 2, by positivity, max N₀ N₁, ?_⟩
  intro N hN r hr hrP hs n hn hodd hm hr1 hgcd
  obtain ⟨hN0, hN1⟩ := max_le_iff.mp hN
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  have hev : Even (nu γ n + 1) := Int.even_add_one.mpr hodd
  have hmain := H N hN0 r hr hrP hs 1 (Or.inr rfl) n hn hev hm hr1 hgcd
  have hwin : F γ N / 2 < ((nu γ n : ℤ) : ℝ) := by
    rw [window, Finset.mem_filter] at hn
    exact hn.2.1
  have hwin' : F γ N / 2 < ((nu γ n + 1 : ℤ) : ℝ) := by
    push_cast
    linarith
  have hdiv : divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) ≤ c / (2 * A) :=
    hD N hN1 r hr hrP (nu γ n + 1) hwin' hm hgcd
  have hAX : A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) ≤ c / 2 * F γ N := by
    have h' : A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) ≤
        A * F γ N * (c / (2 * A)) :=
      mul_le_mul_of_nonneg_left hdiv (mul_nonneg hA.le hX)
    have h'' : A * F γ N * (c / (2 * A)) = c / 2 * F γ N := by
      field_simp
    linarith
  linarith

/-- Assembly of `leaf_coprime_odd_low_half`: the whole odd statement with the range hypothesis
unused. No sorry in this file. -/
theorem leaf_coprime_odd_low_half_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, ¬ Even (nu γ n) →
              ((nu γ n + 1 : ℤ) : ℝ) ≤ F γ N →
              r ≠ 1 → Int.gcd (nu γ n + 1) r = 1 →
                4 * ((nu γ n + 1 : ℤ) : ℝ) ≤ 3 * F γ N →
                  c * F γ N ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re := by
  obtain ⟨δ₀, hδ₀, H⟩ := coprime_odd_full_feed1122 γ h1 h2 a ha
  refine ⟨δ₀, hδ₀, fun δ hδ hδs => ?_⟩
  obtain ⟨κ₀, hκ₀, H⟩ := H δ hδ hδs
  refine ⟨κ₀, hκ₀, fun κ hκ hκs => ?_⟩
  obtain ⟨c, hc, N₀, H⟩ := H κ hκ hκs
  exact ⟨c, hc, N₀, fun N hN r hr hrP hs n hn hodd hm hr1 hgcd _ =>
    H N hN r hr hrP hs n hn hodd hm hr1 hgcd⟩

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
