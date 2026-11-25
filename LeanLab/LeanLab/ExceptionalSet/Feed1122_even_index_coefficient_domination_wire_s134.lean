import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_even_divisor_error_vanishes

/-!
Feed 1122, CLOUD S134: downstream wiring of the case ii a assembly of P0082 page 363.
`leaf_even_divisor_error_vanishes` of `SPLIT_feed1122_leaf_even_index_coefficient_domination.lean`,
P0082 page 359 displays 14 and 15, cannot be closed in its own file, since the file that proves
it, `SPLIT_feed1122_leaf_even_divisor_error_vanishes.lean`, imports that file.  Here the assembly
`leaf_even_index_coefficient_domination_split` is repeated verbatim with the PROVED
`leaf_even_divisor_error_vanishes_split` in place of the envelope leaf, so the case ii a lower bound
rests on the single LEAF `leaf_even_bp_lemma3`, P0082 Lemma 3.

AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected

/-- Statement of `leaf_even_index_coefficient_domination_split`, with the envelope leaf replaced by
the PROVED `leaf_even_divisor_error_vanishes_split`, so CONDITIONAL ON `leaf_even_bp_lemma3` only. -/
theorem leaf_even_index_coefficient_domination_s134 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              r ≠ 1 → Int.gcd (nu γ n) r = 1 →
                c * ((nu γ n : ℤ) : ℝ) ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re := by
  obtain ⟨δ₀, hδ₀, H⟩ := leaf_coprime_selected_of_hyps leaf_even_bp_lemma3
    leaf_even_sing_series_lower leaf_even_landau_real_zero γ h1 h2 a ha
  refine ⟨min δ₀ (1 / 100), lt_min hδ₀ (by norm_num), ?_⟩
  intro δ hδ hδs
  obtain ⟨κ₀, hκ₀, H⟩ := H δ hδ (lt_of_lt_of_le hδs (min_le_left _ _))
  refine ⟨κ₀, hκ₀, ?_⟩
  intro κ hκ hκs
  obtain ⟨c, A, hc, hA, N₀, H⟩ := H κ hκ hκs
  obtain ⟨N₁, hD⟩ := leaf_even_divisor_error_vanishes_split γ h1 h2 (c / (2 * A)) (by positivity)
    δ hδ (lt_of_lt_of_le hδs (min_le_right _ _))
  refine ⟨c / 2, by positivity, max N₀ N₁, ?_⟩
  intro N hN r hr hrP hs n hn heven hm hr1 hgcd
  obtain ⟨hN0, hN1⟩ := max_le_iff.mp hN
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  have hmain := H N hN0 r hr hrP hs 0 (Or.inl rfl) n hn (by simpa using heven)
    (by simpa using hm) hr1 (by simpa using hgcd)
  simp only [add_zero] at hmain
  have hwin : F γ N / 2 < ((nu γ n : ℤ) : ℝ) := by
    rw [window, Finset.mem_filter] at hn
    exact hn.2.1
  have hdiv : divisorError r (F γ N ^ (6 * δ)) (nu γ n) ≤ c / (2 * A) :=
    hD N hN1 r hr hrP (nu γ n) hwin hm hgcd
  have hAX : A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) ≤ c / 2 * F γ N := by
    have h' : A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) ≤
        A * F γ N * (c / (2 * A)) :=
      mul_le_mul_of_nonneg_left hdiv (mul_nonneg hA.le hX)
    have h'' : A * F γ N * (c / (2 * A)) = c / 2 * F γ N := by
      field_simp
    linarith
  have hν : c / 2 * ((nu γ n : ℤ) : ℝ) ≤ c / 2 * F γ N :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  linarith

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
