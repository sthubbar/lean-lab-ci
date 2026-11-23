import LeanLab.ExceptionalSet.SPLIT_leaf_coprime_even_index
import LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelectedDecisions
import LeanLab.ExceptionalSet.Prep1121SingSeries
import LeanLab.ExceptionalSet.RealZeroLower672

/-!
Split of `leaf_even_index_coefficient_domination` of
`LeanLab.ExceptionalSet.SPLIT_leaf_coprime_even_index`, burst-20261122 feed1122, session S89.
Source P0082, Brudern and Perelli 1998, Ann. Inst. Fourier 48, pages 358 to 363.

The statement asks for a lower bound `c ν_n ≤ re R₁(ν_n)` at an even floor value of the window,
for a selected conductor `r ≠ 1` coprime to `ν_n`, with no additive divisor error.

The proof runs through the proved conditional assembly
`DQLeafCoprimeSelected.leaf_coprime_selected_of_hyps`, which is page 363 case ii a: from the
three cited inputs it gives `c X ≤ re R₁(m) + A X Γ(m)` with `Γ = divisorError` the envelope of
displays 14 and 15. The leaves are those three cited inputs plus one estimate that removes the
envelope pointwise:

* `leaf_even_bp_lemma3`, page 358 Lemma 3, Montgomery and Vaughan 1975 formula 6.17, HARD.
* `leaf_even_sing_series_lower`, page 362 case i, the singular series is at least a constant
  times `m / φ(m)` for even `m`, PROVED from `Prep1121SingSeries`.
* `leaf_even_landau_real_zero`, page 358 display 10, Davenport chapter 14, PROVED from `RealZeroLower672`.
* `leaf_even_divisor_error_vanishes`, the envelopes of displays 14 and 15 tend to zero
  uniformly for `X/2 < m ≤ X` coprime to `r`, since the divisor function of `m` is `X^{o(1)}`
  while `P = X^{6δ}`, HARD.

The assembly is proved: the envelope is at most `c / (2A)` for large `N`, so
`(c/2) X ≤ re R₁(ν_n)`, and `ν_n ≤ X` gives `(c/2) ν_n ≤ re R₁(ν_n)`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected
  (BPLemma3CoprimeHyp SingSeriesLowerHyp LandauRealZeroHyp leaf_coprime_selected_of_hyps)

/-- LEAF: P0082 page 358 Lemma 3, which is Montgomery and Vaughan 1975 formula 6.17 with the
error of 6.19 kept explicit, specialised to an even frequency coprime to the exceptional modulus
as on page 363 case ii a, in the form of the reviewed named hypothesis `BPLemma3CoprimeHyp`.
HARD: a real analytic step, the major arc evaluation with an exceptional zero. -/
theorem leaf_even_bp_lemma3 : BPLemma3CoprimeHyp := by
  sorry

/-- P0082 page 362 case i, the singular series of display 11 is at least a constant times
`m / φ(m)` for even `m ≥ 1`, in the form of the named hypothesis `SingSeriesLowerHyp`.
PROVED: it is `Prep1121SingSeries.singSeriesLowerHyp_split` on main, closed with no open
input. Burst S89 review replaced the earlier open leaf here by that proved theorem. -/
theorem leaf_even_sing_series_lower : SingSeriesLowerHyp :=
  LeanLab.ExceptionalSet.UpJ200.Prep1121SingSeries.singSeriesLowerHyp_split

/-- P0082 page 358 display 10, left inequality, Davenport, Multiplicative Number Theory,
chapter 14: a real zero `β < 1` of a real nonprincipal primitive character modulo `r` has
`1 - β ≫ r^{-1/2} (log r)^{-2}`, the named hypothesis `LandauRealZeroHyp`. PROVED: it is
`Task672.landauRealZeroHyp_proved672` on main. Burst S89 review replaced the earlier open leaf
here by that proved theorem. -/
theorem leaf_even_landau_real_zero : LandauRealZeroHyp :=
  LeanLab.ExceptionalSet.Task672.landauRealZeroHyp_proved672

/-- LEAF: P0082 page 359 displays 14 and 15, the envelopes `Γ₁ + Γ₂ = divisorError` are
`o(1)` uniformly over `X/2 < m ≤ X` coprime to `r` and `1 ≤ r ≤ P = X^{6δ}`. Writing `q = r k`
the first envelope is at most `τ(m) (log log P)^2 log P / P` and the second at most
`τ(m) (log log P)^3 / P`, and `τ(m) = X^{o(1)}`. HARD: a divisor sum estimate with the
divisor bound. -/
theorem leaf_even_divisor_error_vanishes (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∀ η : ℝ, 0 < η → ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
      ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
        ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
          ∀ m : ℤ, F γ N / 2 < (m : ℝ) → (m : ℝ) ≤ F γ N → Int.gcd m r = 1 →
            divisorError r (F γ N ^ (6 * δ)) m ≤ η := by
  sorry

/-- Assembly of `leaf_even_index_coefficient_domination` from the three cited inputs through the
proved case ii a assembly, and the vanishing of the envelope. -/
theorem leaf_even_index_coefficient_domination_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
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
  obtain ⟨N₁, hD⟩ := leaf_even_divisor_error_vanishes γ h1 h2 (c / (2 * A)) (by positivity)
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
