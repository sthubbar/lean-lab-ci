import LeanLab.ExceptionalSet.SPLIT_leaf_coprime_selected

/-!
Split of `leaf_coprime_odd_index` of `LeanLab.ExceptionalSet.SPLIT_leaf_coprime_selected`.

The statement being split asks, for `1 < γ < 3/2` and `a > 0`, for a positive cap on the
truncation parameter, a positive cap on the height parameter, a positive constant `c` and a
threshold `N₀`, such that for every admissible truncation, every `N ≥ N₀`, every conductor `r ≥ 2`
selected by `SelectedRealZero`, every index `n` of the floor window whose floor value `ν_n` is odd
and whose upper neighbour `ν_n + 1` is at most `F γ N`, provided `ν_n + 1` is coprime to `r`, the
real part of the major arc integral at that upper neighbour dominates `c F γ N`. There is no
additive error term: the claim is pointwise in `n`, with the conductor entering only through the
hypotheses, since `R1` carries no conductor.

The window places the floor value in `F γ N / 2 < ν_n ≤ F γ N`, so the frequency `ν_n + 1` sits in
`F γ N / 2 + 1 < ν_n + 1 ≤ F γ N + 1`. One set of uniform constants cannot serve the whole range:
the main term of a major arc integral is thinnest next to the top of the range, while the arc error
is largest next to the bottom. The first two leaves split that range at three quarters of `F γ N`,
so each of them says nothing about the frequency on the other side of the cut and each is strictly
easier than the whole statement. They also ignore the conductor altogether.

The upper half is cut once more, by the size of the selected conductor against the square root of
the truncation: the third leaf names only conductors at most `F γ N ^ (3 * δ)`, and the fourth only
conductors above it. A selected conductor is known to be at most the truncation `F γ N ^ (6 * δ)`
and to be large in absolute terms, so the two regimes are genuinely different: a conductor below the
square root of the truncation is reached by the truncated arc sums, a conductor above it only by the
tail beyond the truncation. Neither leaf carries the other regime.

The assembly is the two dichotomies. It takes the smallest of the four lower constants, the largest
of the four thresholds, decides the half of the range from the frequency, and inside the upper half
decides the regime from the conductor. Every step of the assembly is proved; only the four pieces
are left open. Nothing here asserts the parity dichotomy or a shift parameter: the index is already
odd and the frequency is already its upper neighbour.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- LEAF. Lower half of the frequency range, every selected conductor. At an odd floor value
`ν_n` of the window whose upper neighbour is at most three quarters of `F γ N`, the real part of the
major arc integral at `ν_n + 1` dominates `c F γ N` for every conductor `r ≥ 2` selected by
`SelectedRealZero` and coprime to the frequency, with constants chosen for that half of the range
alone. The statement says nothing about a frequency above `3 F γ N / 4`. -/
theorem leaf_coprime_odd_low_half (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
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
  sorry

/-- LEAF. Upper half of the frequency range, small selected conductor. At an odd floor value `ν_n`
of the window whose upper neighbour is larger than three quarters of `F γ N`, and for a conductor
`r ≥ 2` selected by `SelectedRealZero` that is coprime to the frequency and at most the square root
`F γ N ^ (3 * δ)` of the truncation, the real part of the major arc integral at `ν_n + 1` dominates
`c F γ N`, with constants chosen for this regime alone. The statement says nothing about a
frequency at or below `3 F γ N / 4`, and nothing about a conductor above `F γ N ^ (3 * δ)`. -/
theorem leaf_coprime_odd_high_small_conductor (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
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
                  (r : ℝ) ≤ F γ N ^ (3 * δ) →
                  c * F γ N ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re := by
  sorry

/-- LEAF. Upper half of the frequency range, large selected conductor. At an odd floor value `ν_n`
of the window whose upper neighbour is larger than three quarters of `F γ N`, and for a conductor
`r ≥ 2` selected by `SelectedRealZero` that is coprime to the frequency and exceeds the square root
`F γ N ^ (3 * δ)` of the truncation, the real part of the major arc integral at `ν_n + 1` dominates
`c F γ N`, with constants chosen for this regime alone. The statement says nothing about a
frequency at or below `3 F γ N / 4`, and nothing about a conductor at most `F γ N ^ (3 * δ)`. -/
theorem leaf_coprime_odd_high_large_conductor (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
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
  sorry

/-- Assembly of `leaf_coprime_odd_index`: the frequency decides the half of the range, the size of
the selected conductor decides the regime inside the upper half, and the constants are minimised
and the thresholds maximised. -/
theorem leaf_coprime_odd_index_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
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
  obtain ⟨δl, hδl, hL⟩ := leaf_coprime_odd_low_half γ h1 h2 a ha
  obtain ⟨δs, hδs, hS⟩ := leaf_coprime_odd_high_small_conductor γ h1 h2 a ha
  obtain ⟨δg, hδg, hG⟩ := leaf_coprime_odd_high_large_conductor γ h1 h2 a ha
  refine ⟨min δl (min δs δg), lt_min hδl (lt_min hδs hδg), ?_⟩
  intro δ hδ hδsmall
  obtain ⟨hδl', hδrest⟩ := lt_min_iff.mp hδsmall
  obtain ⟨hδs', hδg'⟩ := lt_min_iff.mp hδrest
  obtain ⟨κl, hκl, hL⟩ := hL δ hδ hδl'
  obtain ⟨κs, hκs, hS⟩ := hS δ hδ hδs'
  obtain ⟨κg, hκg, hG⟩ := hG δ hδ hδg'
  refine ⟨min κl (min κs κg), lt_min hκl (lt_min hκs hκg), ?_⟩
  intro κ hκ hκsmall
  obtain ⟨hκl', hκrest⟩ := le_min_iff.mp hκsmall
  obtain ⟨hκs', hκg'⟩ := le_min_iff.mp hκrest
  obtain ⟨cl, hcl, Nl, hL⟩ := hL κ hκ hκl'
  obtain ⟨cs, hcs, Ns, hS⟩ := hS κ hκ hκs'
  obtain ⟨cg, hcg, Ng, hG⟩ := hG κ hκ hκg'
  refine ⟨min cl (min cs cg), lt_min hcl (lt_min hcs hcg), max Nl (max Ns Ng), ?_⟩
  intro N hN r hr hrP hsel n hn hodd hm hr1 hgcd
  obtain ⟨hNl, hNrest⟩ := max_le_iff.mp hN
  obtain ⟨hNs, hNg⟩ := max_le_iff.mp hNrest
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  by_cases hlow : 4 * ((nu γ n + 1 : ℤ) : ℝ) ≤ 3 * F γ N
  · have h := hL N hNl r hr hrP hsel n hn hodd hm hr1 hgcd hlow
    exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hX) h
  · have hhigh : 3 * F γ N < 4 * ((nu γ n + 1 : ℤ) : ℝ) := not_le.mp hlow
    by_cases hsmall : (r : ℝ) ≤ F γ N ^ (3 * δ)
    · have h := hS N hNs r hr hrP hsel n hn hodd hm hr1 hgcd hhigh hsmall
      refine le_trans (mul_le_mul_of_nonneg_right ?_ hX) h
      exact (min_le_right _ _).trans (min_le_left _ _)
    · have hlarge : F γ N ^ (3 * δ) < (r : ℝ) := not_le.mp hsmall
      have h := hG N hNg r hr hrP hsel n hn hodd hm hr1 hgcd hhigh hlarge
      refine le_trans (mul_le_mul_of_nonneg_right ?_ hX) h
      exact (min_le_right _ _).trans (min_le_right _ _)


end LeanLab.ExceptionalSet.UpJ200.Decomp559b
