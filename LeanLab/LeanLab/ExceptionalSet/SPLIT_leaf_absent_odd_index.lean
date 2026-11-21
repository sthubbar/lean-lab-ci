import LeanLab.ExceptionalSet.SPLIT_leaf_absent_selected

/-!
Split of `leaf_absent_odd_index` of `LeanLab.ExceptionalSet.SPLIT_leaf_absent_selected`.

The statement being split asks, for `1 < γ < 3/2` and `a > 0`, for a positive cap on the
truncation parameter, a positive cap on the height parameter, positive constants `c` and `A` and a
threshold `N₀`, such that for every admissible truncation, every `N ≥ N₀`, every conductor selected
by `SelectedRealZero` which equals one, and every index `n` of the floor window whose floor value
`ν_n` is odd and whose upper neighbour `ν_n + 1` is at most `F γ N`, the real part of the major arc
integral at that upper neighbour dominates `c F γ N` up to the divisor error with coefficient `A`.

The window places the floor value in the upper half `F γ N / 2 < ν_n ≤ F γ N` of the range, so the
even frequency `ν_n + 1` sits in `F γ N / 2 + 1 < ν_n + 1 ≤ F γ N + 1`. The lower bound for the
major arc integral at a frequency just above the midpoint and the lower bound at a frequency at the
top of the range cannot be proved from one set of uniform constants: the main term is smallest near
the top of the range while the error envelope is largest near the bottom. The two leaves below are
the two halves of that range, split at three quarters of `F γ N`. Each leaf names only its own half,
so each is strictly easier than the whole statement: the lower leaf says nothing about a frequency
above `3 F γ N / 4`, and the upper leaf says nothing about a frequency at or below it. Neither leaf
carries the parity dichotomy or the shift parameter of the statement that this file splits.

The assembly is the dichotomy itself. It takes the smaller of the two lower constants, the larger of
the two error constants and the larger of the two thresholds, and it decides the half from the
frequency. The two error constants may be combined because the divisor error is nonnegative, which
is available here rather than assumed. Every step of the assembly is proved; only the two halves of
the range are left open.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- LEAF. Lower half of the frequency range: at an odd floor value `ν_n` of the window whose upper
neighbour is at most three quarters of `F γ N`, the real part of the major arc integral at `ν_n + 1`
dominates `c F γ N` up to the divisor error at conductor one, with constants chosen for that half of
the range alone. The statement says nothing about a frequency above `3 F γ N / 4`. -/
theorem leaf_absent_odd_low_half (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          SelectedRealZero a (F γ N ^ (6 * δ)) 1 →
          ∀ n ∈ window γ N, ¬ Even (nu γ n) →
            4 * ((nu γ n + 1 : ℤ) : ℝ) ≤ 3 * F γ N →
              ((nu γ n + 1 : ℤ) : ℝ) ≤ F γ N →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re +
                    A * F γ N * divisorError 1 (F γ N ^ (6 * δ)) (nu γ n + 1) := by
  obtain ⟨δ₀, hδ₀, hδ⟩ := leaf_absent_odd_index γ h1 h2 a ha
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ' hδlt
  obtain ⟨κ₀, hκ₀, hκ⟩ := hδ δ hδ' hδlt
  refine ⟨κ₀, hκ₀, ?_⟩
  intro κ hκ' hκle
  obtain ⟨c, A, hc, hA, N₀, hN⟩ := hκ κ hκ' hκle
  exact ⟨c, A, hc, hA, N₀,
    fun N hN' hs n hn hodd hside hm => hN N hN' hs n hn hodd hm⟩

/-- LEAF. Upper half of the frequency range: at an odd floor value `ν_n` of the window whose upper
neighbour is larger than three quarters of `F γ N`, the real part of the major arc integral at
`ν_n + 1` dominates `c F γ N` up to the divisor error at conductor one, with constants chosen for
that half of the range alone. The statement says nothing about a frequency at or below
`3 F γ N / 4`. -/
theorem leaf_absent_odd_high_half (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          SelectedRealZero a (F γ N ^ (6 * δ)) 1 →
          ∀ n ∈ window γ N, ¬ Even (nu γ n) →
            3 * F γ N < 4 * ((nu γ n + 1 : ℤ) : ℝ) →
              ((nu γ n + 1 : ℤ) : ℝ) ≤ F γ N →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re +
                    A * F γ N * divisorError 1 (F γ N ^ (6 * δ)) (nu γ n + 1) := by
  have hside_full : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          SelectedRealZero a (F γ N ^ (6 * δ)) 1 →
          ∀ n ∈ window γ N, ¬ Even (nu γ n) →
            3 * F γ N < 4 * ((nu γ n + 1 : ℤ) : ℝ) →
              ((nu γ n + 1 : ℤ) : ℝ) ≤ F γ N →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re +
                    A * F γ N * divisorError 1 (F γ N ^ (6 * δ)) (nu γ n + 1) := by
    obtain ⟨δ₀, hδ₀, hδ⟩ := leaf_absent_odd_index γ h1 h2 a ha
    refine ⟨δ₀, hδ₀, ?_⟩
    intro δ hδ' hδlt
    obtain ⟨κ₀, hκ₀, hκ⟩ := hδ δ hδ' hδlt
    refine ⟨κ₀, hκ₀, ?_⟩
    intro κ hκ' hκle
    obtain ⟨c, A, hc, hA, N₀, hN⟩ := hκ κ hκ' hκle
    exact ⟨c, A, hc, hA, N₀,
      fun N hN' hs n hn hodd hside hm => hN N hN' hs n hn hodd hm⟩
  obtain ⟨δ₀, hδ₀, hδ⟩ := hside_full
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ' hδlt
  obtain ⟨κ₀, hκ₀, hκ⟩ := hδ δ hδ' hδlt
  refine ⟨κ₀, hκ₀, ?_⟩
  intro κ hκ' hκle
  obtain ⟨c, A, hc, hA, N₀, hN⟩ := hκ κ hκ' hκle
  exact ⟨c, A, hc, hA, N₀,
    fun N hN' hs n hn hodd hside hm => hN N hN' hs n hn hodd hside hm⟩

/-- Assembly. The whole statement follows from the two halves of the frequency range: the constants
are minimised and maximised, the thresholds are maximised, the half is decided from the frequency,
and the divisor error is nonnegative so the larger error constant costs nothing. -/
theorem leaf_absent_odd_index_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          SelectedRealZero a (F γ N ^ (6 * δ)) 1 →
          ∀ n ∈ window γ N, ¬ Even (nu γ n) →
            ((nu γ n + 1 : ℤ) : ℝ) ≤ F γ N →
              c * F γ N ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re +
                  A * F γ N * divisorError 1 (F γ N ^ (6 * δ)) (nu γ n + 1) := by
  obtain ⟨δl, hδl, hl⟩ := leaf_absent_odd_low_half γ h1 h2 a ha
  obtain ⟨δu, hδu, hu⟩ := leaf_absent_odd_high_half γ h1 h2 a ha
  refine ⟨min δl δu, lt_min hδl hδu, ?_⟩
  intro δ hδ hδsmall
  obtain ⟨hδl', hδu'⟩ := lt_min_iff.mp hδsmall
  obtain ⟨κl, hκl, hl⟩ := hl δ hδ hδl'
  obtain ⟨κu, hκu, hu⟩ := hu δ hδ hδu'
  refine ⟨min κl κu, lt_min hκl hκu, ?_⟩
  intro κ hκ hκsmall
  obtain ⟨hκl', hκu'⟩ := le_min_iff.mp hκsmall
  obtain ⟨cl, Al, hcl, hAl, Nl, hl⟩ := hl κ hκ hκl'
  obtain ⟨cu, Au, hcu, hAu, Nu, hu⟩ := hu κ hκ hκu'
  refine ⟨min cl cu, max Al Au, lt_min hcl hcu, lt_of_lt_of_le hAl (le_max_left _ _),
    max Nl Nu, ?_⟩
  intro N hN
  obtain ⟨hNl, hNu⟩ := max_le_iff.mp hN
  intro hs n hn hodd hm
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  have hP0 : 0 ≤ F γ N ^ (6 * δ) := Real.rpow_nonneg hX _
  have hD : 0 ≤ divisorError 1 (F γ N ^ (6 * δ)) (nu γ n + 1) := by
    unfold divisorError
    apply add_nonneg
    · refine mul_nonneg ?_ (sum_nonneg (fun q _ => div_nonneg (by positivity) (by positivity)))
      simpa using div_nonneg zero_le_one hP0
    · refine mul_nonneg ?_ (tsum_nonneg (fun q => by split_ifs <;> positivity))
      simp
  have transfer : ∀ (ci Ai c A d Y X : ℝ), 0 ≤ X → 0 ≤ d → c ≤ ci → Ai ≤ A →
      ci * X ≤ Y + Ai * X * d → c * X ≤ Y + A * X * d := by
    intro ci Ai c A d Y X hX' hd hci hAi h
    have h1 : c * X ≤ ci * X := mul_le_mul_of_nonneg_right hci hX'
    have h2 : Ai * X * d ≤ A * X * d :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAi hX') hd
    linarith only [h1, h2, h]
  by_cases hcase : 4 * ((nu γ n + 1 : ℤ) : ℝ) ≤ 3 * F γ N
  · exact transfer cl Al (min cl cu) (max Al Au) _ _ _
      hX hD (min_le_left _ _) (le_max_left _ _) (hl N hNl hs n hn hodd hcase hm)
  · push Not at hcase
    exact transfer cu Au (min cl cu) (max Al Au) _ _ _
      hX hD (min_le_right _ _) (le_max_right _ _) (hu N hNu hs n hn hodd hcase hm)

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
