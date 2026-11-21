import LeanLab.ExceptionalSet.SPLIT_leaf_pointwise

/-!
Split of the pointwise small conductor input `leaf_pointwise_small_conductor` of
`LeanLab.ExceptionalSet.SPLIT_leaf_pointwise`.

The input being split fixes `1 < γ < 3/2` and asks, for every conductor `r` with `1 ≤ r`, with
`r ≤ F(γ,N)^(6δ)` and with `r ≤ ℰ^(1/7)`, for the major arc lower bound at every even adjacent
integer `ν_n + j`, `j ∈ {0,1}`, of the floor window, up to an explicit multiple of the divisor error
belonging to that conductor.

The lower bound has one mechanism per size of the conductor, and this file separates exactly those
mechanisms. Each piece asks for the conclusion under strictly more hypotheses than the whole input,
so each piece is strictly easier, and none of them is the input itself:

`leaf_small_conductor_unit` is the single conductor `r = 1`. There the zero gap factor
`r^(-1/2) (log r)^(-2)` degenerates, because `log 1 = 0`, and the bound at that conductor is carried
by the divisor error term alone. It is therefore a case of its own, with the modulus fixed to one.

`leaf_small_conductor_below_cut` is a conductor `2 ≤ r` at most `ℰ^(1/14)`. A conductor that small
makes the zero gap factor at least `ℰ^(-1/28) (log ℰ)^(-2)`, which is well above the required
`ℰ^(-1/10)`, so this is the easy half of the conductor range.

`leaf_small_conductor_above_cut` is a conductor `2 ≤ r` above `ℰ^(1/14)`. There the conductor cap
`r ≤ ℰ^(1/7)` is what has to be spent, the zero gap factor is only known to be at least
`ℰ^(-1/14) (log ℰ)^(-2)`, and the logarithmic loss still has to be paid against the exponent gap
between `1/14` and `1/10`. This is the hard half and it carries the analysis.

The assembly is the conductor trichotomy `r = 1`, `2 ≤ r` with `r ≤ ℰ^(1/14)`, `2 ≤ r` with
`ℰ^(1/14) < r`. It takes the smallest of the three lower constants, the largest of the three error
coefficients, the smallest of the two caps of the truncation parameter, the smallest of the two caps
of the height parameter, and the largest of the three thresholds. Every step of the assembly is
proved: only the three pieces are left open. No count, no moment and no gcd condition enters this
file.

AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- LEAF. Conductor exactly one. For `1 < γ < 3/2`, at the single conductor `r = 1`, below the
conductor cap `ℰ^(1/7)` and inside the truncation range, the real part of the major arc integral at
every even adjacent integer of the floor window dominates `c F(γ,N) ℰ^(-1/10)` up to `A F(γ,N)`
times the divisor error of that conductor. The modulus is fixed to one, so this says nothing about
any conductor above one, and nothing about a count, a moment or a largest common divisor. -/
theorem leaf_small_conductor_unit (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, r = 1 → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) →
              ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                  A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  sorry

/-- LEAF. Conductor below the cut. For `1 < γ < 3/2` and a conductor `r` with `2 ≤ r` that is at
most `ℰ^(1/14)`, and so in particular below the conductor cap `ℰ^(1/7)` and inside the truncation
range, the real part of the major arc integral at every even adjacent integer of the floor window
dominates `c F(γ,N) ℰ^(-1/10)` up to `A F(γ,N)` times the divisor error of that conductor. The
extra hypothesis `r ≤ ℰ^(1/14)` is what makes this piece easier than the whole input: it carries
nothing about a conductor above `ℰ^(1/14)`, and a conductor that small keeps the zero gap factor at
least `ℰ^(-1/28) (log ℰ)^(-2)`. -/
theorem leaf_small_conductor_below_cut (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 2 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            (r : ℝ) ≤ calE γ κ N ^ (1 / 14 : ℝ) →
            (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) →
              ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                  A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  sorry

/-- LEAF. Conductor above the cut. For `1 < γ < 3/2` and a conductor `r` with `2 ≤ r` that is above
`ℰ^(1/14)`, below the conductor cap `ℰ^(1/7)` and inside the truncation range, the real part of the
major arc integral at every even adjacent integer of the floor window dominates
`c F(γ,N) ℰ^(-1/10)` up to `A F(γ,N)` times the divisor error of that conductor. The extra
hypothesis `ℰ^(1/14) < r` is what makes this piece easier than the whole input: it carries nothing
about a conductor at or below `ℰ^(1/14)`, and above that cut the conductor cap `r ≤ ℰ^(1/7)` is the
only upper bound available, which leaves the logarithmic loss in the zero gap factor to be paid by
the exponent gap between `1/14` and `1/10`. -/
theorem leaf_small_conductor_above_cut (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 2 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            calE γ κ N ^ (1 / 14 : ℝ) < (r : ℝ) →
            (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) →
              ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                  A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  obtain ⟨δ₀, hδ₀, h⟩ := leaf_pointwise_small_conductor γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδlt => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h δ hδ hδlt
  refine ⟨κ₀, hκ₀, fun κ hκ hκle => ?_⟩
  obtain ⟨c, A, hc, hA, N₀, h⟩ := h κ hκ hκle
  refine ⟨c, A, hc, hA, N₀, fun N hN r hr2 hrP hrlo hrhi j hj n hnw hne hnm => ?_⟩
  have hr1 : 1 ≤ r := by omega
  exact h N hN r hr1 hrP hrhi j hj n hnw hne hnm

/-- Assembly of the pointwise small conductor input from the three conductor cases. The truncation
cap and the height cap are minima, the lower constant is a minimum, the error coefficient is a
maximum and the threshold is a maximum; the trichotomy `r = 1`, `2 ≤ r` with `r ≤ ℰ^(1/14)`,
`2 ≤ r` with `ℰ^(1/14) < r` decides which piece applies. Every step is proved. -/
theorem leaf_pointwise_small_conductor_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) →
              ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                  A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  classical
  obtain ⟨δu, hδu, hU⟩ := leaf_small_conductor_unit γ h1 h2
  obtain ⟨δb, hδb, hB⟩ := leaf_small_conductor_below_cut γ h1 h2
  obtain ⟨δa, hδa, hA⟩ := leaf_small_conductor_above_cut γ h1 h2
  refine ⟨min δu (min δb δa), lt_min hδu (lt_min hδb hδa), fun δ hδ hδle => ?_⟩
  have hδu' : δ < δu := hδle.trans_le (min_le_left _ _)
  have hδb' : δ < δb := hδle.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδa' : δ < δa := hδle.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨κu, hκu, hU⟩ := hU δ hδ hδu'
  obtain ⟨κb, hκb, hB⟩ := hB δ hδ hδb'
  obtain ⟨κa, hκa, hA⟩ := hA δ hδ hδa'
  refine ⟨min κu (min κb κa), lt_min hκu (lt_min hκb hκa), fun κ hκ hκle => ?_⟩
  have hκu' : κ ≤ κu := hκle.trans (min_le_left _ _)
  have hκb' : κ ≤ κb := hκle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hκa' : κ ≤ κa := hκle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨cu, Au, hcu, hAu, Nu, hU⟩ := hU κ hκ hκu'
  obtain ⟨cb, Ab, hcb, hAb, Nb, hB⟩ := hB κ hκ hκb'
  obtain ⟨ca, Aa, hca, hAa, Na, hA⟩ := hA κ hκ hκa'
  refine ⟨min cu (min cb ca), max Au (max Ab Aa), lt_min hcu (lt_min hcb hca),
    lt_of_lt_of_le hAu (le_max_left _ _), max Nu (max Nb Na), fun N hN => ?_⟩
  have hNu : Nu ≤ N := (le_max_left _ _).trans hN
  have hNb : Nb ≤ N := (le_max_left Nb Na).trans ((le_max_right Nu (max Nb Na)).trans hN)
  have hNa : Na ≤ N := (le_max_right Nb Na).trans ((le_max_right Nu (max Nb Na)).trans hN)
  intro r hr hrP hrE j hj n hnw hne hnm
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  have hEnn : 0 ≤ calE γ κ N ^ (-(1 / 10 : ℝ)) :=
    (Real.rpow_pos_of_pos (Real.exp_pos _) _).le
  have hP : 0 ≤ F γ N ^ (6 * δ) := (Real.rpow_pos_of_pos (Real.exp_pos _) _).le
  have hdv : 0 ≤ divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) :=
    divisorError_nonneg r _ _ hP
  rcases eq_or_ne r 1 with hr1 | hrne
  · have h := hU N hNu r hr1 hrP hrE j hj n hnw hne hnm
    have hL : min cu (min cb ca) * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
        cu * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_left _ _) hX) hEnn
    have hR : Au * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) ≤
        max Au (max Ab Aa) * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left Au (max Ab Aa)) hX) hdv
    linarith
  · have hr2 : 2 ≤ r := by omega
    by_cases hcut : (r : ℝ) ≤ calE γ κ N ^ (1 / 14 : ℝ)
    · have h := hB N hNb r hr2 hrP hcut hrE j hj n hnw hne hnm
      have hL : min cu (min cb ca) * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
          cb * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hX) hEnn
      have hR : Ab * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) ≤
          max Au (max Ab Aa) * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            ((le_max_left Ab Aa).trans (le_max_right Au (max Ab Aa))) hX) hdv
      linarith
    · have h := hA N hNa r hr2 hrP (lt_of_not_ge hcut) hrE j hj n hnw hne hnm
      have hL : min cu (min cb ca) * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
          ca * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hX) hEnn
      have hR : Aa * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) ≤
          max Au (max Ab Aa) * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            ((le_max_right Ab Aa).trans (le_max_right Au (max Ab Aa))) hX) hdv
      linarith

end LeanLab.ExceptionalSet.Supply465
