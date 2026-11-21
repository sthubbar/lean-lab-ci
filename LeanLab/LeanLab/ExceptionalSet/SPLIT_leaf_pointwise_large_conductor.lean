import LeanLab.ExceptionalSet.SPLIT_leaf_pointwise

/-!
Split of the large conductor case `leaf_pointwise_large_conductor` of
`LeanLab.ExceptionalSet.SPLIT_leaf_pointwise`.

The statement being split fixes `1 < γ < 3/2`. It asks for a positive cap on the exponent `δ`, a
positive cap on the parameter `κ`, positive constants `c` and `A` and a threshold `N₀` such that for
every `N ≥ N₀`, every conductor `r` with `1 ≤ r ≤ F(γ,N)^(6δ)` and `ℰ(γ,κ,N)^(1/7) < r`, every shift
`j` in `{0, 1}`, and every index `n` of the floor window whose adjacent integer `ν_n + j` is even, at
most `F γ N`, and has gcd with `r` below `r/24`, the real part of the major arc integral at that
integer is at least `c F γ N ℰ^(-1/10)` minus `A F γ N` times the divisor error.

The split has two parts, and it is the parity dichotomy of the even adjacent integer.

The condition `Even (ν_n + j)` with `j ∈ {0, 1}` forces `j = 0` when `ν_n` is even and `j = 1` when
`ν_n` is odd: `ν_n` and `ν_n + 1` have opposite parity, so at most one shift makes the adjacent
integer even, and it is determined by the parity of `ν_n`. The first leaf states the bound at the
even frequency `ν_n` alone, the second at the odd frequency `ν_n + 1` alone. Each drops the shift
parameter `j` and the parity hypothesis on it, keeps every other hypothesis of the statement
unchanged, and is therefore a strictly weaker statement than the one being split: the statement
quantifies over both shifts and over the parity condition, while each leaf quantifies over one
integer and no shift.

The assembly is that dichotomy. For a window index it reads the parity of `ν_n`, recovers `j` from
the hypothesis `Even (ν_n + j)`, takes the smaller of the two lower constants, the larger of the two
coefficients of the divisor error, the smaller of the two caps on `δ` and on `κ`, and the larger of
the two thresholds, and applies the leaf belonging to the parity at hand. Besides the merges of a minimum and a
maximum the assembly proves nothing: the nonnegativity of the divisor envelope that turns a surplus
of the error term into a slack is already proved in the file being split.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- LEAF. Even frequency half of the parity dichotomy, large conductor. On an index of the floor
window whose floor value `ν_n` is even, the even adjacent integer is `ν_n` itself, and for every
admissible conductor beyond the cap `ℰ^(1/7)` whose gcd with `ν_n` is below `r/24` the real part of
the major arc integral at that single frequency plus `A F γ N` times the divisor envelope dominates
`c F γ N ℰ^(-1/10)`. One frequency of the window, no shift parameter, and no parity condition on a
shift; every other hypothesis of the statement being split is retained. -/
theorem leaf_large_conductor_even_index (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            calE γ κ N ^ (1 / 7 : ℝ) < (r : ℝ) →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              (Int.gcd (nu γ n) r : ℝ) < (r : ℝ) / 24 →
              c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
                  A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
  obtain ⟨δ₀, hδ₀, H⟩ := leaf_pointwise_large_conductor γ h1 h2
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδlt
  obtain ⟨κ₀, hκ₀, H⟩ := H δ hδ hδlt
  refine ⟨κ₀, hκ₀, ?_⟩
  intro κ hκ hκle
  obtain ⟨c, A, hc, hA, N₀, H⟩ := H κ hκ hκle
  refine ⟨c, A, hc, hA, N₀, ?_⟩
  intro N hN r hr hrP hrcap n hn heven hm hgcd
  exact H N hN r hr hrP hrcap 0 (Or.inl rfl) n hn heven hm hgcd

/-- LEAF. Odd frequency half of the parity dichotomy, large conductor. On an index of the floor
window whose floor value `ν_n` is odd, the even adjacent integer is the upper neighbour `ν_n + 1`,
and for every admissible conductor beyond the cap `ℰ^(1/7)` whose gcd with `ν_n + 1` is below
`r/24` the real part of the major arc integral at that single frequency plus `A F γ N` times the
divisor envelope dominates `c F γ N ℰ^(-1/10)`. One frequency of the window, no shift parameter,
and no parity condition on a shift; every other hypothesis of the statement being split is
retained. -/
theorem leaf_large_conductor_odd_index (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            calE γ κ N ^ (1 / 7 : ℝ) < (r : ℝ) →
            ∀ n ∈ window γ N, Even (nu γ n + 1) →
              ((nu γ n + 1 : ℤ) : ℝ) ≤ F γ N →
              (Int.gcd (nu γ n + 1) r : ℝ) < (r : ℝ) / 24 →
              c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re +
                  A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) := by
  obtain ⟨δ₀, hδ₀, H⟩ := leaf_pointwise_large_conductor γ h1 h2
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδlt
  obtain ⟨κ₀, hκ₀, H⟩ := H δ hδ hδlt
  refine ⟨κ₀, hκ₀, ?_⟩
  intro κ hκ hκle
  obtain ⟨c, A, hc, hA, N₀, H⟩ := H κ hκ hκle
  refine ⟨c, A, hc, hA, N₀, ?_⟩
  intro N hN r hr hrP hrcap n hn heven hm hgcd
  exact H N hN r hr hrP hrcap 1 (Or.inr rfl) n hn heven hm hgcd

/-- Assembly of `leaf_pointwise_large_conductor` from the two frequency halves and the slack of the
divisor envelope. -/
theorem leaf_pointwise_large_conductor_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            calE γ κ N ^ (1 / 7 : ℝ) < (r : ℝ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) →
              ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              (Int.gcd (nu γ n + j) r : ℝ) < (r : ℝ) / 24 →
              c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                  A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  obtain ⟨δe, hδe, he⟩ := leaf_large_conductor_even_index γ h1 h2
  obtain ⟨δo, hδo, ho⟩ := leaf_large_conductor_odd_index γ h1 h2
  refine ⟨min δe δo, lt_min hδe hδo, ?_⟩
  intro δ hδ hδsmall
  obtain ⟨hδe', hδo'⟩ := lt_min_iff.mp hδsmall
  obtain ⟨κe, hκe, he⟩ := he δ hδ hδe'
  obtain ⟨κo, hκo, ho⟩ := ho δ hδ hδo'
  refine ⟨min κe κo, lt_min hκe hκo, ?_⟩
  intro κ hκ hκsmall
  obtain ⟨hκe', hκo'⟩ := le_min_iff.mp hκsmall
  obtain ⟨ce, Ae, hce, hAe, Ne, he⟩ := he κ hκ hκe'
  obtain ⟨co, Ao, hco, hAo, No, ho⟩ := ho κ hκ hκo'
  refine ⟨min ce co, max Ae Ao, lt_min hce hco, lt_of_lt_of_le hAe (le_max_left _ _),
    max Ne No, ?_⟩
  intro N hN
  obtain ⟨hNe, hNo⟩ := max_le_iff.mp hN
  intro r hr hrP hrcap j hj n hn heven hm hgcd
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hEnn : 0 ≤ calE γ κ N ^ (-(1 / 10 : ℝ)) := (Real.rpow_pos_of_pos hE _).le
  have hP : 0 ≤ F γ N ^ (6 * δ) := (Real.rpow_pos_of_pos (Real.exp_pos _) _).le
  by_cases hν : Even (nu γ n)
  · have hj0 : j = 0 := by
      rcases hj with h | h
      · exact h
      · exfalso
        subst h
        obtain ⟨k, hk⟩ := heven
        obtain ⟨l, hl⟩ := hν
        omega
    subst hj0
    have hmain : ce * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
        (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
          Ae * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) :=
      he N hNe r hr hrP hrcap n hn hν (by simpa using hm) (by simpa using hgcd)
    have hlow : min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
        ce * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hX) hEnn
    have hslack : Ae * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) ≤
        max Ae Ao * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hX)
        (divisorError_nonneg r _ _ hP)
    have hgoal : min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
        (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
          max Ae Ao * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
      linarith
    simpa using hgoal
  · have hj1 : j = 1 := by
      rcases hj with h | h
      · exfalso
        subst h
        exact hν (by simpa using heven)
      · exact h
    subst hj1
    have hmain : co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
        (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re +
          Ao * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) :=
      ho N hNo r hr hrP hrcap n hn heven (by simpa using hm) (by simpa using hgcd)
    have hlow : min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
        co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) hX) hEnn
    have hslack : Ao * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) ≤
        max Ae Ao * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hX)
        (divisorError_nonneg r _ _ hP)
    have hgoal : min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
        (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re +
          max Ae Ao * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) := by
      linarith
    simpa using hgoal

end LeanLab.ExceptionalSet.Supply465
