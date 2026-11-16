import LeanLab.ExceptionalSet.UpJ200.Decomp559b

/-!
Split of `leaf_prime_product_selected` of `LeanLab.ExceptionalSet.UpJ200.Decomp559b`.

The sealed step is the nonempty prime product case of the case analysis: for admissible
`δ, κ`, a conductor `r` selected by `SelectedRealZero`, an index `n` of the floor window
and a shift `j` in `{0, 1}` with the adjacent integer `ν_n + j` even and at most `F γ N`,
if the conductor shares a factor with `ν_n + j` and some prime `p > 3` divides `r` but not
`ν_n + j`, then the real part of the major arc integral at that frequency is at least
`c F γ N` minus `A F γ N` times the divisor error.

The case uses one property of the shift only: with `j` in `{0, 1}` the parity condition
`Even (ν_n + j)` forces `j = 0` when `ν_n` is even and `j = 1` when `ν_n` is odd, so the
even adjacent integer is `ν_n` in the first case and `ν_n + 1` in the second. The two
leaves below are the two halves of that dichotomy. Each names one even frequency and drops
the shift parameter together with the parity condition on it, so each covers strictly less
than the whole step: the even half says nothing about the frequency `ν_n + 1`, and the odd
half says nothing about the frequency `ν_n`.

The assembly is the dichotomy itself. It reads the parity of `ν_n`, recovers the shift from
the parity condition, takes the smaller of the two lower constants, the larger of the two
error constants and the larger of the two thresholds. The error constants may be combined
because the divisor envelope is nonnegative, which is proved here rather than assumed. Every
step of the assembly is proved; only the two frequency halves are left open.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- LEAF. Even frequency half of the dichotomy: on an index of the floor window whose floor
value `ν_n` is even, the even adjacent integer is `ν_n` itself, and the real part of the
major arc integral at that single frequency dominates `c F γ N` up to the divisor envelope
for a conductor that shares a factor with `ν_n` and has a prime divisor `p > 3` not dividing
`ν_n`. One frequency, no shift parameter, no parity condition on a shift. -/
theorem leaf_prime_product_even_index (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n) →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
  sorry

/-- LEAF. Odd frequency half of the dichotomy: on an index of the floor window whose floor
value `ν_n` is odd, the even adjacent integer is the upper neighbour `ν_n + 1`, and the real
part of the major arc integral at that single frequency dominates `c F γ N` up to the
divisor envelope for a conductor that shares a factor with `ν_n + 1` and has a prime divisor
`p > 3` not dividing `ν_n + 1`. One frequency, no shift parameter, no parity condition on a
shift. -/
theorem leaf_prime_product_odd_index (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, ¬ Even (nu γ n) →
              ((nu γ n + 1 : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n + 1) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + 1) →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) := by
  sorry

/-- Assembly. The whole step follows from the two frequency halves: the parity condition
fixes the shift, the lower constants are minimised, the error constants are maximised and
the thresholds are maximised, and the divisor envelope is nonnegative, so the larger error
constant costs nothing. -/
theorem leaf_prime_product_selected_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n + j) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + j) →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  obtain ⟨δe, hδe, he⟩ := leaf_prime_product_even_index γ h1 h2 a ha
  obtain ⟨δo, hδo, ho⟩ := leaf_prime_product_odd_index γ h1 h2 a ha
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
  intro r hr hrP hs j hj n hn heven hm hgcd hprime
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  have hD : ∀ m : ℤ, 0 ≤ divisorError r (F γ N ^ (6 * δ)) m := by
    intro m
    unfold divisorError
    apply add_nonneg
    · apply mul_nonneg (by positivity)
      exact sum_nonneg (fun q _ => by positivity)
    · apply mul_nonneg (by positivity)
      exact tsum_nonneg (fun q => by split_ifs <;> positivity)
  have transfer : ∀ (ci Ai c A d Y X : ℝ), 0 ≤ X → 0 ≤ d → c ≤ ci → Ai ≤ A →
      ci * X ≤ Y + Ai * X * d → c * X ≤ Y + A * X * d := by
    intro ci Ai c A d Y X hX' hd hci hAi h
    have h1 : c * X ≤ ci * X := mul_le_mul_of_nonneg_right hci hX'
    have h2 : Ai * X * d ≤ A * X * d :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAi hX') hd
    linarith only [h1, h2, h]
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
    have hm' : ((nu γ n : ℤ) : ℝ) ≤ F γ N := by simpa using hm
    have hg' : 1 < Int.gcd (nu γ n) r := by simpa using hgcd
    have hp' : ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n := by
      simpa using hprime
    have hcase := he N hNe r hr hrP hs n hn hν hm' hg' hp'
    simpa using transfer ce Ae (min ce co) (max Ae Ao)
      (divisorError r (F γ N ^ (6 * δ)) (nu γ n))
      ((R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re) (F γ N)
      hX (hD (nu γ n)) (min_le_left _ _) (le_max_left _ _) hcase
  · have hj1 : j = 1 := by
      rcases hj with h | h
      · exfalso
        subst h
        exact hν (by simpa using heven)
      · exact h
    subst hj1
    have hcase := ho N hNo r hr hrP hs n hn hν hm hgcd hprime
    exact transfer co Ao (min ce co) (max Ae Ao)
      (divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1))
      ((R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re) (F γ N)
      hX (hD (nu γ n + 1)) (min_le_right _ _) (le_max_right _ _) hcase

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
