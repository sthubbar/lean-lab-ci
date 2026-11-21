import LeanLab.ExceptionalSet.UpJ200.Decomp559b

/-!
Split of `leaf_prime_product_selected` of `LeanLab.ExceptionalSet.UpJ200.Decomp559b`.

The sealed step is the nonempty prime product case of the case analysis: for admissible
`δ, κ`, a conductor `r` selected by `SelectedRealZero`, an index `n` of the floor window
and a shift `j` in `{0, 1}` with the adjacent integer `ν_n + j` even and at most `F γ N`,
if the conductor shares a factor with `ν_n + j` and some prime `p > 3` divides `r` but not
`ν_n + j`, then the real part of the major arc integral at that frequency is at least
`c F γ N` minus `A F γ N` times the divisor error.

The step is split along the shift `j`. The two leaves below are the two halves of that
dichotomy. Each names one shift value and drops the other, so each covers strictly less
than the whole step: the `j = 0` leaf says nothing about `ν_n + 1`, and the `j = 1` leaf
says nothing about `ν_n`.

The assembly is the dichotomy itself. It reads the shift, takes the smaller of the two
lower constants, the larger of the two error constants and the larger of the two
thresholds. The error constants may be combined because the divisor envelope is
nonnegative, which is proved here rather than assumed. Every step of the assembly is
proved; only the two shift halves are left open.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- LEAF. Shift zero half of the dichotomy: with `j = 0` the even adjacent integer is
`ν_n` itself, and the real part of the major arc integral at that single frequency
dominates `c F γ N` up to the divisor envelope for a conductor that shares a factor
with `ν_n` and has a prime divisor `p > 3` not dividing `ν_n`. One shift value, no
parity condition on a shift. -/
theorem leaf_prime_product_j0 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
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

/-- LEAF. Shift one half of the dichotomy: with `j = 1` the even adjacent integer is
the upper neighbour `ν_n + 1`, and the real part of the major arc integral at that
single frequency dominates `c F γ N` up to the divisor envelope for a conductor that
shares a factor with `ν_n + 1` and has a prime divisor `p > 3` not dividing `ν_n + 1`.
One shift value, no parity condition on a shift. -/
theorem leaf_prime_product_j1 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
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

/-- Assembly. The whole step follows from the two shift halves: the shift fixes which
leaf applies, the lower constants are minimised, the error constants are maximised and
the thresholds are maximised, and the divisor envelope is nonnegative, so the larger
error constant costs nothing. -/
theorem leaf_prime_product_selected_F2083 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
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
  obtain ⟨δ0, hδ0, h0⟩ := leaf_prime_product_j0 γ h1 h2 a ha
  obtain ⟨δ1, hδ1, h1'⟩ := leaf_prime_product_j1 γ h1 h2 a ha
  refine ⟨min δ0 δ1, lt_min hδ0 hδ1, ?_⟩
  intro δ hδ hδsmall
  obtain ⟨hδ0', hδ1'⟩ := lt_min_iff.mp hδsmall
  obtain ⟨κ0, hκ0, h0'⟩ := h0 δ hδ hδ0'
  obtain ⟨κ1, hκ1, h1''⟩ := h1' δ hδ hδ1'
  refine ⟨min κ0 κ1, lt_min hκ0 hκ1, ?_⟩
  intro κ hκ hκsmall
  obtain ⟨hκ0', hκ1'⟩ := le_min_iff.mp hκsmall
  obtain ⟨c0, A0, hc0, hA0, N0, h0''⟩ := h0' κ hκ hκ0'
  obtain ⟨c1, A1, hc1, hA1, N1, h1'''⟩ := h1'' κ hκ hκ1'
  refine ⟨min c0 c1, max A0 A1, lt_min hc0 hc1, lt_of_lt_of_le hA0 (le_max_left _ _),
    max N0 N1, ?_⟩
  intro N hN
  obtain ⟨hN0, hN1⟩ := max_le_iff.mp hN
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
  rcases hj with hj0 | hj1
  · subst hj0
    have heven' : Even (nu γ n) := by simpa using heven
    have hm' : ((nu γ n : ℤ) : ℝ) ≤ F γ N := by simpa using hm
    have hgcd' : 1 < Int.gcd (nu γ n) r := by simpa using hgcd
    have hprime' : ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n := by
      simpa using hprime
    have hcase := h0'' N hN0 r hr hrP hs n hn heven' hm' hgcd' hprime'
    have hgoal : min c0 c1 * F γ N ≤
        (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
          max A0 A1 * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
      have h1' : min c0 c1 * F γ N ≤ c0 * F γ N :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hX
      have h2 : A0 * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) ≤
          max A0 A1 * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hX)
          (hD (nu γ n))
      linarith only [hcase, h1', h2]
    simpa [add_zero] using hgoal
  · subst hj1
    have hodd : ¬ Even (nu γ n) := by
      intro he
      rcases heven with ⟨k, hk⟩
      rcases he with ⟨l, hl⟩
      have h1 : (nu γ n + 1 : ℤ) - nu γ n = 1 := by omega
      have h2 : (nu γ n + 1 : ℤ) - nu γ n = (k - l) + (k - l) := by rw [hk, hl]; ring
      rw [h2] at h1
      have : ¬ Even (1 : ℤ) := by decide
      exact this ⟨k - l, h1.symm⟩
    have hcase := h1''' N hN1 r hr hrP hs n hn hodd hm hgcd hprime
    have hgoal : min c0 c1 * F γ N ≤
        (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re +
          max A0 A1 * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) := by
      have h1' : min c0 c1 * F γ N ≤ c1 * F γ N :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hX
      have h2 : A1 * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) ≤
          max A0 A1 * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hX)
          (hD (nu γ n + 1))
      linarith only [hcase, h1', h2]
    simpa using hgoal

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
