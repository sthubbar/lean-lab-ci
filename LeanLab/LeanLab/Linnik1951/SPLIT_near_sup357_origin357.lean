/-
Split of the phase-zero pointwise supremum bound `near_sup357_origin357` into four
smaller steps. Nothing here changes the statement: `near_sup357_origin357_split`
repeats it character for character and proves it from the four OPEN leaves below,
which record, in order, (1) the size of the damped character prime sum restricted to
the short range where the damping weight is not yet negligible, (2) the smallness of
the complementary range, where the exponential damping alone already bounds the sum
by an absolute constant, (3) the exact splitting of the phase-zero sum into those two
ranges, and (4) the elementary lower bound of the weight N over q times log N to the
fifth. The assembly does not use `near_sup357_origin357`.
-/
import LeanLab.Linnik1951.SPLIT_near_positive_sup357

namespace LeanLab.Linnik1951

/-- LEAF. Step 1 of 4: the short range at phase zero. There is a fixed positive
constant C such that for every large N, every modulus q with 1 at most q at most N to
the one seventh, and every nonprincipal character mod q, the squared norm of the
damped character prime sum, cut down to the primes p at most N log N, is at most C
times N over q times log N to the fifth. All of the character information sits in
this step; the range is short enough that the bound can be read off from the partial
sums of the character over primes, and no prime beyond N log N is involved. -/
theorem near_sup357_origin_short357 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ) else 0)‖ ^ 2 ≤
            C * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := by
  sorry

/-- LEAF. Step 2 of 4: the complementary range carries no character information. For
N at least three, any modulus and any character mod it, the damped character prime sum
over the primes p beyond N log N has norm at most 2. Each summand has norm at most the
real weight exp of minus p over N, and the sum of those weights beyond N log N is at
most 1 because exp of minus log N is 1 over N; the factor 2 leaves room for the
comparison with the integral of the decreasing weight. No cancellation and no
arithmetic input is used. -/
theorem near_sup357_origin_tail357 (N : ℕ) (hN : 3 ≤ N) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    ‖∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                (0 : ℂ) else χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ))‖ ≤ 2 := by
  sorry

/-- LEAF. Step 3 of 4: the splitting identity at phase zero. For N at least one, any
modulus and any character mod it, the value of the damped character prime sum at phase
zero is the sum of its two ranges, the primes p at most N log N and the primes p
beyond N log N. At phase zero the oscillating factor is 1, and the two ranges are the
two complementary branches of the same indicator, so the single sum over all primes is
the sum of the two pieces. -/
theorem near_sup357_origin_split357 {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ)
    (hN : 1 ≤ N) :
    characterPrime280 χ N 0 = ∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ) else 0) + ∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                (0 : ℂ) else χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ)) := by
  sorry

/-- LEAF. Step 4 of 4: the weight is at least one. For N at least three, every modulus
q with 1 at most q at most N to the one seventh satisfies 1 at most N over q times log
N to the fifth. The hypotheses give log N at least 1 and N over q at least N to the six
sevenths, which is at least 1, so the product is at least 1. This is what lets the
assembly trade the absolute constant 8 of step 2 for the same weight that the other
terms carry. -/
theorem near_sup357_origin_weight_one357 {N : ℕ} (hN : 3 ≤ N) {q : ℕ} (hq : 1 ≤ q)
    (hqt : (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ)) :
    (1 : ℝ) ≤ (N : ℝ) / (q : ℝ) * Real.log N ^ 5 := by
  sorry

/-- Private helper for the assembly: the squared norm of a sum of two vectors is at
most twice the sum of the squared norms. -/
private lemma near_sup357_origin_norm_add_sq357 (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h2 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (‖a‖ + ‖b‖) ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  linarith

/-- Private helper for the assembly: with a nonnegative constant and a weight at least
one, twice C times the weight plus twice the constant 4 of the tail step is at most the
constant 2 C plus 8 applied to the weight. -/
private lemma near_sup357_origin_absorb357 (C W : ℝ) (hC : 0 ≤ C) (hW : 1 ≤ W) :
    2 * (C * W) + 2 * 4 ≤ (2 * C + 8) * W := by
  nlinarith [hC, hW]

/-- Assembly of `near_sup357_origin357` from the four leaves above: split the value at
phase zero into the short range and its complement, bound the short range by step 1 and
the complement by the absolute constant of step 2, use step 4 to replace that constant
by the weight, and collect 2 C plus 8 as the new constant. No step uses
`near_sup357_origin357` itself. -/
theorem near_sup357_origin357_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖characterPrime280 χ N 0‖ ^ 2 ≤ C * (N : ℝ) / (q : ℝ) * Real.log N ^ 5 := by
  obtain ⟨C, hC, N0, hshort⟩ := near_sup357_origin_short357 hG
  refine ⟨2 * C + 8, by linarith, max N0 2, ?_⟩
  intro N hN q hq hqt χ hχ
  have hN2 : 2 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hN0N : N0 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN3 : 3 ≤ N := hN2
  have hN1 : 1 ≤ N := by omega
  have hsplit := near_sup357_origin_split357 (χ := χ) (N := N) hN1
  have htail := near_sup357_origin_tail357 N hN3 χ
  have hshortN := hshort N hN0N q hq hqt χ hχ
  have htail2 : ‖∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                (0 : ℂ) else χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ))‖ ^ 2 ≤ 4 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) htail 2
    have hpow : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [hpow] at h
    exact h
  have hW := near_sup357_origin_weight_one357 hN3 hq hqt
  have hC0 : (0 : ℝ) ≤ C := le_of_lt hC
  have htri := near_sup357_origin_norm_add_sq357 (∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ) else 0)) (∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                (0 : ℂ) else χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ)))
  have hWnn : (0 : ℝ) ≤ C * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) :=
    mul_nonneg hC0 (le_trans zero_le_one hW)
  have hmain : ‖∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ) else 0) + ∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                (0 : ℂ) else χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ))‖ ^ 2 ≤
      (2 * C + 8) * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := by
    have hbound : ‖∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ) else 0) + ∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                (0 : ℂ) else χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ))‖ ^ 2 ≤
        2 * (C * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5)) + 2 * 4 := by
      nlinarith [htri, hshortN, htail2]
    exact le_trans hbound (near_sup357_origin_absorb357 C
      ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) hC0 hW)
  calc ‖characterPrime280 χ N 0‖ ^ 2 = ‖∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ) else 0) + ∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                (0 : ℂ) else χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ))‖ ^ 2 := by rw [hsplit]
    _ ≤ (2 * C + 8) * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := hmain
    _ = (2 * C + 8) * (N : ℝ) / (q : ℝ) * Real.log N ^ 5 := by ring

end LeanLab.Linnik1951
