import LeanLab.AlmostPrimeSums.RosserDefect

/-!
AI wrote this Lean code for CODEX task258. Goldbach is open.
At level at least z to the tenth power, a squarefree argument with at
most eight prime factors has zero Rosser defect. Thus the positive
moment is supported on at least nine prime factors. This is a derived
finite support fact for the stopping terms on BJS p. 10 equation 28
and the cube cutoff on Heath Brown p. 34.
-/

namespace LeanLab.AlmostPrimeSums.Decomp1527b

open Finset Real BoundingSieve

/-- In the fundamental lemma range, a squarefree argument with at most
eight prime factors has zero defect. Derived finite support fact from
BJS p. 10 equation 28 and Heath Brown p. 34. -/
theorem rosserDefect_zero_of_card_le_eight (D z : ℝ) (hz : 2 ≤ z) (hD : z ^ 10 ≤ D)
    (upper : Bool) {n : ℕ} (hn : Squarefree n)
    (hP : ∀ p ∈ n.primeFactors, (p : ℝ) < z) (hcard : n.primeFactors.card ≤ 8) :
    rosserDefect D upper n = 0 := by
  classical
  by_cases hn1 : n = 1
  · subst n; cases upper <;> simp [rosserDefect, rosserWeight, decPrimes]
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by
    have h0 := hn.ne_zero
    omega)
  have hprod : (n : ℝ) < z ^ n.primeFactors.card := by
    calc
      _ = ∏ p ∈ n.primeFactors, (p : ℝ) := by
        rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]
      _ < ∏ _p ∈ n.primeFactors, z :=
        Finset.prod_lt_prod_of_nonempty₀
          (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos) hP hne
      _ = _ := by simp
  have hprod8 : (n : ℝ) < z ^ 8 := hprod.trans_le
    (pow_le_pow_right₀ (by linarith) hcard)
  apply rosserDefect_eq_zero_of_small D z (by linarith) upper (fun p hp => (hP p hp).le)
  calc
    (n : ℝ) * z ^ 2 < z ^ 8 * z ^ 2 := mul_lt_mul_of_pos_right hprod8 (by positivity)
    _ = z ^ 10 := by ring
    _ ≤ D := hD

/-- The normalized defect moment in the fundamental lemma range is
supported on divisors with at least nine prime factors. Derived finite
localization for BJS p. 10 equation 28 and Heath Brown p. 34. -/
theorem rosser_defect_moment_eq_many_primes (s : BoundingSieve) (D z : ℝ)
    (hz : 2 ≤ z) (hD : z ^ 10 ≤ D)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) (upper : Bool) :
    (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D upper n) =
      ∑ n ∈ s.prodPrimes.divisors.filter (fun n : ℕ => 9 ≤ n.primeFactors.card),
        s.selbergTerms n * rosserDefect D upper n := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hc : 9 ≤ n.primeFactors.card
  · simp [hc]
  · have hnp := (Nat.mem_divisors.mp hn).1
    have he := rosserDefect_zero_of_card_le_eight D z hz hD upper
      (s.prodPrimes_squarefree.squarefree_of_dvd hnp)
      (fun p hp => hP p (Nat.primeFactors_mono hnp s.prodPrimes_ne_zero hp)) (by omega)
    simp [hc, he]

/-- Both support restrictions hold at once: a nonzero contribution has
at least nine prime factors and n times z squared at least D. Derived
finite localization for BJS p. 10 equation 28 and Heath Brown p. 34. -/
theorem rosser_defect_moment_eq_tail_many_primes (s : BoundingSieve) (D z : ℝ)
    (hz : 2 ≤ z) (hD : z ^ 10 ≤ D)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) (upper : Bool) :
    (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D upper n) =
      ∑ n ∈ s.prodPrimes.divisors.filter
          (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card),
        s.selbergTerms n * rosserDefect D upper n := by
  classical
  rw [rosser_defect_moment_eq_tail s D z (by linarith) hP]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases ht : D ≤ (n : ℝ) * z ^ 2
  · by_cases hc : 9 ≤ n.primeFactors.card
    · simp [ht, hc]
    · have hnp := (Nat.mem_divisors.mp hn).1
      have he := rosserDefect_zero_of_card_le_eight D z hz hD upper
        (s.prodPrimes_squarefree.squarefree_of_dvd hnp)
        (fun p hp => hP p (Nat.primeFactors_mono hnp s.prodPrimes_ne_zero hp)) (by omega)
      simp [ht, hc, he]
  · simp [ht]

end LeanLab.AlmostPrimeSums.Decomp1527b
