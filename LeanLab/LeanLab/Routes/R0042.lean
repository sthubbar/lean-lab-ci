/-
# R-0042, T3 MOONSHOT: the Busy Beaver route, Goldbach as non-halting of a search machine

Unit U-1384, PC run 20261021T1203Z-6472, route id R-0042. AI wrote this Lean code, Claude.
Checked only by the Lean kernel. Goldbach is OPEN and nothing here is progress on it.

Route. Binary Goldbach is a Π₁ sentence: it says a computable search over even N never
fails, so it is equivalent to non-halting of an explicit machine, Aaronson-Yedidia 2016.
The Busy Beaver programme, bbchallenge 2024, proves non-halting by certificate deciders:
cyclers, translated cyclers, backward reasoning and finite automata reduction, all of which
abstract the machine by a finite-state, eventually periodic invariant. The route asks
whether such a certificate class can see the Goldbach machine.

Facts proved here, all unconditional:
1. `gcheck_iff` and `goldbach_iff_gcheck`: the Π₁ normal form, Goldbach iff a Bool check
   holds at every even N ≥ 4.
2. `refutation_finite`: a failure of Goldbach is a single N where the check returns false,
   a finite certificate.
3. `primes_not_eventually_periodic`: no exact finite-state description of the primes.
4. `abstraction_ambiguous`: the barrier. Any sound abstraction of the primality test by
   two eventually periodic sets A ⊇ primes and B ⊇ nonprimes answers BOTH ways on a whole
   infinite arithmetic progression beyond every point. So a periodic abstraction of the
   machine branches into the composite outcome on infinitely many inputs, and the needed
   non-halting certificate must carry non-periodic arithmetic information.
5. `periodic_cover_nonprimes`: stronger, an eventually periodic B ⊇ nonprimes is all of
   [max M 2, ∞), so a periodic abstraction may answer composite at every large p.
Numerics: Routes/numerics/r0042_test.py and r0042_test.out.
No hypotheses are cited, so nothing here is CONDITIONAL.
-/
import Mathlib
import LeanLab.Common.Goldbach

namespace LeanLab.Routes.R0042

open LeanLab

/-- The machine's inner loop: search p ≤ N with p and N - p both prime. -/
def gcheck (N : ℕ) : Bool :=
  (List.range (N + 1)).any fun p => decide p.Prime && decide (N - p).Prime

theorem gcheck_iff (N : ℕ) : gcheck N = true ↔ IsGoldbachSum N := by
  unfold gcheck IsGoldbachSum
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p, hp, h⟩
    rw [List.mem_range] at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨p, N - p, h.1, h.2, by omega⟩
  · rintro ⟨p, q, hp, hq, rfl⟩
    refine ⟨p, List.mem_range.2 (by omega), ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.add_sub_cancel_left]
    exact ⟨hp, hq⟩

/-- Π₁ normal form: binary Goldbach iff the check never fails on 2k + 4. -/
theorem goldbach_iff_gcheck : BinaryGoldbach ↔ ∀ k : ℕ, gcheck (2 * k + 4) = true := by
  unfold BinaryGoldbach
  constructor
  · intro h k
    rw [gcheck_iff]
    exact h _ ⟨k + 2, by ring⟩ (by omega)
  · intro h n hn h4
    obtain ⟨m, rfl⟩ := hn
    have := h (m - 2)
    rw [gcheck_iff] at this
    have e : 2 * (m - 2) + 4 = m + m := by omega
    rwa [e] at this

/-- A refutation of Goldbach is one finite, decidable certificate. -/
theorem refutation_finite (h : ¬ BinaryGoldbach) : ∃ k : ℕ, gcheck (2 * k + 4) = false := by
  rw [goldbach_iff_gcheck] at h
  push_neg at h
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by simpa using hk⟩

/-- No exact finite-state description of the primes: they are not eventually periodic. -/
theorem primes_not_eventually_periodic (d M : ℕ) (hd : 0 < d) :
    ¬ ∀ n, M ≤ n → (n.Prime ↔ (n + d).Prime) := by
  intro h
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + 2)
  have step : ∀ k, (p + k * d).Prime := by
    intro k
    induction k with
    | zero => simpa using hp
    | succ k ih =>
      have := (h (p + k * d) (by omega)).1 ih
      simpa [Nat.succ_mul, add_assoc] using this
  have hc := step p
  have e : p + p * d = p * (1 + d) := by ring
  rw [e] at hc
  have hp2 : 2 ≤ p := hp.two_le
  rcases Nat.prime_mul_iff.1 hc with ⟨_, h1⟩ | ⟨_, h1⟩
  · omega
  · omega

/-- **Abstraction barrier.** If A over-approximates the primes, B the nonprimes, and both
are eventually periodic with common period d, then beyond every K there is a whole
progression n + k d on which the abstract test answers both prime and composite. -/
theorem abstraction_ambiguous (A B : Set ℕ) (d M : ℕ) (hd : 0 < d)
    (hA : ∀ n, M ≤ n → (n ∈ A ↔ n + d ∈ A)) (hB : ∀ n, M ≤ n → (n ∈ B ↔ n + d ∈ B))
    (hPA : ∀ n, n.Prime → n ∈ A) (hPB : ∀ n, ¬ n.Prime → n ∈ B) :
    ∀ K, ∃ n, K ≤ n ∧ ∀ k : ℕ, n + k * d ∈ A ∧ n + k * d ∈ B := by
  intro K
  by_contra hno
  push_neg at hno
  -- beyond L = max K M, A ∩ B is empty
  have prog : ∀ n, M ≤ n → n ∈ A → n ∈ B → ∀ k : ℕ, n + k * d ∈ A ∧ n + k * d ∈ B := by
    intro n hn ha hb k
    induction k with
    | zero => simpa using ⟨ha, hb⟩
    | succ k ih =>
      have hm : M ≤ n + k * d := by omega
      refine ⟨?_, ?_⟩
      · have := (hA _ hm).1 ih.1
        simpa [Nat.succ_mul, add_assoc] using this
      · have := (hB _ hm).1 ih.2
        simpa [Nat.succ_mul, add_assoc] using this
  have empty : ∀ n, max K M ≤ n → ¬ (n ∈ A ∧ n ∈ B) := by
    rintro n hn ⟨ha, hb⟩
    obtain ⟨k, hk⟩ := hno n (le_of_max_le_left hn)
    have := prog n (le_of_max_le_right hn) ha hb k
    exact hk this.1 this.2
  have exact : ∀ n, max K M ≤ n → (n ∈ A ↔ n.Prime) := by
    intro n hn
    constructor
    · intro ha
      by_contra hp
      exact empty n hn ⟨ha, hPB n hp⟩
    · exact hPA n
  apply primes_not_eventually_periodic d (max K M) hd
  intro n hn
  rw [← exact n hn, ← exact (n + d) (by omega)]
  exact hA n (le_trans (le_max_right K M) hn)

/-- **Composite branch everywhere.** An eventually periodic B containing every nonprime
contains every n ≥ max M 2: each class mod d holds the composite n(1 + d). So a periodic
abstraction may answer composite at every large p, and its abstract search can always
reach the fail state; it certifies nothing about Goldbach. -/
theorem periodic_cover_nonprimes (B : Set ℕ) (d M : ℕ) (hd : 0 < d)
    (hB : ∀ n, M ≤ n → (n ∈ B ↔ n + d ∈ B)) (hPB : ∀ n, ¬ n.Prime → n ∈ B) :
    ∀ n, max M 2 ≤ n → n ∈ B := by
  intro n hn
  have back : ∀ k : ℕ, n + k * d ∈ B → n ∈ B := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro h
      apply ih
      have hm : M ≤ n + k * d := by have := le_of_max_le_left hn; omega
      rw [hB _ hm]
      simpa [Nat.succ_mul, add_assoc] using h
  apply back n
  apply hPB
  have e : n + n * d = n * (1 + d) := by ring
  rw [e]
  have h2 : 2 ≤ n := le_of_max_le_right hn
  exact Nat.not_prime_mul (by omega) (by omega)

/-! Vacuity and instance checks. -/

/-- The check is not vacuous: it accepts 28 = 5 + 23 and rejects the odd number 11. -/
example : gcheck 28 = true := by decide
example : gcheck 11 = false := by decide

/-- The hypotheses of `abstraction_ambiguous` are satisfiable: the trivial abstraction
A = B = univ meets them, and then every n is ambiguous. -/
theorem vacuity_abstraction :
    ∀ K, ∃ n, K ≤ n ∧ ∀ k : ℕ, n + k * 6 ∈ (Set.univ : Set ℕ) ∧ n + k * 6 ∈ (Set.univ : Set ℕ) :=
  abstraction_ambiguous Set.univ Set.univ 6 0 (by norm_num) (by simp) (by simp) (by simp)
    (by simp)

/-- A nontrivial instance: A = {2} ∪ odd numbers ⊇ primes, B = univ, period 2. -/
theorem vacuity_odd :
    ∀ K, ∃ n, K ≤ n ∧ ∀ k : ℕ, n + k * 2 ∈ {m : ℕ | m = 2 ∨ m % 2 = 1} ∧
      n + k * 2 ∈ (Set.univ : Set ℕ) := by
  refine abstraction_ambiguous _ _ 2 3 (by norm_num) ?_ (by simp) ?_ (by simp)
  · intro n hn
    simp only [Set.mem_setOf_eq]
    omega
  · intro n hn
    exact hn.eq_two_or_odd

end LeanLab.Routes.R0042

#print axioms LeanLab.Routes.R0042.gcheck_iff
#print axioms LeanLab.Routes.R0042.goldbach_iff_gcheck
#print axioms LeanLab.Routes.R0042.refutation_finite
#print axioms LeanLab.Routes.R0042.primes_not_eventually_periodic
#print axioms LeanLab.Routes.R0042.abstraction_ambiguous
#print axioms LeanLab.Routes.R0042.periodic_cover_nonprimes
#print axioms LeanLab.Routes.R0042.vacuity_abstraction
#print axioms LeanLab.Routes.R0042.vacuity_odd
