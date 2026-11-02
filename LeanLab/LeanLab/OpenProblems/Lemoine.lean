import LeanLab.OpenProblems.PrimeCheck

/-!
# Lemoine's conjecture, also Levy's conjecture, OPEN, sealed statement and closable sub-claims

Unit U-1603, 2026-11-02. AI wrote the Lean code. An OPEN problem, a target for the network, no
claim of progress on it.

Plain math: every odd integer greater than 5 is `p + 2 q` with `p` and `q` prime.

Source: https://en.wikipedia.org/wiki/Lemoine%27s_conjecture, fetched 2026-11-02, states it as
unproven, verified to 10^9 by Corbitt, a June 2019 blog claim to 10^10, and a 2017 claimed proof by
Agama and Gensel found flawed. OEIS A046927, https://oeis.org/A046927, fetched 2026-11-02, gives the
representation count, with a b-file for `n ≤ 10000` by T. D. Noe. Guy, Unsolved Problems, C1.

formal-conjectures: NOT CONFIRMED. No FC file for Lemoine could be confirmed or ruled out. The
repository landing page does not name Lemoine or Levy, a web search found no such file, and the
`FormalConjectures/Wikipedia` tree listing was refused by robots rules on 2026-11-01. That refusal
was not worked around. Nothing here is copied from FC.

Status of the sub-claims: all KNOWN, none ORIGINAL. The finite range lies far below the published
10^9 and is the printed b-file of A046927, so this checks a printed table and extends nothing.
-/

namespace LeanLab.OpenProblems.Lemoine

/-- `n` is a prime plus twice a prime. -/
def IsLemoine (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + 2 * q

/-- **Lemoine's conjecture, OPEN, sealed.** A proof or a counterexample is new knowledge. -/
def LemoineConjecture : Prop := ∀ n : ℕ, Odd n → 5 < n → IsLemoine n

/-- The tail form: Lemoine for every odd `n > N`. -/
def LemoineAbove (N : ℕ) : Prop := ∀ n : ℕ, Odd n → N < n → IsLemoine n

/-! ### Vacuity: the predicate is neither always true nor always false, and 5 is sharp -/

theorem isLemoine_7 : IsLemoine 7 := ⟨3, 2, Nat.prime_three, Nat.prime_two, rfl⟩

theorem not_isLemoine_5 : ¬ IsLemoine 5 := by
  rintro ⟨p, q, hp, hq, h⟩
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  omega

/-! ### The kernel count, matched to the printed table of A046927 -/

/-- Number of primes `q` with `2 n + 1 - 2 q` prime and `2 q < 2 n + 1`, for `n < 20000`. -/
def repCount (n : ℕ) : ℕ :=
  ((List.range (n + 1)).filter fun q =>
    primeB 142 q && primeB 142 (2 * n + 1 - 2 * q)).length

/-- OEIS A046927, DATA as printed, `a(0)` to `a(91)`, read 2026-11-02. -/
def a046927 : List ℕ :=
  [0, 0, 0, 1, 2, 2, 2, 2, 4, 2, 3, 3, 3, 4, 4, 2, 5, 3, 4, 4, 5, 4, 6, 4, 4, 7, 5, 3, 7, 3, 3, 7,
   7, 5, 7, 4, 4, 8, 7, 5, 8, 4, 7, 8, 7, 4, 11, 5, 6, 9, 6, 5, 12, 6, 6, 10, 8, 6, 11, 7, 5, 11,
   8, 6, 10, 6, 6, 13, 8, 5, 13, 6, 9, 12, 8, 6, 14, 8, 6, 11, 10, 9, 16, 5, 8, 13, 9, 9, 14, 7,
   6, 14]

/-- The Lean count equals the printed OEIS table, a check that `repCount` means what A046927
means. Checks a printed table, KNOWN. -/
theorem repCount_eq_a046927 : (List.range 92).map repCount = a046927 := by decide +kernel

/-! ### The base range: the b-file of A046927 -/

/-- Least-prime list used as the search for `q`, all primes up to 181, the largest least `q` in the
b-file range, reached at `n = 14419`. -/
def smallQ : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
   101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181]

/-- Bool form of the base case on one block: `i ∈ [a, a + 1000)` with `n = 2 (i + 3) + 1`. -/
def blockCheck (a : ℕ) : Bool :=
  (List.range 1000).all fun j =>
    let n := 2 * (a + j + 3) + 1
    smallQ.any fun q => decide (2 * q < n) && primeB 142 (n - 2 * q)

theorem block0 : blockCheck 0 = true := by decide +kernel
theorem block1 : blockCheck 1000 = true := by decide +kernel
theorem block2 : blockCheck 2000 = true := by decide +kernel
theorem block3 : blockCheck 3000 = true := by decide +kernel
theorem block4 : blockCheck 4000 = true := by decide +kernel
theorem block5 : blockCheck 5000 = true := by decide +kernel
theorem block6 : blockCheck 6000 = true := by decide +kernel
theorem block7 : blockCheck 7000 = true := by decide +kernel
theorem block8 : blockCheck 8000 = true := by decide +kernel
theorem block9 : blockCheck 9000 = true := by decide +kernel

theorem blocks (t : ℕ) (ht : t < 10) : blockCheck (1000 * t) = true := by
  interval_cases t
  exacts [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9]

theorem smallQ_prime : ∀ q ∈ smallQ, q.Prime := by
  have hlt : ∀ q ∈ smallQ, q < 182 * 182 := by decide +kernel
  have hb : ∀ q ∈ smallQ, primeB 182 q = true := by decide +kernel
  exact fun q hq => (primeB_iff (hlt q hq)).mp (hb q hq)

/-- **Closable sub-claim, PROVED, KNOWN.** Every odd `n` with `5 < n ≤ 20001` is `p + 2 q`, that is
`A046927(i) > 0` for `3 ≤ i ≤ 10000`, the range of its b-file, with `q ≤ 181`. Instance of known
data, far below the published 10^9. -/
theorem lemoine_le_20001 (n : ℕ) (hodd : Odd n) (h5 : 5 < n) (hn : n ≤ 20001) : IsLemoine n := by
  obtain ⟨m, rfl⟩ := hodd
  have ht : (m - 3) / 1000 < 10 := by omega
  have hc := blocks _ ht
  simp only [blockCheck, List.all_eq_true, List.mem_range, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨q, hq, hlt, hp⟩ := hc ((m - 3) % 1000) (Nat.mod_lt _ (by norm_num))
  have hm : 1000 * ((m - 3) / 1000) + (m - 3) % 1000 + 3 = m := by omega
  rw [hm] at hlt hp
  have hbound : 2 * m + 1 - 2 * q < 142 * 142 := by omega
  exact ⟨2 * m + 1 - 2 * q, q, (primeB_iff hbound).mp hp, smallQ_prime q hq, by omega⟩

/-- **Reduction, PROVED.** Lemoine's conjecture is equivalent to its tail above 20001. Any future
theorem for all large `n` with threshold at most 20001 finishes the conjecture. -/
theorem lemoine_iff_above : LemoineConjecture ↔ LemoineAbove 20001 := by
  constructor
  · intro h n hodd hn
    exact h n hodd (by omega)
  · intro h n hodd h5
    by_cases hn : n ≤ 20001
    · exact lemoine_le_20001 n hodd h5 hn
    · exact h n hodd (by omega)

/-- Lemoine gives a sum of three primes, the implication to weak Goldbach stated on the source
page. Elementary, KNOWN. -/
theorem three_primes_of_isLemoine {n : ℕ} (h : IsLemoine n) :
    ∃ a b c : ℕ, a.Prime ∧ b.Prime ∧ c.Prime ∧ n = a + b + c := by
  obtain ⟨p, q, hp, hq, rfl⟩ := h
  exact ⟨p, q, q, hp, hq, hq, by ring⟩

end LeanLab.OpenProblems.Lemoine

#print axioms LeanLab.OpenProblems.Lemoine.not_isLemoine_5
#print axioms LeanLab.OpenProblems.Lemoine.repCount_eq_a046927
#print axioms LeanLab.OpenProblems.Lemoine.lemoine_le_20001
#print axioms LeanLab.OpenProblems.Lemoine.lemoine_iff_above
#print axioms LeanLab.OpenProblems.Lemoine.three_primes_of_isLemoine
