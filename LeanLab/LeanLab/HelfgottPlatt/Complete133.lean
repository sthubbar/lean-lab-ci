/-
P0006 page 2, Section 2, bounded test and false negatives. Searching all
primes below an odd prime is sufficient. This is a completeness boundary,
not the fixed small bound used by the paper. AI wrote the Lean code.
Binary Goldbach is open.
-/
import LeanLab.HelfgottPlatt.Algorithm98

namespace LeanLab.HelfgottPlatt.Task133

/-- Page 2, Section 2. Factoring a positive quadratic nonresidue gives a
prime witness no larger than that nonresidue. This is a standard consequence
of multiplicativity, used for the exhaustive bound comparison. -/
theorem prime_witness_of_nonresidue {N b : ℕ} (hb : 0 < b) (hJ : jacobiSym b N = -1) :
    ∃ q : ℕ, q.Prime ∧ q ≤ b ∧ jacobiSym q N = -1 := by
  have hcast : (b : ℤ) = (b.primeFactorsList.map (fun (q : ℕ) => (q : ℤ))).prod := by
    rw [← Nat.cast_list_prod, Nat.prod_primeFactorsList hb.ne']
  rw [hcast, jacobiSym.list_prod_left] at hJ
  obtain ⟨a, ha, haJ⟩ := List.mem_map.mp (List.neg_one_mem_of_prod_eq_neg_one hJ)
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
  exact ⟨q, Nat.prime_of_mem_primeFactorsList hq,
    Nat.le_of_dvd hb (Nat.dvd_of_mem_primeFactorsList hq), haJ⟩

/-- Page 2, the false negative discussion. An odd prime always has a
prime quadratic nonresidue strictly below itself. This justifies an
exhaustive witness bound, not the paper's fixed small bound. -/
theorem prime_witness_lt {N : ℕ} (hp : N.Prime) (h2 : N ≠ 2) :
    ∃ q : ℕ, q.Prime ∧ q < N ∧ jacobiSym q N = -1 := by
  haveI : Fact N.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare (F := ZMod N)
    (by simpa only [ZMod.ringChar_zmod_n] using h2)
  have hJ : jacobiSym x.val N = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
    simpa using hx
  have hb : 0 < x.val := by
    by_contra h
    have hz : x.val = 0 := by omega
    rw [hz, Nat.cast_zero, jacobiSym.zero_left hp.one_lt] at hJ
    norm_num at hJ
  obtain ⟨q, hq, hqb, hqJ⟩ := prime_witness_of_nonresidue hb hJ
  exact ⟨q, hq, lt_of_le_of_lt hqb (ZMod.val_lt x), hqJ⟩

/-- Page 2, false negative boundary. Testing every prime below the Proth
candidate gives a complete test. This bound grows with N and is not the
fixed bound used by the implementation in the paper. -/
theorem boundedTest_exhaustive {k m B : ℕ} (hk0 : 0 < k) (hk : k < 2 ^ (m + 1))
    (hB : k * 2 ^ (m + 1) ≤ B) :
    Task98.boundedTest k m B = true ↔ (k * 2 ^ (m + 1) + 1).Prime := by
  constructor
  · exact Task98.boundedTest_sound hk0 hk
  · intro hp
    apply (Task98.boundedTest_prime_iff hk0 hp).mpr
    have htwo : k * 2 ^ (m + 1) + 1 ≠ 2 := by
      have hpow : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      rw [pow_succ]
      nlinarith
    obtain ⟨q, hq, hqlt, hqJ⟩ := prime_witness_lt hp htwo
    exact ⟨q, hq, by omega, hqJ⟩

/-- Page 2, completeness boundary instances. Seventeen fails at the small
bound two and succeeds at the exhaustive bound sixteen. The composite
twenty five is rejected even at its exhaustive bound. -/
theorem exhaustive_instances :
    (17 : ℕ).Prime ∧ Task98.boundedTest 1 3 2 = false ∧
      Task98.boundedTest 1 3 16 = true ∧ Task98.boundedTest 3 2 24 = false := by
  decide +kernel

end LeanLab.HelfgottPlatt.Task133
