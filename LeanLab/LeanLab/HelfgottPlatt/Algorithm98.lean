/-
P0006, page 2, Section 2, bounded primality test and its limitations.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottPlatt.HelfgottPlattU1455ProthIff
import LeanLab.HelfgottPlatt.HelfgottPlattU1511Rows

namespace LeanLab.HelfgottPlatt.Task98

/-- Page 2, steps 3 and 4. Search in increasing order for the first prime at most B
whose Jacobi symbol over N is minus one. -/
def firstWitness (N B : ℕ) : Option ℕ :=
  (List.range (B + 1)).find? (fun (a : ℕ) => decide (a.Prime ∧ jacobiSym a N = -1))

/-- Page 2, steps 5 and 6. Return false when no witness was found, otherwise test
congruence 2.2. The Proth hypotheses are supplied to the correctness theorems. -/
def boundedTest (k m B : ℕ) : Bool :=
  let N := k * 2 ^ (m + 1) + 1
  match firstWitness N B with
  | none => false
  | some a => decide ((a : ZMod N) ^ ((N - 1) / 2) = -1)

/-- Page 2, final sentence of Section 2. The algorithm never returns a false positive. -/
theorem boundedTest_sound {k m B : ℕ} (hk0 : 0 < k) (hk : k < 2 ^ (m + 1))
    (h : boundedTest k m B = true) : (k * 2 ^ (m + 1) + 1).Prime := by
  unfold boundedTest at h
  cases hw : firstWitness (k * 2 ^ (m + 1) + 1) B with
  | none => simp [hw] at h
  | some a =>
    have ha := List.find?_some (show
      (List.range (B + 1)).find? (fun (a : ℕ) =>
        decide (a.Prime ∧ jacobiSym a (k * 2 ^ (m + 1) + 1) = -1)) = some a from hw)
    have hJ : jacobiSym a (k * 2 ^ (m + 1) + 1) = -1 := (of_decide_eq_true ha).2
    exact U1455.theorem2_3 hk0 hk rfl hJ (by simpa [hw] using h)

/-- Page 2, steps 3 and 4. The selected witness is the least prime at most B
whose Jacobi symbol is minus one. -/
theorem firstWitness_eq_some {N B a : ℕ} :
    firstWitness N B = some a ↔
      a.Prime ∧ a ≤ B ∧ jacobiSym a N = -1 ∧
        ∀ q, q < a → q.Prime → jacobiSym q N ≠ -1 := by
  simp only [firstWitness, List.find?_range_eq_some, decide_eq_true_eq,
    List.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨hp, hJ⟩, hB, hmin⟩
    refine ⟨hp, hB, hJ, ?_⟩
    intro q hq hqp hqJ
    have h := hmin q hq
    simp [hqp, hqJ] at h
  · rintro ⟨hp, hB, hJ, hmin⟩
    refine ⟨⟨hp, hJ⟩, hB, ?_⟩
    intro q hq
    by_cases hqp : q.Prime
    · simp [hqp, hmin q hq hqp]
    · simp [hqp]

/-- Page 2, the paragraph after the algorithm. For a Proth prime, acceptance is
exactly the existence of a prime witness within the chosen bound. -/
theorem boundedTest_prime_iff {k m B : ℕ} (hk0 : 0 < k)
    (hp : (k * 2 ^ (m + 1) + 1).Prime) :
    boundedTest k m B = true ↔
      ∃ a : ℕ, a.Prime ∧ a ≤ B ∧ jacobiSym a (k * 2 ^ (m + 1) + 1) = -1 := by
  have h2 : k * 2 ^ (m + 1) + 1 ≠ 2 := by
    have hpow : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [pow_succ]
    nlinarith
  cases hw : firstWitness (k * 2 ^ (m + 1) + 1) B with
  | none =>
    constructor
    · intro h
      simp [boundedTest, hw] at h
    · rintro ⟨a, hap, haB, haJ⟩
      have hnone := List.find?_eq_none.mp hw a (List.mem_range.mpr (by omega))
      simp [hap, haJ] at hnone
  | some a =>
    obtain ⟨hap, haB, haJ, _⟩ := firstWitness_eq_some.mp hw
    have hpow := U1455.converse hp h2 haJ
    constructor
    · intro _
      exact ⟨a, hap, haB, haJ⟩
    · intro _
      simpa [boundedTest, hw] using hpow

/-- Page 2, the paragraph after the algorithm. A prime is rejected exactly when
all primes at most B fail the Jacobi witness condition. -/
theorem boundedTest_false_iff {k m B : ℕ} (hk0 : 0 < k)
    (hp : (k * 2 ^ (m + 1) + 1).Prime) :
    boundedTest k m B = false ↔
      ∀ a : ℕ, a.Prime → a ≤ B → jacobiSym a (k * 2 ^ (m + 1) + 1) ≠ -1 := by
  constructor
  · intro hfalse a hap haB haJ
    have htrue := (boundedTest_prime_iff hk0 hp).mpr ⟨a, hap, haB, haJ⟩
    simp [hfalse] at htrue
  · intro hnone
    cases htest : boundedTest k m B with
    | false => rfl
    | true =>
      obtain ⟨a, hap, haB, haJ⟩ := (boundedTest_prime_iff hk0 hp).mp htest
      exact False.elim (hnone a hap haB haJ)

/-- Page 2, false negative mechanism. When the exponent is at least 3, the
only candidate at bound 2 has Jacobi symbol one, so the test always rejects. -/
theorem boundedTest_two (k m : ℕ) : boundedTest k (m + 2) 2 = false := by
  have hJ : jacobiSym 2 (k * 2 ^ (m + 2 + 1) + 1) = 1 := by
    simpa [Nat.add_assoc] using U1511.jacobi_two_proth k m
  simp [boundedTest, firstWitness, show List.range (2 + 1) = [0, 1, 2] by decide,
    List.find?, hJ, Nat.not_prime_zero, Nat.not_prime_one]

/-- Page 2, the two correctness claims after the algorithm, combined.
Acceptance means primality together with the availability of a small witness. -/
theorem boundedTest_correct {k m B : ℕ} (hk0 : 0 < k) (hk : k < 2 ^ (m + 1)) :
    boundedTest k m B = true ↔
      (k * 2 ^ (m + 1) + 1).Prime ∧
        ∃ a : ℕ, a.Prime ∧ a ≤ B ∧ jacobiSym a (k * 2 ^ (m + 1) + 1) = -1 := by
  constructor
  · intro ht
    have hp := boundedTest_sound hk0 hk ht
    exact ⟨hp, (boundedTest_prime_iff hk0 hp).mp ht⟩
  · rintro ⟨hp, hw⟩
    exact (boundedTest_prime_iff hk0 hp).mpr hw

/-- Page 2, vacuity instances for all branches. Thirteen is accepted at bound 2.
Seventeen is prime but rejected at bound 2 and accepted at bound 3. -/
theorem boundedTest_instances :
    firstWitness 13 2 = some 2 ∧ (13 : ℕ).Prime ∧ boundedTest 3 1 2 = true ∧
    firstWitness 17 2 = none ∧ (17 : ℕ).Prime ∧ boundedTest 1 3 2 = false ∧
    firstWitness 17 3 = some 3 ∧ boundedTest 1 3 3 = true := by
  decide +kernel

end LeanLab.HelfgottPlatt.Task98
