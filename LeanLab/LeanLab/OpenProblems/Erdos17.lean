import LeanLab.OpenProblems.PrimeCheck

/-!
# Erdős Problem 17, cluster primes, OPEN, sealed statement and closable sub-claims

Unit U-1603, 2026-11-02. AI wrote the Lean code. An OPEN problem, a target for the network, no
claim of progress on it.

Plain math: are there infinitely many primes `p` such that every even `n ≤ p - 3` is a difference
of two primes `q₁ - q₂` with `q₁, q₂ ≤ p`?

Source: T. F. Bloom, Erdős Problem #17, https://www.erdosproblems.com/17, fetched 2026-11-02, page
status OPEN, latest edit 28 December 2025, marked as not resolvable by a finite computation, with
the upper bounds of Blecksmith, Erdős and Selfridge and of Elsholtz. Guy, Unsolved Problems, C1.

Definition reused from google-deepmind/formal-conjectures, file
`FormalConjectures/ErdosProblems/17.lean`, `IsClusterPrime`, Copyright 2025 The Formal Conjectures
Authors, Apache-2.0, fetched 2026-11-02, as printed there. `Erdos17Statement` is FC's `erdos_17`.

Status of the sub-claims: KNOWN, none ORIGINAL. `oeis_a038133` checks a printed table.
`cluster_iff_composite` is an elementary reformulation, no literature search has been run on it,
so it is not called new.
-/

namespace LeanLab.OpenProblems.Erdos17

/-- As in formal-conjectures, Apache-2.0. -/
def IsClusterPrime (p : ℕ) : Prop :=
  p.Prime ∧ ∀ {n : ℕ}, Even n → (n : ℤ) ≤ (p - 3 : ℤ) →
    ∃ q₁ q₂ : ℕ, q₁.Prime ∧ q₂.Prime ∧ q₁ ≤ p ∧ q₂ ≤ p ∧ (n : ℤ) = (q₁ - q₂ : ℤ)

/-- **Erdős 17, OPEN, sealed.** Infinitely many cluster primes. A proof, or a proof of finiteness,
is new knowledge. -/
def Erdos17Statement : Prop := {p : ℕ | IsClusterPrime p}.Infinite

/-! ### Only odd composite `r = p - n` matter -/

/-- The condition at an odd composite `r`: some prime `q < r` has `p - r + q` prime. -/
def Unblocked (p r : ℕ) : Prop := ∃ q : ℕ, q.Prime ∧ q < r ∧ (p - r + q).Prime

/-- **PROVED, elementary.** For an odd prime `p`, being a cluster prime depends only on the odd
composite `r ≤ p`: when `r` is prime, `p - r` is already a difference `p - r`. -/
theorem cluster_iff_composite {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    IsClusterPrime p ↔ ∀ r : ℕ, Odd r → 3 ≤ r → r ≤ p → ¬ r.Prime → Unblocked p r := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨m, rfl⟩ := hodd
    omega
  constructor
  · rintro ⟨-, h⟩ r hr h3 hrp hnp
    have heven : Even (p - r) := by
      obtain ⟨a, rfl⟩ := hodd
      obtain ⟨b, rfl⟩ := hr
      exact ⟨a - b, by omega⟩
    obtain ⟨q₁, q₂, h1, h2, hq1, hq2, heq⟩ := h heven (by omega)
    have hne : q₂ ≠ r := fun e => hnp (e ▸ h2)
    have hlt : q₂ < r := by omega
    refine ⟨q₂, h2, hlt, ?_⟩
    have : p - r + q₂ = q₁ := by omega
    rwa [this]
  · intro h
    refine ⟨hp, fun {n} hn hle => ?_⟩
    have hrodd : Odd (p - n) := by
      obtain ⟨a, rfl⟩ := hodd
      obtain ⟨b, rfl⟩ := hn
      exact ⟨a - b, by omega⟩
    by_cases hr : (p - n).Prime
    · exact ⟨p, p - n, hp, hr, le_rfl, by omega, by omega⟩
    · obtain ⟨q, hq, hlt, hq1⟩ := h (p - n) hrodd (by omega) (by omega) hr
      refine ⟨p - (p - n) + q, q, hq1, hq, by omega, by omega, by omega⟩

/-- **PROVED, elementary.** For `p > 9`, a cluster prime has one of `p - 2, p - 4, p - 6` prime.
The case `r = 9`. It already explains 33 of the 51 printed terms of A038133. -/
theorem prime_near_of_cluster {p : ℕ} (hc : IsClusterPrime p) (hodd : Odd p) (h9 : 9 < p) :
    (p - 2).Prime ∨ (p - 4).Prime ∨ (p - 6).Prime := by
  obtain ⟨q, hq, hlt, hq1⟩ := (cluster_iff_composite hc.1 hodd).mp hc 9 (by decide) (by norm_num)
    (by omega) (by norm_num)
  have hq2 := hq.two_le
  interval_cases q
  · exfalso
    have heven : Even (p - 9 + 2) := by
      obtain ⟨a, rfl⟩ := hodd
      exact ⟨a - 3, by omega⟩
    have := (Nat.Prime.even_iff hq1).mp heven
    omega
  · exact Or.inr (Or.inr (by simpa [show p - 9 + 3 = p - 6 by omega] using hq1))
  · exact absurd hq (by norm_num)
  · exact Or.inr (Or.inl (by simpa [show p - 9 + 5 = p - 4 by omega] using hq1))
  · exact absurd hq (by norm_num)
  · exact Or.inl (by simpa [show p - 9 + 7 = p - 2 by omega] using hq1)
  · exact absurd hq (by norm_num)

/-! ### Vacuity -/

/-- `97` is not a cluster prime, the FC test and the first term of A038133, here as a corollary of
`prime_near_of_cluster`: `95`, `93` and `91` are composite. -/
theorem not_isClusterPrime_97 : ¬ IsClusterPrime 97 := fun h => by
  rcases prime_near_of_cluster h (by decide) (by norm_num) with h1 | h1 | h1 <;>
    exact absurd h1 (by norm_num)

/-- `n ≤ 2`, a positive instance, so the predicate is a proper part of the primes. -/
theorem isClusterPrime_5 : IsClusterPrime 5 := by
  refine (cluster_iff_composite (by norm_num) (by decide)).mpr ?_
  intro r hr h3 hr5 hnp
  interval_cases r
  · exact absurd Nat.prime_three hnp
  · exact absurd hr (by decide)
  · exact absurd Nat.prime_five hnp

/-! ### The printed table of A038133 -/

/-- `true` when every odd composite `r ≤ p` is unblocked, for `p < 28 * 28`. -/
def clusterB (p : ℕ) : Bool :=
  (List.range (p + 1)).all fun r =>
    decide (r % 2 = 0) || decide (r < 3) || primeB 28 r ||
      (List.range r).any fun q => primeB 28 q && primeB 28 (p - r + q)

/-- OEIS A038133, odd primes that are not cluster primes, DATA as printed, read 2026-11-02. -/
def a038133 : List ℕ :=
  [97, 127, 149, 191, 211, 223, 227, 229, 251, 257, 263, 269, 293, 307, 331, 337, 347, 349, 367,
   373, 379, 383, 397, 409, 419, 431, 457, 479, 487, 499, 521, 541, 547, 557, 563, 569, 587, 593,
   599, 631, 641, 673, 691, 701, 709, 719, 727, 733, 739, 743, 751]

theorem table_check : (List.range 752).all (fun p =>
    !(primeB 28 p && decide (p % 2 = 1)) || (clusterB p == !(a038133.contains p))) = true := by
  decide +kernel

theorem clusterB_iff {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hlt : p < 752) :
    IsClusterPrime p ↔ clusterB p = true := by
  have hB : ∀ {x : ℕ}, x ≤ p → x < 28 * 28 := fun h => by omega
  rw [cluster_iff_composite hp hodd]
  simp only [clusterB, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true, Bool.and_eq_true]
  constructor
  · intro h r hr
    have hrp : r ≤ p := by omega
    by_cases h2 : r % 2 = 0
    · exact Or.inl (Or.inl (Or.inl h2))
    by_cases h3 : r < 3
    · exact Or.inl (Or.inl (Or.inr h3))
    by_cases hpr : r.Prime
    · exact Or.inl (Or.inr ((primeB_iff (hB hrp)).mpr hpr))
    · obtain ⟨q, hq, hlt', hq1⟩ := h r (Nat.odd_iff.mpr (by omega)) (by omega) hrp hpr
      refine Or.inr ⟨q, hlt', (primeB_iff (by omega)).mpr hq, (primeB_iff (hB (by omega))).mpr hq1⟩
  · intro h r hr h3 hrp hnp
    rcases h r (by omega) with ((h1 | h1) | h1) | ⟨q, hlt', h1, h2⟩
    · have := Nat.odd_iff.mp hr
      omega
    · omega
    · exact absurd ((primeB_iff (hB hrp)).mp h1) hnp
    · exact ⟨q, (primeB_iff (by omega)).mp h1, hlt', (primeB_iff (hB (by omega))).mp h2⟩

/-- **Closable sub-claim, PROVED, KNOWN.** For odd primes `p ≤ 751`, the range of the printed
table, `p` is not a cluster prime exactly when `p` is listed in OEIS A038133, under the FC
definition. Checks a printed table and confirms that the sealed predicate means what the source
means. Instance of known data. -/
theorem oeis_a038133 {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hlt : p < 752) :
    ¬ IsClusterPrime p ↔ p ∈ a038133 := by
  have h := table_check
  simp only [List.all_eq_true, List.mem_range] at h
  have hc := h p hlt
  have h1 : primeB 28 p = true := (primeB_iff (by omega)).mpr hp
  have h2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  rw [clusterB_iff hp hodd hlt]
  simp only [h1, h2, decide_true, Bool.and_self, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc]
  simp

end LeanLab.OpenProblems.Erdos17

#print axioms LeanLab.OpenProblems.Erdos17.cluster_iff_composite
#print axioms LeanLab.OpenProblems.Erdos17.prime_near_of_cluster
#print axioms LeanLab.OpenProblems.Erdos17.not_isClusterPrime_97
#print axioms LeanLab.OpenProblems.Erdos17.isClusterPrime_5
#print axioms LeanLab.OpenProblems.Erdos17.oeis_a038133
