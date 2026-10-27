/-
P0073, Section 2, page 428. Eventual continuation for the prime input.
AI wrote this Lean code for CODEX task114. Goldbach is open.
This is not failure-freedom at every target.
-/
import LeanLab.Stein1965.Algorithm114

namespace LeanLab.Stein1965.Decomp114b

/-- Page 428: with an odd seed, the unbounded prime input always supplies
another basis element after finitely many skipped targets. -/
def PrimeContinuationClaim : Prop :=
  ∀ (p0 : ℕ) (B : List ℕ) (e : ℕ), (∃ b ∈ B, Odd b) → Even e →
    ∃ fuel a, findNew p0 B fuel e = some a ∧ a.Prime ∧ p0 ≤ a ∧ a ∉ B

/-- LEAF. Page 428: an arbitrarily large prime and an odd seed give a reachable
uncovered even target with an admissible candidate. Standard input: Euclid's theorem. -/
theorem leaf_reachable (p0 : ℕ) (B : List ℕ) (e : ℕ)
    (hseed : ∃ b ∈ B, Odd b) (he : Even e) :
    ∃ k a, covered B (e + 2 * k) = false ∧ bestA p0 B (e + 2 * k) = some a := by
  obtain ⟨b, hb, hbodd⟩ := hseed
  obtain ⟨q, hqbound, hqprime⟩ := Nat.exists_infinite_primes (p0 + e + 2 * B.sum + 3)
  have hqodd : Odd q := hqprime.odd_of_ne_two (by omega)
  have htarget := Nat.even_iff.mp (hqodd.add_odd hbodd)
  have heven := Nat.even_iff.mp he
  let k := (q + b - e) / 2
  have hstep : e + 2 * k = q + b := by dsimp [k]; omega
  have hc : covered B (e + 2 * k) = false := by
    apply covered_false_of_large
    omega
  have hmem : q ∈ (B.filterMap fun b =>
      if b < e + 2 * k && p0 ≤ e + 2 * k - b && primeB (e + 2 * k - b)
      then some (e + 2 * k - b) else none) :=
    (mem_candidates_iff p0 B (e + 2 * k) q).mpr
      ⟨hqprime, by omega, b, hb, hstep.symm⟩
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (List.isSome_max?_of_mem hmem)
  exact ⟨k, a, hc, (bestA_eq_max? p0 B (e + 2 * k)).trans ha⟩

/-- LEAF. Page 428: finite reachability gives sufficient search fuel. -/
theorem leaf_search (p0 : ℕ) (B : List ℕ) (e k a : ℕ)
    (hc : covered B (e + 2 * k) = false)
    (ha : bestA p0 B (e + 2 * k) = some a) :
    ∃ q, findNew p0 B (k + 1) e = some q := by
  exact findNew_complete p0 B (k + 1) e k a (by omega) hc ha

/-- LEAF. Equations 2.2 and 2.3: every returned value is a fresh admissible prime. -/
theorem leaf_fresh (p0 : ℕ) (B : List ℕ) (fuel e a : ℕ)
    (h : findNew p0 B fuel e = some a) : a.Prime ∧ p0 ≤ a ∧ a ∉ B := by
  exact findNew_sound p0 B fuel e a h

/-- Page 428, eventual continuation. Assembly without sorry. -/
theorem primeContinuation_assembled : PrimeContinuationClaim := by
  intro p0 B e hseed he
  obtain ⟨k, a, hc, ha⟩ := leaf_reachable p0 B e hseed he
  obtain ⟨q, hq⟩ := leaf_search p0 B e k a hc ha
  exact ⟨k + 1, q, hq, leaf_fresh p0 B (k + 1) e q hq⟩

end LeanLab.Stein1965.Decomp114b
