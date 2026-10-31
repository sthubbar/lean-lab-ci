/-
AI wrote this Lean code for CODEX task128.
P0073, Section 2, page 428, continuation for infinite prime inputs.
The generated output has unbounded length. No Goldbach coverage is asserted.
Goldbach is open.
-/
import LeanLab.SteinStein1965.Growth128
import LeanLab.SteinStein1965.Seeds

namespace LeanLab.SteinStein1965

/-- Section 3, page 428: the odd-prime input above any cutoff is unbounded. -/
theorem prime_input_unbounded128 (p0 : ℕ) :
    ∀ T, ∃ a, T < a ∧ primeA p0 a = true ∧ Odd a := by
  intro T
  obtain ⟨a, ha, hp⟩ := Nat.exists_infinite_primes (max (T + 1) (max p0 3))
  have hT : T < a := by omega
  have hp0 : p0 ≤ a := by omega
  have h3 : 3 ≤ a := by omega
  exact ⟨a, hT, (primeA_iff p0 a).mpr ⟨hp0, Or.inr ⟨by omega, hp⟩⟩,
    hp.odd_of_ne_two (by omega)⟩

/-- Section 2, pages 427 and 428: split the scan into an old and a new interval. -/
theorem evensIn_append128 (lo N M : ℕ) (hlo : lo ≤ N + 1) (hNM : N ≤ M) :
    evensIn lo M = evensIn lo N ++ evensIn (N + 1) M := by
  unfold evensIn
  rw [show M + 1 - lo = (N + 1 - lo) + (M + 1 - (N + 1)) by omega,
    ← List.range'_append, List.filter_append]
  rw [show lo + 1 * (N + 1 - lo) = N + 1 by omega]

/-- Page 428: extending the upper limit continues the same finite prime run. -/
theorem sPrime_continuation128 (p0 N M : ℕ) (hN : 2 * p0 ≤ N) (hNM : N ≤ M) :
    sPrime p0 M = (evensIn (N + 1) M).foldl (step (primeA p0)) (sPrime p0 N) := by
  unfold sPrime sAlg
  rw [evensIn_append128 (2 * p0) N M (by omega) hNM, List.foldl_append]

/-- Page 428: every finite prime run can be extended so that it has more output elements. -/
theorem prime_eventual_growth128 (p0 N : ℕ) (hpos : 1 ≤ p0) (hN : 2 * p0 ≤ N) :
    ∃ M, N < M ∧ (sPrime p0 N).1.length < (sPrime p0 M).1.length := by
  have hpre : [p0, nextA p0] <+: (sPrime p0 N).1 :=
    scan_basis_prefix128 (primeA p0) (evensIn (2 * p0) N) ([p0, nextA p0], [])
  have hb : nextA p0 ∈ (sPrime p0 N).1 := hpre.sublist.subset (by simp)
  obtain ⟨M, hM, hg⟩ := eventual_growth128 (primeA p0) (sPrime p0 N) (nextA p0) N
    hb (nextA_odd p0 hpos) (prime_input_unbounded128 p0)
  exact ⟨M, hM, by rw [sPrime_continuation128 p0 N M hN (by omega)]; exact hg⟩

/-- Page 428: the lengths of the finite prime S-sequences are unbounded. -/
theorem prime_output_unbounded128 (p0 : ℕ) (hpos : 1 ≤ p0) :
    ∀ k, ∃ N, 2 * p0 ≤ N ∧ k < (sPrime p0 N).1.length := by
  intro k
  induction k with
  | zero =>
    refine ⟨2 * p0, le_rfl, ?_⟩
    have hpre : [p0, nextA p0] <+: (sPrime p0 (2 * p0)).1 :=
      scan_basis_prefix128 (primeA p0) (evensIn (2 * p0) (2 * p0)) ([p0, nextA p0], [])
    have hh := hpre.length_le
    simp only [List.length_cons, List.length_nil] at hh
    omega
  | succ k ih =>
    obtain ⟨N, hN, hk⟩ := ih
    obtain ⟨M, hM, hg⟩ := prime_eventual_growth128 p0 N hpos hN
    exact ⟨M, by omega, by omega⟩

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.prime_input_unbounded128
#print axioms LeanLab.SteinStein1965.evensIn_append128
#print axioms LeanLab.SteinStein1965.sPrime_continuation128
#print axioms LeanLab.SteinStein1965.prime_eventual_growth128
#print axioms LeanLab.SteinStein1965.prime_output_unbounded128
