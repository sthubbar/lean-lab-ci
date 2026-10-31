/-
P0006 page 2, Section 3 step 4. The fallback selects the greatest prime
strictly below the cutoff. Strict advancement requires a new prime in that
interval. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottPlatt.Window98

namespace LeanLab.HelfgottPlatt.Task133

/-- Page 2, Section 3 step 4. The largest prime strictly below M, or zero
when the prime set is empty. This is a specification of the fallback. -/
def fallbackPrime (M : ℕ) : ℕ :=
  ((Finset.range M).filter Nat.Prime).sup id

/-- Page 2, Section 3 step 4. Above cutoff two the fallback is a prime
below the cutoff and dominates every other prime below it. -/
theorem fallbackPrime_spec {M : ℕ} (hM : 2 < M) :
    (fallbackPrime M).Prime ∧ fallbackPrime M < M ∧
      ∀ q : ℕ, q.Prime → q < M → q ≤ fallbackPrime M := by
  have hmem : 2 ∈ (Finset.range M).filter Nat.Prime :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hM, Nat.prime_two⟩
  have hs := Finset.sup_mem_of_nonempty (f := id) ⟨2, hmem⟩
  have hm : fallbackPrime M ∈ (Finset.range M).filter Nat.Prime := by
    simpa [fallbackPrime] using hs
  obtain ⟨hlt, hp⟩ := Finset.mem_filter.mp hm
  exact ⟨hp, Finset.mem_range.mp hlt, fun q hq hqM =>
    Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqM, hq⟩)⟩

/-- Page 2, Section 3 step 4. A positive search width includes the current
prime among the fallback candidates, so the fallback never decreases it. -/
theorem fallbackPrime_ge {N Δ : ℕ} (hp : N.Prime) (hΔ : 0 < Δ) :
    N ≤ fallbackPrime (N + Δ) := by
  have hM : 2 < N + Δ := by have := hp.two_le; omega
  exact (fallbackPrime_spec hM).2.2 N hp (by omega)

/-- Page 2, Section 3 step 4. Strict advancement is equivalent to a prime
strictly between the current rung and the strict cutoff. -/
theorem fallbackPrime_advances_iff {N Δ : ℕ} (hp : N.Prime) (hΔ : 0 < Δ) :
    N < fallbackPrime (N + Δ) ↔
      ∃ q : ℕ, q.Prime ∧ N < q ∧ q < N + Δ := by
  have hM : 2 < N + Δ := by have := hp.two_le; omega
  obtain ⟨hq, hqM, hmax⟩ := fallbackPrime_spec hM
  constructor
  · intro h
    exact ⟨fallbackPrime (N + Δ), hq, h, hqM⟩
  · rintro ⟨q, hqp, hNq, hqM⟩
    exact lt_of_lt_of_le hNq (hmax q hqp hqM)

/-- Page 2, Section 3 step 4. The fallback repeats the current prime
exactly when no prime lies in the open search interval. -/
theorem fallbackPrime_stagnates_iff {N Δ : ℕ} (hp : N.Prime) (hΔ : 0 < Δ) :
    fallbackPrime (N + Δ) = N ↔
      ¬ ∃ q : ℕ, q.Prime ∧ N < q ∧ q < N + Δ := by
  have hge := fallbackPrime_ge hp hΔ
  rw [← fallbackPrime_advances_iff hp hΔ, not_lt]
  exact ⟨fun h => h.le, fun h => le_antisymm h hge⟩

/-- Page 2, Section 3 step 4. A new prime below the strict cutoff makes
the fallback a certified sharp step when the spacing is even. -/
theorem fallbackPrime_step {N Δ : ℕ} (hp : N.Prime) (hN : 3 ≤ N)
    (hΔ : Even Δ) (hnew : ∃ q : ℕ, q.Prime ∧ N < q ∧ q < N + Δ) :
    (fallbackPrime (N + Δ)).Prime ∧ U6816.Step2 Δ N (fallbackPrime (N + Δ)) := by
  have hpos : 0 < Δ := by obtain ⟨q, _, hq, hqM⟩ := hnew; omega
  obtain ⟨hq, hqM, _⟩ := fallbackPrime_spec (by omega : 2 < N + Δ)
  exact ⟨hq, U6816.algorithm_step hp hq hN
    ((fallbackPrime_advances_iff hp hpos).mpr hnew) hqM hΔ⟩

/-- Page 2, Section 3, small instances of successful fallback and lack of
advancement. The spacing hypothesis alone does not supply a new prime. -/
theorem fallback_instances :
    fallbackPrime 11 = 7 ∧ U6816.Step2 6 5 (fallbackPrime 11) ∧
      (7 : ℕ).Prime ∧ 2 ^ 1 < (4 : ℕ) ∧ Even (4 : ℕ) ∧
        ¬ U6816.Step2 4 7 (fallbackPrime (7 + 4)) := by
  unfold U6816.Step2
  decide +kernel

end LeanLab.HelfgottPlatt.Task133
