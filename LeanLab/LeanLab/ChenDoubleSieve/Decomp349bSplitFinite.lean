import LeanLab.ChenDoubleSieve.Decomp349b

/-!
Split of `Task349.switched_finite_upper`, Wu 2004 pages 40 and 41, equations 10.6
to 10.8 and 10.11. Source: https://arxiv.org/pdf/0705.1652.
Chen's switching principle turns the three switched counts into counts of primes
in the sequence N minus p q m; the linear sieve at s equal 2 and a bilinear
Bombieri and Vinogradov mean value theorem bound that count.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The switched count of Wu 2004 page 40: for each switched pair p, q the number of
primes m with p q m at most N and N minus p q m prime. -/
def switchedCount (N : ℕ) (i : Fin 12) : ℝ :=
  ∑ q ∈ switchedPairs N i,
    (((Finset.range (N + 1)).filter
      (fun m => m.Prime ∧ q.1 * q.2 * m ≤ N ∧ (N - q.1 * q.2 * m).Prime)).card : ℝ)

/-- The sieve remainder of the switched sequence N minus p q m, Wu 2004 page 40, at
level D equal square root N over log N to B: over squarefree d below D coprime to N,
the discrepancy between the switched multiples of d and the expected value, the sum
over the pairs of pi of N over p q, divided by phi d. -/
def switchedRemainder (N : ℕ) (i : Fin 12) (B : ℝ) : ℝ :=
  ∑ d ∈ (Finset.range ⌈(N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B⌉₊).filter
      (fun d => Squarefree d ∧ d.Coprime N),
    |(∑ q ∈ switchedPairs N i,
        (((Finset.range (N + 1)).filter
          (fun m => m.Prime ∧ q.1 * q.2 * m ≤ N ∧ d ∣ N - q.1 * q.2 * m)).card : ℝ)) -
      (∑ q ∈ switchedPairs N i,
        (((Finset.range (N / (q.1 * q.2) + 1)).filter Nat.Prime).card : ℝ)) /
        (d.totient : ℝ)|

/-- LEAF: Wu 2004 page 40, Chen's switching principle before 10.6: writing N minus
p' as p q m, the sifting conditions and the size bounds p q cubed above N, or
p q times N to two sigma one above N for coordinate nine, force m to be prime
up to O of N to one minus epsilon exceptions from m equal 1, p dividing m or a
prime factor of N. Class MEDIUM. -/
theorem leaf_switching :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
        sieveTerms N i ≤ switchedCount N i + η * Θ N := by
  sorry

/-- LEAF: Wu 2004 pages 40 and 41, equations 10.6 to 10.8 and 10.11: the linear
sieve upper bound with s equal 2 applied to the switched sequence at level D and
sifting level D to one half, with F 2 equal e to gamma, the Mertens product for
the local density and the prime number theorem for pi of N over p q, which gives
8 C_N N over log N times the switched sum. Class HARD. -/
theorem leaf_switched_sieve :
    ∀ η : ℝ, 0 < η → ∀ B : ℝ, 0 < B → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
        switchedCount N i ≤ switchedMain N i + η * Θ N + switchedRemainder N i B := by
  sorry

/-- LEAF: Wu 2004 page 40, the remainder of the switched sequence is negligible by
the bilinear mean value theorem of Bombieri and Vinogradov type cited there, at
level square root N over log N to B. Class HARD. -/
theorem leaf_switched_remainder :
    ∃ B : ℝ, 0 < B ∧ ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
        switchedRemainder N i B ≤ η * Θ N := by
  sorry

/-- `switched_finite_upper`, exactly as stated in `Decomp349b`, proved from the three
leaves above. CONDITIONAL ON the LEAFs. -/
theorem switched_finite_upper_of_leaves :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
          sieveTerms N i ≤ switchedMain N i + η * Θ N := by
  intro η hη
  obtain ⟨B, hB, hR⟩ := leaf_switched_remainder
  obtain ⟨N1, h1⟩ := leaf_switching (η / 3) (by positivity)
  obtain ⟨N2, h2⟩ := leaf_switched_sieve (η / 3) (by positivity) B hB
  obtain ⟨N3, h3⟩ := hR (η / 3) (by positivity)
  refine ⟨max N1 (max N2 N3), fun N hEven hN i hi => ?_⟩
  have a1 := h1 N hEven (le_of_max_le_left hN) i hi
  have a2 := h2 N hEven (le_of_max_le_left (le_of_max_le_right hN)) i hi
  have a3 := h3 N hEven (le_of_max_le_right (le_of_max_le_right hN)) i hi
  linarith

end LeanLab.ChenDoubleSieve.Task349
