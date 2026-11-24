import LeanLab.ChenDoubleSieve.Decomp349a

/-!
Split of `Task349.basic_finite_upper`, Wu 2004 page 39, the sieve step before 10.3
and the same step for 10.4. Source: https://arxiv.org/pdf/0705.1652.
The count to prime sum comparison is reduced to three analytic inputs:
the linear sieve upper bound of Jurkat and Richert applied to each A_p, the
Bombieri and Vinogradov remainder sum, and a Mertens type mass bound.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The sieve remainder of Wu 2004 page 38, display for R(D) with the prime sequence:
the sum over squarefree d below D whose prime factors are sifting primes below z,
of the absolute discrepancy between the number of N minus p' divisible by m d and
the expected value pi N over phi of m d. -/
def sieveRemainder (N m : ℕ) (z D : ℝ) : ℝ :=
  ∑ d ∈ (Finset.range ⌈D⌉₊).filter
      (fun d : ℕ => Squarefree d ∧ ∀ q ∈ d.primeFactors, ((q : ℕ) : ℝ) < z ∧ Nat.Coprime q N),
    |(((primeSequence N).filter (fun a => m * d ∣ a)).card : ℝ) -
      (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) / ((m * d).totient : ℝ)|

/-- LEAF: Wu 2004 page 39, the linear sieve upper bound before 10.3, applied to
A_p with sifting level p and level of distribution D over p, D equal square root N
over log N to B; Iwaniec and Jurkat Richert linear sieve, Wu Lemma 2.1 type input,
with pi N replaced by N over log N inside the uniform error eta. Class HARD. -/
theorem leaf_sieve_one (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∀ B : ℝ, 0 < B → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint 1),
        ((Wu41.S (primeSequence N) p N (basicSifting N p 1) : ℕ) : ℝ) ≤
          (N : ℝ) / log N * (Task363.localDensity N (basicSifting N p 1) / ((p : ℝ) - 1) *
            (F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / p) /
              log (basicSifting N p 1)) + η)) +
          sieveRemainder N p (basicSifting N p 1)
            (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / p) := by
  sorry

/-- LEAF: Wu 2004 page 39, the same linear sieve upper bound used for 10.4, applied
to A_p with fixed sifting level N to kappa one, p below N to sigma one or sigma two,
level D over p; linear sieve with pi N replaced by N over log N inside eta.
Class HARD. -/
theorem leaf_sieve_two_three (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∀ B : ℝ, 0 < B → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({2, 3} : Finset (Fin 12)) →
      ∀ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i),
        ((Wu41.S (primeSequence N) p N (basicSifting N p i) : ℕ) : ℝ) ≤
          (N : ℝ) / log N * (Task363.localDensity N (basicSifting N p i) / ((p : ℝ) - 1) *
            (F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / p) /
              log (basicSifting N p i)) + η)) +
          sieveRemainder N p (basicSifting N p i)
            (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / p) := by
  sorry

/-- LEAF: Wu 2004 page 39 with page 38, the remainder terms summed over p are
negligible by the Bombieri and Vinogradov theorem at level square root N over
log N to B, after grouping m equal p d with the divisor function and Cauchy Schwarz.
Class HARD. -/
theorem leaf_remainder_bv :
    ∃ B : ℝ, 0 < B ∧ ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({1, 2, 3} : Finset (Fin 12)) →
        ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i),
          sieveRemainder N p (basicSifting N p i)
            (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / p) ≤ η * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 39, size of the main term of 10.3: by Mertens' product for
the local density V p of page 5 and the prime reciprocal sum over the band from
N to kappa one to N to kappa two, the mass is O of Theta N. Class MEDIUM. -/
theorem leaf_mass_one :
    ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (N : ℝ) / log N * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint 1),
        Task363.localDensity N (basicSifting N p 1) / ((p : ℝ) - 1) ≤ K * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 39, size of the main terms of 10.4: the local density at
N to kappa one is O of C_N over log N by Mertens, and the prime reciprocal sum
over the band up to N to sigma one or sigma two is bounded. Class MEDIUM. -/
theorem leaf_mass_two_three :
    ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({2, 3} : Finset (Fin 12)) →
      (N : ℝ) / log N * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i),
        Task363.localDensity N (basicSifting N p i) / ((p : ℝ) - 1) ≤ K * Θ N := by
  sorry

/-! ### Glue, proved -/

/-- The three ordinary sieve counts are the sums over p of S at the basic sifting level. -/
theorem sieveTerms_basic_eq (N : ℕ) (i : Fin 12) (hi : i ∈ ({1, 2, 3} : Finset (Fin 12))) :
    sieveTerms N i = ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i),
      ((Wu41.S (primeSequence N) p N (basicSifting N p i) : ℕ) : ℝ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;>
    simp [sieveTerms, basicEndpoint, basicSifting]

/-- The sieve leaves for coordinates one, two and three together. -/
theorem leaf_sieve_all (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∀ B : ℝ, 0 < B → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({1, 2, 3} : Finset (Fin 12)) →
      ∀ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i),
        ((Wu41.S (primeSequence N) p N (basicSifting N p i) : ℕ) : ℝ) ≤
          (N : ℝ) / log N * (Task363.localDensity N (basicSifting N p i) / ((p : ℝ) - 1) *
            (F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / p) /
              log (basicSifting N p i)) + η)) +
          sieveRemainder N p (basicSifting N p i)
            (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / p) := by
  intro η hη B hB
  obtain ⟨N1, h1⟩ := leaf_sieve_one F f h η hη B hB
  obtain ⟨N2, h2⟩ := leaf_sieve_two_three F f h η hη B hB
  refine ⟨max N1 N2, fun N hEven hN i hi => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | hi
  · exact h1 N hEven (le_of_max_le_left hN)
  · exact h2 N hEven (le_of_max_le_right hN) i (by simpa using hi)

/-- The mass leaves for coordinates one, two and three together. -/
theorem leaf_mass_all :
    ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({1, 2, 3} : Finset (Fin 12)) →
      (N : ℝ) / log N * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i),
        Task363.localDensity N (basicSifting N p i) / ((p : ℝ) - 1) ≤ K * Θ N := by
  obtain ⟨K1, hK1, M1, hM1⟩ := leaf_mass_one
  obtain ⟨K2, hK2, M2, hM2⟩ := leaf_mass_two_three
  refine ⟨max K1 K2, lt_max_of_lt_left hK1, max 2 (max M1 M2), fun N hEven hN i hi => ?_⟩
  have hΘ : 0 ≤ Θ N := (Θ_pos (show 2 ≤ N by omega)).le
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | hi
  · exact (hM1 N hEven (by omega)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hΘ)
  · exact (hM2 N hEven (by omega) i (by simpa using hi)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hΘ)

/-- `basic_finite_upper`, exactly as stated in `Decomp349a`, proved from the five
leaves above. CONDITIONAL ON the LEAFs. -/
theorem basic_finite_upper_of_leaves (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        ∀ i : Fin 12, i ∈ ({1, 2, 3} : Finset (Fin 12)) →
          sieveTerms N i ≤ basicMain F B N i + η * Θ N := by
  intro η hη
  obtain ⟨B, hB, hR⟩ := leaf_remainder_bv
  obtain ⟨K, hK, M, hM⟩ := leaf_mass_all
  obtain ⟨N1, hS⟩ := leaf_sieve_all F f h (η / (2 * K)) (by positivity) B hB
  obtain ⟨N2, hR2⟩ := hR (η / 2) (by positivity)
  refine ⟨B, hB, max M (max N1 N2), fun N hEven hN i hi => ?_⟩
  have hM' := hM N hEven (le_of_max_le_left hN) i hi
  have hR' := hR2 N hEven (le_of_max_le_right (le_of_max_le_right hN)) i hi
  have hS' := hS N hEven (le_of_max_le_left (le_of_max_le_right hN)) i hi
  rw [sieveTerms_basic_eq N i hi]
  set P := Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i)
  set X := (N : ℝ) / log N
  set D := (N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B
  set a : ℕ → ℝ := fun p => Task363.localDensity N (basicSifting N p i) / ((p : ℝ) - 1)
  set G : ℕ → ℝ := fun p => F (log (D / p) / log (basicSifting N p i))
  set r : ℕ → ℝ := fun p => sieveRemainder N p (basicSifting N p i) (D / p)
  have hsum : ∑ p ∈ P, ((Wu41.S (primeSequence N) p N (basicSifting N p i) : ℕ) : ℝ) ≤
      ∑ p ∈ P, (X * (a p * (G p + η / (2 * K))) + r p) :=
    Finset.sum_le_sum hS'
  have hsplit : ∑ p ∈ P, (X * (a p * (G p + η / (2 * K))) + r p) =
      X * ∑ p ∈ P, a p * G p + η / (2 * K) * (X * ∑ p ∈ P, a p) + ∑ p ∈ P, r p := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hmain : basicMain F B N i = X * ∑ p ∈ P, a p * G p := rfl
  have hmass : η / (2 * K) * (X * ∑ p ∈ P, a p) ≤ η / (2 * K) * (K * Θ N) :=
    mul_le_mul_of_nonneg_left hM' (by positivity)
  have hcalc : η / (2 * K) * (K * Θ N) = η / 2 * Θ N := by
    field_simp
  rw [hmain]
  linarith

end LeanLab.ChenDoubleSieve.Task349
