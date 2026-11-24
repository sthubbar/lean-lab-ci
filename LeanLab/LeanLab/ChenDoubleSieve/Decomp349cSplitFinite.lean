import LeanLab.ChenDoubleSieve.Decomp349c

/-!
Split of `refined_finite_upper` from Decomp349c.
Wu 2004 page 41 equation 10.12: for Upsilon 9, 13 and 14 the first prime
`p1 ≤ N^(1/10)` is handled by Lemma 2.6, the remaining range by Lemma 2.3 and
the switching weight eight. Each of the three terms is split at the one tenth
cutoff into two finite sieve estimates.
Source: https://arxiv.org/pdf/0705.1652, page 41.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349.SplitFinite
open Task275 Task348 Task349
open Wu41 (S)
open Wu04Functional (IsBuchstab)

/-- LEAF: Wu 2004 page 41, sentence before equation 10.12, Upsilon 9 with
`p1 ≤ N^(1/10)`: Lemma 2.6 replaces Lemma 2.3 and gives the weight
`36/5 / (1 - log p1 / log N)` in the retained finite prime sum. Class HARD. -/
theorem pair_low_upper :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∑ q ∈ (refinedPairs N).filter (fun q => (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
          (S (primeSequence N) (q.1 * q.2) (N * q.1) q.2 : ℝ) ≤
        CN N * N / log N *
          ∑ q ∈ (refinedPairs N).filter (fun q => (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
            refinedWeight N q.1 / (((q.1 : ℝ) * q.2) * log ((N : ℝ) / ((q.1 : ℝ) * q.2)))
          + η * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.12, Upsilon 9 with `p1 > N^(1/10)`:
the Lemma 2.3 switched upper bound with weight eight, as for equation 10.10,
kept as a finite prime sum. Class HARD. -/
theorem pair_high_upper :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∑ q ∈ (refinedPairs N).filter (fun q => ¬ (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
          (S (primeSequence N) (q.1 * q.2) (N * q.1) q.2 : ℝ) ≤
        CN N * N / log N *
          ∑ q ∈ (refinedPairs N).filter (fun q => ¬ (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
            refinedWeight N q.1 / (((q.1 : ℝ) * q.2) * log ((N : ℝ) / ((q.1 : ℝ) * q.2)))
          + η * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.12, Upsilon 13 with `p1 ≤ N^(1/10)`:
Lemma 2.6 for the switched count and Lemma 2.10 for the rough number count
`S(A; p2)` giving the Buchstab factor. Class HARD. -/
theorem quad13_low_upper (ω : ℝ → ℝ) (hω : IsBuchstab ω) :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∑ q ∈ (refinedQuads N 10).filter (fun q => (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
          (S (primeSequence N) (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1 : ℝ) ≤
        CN N * N / log N *
          ∑ q ∈ (refinedQuads N 10).filter (fun q => (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
            refinedWeight N q.1 * ω (log ((N : ℝ) / quadProduct q) / log q.2.1) /
              (quadProduct q * log q.2.1)
          + η * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.12, Upsilon 13 with `p1 > N^(1/10)`:
Lemma 2.3 with weight eight and Lemma 2.10. Class HARD. -/
theorem quad13_high_upper (ω : ℝ → ℝ) (hω : IsBuchstab ω) :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∑ q ∈ (refinedQuads N 10).filter (fun q => ¬ (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
          (S (primeSequence N) (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1 : ℝ) ≤
        CN N * N / log N *
          ∑ q ∈ (refinedQuads N 10).filter (fun q => ¬ (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
            refinedWeight N q.1 * ω (log ((N : ℝ) / quadProduct q) / log q.2.1) /
              (quadProduct q * log q.2.1)
          + η * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.12, Upsilon 14 with `p1 ≤ N^(1/10)`:
Lemma 2.6 and Lemma 2.10. Class HARD. -/
theorem quad14_low_upper (ω : ℝ → ℝ) (hω : IsBuchstab ω) :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∑ q ∈ (refinedQuads N 11).filter (fun q => (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
          (S (primeSequence N) (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1 : ℝ) ≤
        CN N * N / log N *
          ∑ q ∈ (refinedQuads N 11).filter (fun q => (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
            refinedWeight N q.1 * ω (log ((N : ℝ) / quadProduct q) / log q.2.1) /
              (quadProduct q * log q.2.1)
          + η * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.12, Upsilon 14 with `p1 > N^(1/10)`:
Lemma 2.3 with weight eight and Lemma 2.10. Class HARD. -/
theorem quad14_high_upper (ω : ℝ → ℝ) (hω : IsBuchstab ω) :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∑ q ∈ (refinedQuads N 11).filter (fun q => ¬ (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
          (S (primeSequence N) (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1 : ℝ) ≤
        CN N * N / log N *
          ∑ q ∈ (refinedQuads N 11).filter (fun q => ¬ (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
            refinedWeight N q.1 * ω (log ((N : ℝ) / quadProduct q) / log q.2.1) /
              (quadProduct q * log q.2.1)
          + η * Θ N := by
  sorry

/-- Glue: a finite sum bound split along a predicate. -/
theorem split_sum_bound {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p]
    (a b : α → ℝ) (c η T : ℝ)
    (hlo : ∑ x ∈ s.filter p, a x ≤ c * ∑ x ∈ s.filter p, b x + η / 2 * T)
    (hhi : ∑ x ∈ s.filter (fun x => ¬ p x), a x ≤
      c * ∑ x ∈ s.filter (fun x => ¬ p x), b x + η / 2 * T) :
    ∑ x ∈ s, a x ≤ c * ∑ x ∈ s, b x + η * T := by
  rw [← sum_filter_add_sum_filter_not s p a, ← sum_filter_add_sum_filter_not s p b,
    mul_add]
  linarith

/-- Glue: the Upsilon 9 count is the real sum over the refined pair domain. -/
theorem sieveTerms_eight (N : ℕ) :
    sieveTerms N 8 = ∑ q ∈ refinedPairs N,
      (S (primeSequence N) (q.1 * q.2) (N * q.1) q.2 : ℝ) := by
  show ((∑ q ∈ refinedPairs N, S (primeSequence N) (q.1 * q.2) (N * q.1) q.2 : ℕ) : ℝ) = _
  push_cast
  rfl

/-- Glue: the Upsilon 13 count is the real sum over the refined quadruple domain. -/
theorem sieveTerms_ten (N : ℕ) :
    sieveTerms N 10 = ∑ q ∈ refinedQuads N 10,
      (S (primeSequence N) (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1 : ℝ) := by
  have hQ : refinedQuads N 10 = Wu08Sum.P4 N (fun p q r s => (N : ℝ) ^ kappa1 ≤ p ∧
      p < q ∧ q < r ∧ r < s ∧ (s : ℝ) < (N : ℝ) ^ kappa2) := by
    simp only [refinedQuads, ↓reduceIte]
  rw [hQ]
  show ((∑ q ∈ Wu08Sum.P4 N (fun p q r s => (N : ℝ) ^ kappa1 ≤ p ∧
      p < q ∧ q < r ∧ r < s ∧ (s : ℝ) < (N : ℝ) ^ kappa2),
      S (primeSequence N) (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1 : ℕ) : ℝ) = _
  push_cast
  rfl

/-- Glue: the Upsilon 14 count is the real sum over the refined quadruple domain. -/
theorem sieveTerms_eleven (N : ℕ) :
    sieveTerms N 11 = ∑ q ∈ refinedQuads N 11,
      (S (primeSequence N) (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1 : ℝ) := by
  have hQ : refinedQuads N 11 = Wu08Sum.P4 N (fun p q r s => (N : ℝ) ^ kappa1 ≤ p ∧
      p < q ∧ q < r ∧ (r : ℝ) < (N : ℝ) ^ kappa2 ∧ (N : ℝ) ^ kappa2 ≤ s ∧
        (s : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / r) := by
    simp only [refinedQuads, show (11 : Fin 12) ≠ 10 by decide, ↓reduceIte]
  rw [hQ]
  show ((∑ q ∈ Wu08Sum.P4 N (fun p q r s => (N : ℝ) ^ kappa1 ≤ p ∧
      p < q ∧ q < r ∧ (r : ℝ) < (N : ℝ) ^ kappa2 ∧ (N : ℝ) ^ kappa2 ≤ s ∧
        (s : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / r),
      S (primeSequence N) (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1 : ℕ) : ℝ) = _
  push_cast
  rfl

/-- The exact statement of `refined_finite_upper`, assembled from the six LEAFs.
CONDITIONAL ON the LEAFs above. -/
theorem refined_finite_upper_of_leaves (ω : ℝ → ℝ) (hω : IsBuchstab ω) :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        ∀ i : Fin 12, i ∈ ({8, 10, 11} : Finset (Fin 12)) →
          sieveTerms N i ≤ refinedMain ω N i + η * Θ N := by
  intro η hη
  have h2 : 0 < η / 2 := by linarith
  obtain ⟨A1, hA1⟩ := pair_low_upper (η / 2) h2
  obtain ⟨A2, hA2⟩ := pair_high_upper (η / 2) h2
  obtain ⟨B1, hB1⟩ := quad13_low_upper ω hω (η / 2) h2
  obtain ⟨B2, hB2⟩ := quad13_high_upper ω hω (η / 2) h2
  obtain ⟨C1, hC1⟩ := quad14_low_upper ω hω (η / 2) h2
  obtain ⟨C2, hC2⟩ := quad14_high_upper ω hω (η / 2) h2
  refine ⟨max (max A1 A2) (max (max B1 B2) (max C1 C2)), ?_⟩
  intro N hE hN i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · rw [sieveTerms_eight]
    unfold refinedMain refinedSum
    rw [if_pos rfl]
    exact split_sum_bound _ _ _ _ _ η _
      (hA1 N hE (by omega)) (hA2 N hE (by omega))
  · rw [sieveTerms_ten]
    unfold refinedMain refinedSum
    rw [if_neg (by decide)]
    exact split_sum_bound _ _ _ _ _ η _
      (hB1 N hE (by omega)) (hB2 N hE (by omega))
  · rw [sieveTerms_eleven]
    unfold refinedMain refinedSum
    rw [if_neg (by decide)]
    exact split_sum_bound _ _ _ _ _ η _
      (hC1 N hE (by omega)) (hC2 N hE (by omega))

end LeanLab.ChenDoubleSieve.Task349.SplitFinite
