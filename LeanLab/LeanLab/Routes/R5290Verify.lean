/-
R-5290 verification, run PC 20261020T2303Z-14596, unit U-1295, T3 VERIFY of
CLOUD 20261020T2217Z-cloud52 U-6747.  AI wrote this Lean code.
Not progress on binary Goldbach, which is OPEN.

Extra checks on Routes/R5290.lean:
* `pairs_card_eq_goldbachPairs`: |pairs N (primesUpTo N)| is the real unordered
  Goldbach count, the number of (p, q) with p ≤ q, p, q prime, p + q = N.
* `pairs_le_symmDiff`: the identity holds for true Hamming distance, adding points
  allowed, not only for deletions T ⊆ S.
* `hamming_eq_r`: least Hamming distance from the primes up to N to an N-avoiding
  set equals the Goldbach count, stated as attained plus lower bound.
* `goldbach_all_iff`: the full conjecture is the distance statement at every even N > 2.
* Non vacuity: `avoiding_empty`, and the count 3 at N = 30.
-/
import LeanLab.Routes.R5290

namespace LeanLab.Routes.R5290Verify

open LeanLab.Routes.R5290

/-- The unordered Goldbach representations of N, written independently of `pairs`. -/
def goldbachPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter
    (fun pq => pq.1 ≤ pq.2 ∧ pq.1 + pq.2 = N ∧ pq.1.Prime ∧ pq.2.Prime)

theorem pairs_card_eq_goldbachPairs (N : ℕ) :
    (pairs N (primesUpTo N)).card = (goldbachPairs N).card := by
  apply Finset.card_bij (fun i _ => (i, N - i))
  · intro i hi
    simp only [pairs, primesUpTo, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨⟨hiN, hip⟩, h2, _, hq⟩ := hi
    simp only [goldbachPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨hiN, by omega⟩, by omega, by omega, hip, hq⟩
  · intro i _ j _ h
    simp only [Prod.mk.injEq] at h
    exact h.1
  · rintro ⟨p, q⟩ h
    simp only [goldbachPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
    obtain ⟨⟨hp, hq⟩, hle, hs, pp, qp⟩ := h
    refine ⟨p, ?_, ?_⟩
    · simp only [pairs, primesUpTo, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨hp, pp⟩, by omega, ⟨by omega, ?_⟩⟩
      have : N - p = q := by omega
      rw [this]; exact qp
    · simp only [Prod.mk.injEq, true_and]; omega

theorem avoiding_mono (N : ℕ) (T U : Finset ℕ) (hU : U ⊆ T) (hT : Avoiding N T) :
    Avoiding N U := fun t ht h => hT t (hU ht) (hU h)

theorem avoiding_empty (N : ℕ) : Avoiding N ∅ := by
  intro t ht; simp at ht

/-- True Hamming distance: any N-avoiding T, not only subsets of S. -/
theorem pairs_le_symmDiff (N : ℕ) (S T : Finset ℕ) (hS : ∀ i ∈ S, i ≤ N)
    (hT : Avoiding N T) : (pairs N S).card ≤ (symmDiff S T).card := by
  classical
  have h1 := pairs_le_sdiff N S (S ∩ T) hS Finset.inter_subset_left
    (avoiding_mono N T _ Finset.inter_subset_right hT)
  have h2 : S \ (S ∩ T) ⊆ symmDiff S T := by
    intro x hx
    rw [Finset.mem_symmDiff]
    simp only [Finset.mem_sdiff, Finset.mem_inter, not_and] at hx
    exact Or.inl ⟨hx.1, hx.2 hx.1⟩
  exact h1.trans (Finset.card_le_card h2)

theorem hamming_eq_r (N : ℕ) :
    (∃ T, Avoiding N T ∧ (symmDiff (primesUpTo N) T).card = (goldbachPairs N).card) ∧
    (∀ T, Avoiding N T → (goldbachPairs N).card ≤ (symmDiff (primesUpTo N) T).card) := by
  classical
  rw [← pairs_card_eq_goldbachPairs]
  refine ⟨⟨primesUpTo N \ pairs N (primesUpTo N),
      delete_pairs_avoiding N _ (primesUpTo_le N), ?_⟩,
    fun T hT => pairs_le_symmDiff N _ T (primesUpTo_le N) hT⟩
  have : symmDiff (primesUpTo N) (primesUpTo N \ pairs N (primesUpTo N))
      = pairs N (primesUpTo N) := by
    rw [symmDiff_def, Finset.sdiff_sdiff_eq_self (pairs_subset N _)]
    have : (primesUpTo N \ pairs N (primesUpTo N)) \ primesUpTo N = ∅ := by
      ext x; simp
    rw [this, Finset.sup_eq_union, Finset.union_empty]
  rw [this]

theorem goldbach_all_iff :
    (∀ N, 2 < N → Even N → ∃ p q, p.Prime ∧ q.Prime ∧ p + q = N) ↔
    (∀ N, 2 < N → Even N →
      ∀ T ⊆ primesUpTo N, Avoiding N T → 1 ≤ (primesUpTo N \ T).card) := by
  constructor
  · intro h N h2 he; exact (goldbach_iff_dist_pos N).mp (h N h2 he)
  · intro h N h2 he; exact (goldbach_iff_dist_pos N).mpr (h N h2 he)

theorem primesUpTo_30 : primesUpTo 30 = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} := by decide

theorem pairs_30 : pairs 30 (primesUpTo 30) = {7, 11, 13} := by
  rw [primesUpTo_30]; decide

theorem goldbachPairs_30_card : (goldbachPairs 30).card = 3 := by
  rw [← pairs_card_eq_goldbachPairs, pairs_30]; rfl

#print axioms pairs_subset
#print axioms delete_pairs_avoiding
#print axioms pairs_le_sdiff
#print axioms hamming_dist_eq
#print axioms goldbach_iff_pairs_nonempty
#print axioms primesUpTo_le
#print axioms goldbach_iff_dist_pos
#print axioms pat_card
#print axioms avoid_card
#print axioms avoid_lt
#print axioms primesUpTo_10
#print axioms pairs_10
#print axioms pairs_11
#print axioms pairs_card_eq_goldbachPairs
#print axioms avoiding_mono
#print axioms avoiding_empty
#print axioms pairs_le_symmDiff
#print axioms hamming_eq_r
#print axioms goldbach_all_iff
#print axioms primesUpTo_30
#print axioms pairs_30
#print axioms goldbachPairs_30_card

end LeanLab.Routes.R5290Verify
