/-
R-5290, CLOUD 20261020T2217Z-cloud52, unit U-6747, T3 MOONSHOT.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.

The incompressibility route.  Binary Goldbach at N is a statement about the
Hamming distance from the prime string to the family of N-avoiding strings,
sets T with t ∈ T → N - t ∉ T.  Plain math twins:
* `pairs N S` is {i ∈ S : 2i ≤ N, N - i ∈ S}, the unordered representations.
* `delete_pairs_avoiding`: S minus its pairs is N-avoiding.
* `pairs_le_sdiff`: every N-avoiding T ⊆ S deletes at least |pairs N S| points.
* `hamming_dist_eq`: so the least deletion turning S into an N-avoiding set has
  size exactly |pairs N S|.
* `goldbach_iff_pairs_nonempty`: for S the primes up to N, pairs is nonempty iff
  N = p + q with p, q prime; so Goldbach at N iff that distance is at least 1.
* `avoid_card`: on k reflected position pairs there are exactly 3^k avoiding
  patterns, against 4^k strings, the counting fact behind every
  incompressibility or random model argument; the primes are one computable
  string, so the count says nothing about them.
-/
import Mathlib

namespace LeanLab.Routes.R5290

/-- T is N-avoiding: no two members, equal or not, sum to N. -/
def Avoiding (N : ℕ) (T : Finset ℕ) : Prop := ∀ t ∈ T, N - t ∉ T

/-- The unordered representations of N inside S, indexed by the smaller summand. -/
def pairs (N : ℕ) (S : Finset ℕ) : Finset ℕ := S.filter (fun i => 2 * i ≤ N ∧ N - i ∈ S)

theorem pairs_subset (N : ℕ) (S : Finset ℕ) : pairs N S ⊆ S := Finset.filter_subset _ _

theorem delete_pairs_avoiding (N : ℕ) (S : Finset ℕ) (hS : ∀ i ∈ S, i ≤ N) :
    Avoiding N (S \ pairs N S) := by
  intro i hi hj
  simp only [Finset.mem_sdiff, pairs, Finset.mem_filter, not_and] at hi hj
  obtain ⟨hiS, hiP⟩ := hi
  obtain ⟨hjS, hjP⟩ := hj
  have hiN := hS i hiS
  by_cases h2 : 2 * i ≤ N
  · exact hiP hiS h2 hjS
  · have e : N - (N - i) = i := by omega
    exact hjP hjS (by omega) (by rw [e]; exact hiS)

theorem pairs_le_sdiff (N : ℕ) (S T : Finset ℕ) (hS : ∀ i ∈ S, i ≤ N) (_hTS : T ⊆ S)
    (hT : Avoiding N T) : (pairs N S).card ≤ (S \ T).card := by
  classical
  let f : ℕ → ℕ := fun i => if i ∈ T then N - i else i
  apply Finset.card_le_card_of_injOn f
  · intro i hi
    simp only [pairs, Finset.coe_filter, Set.mem_ofPred_eq] at hi
    obtain ⟨hiS, _, hNi⟩ := hi
    simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, f]
    split_ifs with hiT
    · exact ⟨hNi, hT i hiT⟩
    · exact ⟨hiS, hiT⟩
  · intro i hi j hj hij
    simp only [pairs, Finset.coe_filter, Set.mem_ofPred_eq] at hi hj
    obtain ⟨hiS, hi2, _⟩ := hi
    obtain ⟨hjS, hj2, _⟩ := hj
    have hiN := hS i hiS
    have hjN := hS j hjS
    simp only [f] at hij
    split_ifs at hij with hiT hjT hjT
    · omega
    · have : i = j := by omega
      exact absurd (this ▸ hiT) hjT
    · have : i = j := by omega
      exact absurd (this ▸ hjT) hiT
    · exact hij

theorem hamming_dist_eq (N : ℕ) (S : Finset ℕ) (hS : ∀ i ∈ S, i ≤ N) :
    (∃ T ⊆ S, Avoiding N T ∧ (S \ T).card = (pairs N S).card) ∧
    (∀ T ⊆ S, Avoiding N T → (pairs N S).card ≤ (S \ T).card) := by
  refine ⟨⟨S \ pairs N S, Finset.sdiff_subset, delete_pairs_avoiding N S hS, ?_⟩,
    fun T hTS hT => pairs_le_sdiff N S T hS hTS hT⟩
  rw [Finset.sdiff_sdiff_eq_self (pairs_subset N S)]

/-- The primes up to N. -/
def primesUpTo (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime

theorem goldbach_iff_pairs_nonempty (N : ℕ) :
    (pairs N (primesUpTo N)).Nonempty ↔ ∃ p q, p.Prime ∧ q.Prime ∧ p + q = N := by
  constructor
  · rintro ⟨i, hi⟩
    simp only [pairs, primesUpTo, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨⟨hiN, hip⟩, _, hNiN, hq⟩ := hi
    exact ⟨i, N - i, hip, hq, by omega⟩
  · rintro ⟨p, q, hp, hq, rfl⟩
    rcases le_total p q with h | h
    · refine ⟨p, ?_⟩
      simp only [pairs, primesUpTo, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨by omega, hp⟩, by omega, ⟨by omega, ?_⟩⟩
      rwa [Nat.add_sub_cancel_left]
    · refine ⟨q, ?_⟩
      simp only [pairs, primesUpTo, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨by omega, hq⟩, by omega, ⟨by omega, ?_⟩⟩
      rwa [Nat.add_sub_cancel]

theorem primesUpTo_le (N : ℕ) : ∀ i ∈ primesUpTo N, i ≤ N := by
  intro i hi
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_range] at hi
  omega

/-- Goldbach at N iff the prime string is at Hamming distance at least 1 from every
N-avoiding subset, with the distance equal to the number of representations. -/
theorem goldbach_iff_dist_pos (N : ℕ) :
    (∃ p q, p.Prime ∧ q.Prime ∧ p + q = N) ↔
      ∀ T ⊆ primesUpTo N, Avoiding N T → 1 ≤ (primesUpTo N \ T).card := by
  rw [← goldbach_iff_pairs_nonempty]
  constructor
  · intro h T hTS hT
    exact le_trans (Finset.card_pos.mpr h) (pairs_le_sdiff N _ T (primesUpTo_le N) hTS hT)
  · intro h
    obtain ⟨⟨T, hTS, hT, hc⟩, _⟩ := hamming_dist_eq N _ (primesUpTo_le N)
    have := h T hTS hT
    rw [hc] at this
    exact Finset.card_pos.mp this

/-- Avoiding patterns on one reflected pair {i, N - i}: not both present. -/
abbrev Pat := {p : Bool × Bool // ¬ (p.1 = true ∧ p.2 = true)}

theorem pat_card : Fintype.card Pat = 3 := by decide

theorem avoid_card (k : ℕ) : Fintype.card (Fin k → Pat) = 3 ^ k := by
  rw [Fintype.card_fun, pat_card, Fintype.card_fin]

theorem avoid_lt (k : ℕ) (hk : 0 < k) :
    Fintype.card (Fin k → Pat) < Fintype.card (Fin k → Bool × Bool) := by
  rw [avoid_card, Fintype.card_fun, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  exact Nat.pow_lt_pow_left (by norm_num) (by omega)

/-! Vacuity checks: the hypotheses hold and the conclusions are not empty. -/

theorem primesUpTo_10 : primesUpTo 10 = {2, 3, 5, 7} := by decide

theorem pairs_10 : pairs 10 (primesUpTo 10) = {3, 5} := by
  rw [primesUpTo_10]; decide

example : Avoiding 10 ({2, 7} : Finset ℕ) ∧ (({2, 3, 5, 7} : Finset ℕ) \ {2, 7}).card = 2 := by
  unfold Avoiding; decide

example : ∃ p q, p.Prime ∧ q.Prime ∧ p + q = 10 :=
  (goldbach_iff_pairs_nonempty 10).mp (by rw [pairs_10]; exact ⟨3, by decide⟩)

/-- The negative side is not empty either: 11 is no sum of two primes, the pairs set
is empty, and the iff then says some avoiding T ⊆ primes up to 11 deletes nothing. -/
theorem pairs_11 : pairs 11 (primesUpTo 11) = ∅ := by
  have : primesUpTo 11 = {2, 3, 5, 7, 11} := by decide
  rw [this]; decide

example : ¬ ∃ p q, p.Prime ∧ q.Prime ∧ p + q = 11 := by
  rw [← goldbach_iff_pairs_nonempty, pairs_11]; exact Finset.not_nonempty_empty

#print axioms delete_pairs_avoiding
#print axioms pairs_le_sdiff
#print axioms hamming_dist_eq
#print axioms goldbach_iff_pairs_nonempty
#print axioms goldbach_iff_dist_pos
#print axioms avoid_card
#print axioms avoid_lt
#print axioms pairs_10
#print axioms pairs_11

end LeanLab.Routes.R5290
