/-
AI wrote this Lean code for CODEX task70.
Section 4, equations 4.1 and 4.2, pages 431 and 432.
The examples validate the counting conventions and do not extend a verification range.
-/
import LeanLab.SteinStein1965.Distinct

namespace LeanLab.SteinStein1965

/-- Index pairs with i at most j, exactly as in equation 4.1. -/
def decompositionPairs (bs : List ℕ) (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range bs.length).product (Finset.range bs.length)).filter fun ij =>
    ij.1 ≤ ij.2 ∧ bs[ij.1]! + bs[ij.2]! = m

/-- The number of decompositions in equation 4.1 for a specified finite basis. -/
def nu (bs : List ℕ) (m : ℕ) : ℕ := (decompositionPairs bs m).card

/-- Equation 4.2 counts positive even targets through x at which nu equals k. -/
def sigma (bs : List ℕ) (k x : ℕ) : ℕ :=
  ((evensIn 2 x).filter fun m => nu bs m == k).length

theorem nu_pos_iff_covers (bs : List ℕ) (m : ℕ) : 0 < nu bs m ↔ covers bs m = true := by
  rw [nu, Finset.card_pos, covers_iff]
  constructor
  · rintro ⟨⟨i, j⟩, hij⟩
    simp only [decompositionPairs, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hij
    obtain ⟨⟨hi, hj⟩, _, he⟩ := hij
    exact ⟨bs[i]!, by simpa [getElem!_pos bs i hi] using List.getElem_mem hi,
      bs[j]!, by simpa [getElem!_pos bs j hj] using List.getElem_mem hj, he⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.mp hb
    by_cases hij : i ≤ j
    · refine ⟨(i, j), ?_⟩
      simp only [decompositionPairs, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨hi, hj⟩, hij, by simpa [getElem!_pos bs i hi, getElem!_pos bs j hj, hia, hjb] using hab⟩
    · refine ⟨(j, i), ?_⟩
      simp only [decompositionPairs, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨hj, hi⟩, by omega, by simpa [getElem!_pos bs i hi, getElem!_pos bs j hj, hia, hjb, Nat.add_comm] using hab⟩

theorem basis_iff_nu_pos (bs : List ℕ) (lo hi : ℕ) :
    IsBasisFor bs lo hi ↔ ∀ m, m % 2 = 0 → lo ≤ m → m ≤ hi → 0 < nu bs m := by
  simp only [IsBasisFor, nu_pos_iff_covers, covers_iff]

theorem frequency_example :
    nu [3, 5] 6 = 1 ∧ nu [3, 5] 8 = 1 ∧ nu [3, 5] 10 = 1 ∧
    sigma [3, 5] 1 10 = 3 ∧ sigma [3, 5] 0 10 = 2 := by
  decide +kernel

/-- Adjacent positive gaps in a supplied increasing input list, as in Table IV. -/
def consecutiveGapCount (xs : List ℕ) (g : ℕ) : ℕ :=
  ((xs.zip xs.tail).filter fun p => p.2 == p.1 + g).length

theorem equal_length_different_gaps :
    ([3, 5] : List ℕ).length = ([3, 7] : List ℕ).length ∧
    consecutiveGapCount [3, 5] 2 = 1 ∧ consecutiveGapCount [3, 7] 2 = 0 := by
  decide +kernel

/-- Page 428 conjectures that the infinite output from 3 is a basis for all evens at least 6. -/
def InfiniteSBasis3 : Prop :=
  ∀ m, m % 2 = 0 → 6 ≤ m →
    ∃ x y, (∃ N, x ∈ (sPrime 3 N).1) ∧ (∃ N, y ∈ (sPrime 3 N).1) ∧ x + y = m

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.nu_pos_iff_covers
#print axioms LeanLab.SteinStein1965.basis_iff_nu_pos
#print axioms LeanLab.SteinStein1965.frequency_example

#print axioms LeanLab.SteinStein1965.equal_length_different_gaps
