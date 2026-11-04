import LeanLab.OpenProblems.SearchAdditive2Basis

/-!
# The three-kind ceiling for block certificates

AI wrote the Lean code. Goldbach remains OPEN. This is known mathematics.
Source: Kohonen, https://arxiv.org/abs/1606.04770, version 2, page 5,
Section 3, the bound `lI*lJ + lI*lK + lJ*lK <= l^2/3`.
The theorem here bounds the current block checker. It makes no claim that
this checker captures every covered integer in the geometric sumset.
-/

namespace LeanLab.OpenProblems.SearchAdditive2Basis

open scoped Pointwise

/-- Covered blocks lie in the union of the three mixed placement sumsets. -/
theorem covered_blocks_le_mixed_products {I J K : List ℕ} {m : ℕ}
    (h : coversB I J K m = true) :
    m ≤ I.length * J.length + I.length * K.length + J.length * K.length := by
  let P := I.toFinset + J.toFinset
  let Q := I.toFinset + K.toFinset
  let R := J.toFinset + K.toFinset
  have hsub : Finset.range m ⊆ P ∪ Q ∪ R := by
    intro b hb
    have hOK := List.all_eq_true.mp h b (by simpa using hb)
    simp only [blockOK, Bool.or_eq_true, Bool.and_eq_true] at hOK
    rcases hOK with (hIJ | hIK) | ⟨hJK, _, _⟩
    · obtain ⟨i, hi, j, hj, hij⟩ := sumHits_spec hIJ
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_add.mpr ⟨i, List.mem_toFinset.mpr hi, j, List.mem_toFinset.mpr hj, hij⟩))
    · obtain ⟨i, hi, k, hk, hik⟩ := sumHits_spec hIK
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_add.mpr ⟨i, List.mem_toFinset.mpr hi, k, List.mem_toFinset.mpr hk, hik⟩))
    · obtain ⟨j, hj, k, hk, hjk⟩ := sumHits_spec hJK
      exact Finset.mem_union_right _
        (Finset.mem_add.mpr ⟨j, List.mem_toFinset.mpr hj, k, List.mem_toFinset.mpr hk, hjk⟩)
  have hP : P.card ≤ I.length * J.length := by
    exact Finset.card_add_le.trans
      (Nat.mul_le_mul (List.toFinset_card_le I) (List.toFinset_card_le J))
  have hQ : Q.card ≤ I.length * K.length := by
    exact Finset.card_add_le.trans
      (Nat.mul_le_mul (List.toFinset_card_le I) (List.toFinset_card_le K))
  have hR : R.card ≤ J.length * K.length := by
    exact Finset.card_add_le.trans
      (Nat.mul_le_mul (List.toFinset_card_le J) (List.toFinset_card_le K))
  have hcard : m ≤ (P ∪ Q ∪ R).card := by simpa using Finset.card_le_card hsub
  have hPQ := Finset.card_union_le P Q
  have hPQR := Finset.card_union_le (P ∪ Q) R
  omega

/-- Three kinds of segments cannot certify a block coefficient above one third. -/
theorem three_mul_covered_blocks_le_sq_segments {I J K : List ℕ} {m : ℕ}
    (h : coversB I J K m = true) :
    3 * m ≤ (I.length + J.length + K.length) ^ 2 := by
  have hm := covered_blocks_le_mixed_products h
  have hs : (3 : ℤ) * (I.length * J.length + I.length * K.length + J.length * K.length) ≤
      ((I.length : ℤ) + J.length + K.length) ^ 2 := by
    nlinarith [sq_nonneg ((I.length : ℤ) - J.length),
      sq_nonneg ((I.length : ℤ) - K.length), sq_nonneg ((J.length : ℤ) - K.length)]
  have hsNat : 3 * (I.length * J.length + I.length * K.length + J.length * K.length) ≤
      (I.length + J.length + K.length) ^ 2 := by exact_mod_cast hs
  omega

end LeanLab.OpenProblems.SearchAdditive2Basis

#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.covered_blocks_le_mixed_products
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.three_mul_covered_blocks_le_sq_segments
