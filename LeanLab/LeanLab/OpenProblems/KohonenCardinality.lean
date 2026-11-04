import LeanLab.OpenProblems.SearchAdditive2Basis

/-!
# Cardinality of Kohonen's explicit family

AI wrote the Lean code. Goldbach remains OPEN. This is known mathematics.
Source: Kohonen, https://arxiv.org/abs/1606.04770, version 2,
page 2 the elementary segments and page 5 the size `42*t + 7`.
All three segments stay inside one block when t is at least two.
-/

namespace LeanLab.OpenProblems.SearchAdditive2Basis

/-- Each elementary segment is contained in one block for t at least two. -/
theorem segments_lt_block (t : ℕ) (ht : 2 ≤ t) :
    (∀ x ∈ V t, x < t ^ 2) ∧ (∀ x ∈ H t, x < t ^ 2) ∧ (∀ x ∈ S t, x < t ^ 2) := by
  constructor
  · intro x hx
    simp only [V, Finset.mem_range] at hx
    nlinarith
  constructor
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' : i < t := Finset.mem_range.mp hi
    have h := Nat.mul_lt_mul_of_pos_right hi' (by omega : 0 < t)
    nlinarith
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' : i + 1 ≤ t := by have := Finset.mem_range.mp hi; omega
    have h := Nat.mul_le_mul_right (t + 1) hi'
    nlinarith

/-- The quotient by block size recovers the placement index. -/
theorem place_block {t : ℕ} {U : Finset ℕ} {B : List ℕ} {x : ℕ}
    (ht : 0 < t) (hU : ∀ u ∈ U, u < t ^ 2) (hx : x ∈ place t U B) :
    x / t ^ 2 ∈ B.toFinset := by
  simp only [place, Finset.mem_biUnion, Finset.mem_image] at hx
  obtain ⟨b, hb, u, hu, rfl⟩ := hx
  simpa only [Nat.add_mul_div_left _ _ (pow_pos ht 2), Nat.div_eq_of_lt (hU u hu),
    Nat.zero_add] using hb

/-- Distinct blocks give disjoint translates, so placement cardinality is exact. -/
theorem card_place_eq {t : ℕ} {U : Finset ℕ} (B : List ℕ)
    (ht : 0 < t) (hU : ∀ u ∈ U, u < t ^ 2) :
    (place t U B).card = B.toFinset.card * U.card := by
  have hdis : (B.toFinset : Set ℕ).PairwiseDisjoint
      (fun b => U.image (fun u => u + t ^ 2 * b)) := by
    intro b _ c _ hbc
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hy
    have h := congrArg (fun n => n / t ^ 2) heq
    simp only [Nat.add_mul_div_left _ _ (pow_pos ht 2), Nat.div_eq_of_lt (hU u hu),
      Nat.div_eq_of_lt (hU v hv), Nat.zero_add] at h
    exact hbc h.symm
  have himg : ∀ b : ℕ, (U.image (fun u => u + t ^ 2 * b)).card = U.card := by
    intro b
    exact Finset.card_image_of_injective _ (by intro u v h; dsimp only at h; omega)
  rw [place, Finset.card_biUnion hdis]
  simp [himg]

/-- Disjoint placement block sets give disjoint placed families. -/
theorem disjoint_place_of_blocks {t : ℕ} {U W : Finset ℕ} {B C : List ℕ}
    (ht : 0 < t) (hU : ∀ u ∈ U, u < t ^ 2) (hW : ∀ w ∈ W, w < t ^ 2)
    (hblocks : Disjoint B.toFinset C.toFinset) : Disjoint (place t U B) (place t W C) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact Finset.disjoint_left.mp hblocks (place_block ht hU hx) (place_block ht hW hy)

/-- The exact size printed on page five. Zero is the sole overlap of the placed families. -/
theorem kohonen_basis_card (t : ℕ) (ht : 2 ≤ t) :
    (basis t kI kJ kK).card = 42 * t + 7 := by
  have ht0 : 0 < t := by omega
  obtain ⟨hV, hH, hS⟩ := segments_lt_block t ht
  let P := place t (V t) kI
  let Q := place t (H t) kJ
  let R := place t (S t) kK
  have hIcard : kI.toFinset.card = 8 := by decide +kernel
  have hJcard : kJ.toFinset.card = 17 := by decide +kernel
  have hKcard : kK.toFinset.card = 17 := by decide +kernel
  have hVcard : (V t).card = t + 1 := by simp [V]
  have hHcard : (H t).card = t := by
    rw [H, Finset.card_image_of_injective _ (by
      intro x y h
      exact Nat.eq_of_mul_eq_mul_right ht0 h)]
    simp
  have hScard : (S t).card = t := by
    rw [S, Finset.card_image_of_injective _ (by
      intro x y h
      exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < t + 1) h)]
    simp
  have hP : P.card = 8 * (t + 1) := by
    dsimp only [P]
    rw [card_place_eq kI ht0 hV, hIcard, hVcard]
  have hQ : Q.card = 17 * t := by
    dsimp only [Q]
    rw [card_place_eq kJ ht0 hH, hJcard, hHcard]
  have hR : R.card = 17 * t := by
    dsimp only [R]
    rw [card_place_eq kK ht0 hS, hKcard, hScard]
  have hPQ : Disjoint P Q := disjoint_place_of_blocks ht0 hV hH (by decide +kernel)
  have hQR : Disjoint Q R := disjoint_place_of_blocks ht0 hH hS (by decide +kernel)
  have hIK : kI.toFinset ∩ kK.toFinset = {0} := by decide +kernel
  have hPR : P ∩ R = {0} := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxP, hxR⟩ := Finset.mem_inter.mp hx
      have hbP := place_block ht0 hV hxP
      have hbR := place_block ht0 hS hxR
      have hxblock : x / t ^ 2 = 0 := by
        have hmem := Finset.mem_inter.mpr ⟨hbP, hbR⟩
        rw [hIK] at hmem
        simpa only [Finset.mem_singleton] using hmem
      simp only [P, R, place, Finset.mem_biUnion, Finset.mem_image] at hxP hxR
      obtain ⟨b, hb, u, hu, hux⟩ := hxP
      obtain ⟨c, hc, v, hv, hvx⟩ := hxR
      have hb0 : b = 0 := by
        have heq : (u + t ^ 2 * b) / t ^ 2 = b := by
          rw [Nat.add_mul_div_left _ _ (pow_pos ht0 2), Nat.div_eq_of_lt (hV u hu)]
          simp
        have := congrArg (fun n => n / t ^ 2) hux
        omega
      have hc0 : c = 0 := by
        have heq : (v + t ^ 2 * c) / t ^ 2 = c := by
          rw [Nat.add_mul_div_left _ _ (pow_pos ht0 2), Nat.div_eq_of_lt (hS v hv)]
          simp
        have := congrArg (fun n => n / t ^ 2) hvx
        omega
      have hux' : u = x := by simpa only [hb0, mul_zero, add_zero] using hux
      have hvx' : v = x := by simpa only [hc0, mul_zero, add_zero] using hvx
      rw [hux'] at hu
      rw [hvx'] at hv
      have hxV : x ≤ t := by simpa only [V, Finset.mem_range, Nat.lt_succ_iff] using hu
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hv
      have hi0 : i = 0 := by
        by_contra hn
        have hi1 : 1 ≤ i := by omega
        have hmul := Nat.mul_le_mul_right (t + 1) hi1
        nlinarith
      have hx0 : x = 0 := by rw [hi0] at hix; simp at hix; omega
      simpa only [Finset.mem_singleton] using hx0
    · intro hx
      have hx0 : x = 0 := Finset.mem_singleton.mp hx
      subst x
      have hV0 : 0 ∈ V t := by simp [V]
      have hS0 : 0 ∈ S t := Finset.mem_image.mpr ⟨0, by simpa using ht0, by simp⟩
      exact Finset.mem_inter.mpr
        ⟨by simpa only [mul_zero, add_zero] using mem_place hV0 (show 0 ∈ kI by decide +kernel),
         by simpa only [mul_zero, add_zero] using mem_place hS0 (show 0 ∈ kK by decide +kernel)⟩
  have hInter : (P ∪ Q) ∩ R = {0} := by
    rw [Finset.union_inter_distrib_right, hPR, Finset.disjoint_iff_inter_eq_empty.mp hQR,
      Finset.union_empty]
  have hcard := Finset.card_union_add_card_inter (P ∪ Q) R
  rw [hInter, Finset.card_singleton, Finset.card_union_of_disjoint hPQ, hP, hQ, hR] at hcard
  change (P ∪ Q ∪ R).card = 42 * t + 7
  omega

/-- The endpoint 510 times t squared is represented by the last mixed block. -/
theorem kohonen_endpoint (t : ℕ) (ht : 0 < t) :
    ∃ a ∈ basis t kI kJ kK, ∃ b ∈ basis t kI kJ kK, a + b = 510 * t ^ 2 := by
  have hV : 1 ∈ V t := by simp only [V, Finset.mem_range]; omega
  have hS : (t - 1) * (t + 1) ∈ S t := by
    exact Finset.mem_image.mpr ⟨t - 1, by simpa using (show t - 1 < t by omega), rfl⟩
  have hA : 1 + t ^ 2 * 137 ∈ basis t kI kJ kK := by
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (mem_place hV (show 137 ∈ kI by decide +kernel)))
  have hB : (t - 1) * (t + 1) + t ^ 2 * 372 ∈ basis t kI kJ kK := by
    exact Finset.mem_union_right _ (mem_place hS (show 372 ∈ kK by decide +kernel))
  have hsquare : (t - 1) * (t + 1) + 1 = t ^ 2 := by
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  refine ⟨_, hA, _, hB, ?_⟩
  nlinarith

/-- The page-five finite family: exact size 42t + 7 and range at least 510t squared. -/
theorem kohonen_exact_certificate (t : ℕ) (ht : 2 ≤ t) :
    ∃ A : Finset ℕ, A.card = 42 * t + 7 ∧
      ∀ n ≤ 510 * t ^ 2, ∃ a ∈ A, ∃ b ∈ A, a + b = n := by
  refine ⟨basis t kI kJ kK, kohonen_basis_card t ht, ?_⟩
  intro n hn
  rcases lt_or_eq_of_le hn with hlt | rfl
  · exact sumset_of_covers (by omega) kohonen_covers n hlt
  · exact kohonen_endpoint t (by omega)

end LeanLab.OpenProblems.SearchAdditive2Basis

#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.segments_lt_block
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.place_block
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.card_place_eq
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.disjoint_place_of_blocks

#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.kohonen_basis_card

#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.kohonen_endpoint
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.kohonen_exact_certificate
