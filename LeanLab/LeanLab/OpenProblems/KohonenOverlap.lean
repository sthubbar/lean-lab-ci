import LeanLab.OpenProblems.KohonenCardinality

/-!
# Bounded overlaps in the three-segment construction

AI wrote the Lean code. Goldbach remains OPEN. This is known mathematics.
Source: Kohonen, https://arxiv.org/abs/1606.04770, version 2,
page 2 the elementary segments and page 5 the normalization by basis size.
-/

namespace LeanLab.OpenProblems.SearchAdditive2Basis

/-- An intersection of placed families lies in placements of the elementary intersection. -/
theorem place_inter_subset {t : ℕ} {U W : Finset ℕ} {B C : List ℕ}
    (ht : 0 < t) (hU : ∀ u ∈ U, u < t ^ 2) (hW : ∀ w ∈ W, w < t ^ 2) :
    place t U B ∩ place t W C ⊆ place t (U ∩ W) B := by
  intro x hx
  obtain ⟨hxU, hxW⟩ := Finset.mem_inter.mp hx
  simp only [place, Finset.mem_biUnion, Finset.mem_image] at hxU hxW
  obtain ⟨b, hbB, u, hu, hux⟩ := hxU
  obtain ⟨c, hcC, w, hw, hwx⟩ := hxW
  have hb : x / t ^ 2 = b := by
    rw [← hux, Nat.add_mul_div_left _ _ (pow_pos ht 2), Nat.div_eq_of_lt (hU u hu)]
    simp
  have hc : x / t ^ 2 = c := by
    rw [← hwx, Nat.add_mul_div_left _ _ (pow_pos ht 2), Nat.div_eq_of_lt (hW w hw)]
    simp
  have hbc : b = c := by omega
  have huw : u = w := by rw [← hbc] at hwx; omega
  exact Finset.mem_biUnion.mpr ⟨b, hbB,
    Finset.mem_image.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, by rwa [huw]⟩, hux⟩⟩

/-- Elementary segment intersections have uniformly bounded cardinalities. -/
theorem segment_inter_card_le (t : ℕ) (ht : 2 ≤ t) :
    (V t ∩ H t).card ≤ 2 ∧ (V t ∩ S t).card ≤ 1 ∧ (H t ∩ S t).card ≤ 1 := by
  have ht0 : 0 < t := by omega
  have hVH : V t ∩ H t ⊆ {0, t} := by
    intro x hx
    obtain ⟨hxV, hxH⟩ := Finset.mem_inter.mp hx
    have hxle : x ≤ t := by simpa only [V, Finset.mem_range, Nat.lt_succ_iff] using hxV
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hxH
    by_cases hi0 : i = 0
    · have hx0 : x = 0 := by rw [hi0] at hix; simp at hix; omega
      simp [hx0]
    · have hi1 : 1 ≤ i := by omega
      have hmul := Nat.mul_le_mul_right t hi1
      have hxt : x = t := by nlinarith
      simp [hxt]
  have hVS : V t ∩ S t ⊆ {0} := by
    intro x hx
    obtain ⟨hxV, hxS⟩ := Finset.mem_inter.mp hx
    have hxle : x ≤ t := by simpa only [V, Finset.mem_range, Nat.lt_succ_iff] using hxV
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hxS
    have hi0 : i = 0 := by
      by_contra hi0
      have hmul := Nat.mul_le_mul_right (t + 1) (show 1 ≤ i by omega)
      nlinarith
    have hx0 : x = 0 := by rw [hi0] at hix; simp at hix; omega
    simpa only [Finset.mem_singleton] using hx0
  have hHS : H t ∩ S t ⊆ {0} := by
    intro x hx
    obtain ⟨hxH, hxS⟩ := Finset.mem_inter.mp hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hxH
    obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hxS
    have hd : t ∣ j * (t + 1) := by
      rw [hjx, ← hix]
      exact dvd_mul_left t i
    have hcop : Nat.Coprime t (t + 1) := by simp [Nat.coprime_self_add_right]
    have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt (hcop.dvd_of_dvd_mul_right hd)
      (Finset.mem_range.mp hj)
    have hx0 : x = 0 := by rw [hj0] at hjx; simp at hjx; omega
    simpa only [Finset.mem_singleton] using hx0
  refine ⟨(Finset.card_le_card hVH).trans Finset.card_le_two, ?_, ?_⟩
  · simpa using Finset.card_le_card hVS
  · simpa using Finset.card_le_card hHS

/-- Total distinct segment count times t exceeds basis size by at most a fixed overlap budget. -/
theorem card_basis_lower (t : ℕ) (I J K : List ℕ) (ht : 2 ≤ t) :
    (I.toFinset.card + J.toFinset.card + K.toFinset.card) * t ≤
      (basis t I J K).card + 2 * I.toFinset.card + J.toFinset.card := by
  have ht0 : 0 < t := by omega
  obtain ⟨hV, hH, hS⟩ := segments_lt_block t ht
  obtain ⟨hVH, hVS, hHS⟩ := segment_inter_card_le t ht
  let P := place t (V t) I
  let Q := place t (H t) J
  let R := place t (S t) K
  have hVcard : (V t).card = t + 1 := by simp [V]
  have hHcard : (H t).card = t := by
    rw [H, Finset.card_image_of_injective _ (by
      intro x y h; exact Nat.eq_of_mul_eq_mul_right ht0 h)]
    simp
  have hScard : (S t).card = t := by
    rw [S, Finset.card_image_of_injective _ (by
      intro x y h; exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < t + 1) h)]
    simp
  have hP : P.card = I.toFinset.card * (t + 1) := by
    dsimp only [P]
    rw [card_place_eq I ht0 hV, hVcard]
  have hQ : Q.card = J.toFinset.card * t := by
    dsimp only [Q]
    rw [card_place_eq J ht0 hH, hHcard]
  have hR : R.card = K.toFinset.card * t := by
    dsimp only [R]
    rw [card_place_eq K ht0 hS, hScard]
  have hPQ : (P ∩ Q).card ≤ I.toFinset.card * 2 := by
    have hc := Finset.card_le_card (place_inter_subset (B := I) (C := J) ht0 hV hH)
    rw [card_place_eq I ht0 (fun u hu => hV u (Finset.mem_inter.mp hu).1)] at hc
    exact hc.trans (Nat.mul_le_mul_left _ hVH)
  have hPR : (P ∩ R).card ≤ I.toFinset.card := by
    have hc := Finset.card_le_card (place_inter_subset (B := I) (C := K) ht0 hV hS)
    rw [card_place_eq I ht0 (fun u hu => hV u (Finset.mem_inter.mp hu).1)] at hc
    exact (hc.trans (Nat.mul_le_mul_left _ hVS)).trans (by simp)
  have hQR : (Q ∩ R).card ≤ J.toFinset.card := by
    have hc := Finset.card_le_card (place_inter_subset (B := J) (C := K) ht0 hH hS)
    rw [card_place_eq J ht0 (fun u hu => hH u (Finset.mem_inter.mp hu).1)] at hc
    exact (hc.trans (Nat.mul_le_mul_left _ hHS)).trans (by simp)
  have hInter : ((P ∪ Q) ∩ R).card ≤ (P ∩ R).card + (Q ∩ R).card := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_le _ _
  have hPQcard := Finset.card_union_add_card_inter P Q
  have hPQRcard := Finset.card_union_add_card_inter (P ∪ Q) R
  change (I.toFinset.card + J.toFinset.card + K.toFinset.card) * t ≤
    (P ∪ Q ∪ R).card + 2 * I.toFinset.card + J.toFinset.card
  nlinarith

end LeanLab.OpenProblems.SearchAdditive2Basis

#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.place_inter_subset
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.segment_inter_card_le

#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.card_basis_lower
