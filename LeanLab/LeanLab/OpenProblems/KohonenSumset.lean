import LeanLab.OpenProblems.SearchAdditive2Basis

/-!
# Geometric sumset counting for three segment kinds

AI wrote the Lean code. Goldbach remains OPEN. This is known mathematics.
Source: Kohonen, https://arxiv.org/abs/1606.04770, version 2, page 5 Section 3.
The argument counts the six commutative segment-pair kinds. Diagonal segment
sumsets have size linear in t. Mixed segment sumsets have size at most
`t^2 + t`, `t^2 + t`, and `t^2`. No checker completeness assumption is used.
-/

namespace LeanLab.OpenProblems.SearchAdditive2Basis

open scoped Pointwise

/-- The sumset of one arithmetic progression with itself has size at most twice its length. -/
theorem card_progression_add_self_le (t step : ℕ) :
    (((Finset.range t).image (· * step)) + ((Finset.range t).image (· * step))).card ≤ 2 * t := by
  have hsub : ((Finset.range t).image (· * step)) + ((Finset.range t).image (· * step)) ⊆
      (Finset.range (2 * t)).image (· * step) := by
    intro n hn
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    refine Finset.mem_image.mpr ⟨i + j, ?_, ?_⟩
    · simp only [Finset.mem_range] at hi hj ⊢
      omega
    · rw [add_mul]
      exact hab
  have hc := (Finset.card_le_card hsub).trans Finset.card_image_le
  simpa using hc

/-- Pair sums of placements are bounded by placement pairs times the elementary sumset size. -/
theorem card_place_add_le (t : ℕ) (U W : Finset ℕ) (B C : List ℕ) :
    (place t U B + place t W C).card ≤ (B.length * C.length) * (U + W).card := by
  let T := (B.toFinset ×ˢ C.toFinset).biUnion fun bc =>
    (U + W).image (fun z => z + t ^ 2 * (bc.1 + bc.2))
  have hsub : place t U B + place t W C ⊆ T := by
    intro n hn
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.mp hn
    simp only [place, Finset.mem_biUnion, Finset.mem_image] at hx hy
    obtain ⟨b, hb, u, hu, hux⟩ := hx
    obtain ⟨c, hc, w, hw, hwy⟩ := hy
    refine Finset.mem_biUnion.mpr ⟨(b, c), Finset.mem_product.mpr ⟨hb, hc⟩, ?_⟩
    refine Finset.mem_image.mpr ⟨u + w, Finset.add_mem_add hu hw, ?_⟩
    dsimp only
    linear_combination hux + hwy + hxy
  calc
    (place t U B + place t W C).card ≤ T.card := Finset.card_le_card hsub
    _ ≤ (B.toFinset ×ˢ C.toFinset).card * (U + W).card :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun _ _ => Finset.card_image_le)
    _ ≤ (B.length * C.length) * (U + W).card := by
      rw [Finset.card_product]
      exact Nat.mul_le_mul_right _
        (Nat.mul_le_mul (List.toFinset_card_le B) (List.toFinset_card_le C))

/-- In a commutative sumset of three unions, six unordered kinds suffice. -/
theorem card_union_three_add_self_le (P Q R : Finset ℕ) :
    ((P ∪ Q ∪ R) + (P ∪ Q ∪ R)).card ≤
      (P + P).card + (Q + Q).card + (R + R).card +
        (P + Q).card + (P + R).card + (Q + R).card := by
  have heq : (P ∪ Q ∪ R) + (P ∪ Q ∪ R) =
      (P + P) ∪ (Q + Q) ∪ (R + R) ∪ (P + Q) ∪ (P + R) ∪ (Q + R) := by
    ext n
    simp only [Finset.union_add, Finset.add_union, add_comm Q P, add_comm R P,
      add_comm R Q, Finset.mem_union]
    tauto
  rw [heq]
  have h1 := Finset.card_union_le (P + P) (Q + Q)
  have h2 := Finset.card_union_le ((P + P) ∪ (Q + Q)) (R + R)
  have h3 := Finset.card_union_le ((P + P) ∪ (Q + Q) ∪ (R + R)) (P + Q)
  have h4 := Finset.card_union_le ((P + P) ∪ (Q + Q) ∪ (R + R) ∪ (P + Q)) (P + R)
  have h5 := Finset.card_union_le ((P + P) ∪ (Q + Q) ∪ (R + R) ∪ (P + Q) ∪ (P + R)) (Q + R)
  omega

/-- The page-five geometric sumset estimate with an explicit linear remainder.
The quadratic coefficient is the sum of the three mixed placement products. -/
theorem card_basis_add_le (t : ℕ) (I J K : List ℕ) :
    (basis t I J K + basis t I J K).card ≤
      (I.length * J.length + I.length * K.length + J.length * K.length) * t ^ 2 +
      (2 * (I.length ^ 2 + J.length ^ 2 + K.length ^ 2) +
        I.length * J.length + I.length * K.length) * t +
      2 * (I.length ^ 2 + J.length ^ 2 + K.length ^ 2) := by
  have hV : (V t).card = t + 1 := by simp [V]
  have hH : (H t).card ≤ t := Finset.card_image_le.trans (by simp)
  have hS : (S t).card ≤ t := Finset.card_image_le.trans (by simp)
  have hVV : (V t + V t).card ≤ 2 * t + 2 := by
    simpa [V, Nat.mul_add] using card_progression_add_self_le (t + 1) 1
  have hHH : (H t + H t).card ≤ 2 * t + 2 := by
    have h : (H t + H t).card ≤ 2 * t := by
      simpa only [H] using card_progression_add_self_le t t
    omega
  have hSS : (S t + S t).card ≤ 2 * t + 2 := by
    have h : (S t + S t).card ≤ 2 * t := by
      simpa only [S] using card_progression_add_self_le t (t + 1)
    omega
  have hVH : (V t + H t).card ≤ t ^ 2 + t := by
    calc (V t + H t).card ≤ (V t).card * (H t).card := Finset.card_add_le
      _ ≤ (t + 1) * t := Nat.mul_le_mul hV.le hH
      _ = t ^ 2 + t := by ring
  have hVS : (V t + S t).card ≤ t ^ 2 + t := by
    calc (V t + S t).card ≤ (V t).card * (S t).card := Finset.card_add_le
      _ ≤ (t + 1) * t := Nat.mul_le_mul hV.le hS
      _ = t ^ 2 + t := by ring
  have hHS : (H t + S t).card ≤ t ^ 2 := by
    calc (H t + S t).card ≤ (H t).card * (S t).card := Finset.card_add_le
      _ ≤ t * t := Nat.mul_le_mul hH hS
      _ = t ^ 2 := by ring
  have hPP := (card_place_add_le t (V t) (V t) I I).trans
    (Nat.mul_le_mul_left (I.length * I.length) hVV)
  have hQQ := (card_place_add_le t (H t) (H t) J J).trans
    (Nat.mul_le_mul_left (J.length * J.length) hHH)
  have hRR := (card_place_add_le t (S t) (S t) K K).trans
    (Nat.mul_le_mul_left (K.length * K.length) hSS)
  have hPQ := (card_place_add_le t (V t) (H t) I J).trans
    (Nat.mul_le_mul_left (I.length * J.length) hVH)
  have hPR := (card_place_add_le t (V t) (S t) I K).trans
    (Nat.mul_le_mul_left (I.length * K.length) hVS)
  have hQR := (card_place_add_le t (H t) (S t) J K).trans
    (Nat.mul_le_mul_left (J.length * K.length) hHS)
  have hUnion := card_union_three_add_self_le (place t (V t) I) (place t (H t) J)
    (place t (S t) K)
  have hsum : (basis t I J K + basis t I J K).card ≤
      (I.length * I.length) * (2 * t + 2) +
      (J.length * J.length) * (2 * t + 2) +
      (K.length * K.length) * (2 * t + 2) +
      (I.length * J.length) * (t ^ 2 + t) +
      (I.length * K.length) * (t ^ 2 + t) +
      (J.length * K.length) * t ^ 2 := by
    change (basis t I J K + basis t I J K).card ≤ _ at hUnion
    omega
  calc
    (basis t I J K + basis t I J K).card ≤ _ := hsum
    _ = _ := by ring

end LeanLab.OpenProblems.SearchAdditive2Basis

#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.card_progression_add_self_le
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.card_place_add_le
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.card_union_three_add_self_le

#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.card_basis_add_le
