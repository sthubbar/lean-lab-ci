/-
Jia 1996, pages 267 to 286, displays 52 to 65 and Lemmas 24 to 28.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The five group estimates remain OPEN. The sealed leaf is not changed.
-/
import LeanLab.Languasco2004.Decomp316a

namespace LeanLab.Languasco2004.Decomp316c
open Finset Real Decomp279a Decomp316a
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Pages 267 to 269: the six rational exponents of each region D_i.
The row is a, b, c, d, e, f for Y^a < p ≤ Y^b and p^c Y^d < q < p^e Y^f.
The default row is unused. -/
def regionData : ℕ → Fin 6 → ℚ
  | 1 => ![16/135, 89/462, 0, 16/135, 1, 0]
  | 2 => ![89/462, 41/180, 0, 16/135, -29/48, 89/288]
  | 3 => ![41/180, 8/33, 0, 16/135, -29/48, 89/288]
  | 4 => ![41/180, 8/33, -1, 41/90, 1, 0]
  | 5 => ![8/33, 37/150, 0, 16/135, -29/48, 89/288]
  | 6 => ![8/33, 37/150, -1, 41/90, -1, 16/33]
  | 7 => ![37/150, 17/63, 0, 16/135, -29/48, 89/288]
  | 8 => ![37/150, 17/63, -1, 701/1566, -1, 16/33]
  | 9 => ![17/63, 17/57, 0, 16/135, -29/48, 89/288]
  | 10 => ![17/63, 17/57, -1, 701/1566, -1, 16/33]
  | 11 => ![17/63, 17/57, -6/5, 17/30, -1/8, 7/24]
  | 12 => ![17/57, 31/99, 0, 16/135, -29/48, 89/288]
  | 13 => ![17/57, 31/99, -1, 701/1566, -1, 16/33]
  | 14 => ![17/57, 31/99, -12/11, 17/33, -1/8, 7/24]
  | 15 => ![31/99, 17/54, 0, 16/135, -29/48, 89/288]
  | 16 => ![31/99, 17/54, -1, 701/1566, -58/67, 89/201]
  | 17 => ![31/99, 17/54, -12/11, 17/33, -1/8, 7/24]
  | 18 => ![17/54, 221/693, -1, 701/1566, -58/67, 89/201]
  | 19 => ![17/54, 221/693, 0, 17/99, -1/8, 7/24]
  | 20 => ![221/693, 859/2610, -1, 701/1566, -58/67, 89/201]
  | 21 => ![221/693, 859/2610, 0, 17/99, -1, 113/198]
  | 22 => ![859/2610, 109/330, 0, 16/135, -58/67, 89/201]
  | 23 => ![859/2610, 109/330, 0, 17/99, -1, 113/198]
  | 24 => ![109/330, 151/450, 0, 16/135, -58/67, 89/201]
  | 25 => ![109/330, 151/450, 0, 17/99, -6, 20/9]
  | 26 => ![151/450, 34/99, 0, 16/135, -58/67, 89/201]
  | 27 => ![151/450, 34/99, 0, 17/99, 1/4, 1/8]
  | 28 => ![151/450, 34/99, -1, 5/9, 1/3, 7/54]
  | 29 => ![34/99, 1649/4752, 0, 16/135, -58/67, 89/201]
  | 30 => ![34/99, 1649/4752, -2, 85/99, -58/49, 85/147]
  | 31 => ![34/99, 1649/4752, -58/49, 85/147, 1/4, 1/8]
  | 32 => ![1649/4752, 25/72, 0, 16/135, -58/67, 89/201]
  | 33 => ![1649/4752, 25/72, -70/59, 34/59, -58/49, 85/147]
  | 34 => ![1649/4752, 25/72, -58/49, 85/147, 1/4, 1/8]
  | 35 => ![25/72, 10/27, 0, 16/135, -58/67, 89/201]
  | 36 => ![25/72, 10/27, -70/59, 34/59, -58/49, 85/147]
  | 37 => ![25/72, 10/27, -58/49, 85/147, -23/15, 7/9]
  | 38 => ![10/27, 617/1620, -70/59, 34/59, -58/49, 85/147]
  | 39 => ![10/27, 617/1620, -58/49, 85/147, -1, 47/81]
  | 40 => ![617/1620, 1823/4725, -70/59, 34/59, -58/49, 85/147]
  | 41 => ![617/1620, 1823/4725, -58/49, 85/147, -29/19, 89/114]
  | 42 => ![1823/4725, 3041/7830, 0, 16/135, -58/49, 85/147]
  | 43 => ![1823/4725, 3041/7830, -58/49, 85/147, -29/19, 89/114]
  | 44 => ![3041/7830, 11/27, 0, 16/135, -29/19, 89/114]
  | 45 => ![11/27, 34/81, 0, 16/135, -29/19, 89/114]
  | 46 => ![11/27, 34/81, -29/19, 89/114, -35/23, 18/23]
  | 47 => ![11/27, 34/81, -23/8, 17/12, -1/4, 25/72]
  | 48 => ![34/81, 49/114, 0, 16/135, -29/19, 89/114]
  | 49 => ![34/81, 49/114, -29/19, 89/114, -35/23, 18/23]
  | 50 => ![34/81, 49/114, -29/10, 17/12, -1/4, 25/72]
  | 51 => ![49/114, 3397/7830, 0, 16/135, -29/19, 89/114]
  | 52 => ![49/114, 3397/7830, -29/10, 17/12, 1/7, 4/21]
  | 53 => ![3397/7830, 4/9, -35/12, 17/12, -29/10, 17/12]
  | 54 => ![3397/7830, 4/9, -29/10, 17/12, 1/7, 4/21]
  | 55 => ![4/9, 701/1566, -29/10, 17/12, -1/5, 3/10]
  | 56 => ![4/9, 701/1566, -6/5, 34/45, 1/7, 4/21]
  | 57 => ![701/1566, 41/90, 0, 16/135, -1/5, 3/10]
  | 58 => ![701/1566, 41/90, -6/5, 34/45, 1/7, 4/21]
  | 59 => ![41/90, 17/36, 0, 16/135, 1/7, 4/21]
  | 60 => ![17/36, 16/33, 0, 16/135, -1, 46/63]
  | 61 => ![16/33, 307/630, 0, 16/135, -58/9, 89/27]
  | 62 => ![16/33, 307/630, 0, 17/99, -1, 46/63]
  | 63 => ![307/630, 211/432, 0, 16/135, -58/9, 89/27]
  | 64 => ![307/630, 211/432, 0, 17/99, -6, 19/6]
  | 65 => ![211/432, 281/570, 0, 16/135, -58/9, 89/27]
  | 66 => ![211/432, 281/570, -58/9, 89/27, -70/11, 36/11]
  | 67 => ![211/432, 281/570, 0, 17/99, -6, 19/6]
  | 68 => ![281/570, 429/870, 0, 16/135, -58/9, 89/27]
  | 69 => ![429/870, 1/2, 0, 17/99, -1, 40/57]
  | _ => ![0, 0, 0, 0, 0, 0]

/-- Pages 267 to 269 display 52: assign a pair to its first matching region.
Zero denotes no matching region. This removes overlap by construction. -/
def regionIndex (Y : ℝ) (p q : ℕ) : ℕ :=
  if h : ∃ i : ℕ, i ∈ Icc 1 69 ∧
      Y ^ (regionData i 0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (regionData i 1 : ℝ) ∧
      (p : ℝ) ^ (regionData i 2 : ℝ) * Y ^ (regionData i 3 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < (p : ℝ) ^ (regionData i 4 : ℝ) * Y ^ (regionData i 5 : ℝ)
    then Nat.find h else 0

/-- Pages 269, 273, 277, 280 and 282: the five groups of region labels.
The groups are exactly the lists in Lemmas 24 to 28. Zero is unassigned. -/
def groupOf (i : ℕ) : ℕ :=
  if i ∈ ({11,14,17,19,21,23,25,27,28,31,34,37,39,41,43,44,45,48,51} : Finset ℕ) then 1 else
  if i ∈ ({47,50,52,54,55,56,57,58,59,60,61,62,63,64,65,67,68,69} : Finset ℕ) then 2 else
  if i ∈ ({4,6,8,10,13,16,18,20,22,24,26,29,32,35} : Finset ℕ) then 3 else
  if i ∈ ({30,33,36,38,40,42,46,49,53,66} : Finset ℕ) then 4 else
  if i ∈ ({1,2,3,5,7,9,12,15} : Finset ℕ) then 5 else 0

/-- Display 52: the contribution assigned to group j, clipped to the sealed
recovery domain. Clipping and the least label convention are part of each
analytic input, so no geometric coverage claim is assumed. -/
def groupSum (j : ℕ) (N Y : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧
    Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y)),
    ∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
      Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ)))),
      if groupOf (regionIndex Y p q) = j then (sifted N Y n (p * q) q : ℝ) else 0

/-- Display 52: disjoint assigned contributions never exceed the full sum. -/
theorem sum_groups_le_recovery (N Y : ℝ) (n : ℕ) :
    ∑ j ∈ Icc 1 5, groupSum j N Y n ≤ recovery N Y n := by
  unfold groupSum recovery
  rw [sum_comm]
  apply sum_le_sum
  intro p hp
  rw [sum_comm]
  apply sum_le_sum
  intro q hq
  simp only [sum_ite_eq]
  split_ifs
  · exact le_rfl
  · positivity

/-- LEAF. Jia page 269, Lemma 24, supporting display 65 on page 286.
Only the contribution of group 1 is bounded. The bound includes the sealed
finite caps, the recovery domain clipping and the region endpoint conventions. -/
theorem group1_lower :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => groupSum 1 N (localization N ε) n <
        0.422726 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Jia page 273, Lemma 25, supporting display 65 on page 286.
Only the contribution of group 2 is bounded. The bound includes the sealed
finite caps, the recovery domain clipping and the region endpoint conventions. -/
theorem group2_lower :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => groupSum 2 N (localization N ε) n <
        0.347181 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Jia page 277, Lemma 26, supporting display 65 on page 286.
Only the contribution of group 3 is bounded. The bound includes the sealed
finite caps, the recovery domain clipping and the region endpoint conventions. -/
theorem group3_lower :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => groupSum 3 N (localization N ε) n <
        0.298946 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Jia page 280, Lemma 27, supporting display 65 on page 286.
Only the contribution of group 4 is bounded. The bound includes the sealed
finite caps, the recovery domain clipping and the region endpoint conventions. -/
theorem group4_lower :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => groupSum 4 N (localization N ε) n <
        0.024582 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Jia page 282, Lemma 28, supporting display 65 on page 286.
Only the contribution of group 5 is bounded. The bound includes the sealed
finite caps, the recovery domain clipping and the region endpoint conventions. -/
theorem group5_lower :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => groupSum 5 N (localization N ε) n <
        1.010623 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- Page 286 display 65: the five region estimates imply the exact sealed leaf.
CONDITIONAL ON group1_lower through group5_lower. -/
theorem recovery_bound_from_parts :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        recovery N (localization N ε) n < 2.104057 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨e1, he1, h1⟩ := group1_lower
  obtain ⟨e2, he2, h2⟩ := group2_lower
  obtain ⟨e3, he3, h3⟩ := group3_lower
  obtain ⟨e4, he4, h4⟩ := group4_lower
  obtain ⟨e5, he5, h5⟩ := group5_lower
  refine ⟨min (min e1 e2) (min e3 (min e4 e5)),
    lt_min (lt_min he1 he2) (lt_min he3 (lt_min he4 he5)), ?_⟩
  intro ε B hε he hB
  obtain ⟨C1, N1, hC1⟩ := h1 ε B hε (he.trans_le ((min_le_left _ _).trans (min_le_left _ _))) hB
  obtain ⟨C2, N2, hC2⟩ := h2 ε B hε (he.trans_le ((min_le_left _ _).trans (min_le_right _ _))) hB
  obtain ⟨C3, N3, hC3⟩ := h3 ε B hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hB
  obtain ⟨C4, N4, hC4⟩ := h4 ε B hε (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) hB
  obtain ⟨C5, N5, hC5⟩ := h5 ε B hε (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) hB
  refine ⟨C1 + C2 + C3 + C4 + C5, max (max (max N1 N2) (max N3 (max N4 N5))) 2, ?_⟩
  intro N hN
  have hNt : max (max N1 N2) (max N3 (max N4 N5)) ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hN1t : N1 ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hNt
  have hN2t : N2 ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hNt
  have hN3t : N3 ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hNt
  have hN4t : N4 ≤ N := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hNt
  have hN5t : N5 ≤ N := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hNt
  let bad1 := (window N ε).filter (fun n => groupSum 1 N (localization N ε) n <
    0.422726 * scale N (localization N ε) n)
  let bad2 := (window N ε).filter (fun n => groupSum 2 N (localization N ε) n <
    0.347181 * scale N (localization N ε) n)
  let bad3 := (window N ε).filter (fun n => groupSum 3 N (localization N ε) n <
    0.298946 * scale N (localization N ε) n)
  let bad4 := (window N ε).filter (fun n => groupSum 4 N (localization N ε) n <
    0.024582 * scale N (localization N ε) n)
  let bad5 := (window N ε).filter (fun n => groupSum 5 N (localization N ε) n <
    1.010623 * scale N (localization N ε) n)
  have hsub : ((window N ε).filter (fun n =>
      recovery N (localization N ε) n < 2.104057 * scale N (localization N ε) n)) ⊆
        (((bad1 ∪ bad2) ∪ bad3) ∪ bad4) ∪ bad5 := by
    intro n hn
    obtain ⟨hnw, hbad⟩ := mem_filter.mp hn
    by_contra h
    have hnall : n ∉ bad1 ∧ n ∉ bad2 ∧ n ∉ bad3 ∧ n ∉ bad4 ∧ n ∉ bad5 := by
      simpa only [mem_union, not_or, and_assoc] using h
    have hg1 : 0.422726 * scale N (localization N ε) n ≤ groupSum 1 N (localization N ε) n :=
      le_of_not_gt (fun hp => hnall.1 (mem_filter.mpr ⟨hnw, hp⟩))
    have hg2 : 0.347181 * scale N (localization N ε) n ≤ groupSum 2 N (localization N ε) n :=
      le_of_not_gt (fun hp => hnall.2.1 (mem_filter.mpr ⟨hnw, hp⟩))
    have hg3 : 0.298946 * scale N (localization N ε) n ≤ groupSum 3 N (localization N ε) n :=
      le_of_not_gt (fun hp => hnall.2.2.1 (mem_filter.mpr ⟨hnw, hp⟩))
    have hg4 : 0.024582 * scale N (localization N ε) n ≤ groupSum 4 N (localization N ε) n :=
      le_of_not_gt (fun hp => hnall.2.2.2.1 (mem_filter.mpr ⟨hnw, hp⟩))
    have hg5 : 1.010623 * scale N (localization N ε) n ≤ groupSum 5 N (localization N ε) n :=
      le_of_not_gt (fun hp => hnall.2.2.2.2 (mem_filter.mpr ⟨hnw, hp⟩))
    have hs := scale_nonneg n (by linarith : 1 ≤ N)
      (Real.one_le_rpow (by linarith : 1 ≤ N) (by positivity : (0 : ℝ) ≤ 7 / 12 + ε))
    change 0 ≤ scale N (localization N ε) n at hs
    have hg := sum_groups_le_recovery N (localization N ε) n
    norm_num [Finset.sum_Icc_succ_top] at hg
    linarith
  have hc := (card_le_card hsub).trans
    ((card_union_le _ _).trans (Nat.add_le_add_right
      ((card_union_le _ _).trans (Nat.add_le_add_right
        ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)) _)) _))
  have hcr : (((window N ε).filter (fun n =>
      recovery N (localization N ε) n < 2.104057 * scale N (localization N ε) n)).card : ℝ) ≤
        (bad1.card : ℝ) + bad2.card + bad3.card + bad4.card + bad5.card := by exact_mod_cast hc
  have hb := add_le_add (add_le_add (add_le_add
    (add_le_add (hC1 N hN1t) (hC2 N hN2t)) (hC3 N hN3t)) (hC4 N hN4t)) (hC5 N hN5t)
  calc _ ≤ (bad1.card : ℝ) + bad2.card + bad3.card + bad4.card + bad5.card := hcr
       _ ≤ C1 * windowLength N ε / Real.log N ^ B +
           C2 * windowLength N ε / Real.log N ^ B +
           C3 * windowLength N ε / Real.log N ^ B +
           C4 * windowLength N ε / Real.log N ^ B +
           C5 * windowLength N ε / Real.log N ^ B := hb
       _ = _ := by ring

#print axioms sum_groups_le_recovery
#print axioms group1_lower
#print axioms group2_lower
#print axioms group3_lower
#print axioms group4_lower
#print axioms group5_lower
#print axioms recovery_bound_from_parts
end
end LeanLab.Languasco2004.Decomp316c
