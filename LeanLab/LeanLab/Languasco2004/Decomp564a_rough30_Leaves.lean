/-
Jia 1996, Lemma 27, pages 280 and 281, with display 40 and Lemma 21, pages 261, 262 and 270.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
Split of Decomp564a.rough30_to_integral into four OPEN leaves and a proved assembly.
The integrand of inner30 is Buchstab's function omega of s = (1 + log (s - 1)) / s on 2 <= s <= 3,
with p = Y^t, q = Y^u and s = (1 - t - u) / u, so that s - 1 = (1 - t) / u - 2.
The leaves are: the Buchstab count for one pair p, q; the prime double sum as a Riemann sum
of the inner30 integral; a Mertens bound for the reciprocal double sum; and the identification
of region label 30 with the five inequalities of region 30 in Jia's table.
-/
import LeanLab.Languasco2004.Model564

namespace LeanLab.Languasco2004.Decomp564aRoughLeaves
open Finset Real Decomp279a Decomp316a Decomp316c GroupSplit548 Model564 Numeric30_548
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF: Jia page 263 display 48 with the Buchstab asymptotic quoted on page 281, Lemma 27.
Class HARD.
For primes p, q in region 30 of Jia's table, the count of q rough integers a in Y < a <= 2Y
with p q dividing a is at least omega of s times Y / (p q log q), here written as
(1 + log (s - 1)) / log (Y / (p q)) with s = log (Y / (p q)) / log q, up to delta Y / (p q log Y).
On region 30, s lies near 2.87, inside 2 <= s <= 3 where omega has this closed form. -/
theorem leaf_buchstab_region30 (δ : ℝ) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ p q : ℕ, p.Prime → q.Prime →
      (Y ^ (34 / 99 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (1649 / 4752 : ℝ) ∧
        (p : ℝ) ^ (-2 : ℝ) * Y ^ (85 / 99 : ℝ) < (q : ℝ) ∧
        (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * Y ^ (85 / 147 : ℝ)) →
      Y / ((p : ℝ) * q) *
          ((1 + Real.log (Real.log (Y / ((p : ℝ) * q)) / Real.log q - 1)) /
            Real.log (Y / ((p : ℝ) * q)))
        - δ * Y / ((p : ℝ) * q * Real.log Y) ≤ (roughCount Y (p * q) q : ℝ) := by
  sorry

/-- LEAF: Jia page 281, Lemma 27, the prime number theorem applied twice to the region 30 sum.
Class HARD.
With p = Y^t and q = Y^u, the double sum over primes of the Buchstab weight divided by p q is a
Riemann sum for the source integral inner30 over 34/99 <= t <= 1649/4752, divided by log Y. -/
theorem leaf_prime_sum_region30 (δ : ℝ) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ((∫ t in (34 / 99 : ℝ)..(1649 / 4752), inner30 t) - δ) / Real.log Y ≤
        ∑ p ∈ range (⌊2 * Y⌋₊ + 1), ∑ q ∈ range (⌊2 * Y⌋₊ + 1),
          if p.Prime ∧ q.Prime ∧
            (Y ^ (34 / 99 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (1649 / 4752 : ℝ) ∧
              (p : ℝ) ^ (-2 : ℝ) * Y ^ (85 / 99 : ℝ) < (q : ℝ) ∧
              (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * Y ^ (85 / 147 : ℝ))
          then (1 + Real.log (Real.log (Y / ((p : ℝ) * q)) / Real.log q - 1)) /
              Real.log (Y / ((p : ℝ) * q)) / ((p : ℝ) * q)
          else 0 := by
  sorry

/-- LEAF: Jia page 281, Lemma 27, the error term of the Buchstab step summed over region 30.
Class MEDIUM.
The reciprocal double sum over region 30 is bounded, by Mertens' estimate for the sum of 1/p
over Y^a < p <= Y^b, which follows from a Chebyshev upper bound and partial summation. -/
theorem leaf_reciprocal_sum_region30 :
    ∃ K Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      (∑ p ∈ range (⌊2 * Y⌋₊ + 1), ∑ q ∈ range (⌊2 * Y⌋₊ + 1),
          if p.Prime ∧ q.Prime ∧
            (Y ^ (34 / 99 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (1649 / 4752 : ℝ) ∧
              (p : ℝ) ^ (-2 : ℝ) * Y ^ (85 / 99 : ℝ) < (q : ℝ) ∧
              (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * Y ^ (85 / 147 : ℝ))
          then 1 / ((p : ℝ) * q) else 0) ≤ K := by
  sorry

/-- LEAF: Jia pages 269 and 280, the table of regions, row 30, and the first matching label rule.
Class MEDIUM.
For Y at least 2 and primes p, q, the first table row containing p, q is row 30 exactly when
p, q satisfy the row 30 inequalities, that is no row 1 to 29 meets row 30.
This is a finite check of linear inequalities in t = log p / log Y and u = log q / log Y. -/
theorem leaf_regionIndex_eq_30_iff (Y : ℝ) (hY : 2 ≤ Y) (p q : ℕ) (hp : p.Prime)
    (hq : q.Prime) :
    regionIndex Y p q ∈ ({30} : Finset ℕ) ↔
      (Y ^ (34 / 99 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (1649 / 4752 : ℝ) ∧
        (p : ℝ) ^ (-2 : ℝ) * Y ^ (85 / 99 : ℝ) < (q : ℝ) ∧
        (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * Y ^ (85 / 147 : ℝ)) := by
  sorry

/-- Jia pages 261, 262, 270 and 281: the exact statement of Decomp564a.rough30_to_integral,
assembled from the four leaves above. CONDITIONAL ON those leaves; no admission of its own. -/
theorem rough30_to_integral_from_leaves (δ : ℝ) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → 2 ≤ Y →
      ((∫ t in (34 / 99 : ℝ)..(1649 / 4752), inner30 t) - δ) * Y / Real.log Y ≤
        roughModel {30} Y := by
  obtain ⟨K, Y3, hK⟩ := leaf_reciprocal_sum_region30
  set K' : ℝ := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  set δ' : ℝ := δ / 2 / (K' + 1) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hδ'K : δ' * K' ≤ δ / 2 := by
    have h1 : δ' * (K' + 1) = δ / 2 := by
      rw [hδ']; field_simp
    nlinarith
  obtain ⟨Y1, h1⟩ := leaf_buchstab_region30 δ' hδ'0
  obtain ⟨Y2, h2⟩ := leaf_prime_sum_region30 (δ / 2) (by positivity)
  refine ⟨max (max Y1 Y2) Y3, ?_⟩
  intro Y hY hY2
  have hY1 : Y1 ≤ Y := (le_max_left _ _).trans ((le_max_left _ _).trans hY)
  have hY2' : Y2 ≤ Y := (le_max_right _ _).trans ((le_max_left _ _).trans hY)
  have hY3 : Y3 ≤ Y := (le_max_right _ _).trans hY
  have hL : 0 < Real.log Y := Real.log_pos (by linarith)
  have hYpos : 0 < Y := by linarith
  set A : ℝ := Y / Real.log Y with hA
  have hA0 : 0 < A := div_pos hYpos hL
  -- the region condition, abbreviated
  set R : ℕ → ℕ → Prop := fun p q =>
    Y ^ (34 / 99 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (1649 / 4752 : ℝ) ∧
      (p : ℝ) ^ (-2 : ℝ) * Y ^ (85 / 99 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * Y ^ (85 / 147 : ℝ) with hR
  set w : ℕ → ℕ → ℝ := fun p q =>
    (1 + Real.log (Real.log (Y / ((p : ℝ) * q)) / Real.log q - 1)) /
      Real.log (Y / ((p : ℝ) * q)) with hw
  have hmodel : roughModel {30} Y =
      ∑ p ∈ range (⌊2 * Y⌋₊ + 1), ∑ q ∈ range (⌊2 * Y⌋₊ + 1),
        if p.Prime ∧ q.Prime ∧ R p q then (roughCount Y (p * q) q : ℝ) else 0 := by
    unfold roughModel
    refine sum_congr rfl (fun p _ => sum_congr rfl (fun q _ => ?_))
    by_cases hp : p.Prime
    · by_cases hq : q.Prime
      · have := leaf_regionIndex_eq_30_iff Y hY2 p q hp hq
        simp only [hp, hq, true_and, hR]
        exact if_congr this rfl rfl
      · simp [hq]
    · simp [hp]
  have hterm : ∀ p q : ℕ,
      Y * (if p.Prime ∧ q.Prime ∧ R p q then w p q / ((p : ℝ) * q) else 0)
        - δ' * A * (if p.Prime ∧ q.Prime ∧ R p q then 1 / ((p : ℝ) * q) else 0)
        ≤ (if p.Prime ∧ q.Prime ∧ R p q then (roughCount Y (p * q) q : ℝ) else 0) := by
    intro p q
    by_cases hc : p.Prime ∧ q.Prime ∧ R p q
    · rw [if_pos hc, if_pos hc, if_pos hc]
      have hb := h1 Y hY1 p q hc.1 hc.2.1 hc.2.2
      have he : Y * (w p q / ((p : ℝ) * q)) - δ' * A * (1 / ((p : ℝ) * q)) =
          Y / ((p : ℝ) * q) * w p q - δ' * Y / ((p : ℝ) * q * Real.log Y) := by
        rw [hA]; ring
      rw [he]; exact hb
    · rw [if_neg hc, if_neg hc, if_neg hc]; simp
  have hsum := sum_le_sum (fun p (_ : p ∈ range (⌊2 * Y⌋₊ + 1)) =>
    sum_le_sum (fun q (_ : q ∈ range (⌊2 * Y⌋₊ + 1)) => hterm p q))
  simp only [sum_sub_distrib, ← mul_sum] at hsum
  have hS2 := h2 Y hY2'
  have hS3 := hK Y hY3
  set S1 := ∑ p ∈ range (⌊2 * Y⌋₊ + 1), ∑ q ∈ range (⌊2 * Y⌋₊ + 1),
    (if p.Prime ∧ q.Prime ∧ R p q then w p q / ((p : ℝ) * q) else 0) with hS1
  set S2 := ∑ p ∈ range (⌊2 * Y⌋₊ + 1), ∑ q ∈ range (⌊2 * Y⌋₊ + 1),
    (if p.Prime ∧ q.Prime ∧ R p q then 1 / ((p : ℝ) * q) else 0) with hS2d
  have hS3' : S2 ≤ K' := hS3.trans (le_max_left _ _)
  have hYS1 : A * ((∫ t in (34 / 99 : ℝ)..(1649 / 4752), inner30 t) - δ / 2) ≤ Y * S1 := by
    have := mul_le_mul_of_nonneg_left hS2 hYpos.le
    calc A * ((∫ t in (34 / 99 : ℝ)..(1649 / 4752), inner30 t) - δ / 2)
        = Y * (((∫ t in (34 / 99 : ℝ)..(1649 / 4752), inner30 t) - δ / 2) / Real.log Y) := by
          rw [hA]; ring
      _ ≤ Y * S1 := this
  have hgoal : ((∫ t in (34 / 99 : ℝ)..(1649 / 4752), inner30 t) - δ) * Y / Real.log Y =
      A * ((∫ t in (34 / 99 : ℝ)..(1649 / 4752), inner30 t) - δ) := by
    rw [hA]; ring
  rw [hgoal, hmodel]
  have hAK : δ' * A * S2 ≤ A * (δ / 2) := by
    have : δ' * S2 ≤ δ / 2 := (mul_le_mul_of_nonneg_left hS3' hδ'0.le).trans hδ'K
    nlinarith
  linarith

#print axioms leaf_buchstab_region30
#print axioms leaf_prime_sum_region30
#print axioms leaf_reciprocal_sum_region30
#print axioms leaf_regionIndex_eq_30_iff
#print axioms rough30_to_integral_from_leaves
end
end LeanLab.Languasco2004.Decomp564aRoughLeaves
