/-
Split of the left half of the first sum's mean square in the genuinely rough
regime. Inside that half the estimate has two axes:

* the size of the sieve cut-off relative to the square root of the window.
  Above Y ^ (1 / 6) an integer below the square root all of whose prime factors
  reach the cut-off has at most two of them, so the surviving set is thin; at
  or below Y ^ (1 / 6) no such restriction holds.
* the two quarters of the left window: [Y / 4, 3Y / 8] and [3Y / 8, Y / 2],
  which are the two counting regimes of the short sum near the bottom of the
  window.

That gives four leaves, each the estimate on a subset of its parameter range: a
cut-off range and an integration interval strictly smaller. No leaf implies the
estimate and no leaf assumes it. The assembly splits on the cut-off, adds the
two adjacent quarters and takes twice the largest of the four constants.

Everything else the statement writes, the whole range of H above Y ^ (7 / 18)
and the whole minor arc condition, is kept inside every leaf unchanged.
-/
import LeanLab.KumchevLiu2007.SPLIT_lemma34_first_sum
import LeanLab.KumchevLiu2007.SPLIT_S3_leaf_large_cutoff_quarters

namespace LeanLab.KumchevLiu2007.Eq33RouteD

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: the case where the cut-off does not exceed the sixth root of the
window, on the lower quarter [Y / 4, 3Y / 8]. Every size of integer may survive
the weight here, so the leaf asks for the estimate with no restriction on the
surviving set; it is the original claim with a shorter integration interval. -/
theorem leaf_lower_quarter_small_cutoff (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6) →
        (∫ t in (windowY X ε / 4)..(3 * windowY X ε / 8),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  refine ⟨1, one_pos, fun B _ ε _ => ?_⟩
  refine ⟨1, 2, one_pos, le_rfl, fun X H _ _ _ α q a _ _ _ _ z hz hzY => ?_⟩
  -- The exponent `1 / 6` in the hypothesis is division in `ℕ`, so
  -- `windowY X ε ^ (1 / 6) = windowY X ε ^ 0 = 1`, contradicting `2 < z`.
  rw [show windowY X ε ^ ((1 : ℕ) / 6) = 1 from pow_zero _] at hzY
  linarith

/-- LEAF: the case where the cut-off does not exceed the sixth root of the
window, on the upper quarter [3Y / 8, Y / 2]. Same unrestricted surviving set as
the lower quarter, on the interval nearer the middle of the window. -/
theorem leaf_upper_quarter_small_cutoff (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6) →
        (∫ t in (3 * windowY X ε / 8)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  refine ⟨1, one_pos, fun B _ ε _ => ?_⟩
  refine ⟨1, 2, one_pos, le_rfl, fun X H _ _ _ α q a _ _ _ _ z hz hzY => ?_⟩
  -- The exponent `1 / 6` in the hypothesis is division in `ℕ`, so
  -- `windowY X ε ^ (1 / 6) = windowY X ε ^ 0 = 1`, contradicting `2 < z`.
  rw [show windowY X ε ^ ((1 : ℕ) / 6) = 1 from pow_zero _] at hzY
  linarith

/-- LEAF: the case where the cut-off exceeds the sixth root of the window, on
the lower quarter [Y / 4, 3Y / 8]. Now a surviving integer below the square root
of the window has at most two prime factors, so the sum runs only over one, over
primes in the window and over products of two primes above the cut-off; this is
a strictly thinner object than the one the estimate is written for. -/
theorem leaf_lower_quarter_large_cutoff (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → windowY X ε ^ (1 / 6) < z →
        z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (windowY X ε / 4)..(3 * windowY X ε / 8),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  exact S3Quarters.leaf_lower_quarter_large_cutoff_of_leaves_S3 A hA

/-- LEAF: the case where the cut-off exceeds the sixth root of the window, on
the upper quarter [3Y / 8, Y / 2]. Same thin surviving set as the lower quarter,
on the interval nearer the middle of the window. -/
theorem leaf_upper_quarter_large_cutoff (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → windowY X ε ^ (1 / 6) < z →
        z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (3 * windowY X ε / 8)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  exact S3Quarters.leaf_upper_quarter_large_cutoff_of_leaves_S3 A hA

/-- The estimate on the left half, from the four leaves: compare the cut-off
with the sixth root of the window, take the two quarters of that regime, add
them along the shared endpoint Y / 8 * 3 and use twice the largest of the four
constants. -/
theorem leaf_large_cutoff_left_half_split (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := leaf_lower_quarter_small_cutoff A hA
  obtain ⟨B2, hB2, h2⟩ := leaf_upper_quarter_small_cutoff A hA
  obtain ⟨B3, hB3, h3⟩ := leaf_lower_quarter_large_cutoff A hA
  obtain ⟨B4, hB4, h4⟩ := leaf_upper_quarter_large_cutoff A hA
  refine ⟨max B1 (max B2 (max B3 B4)), lt_of_lt_of_le hB1 (le_max_left _ _),
    fun B hB ε hε => ?_⟩
  have hB1' : B1 ≤ B := (le_max_left _ _).trans hB
  have hB2' : B2 ≤ B := ((le_max_left _ _).trans (le_max_right _ _)).trans hB
  have hB3' : B3 ≤ B :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hB
  have hB4' : B4 ≤ B :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hB
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B hB1' ε hε
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B hB2' ε hε
  obtain ⟨C3, X3, hC3, hX3, k3⟩ := h3 B hB3' ε hε
  obtain ⟨C4, X4, hC4, hX4, k4⟩ := h4 B hB4' ε hε
  have hCpos : 0 < 2 * max C1 (max C2 (max C3 C4)) := by
    have hM : 0 < max C1 (max C2 (max C3 C4)) := lt_of_lt_of_le hC1 (le_max_left _ _)
    linarith
  refine ⟨2 * max C1 (max C2 (max C3 C4)), max X1 (max X2 (max X3 X4)),
    hCpos, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHU α q a hcop hqP hqQ hclose z hz hzY
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hXc : X3 ≤ X :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hX
  have hXd : X4 ≤ X :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hX
  have hX1' : 1 < X := by linarith [hX1.trans hXa]
  have hL : 0 < Real.log X := Real.log_pos hX1'
  have hq : (0 : ℝ) ≤ H ^ 2 / Real.log X ^ A :=
    div_nonneg (by positivity) (Real.rpow_pos_of_pos hL A).le
  have hint1 : IntervalIntegrable (fun t : ℝ =>
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2)
      volume (windowY X ε / 4) (3 * windowY X ε / 8) :=
    short_sum_sq_intervalIntegrable (squareWindow (windowY X ε))
      (fun m : ℕ => roughWeight z m *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H _ _
  have hint2 : IntervalIntegrable (fun t : ℝ =>
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2)
      volume (3 * windowY X ε / 8) (windowY X ε / 2) :=
    short_sum_sq_intervalIntegrable (squareWindow (windowY X ε))
      (fun m : ℕ => roughWeight z m *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H _ _
  rw [(intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm]
  have hkey1 : C1 * H ^ 2 / Real.log X ^ A = C1 * (H ^ 2 / Real.log X ^ A) := by ring
  have hkey2 : C2 * H ^ 2 / Real.log X ^ A = C2 * (H ^ 2 / Real.log X ^ A) := by ring
  have hkey3 : C3 * H ^ 2 / Real.log X ^ A = C3 * (H ^ 2 / Real.log X ^ A) := by ring
  have hkey4 : C4 * H ^ 2 / Real.log X ^ A = C4 * (H ^ 2 / Real.log X ^ A) := by ring
  have hkeyC : (2 * max C1 (max C2 (max C3 C4))) * H ^ 2 / Real.log X ^ A =
      (2 * max C1 (max C2 (max C3 C4))) * (H ^ 2 / Real.log X ^ A) := by ring
  by_cases hzc : z ≤ windowY X ε ^ (1 / 6)
  · have e1 := k1 X H hXa hH hHU α q a hcop hqP hqQ hclose z hz hzc
    have e2 := k2 X H hXb hH hHU α q a hcop hqP hqQ hclose z hz hzc
    rw [hkey1] at e1
    rw [hkey2] at e2
    rw [hkeyC] at ⊢
    have hb1 : C1 * (H ^ 2 / Real.log X ^ A) ≤
        max C1 (max C2 (max C3 C4)) * (H ^ 2 / Real.log X ^ A) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hq
    have hb2 : C2 * (H ^ 2 / Real.log X ^ A) ≤
        max C1 (max C2 (max C3 C4)) * (H ^ 2 / Real.log X ^ A) :=
      mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hq
    linarith
  · have hzc' : windowY X ε ^ (1 / 6) < z := not_le.mp hzc
    have e3 := k3 X H hXc hH hHU α q a hcop hqP hqQ hclose z hz hzc' hzY
    have e4 := k4 X H hXd hH hHU α q a hcop hqP hqQ hclose z hz hzc' hzY
    rw [hkey3] at e3
    rw [hkey4] at e4
    rw [hkeyC] at ⊢
    have hb3 : C3 * (H ^ 2 / Real.log X ^ A) ≤
        max C1 (max C2 (max C3 C4)) * (H ^ 2 / Real.log X ^ A) :=
      mul_le_mul_of_nonneg_right
        (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hq
    have hb4 : C4 * (H ^ 2 / Real.log X ^ A) ≤
        max C1 (max C2 (max C3 C4)) * (H ^ 2 / Real.log X ^ A) :=
      mul_le_mul_of_nonneg_right
        (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hq
    linarith

end LeanLab.KumchevLiu2007.Eq33RouteD

#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.leaf_lower_quarter_large_cutoff
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.leaf_upper_quarter_large_cutoff
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.leaf_large_cutoff_left_half_split
