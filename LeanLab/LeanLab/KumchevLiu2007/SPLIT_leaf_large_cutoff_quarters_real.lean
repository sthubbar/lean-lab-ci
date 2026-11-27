/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 11 Lemma 3.4 as applied on
page 15, burst-20261124 S4-13 and S4-14.

In SPLIT_leaf_large_cutoff_left_half.lean the cut point `windowY X ε ^ (1 / 6)`
is a natural number power with exponent `1 / 6 = 0`, so it equals one. The two
leaves `leaf_lower_quarter_large_cutoff` and `leaf_upper_quarter_large_cutoff`
there therefore cover every cut-off `z` with `2 < z ≤ Y ^ (1/6 + ε/2)`. The
twin file SPLIT_leaf_large_cutoff_left_half_twin.lean already states the same
quarter estimates cut at the real sixth root `Y ^ ((1 : ℝ) / 6)`. This file
closes each of the two old leaves, in its exact statement, from the two twin
leaves on the same quarter: below the real sixth root use the small cut-off
twin leaf, above it the large cut-off twin leaf, with the larger constant and
threshold. No new sorry and no new definition. The file cannot be imported by
the old file because the twin imports it, so the old sorry stays until the
twin leaves are proved.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SPLIT_leaf_large_cutoff_left_half_twin

namespace LeanLab.KumchevLiu2007.Eq33RouteD.SixthTwin1122

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a LeanLab.KumchevLiu2007.Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- Exact statement of `Eq33RouteD.leaf_lower_quarter_large_cutoff`, P0088 page 11
Lemma 3.4 on the quarter [Y / 4, 3Y / 8], from the two real sixth root twin
leaves on that quarter. -/
theorem leaf_lower_quarter_large_cutoff_of_leaves (A : ℝ) (hA : 0 < A) :
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
  obtain ⟨B1, hB1, h1⟩ := leaf_lower_quarter_small_cutoff_real A hA
  obtain ⟨B2, hB2, h2⟩ := leaf_lower_quarter_large_cutoff_real A hA
  refine ⟨max B1 B2, lt_of_lt_of_le hB1 (le_max_left _ _), fun B hB ε hε => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε
  refine ⟨max C1 C2, max X1 X2, lt_of_lt_of_le hC1 (le_max_left _ _),
    hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHU α q a hcop hqP hqQ hclose z hz _ hzY
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith [hX1.trans hXa])
  have hq : (0 : ℝ) ≤ H ^ 2 / Real.log X ^ A :=
    div_nonneg (by positivity) (Real.rpow_pos_of_pos hL A).le
  have hk : ∀ C : ℝ, C * H ^ 2 / Real.log X ^ A = C * (H ^ 2 / Real.log X ^ A) :=
    fun C => by ring
  rw [hk]
  by_cases hzc : z ≤ windowY X ε ^ ((1 : ℝ) / 6)
  · have e := k1 X H hXa hH hHU α q a hcop hqP hqQ hclose z hz hzc
    rw [hk] at e
    exact e.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq)
  · have e := k2 X H hXb hH hHU α q a hcop hqP hqQ hclose z hz (not_le.mp hzc) hzY
    rw [hk] at e
    exact e.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hq)

/-- Exact statement of `Eq33RouteD.leaf_upper_quarter_large_cutoff`, P0088 page 11
Lemma 3.4 on the quarter [3Y / 8, Y / 2], from the two real sixth root twin
leaves on that quarter. -/
theorem leaf_upper_quarter_large_cutoff_of_leaves (A : ℝ) (hA : 0 < A) :
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
  obtain ⟨B1, hB1, h1⟩ := leaf_upper_quarter_small_cutoff_real A hA
  obtain ⟨B2, hB2, h2⟩ := leaf_upper_quarter_large_cutoff_real A hA
  refine ⟨max B1 B2, lt_of_lt_of_le hB1 (le_max_left _ _), fun B hB ε hε => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε
  refine ⟨max C1 C2, max X1 X2, lt_of_lt_of_le hC1 (le_max_left _ _),
    hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHU α q a hcop hqP hqQ hclose z hz _ hzY
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith [hX1.trans hXa])
  have hq : (0 : ℝ) ≤ H ^ 2 / Real.log X ^ A :=
    div_nonneg (by positivity) (Real.rpow_pos_of_pos hL A).le
  have hk : ∀ C : ℝ, C * H ^ 2 / Real.log X ^ A = C * (H ^ 2 / Real.log X ^ A) :=
    fun C => by ring
  rw [hk]
  by_cases hzc : z ≤ windowY X ε ^ ((1 : ℝ) / 6)
  · have e := k1 X H hXa hH hHU α q a hcop hqP hqQ hclose z hz hzc
    rw [hk] at e
    exact e.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq)
  · have e := k2 X H hXb hH hHU α q a hcop hqP hqQ hclose z hz (not_le.mp hzc) hzY
    rw [hk] at e
    exact e.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hq)

end LeanLab.KumchevLiu2007.Eq33RouteD.SixthTwin1122

#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.SixthTwin1122.leaf_lower_quarter_large_cutoff_of_leaves
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.SixthTwin1122.leaf_upper_quarter_large_cutoff_of_leaves
