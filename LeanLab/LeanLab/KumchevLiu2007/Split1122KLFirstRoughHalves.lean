/-
S43 0149, burst-20261122. Kumchev and Liu 2007, P0088, arXiv 0801.0130.
Restates the large cutoff leaf Prep1121DKLRoughCut.first_rough_block as two
half window leaves, the form of SPLIT_lemma34_first_sum: Lemma 3.4 of page 11
integrates over [x, 2x], so x = Y/4 gives [Y/4, Y/2] and x = Y/2 gives [Y/2, Y].
In the block range y = H <= Y P^(-4) <= Y/4 <= x, so the y <= x condition of
Lemma 3.4 holds in both halves. The assembly by integral_add_adjacent_intervals
is PROVED and yields the exact statements of Prep1121DKLRoughCut.first_rough_block
and Prep1121KLRough.first_sum_block. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121DKLRoughCut
import LeanLab.KumchevLiu2007.SPLIT_lemma34_first_sum
import LeanLab.KumchevLiu2007.Split1122KLLemma34M1

namespace LeanLab.KumchevLiu2007.Split1122KLFirstRoughHalves

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 11 Lemma 3.4 with x = Y/4, its integral over [x, 2x], applied on page 15 to the first sum of display 52,
left half [Y/4, Y/2] of the window, block
range X^(7/18+eps) P^(-4) <= H <= Y P^(-4), cutoff 2 < z <= z1 = Y^(1/6+eps/2),
y = H <= x. HARD. -/
theorem block_rough_left_half (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in windowY X ε / 4..windowY X ε / 2,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  exact Split1122KLLemma34M1.block_rough_left_half_of_lemma34 A hA

/-- LEAF: P0088 page 11 Lemma 3.4 with x = Y/2, its integral over [x, 2x], applied on page 15 to the first sum of display 52,
right half [Y/2, Y] of the window, block
range X^(7/18+eps) P^(-4) <= H <= Y P^(-4), cutoff 2 < z <= z1 = Y^(1/6+eps/2),
y = H <= x. HARD. -/
theorem block_rough_right_half (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in windowY X ε / 2..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  exact Split1122KLLemma34M1.block_rough_right_half_of_lemma34 A hA

/-- PROVED from the two half leaves. P0088 page 11 Lemma 3.4 over [x, 2x] with
x = Y/4 and x = Y/2 covers [Y/4, Y]; page 15 display 52 first sum. The exact type of
Prep1121DKLRoughCut.first_rough_block, constant C1 + C2. No sorry of its own. -/
theorem first_rough_block_of_halves (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := block_rough_left_half A hA
  obtain ⟨B2, hB2, h2⟩ := block_rough_right_half A hA
  refine ⟨max B1 B2, lt_max_of_lt_left hB1, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hε'
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε hε'
  refine ⟨C1 + C2, max X1 X2, by linarith, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose z hz2 hz
  have e1 := k1 X H ((le_max_left _ _).trans hX) hlo hhi α q a hcop hqP hqQ hclose z hz2 hz
  have e2 := k2 X H ((le_max_right _ _).trans hX) hlo hhi α q a hcop hqP hqQ hclose z hz2 hz
  have hint1 := short_sum_sq_intervalIntegrable (squareWindow (windowY X ε))
      (fun m : ℕ => roughWeight z m *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H
      (windowY X ε / 4) (windowY X ε / 2)
  have hint2 := short_sum_sq_intervalIntegrable (squareWindow (windowY X ε))
      (fun m : ℕ => roughWeight z m *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H
      (windowY X ε / 2) (windowY X ε)
  rw [(intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm]
  have hsum : (C1 + C2) * H ^ 2 / Real.log X ^ A =
      C1 * H ^ 2 / Real.log X ^ A + C2 * H ^ 2 / Real.log X ^ A := by ring
  rw [hsum]
  exact add_le_add e1 e2

example : type_of% @Prep1121DKLRoughCut.first_rough_block := first_rough_block_of_halves

/-- PROVED. The exact statement of Prep1121KLRough.first_sum_block, P0088 page 15
display 52 first sum via page 11 Lemma 3.4, from Prep1121DKLRoughCut.first_small_block
and first_rough_block_of_halves; the proof of first_sum_block_of_pieces. -/
theorem first_sum_block_of_halves (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := Prep1121DKLRoughCut.first_small_block A hA
  obtain ⟨B2, hB2, h2⟩ := first_rough_block_of_halves A hA
  refine ⟨max B1 B2, lt_max_of_lt_left hB1, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hε'
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε hε'
  refine ⟨max C1 C2, max X1 X2, lt_max_of_lt_left hC1, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose z hz
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hq : 0 ≤ H ^ 2 / Real.log X ^ A := by positivity
  have r1 : C1 * H ^ 2 / Real.log X ^ A ≤ max C1 C2 * H ^ 2 / Real.log X ^ A := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hq
  have r2 : C2 * H ^ 2 / Real.log X ^ A ≤ max C1 C2 * H ^ 2 / Real.log X ^ A := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hq
  by_cases hz2 : z ≤ 2
  · simp only [Prep1121DKLRoughCut.roughWeight_eq_one_of_le_two hz2, one_mul]
    exact (k1 X H hXa hlo hhi α q a hcop hqP hqQ hclose).trans r1
  · exact (k2 X H hXb hlo hhi α q a hcop hqP hqQ hclose z (lt_of_not_ge hz2) hz).trans r2

example : type_of% @Prep1121KLRough.first_sum_block := first_sum_block_of_halves

end LeanLab.KumchevLiu2007.Split1122KLFirstRoughHalves

#print axioms LeanLab.KumchevLiu2007.Split1122KLFirstRoughHalves.block_rough_left_half
#print axioms LeanLab.KumchevLiu2007.Split1122KLFirstRoughHalves.block_rough_right_half
#print axioms LeanLab.KumchevLiu2007.Split1122KLFirstRoughHalves.first_rough_block_of_halves
#print axioms LeanLab.KumchevLiu2007.Split1122KLFirstRoughHalves.first_sum_block_of_halves
