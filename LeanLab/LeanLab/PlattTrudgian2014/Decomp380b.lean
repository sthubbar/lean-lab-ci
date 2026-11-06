/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 pages 177 to 179, Lemmas 5 and 6 in the continuous case.
-/
import LeanLab.PlattTrudgian2014.Decomp281a
import LeanLab.PlattTrudgian2014.CosineTransfer125
import LeanLab.PlattTrudgian2014.LambdaBlocks
import LeanLab.PlattTrudgian2014.TransferBridge380

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Finset

/-- P0026 page 178, periodicity of the polynomial tail in the proof of Lemma 5. -/
theorem halfCosPoly_integer_period380 (x : ℝ) (r : ℕ) :
    halfCosPoly125 (x + r * (2 * Real.pi)) = halfCosPoly125 x := by
  unfold halfCosPoly125
  apply sum_congr rfl
  intro j _
  congr 1
  convert Real.cos_add_nat_mul_two_pi ((j : ℝ) * x) ((j : ℕ) * r) using 1 <;>
    push_cast <;> ring

/-- P0026 page 178, the common tail after a dyadic inverse branch. -/
theorem half_product_branch380 (L r : ℕ) (x : ℝ) :
    (∏ j ∈ range (L + 1), halfCosPoly125 (2 * Real.pi * (2 : ℝ) ^ j * ((x + r) / 2))) =
      halfCosPoly125 (2 * Real.pi * ((x + r) / 2)) *
        ∏ j ∈ range L, halfCosPoly125 (2 * Real.pi * (2 : ℝ) ^ j * x) := by
  rw [prod_range_succ']
  simp only [pow_zero, mul_one]
  rw [mul_comm]
  congr 1
  apply prod_congr rfl
  intro j _
  rw [show 2 * Real.pi * (2 : ℝ) ^ (j + 1) * ((x + r) / 2) =
      2 * Real.pi * (2 : ℝ) ^ j * x + ((2 ^ j * r : ℕ) : ℝ) * (2 * Real.pi) by
    push_cast; rw [pow_succ]; ring]
  exact halfCosPoly_integer_period380 _ _

/-- LEAF. P0026 page 178, first change of variable in the proof of Lemma 5.
Split the unit interval into its two inverse branches and pair the first factors.
The product of the remaining factors is the common tail. -/
theorem half_product_halving380 (L : ℕ) (i : Fin 16) :
    halfProductMoment281 (L + 1) i =
      ∫ x : ℝ in 0..1,
        ((Real.cos (2 * Real.pi * (i : ℝ) * (x / 2)) * halfCosPoly125 (2 * Real.pi * (x / 2)) +
          Real.cos (2 * Real.pi * (i : ℝ) * ((x + 1) / 2)) *
            halfCosPoly125 (2 * Real.pi * ((x + 1) / 2))) / 2) *
          ∏ j ∈ range L, halfCosPoly125 (2 * Real.pi * (2 : ℝ) ^ j * x) := by
  unfold halfProductMoment281
  have hf : Continuous (fun x : ℝ => Real.cos (2 * Real.pi * (i : ℝ) * x) *
      ∏ j ∈ range (L + 1), halfCosPoly125 (2 * Real.pi * (2 : ℝ) ^ j * x)) := by
    unfold halfCosPoly125
    fun_prop
  rw [integral_branches hf 2 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, sum_empty, zero_add,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext x
  have h0 := half_product_branch380 L 0 x
  have h1 := half_product_branch380 L 1 x
  simp only [Nat.cast_zero, Nat.cast_one, add_zero] at h0 h1
  rw [h0, h1]
  ring

/-- LEAF. P0026 page 178, h star in Lemma 5, regrouped as the matrix in Lemma 6.
The half period average of the first cosine factors has only even frequencies.
The zero frequency occurs once in each cosine product. -/
theorem half_transfer_cosine380 (i : Fin 16) (y : ℝ) :
    (Real.cos ((i : ℝ) * y) * halfCosPoly125 y +
      Real.cos ((i : ℝ) * (y + Real.pi)) * halfCosPoly125 (y + Real.pi)) / 2 =
        ∑ j : Fin 16, (halfTransfer125 i j : ℝ) * Real.cos (2 * (j : ℝ) * y) := by
  exact half_transfer_cosine_proved380 i y

/-- P0026 pages 178 to 179, exactly the existing continuous matrix recurrence.
The inverse branch integral and finite cosine regrouping leaves are both proved. -/
theorem half_product_recurrence_decomposed380 (L : ℕ) (i : Fin 16) :
    halfProductMoment281 (L + 1) i =
      ∑ j : Fin 16, (halfTransfer125 i j : ℝ) * halfProductMoment281 L j := by
  rw [half_product_halving380]
  have hpoint (x : ℝ) :
      (Real.cos (2 * Real.pi * (i : ℝ) * (x / 2)) * halfCosPoly125 (2 * Real.pi * (x / 2)) +
        Real.cos (2 * Real.pi * (i : ℝ) * ((x + 1) / 2)) *
          halfCosPoly125 (2 * Real.pi * ((x + 1) / 2))) / 2 =
        ∑ j : Fin 16, (halfTransfer125 i j : ℝ) * Real.cos (2 * Real.pi * (j : ℝ) * x) := by
    convert half_transfer_cosine380 i (Real.pi * x) using 1 <;> congr 1 <;> try ring
    funext j
    congr 1
    congr 1
    ring
  simp_rw [hpoint, sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro j _
    unfold halfProductMoment281
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    ring
  · intro j _
    have hcont : Continuous (fun x : ℝ =>
        ((halfTransfer125 i j : ℝ) * Real.cos (2 * Real.pi * (j : ℝ) * x)) *
          ∏ k ∈ range L, halfCosPoly125 (2 * Real.pi * (2 : ℝ) ^ k * x)) := by
      unfold halfCosPoly125
      fun_prop
    exact hcont.intervalIntegrable _ _

set_option format.width 240
#print axioms halfCosPoly_integer_period380
#print axioms half_product_branch380
#print axioms half_product_halving380
#print axioms half_transfer_cosine380
#print axioms half_product_recurrence_decomposed380

end LeanLab.PlattTrudgian2014
