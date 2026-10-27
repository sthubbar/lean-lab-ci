import Mathlib

/-! P0023, pages 168 and 169. AI wrote the Lean code. Binary Goldbach is open. -/

namespace LeanLab.LiuWang2002.Vaughan109

open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction

/-- The part supported on `n ≤ X`, page 169. -/
noncomputable def shortPart (f : ArithmeticFunction ℝ) (X : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if (n : ℝ) ≤ X then f n else 0, by simp⟩

/-- The complementary part, page 169. -/
noncomputable def longPart (f : ArithmeticFunction ℝ) (X : ℝ) : ArithmeticFunction ℝ :=
  f - shortPart f X

/-- First coefficient of display 6.8, page 169. -/
noncomputable def lambda1 (U : ℝ) : ArithmeticFunction ℝ := shortPart Λ U

/-- Second coefficient of display 6.8, page 169. -/
noncomputable def lambda2 (V : ℝ) : ArithmeticFunction ℝ :=
  shortPart (μ : ArithmeticFunction ℝ) V * ArithmeticFunction.log

/-- Third coefficient of display 6.8, page 169. -/
noncomputable def lambda3 (U V : ℝ) : ArithmeticFunction ℝ :=
  -(shortPart Λ U * shortPart (μ : ArithmeticFunction ℝ) V * ζ)

/-- Fourth coefficient of display 6.8, page 169. -/
noncomputable def lambda4 (U V : ℝ) : ArithmeticFunction ℝ :=
  longPart (μ : ArithmeticFunction ℝ) V * (longPart Λ U * ζ)

/-- LEAF. Vaughan coefficient identity 6.7 and 6.8, pages 168 and 169.
Mathlib supplies the Mobius convolution identities used in Davenport page 138. -/
theorem vaughan_coefficients (U V : ℝ) :
    Λ = lambda1 U + lambda2 V + lambda3 U V + lambda4 U V := by
  unfold lambda1 lambda2 lambda3 lambda4 longPart
  rw [← vonMangoldt_mul_zeta]
  have hm : (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) = 1 :=
    coe_moebius_mul_coe_zeta
  linear_combination -(Λ - shortPart Λ U) * hm

/-- Display 3.8, page 144, with its inclusive lower cutoff. -/
noncomputable def weightedSum (f : ArithmeticFunction ℝ) (N c α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (Nat.floor N + 1),
    if c * N ≤ (n : ℝ) then (f n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (α * n)) else 0

/-- Display 3.8 with the general cutoff of Proposition 6.1, page 168. -/
noncomputable def S (N c α : ℝ) : ℂ := weightedSum Λ N c α

/-- First parameter in display 6.6, page 168. -/
noncomputable def U (N : ℝ) : ℝ := N ^ (2 / 5 : ℝ) * Real.log N ^ (-(4 / 5) : ℝ)
/-- Second parameter in display 6.6, page 168. -/
noncomputable def V (N : ℝ) : ℝ := N ^ (2 / 5 : ℝ) * Real.log N ^ (1 / 5 : ℝ)

/-- First sum of display 6.8 with the cutoff of display 3.8. -/
noncomputable def S1 (N c α : ℝ) : ℂ := weightedSum (lambda1 (U N)) N c α
/-- Second sum of display 6.8 with the cutoff of display 3.8. -/
noncomputable def S2 (N c α : ℝ) : ℂ := weightedSum (lambda2 (V N)) N c α
/-- Third sum of display 6.8 with the cutoff of display 3.8. -/
noncomputable def S3 (N c α : ℝ) : ℂ := weightedSum (lambda3 (U N) (V N)) N c α
/-- Fourth sum of display 6.8 with the cutoff of display 3.8. -/
noncomputable def S4 (N c α : ℝ) : ℂ := weightedSum (lambda4 (U N) (V N)) N c α

/-- LEAF. Display 6.7, page 168, with the cutoff of display 3.8. -/
theorem vaughan_sum (N c α : ℝ) : S N c α = S1 N c α + S2 N c α + S3 N c α + S4 N c α := by
  unfold S S1 S2 S3 S4 weightedSum
  rw [vaughan_coefficients (U N) (V N)]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp [ArithmeticFunction.add_apply, Complex.ofReal_add, add_mul]

end LeanLab.LiuWang2002.Vaughan109

#print axioms LeanLab.LiuWang2002.Vaughan109.vaughan_coefficients
#print axioms LeanLab.LiuWang2002.Vaughan109.vaughan_sum
