import LeanLab.Zhao2025.Lemma23

/-!
The elementary application of Lemma 2.3 in the proof of Lemma 3.1.
Source: Zhao 2025, display 3.9, page 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- The exponential weight controls the square root of the product of two B factors. -/
theorem weighted_sqrt_B (t1 t2 l L l0 : ℝ) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2)
    (hl : 0 < l) (hL : 0 < L) (h0 : 0 ≤ l0) :
    Real.exp (-((t1 + t2) / 2 * max (L - l) 0)) *
      Real.sqrt (B t1 l l0 * B t2 l l0) ≤ Real.sqrt (B t1 L l0 * B t2 L l0) := by
  let d := max (L - l) 0
  have h1 := lemma2_3 t1 l L l0 ht1 hl hL h0
  have h2 := lemma2_3 t2 l L l0 ht2 hl hL h0
  have hb1L := (B_nonneg_order t1 L L l0 ht1 hL h0 le_rfl).1
  have hb2l := (B_nonneg_order t2 l l l0 ht2 hl h0 le_rfl).1
  have hp := mul_le_mul h1 h2 (mul_nonneg (Real.exp_pos _).le hb2l) hb1L
  have hs : Real.exp (-((t1 + t2) / 2 * d)) ^ 2 =
      Real.exp (-(d * t1)) * Real.exp (-(d * t2)) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  change Real.exp (-((t1 + t2) / 2 * d)) * _ ≤ _
  calc
    _ = Real.sqrt (Real.exp (-((t1 + t2) / 2 * d)) ^ 2 * (B t1 l l0 * B t2 l l0)) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]
    _ = Real.sqrt ((Real.exp (-(d * t1)) * B t1 l l0) *
        (Real.exp (-(d * t2)) * B t2 l l0)) := by
      rw [hs]
      congr 1
      ring
    _ ≤ _ := Real.sqrt_le_sqrt hp

#print axioms weighted_sqrt_B

end LeanLab.Zhao2025.Task56
