/-
P0079 page 10, Section 5, summation of the inverse-square interval bounds.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.CountBounds293

open Real MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 10, Section 5, and Parsell page 371. A step of length h
in the inverse-square tail is bounded by a telescoping reciprocal difference. -/
theorem inverse_square_step396 (a h : ℝ) (hh : 0 < h) (ha : h ≤ a) :
    h / a ^ 2 ≤ 2 / a - 2 / (a + h) := by
  have ha0 : 0 < a := hh.trans_le ha
  have hap : 0 < a + h := by positivity
  have heq : 2 / a - 2 / (a + h) = 2 * h / (a * (a + h)) := by
    field_simp
    ring
  rw [heq]
  apply (div_le_div_iff₀ (sq_pos_of_pos ha0) (mul_pos ha0 hap)).mpr
  nlinarith [mul_nonneg (mul_nonneg hh.le ha0.le) (sub_nonneg.mpr ha)]

/-- P0079 page 10, Section 5, and Parsell page 371. Summing the weighted
interval estimates and passing to the improper integral gives the tail bound.
No prime number theorem or periodicity input is hidden in this summation step. -/
theorem integral_tail_of_blocks396 (f : ℝ → ℝ) (hf : Integrable f)
    (a h A : ℝ) (hh : 0 < h) (ha : h ≤ a) (hA : 0 ≤ A)
    (hblocks : ∀ n : ℕ,
      (∫ x in (a + n * h)..(a + (n + 1) * h), f x) ≤ A * h / (a + n * h) ^ 2) :
    (∫ x in Set.Ioi a, f x) ≤ 2 * A / a := by
  have ha0 : 0 < a := hh.trans_le ha
  have hb (n : ℕ) : 0 < a + n * h := by positivity
  have H (n : ℕ) : (∫ x in a..(a + n * h), f x) ≤
      2 * A / a - 2 * A / (a + n * h) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep := mul_le_mul_of_nonneg_left
        (inverse_square_step396 (a + n * h) h hh (by nlinarith [Nat.cast_nonneg (α := ℝ) n])) hA
      have hstep' : A * h / (a + n * h) ^ 2 ≤
          2 * A / (a + n * h) - 2 * A / (a + (n + 1) * h) := by
        convert hstep using 1 <;> push_cast <;> ring
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (b := a + (n : ℝ) * h) hf.intervalIntegrable hf.intervalIntegrable]
      have hi := hblocks n
      push_cast at hi ⊢
      linarith
  have hlim : Tendsto (fun n : ℕ => a + n * h) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const hh)
  apply le_of_tendsto (intervalIntegral_tendsto_integral_Ioi a hf.integrableOn hlim)
  apply Eventually.of_forall
  intro n
  exact (H n).trans (sub_le_self _ (by positivity))

end LeanLab.LZPowersOfTwo
