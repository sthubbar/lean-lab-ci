/- AI wrote the Lean code. Goldbach is open.
Task616 U-1690, Buchstab1938 p. 383 integral and p. 384 iteration. -/
import Mathlib

open MeasureTheory intervalIntegral
noncomputable section
namespace LeanLab.AlmostPrimeSums.Kernel616

/-- The common kernel in Buchstab Theorems 1 and 2 on pp. 381 and 383. -/
def kernel (z : ℝ) : ℝ := (z + 1) / z ^ 2

/-- The Buchstab kernel is positive on the integration domain. -/
theorem kernel_pos {z : ℝ} (hz : 0 < z) : 0 < kernel z := by
  unfold kernel
  positivity

/-- Left and right rectangles bound the kernel on every positive cell. -/
theorem kernel_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : kernel b ≤ kernel a := by
  have hb : 0 < b := ha.trans_le hab
  unfold kernel
  apply (div_le_div_iff₀ (sq_pos_of_pos hb) (sq_pos_of_pos ha)).mpr
  have hp : 0 ≤ (b - a) * (a * b + a + b) :=
    mul_nonneg (sub_nonneg.mpr hab) (by positivity)
  nlinarith

/-- Exact one cell integral bounds for nonnegative step majorants and minorants.
The kernel uses opposite endpoints because it decreases. -/
theorem rectangle_bounds {a b L U : ℝ} {f : ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L)
    (hf : IntervalIntegrable (fun z => f z * kernel z) volume a b)
    (hbounds : ∀ z ∈ Set.Icc a b, L ≤ f z ∧ f z ≤ U) :
    L * (b - a) * kernel b ≤ (∫ z in a..b, f z * kernel z) ∧
    (∫ z in a..b, f z * kernel z) ≤ U * (b - a) * kernel a := by
  have hU : 0 ≤ U := hL.trans ((hbounds a ⟨le_rfl, hab⟩).1.trans (hbounds a ⟨le_rfl, hab⟩).2)
  constructor
  · have h := integral_mono_on hab (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => L * kernel b) volume a b) hf (by
      intro z hz
      exact mul_le_mul (hbounds z hz).1 (kernel_antitone (ha.trans_le hz.1) hz.2)
        (kernel_pos (ha.trans_le hab)).le (hL.trans (hbounds z hz).1))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_left_comm, mul_comm, mul_assoc] using h
  · have h := integral_mono_on hab hf (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => U * kernel a) volume a b) (by
      intro z hz
      exact mul_le_mul (hbounds z hz).2 (kernel_antitone ha hz.1)
        (kernel_pos (ha.trans_le hz.1)).le hU)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_left_comm, mul_comm, mul_assoc] using h

/-- The right and left cell factors are exact rational numbers on the grid of width one over q. -/
theorem grid_mass {q i : ℝ} (hq : q ≠ 0) (hi : i ≠ 0) :
    2 * (1 / q) * kernel (i / q) = 2 * (i + q) / i ^ 2 := by
  unfold kernel
  field_simp

/-- Integer rounding down encloses a nonnegative rational cell mass. -/
theorem floor_cell (a d : ℕ) (hd : 0 < d) :
    ((a / d : ℕ) : ℚ) ≤ (a : ℚ) / d := by
  apply (le_div_iff₀ (by exact_mod_cast hd : (0 : ℚ) < d)).mpr
  exact_mod_cast Nat.div_mul_le_self a d

/-- Integer rounding up encloses a nonnegative rational cell mass. -/
theorem ceil_cell (a d : ℕ) (hd : 0 < d) :
    (a : ℚ) / d ≤ (((a + d - 1) / d : ℕ) : ℚ) := by
  apply (div_le_iff₀ (by exact_mod_cast hd : (0 : ℚ) < d)).mpr
  have hround : a ≤ (a + d - 1) / d * d := by
    simpa only [Nat.ceilDiv_eq_add_pred_div, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] using
      (le_smul_ceilDiv (b := a) hd)
  exact_mod_cast hround

/-- A positive cell with constant coefficient gives a nonempty instance of the rectangle theorem. -/
theorem rectangle_instance :
    (∫ z in (5 : ℝ)..6, kernel z) ≤ kernel 5 := by
  have hc : ContinuousOn kernel (Set.Icc 5 6) := by
    change ContinuousOn (fun x : ℝ => (x + 1) / x ^ 2) (Set.Icc 5 6)
    apply ContinuousOn.div (continuousOn_id.add continuousOn_const)
      (continuousOn_id.pow 2)
    intro x hx
    exact pow_ne_zero 2 (by change x ≠ 0; linarith [hx.1])
  have hi : IntervalIntegrable (fun z => (1 : ℝ) * kernel z) volume 5 6 := by
    have hc' : ContinuousOn kernel (Set.uIcc 5 6) := by
      simpa only [Set.uIcc_of_le (by norm_num : (5 : ℝ) ≤ 6)] using hc
    simpa using hc'.intervalIntegrable
  have h := (rectangle_bounds (L := 1) (U := 1) (f := fun _ => 1)
    (by norm_num : (0 : ℝ) < 5) (by norm_num) (by norm_num) hi
    (by intro z hz; exact ⟨le_rfl, le_rfl⟩)).2
  norm_num at h
  exact h

end LeanLab.AlmostPrimeSums.Kernel616
