import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.JCertificate

/-!
Two certified scalar coefficients in Wu 2004 Theorem 2.
Source: https://arxiv.org/pdf/0705.1652, pages 40 to 42, equations 10.10 and 10.11.
AI wrote the Lean code. Binary Goldbach is open.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Real Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task275.Thm2Scalar
open Wu04JCertificate (up upperPanelQ le_up)
open Wu04Panels (JUpper)

/-- A rational uniform partition from two to b with m panels. -/
def nodeQ (b : ℚ) (m j : ℕ) : ℚ := 2 + j * (b - 2) / m

/-- The existing proved rational upper panel rounded upward to fifteen decimals. -/
def upperCell (b : ℚ) (m j : ℕ) : ℚ :=
  up (upperPanelQ (nodeQ b m j) (nodeQ b m (j + 1)))

/-- Every such upper panel sum bounds the actual logarithmic integral. -/
theorem J_upper_partition (b : ℚ) (m : ℕ) (hb : 2 ≤ b) (hm : 0 < m) :
    (∫ t in (2 : ℝ)..(b : ℝ), log (t - 1) / t) ≤
      ((∑ j ∈ range m, upperCell b m j : ℚ) : ℝ) := by
  let x : ℕ → ℝ := fun j => (nodeQ b m j : ℝ)
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hx (j : ℕ) : x j = 2 + (j : ℝ) * ((b : ℝ) - 2) / m := by simp [x, nodeQ]
  have hxp (j : ℕ) : 2 ≤ x j ∧ x j ≤ x (j + 1) := by
    rw [hx j, hx (j + 1)]
    push_cast
    have hnon : 0 ≤ (j : ℝ) * ((b : ℝ) - 2) / m :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg j) (by linarith)) hmR.le
    have hstep : 0 ≤ ((b : ℝ) - 2) / m := div_nonneg (by linarith) hmR.le
    have heq : ((j : ℝ) + 1) * ((b : ℝ) - 2) / m -
        (j : ℝ) * ((b : ℝ) - 2) / m = ((b : ℝ) - 2) / m := by ring
    constructor <;> linarith
  have hp := (Wu04Panels.J_partition_arithmetic 16 m x (fun j _ => hxp j)).2
  have hcell (j : ℕ) : JUpper 16 (x j) (x (j + 1)) ≤ (upperCell b m j : ℝ) := by
    have h : (upperPanelQ (nodeQ b m j) (nodeQ b m (j + 1)) : ℝ) ≤
        (up (upperPanelQ (nodeQ b m j) (nodeQ b m (j + 1))) : ℝ) := by
      exact_mod_cast le_up (upperPanelQ (nodeQ b m j) (nodeQ b m (j + 1)))
    simpa [upperCell, upperPanelQ, JUpper, x] using h
  have hx0 : x 0 = 2 := by simp [x, nodeQ]
  have hxm : x m = (b : ℝ) := by
    rw [hx]
    field_simp [hmR.ne']
    ring
  rw [hx0, hxm] at hp
  exact hp.trans (by simpa only [Rat.cast_sum] using
    (sum_le_sum (fun j (_ : j ∈ range m) => hcell j)))

/-- A kernel checked rational certificate for the printed F7 upper bound. -/
theorem F7_certificate :
    8 * (∑ j ∈ range 32, upperCell (84 / 41) 32 j : ℚ) ≤ 4609 / 1000000 := by
  decide +kernel

/-- A kernel checked rational certificate for the printed F8 upper bound. -/
theorem F8_certificate :
    8 * (∑ j ∈ range 512, upperCell (359 / 141) 512 j : ℚ) ≤ 434368 / 1000000 := by
  decide +kernel

/-- The actual F7 integral satisfies the printed upper estimate, with no analytic input. -/
theorem F7_upper (F f ω : ℝ → ℝ) : integralTerms F f ω 6 ≤ 0.004609 := by
  change 8 * (∫ t in (2 : ℝ)..(1 / sigma1 - 1), log (t - 1) / t) ≤ 0.004609
  have he : (1 / sigma1 - 1 : ℝ) = ((84 / 41 : ℚ) : ℝ) := by norm_num [sigma1]
  rw [he]
  have hp := J_upper_partition (84 / 41) 32 (by norm_num) (by decide)
  have hc : 8 * ((∑ j ∈ range 32, upperCell (84 / 41) 32 j : ℚ) : ℝ) ≤ 0.004609 := by
    have hq : ((8 * (∑ j ∈ range 32, upperCell (84 / 41) 32 j) : ℚ) : ℝ) ≤
        ((4609 / 1000000 : ℚ) : ℝ) := Rat.cast_le.mpr F7_certificate
    convert hq using 1 <;> push_cast <;> norm_num
  exact (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 8)).trans hc

/-- The actual F8 integral satisfies the printed upper estimate, with no analytic input. -/
theorem F8_upper (F f ω : ℝ → ℝ) : integralTerms F f ω 7 ≤ 0.434368 := by
  change 8 * (∫ t in (2 : ℝ)..(1 / sigma2 - 1), log (t - 1) / t) ≤ 0.434368
  have he : (1 / sigma2 - 1 : ℝ) = ((359 / 141 : ℚ) : ℝ) := by norm_num [sigma2]
  rw [he]
  have hp := J_upper_partition (359 / 141) 512 (by norm_num) (by decide)
  have hc : 8 * ((∑ j ∈ range 512, upperCell (359 / 141) 512 j : ℚ) : ℝ) ≤ 0.434368 := by
    have hq : ((8 * (∑ j ∈ range 512, upperCell (359 / 141) 512 j) : ℚ) : ℝ) ≤
        ((434368 / 1000000 : ℚ) : ℝ) := Rat.cast_le.mpr F8_certificate
    convert hq using 1 <;> push_cast <;> norm_num
  exact (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 8)).trans hc

end LeanLab.ChenDoubleSieve.Task275.Thm2Scalar
