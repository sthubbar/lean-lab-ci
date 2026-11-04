import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
AI wrote this Lean code for CODEX task296.
P0004 pages 22 to 25 equations 3.119, 3.141 and 3.142.
These are the cubic square mean transfer estimates.
Binary Goldbach is OPEN.
-/

open MeasureTheory

namespace LeanLab.HardyLittlewood1923.Decomp296Transfer

/-- P0004 page 22 equation 3.119, a symmetric bound for the cubic difference. -/
theorem cube_difference_le (z w : ℂ) :
    ‖z ^ 3 - w ^ 3‖ ≤ (3 / 2 : ℝ) * ‖z - w‖ * (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
  have he : z ^ 3 - w ^ 3 = (z - w) * (z ^ 2 + z * w + w ^ 2) := by ring
  have ht : ‖z ^ 2 + z * w + w ^ 2‖ ≤ ‖z‖ ^ 2 + ‖z‖ * ‖w‖ + ‖w‖ ^ 2 := by
    calc _ ≤ ‖z ^ 2 + z * w‖ + ‖w ^ 2‖ := norm_add_le _ _
      _ ≤ ‖z ^ 2‖ + ‖z * w‖ + ‖w ^ 2‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by rw [norm_pow, norm_mul, norm_pow]
  have hs : ‖z‖ ^ 2 + ‖z‖ * ‖w‖ + ‖w‖ ^ 2 ≤
      (3 / 2 : ℝ) * (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
    nlinarith only [sq_nonneg (‖z‖ - ‖w‖)]
  rw [he, norm_mul]
  calc _ ≤ ‖z - w‖ * ((3 / 2 : ℝ) * (‖z‖ ^ 2 + ‖w‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (ht.trans hs) (norm_nonneg _)
    _ = _ := by ring

#print axioms cube_difference_le

/-- P0004 pages 24 and 25 equations 3.141 and 3.142, the square mean transfer. -/
theorem cubic_integral_transfer {μ : Measure ℝ} {f g w : ℝ → ℂ} {E W : ℝ}
    (_hE : 0 ≤ E) (hW : 0 ≤ W)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hw : AEStronglyMeasurable w μ)
    (hf2 : Integrable (fun θ => ‖f θ‖ ^ 2) μ)
    (hg2 : Integrable (fun θ => ‖g θ‖ ^ 2) μ)
    (hfg : ∀ᵐ θ ∂μ, ‖f θ - g θ‖ ≤ E)
    (hwb : ∀ᵐ θ ∂μ, ‖w θ‖ ≤ W) :
    Integrable (fun θ => w θ * (f θ ^ 3 - g θ ^ 3)) μ ∧
    ‖∫ θ, w θ * (f θ ^ 3 - g θ ^ 3) ∂μ‖ ≤
      (3 / 2 : ℝ) * W * E * ((∫ θ, ‖f θ‖ ^ 2 ∂μ) + ∫ θ, ‖g θ‖ ^ 2 ∂μ) := by
  have hm : AEStronglyMeasurable (fun θ => w θ * (f θ ^ 3 - g θ ^ 3)) μ :=
    hw.mul ((hf.pow 3).sub (hg.pow 3))
  have hb : ∀ᵐ θ ∂μ, ‖w θ * (f θ ^ 3 - g θ ^ 3)‖ ≤
      (3 / 2 : ℝ) * W * E * (‖f θ‖ ^ 2 + ‖g θ‖ ^ 2) := by
    filter_upwards [hfg, hwb] with θ hθ hwθ
    rw [norm_mul]
    calc
      _ ≤ W * ((3 / 2 : ℝ) * E * (‖f θ‖ ^ 2 + ‖g θ‖ ^ 2)) := by
        apply mul_le_mul hwθ _ (norm_nonneg _) hW
        exact (cube_difference_le _ _).trans (by gcongr)
      _ = _ := by ring
  have hi := (hf2.add hg2).const_mul ((3 / 2 : ℝ) * W * E)
  have hkernel : Integrable (fun θ => w θ * (f θ ^ 3 - g θ ^ 3)) μ := hi.mono' hm hb
  refine ⟨hkernel, (norm_integral_le_integral_norm _).trans ?_⟩
  calc _ ≤ ∫ θ, (3 / 2 : ℝ) * W * E * (‖f θ‖ ^ 2 + ‖g θ‖ ^ 2) ∂μ :=
      integral_mono_ae hkernel.norm hi hb
    _ = _ := by rw [integral_const_mul, integral_add hf2 hg2]

#print axioms cubic_integral_transfer

/-- P0004 page 25 equation 3.142, the resulting power and logarithmic exponents. -/
theorem cubic_integral_rate {μ : Measure ℝ} {f g w : ℝ → ℂ}
    {n : ℕ} (hn : 4 ≤ n) {Θ C D W : ℝ} {A : ℕ}
    (hD : 0 ≤ D) (hW : 0 ≤ W)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hw : AEStronglyMeasurable w μ)
    (hf2 : Integrable (fun θ => ‖f θ‖ ^ 2) μ)
    (hg2 : Integrable (fun θ => ‖g θ‖ ^ 2) μ)
    (hfg : ∀ᵐ θ ∂μ, ‖f θ - g θ‖ ≤ D * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n ^ A)
    (hwb : ∀ᵐ θ ∂μ, ‖w θ‖ ≤ W)
    (hmean : (∫ θ, ‖f θ‖ ^ 2 ∂μ) + ∫ θ, ‖g θ‖ ^ 2 ∂μ ≤ C * n * Real.log n) :
    ‖∫ θ, w θ * (f θ ^ 3 - g θ ^ 3) ∂μ‖ ≤
      ((3 / 2 : ℝ) * W * D * C) * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ (A + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hE : 0 ≤ D * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n ^ A := by positivity
  have ht := (cubic_integral_transfer hE hW hf hg hw hf2 hg2 hfg hwb).2
  have hp : (n : ℝ) ^ (Θ + 1 / 4) * n = (n : ℝ) ^ (2 + (Θ - 3 / 4)) := by
    conv_lhs => arg 2; rw [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  calc _ ≤ (3 / 2 : ℝ) * W * (D * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n ^ A) *
        ((∫ θ, ‖f θ‖ ^ 2 ∂μ) + ∫ θ, ‖g θ‖ ^ 2 ∂μ) := ht
    _ ≤ (3 / 2 : ℝ) * W * (D * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n ^ A) *
        (C * n * Real.log n) := mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = ((3 / 2 : ℝ) * W * D * C) *
        ((n : ℝ) ^ (Θ + 1 / 4) * n) * (Real.log n ^ A * Real.log n) := by ring
    _ = _ := by rw [hp, ← pow_succ]

#print axioms cubic_integral_rate

end LeanLab.HardyLittlewood1923.Decomp296Transfer
