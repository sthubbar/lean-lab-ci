import LeanLab.ChirreHagen2025.Decomp358b
import LeanLab.ChirreHagen2025.BacklundIntegral272

/-!
P0075 page 3, the two tail displays after equation 2.1.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp358c
open MeasureTheory Set

/-- LEAF. P0075 page 3, first psi tail display, pointwise comparison only.
The source's Schoenfeld input is explicit. No integration or factor sigma plus it
occurs in this leaf. -/
theorem psi_kernel_norm_le (σ t y : ℝ) (hσ : 1 < σ) (hy : 74 ≤ y)
    (hpsi : |Chebyshev.psi y - y| ≤ Real.sqrt y * Real.log y ^ 2 / (8 * Real.pi)) :
    ‖((Chebyshev.psi y - y : ℝ) : ℂ) /
      (y : ℂ) ^ ((σ : ℂ) + t * Complex.I + 1)‖ ≤
      (Real.sqrt y * Real.log y ^ 2 / y ^ 2) / (8 * Real.pi) := by
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hy0]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
    Complex.one_re]
  have hpow : y ^ 2 ≤ y ^ (σ + 1) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hy1
    norm_num
    linarith
  calc
    _ ≤ (Real.sqrt y * Real.log y ^ 2 / (8 * Real.pi)) / y ^ (σ + 1) :=
      div_le_div_of_nonneg_right hpsi (by positivity)
    _ ≤ (Real.sqrt y * Real.log y ^ 2 / (8 * Real.pi)) / y ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
    _ = _ := by ring

/-- LEAF. P0075 page 3, passage between the two tail displays.
This bounds only the norm of sigma plus it. -/
theorem height_norm_le (σ t : ℝ) (hσ : 1 < σ) (hσtop : σ < 2)
    (ht : 100 ≤ |t|) : ‖(σ : ℂ) + t * Complex.I‖ ≤ 1.001 * |t| := by
  have hnorm : ‖(σ : ℂ) + t * Complex.I‖ ^ 2 = σ ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    <;> ring
  have ht2 : 10000 ≤ t ^ 2 := by nlinarith [sq_abs t]
  have hs2 : σ ^ 2 ≤ 4 := by nlinarith
  nlinarith [norm_nonneg ((σ : ℂ) + t * Complex.I), abs_nonneg t, sq_abs t]

/-- P0075 page 3, first tail display after evaluating the majorant integral.
CONDITIONAL ON the supplied pointwise psi estimate. -/
theorem psi_integral_bound (σ t : ℝ) (hσ : 1 < σ) (N : ℕ) (hN : 74 ≤ N)
    (hpsi : ∀ y : ℝ, (N : ℝ) < y →
      |Chebyshev.psi y - y| ≤ Real.sqrt y * Real.log y ^ 2 / (8 * Real.pi)) :
    IntegrableOn (fun y : ℝ => ((Chebyshev.psi y - y : ℝ) : ℂ) /
      (y : ℂ) ^ ((σ : ℂ) + t * Complex.I + 1)) (Set.Ioi (N : ℝ)) ∧
    ‖∫ y in Set.Ioi (N : ℝ), ((Chebyshev.psi y - y : ℝ) : ℂ) /
      (y : ℂ) ^ ((σ : ℂ) + t * Complex.I + 1)‖ ≤
      (Real.log (N : ℝ) ^ 2 + 4 * Real.log (N : ℝ) + 8) /
        (4 * Real.pi * Real.sqrt (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmaj := (BacklundIntegral272.majorant_integrable (N : ℝ) hN0).div_const (8 * Real.pi)
  have hpoint : ∀ᵐ y ∂volume.restrict (Ioi (N : ℝ)),
      ‖((Chebyshev.psi y - y : ℝ) : ℂ) /
        (y : ℂ) ^ ((σ : ℂ) + t * Complex.I + 1)‖ ≤
        (Real.sqrt y * Real.log y ^ 2 / y ^ 2) / (8 * Real.pi) :=
    (ae_restrict_mem measurableSet_Ioi).mono fun y hy =>
      psi_kernel_norm_le σ t y hσ
        (by
          have h : (74 : ℝ) ≤ N := by exact_mod_cast hN
          exact h.trans (show (N : ℝ) ≤ y from hy.le))
        (hpsi y hy)
  have hp : Measurable (fun y : ℝ => Chebyshev.psi y - y) :=
    Chebyshev.psi_mono.measurable.sub measurable_id
  have hc : Continuous (fun y : ℝ =>
      (y : ℂ) ^ ((σ : ℂ) + t * Complex.I + 1)) :=
    Complex.continuous_ofReal_cpow_const (by simp; linarith)
  have hm : Measurable (fun y : ℝ => ((Chebyshev.psi y - y : ℝ) : ℂ) /
      (y : ℂ) ^ ((σ : ℂ) + t * Complex.I + 1)) :=
    (Complex.continuous_ofReal.measurable.comp hp).div hc.measurable
  refine ⟨hmaj.mono' hm.aestronglyMeasurable hpoint, ?_⟩
  have hbound := norm_integral_le_of_norm_le hmaj hpoint
  apply hbound.trans_eq
  rw [integral_div, BacklundIntegral272.majorant_integral (N : ℝ) hN0]
  ring

/-- P0075 page 3. Exact target statement from Decomp272c.
CONDITIONAL ON Schoenfeld's psi estimate in Decomp358b. -/
theorem psi_tail_bound (hRH : RiemannHypothesis) (σ t : ℝ)
    (hσ : 1 < σ) (hσtop : σ < 2) (ht : 100 ≤ |t|) (N : ℕ) (hN : 74 ≤ N) :
    ‖((σ : ℂ) + t * Complex.I) *
      ∫ y in Set.Ioi (N : ℝ), ((Chebyshev.psi y - y : ℝ) : ℂ) /
        (y : ℂ) ^ ((σ : ℂ) + t * Complex.I + 1)‖ ≤
      1.001 * |t| * (Real.log (N : ℝ) ^ 2 + 4 * Real.log (N : ℝ) + 8) /
        (4 * Real.pi * Real.sqrt (N : ℝ)) := by
  have hb := psi_integral_bound σ t hσ N hN (fun y hy =>
    Decomp358b.schoenfeld_psi hRH y
      (by
        have h : (74 : ℝ) ≤ N := by exact_mod_cast hN
        linarith))
  rw [norm_mul]
  calc
    _ ≤ (1.001 * |t|) * ((Real.log (N : ℝ) ^ 2 + 4 * Real.log (N : ℝ) + 8) /
        (4 * Real.pi * Real.sqrt (N : ℝ))) :=
      mul_le_mul (height_norm_le σ t hσ hσtop ht) hb.2 (norm_nonneg _) (by positivity)
    _ = _ := by ring

end LeanLab.ChirreHagen2025.Decomp358c
