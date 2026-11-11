import LeanLab.ChirreHagen2025.Decomp391a
import LeanLab.PNTPort.ExplicitPsi1.ZeroSum

/-!
Absolute convergence of the zero series in CHS page 4 equation 3.3.
Reuse the unconditional PNTPort zero-count summability theorem.
https://arxiv.org/abs/2206.00819
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.ZeroConvergence391d
open ArithmeticFunction MeasureTheory Set Filter

/-- CHS page 4 equation 3.3, comparison of shifted zero denominators outside a disk. -/
theorem shifted_denominator_comparison (z : ℂ) (hz : 2 ≤ ‖z‖) :
    ‖z + 1‖ ≤ 3 * ‖z - 1‖ := by
  have hm := norm_sub_norm_le z (1 : ℂ)
  simp only [norm_one] at hm
  have hh := norm_add_le (z - 1) (2 : ℂ)
  rw [show z - 1 + 2 = z + 1 by ring] at hh
  norm_num at hh
  linarith

/-- CHS page 4 equation 3.3, domination by the existing convergent zero-count weight. -/
theorem zero_term_norm_le (x : ℝ) (hx : 1 ≤ x)
    (ρ : ℂ) (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) (hρ : 2 ≤ ‖ρ‖) (m : ℕ) :
    ‖(m : ℂ) * (x : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))‖ ≤
      3 * ((m : ℝ) / ‖ρ * (ρ + 1)‖) := by
  have hx0 : 0 < x := by linarith
  have hz0 : (ρ : ℂ) ≠ 0 := by intro h; have := hre0; simp [h] at this
  have hzm : (ρ : ℂ) - 1 ≠ 0 := by
    intro h
    have hh : (ρ : ℂ) = 1 := sub_eq_zero.mp h
    have := hre1
    simp [hh] at this
  have hzp : (ρ : ℂ) + 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    have := hre0
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
    linarith
  have hdm : 0 < ‖(ρ : ℂ) * ((ρ : ℂ) - 1)‖ := norm_pos_iff.mpr (mul_ne_zero hz0 hzm)
  have hdp : 0 < ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ := norm_pos_iff.mpr (mul_ne_zero hz0 hzp)
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hx (sub_nonpos.mpr hre1.le)
  have hc := shifted_denominator_comparison ρ hρ
  rw [norm_div, norm_mul, Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp only [Complex.sub_re, Complex.one_re]
  calc
    _ ≤ (m : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) - 1)‖ := by
      apply div_le_div_of_nonneg_right _ hdm.le
      simpa using mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg m)
    _ ≤ _ := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hdm hdp).mpr
      calc
        _ = ((m : ℝ) * ‖(ρ : ℂ)‖) * ‖(ρ : ℂ) + 1‖ := by
          rw [norm_mul]; ring
        _ ≤ ((m : ℝ) * ‖(ρ : ℂ)‖) * (3 * ‖(ρ : ℂ) - 1‖) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
        _ = _ := by rw [norm_mul]; ring

/-- CHS page 4 equation 3.3, absolute convergence of its zero expansion.
This discharges the convergence component of Decomp391a.weighted_explicit_formula.
The identity and the quantitative zero estimate remain separate analytic inputs. -/
theorem zero_series_summable (x : ℝ) (hx : 1 ≤ x) :
    Summable (Decomp391a.zeroTerm x) := by
  let i : {s : ℂ // riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1} →
      LeanLab.PNTPort.ExplicitPsi1.Zall :=
    fun ρ => ⟨ρ, ρ.2.1, by linarith [ρ.2.2.1]⟩
  have hi : Function.Injective i := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : LeanLab.PNTPort.ExplicitPsi1.Zall => (z : ℂ)) h
  have hw : Summable (fun ρ : {s : ℂ // riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1} =>
      (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) := by
    simpa [i, Function.comp_def, LeanLab.PNTPort.ExplicitPsi1.hw] using
      (LeanLab.PNTPort.ExplicitPsi1.summable_hw.comp_injective hi)
  have hc := (isCompact_closedBall (0 : ℂ) 2).inter_riemannZetaZeros_finite
  have hpre : ((fun ρ : {s : ℂ // riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1} => (ρ : ℂ)) ⁻¹'
      (Metric.closedBall (0 : ℂ) 2 ∩ riemannZetaZeros)).Finite :=
    hc.preimage (fun a _ b _ h => Subtype.ext h)
  have hf : {ρ : {s : ℂ // riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1} | ¬ 2 ≤ ‖(ρ : ℂ)‖}.Finite := by
    apply hpre.subset
    intro ρ hρ
    refine ⟨?_, ρ.2.1⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using (lt_of_not_ge hρ).le
  apply (hw.mul_left 3).of_norm_bounded_eventually
  filter_upwards [eventually_cofinite.mpr hf] with ρ hρ
  simpa only [Decomp391a.zeroTerm] using
    zero_term_norm_le x hx ρ ρ.2.2.1 ρ.2.2.2 hρ (analyticOrderNatAt riemannZeta ρ)

end LeanLab.ChirreHagen2025.ZeroConvergence391d
