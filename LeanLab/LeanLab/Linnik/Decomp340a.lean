/-
Elementary endpoint integration for the detector counting interface.
The intended application is Gallagher 1970 p.336 before display 25.
The written argument was read from rendered source pages 333, 335 and 336.
Source https://doi.org/10.1007/BF01403187
AI wrote the Lean code. Codex task340. Goldbach is open.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

open MeasureTheory Finset
open scoped Classical

namespace LeanLab.Linnik.Decomp340a

/-- Endpoint functions on natural floors are integrable with logarithmic weight
on every compact interval with positive lower endpoint. -/
theorem integrableOn_floor_div (F : ℕ → ℝ) {x y : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => F ⌊t⌋₊ / t) (Set.Icc x y) := by
  have hm : Measurable (fun t : ℝ => F ⌊t⌋₊ / t) :=
    ((measurable_of_countable F).comp Nat.measurable_floor).div measurable_id
  apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top hm.aestronglyMeasurable
    ((∑ n ∈ range (⌊y⌋₊ + 1), ‖F n‖) / x)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have ht0 : 0 < t := hx.trans_le ht.1
  have hn : ⌊t⌋₊ ∈ range (⌊y⌋₊ + 1) :=
    mem_range.mpr (by have := Nat.floor_le_floor ht.2; omega)
  have hF : ‖F ⌊t⌋₊‖ ≤ ∑ n ∈ range (⌊y⌋₊ + 1), ‖F n‖ :=
    single_le_sum (fun n _ => norm_nonneg (F n)) hn
  rw [norm_div, Real.norm_of_nonneg ht0.le]
  exact (div_le_div_of_nonneg_left (norm_nonneg _) hx ht.1).trans
    (div_le_div_of_nonneg_right hF hx.le)

/-- Gallagher 1970 p.336 the uniform scalar normalization of the fixed character count.
A radius padded by one over two log T costs only an absolute exponential constant.
The supplied finite numerical inequality is rescaled without a logarithmic loss. -/
theorem detector_count_scale {n a c₀ C K B l d r E : ℝ}
    (hn : 0 ≤ n) (hc₀ : 0 < c₀) (hC : 0 ≤ C) (hK : 0 < K) (hl : 0 < l)
    (hr : r ≤ d + 1 / (2 * l))
    (hcount : n * (c₀ * Real.exp (-2 * C * K * r * l) * (K * l) ^ 2) ^ 2 ≤
      a * l * ((B - 1) * K * l) * E) :
    n ≤ (a * (B - 1) / (c₀ ^ 2 * K ^ 3) * Real.exp (2 * C * K)) *
      Real.exp (4 * C * K * d * l) * E / l ^ 2 := by
  have hrl : r * l ≤ d * l + 1 / 2 := by
    have hm := mul_le_mul_of_nonneg_right hr hl.le
    have he : (1 / (2 * l)) * l = 1 / 2 := by field_simp
    nlinarith
  have hex : Real.exp (-4 * C * K * d * l - 2 * C * K) ≤
      Real.exp (-4 * C * K * r * l) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hrl (show 0 ≤ 4 * C * K by positivity)
    nlinarith
  have hg : 1 ≤ Real.exp (-4 * C * K * r * l) *
      Real.exp (4 * C * K * d * l) * Real.exp (2 * C * K) := by
    calc
      1 = Real.exp (-4 * C * K * d * l - 2 * C * K) *
          Real.exp (4 * C * K * d * l) * Real.exp (2 * C * K) := by
        rw [← Real.exp_add, ← Real.exp_add]
        have he : (-4 * C * K * d * l - 2 * C * K) + 4 * C * K * d * l + 2 * C * K = 0 := by ring
        rw [he, Real.exp_zero]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hex (Real.exp_pos _).le) (Real.exp_pos _).le
  have hsq : (c₀ * Real.exp (-2 * C * K * r * l) * (K * l) ^ 2) ^ 2 =
      c₀ ^ 2 * Real.exp (-4 * C * K * r * l) * K ^ 4 * l ^ 4 := by
    have he : Real.exp (-2 * C * K * r * l) ^ 2 = Real.exp (-4 * C * K * r * l) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = c₀ ^ 2 * Real.exp (-2 * C * K * r * l) ^ 2 * K ^ 4 * l ^ 4 := by ring
      _ = _ := by rw [he]
  have hm := mul_le_mul_of_nonneg_right hcount
    (show 0 ≤ Real.exp (4 * C * K * d * l) * Real.exp (2 * C * K) by positivity)
  rw [hsq] at hm
  have hlo := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ n * c₀ ^ 2 * K ^ 4 * l ^ 4 by positivity)
  have hb : n * (c₀ ^ 2 * K ^ 4 * l ^ 4) ≤
      (a * l * ((B - 1) * K * l) * E) *
        (Real.exp (4 * C * K * d * l) * Real.exp (2 * C * K)) := by
    nlinarith [hm, hlo]
  apply (mul_le_mul_iff_right₀ (show 0 < c₀ ^ 2 * K ^ 4 * l ^ 4 by positivity)).mp
  convert hb using 1 <;> field_simp [hc₀.ne', hK.ne', hl.ne']

end LeanLab.Linnik.Decomp340a
