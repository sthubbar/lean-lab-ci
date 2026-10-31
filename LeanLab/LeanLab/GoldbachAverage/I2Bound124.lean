import LeanLab.GoldbachAverage.ShiftedMass124

/-!
The weighted I2 estimate on P0051 page 11 before the geometric tail conversion.
Every integral has a separate integrability argument.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.I2Bound124
open MeasureTheory Filter Set
open FloorVariance82 WeightedPrefixBound82 WeightedIncrement124 WeightedSquare124
  WeightedCauchy124 WeightedMass124 ShiftedMass124 Sliding124

/-- The positive half line weighted R square mass used on P0051 page 11. -/
def rMass (N : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0, psiFloorError x ^ 2 * Real.exp (-2 * x / N)

/-- The positive half line weighted R increment square mass used on P0051 page 11. -/
def deltaMass (N : ℕ) (h : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0, (psiFloorError (x + h) - psiFloorError x) ^ 2 * Real.exp (-2 * x / N)

/-- I2 from P0051 page 9 eq. 49, with the exact finite sum identified in WeightedIncrement124. -/
def I2 (N : ℕ) (h : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0, weightedIncrement N x h ^ 2

/-- The weighted R increment square is integrable on the positive half line.
Source: P0051 page 11 first and fourth displays. -/
theorem weighted_delta_integrable (N : ℕ) (hN : 1 ≤ N) {h : ℝ} (hh : 0 ≤ h) :
    IntegrableOn (fun x : ℝ =>
      (psiFloorError (x + h) - psiFloorError x) ^ 2 * Real.exp (-2 * x / N)) (Ioi 0) := by
  have hR := weighted_R_square_integrable N hN
  have hS := shifted_R_square_integrable N hN hh
  have hM : IntegrableOn (fun x : ℝ =>
      2 * (psiFloorError (x + h) ^ 2 * Real.exp (-2 * x / N)) +
      2 * (psiFloorError x ^ 2 * Real.exp (-2 * x / N))) (Ioi 0) :=
    (hS.const_mul 2).add (hR.const_mul 2)
  have hm : Measurable (fun x : ℝ =>
      (psiFloorError (x + h) - psiFloorError x) ^ 2 * Real.exp (-2 * x / N)) :=
    ((((measurable_psiFloorError.comp (measurable_id.add_const h)).sub
      measurable_psiFloorError).pow_const 2).mul (by fun_prop))
  refine hM.mono' hm.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hs : (psiFloorError (x + h) - psiFloorError x) ^ 2 ≤
      2 * psiFloorError (x + h) ^ 2 + 2 * psiFloorError x ^ 2 := by
    nlinarith [sq_nonneg (psiFloorError (x + h) + psiFloorError x)]
  have ht := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-2 * x / N)).le
  nlinarith

/-- LEAF. P0051 page 11 first display with Cauchy Schwarz inserted in the final term. -/
theorem increment_square_cs (N : ℕ) (hN : 1 ≤ N) {x h : ℝ}
    (hx : 0 ≤ x) (hh : 0 ≤ h) :
    weightedIncrement N x h ^ 2 ≤ 3 *
      ((psiFloorError (x + h) - psiFloorError x) ^ 2 * Real.exp (-2 * x / N) +
        (h / N) ^ 2 * psiFloorError (x + h) ^ 2 * Real.exp (-2 * x / N) +
        (1 / (N : ℝ)) ^ 2 * h *
          ∫ u in x..(x + h), psiFloorError u ^ 2 * Real.exp (-2 * u / N)) := by
  have hs := weighted_increment_square N hN hx hh
  have hc := mul_le_mul_of_nonneg_left (weighted_R_short_integral_sq N hN hx hh)
    (sq_nonneg (1 / (N : ℝ)))
  nlinarith

/-- LEAF. P0051 page 11, the complete weighted I2 bound before the dyadic tail conversion.
The explicit endpoint cost is three times the sum of exp two and one. -/
theorem I2_weighted_bound (N : ℕ) (hN : 1 ≤ N) {h : ℝ}
    (hh : 0 ≤ h) (hhN : h ≤ N) :
    IntegrableOn (fun x : ℝ => weightedIncrement N x h ^ 2) (Ioi 0) ∧
    I2 N h ≤ 3 * deltaMass N h +
      3 * (Real.exp 2 + 1) * (h / N) ^ 2 * rMass N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ → ℝ := fun u => psiFloorError u ^ 2 * Real.exp (-2 * u / N)
  let A : ℝ → ℝ := fun x =>
    (psiFloorError (x + h) - psiFloorError x) ^ 2 * Real.exp (-2 * x / N)
  let B : ℝ → ℝ := fun x => psiFloorError (x + h) ^ 2 * Real.exp (-2 * x / N)
  let C : ℝ → ℝ := fun x => ∫ u in x..(x + h), f u
  let d : ℝ := (h / N) ^ 2
  let e : ℝ := (1 / (N : ℝ)) ^ 2 * h
  have hf : Integrable f μ := weighted_R_square_integrable N hN
  have hA : Integrable A μ := weighted_delta_integrable N hN hh
  have hB : Integrable B μ := shifted_R_square_integrable N hN hh
  have hC : Integrable C μ := positive_sliding_integrable hf hh
  have hG : Integrable (fun x => 3 * (A x + d * B x + e * C x)) μ :=
    ((hA.add (hB.const_mul d)).add (hC.const_mul e)).const_mul 3
  have hpt : ∀ x : ℝ, 0 ≤ x → weightedIncrement N x h ^ 2 ≤
      3 * (A x + d * B x + e * C x) := by
    intro x hx
    simpa only [A, B, C, d, e, f, mul_assoc] using increment_square_cs N hN hx hh
  have hwm : Measurable (fun x : ℝ => weightedIncrement N x h) := by
    change Measurable (fun x : ℝ => WeightedPrefix82.weightedPrefix N (x + h) -
      WeightedPrefix82.weightedPrefix N x)
    exact ((measurable_weightedPrefix N).comp (measurable_id.add_const h)).sub
      (measurable_weightedPrefix N)
  have hW : Integrable (fun x => weightedIncrement N x h ^ 2) μ := by
    refine hG.mono' (hwm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt x hx.le
  refine ⟨hW, ?_⟩
  have hi := integral_mono_ae hW hG (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpt x hx.le)
  have hInt : (∫ x, 3 * (A x + d * B x + e * C x) ∂μ) =
      3 * ((∫ x, A x ∂μ) + d * (∫ x, B x ∂μ) + e * (∫ x, C x ∂μ)) := by
    rw [integral_const_mul,
      integral_add (f := fun x => A x + d * B x) (g := fun x => e * C x)
        (hA.add (hB.const_mul d)) (hC.const_mul e),
      integral_add (f := A) (g := fun x => d * B x) hA (hB.const_mul d),
      integral_const_mul, integral_const_mul]
  rw [hInt, show (∫ x, A x ∂μ) = deltaMass N h from rfl] at hi
  have hBbound : (∫ x, B x ∂μ) ≤ Real.exp 2 * rMass N :=
    shifted_R_mass_bound N hN hh hhN
  have hCbound : (∫ x, C x ∂μ) ≤ h * rMass N :=
    positive_sliding_integral_le hf (fun u _ => by dsimp [f]; positivity) hh
  have hd : 0 ≤ d := sq_nonneg _
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hBB := mul_le_mul_of_nonneg_left hBbound hd
  have hCC := mul_le_mul_of_nonneg_left hCbound he
  have heh : e * h = d := by
    dsimp [e, d]
    field_simp [hN0.ne'] <;> ring
  have heq : e * (h * rMass N) = d * rMass N := by rw [← mul_assoc, heh]
  rw [heq] at hCC
  have hsum : deltaMass N h + d * (∫ x, B x ∂μ) + e * (∫ x, C x ∂μ) ≤
      deltaMass N h + d * (Real.exp 2 * rMass N) + d * rMass N := by
    linarith only [hBB, hCC]
  change (∫ x, weightedIncrement N x h ^ 2 ∂μ) ≤
    3 * deltaMass N h + 3 * (Real.exp 2 + 1) * d * rMass N
  calc _ ≤ 3 * (deltaMass N h + d * (∫ x, B x ∂μ) + e * (∫ x, C x ∂μ)) := hi
    _ ≤ 3 * (deltaMass N h + d * (Real.exp 2 * rMass N) + d * rMass N) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

end LeanLab.GoldbachAverage.I2Bound124
