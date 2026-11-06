/-
P0059 page 5 Section 2.5 and page 7 Lemma 2.5.
Source 4, arXiv 1310.6374 page 8 Corollary 2.6.
The same continuous Rosser envelope controls the inclusive endpoint count.
AI wrote this Lean code. CODEX task399. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.CountParts399

namespace LeanLab.KadiriLumley2014.Task399

open Real Set MeasureTheory Filter Topology
open Task259

/-- The auxiliary count through T includes an ordinate equal to T. -/
noncomputable def inclusiveCount (T : ℝ) : ℝ :=
  positiveZeroSum (fun ρ => if ρ.im ≤ T then 1 else 0)

/-- The inclusive count family has finite support and is summable. -/
theorem inclusiveCount_summable (T : ℝ) :
    Summable (fun ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} =>
      if 0 < (ρ : ℂ).im then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (if (ρ : ℂ).im ≤ T then 1 else 0) else 0) := by
  refine summable_bounded_positive_zero_family T (fun ρ => if ρ.im ≤ T then 1 else 0) ?_
  intro ρ hρ
  exact ite_eq_right (not_le_of_gt hρ)

/-- The strict count is at most the inclusive count at the same cutoff. -/
theorem zeroCount_le_inclusive (T : ℝ) : zeroCount T ≤ inclusiveCount T := by
  unfold zeroCount inclusiveCount positiveZeroSum
  apply Summable.tsum_le_tsum _ (zeroCount_summable T) (inclusiveCount_summable T)
  intro ρ
  by_cases hp : 0 < (ρ : ℂ).im
  · simp only [ite_eq_left hp]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    split_ifs with hlt hle
    · rfl
    · exact absurd hlt.le hle
    · norm_num
    · rfl
  · simp [hp]

/-- The inclusive count at T is at most the strict count at every larger cutoff. -/
theorem inclusiveCount_le_zeroCount {T U : ℝ} (hTU : T < U) :
    inclusiveCount T ≤ zeroCount U := by
  unfold zeroCount inclusiveCount positiveZeroSum
  apply Summable.tsum_le_tsum _ (inclusiveCount_summable T) (zeroCount_summable U)
  intro ρ
  by_cases hp : 0 < (ρ : ℂ).im
  · simp only [ite_eq_left hp]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    split_ifs with hle hlt
    · rfl
    · exact absurd (hle.trans_lt hTU) hlt
    · norm_num
    · rfl
  · simp [hp]

/-- The Rosser error also bounds the inclusive count, by taking the continuous upper envelope from the right.
CONDITIONAL ON the existing Rosser count input. -/
theorem inclusive_rosser_bound (hCount : RosserCountBound) {T : ℝ} (hT : 2 ≤ T) :
    |inclusiveCount T - countMain T| ≤ countRemainder T := by
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hcont : ContinuousAt (fun U => countMain U + countRemainder U) T := by
    unfold countMain countRemainder
    fun_prop (disch := positivity)
  have hlim : Tendsto (fun U => countMain U + countRemainder U) (nhdsWithin T (Ioi T))
      (nhds (countMain T + countRemainder T)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hupper : inclusiveCount T ≤ countMain T + countRemainder T := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with U hTU
    have hle := inclusiveCount_le_zeroCount hTU
    have herror := (abs_le.mp (hCount U (hT.trans hTU.le))).2
    linarith
  have hlower := (abs_le.mp (hCount T hT)).1
  have hmono := zeroCount_le_inclusive T
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end LeanLab.KadiriLumley2014.Task399
