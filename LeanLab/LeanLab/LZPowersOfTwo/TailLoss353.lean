/-
A bound-loss check for the elementary alternative to P0079 page 10, Section 5.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.CountBounds293

open Real Filter
open scoped Topology
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 10, Section 5, a lab check of the discarded pointwise method.
The naive scale X squared over log squared X is arbitrarily larger than the
required second-moment scale X over log X. This is not a paper error. -/
theorem naive_tail_loss353 :
    Tendsto (fun X : ℝ => (X ^ 2 / (log X) ^ 2) / (X / log X)) atTop atTop := by
  have hz : Tendsto (fun X : ℝ => log X / X) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hp : ∀ᶠ X : ℝ in atTop, log X / X ∈ Set.Ioi 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact div_pos (log_pos hX) (by linarith)
  have hgt : Tendsto (fun X : ℝ => log X / X) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz, hp⟩
  refine hgt.inv_tendsto_nhdsGT_zero.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hx : X ≠ 0 := by linarith
  have hl : log X ≠ 0 := (log_pos hX).ne'
  simp only [Pi.inv_apply]
  field_simp

end LeanLab.LZPowersOfTwo
