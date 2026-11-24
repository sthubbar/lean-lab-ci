/-
PROVED leaf `level_tendsto` of SPLIT_fixedKappa_of_allLevels. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BS2022GRH.SPLIT_fixedKappa_of_allLevels

namespace LeanLab.BS2022GRH.SieveAllLevels1611
open Real Finset Classical Filter Topology
open LeanLab.BS2022GRH LeanLab.BS2022GRH.ChenThresholdGRH

theorem level_tendsto_proof (z D εF : ℝ) (hD : 0 < D) :
    Tendsto (fun δ => log (D * (1 - δ)) / log z / (1 + εF)) (𝓝[>] 0)
      (𝓝 (log D / log z / (1 + εF))) := by
  have hc : ContinuousAt (fun δ : ℝ => log (D * (1 - δ)) / log z / (1 + εF)) 0 := by
    have h1 : ContinuousAt (fun δ : ℝ => D * (1 - δ)) 0 :=
      (continuous_const.mul (continuous_const.sub continuous_id)).continuousAt
    have h2 : D * (1 - 0) ≠ 0 := by simp [hD.ne']
    exact ((h1.log h2).div_const _).div_const _
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simpa using this

end LeanLab.BS2022GRH.SieveAllLevels1611

#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.level_tendsto_proof
