/-
PROVED leaf `upper_limit` of SPLIT_fixedKappa_of_allLevels. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BS2022GRH.SPLIT_fixedKappa_of_allLevels

namespace LeanLab.BS2022GRH.SieveAllLevels1611
open Real Finset Classical Filter Topology
open LeanLab.BS2022GRH LeanLab.BS2022GRH.ChenThresholdGRH

/-- `hS` is continuous: the pieces agree at 2 and 3. -/
theorem hS_continuous_upper : Continuous hS := by
  have e : hS = fun s => if s ≤ 2 then exp (-2) else
      if s ≤ 3 then exp (-s) else 3 / max s 1 * exp (-s) := by
    funext s; unfold hS
    split_ifs with h1 h2 <;> try rfl
    rw [max_eq_left (by linarith)]
  rw [e]
  refine Continuous.if_le continuous_const ?_ continuous_id continuous_const ?_
  · refine Continuous.if_le (continuous_exp.comp continuous_neg) ?_ continuous_id
      continuous_const ?_
    · exact (continuous_const.div (continuous_id.max continuous_const)
        (fun x => by positivity)).mul (continuous_exp.comp continuous_neg)
    · intro x hx; obtain rfl : x = _ := hx; norm_num
  · intro x hx; obtain rfl : x = _ := hx; norm_num

theorem upper_limit_proof (S X R c s₀ : ℝ) (hs₀ : 0 < s₀) (f : ℝ → ℝ)
    (hf : Tendsto f (𝓝[>] 0) (𝓝 s₀))
    (hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      S ≤ (2 * exp eulerMascheroniConstant / f δ + c * hS (f δ)) * X + R) :
    S ≤ (2 * exp eulerMascheroniConstant / s₀ + c * hS s₀) * X + R := by
  have hG : ContinuousAt (fun s => (2 * exp eulerMascheroniConstant / s + c * hS s) * X + R) s₀ :=
    by
    have := hS_continuous_upper.continuousAt (x := s₀)
    exact (((continuousAt_const.div continuousAt_id hs₀.ne').add
      (continuousAt_const.mul this)).mul continuousAt_const).add continuousAt_const
  exact ge_of_tendsto (hG.tendsto.comp hf) hev

end LeanLab.BS2022GRH.SieveAllLevels1611

#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.upper_limit_proof
