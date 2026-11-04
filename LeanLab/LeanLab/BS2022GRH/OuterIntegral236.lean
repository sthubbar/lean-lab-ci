/- AI wrote the Lean code for CODEX task236.
The integral coefficient in journal Lemma 14 p. 1239. Goldbach is open. -/
import LeanLab.BS2022GRH.SlicePartial236
namespace LeanLab.BS2022GRH.SliceMass236
open Real Finset Classical MeasureTheory intervalIntegral
noncomputable section

/-- Substitution u equals N to beta gives the exact printed integral coefficient,
journal p. 1239. The value of cbar is the existing lab integral. -/
theorem outer_integral_eq_cbar (N : ℝ) (hN : 1 < N) :
    (∫ u in N ^ (1 / 8 : ℝ)..N ^ (1 / 3 : ℝ), H N u / (u * log u)) =
      LeanLab.ChenExplicit.BJS.cbar / log N := by
  have hN0 : 0 < N := by linarith
  have hL : 0 < log N := log_pos hN
  let f : ℝ → ℝ := fun β => N ^ β
  let f' : ℝ → ℝ := fun β => N ^ β * log N
  have hd : ∀ β ∈ Set.uIcc (1 / 8 : ℝ) (1 / 3), HasDerivAt f (f' β) β := by
    intro β _
    convert (((hasDerivAt_id β).const_mul (log N)).exp) using 1
    · ext t
      dsimp [f]
      rw [rpow_def_of_pos hN0]
    · dsimp [f']
      rw [rpow_def_of_pos hN0]
      simp
  have hcd : ContinuousOn f' (Set.uIcc (1 / 8 : ℝ) (1 / 3)) := by
    dsimp [f']
    fun_prop
  have hcg : ContinuousOn (fun u : ℝ => H N u / (u * log u))
      (f '' Set.uIcc (1 / 8 : ℝ) (1 / 3)) := by
    apply continuousOn_of_forall_continuousAt
    intro u hu
    obtain ⟨β, hβ, rfl⟩ := hu
    rw [Set.uIcc_of_le (by norm_num : (1 / 8 : ℝ) ≤ 1 / 3)] at hβ
    have hβ0 : 0 < β := by linarith [hβ.1]
    have hu0 : 0 < f β := rpow_pos_of_pos hN0 _
    have hlu : 0 < log (f β) := by
      dsimp [f]
      rw [log_rpow hN0]
      exact mul_pos hβ0 hL
    have hgap : 0 < log N - log (f β) - log (N ^ (1 / 3 : ℝ)) := by
      dsimp [f]
      rw [log_rpow hN0, log_rpow hN0]
      nlinarith [hβ.2]
    exact (H_hasDeriv N (f β) hN hu0 hgap).continuousAt.div
      (continuousAt_id.mul (continuousAt_log hu0.ne')) (mul_ne_zero hu0.ne' hlu.ne')
  have hsub := integral_comp_mul_deriv' hd hcd hcg
  change (∫ β in (1 / 8 : ℝ)..(1 / 3),
      H N (N ^ β) / (N ^ β * log (N ^ β)) * (N ^ β * log N)) =
    (∫ u in N ^ (1 / 8 : ℝ)..N ^ (1 / 3 : ℝ), H N u / (u * log u)) at hsub
  rw [← hsub]
  calc
    _ = ∫ β in (1 / 8 : ℝ)..(1 / 3),
        (log (2 - 3 * β) / (β * (1 - β))) / log N := by
      apply integral_congr
      intro β hβ
      rw [Set.uIcc_of_le (by norm_num : (1 / 8 : ℝ) ≤ 1 / 3)] at hβ
      have hβ0 : β ≠ 0 := by linarith [hβ.1]
      have hβ1 : 1 - β ≠ 0 := by linarith [hβ.2]
      have hp : N ^ β ≠ 0 := (rpow_pos_of_pos hN0 _).ne'
      dsimp only
      rw [H_rpow N β hN (by linarith [hβ.2]), log_rpow hN0]
      field_simp
      <;> ring
    _ = _ := by rw [intervalIntegral.integral_div]; rfl

end
end LeanLab.BS2022GRH.SliceMass236
#print axioms LeanLab.BS2022GRH.SliceMass236.outer_integral_eq_cbar
