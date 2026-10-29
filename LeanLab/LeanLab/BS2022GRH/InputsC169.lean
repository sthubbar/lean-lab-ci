/- AI wrote this Lean code for CODEX task169.
Assembly of the decomposed journal inputs. Goldbach is open. -/
import LeanLab.BS2022GRH.DecompC169b
import LeanLab.BS2022GRH.DecompC169d
import LeanLab.BS2022GRH.DecompC164c
import LeanLab.BS2022GRH.Cert1575Closed

namespace LeanLab.BS2022GRH.InputsC169
open ChenThresholdGRH

/-- The exact three journal predicates assembled from named leaves.
This theorem is OPEN through the analytic leaves and the task164 normalization question. -/
theorem theorems567 : Thm5J ∧ Thm6J ∧ Thm7J :=
  ⟨DecompC169a.thm5J, DecompC169b.thm6J, DecompC164c.thm7J⟩

/-- The existing threshold assembled from the decomposed inputs and closed numeric certificates.
OPEN through the named analytic leaves. No claim of a proved Chen threshold is made. -/
theorem threshold : ChenThreshold13375 :=
  Cert1575.chenThreshold13375_of_deep_closed DecompC169a.thm5J DecompC169b.thm6J
    DecompC164c.thm7J DecompC169d.linearSieveT4_8349

end LeanLab.BS2022GRH.InputsC169

#print axioms LeanLab.BS2022GRH.InputsC169.theorems567
#print axioms LeanLab.BS2022GRH.InputsC169.threshold
