/- AI wrote the Lean code for CODEX task164.
Kernel certificate for the OPEN finite_sum_le leaf in DecompJ278.
Journal display 6 p. 1221. Goldbach is open. -/
import LeanLab.BS2022GRH.Cert1575Defs
namespace LeanLab.BS2022GRH.CertC164
open Cert1575Defs
set_option maxRecDepth 200000
set_option maxHeartbeats 0
/-- Reciprocal square upper sum over residues 1 and 5 modulo 6,
from 3001 to 100501, filtered by coprimality with 400 factorial.
This certifies a named finite epsilon leaf, not a number theory range extension. -/
theorem finite_window : outer (fac 400) (10 ^ 20) 3626548665143193 250 65 3001 0 = true := by
  decide +kernel
/-- Lower certificate on the same finite block, with rounding left explicit.
This reuses the upper checker sum and subtracts at most one per tested residue. -/
theorem lower_window : 7884029693000000 ≤ inner (fac 400) (10 ^ 20) 16416 1501 0 := by
  decide +kernel
end LeanLab.BS2022GRH.CertC164
#print axioms LeanLab.BS2022GRH.CertC164.finite_window
#print axioms LeanLab.BS2022GRH.CertC164.lower_window
