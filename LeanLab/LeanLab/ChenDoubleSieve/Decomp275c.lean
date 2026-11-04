import LeanLab.ChenDoubleSieve.Decomp275b

/-!
Assembly for Wu 2004 Theorem 2 from the five open leaves in Decomp275b.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ChenDoubleSieve.Task275

/-- Wu 2004 Theorem 2, with the exact statement of wu2004_thm2.
This assembly has no sorry of its own. Its five analytic leaves remain OPEN. -/
theorem wu2004_thm2_checked : ChenLower 0.836 :=
  thm2_analytic_link_checked thm2_eval_checked

end LeanLab.ChenDoubleSieve.Task275
