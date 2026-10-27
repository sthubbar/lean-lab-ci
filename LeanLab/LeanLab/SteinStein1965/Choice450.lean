/-
AI wrote this Lean code for CODEX task70.
Stein and Stein 1965, Section 2, equation 2.3, page 427, and Table I, page 430.
The changed choice is a diagnostic and is not the paper's maximum rule.
-/
import LeanLab.SteinStein1965.Soundness

namespace LeanLab.SteinStein1965

def prefix89 : List ℕ :=
  [89, 97, 101, 103, 107, 109, 131, 113, 127, 139, 149, 163, 179,
   173, 181, 199, 211, 227, 229, 263, 293, 283, 281, 307, 317]

/-- The unchanged S-algorithm immediately before target 450. -/
theorem prefix89_448 : sPrime 89 448 = (prefix89, [180, 182, 184, 188]) := by
  decide +kernel

/-- The maximum rule chooses 353, while 223 is an admissible different choice. -/
theorem choice450 : covers prefix89 450 = false ∧
    (cands (primeA 89) prefix89 450).max? = some 353 ∧
    223 ∈ cands (primeA 89) prefix89 450 ∧
    prefix89.length = 25 ∧ 223 + 227 = 450 ∧ 227 ∈ prefix89 := by
  decide +kernel

/-- One diagnostic replacement at target 450. All other steps use the original rule. -/
def changedStep (st : List ℕ × List ℕ) (m : ℕ) : List ℕ × List ℕ :=
  if m = 450 then (st.1 ++ [223], st.2) else step (primeA 89) st m

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.prefix89_448
#print axioms LeanLab.SteinStein1965.choice450
