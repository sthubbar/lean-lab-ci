/-
U-1316, PC run 20261021T0103Z-19411: independent verify of R-5310.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.
Axiom audit of every R5310 theorem, plus independent instance checks.
-/
import LeanLab.Routes.R5310

namespace LeanLab.Routes.Verify1316

open LeanLab.Routes.R5310
open scoped ArithmeticFunction.Omega

/-- Instance of `pgf_twist` at z = -1 on ℤ: the twisted mass at -1 equals the twisted mass at 1. -/
example (S : Finset ℕ) (w : ℕ → ℤ) (k : ℕ → ℕ) :
    pgf S (fun s => w s * (1 + (-1) ^ k s)) k (-1) =
      pgf S (fun s => w s * (1 + (-1) ^ k s)) k 1 := by
  rw [pgf_twist, pgf_twist, neg_neg, add_comm]

/-- Concrete instance of `twist_coeff_odd` with a nonempty filter: k = id on {1,2,3}, j = 3. -/
example : ∑ s ∈ ({1, 2, 3} : Finset ℕ).filter (fun s => id s = 3),
    (1 : ℤ) * (1 + (-1) ^ id s) = 0 :=
  twist_coeff_odd _ _ _ 3 ⟨1, rfl⟩

/-- The untwisted odd coefficient is nonzero there, so the twist really changes it. -/
example : ∑ s ∈ ({1, 2, 3} : Finset ℕ).filter (fun s => id s = 3), (1 : ℤ) = 1 := by
  decide

/-- Independent recount at N = 32: Goldbach pairs p < 32 with 32 - p prime are 3,13,19,29. -/
example : ((Finset.range 32).filter (fun p => p.Prime ∧ Ω (32 - p) = 1)).card = 4 := by
  rw [goldbach_coeff]
  decide

/-- Edge case N = 0 and the convention N - p truncated: count is 0. -/
example : ((Finset.range 0).filter (fun p => p.Prime ∧ Ω (0 - p) = 1)).card = 0 := by
  simp

end LeanLab.Routes.Verify1316

#print axioms LeanLab.Routes.R5310.pgf_twist
#print axioms LeanLab.Routes.R5310.twist_coeff_odd
#print axioms LeanLab.Routes.R5310.twist_nonneg
#print axioms LeanLab.Routes.R5310.pgf_twist_sub_le
#print axioms LeanLab.Routes.R5310.goldbach_coeff
#print axioms LeanLab.Routes.R5310.goldbach_coeff_thirty
#print axioms LeanLab.Routes.R5310.pgf_twist_example
