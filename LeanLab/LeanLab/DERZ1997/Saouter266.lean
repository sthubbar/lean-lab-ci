import LeanLab.DERZ1997.Statements
import LeanLab.Saouter1998.ProthLadder1597

/-!
P0011 page 100, the finite and asymptotic ranges of the main theorem.
This uses the existing certified prime ladder in place of the intermediate prime-gap lemma.
CONDITIONAL ON Zinoviev's asymptotic input and binary Goldbach up to 4 times 10 to the 18.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.DERZ1997

/-- The P0011 assembly from Zinoviev and the even verification through the existing prime ladder.
P0011 page 100 and Saouter 1998 page 863. -/
theorem derz_main_of_even_ladder266
    (hZ : GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → IsTernarySum n)
    (hD : EvenGoldbachUpTo (4 * 10 ^ 18)) : GRH → TernaryGoldbach :=
  derz_main_of_saouter hZ
    (LeanLab.Saouter1998.ProthLadder1597.ternaryGoldbachUpTo_1e20_of_even hD)

/-- Concrete instance of the reused ladder method, at a kernel-checked even range. -/
example : TernaryGoldbachUpTo 293 :=
  LeanLab.Saouter1998.ProthLadder1597.ternaryGoldbachUpTo_293_vacuity

end LeanLab.DERZ1997
