/-
Jia 1996 pages 281 and 282, exact two term polynomial integral certificate.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Short564
namespace LeanLab.Languasco2004.Polynomial564s
open Real intervalIntegral RemainderData564 Short564
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- LEAF. Jia pages 281 and 282, Lemma 27, supporting display 65 on page 286.
OPEN computational integral enclosure for printed term 13.
The two family subtotals retain their original required coefficients. -/
theorem short_integral_13 :
    let i : Fin 16 := ⟨11, by decide⟩
    let r := numericData i
    (rowTarget i : ℝ) ≤ ∫ t in (r 0 : ℝ)..(r 1),
      ∫ u in ((r 2 : ℝ)+r 3*t)..((r 4 : ℝ)+r 5*t), shortPolynomial i t u := by sorry
#print axioms short_integral_13
end
end LeanLab.Languasco2004.Polynomial564s
