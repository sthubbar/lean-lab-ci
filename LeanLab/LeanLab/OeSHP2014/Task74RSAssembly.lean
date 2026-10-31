import LeanLab.OeSHP2014.U1454Reductions
import LeanLab.RamareSaouter2003.Triad19
import LeanLab.RamareSaouter2003.MuStar55Cert

/-! The next assembly step named in U1454, using existing row 60 on main.
Theorem 2.1 remains conditional on the even range and the RS analytic and chain inputs.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
namespace LeanLab.OeSHP2014.Task74

open LeanLab
open LeanLab.OeSHP2014.U1454
open LeanLab.RamareSaouter2003

/-- The paper's odd range from the underlying RS inputs, with the mu bound discharged. -/
theorem theorem2_1_of_rs_inputs {NT : ℝ → ℝ}
    (hE : EvenGoldbachUpTo N0)
    (h4 : Smooth.Theorem4Fm NT 3300000000)
    (hN : Row1.Lemma1Upper NT)
    (hc : Smooth.ChainCert 10726905041 ((10 : ℝ)^20) 28314000) :
    TernaryGoldbachUpTo (209267308 * N0 - 1) := by
  have hmu : Triad19.MuStar55Bounds := MuStar55Cert.muStar55Bounds
  exact theorem2_1_of hE
    (MuStar55Cert.theorem3_of_thm4 h4 hN hc)
    (MuStar55Cert.theorem2_row59_of_thm4 h4 hN)
    (Triad19.theorem2_row60_of h4 hN hmu)

end LeanLab.OeSHP2014.Task74
#print axioms LeanLab.OeSHP2014.Task74.theorem2_1_of_rs_inputs
