/-
Unit U-1514, T2 FRONTIER, idea I-0112, run PC 20261025T0803Z-22023. AI-written Lean code, Claude.
Checked only by the Lean kernel. KNOWN mathematics. Binary Goldbach is OPEN.

Exact type checks of `U1514.RS3` against the lab's three earlier forms of Ramaré-Saouter
Theorem 3, and Tao 2012 Theorem 8.1, Theorem 1.4 and the six primes bound with
Ramaré-Saouter's inputs `Theorem2At1e20` and `ChainCert` replaced by the U1514 inputs.
-/
import Mathlib
import LeanLab.Routes.U1514RS3
import LeanLab.Routes.U1505TaoRS
import LeanLab.RamareSaouter2003.Statements

namespace LeanLab.Routes.U1514
open LeanLab.KadiriLumley2014 LeanLab.GoldbachGaps.Sumset LeanLab.Tao2012
  LeanLab.SchnirelmannConstant

/-- Exact type check: `RS3` is definitionally the type of `RamareSaouter2003.theorem3`. -/
example : RS3 = type_of% @LeanLab.RamareSaouter2003.theorem3 := rfl

/-- Exact type check: `theorem3_of_chain` concludes `RS3`. -/
example (h2 : LeanLab.RamareSaouter2003.Smooth.Theorem2At1e20)
    (hc : LeanLab.RamareSaouter2003.Smooth.ChainCert 10726905041 ((10 : ℝ) ^ 20) 28314000) :
    RS3 :=
  LeanLab.RamareSaouter2003.Smooth.theorem3_of_chain h2 hc

/-- Exact type check: `RS3` is the hypothesis of `U1505.theorem8_1_of_rs3` and of
`RamareSaouter2003.rsShortIntervals_of`. -/
example (h : RS3) : Theorem8_1 ∧ RSShortIntervals :=
  ⟨LeanLab.Routes.U1505.theorem8_1_of_rs3 h, LeanLab.RamareSaouter2003.rsShortIntervals_of h⟩

/-- Tao's Theorem 8.1 CONDITIONAL ON `KLRow (4 · 10^18) 36082898`, `GapBound1476`,
`RecordGap456` and `BottomCheck`. -/
theorem theorem8_1_of_kl (hKL : KLRow (4 * 10 ^ 18) 36082898) (hG : GapBound1476)
    (h456 : RecordGap456) (hB : BottomCheck) : Theorem8_1 :=
  LeanLab.Routes.U1505.theorem8_1_of_rs3 (rs3_of_inputs hKL hG h456 hB)

/-- Tao's Theorem 1.4 CONDITIONAL ON `KLRow (4 · 10^18) 36082898`, `GapBound1476`,
`RecordGap456`, `BottomCheck`, and Tao's other cited inputs `EvenGoldbachUpTo N0`,
`Theorem8_2_printed`, `LiuWang`. -/
theorem theorem1_4_of_kl (hKL : KLRow (4 * 10 ^ 18) 36082898) (hG : GapBound1476)
    (h456 : RecordGap456) (hB : BottomCheck)
    (h16 : EvenGoldbachUpTo N0) (h82 : Theorem8_2_printed) (hLW : LiuWang) :
    ∀ x : ℕ, Odd x → 1 < x → AtMostPrimes 5 x :=
  theorem1_4_of_section8 (theorem8_1_of_kl hKL hG h456 hB) h16 h82 hLW

/-- The six primes bound with the same inputs. -/
theorem every_at_most_six_of_kl (hKL : KLRow (4 * 10 ^ 18) 36082898) (hG : GapBound1476)
    (h456 : RecordGap456) (hB : BottomCheck)
    (h16 : EvenGoldbachUpTo N0) (h82 : Theorem8_2_printed) (hLW : LiuWang) :
    ∀ n : ℕ, 1 < n → AtMostPrimes 6 n :=
  every_at_most_six_of_section8 (theorem8_1_of_kl hKL hG h456 hB) h16 h82 hLW

end LeanLab.Routes.U1514
