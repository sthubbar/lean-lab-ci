/-
Ported from Prove2Me, mission 0814790f.
Source LL_Decomp368b_primorial_c6. Author kmehltretter82. Apache 2.0.
Lean 4.33.1 source adapted for Lean 4.35.0.
Derived certificates for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib.NumberTheory.Primorial
import LeanLab.Ported.Prove2Me.PrimorialRange_bound_32000000_34129386
import LeanLab.Ported.Prove2Me.PrimorialRange_bound_34129386_42496200
import LeanLab.Ported.Prove2Me.PrimorialRange_bound_42496200_52597756
import LeanLab.Ported.Prove2Me.PrimorialRange_bound_52597756_60984648
import LeanLab.Ported.Prove2Me.PrimorialRange_bound_60984648_69355435
import LeanLab.Ported.Prove2Me.PrimorialRange_bound_69355435_77727216
import LeanLab.Ported.Prove2Me.PrimorialRange_bound_77727216_87458565
import LeanLab.Ported.Prove2Me.PrimorialRange_bound_87458565_100000000
namespace LeanLab.Ported.Prove2Me.Task666


theorem LL_Decomp368b.primorial_c6 (n : ℕ) (hn : 32000000 < n) (hn' : n ≤ 100000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  by_cases h0 : n ≤ 34129386
  · exact PrimorialRange.bound_32000000_34129386 n hn h0
  by_cases h1 : n ≤ 42496200
  · exact PrimorialRange.bound_34129386_42496200 n (by omega) h1
  by_cases h2 : n ≤ 52597756
  · exact PrimorialRange.bound_42496200_52597756 n (by omega) h2
  by_cases h3 : n ≤ 60984648
  · exact PrimorialRange.bound_52597756_60984648 n (by omega) h3
  by_cases h4 : n ≤ 69355435
  · exact PrimorialRange.bound_60984648_69355435 n (by omega) h4
  by_cases h5 : n ≤ 77727216
  · exact PrimorialRange.bound_69355435_77727216 n (by omega) h5
  by_cases h6 : n ≤ 87458565
  · exact PrimorialRange.bound_77727216_87458565 n (by omega) h6
  exact PrimorialRange.bound_87458565_100000000 n (by omega) hn'

end LeanLab.Ported.Prove2Me.Task666
