import LeanLab.ChenDoubleSieve.Decomp587f
import LeanLab.ChenDoubleSieve.Task587Row3FourteenSupply

/-!
Compact phi reduction for Wu 2004 Lemma 5.2 page 26, D2,14.
Source: https://arxiv.org/abs/0705.1652, Table 1 row four page 30.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,14 at Table 1 row four page 30.
Certify the Buchstab integral only for phi between two and fourteen fifths.
The first interval runs from 25/103 through 25/89. The ordered final pair runs
from 100/291 through 2/5. Use a profile polynomial and exact separated moments.
The unbounded phi tail is supplied by Task587Row3FourteenSupply. -/
theorem r3Fourteen_compact {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (14 / 5 : ℝ)) :
    buchstabIntegral ω 1 r3FourteenLo r3FourteenHi φ ≤ ((2640381 / 1000000000) : ℝ) := by
  by_cases hs : φ ≤ (13 / 5 : ℝ)
  · exact r3Fourteen_short hω hz hφ hs
  · exact r3Fourteen_integral_early_tail hω (le_of_not_ge hs)

/-- The exact original I2_r3_14 statement follows from the compact leaf and proved tail.
Wu 2004 page 26, Table 1 row four page 30. CONDITIONAL ON r3Fourteen_compact. -/
theorem I2_r3_14_from_compact {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 5 ≤ ((2640381 / 1000000000) : ℝ) := by
  have hb : buchstabSup ω 1 r3FourteenLo r3FourteenHi ≤ ((2640381 / 1000000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 r3FourteenLo r3FourteenHi 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (14 / 5 : ℝ)
      · exact r3Fourteen_compact hω hz hφ ht
      · exact r3Fourteen_integral_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r3FourteenLo, r3FourteenHi]

end LeanLab.ChenDoubleSieve.Task587
