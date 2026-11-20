import LeanLab.ChenDoubleSieve.Decomp587f

/-!
Compact phi reduction for Wu 2004 Lemma 5.2 page 26, D2,13.
Source: https://arxiv.org/abs/0705.1652, Table 1 row four page 30.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,13 at Table 1 row four page 30.
Certify the Buchstab integral only for phi between two and sixteen fifths.
The three separated coordinate intervals are 25/103 through 25/89,
25/89 through 100/291 and 100/291 through 2/5. Use a profile polynomial and exact separated moments.
The unbounded phi tail uses r3Thirteen_integral_early_tail. -/
theorem r3Thirteen_compact {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (16 / 5 : ℝ)) :
    buchstabIntegral ω 1 r3ThirteenLo r3ThirteenHi φ ≤ (8106273 / 1000000000 : ℝ) := by
  by_cases hs : φ ≤ (13 / 5 : ℝ)
  · exact r3Thirteen_short hω hz hφ hs
  · exact r3Thirteen_integral_early_tail hω (le_of_not_ge hs)

/-- The exact original I2_r3_13 statement follows from the compact leaf and proved tail.
Wu 2004 page 26, Table 1 row four page 30. CONDITIONAL ON r3Thirteen_compact. -/
theorem I2_r3_13_from_compact {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 4 ≤ (8106273/1000000000 : ℝ) := by
  have hb : buchstabSup ω 1 r3ThirteenLo r3ThirteenHi ≤ (8106273 / 1000000000 : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 r3ThirteenLo r3ThirteenHi 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (16 / 5 : ℝ)
      · exact r3Thirteen_compact hω hz hφ ht
      · exact r3Thirteen_integral_early_tail hω
          ((by norm_num : (13 / 5 : ℝ) ≤ 16 / 5).trans (le_of_not_ge ht))
  convert hb using 1 <;> norm_num [I2, tableParams, r3ThirteenLo, r3ThirteenHi]

end LeanLab.ChenDoubleSieve.Task587
