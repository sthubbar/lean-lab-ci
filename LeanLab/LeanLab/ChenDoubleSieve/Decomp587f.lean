import LeanLab.Ported.Prove2Me.Decomp587fR3FourteenShort
import LeanLab.Ported.Prove2Me.Decomp587fR3ThirteenShort
import LeanLab.Ported.Prove2Me.Decomp587fR3ElevenShort
import LeanLab.Ported.Prove2Me.Decomp587fR3TenShort
import LeanLab.Ported.Prove2Me.Decomp587fR3NineShort
import LeanLab.ChenDoubleSieve.Task587EarlySupply

/-!
Five compact profile leaves for Wu 2004 Lemma 5.2 page 26.
Source: https://arxiv.org/abs/0705.1652, Table 1 row four page 30.
Every remaining phi interval is two through thirteen fifths.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,9, Table 1 row four page 30.
Only phi from two through thirteen fifths remains. The unbounded tail is proved
by r3Nine_integral_early_tail. Certify the Buchstab profile on this compact
interval and combine it with the exact reciprocal polynomial moments.
This statement has no supremum and is strictly smaller than the original leaf. -/
theorem r3Nine_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (13 / 5 : ℝ)) :
    buchstabIntegral ω 1 (fun _ => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ)) φ ≤ (12408337 / 1000000000 : ℝ) := by
  exact LeanLab.Ported.Prove2Me.Decomp587fR3NineShort.solution hω hz hφ hφtop

/-- The exact original I2_r3_9 bound follows from its compact profile leaf and proved tail.
Wu 2004 page 26, Table 1 row four page 30. CONDITIONAL ON r3Nine_short. -/
theorem I2_r3_9_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 0 ≤ (12408337 / 1000000000 : ℝ) := by
  have hb : buchstabSup ω 1 (fun _ => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ)) ≤ (12408337 / 1000000000 : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun _ => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (13 / 5 : ℝ)
      · exact r3Nine_short hω hz hφ ht
      · exact r3Nine_integral_early_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams]

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,10, Table 1 row four page 30.
Only phi from two through thirteen fifths remains. The unbounded tail is proved
by r3Ten_integral_early_tail. Certify the Buchstab profile on this compact
interval and combine it with the exact reciprocal polynomial moments.
This statement has no supremum and is strictly smaller than the original leaf. -/
theorem r3Ten_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (13 / 5 : ℝ)) :
    buchstabIntegral ω 1 r3TenLo r3TenHi φ ≤ (2710363 / 500000000 : ℝ) := by
  exact LeanLab.Ported.Prove2Me.Decomp587fR3TenShort.solution hω hz hφ hφtop

/-- The exact original I2_r3_10 bound follows from its compact profile leaf and proved tail.
Wu 2004 page 26, Table 1 row four page 30. CONDITIONAL ON r3Ten_short. -/
theorem I2_r3_10_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 1 ≤ (2710363 / 500000000 : ℝ) := by
  have hb : buchstabSup ω 1 r3TenLo r3TenHi ≤ (2710363 / 500000000 : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 r3TenLo r3TenHi 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (13 / 5 : ℝ)
      · exact r3Ten_short hω hz hφ ht
      · exact r3Ten_integral_early_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r3TenLo, r3TenHi]

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,11, Table 1 row four page 30.
Only phi from two through thirteen fifths remains. The unbounded tail is proved
by r3Eleven_integral_early_tail. Certify the Buchstab profile on this compact
interval and combine it with the exact reciprocal polynomial moments.
This statement has no supremum and is strictly smaller than the original leaf. -/
theorem r3Eleven_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (13 / 5 : ℝ)) :
    buchstabIntegral ω 1 r3ElevenLo r3ElevenHi φ ≤ (1821597 / 500000000 : ℝ) := by
  exact LeanLab.Ported.Prove2Me.Decomp587fR3ElevenShort.solution hω hz hφ hφtop

/-- The exact original I2_r3_11 bound follows from its compact profile leaf and proved tail.
Wu 2004 page 26, Table 1 row four page 30. CONDITIONAL ON r3Eleven_short. -/
theorem I2_r3_11_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 2 ≤ (1821597 / 500000000 : ℝ) := by
  have hb : buchstabSup ω 1 r3ElevenLo r3ElevenHi ≤ (1821597 / 500000000 : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 r3ElevenLo r3ElevenHi 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (13 / 5 : ℝ)
      · exact r3Eleven_short hω hz hφ ht
      · exact r3Eleven_integral_early_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r3ElevenLo, r3ElevenHi]

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,13, Table 1 row four page 30.
Only phi from two through thirteen fifths remains. The unbounded tail is proved
by r3Thirteen_integral_early_tail. Certify the Buchstab profile on this compact
interval and combine it with the exact reciprocal polynomial moments.
This statement has no supremum and is strictly smaller than the original leaf. -/
theorem r3Thirteen_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (13 / 5 : ℝ)) :
    buchstabIntegral ω 1 r3ThirteenLo r3ThirteenHi φ ≤ (8106273 / 1000000000 : ℝ) := by
  exact LeanLab.Ported.Prove2Me.Decomp587fR3ThirteenShort.solution hω hz hφ hφtop

/-- The exact original I2_r3_13 bound follows from its compact profile leaf and proved tail.
Wu 2004 page 26, Table 1 row four page 30. CONDITIONAL ON r3Thirteen_short. -/
theorem I2_r3_13_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 4 ≤ (8106273 / 1000000000 : ℝ) := by
  have hb : buchstabSup ω 1 r3ThirteenLo r3ThirteenHi ≤ (8106273 / 1000000000 : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 r3ThirteenLo r3ThirteenHi 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (13 / 5 : ℝ)
      · exact r3Thirteen_short hω hz hφ ht
      · exact r3Thirteen_integral_early_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r3ThirteenLo, r3ThirteenHi]

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,14, Table 1 row four page 30.
Only phi from two through thirteen fifths remains. The unbounded tail is proved
by r3Fourteen_integral_early_tail. Certify the Buchstab profile on this compact
interval and combine it with the exact reciprocal polynomial moments.
This statement has no supremum and is strictly smaller than the original leaf. -/
theorem r3Fourteen_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (13 / 5 : ℝ)) :
    buchstabIntegral ω 1 r3FourteenLo r3FourteenHi φ ≤ (2640381 / 1000000000 : ℝ) := by
  exact LeanLab.Ported.Prove2Me.Decomp587fR3FourteenShort.solution hω hz hφ hφtop

/-- The exact original I2_r3_14 bound follows from its compact profile leaf and proved tail.
Wu 2004 page 26, Table 1 row four page 30. CONDITIONAL ON r3Fourteen_short. -/
theorem I2_r3_14_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 5 ≤ (2640381 / 1000000000 : ℝ) := by
  have hb : buchstabSup ω 1 r3FourteenLo r3FourteenHi ≤ (2640381 / 1000000000 : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 r3FourteenLo r3FourteenHi 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (13 / 5 : ℝ)
      · exact r3Fourteen_short hω hz hφ ht
      · exact r3Fourteen_integral_early_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r3FourteenLo, r3FourteenHi]

end LeanLab.ChenDoubleSieve.Task587
