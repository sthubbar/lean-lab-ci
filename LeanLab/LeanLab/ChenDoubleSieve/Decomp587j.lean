import LeanLab.ChenDoubleSieve.Task665R1J17
import LeanLab.Ported.Prove2Me.Decomp587jR1J16
import LeanLab.Ported.Prove2Me.Decomp587jR1J15
import LeanLab.Ported.Prove2Me.Decomp587jR1J14
import LeanLab.Ported.Prove2Me.Decomp587jR1J13
import LeanLab.ChenDoubleSieve.Task587R1J13
import LeanLab.ChenDoubleSieve.Task587R1J14
import LeanLab.ChenDoubleSieve.Task587R1J15
import LeanLab.ChenDoubleSieve.Task587R1J16
import LeanLab.ChenDoubleSieve.Task587R1J17

/-!
Smaller compact profile obligations for Wu 2004 Lemma 5.2 page 26.
Source: https://arxiv.org/abs/0705.1652, Table 1 page 30.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,13, Table 1 row 2 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r1_13 leaf. -/
theorem r1j13_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r1j13_lo j : ℝ)) (fun j => (r1j13_hi j : ℝ)) φ ≤ ((20031169 / 1000000000) : ℝ) := by
  exact LeanLab.Ported.Prove2Me.Decomp587jR1J13.r1j13_short hω hz hφ hφtop

/-- The exact original I2_r1_13 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 2 page 30. CONDITIONAL ON r1j13_short. -/
theorem I2_r1_13_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 4 ≤ ((20031169 / 1000000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r1j13_lo j : ℝ)) (fun j => (r1j13_hi j : ℝ)) ≤ ((20031169 / 1000000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r1j13_lo j : ℝ)) (fun j => (r1j13_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r1j13_short hω hz hφ ht
      · exact r1j13_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r1j13_lo, r1j13_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,14, Table 1 row 2 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r1_14 leaf. -/
theorem r1j14_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r1j14_lo j : ℝ)) (fun j => (r1j14_hi j : ℝ)) φ ≤ ((9167311 / 1000000000) : ℝ) := by
  exact LeanLab.Ported.Prove2Me.Decomp587jR1J14.r1j14_short hω hz hφ hφtop

/-- The exact original I2_r1_14 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 2 page 30. CONDITIONAL ON r1j14_short. -/
theorem I2_r1_14_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 5 ≤ ((9167311 / 1000000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r1j14_lo j : ℝ)) (fun j => (r1j14_hi j : ℝ)) ≤ ((9167311 / 1000000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r1j14_lo j : ℝ)) (fun j => (r1j14_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r1j14_short hω hz hφ ht
      · exact r1j14_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r1j14_lo, r1j14_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,15, Table 1 row 2 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r1_15 leaf. -/
theorem r1j15_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r1j15_lo j : ℝ)) (fun j => (r1j15_hi j : ℝ)) φ ≤ ((2887983 / 1000000000) : ℝ) := by
  exact LeanLab.Ported.Prove2Me.Decomp587jR1J15.r1j15_short hω hz hφ hφtop

/-- The exact original I2_r1_15 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 2 page 30. CONDITIONAL ON r1j15_short. -/
theorem I2_r1_15_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 6 ≤ ((2887983 / 1000000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r1j15_lo j : ℝ)) (fun j => (r1j15_hi j : ℝ)) ≤ ((2887983 / 1000000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r1j15_lo j : ℝ)) (fun j => (r1j15_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r1j15_short hω hz hφ ht
      · exact r1j15_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r1j15_lo, r1j15_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,16, Table 1 row 2 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r1_16 leaf. -/
theorem r1j16_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 2 (fun j => (r1j16_lo j : ℝ)) (fun j => (r1j16_hi j : ℝ)) φ ≤ ((35393 / 500000000) : ℝ) := by
  exact LeanLab.Ported.Prove2Me.Decomp587jR1J16.r1j16_short hω hz hφ hφtop

/-- The exact original I2_r1_16 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 2 page 30. CONDITIONAL ON r1j16_short. -/
theorem I2_r1_16_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 7 ≤ ((35393 / 500000000) : ℝ) := by
  have hb : buchstabSup ω 2 (fun j => (r1j16_lo j : ℝ)) (fun j => (r1j16_hi j : ℝ)) ≤ ((35393 / 500000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 2 (fun j => (r1j16_lo j : ℝ)) (fun j => (r1j16_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r1j16_short hω hz hφ ht
      · exact r1j16_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r1j16_lo, r1j16_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,17, Table 1 row 2 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r1_17 leaf. -/
theorem r1j17_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 2 (fun j => (r1j17_lo j : ℝ)) (fun j => (r1j17_hi j : ℝ)) φ ≤ ((92979 / 1000000000) : ℝ) := by
  exact Task665R1.r1j17_certified hω hz hφ hφtop

/-- The exact original I2_r1_17 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 2 page 30. CONDITIONAL ON r1j17_short. -/
theorem I2_r1_17_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 8 ≤ ((92979 / 1000000000) : ℝ) := by
  have hb : buchstabSup ω 2 (fun j => (r1j17_lo j : ℝ)) (fun j => (r1j17_hi j : ℝ)) ≤ ((92979 / 1000000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 2 (fun j => (r1j17_lo j : ℝ)) (fun j => (r1j17_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r1j17_short hω hz hφ ht
      · exact r1j17_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r1j17_lo, r1j17_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

end LeanLab.ChenDoubleSieve.Task587
