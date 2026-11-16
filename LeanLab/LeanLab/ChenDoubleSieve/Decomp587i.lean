import LeanLab.ChenDoubleSieve.Task587R2J16
import LeanLab.ChenDoubleSieve.Task587R1J9
import LeanLab.ChenDoubleSieve.Task587R1J10
import LeanLab.ChenDoubleSieve.Task587R1J11
import LeanLab.ChenDoubleSieve.Task587R1J12

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

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,16, Table 1 row 3 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r2_16 leaf. -/
theorem r2j16_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 2 (fun j => (r2j16_lo j : ℝ)) (fun j => (r2j16_hi j : ℝ)) φ ≤ ((42971 / 500000000) : ℝ) := by
  sorry

/-- The exact original I2_r2_16 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 3 page 30. CONDITIONAL ON r2j16_short. -/
theorem I2_r2_16_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 7 ≤ ((42971 / 500000000) : ℝ) := by
  have hb : buchstabSup ω 2 (fun j => (r2j16_lo j : ℝ)) (fun j => (r2j16_hi j : ℝ)) ≤ ((42971 / 500000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 2 (fun j => (r2j16_lo j : ℝ)) (fun j => (r2j16_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r2j16_short hω hz hφ ht
      · exact r2j16_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r2j16_lo, r2j16_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,9, Table 1 row 2 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r1_9 leaf. -/
theorem r1j9_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r1j9_lo j : ℝ)) (fun j => (r1j9_hi j : ℝ)) φ ≤ ((14713151 / 1000000000) : ℝ) := by
  sorry

/-- The exact original I2_r1_9 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 2 page 30. CONDITIONAL ON r1j9_short. -/
theorem I2_r1_9_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 0 ≤ ((14713151 / 1000000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r1j9_lo j : ℝ)) (fun j => (r1j9_hi j : ℝ)) ≤ ((14713151 / 1000000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r1j9_lo j : ℝ)) (fun j => (r1j9_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r1j9_short hω hz hφ ht
      · exact r1j9_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r1j9_lo, r1j9_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,10, Table 1 row 2 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r1_10 leaf. -/
theorem r1j10_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r1j10_lo j : ℝ)) (fun j => (r1j10_hi j : ℝ)) φ ≤ ((8347739 / 1000000000) : ℝ) := by
  sorry

/-- The exact original I2_r1_10 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 2 page 30. CONDITIONAL ON r1j10_short. -/
theorem I2_r1_10_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 1 ≤ ((8347739 / 1000000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r1j10_lo j : ℝ)) (fun j => (r1j10_hi j : ℝ)) ≤ ((8347739 / 1000000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r1j10_lo j : ℝ)) (fun j => (r1j10_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r1j10_short hω hz hφ ht
      · exact r1j10_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r1j10_lo, r1j10_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,11, Table 1 row 2 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r1_11 leaf. -/
theorem r1j11_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r1j11_lo j : ℝ)) (fun j => (r1j11_hi j : ℝ)) φ ≤ ((2294543 / 500000000) : ℝ) := by
  sorry

/-- The exact original I2_r1_11 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 2 page 30. CONDITIONAL ON r1j11_short. -/
theorem I2_r1_11_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 2 ≤ ((2294543 / 500000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r1j11_lo j : ℝ)) (fun j => (r1j11_hi j : ℝ)) ≤ ((2294543 / 500000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r1j11_lo j : ℝ)) (fun j => (r1j11_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r1j11_short hω hz hφ ht
      · exact r1j11_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r1j11_lo, r1j11_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,12, Table 1 row 2 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r1_12 leaf. -/
theorem r1j12_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r1j12_lo j : ℝ)) (fun j => (r1j12_hi j : ℝ)) φ ≤ ((3417039 / 1000000000) : ℝ) := by
  sorry

/-- The exact original I2_r1_12 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 2 page 30. CONDITIONAL ON r1j12_short. -/
theorem I2_r1_12_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 3 ≤ ((3417039 / 1000000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r1j12_lo j : ℝ)) (fun j => (r1j12_hi j : ℝ)) ≤ ((3417039 / 1000000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r1j12_lo j : ℝ)) (fun j => (r1j12_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r1j12_short hω hz hφ ht
      · exact r1j12_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r1j12_lo, r1j12_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

end LeanLab.ChenDoubleSieve.Task587
