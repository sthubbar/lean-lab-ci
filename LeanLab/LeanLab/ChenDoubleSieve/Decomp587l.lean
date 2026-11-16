import LeanLab.ChenDoubleSieve.Task587R0J14
import LeanLab.ChenDoubleSieve.Task587R0J15
import LeanLab.ChenDoubleSieve.Task587R0J16
import LeanLab.ChenDoubleSieve.Task587R0J17
import LeanLab.ChenDoubleSieve.Task587R0J19

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

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,14, Table 1 row 1 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r0_14 leaf. -/
theorem r0j14_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j14_lo j : ℝ)) (fun j => (r0j14_hi j : ℝ)) φ ≤ ((14345377 / 1000000000) : ℝ) := by
  sorry

/-- The exact original I2_r0_14 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 1 page 30. CONDITIONAL ON r0j14_short. -/
theorem I2_r0_14_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 5 ≤ ((14345377 / 1000000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r0j14_lo j : ℝ)) (fun j => (r0j14_hi j : ℝ)) ≤ ((14345377 / 1000000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r0j14_lo j : ℝ)) (fun j => (r0j14_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r0j14_short hω hz hφ ht
      · exact r0j14_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r0j14_lo, r0j14_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,15, Table 1 row 1 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r0_15 leaf. -/
theorem r0j15_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j15_lo j : ℝ)) (fun j => (r0j15_hi j : ℝ)) φ ≤ ((662003 / 125000000) : ℝ) := by
  sorry

/-- The exact original I2_r0_15 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 1 page 30. CONDITIONAL ON r0j15_short. -/
theorem I2_r0_15_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 6 ≤ ((662003 / 125000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r0j15_lo j : ℝ)) (fun j => (r0j15_hi j : ℝ)) ≤ ((662003 / 125000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r0j15_lo j : ℝ)) (fun j => (r0j15_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r0j15_short hω hz hφ ht
      · exact r0j15_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r0j15_lo, r0j15_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,16, Table 1 row 1 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r0_16 leaf. -/
theorem r0j16_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 2 (fun j => (r0j16_lo j : ℝ)) (fun j => (r0j16_hi j : ℝ)) φ ≤ ((18727 / 250000000) : ℝ) := by
  sorry

/-- The exact original I2_r0_16 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 1 page 30. CONDITIONAL ON r0j16_short. -/
theorem I2_r0_16_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 7 ≤ ((18727 / 250000000) : ℝ) := by
  have hb : buchstabSup ω 2 (fun j => (r0j16_lo j : ℝ)) (fun j => (r0j16_hi j : ℝ)) ≤ ((18727 / 250000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 2 (fun j => (r0j16_lo j : ℝ)) (fun j => (r0j16_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r0j16_short hω hz hφ ht
      · exact r0j16_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r0j16_lo, r0j16_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,17, Table 1 row 1 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r0_17 leaf. -/
theorem r0j17_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 2 (fun j => (r0j17_lo j : ℝ)) (fun j => (r0j17_hi j : ℝ)) φ ≤ ((45791 / 250000000) : ℝ) := by
  sorry

/-- The exact original I2_r0_17 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 1 page 30. CONDITIONAL ON r0j17_short. -/
theorem I2_r0_17_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 8 ≤ ((45791 / 250000000) : ℝ) := by
  have hb : buchstabSup ω 2 (fun j => (r0j17_lo j : ℝ)) (fun j => (r0j17_hi j : ℝ)) ≤ ((45791 / 250000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 2 (fun j => (r0j17_lo j : ℝ)) (fun j => (r0j17_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r0j17_short hω hz hφ ht
      · exact r0j17_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r0j17_lo, r0j17_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,19, Table 1 row 1 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r0_19 leaf. -/
theorem r0j19_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 2 (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) φ ≤ ((70737 / 1000000000) : ℝ) := by
  sorry

/-- The exact original I2_r0_19 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 1 page 30. CONDITIONAL ON r0j19_short. -/
theorem I2_r0_19_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 10 ≤ ((70737 / 1000000000) : ℝ) := by
  have hb : buchstabSup ω 2 (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) ≤ ((70737 / 1000000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 2 (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r0j19_short hω hz hφ ht
      · exact r0j19_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r0j19_lo, r0j19_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

end LeanLab.ChenDoubleSieve.Task587
