import LeanLab.ChenDoubleSieve.Task587R0J9
import LeanLab.ChenDoubleSieve.Task587R0J10
import LeanLab.ChenDoubleSieve.Task587R0J11
import LeanLab.ChenDoubleSieve.Task587R0J12
import LeanLab.ChenDoubleSieve.Task587R0J13

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

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,9, Table 1 row 1 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r0_9 leaf. -/
theorem r0j9_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j9_lo j : ℝ)) (fun j => (r0j9_hi j : ℝ)) φ ≤ ((870161 / 62500000) : ℝ) := by
  sorry

/-- The exact original I2_r0_9 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 1 page 30. CONDITIONAL ON r0j9_short. -/
theorem I2_r0_9_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 0 ≤ ((870161 / 62500000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r0j9_lo j : ℝ)) (fun j => (r0j9_hi j : ℝ)) ≤ ((870161 / 62500000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r0j9_lo j : ℝ)) (fun j => (r0j9_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r0j9_short hω hz hφ ht
      · exact r0j9_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r0j9_lo, r0j9_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,10, Table 1 row 1 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r0_10 leaf. -/
theorem r0j10_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j10_lo j : ℝ)) (fun j => (r0j10_hi j : ℝ)) φ ≤ ((9342453 / 1000000000) : ℝ) := by
  sorry

/-- The exact original I2_r0_10 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 1 page 30. CONDITIONAL ON r0j10_short. -/
theorem I2_r0_10_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 1 ≤ ((9342453 / 1000000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r0j10_lo j : ℝ)) (fun j => (r0j10_hi j : ℝ)) ≤ ((9342453 / 1000000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r0j10_lo j : ℝ)) (fun j => (r0j10_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r0j10_short hω hz hφ ht
      · exact r0j10_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r0j10_lo, r0j10_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,11, Table 1 row 1 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r0_11 leaf. -/
theorem r0j11_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j11_lo j : ℝ)) (fun j => (r0j11_hi j : ℝ)) φ ≤ ((2272569 / 500000000) : ℝ) := by
  sorry

/-- The exact original I2_r0_11 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 1 page 30. CONDITIONAL ON r0j11_short. -/
theorem I2_r0_11_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 2 ≤ ((2272569 / 500000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r0j11_lo j : ℝ)) (fun j => (r0j11_hi j : ℝ)) ≤ ((2272569 / 500000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r0j11_lo j : ℝ)) (fun j => (r0j11_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r0j11_short hω hz hφ ht
      · exact r0j11_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r0j11_lo, r0j11_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,12, Table 1 row 1 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r0_12 leaf. -/
theorem r0j12_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j12_lo j : ℝ)) (fun j => (r0j12_hi j : ℝ)) φ ≤ ((7085137 / 1000000000) : ℝ) := by
  sorry

/-- The exact original I2_r0_12 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 1 page 30. CONDITIONAL ON r0j12_short. -/
theorem I2_r0_12_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 3 ≤ ((7085137 / 1000000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r0j12_lo j : ℝ)) (fun j => (r0j12_hi j : ℝ)) ≤ ((7085137 / 1000000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r0j12_lo j : ℝ)) (fun j => (r0j12_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r0j12_short hω hz hφ ht
      · exact r0j12_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r0j12_lo, r0j12_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,13, Table 1 row 1 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r0_13 leaf. -/
theorem r0j13_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j13_lo j : ℝ)) (fun j => (r0j13_hi j : ℝ)) φ ≤ ((24633499 / 1000000000) : ℝ) := by
  sorry

/-- The exact original I2_r0_13 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 1 page 30. CONDITIONAL ON r0j13_short. -/
theorem I2_r0_13_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 4 ≤ ((24633499 / 1000000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r0j13_lo j : ℝ)) (fun j => (r0j13_hi j : ℝ)) ≤ ((24633499 / 1000000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r0j13_lo j : ℝ)) (fun j => (r0j13_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r0j13_short hω hz hφ ht
      · exact r0j13_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r0j13_lo, r0j13_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

end LeanLab.ChenDoubleSieve.Task587
