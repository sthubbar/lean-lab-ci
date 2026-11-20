import LeanLab.Ported.Prove2Me.Decomp587hR2J14
import LeanLab.Ported.Prove2Me.Decomp587hR2J13
import LeanLab.Ported.Prove2Me.Decomp587hR2J11
import LeanLab.Ported.Prove2Me.Decomp587hR2J10
import LeanLab.Ported.Prove2Me.Decomp587hR2J9
import LeanLab.ChenDoubleSieve.Task587R2J9
import LeanLab.ChenDoubleSieve.Task587R2J10
import LeanLab.ChenDoubleSieve.Task587R2J11
import LeanLab.ChenDoubleSieve.Task587R2J13
import LeanLab.ChenDoubleSieve.Task587R2J14

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

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,9, Table 1 row 3 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r2_9 leaf. -/
theorem r2j9_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r2j9_lo j : ℝ)) (fun j => (r2j9_hi j : ℝ)) φ ≤ ((8633809 / 500000000) : ℝ) := by
  exact LeanLab.Ported.Prove2Me.Decomp587hR2J9.solution hω hz hφ hφtop

/-- The exact original I2_r2_9 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 3 page 30. CONDITIONAL ON r2j9_short. -/
theorem I2_r2_9_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 0 ≤ ((8633809 / 500000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r2j9_lo j : ℝ)) (fun j => (r2j9_hi j : ℝ)) ≤ ((8633809 / 500000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r2j9_lo j : ℝ)) (fun j => (r2j9_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r2j9_short hω hz hφ ht
      · exact r2j9_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r2j9_lo, r2j9_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,10, Table 1 row 3 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r2_10 leaf. -/
theorem r2j10_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r2j10_lo j : ℝ)) (fun j => (r2j10_hi j : ℝ)) φ ≤ ((3714811 / 500000000) : ℝ) := by
  exact LeanLab.Ported.Prove2Me.Decomp587hR2J10.solution hω hz hφ hφtop

/-- The exact original I2_r2_10 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 3 page 30. CONDITIONAL ON r2j10_short. -/
theorem I2_r2_10_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 1 ≤ ((3714811 / 500000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r2j10_lo j : ℝ)) (fun j => (r2j10_hi j : ℝ)) ≤ ((3714811 / 500000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r2j10_lo j : ℝ)) (fun j => (r2j10_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r2j10_short hω hz hφ ht
      · exact r2j10_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r2j10_lo, r2j10_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,11, Table 1 row 3 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r2_11 leaf. -/
theorem r2j11_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r2j11_lo j : ℝ)) (fun j => (r2j11_hi j : ℝ)) φ ≤ ((5342719 / 1000000000) : ℝ) := by
  exact LeanLab.Ported.Prove2Me.Decomp587hR2J11.solution hω hz hφ hφtop

/-- The exact original I2_r2_11 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 3 page 30. CONDITIONAL ON r2j11_short. -/
theorem I2_r2_11_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 2 ≤ ((5342719 / 1000000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r2j11_lo j : ℝ)) (fun j => (r2j11_hi j : ℝ)) ≤ ((5342719 / 1000000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r2j11_lo j : ℝ)) (fun j => (r2j11_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r2j11_short hω hz hφ ht
      · exact r2j11_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r2j11_lo, r2j11_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,13, Table 1 row 3 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r2_13 leaf. -/
theorem r2j13_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r2j13_lo j : ℝ)) (fun j => (r2j13_hi j : ℝ)) φ ≤ ((489689 / 31250000) : ℝ) := by
  exact LeanLab.Ported.Prove2Me.Decomp587hR2J13.solution hω hz hφ hφtop

/-- The exact original I2_r2_13 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 3 page 30. CONDITIONAL ON r2j13_short. -/
theorem I2_r2_13_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 4 ≤ ((489689 / 31250000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r2j13_lo j : ℝ)) (fun j => (r2j13_hi j : ℝ)) ≤ ((489689 / 31250000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r2j13_lo j : ℝ)) (fun j => (r2j13_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r2j13_short hω hz hφ ht
      · exact r2j13_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r2j13_lo, r2j13_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,14, Table 1 row 3 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r2_14 leaf. -/
theorem r2j14_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r2j14_lo j : ℝ)) (fun j => (r2j14_hi j : ℝ)) φ ≤ ((54491 / 10000000) : ℝ) := by
  exact LeanLab.Ported.Prove2Me.Decomp587hR2J14.solution hω hz hφ hφtop

/-- The exact original I2_r2_14 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 3 page 30. CONDITIONAL ON r2j14_short. -/
theorem I2_r2_14_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 5 ≤ ((54491 / 10000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r2j14_lo j : ℝ)) (fun j => (r2j14_hi j : ℝ)) ≤ ((54491 / 10000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r2j14_lo j : ℝ)) (fun j => (r2j14_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r2j14_short hω hz hφ ht
      · exact r2j14_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r2j14_lo, r2j14_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

end LeanLab.ChenDoubleSieve.Task587

#print axioms LeanLab.ChenDoubleSieve.Task587.r2j9_short
#print axioms LeanLab.ChenDoubleSieve.Task587.I2_r2_9_from_short

#print axioms LeanLab.ChenDoubleSieve.Task587.r2j10_short
#print axioms LeanLab.ChenDoubleSieve.Task587.I2_r2_10_from_short

#print axioms LeanLab.ChenDoubleSieve.Task587.r2j11_short
#print axioms LeanLab.ChenDoubleSieve.Task587.I2_r2_11_from_short

#print axioms LeanLab.ChenDoubleSieve.Task587.r2j13_short
#print axioms LeanLab.ChenDoubleSieve.Task587.I2_r2_13_from_short

#print axioms LeanLab.ChenDoubleSieve.Task587.r2j14_short
#print axioms LeanLab.ChenDoubleSieve.Task587.I2_r2_14_from_short
