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

/-- The sharp reciprocal certificate only needs a uniform lower bound of seven halves on the
kernel argument; the phi threshold of `cell_tail_integral` is only one way to obtain it.
Wu 2004 pages 9 and 26, derived uniform polynomial reduction. -/
private theorem cell_integral_of_argument {ω : ℝ → ℝ} (hω : IsBuchstab ω) {n : ℕ}
    (N : ℕ) (lo hi : Fin (n + 2) → ℚ) {φ : ℝ}
    (hlo : ∀ j, 0 < lo j) (hle : ∀ j, lo j ≤ hi j)
    (harg : ∀ x ∈ domain (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)),
      (7 / 2 : ℝ) ≤ (φ - ∑ j, x j) / x ⟨n, by omega⟩) :
    buchstabIntegral ω n (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)) φ ≤
      (5618 / 10000 : ℝ) * ∫ x in domain (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)),
        cellPoly N ⟨n, by omega⟩ lo hi x := by
  have hl (j : Fin (n + 2)) : (0 : ℝ) < lo j := by exact_mod_cast hlo j
  have hf := kernel_integrable_above_one hω (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)) φ hl
    (fun x hx => (by norm_num : (1 : ℝ) ≤ 7 / 2).trans (harg x hx))
  have hm := setIntegral_mono_on hf
    ((cellPoly_integrable N ⟨n, by omega⟩ lo hi).const_mul (5618 / 10000 : ℝ))
    (Wu04I1.domain_isCompact _ _).measurableSet (fun x hx => by
      have hp (j : Fin (n + 2)) : 0 < x j := (hl j).trans_le (hx.2 j).1
      have hd : 0 < (∏ j, x j) * x ⟨n, by omega⟩ := mul_pos (prod_pos fun j _ => hp j) (hp _)
      have hw := div_le_div_of_nonneg_right (buchstab_le_5618 hω (harg x hx)) hd.le
      calc
        _ ≤ (5618 / 10000 : ℝ) / ((∏ j, x j) * x ⟨n, by omega⟩) := hw
        _ = (5618 / 10000 : ℝ) * (1 / ((∏ j, x j) * x ⟨n, by omega⟩)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_le_cellPoly N _ lo hi hlo hle hx) (by norm_num))
  simpa only [buchstabIntegral, MeasureTheory.integral_const_mul] using hm

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,12, Table 1 row 2 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r1_12 leaf. -/
theorem r1j12_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r1j12_lo j : ℝ)) (fun j => (r1j12_hi j : ℝ)) φ ≤ ((3417039 / 1000000000) : ℝ) := by
  have harg : ∀ x ∈ domain (fun j => (r1j12_lo j : ℝ)) (fun j => (r1j12_hi j : ℝ)),
      (7 / 2 : ℝ) ≤ (φ - ∑ j, x j) / x ⟨1, by omega⟩ := by
    intro x hx
    change (7 / 2 : ℝ) ≤ (φ - ∑ j, x j) / x 1
    have hlo1 : ((2 / 9 : ℚ) : ℝ) ≤ x 1 := (hx.2 1).1
    have hhi1 : x 1 ≤ ((50 / 177 : ℚ) : ℝ) := (hx.2 1).2
    have hpos : (0 : ℝ) < x 1 := by
      have h2 : (0 : ℝ) < ((2 / 9 : ℚ) : ℝ) := by norm_num
      linarith
    have hsum : ∑ j, x j ≤ ((4070 / 4071 : ℚ) : ℝ) := by
      rw [Fin.sum_univ_three]
      have h0 : x 0 ≤ ((50 / 177 : ℚ) : ℝ) := (hx.2 0).2
      have h2 : x 2 ≤ ((10 / 23 : ℚ) : ℝ) := (hx.2 2).2
      linarith
    rw [le_div_iff₀ hpos]
    push_cast at hhi1 hsum
    have hm : (7 / 2 : ℝ) * x 1 ≤ (7 / 2 : ℝ) * (50 / 177 : ℝ) := by
      nlinarith [hhi1]
    nlinarith [hφ, hm, hsum]
  have h := cell_integral_of_argument hω (n := 1) 6 r1j12_lo r1j12_hi
    (by intro j; fin_cases j <;> norm_num [r1j12_lo])
    (by intro j; fin_cases j <;> norm_num [r1j12_lo, r1j12_hi])
    harg
  change buchstabIntegral ω 1 (fun j => (r1j12_lo j : ℝ)) (fun j => (r1j12_hi j : ℝ)) φ ≤
    (5618 / 10000 : ℝ) * (∫ x in domain (fun j => (r1j12_lo j : ℝ)) (fun j => (r1j12_hi j : ℝ)),
      cellPoly 6 (1 : Fin 3) r1j12_lo r1j12_hi x) at h
  rw [r1j12_integral] at h
  exact h.trans (by norm_num)

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
