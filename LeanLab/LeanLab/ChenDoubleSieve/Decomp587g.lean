import LeanLab.Ported.Prove2Me.Decomp587g
import LeanLab.ChenDoubleSieve.Task587R0J18
import LeanLab.ChenDoubleSieve.Task587PairMoments

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

/-- Wu 2004 Lemma 5.2 page 26, D2,18, Table 1 row one page 30.
An exact polynomial moment on two separated ordered pairs.
The coefficient list, its rational candidate and its algebraic identity are
already supplied. Split product volume across the two pairs and apply
ordered_shifted_monomial in dimension two to each monomial.
This piece has no Buchstab function, no phi parameter and no supremum. -/
theorem r0j18_polynomial_moment :
    (∫ x in domain (fun j => (r0j18_lo j : ℝ)) (fun j => (r0j18_hi j : ℝ)), cellPoly 4 (2 : Fin 4) r0j18_lo r0j18_hi x) = ((703339176360357635785404251179921753005659 / 3730562034504042713022920634997268666666880000) : ℝ) := by
  have h := integral_listEvalPair r0j18_terms (a := 10 / 29) (b := 25 / 61)
    (c := 5 / 11) (by norm_num) (by norm_num)
  have he (x : Fin 4 → ℝ) :
      listEvalN r0j18_terms (fun j => x j - (![(10 / 29 : ℝ), (10 / 29 : ℝ), (25 / 61 : ℝ), (25 / 61 : ℝ)] : Fin 4 → ℝ) j) =
      cellPoly 4 (2 : Fin 4) r0j18_lo r0j18_hi x := by
    rw [r0j18_eval]
    congr 1
    ext j
    fin_cases j <;> norm_num [r0j18_lo] <;> ring
  push_cast at h
  simp_rw [he] at h
  have hL : (![(10 / 29 : ℝ), (10 / 29 : ℝ), (25 / 61 : ℝ), (25 / 61 : ℝ)] : Fin 4 → ℝ) =
      (fun j => (r0j18_lo j : ℝ)) := by
    ext j; fin_cases j <;> norm_num [r0j18_lo]
  have hH : (![(25 / 61 : ℝ), (25 / 61 : ℝ), (5 / 11 : ℝ), (5 / 11 : ℝ)] : Fin 4 → ℝ) =
      (fun j => (r0j18_hi j : ℝ)) := by
    ext j; fin_cases j <;> norm_num [r0j18_hi]
  rw [hL, hH, r0j18_moment] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

/-- The phi tail follows from the exact polynomial moment.
Wu 2004 page 26, D2,18, Table 1 row one page 30. -/
theorem r0j18_tail {ω : ℝ → ℝ} (hω : IsBuchstab ω) {φ : ℝ} (hφ : (7 / 2 : ℝ) ≤ φ) :
    buchstabIntegral ω 2 (fun j => (r0j18_lo j : ℝ)) (fun j => (r0j18_hi j : ℝ)) φ ≤ ((155569 / 1000000000) : ℝ) := by
  have h := cell_tail_integral hω (n := 2) (by norm_num) 4 r0j18_lo r0j18_hi hφ
    (by intro j; fin_cases j <;> norm_num [r0j18_lo])
    (by intro j; fin_cases j <;> norm_num [r0j18_lo, r0j18_hi])
    (by intro j; fin_cases j <;> norm_num [r0j18_hi])
  change buchstabIntegral ω 2 (fun j => (r0j18_lo j : ℝ)) (fun j => (r0j18_hi j : ℝ)) φ ≤ (5618 / 10000 : ℝ) * (∫ x in domain (fun j => (r0j18_lo j : ℝ)) (fun j => (r0j18_hi j : ℝ)), cellPoly 4 (2 : Fin 4) r0j18_lo r0j18_hi x) at h
  rw [r0j18_polynomial_moment] at h
  exact h.trans (by norm_num)

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,18, Table 1 row 1 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r0_18 leaf. -/
theorem r0j18_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 2 (fun j => (r0j18_lo j : ℝ)) (fun j => (r0j18_hi j : ℝ)) φ ≤ ((155569 / 1000000000) : ℝ) := by
  exact LeanLab.Ported.Prove2Me.Task662.solution hω hz hφ hφtop

/-- The exact original I2_r0_18 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 1 page 30. CONDITIONAL ON r0j18_short. -/
theorem I2_r0_18_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 9 ≤ ((155569 / 1000000000) : ℝ) := by
  have hb : buchstabSup ω 2 (fun j => (r0j18_lo j : ℝ)) (fun j => (r0j18_hi j : ℝ)) ≤ ((155569 / 1000000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 2 (fun j => (r0j18_lo j : ℝ)) (fun j => (r0j18_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r0j18_short hω hz hφ ht
      · exact r0j18_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r0j18_lo, r0j18_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

end LeanLab.ChenDoubleSieve.Task587
