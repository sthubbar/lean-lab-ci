/-
Jia 1996 Lemma 27, pages 281 and 282, exact polynomial integral certificates.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.RemainderData564

namespace LeanLab.Languasco2004.Polynomial564a
open Real intervalIntegral RemainderData564
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Pages 281 and 282: exact polynomial integration for printed term 3. -/
theorem polynomial_integral_3 :
    let i : Fin 16 := ⟨1, by decide⟩
    let r := numericData i
    (r 9 : ℝ) ≤ ∫ t in (r 0 : ℝ)..(r 1),
      ∫ u in ((r 2 : ℝ) + r 3*t)..((r 4 : ℝ) + r 5*t), polynomial i t u := by
  norm_num [polynomial, numericData, isLog, reciprocal]
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  norm_num

#print axioms polynomial_integral_3

/-- Pages 281 and 282: exact polynomial integration for printed term 5. -/
theorem polynomial_integral_5 :
    let i : Fin 16 := ⟨3, by decide⟩
    let r := numericData i
    (r 9 : ℝ) ≤ ∫ t in (r 0 : ℝ)..(r 1),
      ∫ u in ((r 2 : ℝ) + r 3*t)..((r 4 : ℝ) + r 5*t), polynomial i t u := by
  norm_num [polynomial, numericData, isLog, reciprocal]
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  norm_num

#print axioms polynomial_integral_5

/-- Pages 281 and 282: exact polynomial integration for printed term 6. -/
theorem polynomial_integral_6 :
    let i : Fin 16 := ⟨4, by decide⟩
    let r := numericData i
    (r 9 : ℝ) ≤ ∫ t in (r 0 : ℝ)..(r 1),
      ∫ u in ((r 2 : ℝ) + r 3*t)..((r 4 : ℝ) + r 5*t), polynomial i t u := by
  norm_num [polynomial, numericData, isLog, reciprocal]
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  norm_num

#print axioms polynomial_integral_6

/-- Pages 281 and 282: exact polynomial integration for printed term 8. -/
theorem polynomial_integral_8 :
    let i : Fin 16 := ⟨6, by decide⟩
    let r := numericData i
    (r 9 : ℝ) ≤ ∫ t in (r 0 : ℝ)..(r 1),
      ∫ u in ((r 2 : ℝ) + r 3*t)..((r 4 : ℝ) + r 5*t), polynomial i t u := by
  norm_num [polynomial, numericData, isLog, reciprocal]
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  norm_num

#print axioms polynomial_integral_8

/-- Pages 281 and 282: exact polynomial integration for printed term 10. -/
theorem polynomial_integral_10 :
    let i : Fin 16 := ⟨8, by decide⟩
    let r := numericData i
    (r 9 : ℝ) ≤ ∫ t in (r 0 : ℝ)..(r 1),
      ∫ u in ((r 2 : ℝ) + r 3*t)..((r 4 : ℝ) + r 5*t), polynomial i t u := by
  norm_num [polynomial, numericData, isLog, reciprocal]
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  norm_num

#print axioms polynomial_integral_10

/-- Pages 281 and 282: exact polynomial integration for printed term 12. -/
theorem polynomial_integral_12 :
    let i : Fin 16 := ⟨10, by decide⟩
    let r := numericData i
    (r 9 : ℝ) ≤ ∫ t in (r 0 : ℝ)..(r 1),
      ∫ u in ((r 2 : ℝ) + r 3*t)..((r 4 : ℝ) + r 5*t), polynomial i t u := by
  norm_num [polynomial, numericData, isLog, reciprocal]
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  norm_num

#print axioms polynomial_integral_12

/-- Pages 281 and 282: exact polynomial integration for printed term 14. -/
theorem polynomial_integral_14 :
    let i : Fin 16 := ⟨12, by decide⟩
    let r := numericData i
    (r 9 : ℝ) ≤ ∫ t in (r 0 : ℝ)..(r 1),
      ∫ u in ((r 2 : ℝ) + r 3*t)..((r 4 : ℝ) + r 5*t), polynomial i t u := by
  norm_num [polynomial, numericData, isLog, reciprocal]
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  norm_num

#print axioms polynomial_integral_14

/-- Pages 281 and 282: exact polynomial integration for printed term 16. -/
theorem polynomial_integral_16 :
    let i : Fin 16 := ⟨14, by decide⟩
    let r := numericData i
    (r 9 : ℝ) ≤ ∫ t in (r 0 : ℝ)..(r 1),
      ∫ u in ((r 2 : ℝ) + r 3*t)..((r 4 : ℝ) + r 5*t), polynomial i t u := by
  norm_num [polynomial, numericData, isLog, reciprocal]
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  norm_num

#print axioms polynomial_integral_16
end
end LeanLab.Languasco2004.Polynomial564a
