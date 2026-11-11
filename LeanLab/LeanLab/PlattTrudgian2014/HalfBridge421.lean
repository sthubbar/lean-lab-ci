/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 pages 173 to 185. The degree 16 Taylor variant uses the certified task125 data.
The recurrence follows the written Lemma 5 zero column convention recorded by task380.
-/
import LeanLab.PlattTrudgian2014.NormBridge421
import LeanLab.PlattTrudgian2014.Decomp380b

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Filter
open scoped Topology

/-- P0026 Theorem 2 and Lemmas 4 to 7, the exact sealed half norm moment target.
The recurrence, norm comparison, finite certificates and iteration are all discharged. -/
theorem half_norm_moment_transfer_proved421
    (hmajor : ∀ x : ℝ, Real.exp ((halfParameter125 : ℝ) * Real.cos x) ≤ halfCosPoly125 x)
    (hcoeff : ∀ j : Fin 17, 0 ≤ halfCoeff125 j)
    (hvec : ∀ j : Fin 16, 0 < halfVector125 j)
    (hcert : ∀ i : Fin 16, (∑ j : Fin 16, halfTransfer125 i j * halfVector125 j) ≤
      halfRadius125 * halfVector125 i) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ L : ℕ,
      (∫ x : ℝ in 0..1, Real.exp ((halfParameter125 : ℝ) * ‖G L x‖)) ≤
        A * Real.exp ((Real.log (halfRadius125 : ℝ) + 0.0000000000001) * L) := by
  have ht : (0 : ℝ) ≤ halfParameter125 := by exact_mod_cast half_parameter_box125.1.le
  have hr : (0 : ℝ) < halfRadius125 := by exact_mod_cast (lt_trans (by norm_num) half_radius_box125.1)
  have hU : ∀ i j : Fin 16, (0 : ℝ) ≤ halfTransfer125 i j := by
    intro i j
    have hb (k : ℤ) : 0 ≤ halfCoeffInt125 k := by
      unfold halfCoeffInt125
      split_ifs
      · exact hcoeff _
      · exact le_rfl
    have hb1 := hb (2 * (j : ℤ) - i)
    have hb2 := hb (2 * (j : ℤ) + i)
    have hb3 := hb ((i : ℤ) - 2 * j)
    have hu : 0 ≤ halfTransfer125 i j := by
      unfold halfTransfer125
      split_ifs <;> positivity
    exact_mod_cast hu
  have hw0 : (halfVector125 0 : ℝ) = 1 := by norm_num [halfVector125]
  have hbase : ∀ i : Fin 16, halfProductMoment281 0 i ≤ (halfVector125 i : ℝ) := by
    intro i
    rw [half_product_initial281]
    split_ifs with hi
    · simpa [hi, hw0]
    · exact_mod_cast (hvec i).le
  have hiter (L : ℕ) : halfProductMoment281 L 0 ≤ (halfRadius125 : ℝ) ^ L := by
    have hc (i : Fin 16) :
        (∑ j : Fin 16, (halfTransfer125 i j : ℝ) * (halfVector125 j : ℝ)) ≤
          (halfRadius125 : ℝ) * (halfVector125 i : ℝ) := by exact_mod_cast hcert i
    simpa [hw0] using transfer_iterate125
      (fun i j => (halfTransfer125 i j : ℝ)) (fun i => (halfVector125 i : ℝ))
      (halfRadius125 : ℝ) 1 halfProductMoment281 hU hr.le (by norm_num)
      (by simpa using hbase) half_product_recurrence_decomposed380 hc L 0
  obtain ⟨C, hC, hcomp⟩ := norm_real_moment_comparison_proved421 (halfParameter125 : ℝ) ht
  obtain ⟨B, hB, habs⟩ := sqrt_prefactor_absorbed281 (halfParameter125 : ℝ)
    0.0000000000001 ht (by norm_num)
  refine ⟨C * B, mul_nonneg hC hB, fun L => ?_⟩
  have hm := (half_real_moment_majorized281 hmajor L).trans (hiter L)
  calc
    _ ≤ C * (1 + Real.sqrt ((halfParameter125 : ℝ) * L)) * (halfRadius125 : ℝ) ^ L :=
      (hcomp L).trans (mul_le_mul_of_nonneg_left hm (by positivity))
    _ ≤ C * (B * Real.exp (0.0000000000001 * L)) * (halfRadius125 : ℝ) ^ L := by
      gcongr
      exact habs L
    _ = C * B * (Real.exp (0.0000000000001 * L) *
        Real.exp (Real.log (halfRadius125 : ℝ) * L)) := by
      have hp : (halfRadius125 : ℝ) ^ L =
          Real.exp (Real.log (halfRadius125 : ℝ) * L) := by
        rw [mul_comm, Real.exp_nat_mul, Real.exp_log hr]
      rw [hp]
      ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

/-- P0026 pages 184 to 185, the certified half exponent moment gap. -/
theorem pr_half_moment_certificate_proved421 :
    ∃ t A b : ℝ, 0 < t ∧ 0 ≤ A ∧
      b < t * 0.7163435444776661 - (1 / 2) * Real.log 2 ∧
      ∀ L : ℕ, (∫ x : ℝ in 0..1, Real.exp (t * ‖G L x‖)) ≤
        A * Real.exp (b * L) := by
  obtain ⟨A, hA, hm⟩ := half_norm_moment_transfer_proved421 half_exp_majorant125
    half_coeff_nonneg125 half_vector_pos125 half_perron_certificate125
  refine ⟨(halfParameter125 : ℝ), A,
    Real.log (halfRadius125 : ℝ) + 0.0000000000001, ?_, hA, ?_, hm⟩
  · exact_mod_cast half_parameter_box125.1
  · have hg := half_pressure_gap125
    linarith

/-- P0026 page 185 Corollary 1, the exact existing half exponent cited Prop. -/
theorem pr_half_input_proved421 : PRHalfInput := by
  obtain ⟨t, A, b, ht, hA, hgap, hm⟩ := pr_half_moment_certificate_proved421
  apply powerLogBound_of_exp_decay125 hA (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by linarith : (1 / 2 : ℝ) * Real.log 2 < t * 0.7163435444776661 - b)
  intro N _
  exact large_values_of_norm_moment125 ht hm N

/-- P0024 page 6, the exact existing half exponent lambda conclusion.
This uses the repaired normalization already present in LambdaOK. -/
theorem pt_lambda_GRH_proved421 : LambdaOK (1 / 2) 0.7163436 :=
  pt_lambda_GRH_of_pr pr_half_input_proved421

set_option format.width 240
#print axioms half_norm_moment_transfer_proved421
#print axioms pr_half_moment_certificate_proved421
#print axioms pr_half_input_proved421
#print axioms pt_lambda_GRH_proved421

end LeanLab.PlattTrudgian2014
