/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 is Pintz and Ruzsa 2003, cited by Platt and Trudgian 2014.
This file decomposes Corollary 1 on page 185 through the existing PRHalfInput.
The analytic norm moment transfer is open. The finite pressure data are certified.
-/
import LeanLab.PlattTrudgian2014.PRSavings
import LeanLab.PlattTrudgian2014.Pressure125
import LeanLab.PlattTrudgian2014.Polynomial125

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Filter
open scoped Topology

/-- LEAF. P0026 pages 173 to 179, Theorem 2 and Lemmas 4 to 7.
The positive cosine majorant and nonnegative transfer certificate bound real moments.
The norm comparison of Section 4 gives a polynomial prefactor, absorbed in 1e-13 per term.
All finite certificate hypotheses below have independent kernel proofs. -/
theorem half_norm_moment_transfer125
    (hmajor : ∀ x : ℝ, Real.exp ((halfParameter125 : ℝ) * Real.cos x) ≤ halfCosPoly125 x)
    (hcoeff : ∀ j : Fin 17, 0 ≤ halfCoeff125 j)
    (hvec : ∀ j : Fin 16, 0 < halfVector125 j)
    (hcert : ∀ i : Fin 16, (∑ j : Fin 16, halfTransfer125 i j * halfVector125 j) ≤
      halfRadius125 * halfVector125 i) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ L : ℕ,
      (∫ x : ℝ in 0..1, Real.exp ((halfParameter125 : ℝ) * ‖G L x‖)) ≤
        A * Real.exp ((Real.log (halfRadius125 : ℝ) + 0.0000000000001) * L) := by
  sorry

/-- P0026 pages 184 to 185, display 7.1 and Corollary 1.
The finite pressure data are discharged. CONDITIONAL ON the analytic norm moment transfer. -/
theorem pr_half_moment_certificate125 :
    ∃ t A b : ℝ, 0 < t ∧ 0 ≤ A ∧
      b < t * 0.7163435444776661 - (1 / 2) * Real.log 2 ∧
      ∀ L : ℕ, (∫ x : ℝ in 0..1, Real.exp (t * ‖G L x‖)) ≤
        A * Real.exp (b * L) := by
  obtain ⟨A, hA, hm⟩ := half_norm_moment_transfer125 half_exp_majorant125
    half_coeff_nonneg125 half_vector_pos125 half_perron_certificate125
  refine ⟨(halfParameter125 : ℝ), A,
    Real.log (halfRadius125 : ℝ) + 0.0000000000001, ?_, hA, ?_, hm⟩
  · exact_mod_cast half_parameter_box125.1
  · have hg := half_pressure_gap125
    linarith

/-- LEAF. P0026 page 184, exponential Markov inequality before display 7.1.
A uniform norm moment estimate bounds the large values measure. -/
theorem large_values_of_norm_moment125 {t A b lam : ℝ} (ht : 0 < t)
    (hm : ∀ L : ℕ, (∫ x : ℝ in 0..1, Real.exp (t * ‖G L x‖)) ≤
      A * Real.exp (b * L)) (N : ℕ) :
    (volume (bigSet N lam)).toReal ≤
      A * Real.exp (-(t * lam - b) * Lof N) := by
  let L := Lof N
  have hf : Continuous (fun x : ℝ => Real.exp (t * ‖G L x‖)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_G L).norm)
  have hmkv := mul_meas_ge_le_integral_of_nonneg
    (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
    (f := fun x : ℝ => Real.exp (t * ‖G L x‖))
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    hf.integrableOn_Icc (Real.exp (t * (lam * L)))
  have hset : {x : ℝ | Real.exp (t * (lam * L)) ≤ Real.exp (t * ‖G L x‖)} =
      {x : ℝ | lam * L ≤ ‖G L x‖} := by
    ext x
    simp only [Set.mem_ofPred_eq, Real.exp_le_exp, mul_le_mul_iff_right₀ ht]
  rw [hset, Measure.real, Measure.restrict_apply' measurableSet_Icc] at hmkv
  have hsub : bigSet N lam ⊆ {x : ℝ | lam * L ≤ ‖G L x‖} ∩ Set.Icc 0 1 :=
    fun x hx => ⟨hx.2.le, hx.1⟩
  have hfin : volume ({x : ℝ | lam * L ≤ ‖G L x‖} ∩ Set.Icc 0 1) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc])
      (measure_mono Set.inter_subset_right)
  have hmono := ENNReal.toReal_mono hfin (measure_mono hsub)
  have hprod := mul_le_mul_of_nonneg_left hmono (Real.exp_nonneg (t * (lam * L)))
  have hbound : Real.exp (t * (lam * L)) * (volume (bigSet N lam)).toReal ≤
      A * Real.exp (b * L) := by
    apply hprod.trans
    apply le_trans _ (hm L)
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc] using hmkv
  calc
    _ ≤ A * Real.exp (b * L) / Real.exp (t * (lam * L)) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hbound)
    _ = A * Real.exp (-(t * lam - b) * Lof N) := by
      rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [L]
      ring

/-- LEAF. P0026 pages 184 to 185, strict saving in display 7.1 absorbs L to power 100.
The generic version retains any natural logarithmic saving and the floor in Lof. -/
theorem powerLogBound_of_exp_decay125 {c lam C b : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hgap : c * Real.log 2 < b)
    (hvol : ∀ N : ℕ, 2 ≤ N → (volume (bigSet N lam)).toReal ≤
      C * Real.exp (-b * Lof N)) (k : ℕ) : PowerLogBound c lam k := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let δ := b - c * Real.log 2
  have hδ : 0 < δ := sub_pos.mpr hgap
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-δ * n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) δ hδ).comp
        tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp (ht.eventually_le_const (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (Lof_tendsto_atTop.eventually_ge_atTop M)
  refine ⟨C * Real.exp (c * Real.log 2), mul_nonneg hC (Real.exp_nonneg _), N0, ?_⟩
  intro N hN hN2
  have hL := hM (Lof N) (hN0 N hN)
  have hLp : (0 : ℝ) < Lof N := by exact_mod_cast (one_le_Lof hN2)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfloor : Real.log (N : ℝ) < ((Lof N : ℝ) + 1) * Real.log 2 :=
    (div_lt_iff₀ hl).mp (Nat.lt_floor_add_one (Real.log (N : ℝ) / Real.log 2))
  have he : Real.exp (-(c * Real.log 2) * Lof N) ≤
      Real.exp (c * Real.log 2) * (N : ℝ) ^ (-c) := by
    rw [Real.rpow_def_of_pos hNp, ← Real.exp_add, Real.exp_le_exp]
    have hh := mul_le_mul_of_nonneg_left hfloor.le hc
    nlinarith
  have hfactor : (Lof N : ℝ) ^ k * Real.exp (-b * Lof N) ≤
      Real.exp (-(c * Real.log 2) * Lof N) := by
    have heq : -b * (Lof N : ℝ) =
        -δ * Lof N + -(c * Real.log 2) * Lof N := by dsimp [δ]; ring
    rw [heq, Real.exp_add, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right hL (Real.exp_nonneg _)).trans_eq (one_mul _)
  rw [le_div_iff₀ (pow_pos hLp k)]
  calc
    _ ≤ (C * Real.exp (-b * Lof N)) * (Lof N : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right (hvol N hN2) (pow_nonneg hLp.le k)
    _ = C * ((Lof N : ℝ) ^ k * Real.exp (-b * Lof N)) := by ring
    _ ≤ C * Real.exp (-(c * Real.log 2) * Lof N) :=
      mul_le_mul_of_nonneg_left hfactor hC
    _ ≤ C * (Real.exp (c * Real.log 2) * (N : ℝ) ^ (-c)) :=
      mul_le_mul_of_nonneg_left he hC
    _ = _ := by ring

/-- Assembly of P0026 page 185 Corollary 1, exactly the existing cited Prop.
CONDITIONAL ON the open numerical moment certificate. -/
theorem pr_half_decomposed125 : PRHalfInput := by
  obtain ⟨t, A, b, ht, hA, hgap, hm⟩ := pr_half_moment_certificate125
  apply powerLogBound_of_exp_decay125 hA (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by linarith : (1 / 2 : ℝ) * Real.log 2 < t * 0.7163435444776661 - b)
  intro N _
  exact large_values_of_norm_moment125 ht hm N

/-- The exact sealed Platt and Trudgian half exponent conclusion.
CONDITIONAL ON half_norm_moment_transfer125 through the exact PRHalfInput assembly. -/
theorem pt_lambda_GRH_decomposed125 : LambdaOK (1 / 2) 0.7163436 :=
  pt_lambda_GRH_of_pr pr_half_decomposed125

set_option format.width 200

#print axioms half_norm_moment_transfer125
#print axioms pt_lambda_GRH_decomposed125
#print axioms pr_half_moment_certificate125
#print axioms large_values_of_norm_moment125
#print axioms powerLogBound_of_exp_decay125
#print axioms pr_half_decomposed125

end LeanLab.PlattTrudgian2014
