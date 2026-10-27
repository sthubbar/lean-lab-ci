import LeanLab.Ternary78.FiniteWeights

/-
AI wrote this Lean code. Binary Goldbach is open.
Elementary Euler product accounting for the Mellin weight Gamma of sigma plus iT.
Source for the Euler limit is Mathlib Complex.GammaSeq_tendsto_Gamma.
This supplies a weight hypothesis, not a numerical 0.985 certificate.
-/

namespace LeanLab.Ternary78.Bennett
open Real Complex Filter

/-- Each denominator factor in Euler's Gamma approximation grows with height. -/
theorem gamma_factor_norm_mono (σ : ℝ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (j : ℕ) :
    ‖(σ : ℂ) + (u : ℂ) * I + j‖ ≤ ‖(σ : ℂ) + (v : ℂ) * I + j‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.natCast_im]
  nlinarith

#print axioms gamma_factor_norm_mono

/-- Finite Euler approximations decrease with nonnegative height when sigma is positive. -/
theorem gammaSeq_norm_antitone {σ : ℝ} (hσ : 0 < σ) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (n : ℕ) :
    ‖Complex.GammaSeq ((σ : ℂ) + (v : ℂ) * I) n‖ ≤
      ‖Complex.GammaSeq ((σ : ℂ) + (u : ℂ) * I) n‖ := by
  have hden : 0 < ∏ j ∈ Finset.range (n + 1), ‖(σ : ℂ) + (u : ℂ) * I + j‖ := by
    apply Finset.prod_pos
    intro j _
    apply norm_pos_iff.mpr
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.zero_re] at hr
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    nlinarith
  have hprod : (∏ j ∈ Finset.range (n + 1), ‖(σ : ℂ) + (u : ℂ) * I + j‖) ≤
      ∏ j ∈ Finset.range (n + 1), ‖(σ : ℂ) + (v : ℂ) * I + j‖ := by
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => gamma_factor_norm_mono σ hu huv j)
  have hnumer : ‖(n : ℂ) ^ ((σ : ℂ) + (v : ℂ) * I)‖ =
      ‖(n : ℂ) ^ ((σ : ℂ) + (u : ℂ) * I)‖ := by
    rw [Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa using ne_of_gt hσ),
      Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa using ne_of_gt hσ)]
    simp
  simp only [Complex.GammaSeq, norm_div, norm_mul, norm_prod]
  rw [hnumer]
  exact div_le_div_of_nonneg_left (by positivity) hden hprod

#print axioms gammaSeq_norm_antitone

/-- The Gamma norm decreases on nonnegative heights, with no cited analytic input. -/
theorem gamma_norm_antitone {σ : ℝ} (hσ : 0 < σ) :
    AntitoneOn (fun T : ℝ => ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * I)‖) (Set.Ici 0) := by
  intro u hu v _ huv
  exact le_of_tendsto_of_tendsto'
    (Complex.GammaSeq_tendsto_Gamma ((σ : ℂ) + (v : ℂ) * I)).norm
    (Complex.GammaSeq_tendsto_Gamma ((σ : ℂ) + (u : ℂ) * I)).norm
    (fun n => gammaSeq_norm_antitone hσ hu huv n)

/-- Concrete positive sigma used by the existing 7/8 model. -/
example : AntitoneOn (fun T : ℝ => ‖Complex.Gamma ((7 / 8 : ℂ) + (T : ℂ) * I)‖)
    (Set.Ici 0) := by
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
    gamma_norm_antitone (by norm_num : (0 : ℝ) < 7 / 8)

#print axioms gamma_norm_antitone

/-- Replacing an ordinate by its absolute value leaves its Gamma norm unchanged. -/
theorem gamma_norm_abs (σ T : ℝ) :
    ‖Complex.Gamma ((σ : ℂ) + ((|T| : ℝ) : ℂ) * I)‖ =
      ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * I)‖ := by
  by_cases hT : 0 ≤ T
  · rw [abs_of_nonneg hT]
  · rw [abs_of_neg (lt_of_not_ge hT)]
    have he : (σ : ℂ) + ((-T : ℝ) : ℂ) * I =
        starRingEnd ℂ ((σ : ℂ) + (T : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [he, Complex.Gamma_conj]
    simp

#print axioms gamma_norm_abs

/-- CONDITIONAL ON BennettThm1_1 only as a cited analytic input.
This is the finite weighted zero sum with its actual Gamma weight. -/
theorem gamma_weighted_lower_of_bennett
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ} {Q q : ℕ} [NeZero q]
    (hB : BennettThm1_1 N Q) (hq : q ≤ Q) (hq1 : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ι : Type*} [DecidableEq ι] (z : Finset ι) (γ : ι → ℝ)
    {σ : ℝ} (hσ : 0 < σ) (t : ℕ → ℝ) (ht : Monotone t) (ht0 : ∀ i, 0 ≤ t i)
    (k : ℕ) (hcount : ∀ i, 0 < i → i ≤ k →
      N q χ (t i) = (heightSet z γ t i).card) :
    weightedCount (gridLower χ t)
        (fun i => ‖Complex.Gamma ((σ : ℂ) + (t i : ℂ) * I)‖) k ≤
      ∑ a ∈ heightSet z γ t k, ‖Complex.Gamma ((σ : ℂ) + (γ a : ℂ) * I)‖ := by
  calc weightedCount (gridLower χ t)
        (fun i => ‖Complex.Gamma ((σ : ℂ) + (t i : ℂ) * I)‖) k ≤
        ∑ a ∈ heightSet z γ t k, ‖Complex.Gamma ((σ : ℂ) + ((|γ a| : ℝ) : ℂ) * I)‖ :=
      height_weighted_lower_of_bennett hB hq hq1 χ hχ z γ t ht ht0
        (fun T => ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * I)‖)
        (gamma_norm_antitone hσ) (fun _ _ => norm_nonneg _) k hcount
    _ = ∑ a ∈ heightSet z γ t k, ‖Complex.Gamma ((σ : ℂ) + (γ a : ℂ) * I)‖ :=
      Finset.sum_congr rfl (fun a _ => gamma_norm_abs σ (γ a))

#print axioms gamma_weighted_lower_of_bennett

/-- CONDITIONAL ON BennettThm1_1. The extended nonnegative zero sum requires
no unproved summability input. The finite zero list represents the cutoff counts. -/
theorem gamma_tsum_lower_of_bennett
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ} {Q q : ℕ} [NeZero q]
    (hB : BennettThm1_1 N Q) (hq : q ≤ Q) (hq1 : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ι : Type*} [DecidableEq ι] (z : Finset ι) (γ : ι → ℝ)
    {σ : ℝ} (hσ : 0 < σ) (t : ℕ → ℝ) (ht : Monotone t) (ht0 : ∀ i, 0 ≤ t i)
    (k : ℕ) (hcount : ∀ i, 0 < i → i ≤ k →
      N q χ (t i) = (heightSet z γ t i).card) :
    ENNReal.ofReal (weightedCount (gridLower χ t)
        (fun i => ‖Complex.Gamma ((σ : ℂ) + (t i : ℂ) * I)‖) k) ≤
      ∑' a, ENNReal.ofReal ‖Complex.Gamma ((σ : ℂ) + (γ a : ℂ) * I)‖ := by
  classical
  have h := gamma_weighted_lower_of_bennett hB hq hq1 χ hχ z γ hσ t ht ht0 k hcount
  calc ENNReal.ofReal (weightedCount (gridLower χ t)
        (fun i => ‖Complex.Gamma ((σ : ℂ) + (t i : ℂ) * I)‖) k) ≤
        ENNReal.ofReal (∑ a ∈ heightSet z γ t k,
          ‖Complex.Gamma ((σ : ℂ) + (γ a : ℂ) * I)‖) := ENNReal.ofReal_le_ofReal h
    _ = ∑ a ∈ heightSet z γ t k,
        ENNReal.ofReal ‖Complex.Gamma ((σ : ℂ) + (γ a : ℂ) * I)‖ :=
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)
    _ ≤ ∑' a, ENNReal.ofReal ‖Complex.Gamma ((σ : ℂ) + (γ a : ℂ) * I)‖ :=
      ENNReal.sum_le_tsum _

#print axioms gamma_tsum_lower_of_bennett

/-- CONDITIONAL ON BennettThm1_1. A fixed integer grid at sigma 7/8 needs
no extra weight, zero enumeration or convergence hypothesis. -/
theorem gamma78_integer_grid_lower_of_bennett
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ} {Q q : ℕ} [NeZero q]
    (hB : BennettThm1_1 N Q) (hq : q ≤ Q) (hq1 : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (k : ℕ) :
    weightedCount (gridLower χ (fun i : ℕ => (i : ℝ)))
        (fun i => ‖Complex.Gamma (((7 / 8 : ℝ) : ℂ) + (i : ℂ) * I)‖) k ≤
      weightedCount (gridCount N χ (fun i : ℕ => (i : ℝ)))
        (fun i => ‖Complex.Gamma (((7 / 8 : ℝ) : ℂ) + (i : ℂ) * I)‖) k := by
  apply weightedCount_lower_of_bennett hB hq hq1 χ hχ
  · intro i
    have h := gamma_norm_antitone (by norm_num : (0 : ℝ) < 7 / 8)
      (show (i : ℝ) ∈ Set.Ici 0 from (show (0 : ℝ) ≤ i from Nat.cast_nonneg i))
      (show ((i + 1 : ℕ) : ℝ) ∈ Set.Ici 0 from
        (show (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) from Nat.cast_nonneg (i + 1)))
      (by exact_mod_cast Nat.le_succ i)
    simpa only [Complex.ofReal_natCast] using h
  · exact fun _ => norm_nonneg _

#print axioms gamma78_integer_grid_lower_of_bennett

end LeanLab.Ternary78.Bennett
