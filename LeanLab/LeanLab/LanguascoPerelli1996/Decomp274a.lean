import LeanLab.LanguascoPerelli1996.Decomp108

/-!
P0071 pages 354 and 355, the written proof of Lemma 2.
The variation estimate is split at Cauchy Schwarz and partial summation.
All existing declarations keep their statements and proof bodies.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Decomp274a
open Real MeasureTheory intervalIntegral

/-- Cauchy–Schwarz for the interval integral of a product of two nonnegative
continuous functions. -/
private theorem interval_mul_le_sqrt_mul_sqrt {a b : ℝ} (hab : a ≤ b) {F G : ℝ → ℝ}
    (hF : Continuous F) (hG : Continuous G) (hF0 : ∀ v, 0 ≤ F v) (hG0 : ∀ v, 0 ≤ G v) :
    (∫ v in a..b, F v * G v) ≤
      Real.sqrt (∫ v in a..b, F v ^ 2) * Real.sqrt (∫ v in a..b, G v ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  have hFint : Integrable (fun v : ℝ => F v ^ 2) (volume.restrict (Set.Ioc a b)) :=
    ((hF.pow 2).intervalIntegrable a b).1
  have hGint : Integrable (fun v : ℝ => G v ^ 2) (volume.restrict (Set.Ioc a b)) :=
    ((hG.pow 2).intervalIntegrable a b).1
  have hFmem : MemLp F (ENNReal.ofReal 2) (volume.restrict (Set.Ioc a b)) := by
    rw [show ENNReal.ofReal 2 = (2 : ENNReal) by norm_num]
    exact (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).2 hFint
  have hGmem : MemLp G (ENNReal.ofReal 2) (volume.restrict (Set.Ioc a b)) := by
    rw [show ENNReal.ofReal 2 = (2 : ENNReal) by norm_num]
    exact (memLp_two_iff_integrable_sq hG.aestronglyMeasurable).2 hGint
  have hlen := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Set.Ioc a b)) (p := 2) (q := 2) hpq
    (ae_of_all _ hF0) (ae_of_all _ hG0) hFmem hGmem
  have hconvF : (∫ v, F v ^ (2 : ℝ) ∂(volume.restrict (Set.Ioc a b))) =
      ∫ v, F v ^ 2 ∂(volume.restrict (Set.Ioc a b)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with v
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  have hconvG : (∫ v, G v ^ (2 : ℝ) ∂(volume.restrict (Set.Ioc a b))) =
      ∫ v, G v ^ 2 ∂(volume.restrict (Set.Ioc a b)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with v
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  rw [hconvF, hconvG] at hlen
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact hlen

/-- The band zero sum is a finite exponential sum in the variable `v`, where the
argument of the zero sum is `X * exp v`. -/
private theorem zSum_band_eq_expsum {X : ℝ} (hX : 0 < X) (U T : ℝ)
    (q : ℕ) [NeZero q] (a : ℕ) :
    ∃ (ι : Type) (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ),
      ∀ v : ℝ, zSum (X * Real.exp v) U T q a = ∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * v) := by
  classical
  refine ⟨_, Finset.univ.sigma (fun χ : DirichletCharacter ℂ q =>
      ((Zeros108.ntZeros_finite χ T).sdiff (t := {ρ : ℂ | |ρ.im| ≤ U})).toFinset),
    fun i => i.1 (a : ZMod q) * tau i.1⁻¹ * (mult i.1 i.2 : ℂ) *
      Complex.exp (Complex.I * (i.2.im : ℂ) * (Real.log X : ℂ)), fun i => i.2.im, ?_⟩
  intro v
  rw [Band108.zSum_eq_sum]
  simp only [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [Real.log_mul hX.ne' (Real.exp_pos v).ne', Real.log_exp, Complex.ofReal_add, mul_add,
    Complex.exp_add]
  ring

/-- Cauchy–Schwarz for the total variation of the squared norm of a finite
exponential sum on `[-1,1]`: the pointwise bound on the derivative of the squared
norm, then the interval Cauchy–Schwarz inequality. -/
private theorem expsum_variation_cauchy {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) :
    (∫ v in (-1 : ℝ)..1,
      |deriv (fun t : ℝ => ‖∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * t)‖ ^ 2) v|) ≤
      2 * Real.sqrt (∫ v in (-1 : ℝ)..1,
          ‖∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * v)‖ ^ 2) *
        Real.sqrt (∫ v in (-1 : ℝ)..1,
          ‖deriv (fun t : ℝ => ∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * t)) v‖ ^ 2) := by
  classical
  let f : ℝ → ℂ := fun v => ∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * v)
  let d : ℝ → ℂ := fun v => ∑ i ∈ s, c i * (Complex.exp (Complex.I * γ i * v) * (Complex.I * γ i))
  have hd (v : ℝ) : HasDerivAt f (d v) v := by
    have hbase : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) v := by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using! Complex.ofRealCLM.hasDerivAt
    have hi (i : ι) : HasDerivAt (fun t : ℝ => c i * Complex.exp (Complex.I * γ i * t))
        (c i * (Complex.exp (Complex.I * γ i * v) * (Complex.I * γ i))) v := by
      simpa only [mul_one] using ((hbase.const_mul (Complex.I * γ i)).cexp.const_mul (c i))
    exact HasDerivAt.fun_sum (u := s) (fun i _ => hi i)
  have hbase : Continuous (fun v : ℝ => (v : ℂ)) := Complex.ofRealCLM.continuous
  have hexp (i : ι) : Continuous (fun v : ℝ => Complex.exp (Complex.I * (γ i : ℂ) * (v : ℂ))) :=
    (continuous_const.mul hbase).cexp
  have hterm (i : ι) : Continuous (fun v : ℝ => c i * Complex.exp (Complex.I * (γ i : ℂ) * (v : ℂ))) :=
    continuous_const.mul (hexp i)
  have hfcont : Continuous f := by
    dsimp only [f]
    exact continuous_finsetSum s (fun i _ => hterm i)
  have hdcont : Continuous d := by
    dsimp only [d]
    exact continuous_finsetSum s (fun i _ =>
      continuous_const.mul ((hexp i).mul continuous_const))
  have hderivcont : Continuous (fun v => deriv (fun t : ℝ => ‖f t‖ ^ 2) v) := by
    have hfun : (fun v => deriv (fun t : ℝ => ‖f t‖ ^ 2) v) =
        (fun v => 2 * inner (𝕜 := ℝ) (f v) (d v)) := by
      funext v
      exact (hd v).norm_sq.deriv
    rw [hfun]
    exact continuous_const.mul (hfcont.inner hdcont)
  have hcont : Continuous (fun v => |deriv (fun t : ℝ => ‖f t‖ ^ 2) v|) := hderivcont.abs
  have hp (v : ℝ) : |deriv (fun t : ℝ => ‖f t‖ ^ 2) v| ≤ 2 * (‖f v‖ * ‖d v‖) := by
    have h1 : deriv (fun t : ℝ => ‖f t‖ ^ 2) v = 2 * inner (𝕜 := ℝ) (f v) (d v) :=
      (hd v).norm_sq.deriv
    have hh : |inner (𝕜 := ℝ) (f v) (d v)| ≤ ‖f v‖ * ‖d v‖ :=
      norm_inner_le_norm (𝕜 := ℝ) (f v) (d v)
    rw [h1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hh (by norm_num)
  have hmono : (∫ v in (-1 : ℝ)..1, |deriv (fun t : ℝ => ‖f t‖ ^ 2) v|) ≤
      ∫ v in (-1 : ℝ)..1, 2 * (‖f v‖ * ‖d v‖) :=
    integral_mono_on (μ := volume) (a := (-1 : ℝ)) (b := 1) (by norm_num)
      (hcont.intervalIntegrable _ _)
      ((continuous_const.mul (hfcont.norm.mul hdcont.norm)).intervalIntegrable _ _)
      (fun v _ => hp v)
  have hcs := interval_mul_le_sqrt_mul_sqrt (a := (-1 : ℝ)) (b := 1) (by norm_num)
    (F := fun v => ‖f v‖) (G := fun v => ‖d v‖) hfcont.norm hdcont.norm
    (fun v => norm_nonneg _) (fun v => norm_nonneg _)
  have hd_eq : (∫ v in (-1 : ℝ)..1, ‖d v‖ ^ 2) = ∫ v in (-1 : ℝ)..1, ‖deriv f v‖ ^ 2 := by
    have h : deriv f = d := by funext v; exact (hd v).deriv
    rw [h]
  have key : (∫ v in (-1 : ℝ)..1, |deriv (fun t : ℝ => ‖f t‖ ^ 2) v|) ≤
      2 * Real.sqrt (∫ v in (-1 : ℝ)..1, ‖f v‖ ^ 2) *
        Real.sqrt (∫ v in (-1 : ℝ)..1, ‖deriv f v‖ ^ 2) := by
    calc (∫ v in (-1 : ℝ)..1, |deriv (fun t : ℝ => ‖f t‖ ^ 2) v|)
        ≤ ∫ v in (-1 : ℝ)..1, 2 * (‖f v‖ * ‖d v‖) := hmono
      _ = 2 * (∫ v in (-1 : ℝ)..1, ‖f v‖ * ‖d v‖) := by
          rw [intervalIntegral.integral_const_mul]
      _ ≤ 2 * (Real.sqrt (∫ v in (-1 : ℝ)..1, ‖f v‖ ^ 2) *
            Real.sqrt (∫ v in (-1 : ℝ)..1, ‖d v‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hcs (by norm_num)
      _ = 2 * Real.sqrt (∫ v in (-1 : ℝ)..1, ‖f v‖ ^ 2) *
            Real.sqrt (∫ v in (-1 : ℝ)..1, ‖d v‖ ^ 2) := by ring
      _ = 2 * Real.sqrt (∫ v in (-1 : ℝ)..1, ‖f v‖ ^ 2) *
            Real.sqrt (∫ v in (-1 : ℝ)..1, ‖deriv f v‖ ^ 2) := by rw [hd_eq]
  have e1 : (fun t : ℝ => ‖∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * t)‖ ^ 2) =
      (fun t => ‖f t‖ ^ 2) := rfl
  have e2 : (fun v : ℝ => ‖∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * v)‖ ^ 2) =
      (fun v => ‖f v‖ ^ 2) := rfl
  have e3 : (fun t : ℝ => ∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * t)) = f := rfl
  rw [e1, e2, e3]
  exact key

/-- LEAF. Page 355, the Cauchy Schwarz display between displays 12 and 13.
Differentiation of the squared norm and Cauchy Schwarz bound variation
by twice the product of the two local L2 norms. The derivative includes
multiplication of each frequency by i, which preserves its norm. -/
theorem band_variation_cauchy_schwarz {X : ℝ} (hX : 0 < X) (U T : ℝ)
    (q : ℕ) [NeZero q] (a : ℕ) :
    (∫ v in (-1 : ℝ)..1, |deriv (Decomp108.energy X U T q a) v|) ≤
      2 * Real.sqrt (∫ v in (-1 : ℝ)..1, ‖zSum (X * Real.exp v) U T q a‖ ^ 2) *
        Real.sqrt (∫ v in (-1 : ℝ)..1,
          ‖deriv (fun t : ℝ => zSum (X * Real.exp t) U T q a) v‖ ^ 2) := by
  obtain ⟨ι, s, c, γ, hsum⟩ := zSum_band_eq_expsum hX U T q a
  have hval : (fun v : ℝ => ‖zSum (X * Real.exp v) U T q a‖ ^ 2) =
      fun v : ℝ => ‖∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * v)‖ ^ 2 := by
    funext v
    rw [hsum v]
  have hfun : (fun t : ℝ => zSum (X * Real.exp t) U T q a) =
      fun t : ℝ => ∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * t) := funext hsum
  change (∫ v in (-1 : ℝ)..1,
      |deriv (fun t : ℝ => ‖zSum (X * Real.exp t) U T q a‖ ^ 2) v|) ≤
    2 * Real.sqrt (∫ v in (-1 : ℝ)..1, ‖zSum (X * Real.exp v) U T q a‖ ^ 2) *
      Real.sqrt (∫ v in (-1 : ℝ)..1,
        ‖deriv (fun t : ℝ => zSum (X * Real.exp t) U T q a) v‖ ^ 2)
  rw [hval, hfun]
  exact expsum_variation_cauchy s c γ

/-- LEAF. Page 355, partial summation in the deduction of display 13.
The differentiated band sum has local squared L2 norm bounded by an
absolute constant times T squared times the uniform correlation bound.
This isolates the frequency weighted factor of the Cauchy Schwarz display.
The undifferentiated factor is already bounded by Mass108.band_local_mass. -/
theorem band_derivative_mass :
    GRH → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 < X → ∀ U T : ℝ, 0 ≤ U → U < T → 1 ≤ T →
      ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q → ∀ M : ℝ,
        (∀ u, U ≤ u → u ≤ T → ‖F X u q a‖ ≤ M) →
          (∫ v in (-1 : ℝ)..1,
            ‖deriv (fun t : ℝ => zSum (X * Real.exp t) U T q a) v‖ ^ 2) ≤
              C * T ^ 2 * M := by
  sorry

/-- Page 355 display 13, with exactly the statement of variation_control.
CONDITIONAL ON band_variation_cauchy_schwarz and band_derivative_mass. -/
theorem variation_control_decomposed :
    GRH → ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℝ, 0 < X → ∀ U T : ℝ, 0 ≤ U → U < T → 1 ≤ T →
      ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q → ∀ M : ℝ,
        (∀ u, U ≤ u → u ≤ T → ‖F X u q a‖ ≤ M) →
          (∫ v in (-1 : ℝ)..1, |deriv (Decomp108.energy X U T q a) v|) ≤ B * T * M := by
  intro hGRH
  obtain ⟨C, hC, hd⟩ := band_derivative_mass hGRH
  refine ⟨4 * Real.exp 2 + C, by positivity, ?_⟩
  intro X hX U T hU hUT hT q inst a ha M hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM U le_rfl hUT.le)
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hm : (∫ v in (-1 : ℝ)..1, ‖zSum (X * Real.exp v) U T q a‖ ^ 2) ≤
      (4 * Real.exp 2) * M := by
    have hb := Mass108.band_local_mass hX U T hUT.le q a
    have he := Real.exp_pos (2 : ℝ)
    have hu := hM U le_rfl hUT.le
    have ht := hM T hUT.le le_rfl
    nlinarith
  have hd' := hd X hX U T hU hUT hT q a ha M hM
  have hs : Real.sqrt (C * T ^ 2 * M) = T * Real.sqrt (C * M) := by
    rw [show C * T ^ 2 * M = T ^ 2 * (C * M) by ring,
      Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT0]
  have hy : 2 * Real.sqrt ((4 * Real.exp 2) * M) * Real.sqrt (C * M) ≤
      (4 * Real.exp 2) * M + C * M := by
    nlinarith [sq_nonneg (Real.sqrt ((4 * Real.exp 2) * M) - Real.sqrt (C * M)),
      Real.sq_sqrt (show 0 ≤ (4 * Real.exp 2) * M by positivity),
      Real.sq_sqrt (mul_nonneg hC hM0)]
  calc
    _ ≤ 2 * Real.sqrt (∫ v in (-1 : ℝ)..1, ‖zSum (X * Real.exp v) U T q a‖ ^ 2) *
        Real.sqrt (∫ v in (-1 : ℝ)..1,
          ‖deriv (fun t : ℝ => zSum (X * Real.exp t) U T q a) v‖ ^ 2) :=
      band_variation_cauchy_schwarz hX U T q a
    _ ≤ 2 * Real.sqrt ((4 * Real.exp 2) * M) * Real.sqrt (C * T ^ 2 * M) := by
      gcongr
    _ = T * (2 * Real.sqrt ((4 * Real.exp 2) * M) * Real.sqrt (C * M)) := by
      rw [hs]; ring
    _ ≤ T * ((4 * Real.exp 2) * M + C * M) := mul_le_mul_of_nonneg_left hy hT0
    _ = (4 * Real.exp 2 + C) * T * M := by ring


end LeanLab.LanguascoPerelli1996.Decomp274a

#print axioms LeanLab.LanguascoPerelli1996.Decomp274a.band_variation_cauchy_schwarz
#print axioms LeanLab.LanguascoPerelli1996.Decomp274a.band_derivative_mass
#print axioms LeanLab.LanguascoPerelli1996.Decomp274a.variation_control_decomposed
