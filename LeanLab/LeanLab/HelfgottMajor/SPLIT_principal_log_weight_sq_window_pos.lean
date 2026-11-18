import LeanLab.HelfgottMajor.SPLIT_principal_log_weight_sq_long

/-!
Splitting the positive window square energy `principal_log_weight_sq_window_pos`, the bound
`∫ t in (2, 5], ‖principalLogWeight t‖ ^ 2 ≤ 75` on the window next to the cut at height two.

The window is cut at height seven halves.  On each of the two halves the squared weight is
dominated pointwise by the same rational majorant, the squared logarithm of `t` plus seven
divided by the squared size of the contour parameter, and the majorant is then integrated on each
half with an explicit allowance.  The two allowances add up to seventy five.

The pointwise domination is the only analytic input of the window and is kept as its own step: it
is a bound for the logarithmic derivative of the zeta function on the left line, not an integral
estimate, and it does not depend on the length of the window.  The two integral estimates are the
calculus steps, one on each half of the window.

Each step below is a single inequality.  No prime sum, no zero sum and no scale appears in any of
them.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
open Real MeasureTheory Contour457
open Complex Filter Topology
open scoped Real

/-- `Every` complex number which is not a nonpositive even integer has `Γ_ℝ ≠ 0`. -/
private theorem GammaR_ne_zero_of_ne {z : ℂ} (hz : ∀ m : ℕ, z ≠ -(2 * m : ℕ)) :
    Complex.Gammaℝ z ≠ 0 := by
  intro hzero
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hzero
  refine hz n ?_
  push_cast at hn ⊢
  exact hn

/-- `Differentiability of Γ_ℝ` away from the nonpositive even integers. -/
private theorem differentiableAt_GammaR {z : ℂ} (hz : ∀ m : ℕ, z ≠ -(2 * m : ℕ)) :
    DifferentiableAt ℂ Complex.Gammaℝ z := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz2 : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
    intro m h
    apply hz m
    have h2 : z = -(2 * (m : ℂ)) := by linear_combination 2 * h
    rw [h2]; push_cast; ring
  have hc : DifferentiableAt ℂ (fun w : ℂ => (π : ℂ) ^ (-w / 2)) z := by
    have hlin : HasDerivAt (fun w : ℂ => -w / 2) (-(1 / 2)) z := by
      have h := (hasDerivAt_id z).neg.div_const 2
      have h' : (-(1 : ℂ) / 2) = -(1 / 2) := by norm_num
      rw [h'] at h
      exact h
    exact (hlin.const_cpow (Or.inl hπ)).differentiableAt
  have hΓ : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) z := by
    have hlin : HasDerivAt (fun w : ℂ => w / 2) (1 / 2) z := by
      simpa using (hasDerivAt_id z).div_const 2
    exact (Complex.differentiableAt_Gamma (z / 2) hz2).comp z hlin.differentiableAt
  conv_lhs =>
    rw [show Complex.Gammaℝ = fun z => (π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) from
      funext Complex.Gammaℝ_def]
  exact hc.mul hΓ

/-- `logDeriv` of `π ^ (-z/2)` is `-(log π)/2`. -/
private theorem logDeriv_cpow_pi_neg_half (z : ℂ) :
    logDeriv (fun w : ℂ => (π : ℂ) ^ (-w / 2)) z = -(1 / 2) * Complex.log (π : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hlin : HasDerivAt (fun w : ℂ => -w / 2) (-(1 / 2)) z := by
    have h := (hasDerivAt_id z).neg.div_const 2
    have h' : (-(1 : ℂ) / 2) = -(1 / 2) := by norm_num
    rw [h'] at h
    exact h
  have hd := hlin.const_cpow (Or.inl hπ)
  have hne : (π : ℂ) ^ (-z / 2) ≠ 0 := by
    rw [Complex.cpow_def, if_neg hπ]; exact Complex.exp_ne_zero _
  rw [logDeriv_apply, hd.deriv]
  field_simp

/-- `logDeriv` of `Γ_ℝ z = π ^ (-z/2) Γ (z/2)` is `-(log π)/2 + ψ(z/2)/2`. -/
private theorem logDeriv_GammaR {z : ℂ} (hz : ∀ m : ℕ, z ≠ -(2 * m : ℕ)) :
    logDeriv Complex.Gammaℝ z = -(1 / 2) * Complex.log (π : ℂ) + (1 / 2) * Complex.digamma (z / 2) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz2 : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
    intro m h
    apply hz m
    have h2 : z = -(2 * (m : ℂ)) := by linear_combination 2 * h
    rw [h2]; push_cast; ring
  have h1 : (π : ℂ) ^ (-z / 2) ≠ 0 := by
    rw [Complex.cpow_def, if_neg hπ]; exact Complex.exp_ne_zero _
  have h2 : Complex.Gamma (z / 2) ≠ 0 := Complex.Gamma_ne_zero hz2
  have hd1 : DifferentiableAt ℂ (fun w : ℂ => (π : ℂ) ^ (-w / 2)) z := by
    have hlin : HasDerivAt (fun w : ℂ => -w / 2) (-(1 / 2)) z := by
      have h := (hasDerivAt_id z).neg.div_const 2
      have h' : (-(1 : ℂ) / 2) = -(1 / 2) := by norm_num
      rw [h'] at h
      exact h
    exact (hlin.const_cpow (Or.inl hπ)).differentiableAt
  have hd2 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) z := by
    have hlin : HasDerivAt (fun w : ℂ => w / 2) (1 / 2) z := by
      simpa using (hasDerivAt_id z).div_const 2
    exact (Complex.differentiableAt_Gamma (z / 2) hz2).comp z hlin.differentiableAt
  have hG : logDeriv (fun w : ℂ => Complex.Gamma (w / 2)) z = (1 / 2) * Complex.digamma (z / 2) := by
    have hlin : HasDerivAt (fun w : ℂ => w / 2) (1 / 2) z := by
      simpa using (hasDerivAt_id z).div_const 2
    exact HasDerivAt.logDeriv_Gamma hlin hz2
  conv_lhs =>
    rw [show Complex.Gammaℝ = fun z => (π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) from
      funext Complex.Gammaℝ_def]
  rw [logDeriv_fun_mul z h1 h2 hd1 hd2, logDeriv_cpow_pi_neg_half, hG]

/-- The functional equation for `ζ'/ζ` in completed form:
`ζ'/ζ(s) = -ζ'/ζ(1-s) + log π - ψ(s/2)/2 - ψ((1-s)/2)/2`. -/
private theorem logDeriv_riemannZeta_completed {s : ℂ} (hs : ∀ n : ℤ, s ≠ n)
    (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s
      = -logDeriv riemannZeta (1 - s) + Complex.log (π : ℂ)
        - (1 / 2) * Complex.digamma (s / 2) - (1 / 2) * Complex.digamma ((1 - s) / 2) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hcompl : s ∈ (Set.range (Int.cast : ℤ → ℂ))ᶜ := by
    simpa [Set.mem_compl_iff, Set.mem_range, eq_comm] using hs
  -- the identity holds near `s`
  have hev : riemannZeta =ᶠ[𝓝 s]
      fun z => riemannZeta (1 - z) *
        (((fun w : ℂ => Complex.Gammaℝ (1 - w)) / Complex.Gammaℝ) z) := by
    filter_upwards [isClosed_range_intCast.isOpen_compl.mem_nhds hcompl] with z hz'
    rw [Set.mem_compl_iff, Set.mem_range, not_exists] at hz'
    have hz0 : z ≠ 0 := fun h => hz' 0 (by simp [h])
    have h1z0 : (1 : ℂ) - z ≠ 0 := by
      intro h
      exact hz' 1 (by push_cast at h ⊢; exact sub_eq_zero.mp h)
    have hnz : ∀ m : ℕ, z ≠ -(2 * m : ℕ) := by
      intro m h
      exact hz' (-(2 * (m : ℤ))) (by push_cast at h ⊢; exact h.symm)
    have hn1z : ∀ m : ℕ, (1 : ℂ) - z ≠ -(2 * m : ℕ) := by
      intro m h
      exact hz' (2 * (m : ℤ) + 1) (by push_cast at h ⊢; rw [show z = 2 * (m : ℂ) + 1 by linear_combination (norm := ring_nf) -h])
    have hGz : Complex.Gammaℝ z ≠ 0 := GammaR_ne_zero_of_ne hnz
    have hG1z : Complex.Gammaℝ ((1 : ℂ) - z) ≠ 0 := GammaR_ne_zero_of_ne hn1z
    rw [riemannZeta_def_of_ne_zero hz0, riemannZeta_def_of_ne_zero h1z0, completedRiemannZeta_one_sub]
    simp only [Pi.div_apply]
    field_simp
  rw [(logDeriv_congr_nhds hev).eq_of_nhds]
  have hpt := hev.self_of_nhds
  simp only at hpt
  -- nonvanishing and integer facts at `s`
  have hs0 : s ≠ 0 := fun h => hs 0 (by simp [h])
  have hsint : ∀ m : ℕ, s ≠ -(2 * m : ℕ) := by
    intro m h
    exact hs (-(2 * (m : ℤ))) (by push_cast at h ⊢; exact h)
  have hs1int : ∀ m : ℕ, (1 : ℂ) - s ≠ -(2 * m : ℕ) := by
    intro m h
    exact hs (2 * (m : ℤ) + 1) (by push_cast at h ⊢; rw [show s = 2 * (m : ℂ) + 1 by linear_combination (norm := ring_nf) -h])
  have hGs : Complex.Gammaℝ s ≠ 0 := GammaR_ne_zero_of_ne hsint
  have hG1s : Complex.Gammaℝ ((1 : ℂ) - s) ≠ 0 := GammaR_ne_zero_of_ne hs1int
  have hz1s : riemannZeta ((1 : ℂ) - s) ≠ 0 := by
    intro h
    refine hz ?_
    rw [hpt, h, zero_mul]
  have hdζ1 : DifferentiableAt ℂ riemannZeta ((1 : ℂ) - s) := by
    refine differentiableAt_riemannZeta ?_
    intro h
    exact hs 0 (by linear_combination -h)
  have hdΓs : DifferentiableAt ℂ Complex.Gammaℝ s := differentiableAt_GammaR hsint
  have hdΓ1s : DifferentiableAt ℂ Complex.Gammaℝ ((1 : ℂ) - s) := differentiableAt_GammaR hs1int
  have hderiv : deriv (fun z : ℂ => 1 - z) s = -1 := by
    rw [deriv_const_sub]
    simp
  have hdlin : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s := by fun_prop
  -- log derivative of `ζ (1 - ·)`
  have e1 : logDeriv (fun z : ℂ => riemannZeta (1 - z)) s = -logDeriv riemannZeta (1 - s) := by
    rw [logDeriv_fun_comp hdζ1 hdlin, hderiv]; ring
  -- log derivative of `Γ_ℝ (1 - ·)`
  have e2 : logDeriv (fun z : ℂ => Complex.Gammaℝ (1 - z)) s
      = -logDeriv Complex.Gammaℝ (1 - s) := by
    rw [logDeriv_fun_comp hdΓ1s hdlin, hderiv]; ring
  have hdF : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (1 - z)) s := hdζ1.comp s hdlin
  have hdA : DifferentiableAt ℂ (fun z : ℂ => Complex.Gammaℝ (1 - z)) s := hdΓ1s.comp s hdlin
  have hdB : DifferentiableAt ℂ Complex.Gammaℝ s := hdΓs
  have hGneq : (((fun w : ℂ => Complex.Gammaℝ (1 - w)) / Complex.Gammaℝ) s) ≠ 0 := by
    simp only [Pi.div_apply]
    exact div_ne_zero hG1s hGs
  have hdiv : logDeriv (fun i : ℂ => Complex.Gammaℝ (1 - i) / Complex.Gammaℝ i) s
      = -logDeriv Complex.Gammaℝ (1 - s) - logDeriv Complex.Gammaℝ s := by
    rw [logDeriv_fun_div s hG1s hGs hdA hdB, e2]
  have e3 : logDeriv (((fun w : ℂ => Complex.Gammaℝ (1 - w)) / Complex.Gammaℝ)) s
      = -logDeriv Complex.Gammaℝ (1 - s) - logDeriv Complex.Gammaℝ s := hdiv
  rw [logDeriv_fun_mul s hz1s hGneq hdF (hdA.div hdB hGs)]
  rw [e3, e1, logDeriv_GammaR hsint, logDeriv_GammaR hs1int]
  ring

private theorem log_three_le : Real.log 3 ≤ 1.1 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  calc (3 : ℝ) ≤ ∑ i ∈ Finset.range 10, (1.1 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp 1.1 := Real.sum_le_exp_of_nonneg (by norm_num) _

/-- `log 5 ≤ 1.61`. -/
private theorem log_five_le : Real.log 5 ≤ 1.61 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  calc (5 : ℝ) ≤ ∑ i ∈ Finset.range 11, (1.61 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp 1.61 := Real.sum_le_exp_of_nonneg (by norm_num) _

/-- `log 7 ≤ 1.95`. -/
private theorem log_seven_le : Real.log 7 ≤ 1.95 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  calc (7 : ℝ) ≤ ∑ i ∈ Finset.range 11, (1.95 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp 1.95 := Real.sum_le_exp_of_nonneg (by norm_num) _

/-- `log 8 ≤ 2.08`. -/
private theorem log_eight_le : Real.log 8 ≤ 2.08 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  calc (8 : ℝ) ≤ ∑ i ∈ Finset.range 11, (2.08 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp 2.08 := Real.sum_le_exp_of_nonneg (by norm_num) _

/-- The head of the von Mangoldt series: `Σ_{n < 8} Λ n / n^{3/2} ≤ 0.81`. -/
private theorem vonMangoldt_head_le :
    ∑ n ∈ Finset.range 8,
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ) ≤ 0.81 := by
  have h2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)] <;> norm_num
  have h3 : ArithmeticFunction.vonMangoldt 3 = Real.log 3 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)] <;> norm_num
  have h4 : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)] <;> norm_num
  have h5 : ArithmeticFunction.vonMangoldt 5 = Real.log 5 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)] <;> norm_num
  have h6 : ArithmeticFunction.vonMangoldt 6 = 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (by decide +kernel)] <;> norm_num
  have h7 : ArithmeticFunction.vonMangoldt 7 = Real.log 7 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)] <;> norm_num
  have h0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (by decide +kernel)]
  have h1 : ArithmeticFunction.vonMangoldt 1 = 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (by decide +kernel)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, h0, h1, h2, h3, h4, h5, h6, h7]
  have s2 := Real.log_two_lt_d9
  have s3 := log_three_le
  have s5 := log_five_le
  have s7 := log_seven_le
  have r2 : (2.8284 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add_of_nonneg (by norm_num)
      (by norm_num) (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have r3 : (5.1961 : ℝ) ≤ (3 : ℝ) ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add_of_nonneg (by norm_num)
      (by norm_num) (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have r4 : (8 : ℝ) ≤ (4 : ℝ) ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add_of_nonneg (by norm_num)
      (by norm_num) (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 4), Real.sqrt_nonneg 4]
  have r5 : (11.1803 : ℝ) ≤ (5 : ℝ) ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add_of_nonneg (by norm_num)
      (by norm_num) (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have r7 : (18.5202 : ℝ) ≤ (7 : ℝ) ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add_of_nonneg (by norm_num)
      (by norm_num) (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 7), Real.sqrt_nonneg 7]
  have p2 : (0 : ℝ) < (2 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have p3 : (0 : ℝ) < (3 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have p4 : (0 : ℝ) < (4 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have p5 : (0 : ℝ) < (5 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have p7 : (0 : ℝ) < (7 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have e2 : Real.log 2 / (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.246 := by
    rw [div_le_iff₀ p2]; nlinarith
  have e3 : Real.log 3 / (3 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.212 := by
    rw [div_le_iff₀ p3]; nlinarith
  have e4 : Real.log 2 / (4 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.087 := by
    rw [div_le_iff₀ p4]; nlinarith
  have e5 : Real.log 5 / (5 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.145 := by
    rw [div_le_iff₀ p5]; nlinarith
  have e7 : Real.log 7 / (7 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.106 := by
    rw [div_le_iff₀ p7]; nlinarith
  norm_num
  linarith

/-! ### Monotonicity and summability of `log x / x^{3/2}` -/

/-- Derivative of `log x · x^{-3/2}` on the positive axis. -/
private theorem hasDerivAt_log_mul_rpow (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.log y * y ^ (-(3 / 2 : ℝ)))
      (x ^ (-(5 / 2) : ℝ) * (1 - (3 / 2) * Real.log x)) x := by
  have hL : HasDerivAt (fun y : ℝ => Real.log y) x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hP : HasDerivAt (fun y : ℝ => y ^ (-(3 / 2 : ℝ)))
      ((-(3 / 2 : ℝ)) * x ^ ((-(3 / 2 : ℝ)) - 1)) x :=
    Real.hasDerivAt_rpow_const (p := (-(3 / 2 : ℝ))) (Or.inl hx.ne')
  have h := hL.mul hP
  have eexp : ((-(3 / 2 : ℝ)) - 1) = -(5 / 2 : ℝ) := by norm_num
  have e1 : x⁻¹ * x ^ (-(3 / 2) : ℝ) = x ^ (-(5 / 2) : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hx]
    norm_num
  rw [eexp] at h
  convert h using 1
  rw [e1]
  ring

/-- `log x · x^{-3/2}` is antitone on `[8, ∞)`. -/
private theorem antitoneOn_log_mul_rpow :
    AntitoneOn (fun x : ℝ => Real.log x * x ^ (-(3 / 2) : ℝ)) (Set.Ici 8) := by
  have hlog8 : (1 : ℝ) ≤ Real.log 8 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  refine antitoneOn_of_deriv_nonpos (convex_Ici 8) ?_ ?_ ?_
  · refine ContinuousOn.mul ?_ ?_
    · refine Real.continuousOn_log.mono ?_
      intro y hy
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have hy8 : (8 : ℝ) ≤ y := hy
      linarith
    · exact ContinuousOn.rpow_const continuousOn_id
        (fun y hy => Or.inl (by have hy8 : (8 : ℝ) ≤ y := hy; linarith))
  · intro y hy
    have hy8 : (8 : ℝ) < y := by
      rw [interior_Ici] at hy
      exact hy
    exact ((hasDerivAt_log_mul_rpow y (by linarith)).differentiableAt).differentiableWithinAt
  · intro y hy
    have hy8 : (8 : ℝ) < y := by
      rw [interior_Ici] at hy
      exact hy
    have hlogy : (1 : ℝ) ≤ Real.log y :=
      le_trans hlog8 (Real.log_le_log (by norm_num) (le_of_lt hy8))
    have hpos : (0 : ℝ) < y := by linarith
    have hp : (0 : ℝ) < y ^ (-(5 / 2) : ℝ) := Real.rpow_pos_of_pos hpos _
    rw [(hasDerivAt_log_mul_rpow y hpos).deriv]
    have hcoef : 1 - (3 / 2) * Real.log y ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hp) hcoef

/-- `log x / x^{3/2}` is antitone on `[8, ∞)`. -/
private theorem antitoneOn_log_div_rpow :
    AntitoneOn (fun x : ℝ => Real.log x / x ^ (3 / 2 : ℝ)) (Set.Ici 8) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) < x := by
    have : (8 : ℝ) ≤ x := hx
    linarith
  have hy0 : (0 : ℝ) < y := by
    have : (8 : ℝ) ≤ y := hy
    linarith
  show Real.log y / y ^ (3 / 2 : ℝ) ≤ Real.log x / x ^ (3 / 2 : ℝ)
  simp only [div_eq_mul_inv]
  rw [← Real.rpow_neg (le_of_lt hx0), ← Real.rpow_neg (le_of_lt hy0)]
  exact antitoneOn_log_mul_rpow hx hy hxy

/-- The logarithm series is summable. -/
private theorem summable_log_div_rpow :
    Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ (3 / 2 : ℝ)) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(5 / 4) : ℝ)) := by
    have h := (Real.summable_nat_rpow_inv (p := (5 / 4 : ℝ))).mpr (by norm_num)
    refine h.congr (fun n => ?_)
    rw [eq_comm, Real.rpow_neg (Nat.cast_nonneg n)]
  have hmaj : Summable (fun n : ℕ => 4 * (n : ℝ) ^ (-(5 / 4) : ℝ)) := hbase.mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have hn : (0:ℝ) < (n:ℝ) := by exact_mod_cast h
      positivity
  · rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have hn : (0:ℝ) < (n:ℝ) := by exact_mod_cast h
      have hlog : Real.log (n:ℝ) ≤ 4 * (n:ℝ) ^ (1/4:ℝ) := by
        have h1 := Real.log_le_rpow_div (le_of_lt hn) (by norm_num : (0:ℝ) < 1/4)
        have h2 : (n:ℝ) ^ (1/4:ℝ) / (1/4) = 4 * (n:ℝ) ^ (1/4:ℝ) := by ring
        rwa [h2] at h1
      have h3 : (n:ℝ) ^ (3/2:ℝ) = (n:ℝ) ^ (1/4:ℝ) * (n:ℝ) ^ (5/4:ℝ) := by
        rw [← Real.rpow_add hn]
        norm_num
      rw [h3]
      have hp1 : (0:ℝ) < (n:ℝ) ^ (1/4:ℝ) := Real.rpow_pos_of_pos hn _
      have hp2 : (0:ℝ) < (n:ℝ) ^ (5/4:ℝ) := Real.rpow_pos_of_pos hn _
      have h5 : 4 * (n:ℝ) ^ (1/4:ℝ) / ((n:ℝ) ^ (1/4:ℝ) * (n:ℝ) ^ (5/4:ℝ))
          = 4 * (n:ℝ) ^ (-(5/4):ℝ) := by
        rw [Real.rpow_neg (le_of_lt hn)]
        field_simp
      calc Real.log (n:ℝ) / ((n:ℝ) ^ (1/4:ℝ) * (n:ℝ) ^ (5/4:ℝ))
          ≤ 4 * (n:ℝ) ^ (1/4:ℝ) / ((n:ℝ) ^ (1/4:ℝ) * (n:ℝ) ^ (5/4:ℝ)) :=
            div_le_div_of_nonneg_right hlog (le_of_lt (mul_pos hp1 hp2))
        _ = 4 * (n:ℝ) ^ (-(5/4):ℝ) := h5

/-- `log 8 ≥ 2`. -/
private theorem log_eight_ge : (2 : ℝ) ≤ Real.log 8 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h1 := Real.exp_one_lt_d9
  have hpos : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  nlinarith

/-- `√8 ≥ 2.8284`. -/
private theorem sqrt_eight_ge : (2.8284 : ℝ) ≤ Real.sqrt 8 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

/-- `log x / x^{3/2}` is integrable on `(8, ∞)`. -/
private theorem integrableOn_log_div_rpow :
    IntegrableOn (fun x : ℝ => Real.log x / x ^ (3 / 2 : ℝ)) (Set.Ioi 8) := by
  have hsum8 : Summable (fun n : ℕ =>
      Real.log ((n + 8 : ℕ) : ℝ) / (((n + 8 : ℕ)) : ℝ) ^ (3 / 2 : ℝ)) :=
    (summable_nat_add_iff 8).mpr summable_log_div_rpow
  have hnn : ∀ t ∈ Set.Ioi (8 : ℝ), 0 ≤ Real.log t / t ^ (3 / 2 : ℝ) := by
    intro t ht
    have ht8 : (8 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hl : (0 : ℝ) < Real.log t := lt_of_lt_of_le (by linarith [log_eight_ge])
      (Real.log_le_log (by norm_num) (le_of_lt ht8))
    positivity
  exact antitoneOn_log_div_rpow.integrableOn_Ioi_of_summable_comp_add hsum8 hnn

/-- The improper integral `∫_8^∞ log x / x^{3/2} ≤ 2.9`. -/
private theorem integral_Ioi_log_div_rpow_le :
    ∫ x in Set.Ioi (8 : ℝ), Real.log x / x ^ (3 / 2 : ℝ) ≤ 2.9 := by
  have hA : ∀ x ∈ Set.Ici (8 : ℝ),
      HasDerivAt (fun y : ℝ => -(2 * Real.log y + 4) * y ^ (-(1 / 2) : ℝ))
        (Real.log x / x ^ (3 / 2 : ℝ)) x := by
    intro x hx
    have hx8 : (8 : ℝ) ≤ x := hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hL : HasDerivAt (fun y : ℝ => Real.log y) x⁻¹ x := Real.hasDerivAt_log hx0.ne'
    have hP : HasDerivAt (fun y : ℝ => y ^ (-(1 / 2) : ℝ))
        ((-(1 / 2 : ℝ)) * x ^ ((-(1 / 2 : ℝ)) - 1)) x :=
      Real.hasDerivAt_rpow_const (p := (-(1 / 2 : ℝ))) (Or.inl hx0.ne')
    have h2L : HasDerivAt (fun y : ℝ => 2 * Real.log y + 4) (2 * x⁻¹) x :=
      (hL.const_mul 2).add_const 4
    have h := h2L.neg.mul hP
    have eexp : ((-(1 / 2 : ℝ)) - 1) = -(3 / 2 : ℝ) := by norm_num
    have e1 : x⁻¹ * x ^ (-(1 / 2) : ℝ) = x ^ (-(3 / 2) : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hx0]
      norm_num
    rw [eexp] at h
    convert h using 1
    rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hx0), ← e1]
    simp only [Pi.neg_apply]
    ring
  have htend : Tendsto (fun y : ℝ => -(2 * Real.log y + 4) * y ^ (-(1 / 2) : ℝ))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => Real.log y / y ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
    have h2 : Tendsto (fun y : ℝ => y ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have hev : (fun y : ℝ => -(2 * Real.log y + 4) * y ^ (-(1 / 2) : ℝ))
        =ᶠ[atTop] fun y => (-2) * (Real.log y / y ^ (1 / 2 : ℝ)) - 4 * y ^ (-(1 / 2) : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      rw [Real.rpow_neg (le_of_lt hy)]
      field_simp
      ring
    rw [Filter.tendsto_congr' hev]
    simpa using (h1.const_mul (-2)).sub (h2.const_mul 4)
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hA integrableOn_log_div_rpow htend
  rw [hval]
  have e8 : (8 : ℝ) ^ (-(1 / 2) : ℝ) = (Real.sqrt 8)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
  rw [e8]
  have hlog8 := log_eight_le
  have hsq := sqrt_eight_ge
  have hpos : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.2 (by norm_num)
  rw [show (0 : ℝ) - (-(2 * Real.log 8 + 4) * (Real.sqrt 8)⁻¹)
      = (2 * Real.log 8 + 4) / Real.sqrt 8 by
    field_simp
    ring]
  rw [div_le_iff₀ hpos]
  nlinarith

/-- `0 ≤ log x / x^{3/2}` for `x > 8`. -/
private theorem nonneg_log_div_rpow {t : ℝ} (ht : t ∈ Set.Ioi (8 : ℝ)) :
    0 ≤ Real.log t / t ^ (3 / 2 : ℝ) := by
  have ht8 : (8 : ℝ) < t := ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hl : (0 : ℝ) < Real.log t :=
    lt_of_lt_of_le (by linarith [log_eight_ge]) (Real.log_le_log (by norm_num) (le_of_lt ht8))
  positivity

/-- The von Mangoldt series is summable. -/
private theorem summable_vonMangoldt_div_rpow :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ)) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) summable_log_div_rpow
  · positivity
  · exact div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (by positivity)

/-- `Σ_{n < 9} Λ n / n^{3/2} ≤ 0.841`. -/
private theorem vonMangoldt_head9_le :
    ∑ n ∈ Finset.range 9, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ) ≤ 0.841 := by
  have h8 : ArithmeticFunction.vonMangoldt 8 = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)] <;> norm_num
  rw [Finset.sum_range_succ, h8]
  have hb := vonMangoldt_head_le
  have p8 : (0 : ℝ) < (8 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have r8 : (22.627 : ℝ) ≤ (8 : ℝ) ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add_of_nonneg (by norm_num) (by norm_num) (by norm_num), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 8), Real.sqrt_nonneg 8]
  have e8 : Real.log 2 / (8 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.031 := by
    rw [div_le_iff₀ p8]
    nlinarith [Real.log_two_lt_d9]
  linarith

/-- `Σ' n, Λ n / n^{3/2} ≤ 4`. -/
private theorem vonMangoldt_tsum_le_four :
    ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
  set f : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ) with hf
  set g : ℕ → ℝ := fun n => Real.log n / (n : ℝ) ^ (3 / 2 : ℝ) with hg
  have hf0 : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    simp only [hf]
    positivity
  have hfg : ∀ n : ℕ, f n ≤ g n := by
    intro n
    simp only [hf, hg]
    exact div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (by positivity)
  have hsum_f : Summable f := by
    rw [hf, hg] at *
    exact summable_vonMangoldt_div_rpow
  have hsum_sf : Summable (fun n : ℕ => f (n + 9)) := (summable_nat_add_iff 9).mpr hsum_f
  have htail : ∑' n : ℕ, f (n + 9) ≤ 2.9 := by
    have hsum_sg : Summable (fun n : ℕ => g (n + 9)) := by
      rw [hg]; exact (summable_nat_add_iff 9).mpr summable_log_div_rpow
    have hstep : ∑' n : ℕ, f (n + 9) ≤ ∑' n : ℕ, g (n + 9) :=
      hsum_sf.tsum_le_tsum (fun n => hfg (n + 9)) hsum_sg
    have hint : ∑' n : ℕ, g (n + 9) ≤ ∫ x in Set.Ioi (8 : ℝ), Real.log x / x ^ (3 / 2 : ℝ) := by
      have hanti := antitoneOn_log_div_rpow.tsum_comp_add_le_integral 8
        integrableOn_log_div_rpow (fun t ht => nonneg_log_div_rpow ht)
      simpa [hg, Nat.add_assoc] using hanti
    linarith [hstep, hint, integral_Ioi_log_div_rpow_le]
  have hsplit := hsum_f.sum_add_tsum_nat_add 9
  have hhead := vonMangoldt_head9_le
  linarith [hsplit, hhead, htail]

/-- `‖ζ'/ζ(3/2 + iu)‖ ≤ 4`: the von Mangoldt series bound at `Re s = 3/2`. -/
private theorem logDeriv_three_half_le (u : ℝ) :
    ‖logDeriv riemannZeta ((3 / 2 : ℂ) + u * I)‖ ≤ 4 := by
  set s : ℂ := (3 / 2 : ℂ) + u * I with hs
  have hre : 1 < s.re := by rw [hs]; simp; norm_num
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hre
  have he : logDeriv riemannZeta s
      = -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    rw [hL, logDeriv_apply]
    ring
  have hn : ∀ n : ℕ,
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖
        = ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ) := by
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with hz
    · subst hz
      simp
    · rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      congr 1
      rw [hs]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero]
      norm_num
  have hsum_norm : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖) :=
    summable_vonMangoldt_div_rpow.congr (fun n => (hn n).symm)
  rw [he, norm_neg]
  calc ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖
      ≤ ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ :=
        norm_tsum_le_tsum_norm hsum_norm
    _ = ∑' n, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ) := tsum_congr hn
    _ ≤ 4 := vonMangoldt_tsum_le_four


/-! ### Nonvanishing and recurrence facts for the digamma function off the real axis -/

/-- A point with nonzero imaginary part is never a nonpositive integer. -/
private theorem ne_nat_neg_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) :
    ∀ m : ℕ, w ≠ -(m : ℂ) := by
  intro m hm
  apply hw
  have h := congrArg Complex.im hm
  simpa using h

/-- A point with nonzero imaginary part is not zero. -/
private theorem ne_zero_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) : w ≠ 0 := by
  intro h
  exact hw (by simp [h])

/-- A point on the vertical line `Re = c` with nonzero imaginary part is not an integer. -/
private theorem mem_integerComplement_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    z ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  exact hz (by rw [← hn]; simp)

/-! ### A digamma bound at general real part -/

/-- `Re ψ(a + iu) ≤ log ‖a + iu‖ + 1/(8(a-1))` for `a > 1` and `u ≠ 0`: the general
`a` version of the partial-fraction estimate for the digamma function. -/
private theorem digamma_re_le_shift (a u : ℝ) (ha : 1 < a) (hu : u ≠ 0) :
    (Complex.digamma ((a : ℂ) + u * I)).re ≤ Real.log ‖(a : ℂ) + u * I‖ + 1 / (8 * (a - 1)) := by
  let z : ℂ := ((a - 1 : ℝ) : ℂ) + u * I
  have hzim : z.im = u := by simp [z]
  have hz : z ∈ Complex.integerComplement := mem_integerComplement_of_im_ne_zero (by simp [hzim, hu])
  have hre : 0 < z.re := by simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero]; linarith
  have hw : z + 1 = (a : ℂ) + u * I := by simp only [z]; push_cast; ring
  have hl := (Complex.continuous_re.tendsto _).comp (DigammaBudget.tendsto_log_sub_sum hz hre)
  rw [hw] at hl
  apply le_of_tendsto hl
  apply Filter.Eventually.of_forall
  intro N
  have hb := DigammaBudget.log_norm_partial_sum_le a u ha N
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hp : 0 ≤ 1 / (8 * (a + (N : ℝ) - 1)) := by
    have : 0 < a + (N : ℝ) - 1 := by linarith
    positivity
  have he : (N : ℂ) + 1 + z = (((a + N : ℝ)) : ℂ) + u * I := by
    simp only [z]; push_cast; ring
  dsimp only [Function.comp_def]
  rw [he]
  simp only [Complex.sub_re, Complex.log_re]
  have hsum : (∑ n ∈ Finset.range N, 1 / (z + (n : ℂ) + 1)).re =
      ∑ n ∈ Finset.range N, ((a + (n : ℝ)) / ((a + (n : ℝ)) ^ 2 + u ^ 2)) := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [show z + (n : ℂ) + 1 = (((a + (n : ℝ)) : ℝ) : ℂ) + u * I by
      simp only [z]; push_cast; ring,
      one_div, DigammaBudget.inv_re_vertical]
  rw [hsum]
  linarith

/-- The digamma recurrence taken down from `11/4 + iy` to `-1/4 + iy`. -/
private theorem digamma_neg_quarter_shift (y : ℝ) (hy : y ≠ 0) :
    Complex.digamma ((-(1 / 4) : ℂ) + y * I)
      = Complex.digamma ((11 / 4 : ℂ) + y * I)
        - (((-(1 / 4) : ℂ) + y * I))⁻¹ - (((3 / 4 : ℂ) + y * I))⁻¹
        - (((7 / 4 : ℂ) + y * I))⁻¹ := by
  have him1 : ((-(1 / 4) : ℂ) + y * I).im = y := by simp
  have him2 : (((3 / 4) : ℂ) + y * I).im = y := by simp
  have him3 : (((7 / 4) : ℂ) + y * I).im = y := by simp
  have h1 := Complex.digamma_apply_add_one ((-(1 / 4) : ℂ) + y * I)
    (ne_nat_neg_of_im_ne_zero (by simp [him1, hy]))
  have e1 : (-(1 / 4) : ℂ) + y * I + 1 = (3 / 4 : ℂ) + y * I := by push_cast; ring
  rw [e1] at h1
  have h2 := Complex.digamma_apply_add_one ((3 / 4 : ℂ) + y * I)
    (ne_nat_neg_of_im_ne_zero (by simp [him2, hy]))
  have e2 : (3 / 4 : ℂ) + y * I + 1 = (7 / 4 : ℂ) + y * I := by push_cast; ring
  rw [e2] at h2
  have h3 := Complex.digamma_apply_add_one ((7 / 4 : ℂ) + y * I)
    (ne_nat_neg_of_im_ne_zero (by simp [him3, hy]))
  have e3 : (7 / 4 : ℂ) + y * I + 1 = (11 / 4 : ℂ) + y * I := by push_cast; ring
  rw [e3] at h3
  rw [h3, h2, h1]
  ring

/-- The digamma recurrence taken down from `15/4 - iy` to `3/4 - iy`. -/
private theorem digamma_three_quarter_shift (y : ℝ) (hy : y ≠ 0) :
    Complex.digamma ((3 / 4 : ℂ) - y * I)
      = Complex.digamma ((15 / 4 : ℂ) - y * I)
        - (((3 / 4 : ℂ) - y * I))⁻¹ - (((7 / 4 : ℂ) - y * I))⁻¹
        - (((11 / 4 : ℂ) - y * I))⁻¹ := by
  have him1 : (((3 / 4) : ℂ) - y * I).im = -y := by simp
  have him2 : (((7 / 4) : ℂ) - y * I).im = -y := by simp
  have him3 : (((11 / 4) : ℂ) - y * I).im = -y := by simp
  have hy' : -y ≠ 0 := by simpa using hy
  have h1 := Complex.digamma_apply_add_one (((3 / 4) : ℂ) - y * I)
    (ne_nat_neg_of_im_ne_zero (by simp [him1, hy']))
  have e1 : (3 / 4 : ℂ) - y * I + 1 = (7 / 4 : ℂ) - y * I := by push_cast; ring
  rw [e1] at h1
  have h2 := Complex.digamma_apply_add_one (((7 / 4) : ℂ) - y * I)
    (ne_nat_neg_of_im_ne_zero (by simp [him2, hy']))
  have e2 : (7 / 4 : ℂ) - y * I + 1 = (11 / 4 : ℂ) - y * I := by push_cast; ring
  rw [e2] at h2
  have h3 := Complex.digamma_apply_add_one (((11 / 4) : ℂ) - y * I)
    (ne_nat_neg_of_im_ne_zero (by simp [him3, hy']))
  have e3 : (11 / 4 : ℂ) - y * I + 1 = (15 / 4 : ℂ) - y * I := by push_cast; ring
  rw [e3] at h3
  rw [h3, h2, h1]
  ring

/-! ### The imaginary part of the digamma function off the real axis -/

/-- The imaginary part of the digamma partial-fraction series: for `z` in the integer
complement, `Im (ψ z + γ + 1/z) = Σ y / ((n + 1 + Re z)^2 + y^2)` with `y = Im z`. -/
private theorem digamma_im_hasSum {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    HasSum (fun n : ℕ => z.im / (((n : ℝ) + 1 + z.re) ^ 2 + z.im ^ 2))
      ((Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + z⁻¹).im) := by
  have hterm : ∀ n : ℕ, Complex.imCLM (1 / ((n : ℂ) + 1) - 1 / (z + (n : ℂ) + 1))
      = z.im / (((n : ℝ) + 1 + z.re) ^ 2 + z.im ^ 2) := by
    intro n
    have h1 : (((n : ℂ) + 1)⁻¹).im = 0 := by
      have e : ((n : ℂ) + 1)⁻¹ = (((n : ℝ) + 1)⁻¹ : ℂ) := by push_cast; rfl
      rw [e]
      simp
    have h2 : (z + (n : ℂ) + 1).im = z.im := by simp
    have h3 : (z + (n : ℂ) + 1).re = z.re + (n : ℝ) + 1 := by simp
    have h4 : ((z + (n : ℂ) + 1)⁻¹).im = -(z.im) / Complex.normSq (z + (n : ℂ) + 1) := by
      rw [Complex.inv_im, h2]
    have hns : Complex.normSq (z + (n : ℂ) + 1) = ((n : ℝ) + 1 + z.re) ^ 2 + z.im ^ 2 := by
      rw [Complex.normSq_apply, h3, h2]; ring
    simp only [Complex.imCLM_apply, Complex.sub_im, one_div, h1, h4, hns, zero_sub]
    ring
  have h := DigammaBudget.hasSum_digamma_series hz
  have hmap := h.map Complex.imCLM Complex.imCLM.continuous
  have hfun : (Complex.imCLM ∘ fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + (n : ℂ) + 1))
      = fun n : ℕ => z.im / (((n : ℝ) + 1 + z.re) ^ 2 + z.im ^ 2) := by
    funext n
    exact hterm n
  have hval : Complex.imCLM (z.digamma + (Real.eulerMascheroniConstant : ℂ) + 1 / z)
      = (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + z⁻¹).im := by
    simp [Complex.imCLM_apply, one_div]
  rw [hfun, hval] at hmap
  exact hmap

/-- The telescoping sum `Σ_{j<N} (1/(j+a) - 1/(j+a+1)) = 1/a - 1/(N+a)`. -/
private theorem sum_range_telescope (a : ℝ) (N : ℕ) (ha : 0 < a) :
    (∑ j ∈ Finset.range N, (1 / ((j : ℝ) + a) - 1 / ((j : ℝ) + a + 1)))
      = 1 / a - 1 / ((N : ℝ) + a) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : (0 : ℝ) < (N : ℝ) + a := by positivity
    have h2 : (0 : ℝ) < (N : ℝ) + a + 1 := by linarith
    have h3 : (0 : ℝ) < a := ha
    push_cast
    field_simp
    ring

/-- The imaginary part of `ψ` at `x + iy` for `x ≥ -1/4` and `y > 0`: the first three terms of
the series plus a telescoped tail. -/
private theorem digamma_im_tsum_le (x y : ℝ) (hy : 0 < y) (hx : -(1 / 4) ≤ x) :
    (∑' n : ℕ, y / (((n : ℝ) + 1 + x) ^ 2 + y ^ 2))
      ≤ (y / ((x + 1) ^ 2 + y ^ 2) + y / ((x + 2) ^ 2 + y ^ 2)
        + y / ((x + 3) ^ 2 + y ^ 2)) + y / (x + 7 / 2) := by
  let z : ℂ := (x : ℂ) + y * I
  have hzim : z.im = y := by simp [z]
  have hzre : z.re = x := by simp [z]
  have hz : z ∈ Complex.integerComplement :=
    mem_integerComplement_of_im_ne_zero (by simp [hzim, hy.ne'])
  have h := digamma_im_hasSum hz
  have hfdef : ∀ n : ℕ, z.im / (((n : ℝ) + 1 + z.re) ^ 2 + z.im ^ 2)
      = y / (((n : ℝ) + 1 + x) ^ 2 + y ^ 2) := by
    intro n; rw [hzim, hzre]
  have hEq : HasSum (fun n : ℕ => y / (((n : ℝ) + 1 + x) ^ 2 + y ^ 2))
      ((Complex.digamma z).im + (-z.im / Complex.normSq z)) := by
    have e : (fun n : ℕ => z.im / (((n : ℝ) + 1 + z.re) ^ 2 + z.im ^ 2))
        = fun n : ℕ => y / (((n : ℝ) + 1 + x) ^ 2 + y ^ 2) := funext hfdef
    rw [← e]
    have hz1 : (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + z⁻¹).im
        = (Complex.digamma z).im + (-z.im / Complex.normSq z) := by
      simp [Complex.add_im, Complex.inv_im]
    rw [← hz1]
    exact h
  have hf0 : ∀ n : ℕ, 0 ≤ y / (((n : ℝ) + 1 + x) ^ 2 + y ^ 2) := by
    intro n; positivity
  have hthree : (∑ n ∈ Finset.range 3, y / (((n : ℝ) + 1 + x) ^ 2 + y ^ 2))
      = y / ((x + 1) ^ 2 + y ^ 2) + y / ((x + 2) ^ 2 + y ^ 2)
        + y / ((x + 3) ^ 2 + y ^ 2) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    ring_nf
  have hterm : ∀ j : ℕ, y / (((((3 + j : ℕ)) : ℝ) + 1 + x) ^ 2 + y ^ 2)
      ≤ y * (1 / ((j : ℝ) + (x + 7 / 2)) - 1 / ((j : ℝ) + (x + 7 / 2) + 1)) := by
    intro j
    push_cast
    have e0 : (3 + ↑j + 1 + x : ℝ) = (↑j + 4 + x) := by ring
    rw [e0]
    have hu : (1 / 2 : ℝ) < (j : ℝ) + 4 + x := by
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hA : (0 : ℝ) < ((j : ℝ) + 4 + x) ^ 2 - 1 / 4 := by nlinarith
    have hB : (0 : ℝ) < ((j : ℝ) + 4 + x) ^ 2 + y ^ 2 := by positivity
    have e1 : (j : ℝ) + (x + 7 / 2) = ((j : ℝ) + 4 + x) - 1 / 2 := by ring
    have e2 : (j : ℝ) + (x + 7 / 2) + 1 = ((j : ℝ) + 4 + x) + 1 / 2 := by ring
    rw [e2, e1]
    have hk1 : ((j : ℝ) + 4 + x) - 1 / 2 ≠ 0 := by linarith
    have hk2 : ((j : ℝ) + 4 + x) + 1 / 2 ≠ 0 := by linarith
    have hkden : (((j : ℝ) + 4 + x) - 1 / 2) * (((j : ℝ) + 4 + x) + 1 / 2)
        = ((j : ℝ) + 4 + x) ^ 2 - 1 / 4 := by ring
    have hkey : 1 / (((j : ℝ) + 4 + x) - 1 / 2) - 1 / (((j : ℝ) + 4 + x) + 1 / 2)
        = 1 / (((j : ℝ) + 4 + x) ^ 2 - 1 / 4) := by
      rw [← hkden]
      rw [div_sub_div _ _ hk1 hk2]
      norm_num
    rw [hkey]
    have hgt : ((j : ℝ) + 4 + x) ^ 2 - 1 / 4 ≤ ((j : ℝ) + 4 + x) ^ 2 + y ^ 2 := by nlinarith
    calc y / (((j : ℝ) + 4 + x) ^ 2 + y ^ 2)
        ≤ y / (((j : ℝ) + 4 + x) ^ 2 - 1 / 4) := div_le_div_of_nonneg_left hy.le hA hgt
      _ = y * (1 / (((j : ℝ) + 4 + x) ^ 2 - 1 / 4)) := by ring
  have hbound : ∀ᶠ N : ℕ in Filter.atTop,
      (∑ n ∈ Finset.range N, y / (((n : ℝ) + 1 + x) ^ 2 + y ^ 2))
        ≤ (y / ((x + 1) ^ 2 + y ^ 2) + y / ((x + 2) ^ 2 + y ^ 2)
            + y / ((x + 3) ^ 2 + y ^ 2)) + y / (x + 7 / 2) := by
    apply Filter.Eventually.of_forall
    intro N
    rcases Nat.lt_or_ge N 3 with hN | hN
    · have hsub : (∑ n ∈ Finset.range N, y / (((n : ℝ) + 1 + x) ^ 2 + y ^ 2))
          ≤ ∑ n ∈ Finset.range 3, y / (((n : ℝ) + 1 + x) ^ 2 + y ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hN.le)
          (fun i _ _ => hf0 i)
      have hpos : 0 ≤ y / (x + 7 / 2) := by
        apply div_nonneg hy.le
        linarith
      rw [hthree] at hsub
      linarith
    · have hsplit := Finset.sum_range_add
          (fun n : ℕ => y / (((n : ℝ) + 1 + x) ^ 2 + y ^ 2)) 3 (N - 3)
      rw [show 3 + (N - 3) = N from by omega] at hsplit
      have htail : (∑ j ∈ Finset.range (N - 3),
            y / (((((3 + j : ℕ)) : ℝ) + 1 + x) ^ 2 + y ^ 2))
          ≤ ∑ j ∈ Finset.range (N - 3),
              y * (1 / ((j : ℝ) + (x + 7 / 2)) - 1 / ((j : ℝ) + (x + 7 / 2) + 1)) :=
        Finset.sum_le_sum (fun j _ => hterm j)
      have htele : (∑ j ∈ Finset.range (N - 3),
            y * (1 / ((j : ℝ) + (x + 7 / 2)) - 1 / ((j : ℝ) + (x + 7 / 2) + 1)))
          = y * (1 / (x + 7 / 2) - 1 / (((N - 3 : ℕ) : ℝ) + (x + 7 / 2))) := by
        rw [← Finset.mul_sum, sum_range_telescope (x + 7 / 2) (N - 3) (by linarith)]
      have hle : y * (1 / (x + 7 / 2) - 1 / (((N - 3 : ℕ) : ℝ) + (x + 7 / 2)))
          ≤ y / (x + 7 / 2) := by
        have hpos1 : (0 : ℝ) < x + 7 / 2 := by linarith
        have hpos2 : (0 : ℝ) < ((N - 3 : ℕ) : ℝ) + (x + 7 / 2) := by
          have h0 : (0 : ℝ) ≤ ((N - 3 : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
        have hinv : 0 ≤ 1 / (((N - 3 : ℕ) : ℝ) + (x + 7 / 2)) := by positivity
        have hsub : 1 / (x + 7 / 2) - 1 / (((N - 3 : ℕ) : ℝ) + (x + 7 / 2))
            ≤ 1 / (x + 7 / 2) := by linarith
        calc y * (1 / (x + 7 / 2) - 1 / (((N - 3 : ℕ) : ℝ) + (x + 7 / 2)))
            ≤ y * (1 / (x + 7 / 2)) := mul_le_mul_of_nonneg_left hsub hy.le
          _ = y / (x + 7 / 2) := by ring
      rw [hsplit, hthree]
      have hchain : (∑ j ∈ Finset.range (N - 3),
            y / (((((3 + j : ℕ)) : ℝ) + 1 + x) ^ 2 + y ^ 2))
          ≤ y * (1 / (x + 7 / 2) - 1 / (((N - 3 : ℕ) : ℝ) + (x + 7 / 2))) :=
        htele ▸ htail
      linarith [hchain, hle]
  have hC := le_of_tendsto hEq.tendsto_sum_nat hbound
  have hns : Complex.normSq z = x ^ 2 + y ^ 2 := by
    simp only [Complex.normSq_apply, hzre, hzim]; ring
  rw [hzim, hns] at hC
  rw [hEq.tsum_eq, hzim, hns]
  linarith

/-- The imaginary part of `ψ` as the series plus the contribution of `1/z`. -/
private theorem digamma_im_eq_tsum (x y : ℝ) (hy : y ≠ 0) :
    (Complex.digamma ((x : ℂ) + y * I)).im
      = (∑' n : ℕ, y / (((n : ℝ) + 1 + x) ^ 2 + y ^ 2)) + y / (x ^ 2 + y ^ 2) := by
  let z : ℂ := (x : ℂ) + y * I
  have hzim : z.im = y := by simp [z]
  have hzre : z.re = x := by simp [z]
  have hz : z ∈ Complex.integerComplement :=
    mem_integerComplement_of_im_ne_zero (by simp [hzim, hy])
  have h := digamma_im_hasSum hz
  have hfdef : ∀ n : ℕ, z.im / (((n : ℝ) + 1 + z.re) ^ 2 + z.im ^ 2)
      = y / (((n : ℝ) + 1 + x) ^ 2 + y ^ 2) := by
    intro n; rw [hzim, hzre]
  have htsum : (∑' n : ℕ, z.im / (((n : ℝ) + 1 + z.re) ^ 2 + z.im ^ 2))
      = ∑' n : ℕ, y / (((n : ℝ) + 1 + x) ^ 2 + y ^ 2) := tsum_congr hfdef
  have hv : (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + z⁻¹).im
      = (Complex.digamma z).im + (-z.im / Complex.normSq z) := by
    simp only [Complex.add_im, Complex.inv_im, Complex.ofReal_im, add_zero]
  have hns : Complex.normSq z = x ^ 2 + y ^ 2 := by
    simp only [Complex.normSq_apply, hzre, hzim]; ring
  have hkey : (∑' n : ℕ, z.im / (((n : ℝ) + 1 + z.re) ^ 2 + z.im ^ 2))
      = (Complex.digamma z).im - z.im / Complex.normSq z := by
    rw [h.tsum_eq, hv]; ring
  rw [htsum, hzim, hns] at hkey
  show (Complex.digamma z).im = (∑' n : ℕ, y / (((n : ℝ) + 1 + x) ^ 2 + y ^ 2)) + y / (x ^ 2 + y ^ 2)
  linarith

/-- The imaginary part at `x + iy` for `y > 0`, bounded by the first three terms of the
series and the telescoped tail. -/
private theorem digamma_im_le (x y : ℝ) (hy : 0 < y) (hx : -(1 / 4) ≤ x) :
    (Complex.digamma ((x : ℂ) + y * I)).im
      ≤ y / (x ^ 2 + y ^ 2) + (y / ((x + 1) ^ 2 + y ^ 2) + y / ((x + 2) ^ 2 + y ^ 2)
        + y / ((x + 3) ^ 2 + y ^ 2)) + y / (x + 7 / 2) := by
  rw [digamma_im_eq_tsum x y hy.ne']
  linarith [digamma_im_tsum_le x y hy hx]

/-- The series part at the conjugated point: the same bound with the sign reversed. -/
private theorem digamma_im_conj_ge (x y : ℝ) (hy : 0 < y) (hx : -(1 / 4) ≤ x) :
    - (y / (x ^ 2 + y ^ 2) + (y / ((x + 1) ^ 2 + y ^ 2) + y / ((x + 2) ^ 2 + y ^ 2)
        + y / ((x + 3) ^ 2 + y ^ 2)) + y / (x + 7 / 2))
      ≤ (Complex.digamma ((x : ℂ) - y * I)).im := by
  have h := digamma_im_eq_tsum x (-y) (by linarith)
  have hw : ((x : ℂ) + ((-y : ℝ) : ℂ) * I) = ((x : ℂ) - y * I) := by push_cast; ring
  rw [hw] at h
  have ht : (∑' n : ℕ, (-y) / (((n : ℝ) + 1 + x) ^ 2 + (-y) ^ 2))
      = -(∑' n : ℕ, y / (((n : ℝ) + 1 + x) ^ 2 + y ^ 2)) := by
    rw [← tsum_neg]
    exact tsum_congr (fun n => by ring)
  rw [ht] at h
  have hy2e : x ^ 2 + (-y) ^ 2 = x ^ 2 + y ^ 2 := by ring
  rw [hy2e] at h
  have he : -y / (x ^ 2 + y ^ 2) = -(y / (x ^ 2 + y ^ 2)) := by ring
  rw [he] at h
  linarith [digamma_im_tsum_le x y hy hx, h]

/-- The imaginary part at the conjugated point is nonpositive. -/
private theorem digamma_im_conj_nonpos (x y : ℝ) (hy : 0 < y) :
    (Complex.digamma ((x : ℂ) - y * I)).im ≤ 0 := by
  have h := digamma_im_eq_tsum x (-y) (by linarith)
  have hw : ((x : ℂ) + ((-y : ℝ) : ℂ) * I) = ((x : ℂ) - y * I) := by push_cast; ring
  rw [hw] at h
  have ht : (∑' n : ℕ, (-y) / (((n : ℝ) + 1 + x) ^ 2 + (-y) ^ 2))
      = -(∑' n : ℕ, y / (((n : ℝ) + 1 + x) ^ 2 + y ^ 2)) := by
    rw [← tsum_neg]
    exact tsum_congr (fun n => by ring)
  rw [ht] at h
  have hy2e : x ^ 2 + (-y) ^ 2 = x ^ 2 + y ^ 2 := by ring
  rw [hy2e] at h
  have he : -y / (x ^ 2 + y ^ 2) = -(y / (x ^ 2 + y ^ 2)) := by ring
  rw [he] at h
  have hnn : 0 ≤ (∑' n : ℕ, y / (((n : ℝ) + 1 + x) ^ 2 + y ^ 2)) :=
    tsum_nonneg (fun n => by positivity)
  have hy2 : 0 ≤ y / (x ^ 2 + y ^ 2) := by positivity
  linarith

/-! ### A lower bound for the real part of the digamma function -/

/-- The real part of the digamma partial-fraction series. -/
private theorem digamma_re_hasSum {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1)
        - ((n : ℝ) + 1 + z.re) / (((n : ℝ) + 1 + z.re) ^ 2 + z.im ^ 2))
      ((Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + z⁻¹).re) := by
  have hterm : ∀ n : ℕ, Complex.reCLM (1 / ((n : ℂ) + 1) - 1 / (z + (n : ℂ) + 1))
      = 1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + z.re) / (((n : ℝ) + 1 + z.re) ^ 2 + z.im ^ 2) := by
    intro n
    have h1 : (((n : ℂ) + 1)⁻¹).re = 1 / ((n : ℝ) + 1) := by
      rw [Complex.inv_re]
      have hns : Complex.normSq ((n : ℂ) + 1) = ((n : ℝ) + 1) ^ 2 := by
        rw [Complex.normSq_apply]; simp; ring
      have hre : ((n : ℂ) + 1).re = (n : ℝ) + 1 := by simp
      rw [hns, hre]
      field_simp
    have h2 : (z + (n : ℂ) + 1).im = z.im := by simp
    have h3 : (z + (n : ℂ) + 1).re = z.re + (n : ℝ) + 1 := by simp
    have h4 : ((z + (n : ℂ) + 1)⁻¹).re
        = (z.re + (n : ℝ) + 1) / Complex.normSq (z + (n : ℂ) + 1) := by
      rw [Complex.inv_re, h3]
    have hns : Complex.normSq (z + (n : ℂ) + 1) = ((n : ℝ) + 1 + z.re) ^ 2 + z.im ^ 2 := by
      rw [Complex.normSq_apply, h3, h2]; ring
    simp only [Complex.reCLM_apply, Complex.sub_re, one_div, h1, h4, hns]
    ring
  have h := DigammaBudget.hasSum_digamma_series hz
  have hmap := h.map Complex.reCLM Complex.reCLM.continuous
  have hfun : (Complex.reCLM ∘ fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + (n : ℂ) + 1))
      = fun n : ℕ => 1 / ((n : ℝ) + 1)
          - ((n : ℝ) + 1 + z.re) / (((n : ℝ) + 1 + z.re) ^ 2 + z.im ^ 2) := by
    funext n
    exact hterm n
  have hval : Complex.reCLM (z.digamma + (Real.eulerMascheroniConstant : ℂ) + 1 / z)
      = (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + z⁻¹).re := by
    simp [Complex.reCLM_apply, one_div]
  rw [hfun, hval] at hmap
  exact hmap

/-- A lower bound for the real part of `ψ` at `x + iy`: the terms of the partial-fraction
series have nonnegative real part, so only `-γ - Re(1/z)` survives. -/
private theorem digamma_re_ge (x y : ℝ) (hy : y ≠ 0) (hx : 0 ≤ x) :
    -Real.eulerMascheroniConstant - x / (x ^ 2 + y ^ 2)
      ≤ (Complex.digamma ((x : ℂ) + y * I)).re := by
  let z : ℂ := (x : ℂ) + y * I
  have hzim : z.im = y := by simp [z]
  have hzre : z.re = x := by simp [z]
  have hz : z ∈ Complex.integerComplement :=
    mem_integerComplement_of_im_ne_zero (by simp only [hzim]; exact hy)
  have h := digamma_re_hasSum hz
  have hterm : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + 1)
      - ((n : ℝ) + 1 + x) / (((n : ℝ) + 1 + x) ^ 2 + y ^ 2) := by
    intro n
    have hn1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have h2 : (0 : ℝ) < ((n : ℝ) + 1 + x) ^ 2 + y ^ 2 := by positivity
    have hu : (0 : ℝ) < (n : ℝ) + 1 + x := by linarith
    have hux : 0 ≤ ((n : ℝ) + 1 + x) * x := mul_nonneg (le_of_lt hu) hx
    have hkey : ((n : ℝ) + 1 + x) * ((n : ℝ) + 1) ≤ ((n : ℝ) + 1 + x) ^ 2 + y ^ 2 := by
      nlinarith [hux, sq_nonneg y]
    rw [sub_nonneg, div_le_div_iff₀ h2 h1]
    nlinarith [hkey]
  have hnn : 0 ≤ (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + z⁻¹).re := by
    refine h.nonneg ?_
    intro n
    rw [hzre, hzim]
    simpa using hterm n
  have hval : (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + z⁻¹).re
      = (Complex.digamma z).re + Real.eulerMascheroniConstant + x / (x ^ 2 + y ^ 2) := by
    have hns : Complex.normSq z = x ^ 2 + y ^ 2 := by
      simp only [Complex.normSq_apply, hzre, hzim]; ring
    simp only [Complex.add_re, Complex.inv_re, hns, hzre, Complex.ofReal_re]
  rw [hval] at hnn
  show -Real.eulerMascheroniConstant - x / (x ^ 2 + y ^ 2) ≤ (Complex.digamma z).re
  linarith

/-- The imaginary part of `ψ` off the real axis is nonnegative. -/
private theorem digamma_im_ge (x y : ℝ) (hy : 0 < y) :
    0 ≤ (Complex.digamma ((x : ℂ) + y * I)).im := by
  let z : ℂ := (x : ℂ) + y * I
  have hzim : z.im = y := by simp [z]
  have hzre : z.re = x := by simp [z]
  have hz : z ∈ Complex.integerComplement :=
    mem_integerComplement_of_im_ne_zero (by simp [hzim, hy.ne'])
  have h := digamma_im_hasSum hz
  have hnn : 0 ≤ (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + z⁻¹).im := by
    refine h.nonneg ?_
    intro n
    rw [hzim, hzre]
    positivity
  have hval : (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + z⁻¹).im
      = (Complex.digamma z).im + (-y / (x ^ 2 + y ^ 2)) := by
    have hns : Complex.normSq z = x ^ 2 + y ^ 2 := by
      simp only [Complex.normSq_apply, hzre, hzim]; ring
    simp only [Complex.add_im, Complex.inv_im, hns, hzim, Complex.ofReal_im, add_zero]
  rw [hval] at hnn
  have hpos : (0 : ℝ) < x ^ 2 + y ^ 2 := by positivity
  have hx2 : -y / (x ^ 2 + y ^ 2) ≤ 0 := by
    have hp1 : (0 : ℝ) ≤ y / (x ^ 2 + y ^ 2) := by positivity
    have he : -y / (x ^ 2 + y ^ 2) = -(y / (x ^ 2 + y ^ 2)) := by ring
    rw [he]; linarith
  show 0 ≤ (Complex.digamma z).im
  linarith [hnn, hx2]

/-- `Re ψ(-1/4 + iy) ≤ log(y + 11/4) + 1/14` minus the three explicit reciprocal terms. -/
private theorem digamma_re_neg_quarter_le (y : ℝ) (hy : 0 < y) :
    (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).re
      ≤ Real.log (y + 11 / 4) + 1 / 14
        - ((-(1 / 4)) / (1 / 16 + y ^ 2) + (3 / 4) / (9 / 16 + y ^ 2)
            + (7 / 4) / (49 / 16 + y ^ 2)) := by
  have hsh := digamma_neg_quarter_shift y hy.ne'
  have h1 : (Complex.digamma ((11 / 4 : ℂ) + y * I)).re
      ≤ Real.log ‖(11 / 4 : ℂ) + y * I‖ + 1 / 14 := by
    have h := digamma_re_le_shift (11 / 4) y (by norm_num) hy.ne'
    have hc : (1 : ℝ) / (8 * (11 / 4 - 1)) = 1 / 14 := by norm_num
    rw [hc] at h
    have e : ((11 / 4 : ℝ) : ℂ) + (y : ℂ) * I = (11 / 4 : ℂ) + y * I := by push_cast; ring
    rw [e] at h
    exact h
  have harg : ‖((11 / 4 : ℂ) + y * I)‖ ≤ y + 11 / 4 := by
    have hsq : ‖((11 / 4 : ℂ) + y * I)‖ ^ 2 = (11 / 4 : ℝ) ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    nlinarith [norm_nonneg ((11 / 4 : ℂ) + y * I), hy]
  have hpos : (0 : ℝ) < ‖((11 / 4 : ℂ) + y * I)‖ := by
    have h := Complex.re_le_norm ((11 / 4 : ℂ) + y * I)
    have h2 : ((11 / 4 : ℂ) + y * I).re = 11 / 4 := by simp
    rw [h2] at h; linarith
  have hlog : Real.log ‖((11 / 4 : ℂ) + y * I)‖ ≤ Real.log (y + 11 / 4) :=
    Real.log_le_log hpos harg
  have e1 : (((-(1 / 4) : ℂ) + y * I))⁻¹.re = (-(1 / 4)) / (1 / 16 + y ^ 2) := by
    have h := DigammaBudget.inv_re_vertical (-(1 / 4)) y
    have ea : (((-(1 / 4) : ℝ)) : ℂ) = (-(1 / 4) : ℂ) := by push_cast; norm_num
    rw [ea] at h
    rw [h]
    norm_num
  have e2 : ((((3 / 4 : ℂ)) + y * I))⁻¹.re = (3 / 4) / (9 / 16 + y ^ 2) := by
    have h := DigammaBudget.inv_re_vertical (3 / 4) y
    have ea : (((3 / 4 : ℝ)) : ℂ) = (3 / 4 : ℂ) := by push_cast; norm_num
    rw [ea] at h
    rw [h]
    norm_num
  have e3 : ((((7 / 4 : ℂ)) + y * I))⁻¹.re = (7 / 4) / (49 / 16 + y ^ 2) := by
    have h := DigammaBudget.inv_re_vertical (7 / 4) y
    have ea : (((7 / 4 : ℝ)) : ℂ) = (7 / 4 : ℂ) := by push_cast; norm_num
    rw [ea] at h
    rw [h]
    norm_num
  have hr := congrArg Complex.re hsh
  rw [Complex.sub_re, Complex.sub_re, Complex.sub_re] at hr
  linarith [hr, e1, e2, e3, h1, hlog]

/-- `Re ψ(3/4 - iy) ≤ log(y + 15/4) + 1/22` minus the three explicit reciprocal terms. -/
private theorem digamma_re_three_quarter_le (y : ℝ) (hy : 0 < y) :
    (Complex.digamma ((3 / 4 : ℂ) - y * I)).re
      ≤ Real.log (y + 15 / 4) + 1 / 22
        - ((3 / 4) / (9 / 16 + y ^ 2) + (7 / 4) / (49 / 16 + y ^ 2)
            + (11 / 4) / (121 / 16 + y ^ 2)) := by
  have hsh := digamma_three_quarter_shift y hy.ne'
  have h1 : (Complex.digamma ((15 / 4 : ℂ) - y * I)).re
      ≤ Real.log ‖(15 / 4 : ℂ) - y * I‖ + 1 / 22 := by
    have h := digamma_re_le_shift (15 / 4) (-y) (by norm_num) (by linarith)
    have hc : (1 : ℝ) / (8 * (15 / 4 - 1)) = 1 / 22 := by norm_num
    rw [hc] at h
    have e : ((15 / 4 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I = (15 / 4 : ℂ) - y * I := by
      push_cast; ring
    rw [e] at h
    exact h
  have harg : ‖((15 / 4 : ℂ) - y * I)‖ ≤ y + 15 / 4 := by
    have hsq : ‖((15 / 4 : ℂ) - y * I)‖ ^ 2 = (15 / 4 : ℝ) ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    nlinarith [norm_nonneg ((15 / 4 : ℂ) - y * I), hy]
  have hpos : (0 : ℝ) < ‖((15 / 4 : ℂ) - y * I)‖ := by
    have h := Complex.re_le_norm ((15 / 4 : ℂ) - y * I)
    have h2 : ((15 / 4 : ℂ) - y * I).re = 15 / 4 := by simp
    rw [h2] at h; linarith
  have hlog : Real.log ‖((15 / 4 : ℂ) - y * I)‖ ≤ Real.log (y + 15 / 4) :=
    Real.log_le_log hpos harg
  have e1 : ((((3 / 4 : ℂ)) - y * I))⁻¹.re = (3 / 4) / (9 / 16 + y ^ 2) := by
    have h := DigammaBudget.inv_re_vertical (3 / 4) (-y)
    have e : ((3 / 4 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I = (3 / 4 : ℂ) - y * I := by push_cast; ring
    rw [e] at h
    rw [h]
    norm_num
  have e2 : ((((7 / 4 : ℂ)) - y * I))⁻¹.re = (7 / 4) / (49 / 16 + y ^ 2) := by
    have h := DigammaBudget.inv_re_vertical (7 / 4) (-y)
    have e : ((7 / 4 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I = (7 / 4 : ℂ) - y * I := by push_cast; ring
    rw [e] at h
    rw [h]
    norm_num
  have e3 : ((((11 / 4 : ℂ)) - y * I))⁻¹.re = (11 / 4) / (121 / 16 + y ^ 2) := by
    have h := DigammaBudget.inv_re_vertical (11 / 4) (-y)
    have e : ((11 / 4 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I = (11 / 4 : ℂ) - y * I := by push_cast; ring
    rw [e] at h
    rw [h]
    norm_num
  have hr := congrArg Complex.re hsh
  rw [Complex.sub_re, Complex.sub_re, Complex.sub_re] at hr
  linarith [hr, e1, e2, e3, h1, hlog]

/-- The imaginary part bound at `-1/4 + iy`, with the series terms written out. -/
private theorem digamma_im_le_neg_quarter (y : ℝ) (hy : 0 < y) :
    (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).im
      ≤ y / (1 / 16 + y ^ 2) + (y / (9 / 16 + y ^ 2) + y / (49 / 16 + y ^ 2)
          + y / (121 / 16 + y ^ 2)) + y / (13 / 4) := by
  have h := digamma_im_le (-(1 / 4)) y hy (by norm_num)
  have ep : (((-(1 / 4) : ℝ)) : ℂ) + (y : ℂ) * I = (-(1 / 4) : ℂ) + y * I := by push_cast; ring
  rw [ep] at h
  convert h using 2 <;> norm_num

/-- The imaginary part bound at the conjugate point `3/4 - iy`, with the series terms written
out. -/
private theorem digamma_im_conj_ge_three_quarter (y : ℝ) (hy : 0 < y) :
    - (y / (9 / 16 + y ^ 2) + (y / (49 / 16 + y ^ 2) + y / (121 / 16 + y ^ 2)
        + y / (225 / 16 + y ^ 2)) + y / (17 / 4))
      ≤ (Complex.digamma ((3 / 4 : ℂ) - y * I)).im := by
  have h := digamma_im_conj_ge (3 / 4) y hy (by norm_num)
  have ep : (((3 / 4 : ℝ)) : ℂ) - (y : ℂ) * I = ((3 / 4 : ℂ) - y * I) := by push_cast; ring
  rw [ep] at h
  convert h using 2 <;> norm_num

/-- A norm bound for `ψ` from a two sided real part bound and an imaginary part bound. -/
private theorem digamma_norm_le {z : ℂ} {M Ig c : ℝ}
    (hre : |(Complex.digamma z).re| ≤ M) (him : |(Complex.digamma z).im| ≤ Ig)
    (hn : M ^ 2 + Ig ^ 2 ≤ c ^ 2) (hc : 0 ≤ c) :
    ‖Complex.digamma z‖ ≤ c := by
  have hsq : ‖Complex.digamma z‖ ^ 2 = (Complex.digamma z).re ^ 2 + (Complex.digamma z).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1 : (Complex.digamma z).re ^ 2 ≤ M ^ 2 := by
    have := abs_le.mp hre
    nlinarith
  have h2 : (Complex.digamma z).im ^ 2 ≤ Ig ^ 2 := by
    have := abs_le.mp him
    nlinarith
  have h3 : ‖Complex.digamma z‖ ^ 2 ≤ c ^ 2 := by rw [hsq]; linarith
  nlinarith [norm_nonneg (Complex.digamma z), hc]

/-! ### Rational bounds for the logarithms used on the window -/

/-- `log 4 ≤ 1.387`. -/
private theorem log_four_le : Real.log 4 ≤ 1.387 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  calc (4 : ℝ) ≤ ∑ i ∈ Finset.range 20, (1.387 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp 1.387 := Real.sum_le_exp_of_nonneg (by norm_num) _

/-- `log (17/4) ≤ 1.447`. -/
private theorem log_seventeen_quarter_le : Real.log (17 / 4) ≤ 1.447 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  calc (17 / 4 : ℝ) ≤ ∑ i ∈ Finset.range 20, (1.447 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp 1.447 := Real.sum_le_exp_of_nonneg (by norm_num) _

/-- `log (19/4) ≤ 1.559`. -/
private theorem log_nineteen_quarter_le : Real.log (19 / 4) ≤ 1.559 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  calc (19 / 4 : ℝ) ≤ ∑ i ∈ Finset.range 20, (1.559 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp 1.559 := Real.sum_le_exp_of_nonneg (by norm_num) _

/-- `log 5 ≤ 1.61` (window version). -/
private theorem window_log_five_le : Real.log 5 ≤ 1.61 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  calc (5 : ℝ) ≤ ∑ i ∈ Finset.range 20, (1.61 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp 1.61 := Real.sum_le_exp_of_nonneg (by norm_num) _

/-- `log (21/4) ≤ 1.659`. -/
private theorem log_twentyone_quarter_le : Real.log (21 / 4) ≤ 1.659 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  calc (21 / 4 : ℝ) ≤ ∑ i ∈ Finset.range 20, (1.659 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp 1.659 := Real.sum_le_exp_of_nonneg (by norm_num) _

/-- `log (23/4) ≤ 1.75`. -/
private theorem log_twentythree_quarter_le : Real.log (23 / 4) ≤ 1.75 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  calc (23 / 4 : ℝ) ≤ ∑ i ∈ Finset.range 20, (1.75 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp 1.75 := Real.sum_le_exp_of_nonneg (by norm_num) _

/-- `log (25/4) ≤ 1.833`. -/
private theorem log_twentyfive_quarter_le : Real.log (25 / 4) ≤ 1.833 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  calc (25 / 4 : ℝ) ≤ ∑ i ∈ Finset.range 20, (1.833 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp 1.833 := Real.sum_le_exp_of_nonneg (by norm_num) _

/-- `π ≤ 3.15`, hence `log π ≤ 1.15`. -/
private theorem log_pi_le : Real.log π ≤ 1.15 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  calc π ≤ 3.15 := le_of_lt Real.pi_lt_d2
    _ ≤ ∑ i ∈ Finset.range 20, (1.15 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp 1.15 := Real.sum_le_exp_of_nonneg (by norm_num) _

/-- A lower bound for `Re ψ` at `3/4 + iy`. -/
private theorem digamma_re_three_quarter_ge (y : ℝ) (hy : y ≠ 0) :
    -(2 / 3 : ℝ) - (3 / 4) / (9 / 16 + y ^ 2)
      ≤ (Complex.digamma ((3 / 4 : ℂ) + y * I)).re := by
  have h1 := digamma_re_ge (3 / 4) y hy (by norm_num)
  have hxe : ((3 / 4 : ℝ)) ^ 2 = 9 / 16 := by norm_num
  rw [hxe] at h1
  have e : ((3 / 4 : ℝ) : ℂ) + (y : ℂ) * I = (3 / 4 : ℂ) + y * I := by push_cast; ring
  rw [e] at h1
  have h2 := Real.eulerMascheroniConstant_lt_two_thirds
  linarith

/-- A lower bound for `Re ψ` at `-1/4 + iy`, from the bound at `3/4 + iy`. -/
private theorem digamma_re_neg_quarter_ge (y : ℝ) (hy : y ≠ 0) :
    -(2 / 3 : ℝ) - (3 / 4) / (9 / 16 + y ^ 2)
      ≤ (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).re := by
  have h1 : (Complex.digamma ((3 / 4 : ℂ) + y * I))
      = Complex.digamma ((-(1 / 4) : ℂ) + y * I) + ((-(1 / 4) : ℂ) + y * I)⁻¹ := by
    have h := Complex.digamma_apply_add_one ((-(1 / 4) : ℂ) + y * I)
      (ne_nat_neg_of_im_ne_zero (by simp [hy]))
    have e : (-(1 / 4) : ℂ) + y * I + 1 = (3 / 4 : ℂ) + y * I := by push_cast; ring
    rw [e] at h
    exact h
  have hneg : ((-(1 / 4) : ℂ) + y * I)⁻¹.re ≤ 0 := by
    have h := DigammaBudget.inv_re_vertical (-(1 / 4)) y
    have ea : (((-(1 / 4) : ℝ)) : ℂ) = (-(1 / 4) : ℂ) := by push_cast; norm_num
    rw [ea] at h
    rw [h]
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num)
      (by positivity : (0 : ℝ) ≤ ((-(1 / 4) : ℝ)) ^ 2 + y ^ 2)
  have h3 := digamma_re_three_quarter_ge y hy
  have hr : (Complex.digamma ((3 / 4 : ℂ) + y * I)).re
      = (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).re + ((-(1 / 4) : ℂ) + y * I)⁻¹.re := by
    rw [h1]
    simp
  rw [hr] at h3
  linarith


set_option maxHeartbeats 4000000 in
/-- LEAF. The pointwise domination on the window: for `2 < t ≤ 5` the logarithmic derivative of
the zeta function on the left line is at most `log t + 7`.  This is the analytic step, a bound
for the zeta logarithmic derivative at a single point rather than an integral over the window. -/
theorem principal_log_weight_sq_window_pos_pointwise :
    ∀ t ∈ Set.Ioc (2 : ℝ) 5,
      ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ Real.log t + 7 := by
  intro t ht
  obtain ⟨ht2, ht5⟩ := ht
  set y : ℝ := t / 2 with hy
  have hy1 : (1 : ℝ) < y := by simp only [hy]; linarith
  have hypos : (0 : ℝ) < y := by linarith
  have hy25 : y ≤ 5 / 2 := by simp only [hy]; linarith
  have ht2y : t = 2 * y := by simp only [hy]; ring
  have hs : ∀ n : ℤ, ((-1 / 2 : ℂ) + t * I) ≠ n := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp at hre
    have h2 : (2 : ℤ) * n = -1 := by
      have hh : (2 : ℝ) * (n : ℝ) = -1 := by rw [← hre]; norm_num
      exact_mod_cast hh
    omega
  have hzn : riemannZeta ((-1 / 2 : ℂ) + t * I) ≠ 0 := by
    have h := LeanLab.PNTPort.ZetaZeros.zeta_left_ne t
    have e : (((-1 / 2 : ℝ)) : ℂ) + t * I = (-1 / 2 : ℂ) + t * I := by push_cast; ring
    rwa [e] at h
  have hfe := logDeriv_riemannZeta_completed hs hzn
  have hlogpi : ‖Complex.log (π : ℂ)‖ ≤ 1.15 := by
    rw [show Complex.log (π : ℂ) = ((Real.log π : ℝ) : ℂ) by
      rw [← Complex.ofReal_log (le_of_lt Real.pi_pos)], Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    exact log_pi_le
  have hA : ‖logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I))‖ ≤ 4 := by
    have e : (1 - ((-1 / 2 : ℂ) + t * I)) = ((3 / 2 : ℂ) + (-t) * I) := by push_cast; ring
    rw [e]
    have h := logDeriv_three_half_le (-t)
    simp only [Complex.ofReal_neg] at h
    exact h
  have e1 : ((-1 / 2 : ℂ) + t * I) / 2 = (-(1 / 4) : ℂ) + y * I := by
    rw [ht2y]; push_cast; ring
  have e2 : (1 - ((-1 / 2 : ℂ) + t * I)) / 2 = ((3 / 4 : ℂ) - y * I) := by
    rw [ht2y]; push_cast; ring


  rcases le_or_gt y (5 / 4) with hcA | hcA

  · -- case 1: y ≤ 5 / 4

    have hyL : (1 : ℝ) ≤ y := le_of_lt hy1
    have hyC : y ≤ (5 / 4 : ℝ) := hcA
    have hRe1hi : (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).re ≤ (1.150 : ℝ) := by
      have h := digamma_re_neg_quarter_le y hypos
      have hl : Real.log (y + 11 / 4) ≤ 1.387 :=
        le_trans (Real.log_le_log (by linarith) (by linarith)) log_four_le
      have hA1 : (-(1 / 4) : ℝ) / (1 / 16 + (1 : ℝ) ^ 2) ≤ (-(1 / 4) : ℝ) / (1 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyL]
      have hA2 : (3 / 4 : ℝ) / (9 / 16 + (5 / 4 : ℝ) ^ 2) ≤ (3 / 4 : ℝ) / (9 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      have hA3 : (7 / 4 : ℝ) / (49 / 16 + (5 / 4 : ℝ) ^ 2) ≤ (7 / 4 : ℝ) / (49 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      linarith
    have hRe1lo : -(1.150 : ℝ) ≤ (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).re := by
      have h := digamma_re_neg_quarter_ge y hypos.ne'
      have hy2 : (1 : ℝ) ≤ y ^ 2 := by nlinarith
      have hq : (3 / 4 : ℝ) / (9 / 16 + y ^ 2) ≤ (29 / 60 : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hy2]
      linarith [h, hq]
    have hIm1hi : (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).im ≤ (2.434 : ℝ) := by
      have h := digamma_im_le_neg_quarter y hypos
      have ht1 : y / (1 / 16 + y ^ 2) ≤ (1 : ℝ) / (1 / 16 + (1 : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ y - 1)
          (by nlinarith : (1 / 16 : ℝ) - (1 : ℝ) * y ≤ 0)]
      have ht2 : y / (9 / 16 + y ^ 2) ≤ (1 : ℝ) / (9 / 16 + (1 : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ y - 1)
          (by nlinarith : (9 / 16 : ℝ) - (1 : ℝ) * y ≤ 0)]
      have ht3 : y / (49 / 16 + y ^ 2) ≤ 2 / 7 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 7 / 4)]
      have ht4 : y / (121 / 16 + y ^ 2) ≤ 2 / 11 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 11 / 4)]
      have ht5 : y / (13 / 4) ≤ (5 / 4 : ℝ) / (13 / 4) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      linarith
    have hIm1lo : -(2.434 : ℝ) ≤ (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).im := by
      have h := digamma_im_ge (-(1 / 4)) y hypos
      have e : (((-(1 / 4) : ℝ)) : ℂ) + (y : ℂ) * I = (-(1 / 4) : ℂ) + y * I := by push_cast; ring
      rw [e] at h
      linarith
    have hRe2hi : (Complex.digamma ((3 / 4 : ℂ) - y * I)).re ≤ (1.150 : ℝ) := by
      have h := digamma_re_three_quarter_le y hypos
      have hl : Real.log (y + 15 / 4) ≤ 1.61 :=
        le_trans (Real.log_le_log (by linarith) (by linarith)) window_log_five_le
      have hB1 : (3 / 4 : ℝ) / (9 / 16 + (5 / 4 : ℝ) ^ 2) ≤ (3 / 4 : ℝ) / (9 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      have hB2 : (7 / 4 : ℝ) / (49 / 16 + (5 / 4 : ℝ) ^ 2) ≤ (7 / 4 : ℝ) / (49 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      have hB3 : (11 / 4 : ℝ) / (121 / 16 + (5 / 4 : ℝ) ^ 2) ≤ (11 / 4 : ℝ) / (121 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      linarith
    have hRe2lo : -(1.150 : ℝ) ≤ (Complex.digamma ((3 / 4 : ℂ) - y * I)).re := by
      have h := digamma_re_three_quarter_ge (-y) (by linarith)
      have e : ((3 / 4 : ℂ) + ((-y : ℝ)) * I) = ((3 / 4 : ℂ) - y * I) := by push_cast; ring
      rw [e] at h
      have e2 : ((-y : ℝ)) ^ 2 = y ^ 2 := by ring
      rw [e2] at h
      have hy2 : (1 : ℝ) ≤ y ^ 2 := by nlinarith
      have hq : (3 / 4 : ℝ) / (9 / 16 + y ^ 2) ≤ (29 / 60 : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hy2]
      linarith [h, hq]
    have hIm2hi : (Complex.digamma ((3 / 4 : ℂ) - y * I)).im ≤ (1.535 : ℝ) := by
      have h := digamma_im_conj_nonpos (3 / 4) y hypos
      have e : (((3 / 4 : ℝ) : ℂ) - (y : ℂ) * I) = ((3 / 4 : ℂ) - y * I) := by push_cast; ring
      rw [e] at h
      linarith
    have hIm2lo : -(1.535 : ℝ) ≤ (Complex.digamma ((3 / 4 : ℂ) - y * I)).im := by
      have h := digamma_im_conj_ge_three_quarter y hypos
      have ht1 : y / (9 / 16 + y ^ 2) ≤ (1 : ℝ) / (9 / 16 + (1 : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ y - 1)
          (by nlinarith : (9 / 16 : ℝ) - (1 : ℝ) * y ≤ 0)]
      have ht2 : y / (49 / 16 + y ^ 2) ≤ 2 / 7 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 7 / 4)]
      have ht3 : y / (121 / 16 + y ^ 2) ≤ 2 / 11 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 11 / 4)]
      have ht4 : y / (225 / 16 + y ^ 2) ≤ 2 / 15 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 15 / 4)]
      have ht5 : y / (17 / 4) ≤ (5 / 4 : ℝ) / (17 / 4) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      linarith
    have hc1 : ‖Complex.digamma ((-(1 / 4) : ℂ) + y * I)‖ ≤ (2.694 : ℝ) := by
      refine digamma_norm_le (M := 1.150) (Ig := 2.434) (c := 2.694) ?_ ?_ (by norm_num) (by norm_num)
      · rw [abs_le]; exact ⟨hRe1lo, hRe1hi⟩
      · rw [abs_le]; exact ⟨hIm1lo, hIm1hi⟩
    have hc2 : ‖Complex.digamma ((3 / 4 : ℂ) - y * I)‖ ≤ (1.920 : ℝ) := by
      refine digamma_norm_le (M := 1.150) (Ig := 1.535) (c := 1.920) ?_ ?_ (by norm_num) (by norm_num)
      · rw [abs_le]; exact ⟨hRe2lo, hRe2hi⟩
      · rw [abs_le]; exact ⟨hIm2lo, hIm2hi⟩
    have hL0 : (0.688 : ℝ) ≤ Real.log t := by
      rw [ht2y]
      have h2 : Real.log 2 ≤ Real.log (2 * y) :=
        Real.log_le_log (by norm_num) (by linarith)
      have h3 : (0.688 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      linarith
    have hnorm := hfe
    rw [e1, e2] at hnorm
    rw [hnorm]
    have hstep : ‖-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I)) + Complex.log (π : ℂ)
        - 1 / 2 * Complex.digamma ((-(1 / 4) : ℂ) + y * I)
        - 1 / 2 * Complex.digamma ((3 / 4 : ℂ) - y * I)‖
        ≤ ‖logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I))‖ + ‖Complex.log (π : ℂ)‖
          + ‖(1 / 2 : ℂ) * Complex.digamma ((-(1 / 4) : ℂ) + y * I)‖
          + ‖(1 / 2 : ℂ) * Complex.digamma ((3 / 4 : ℂ) - y * I)‖ := by
      have h4 := norm_sub_le
        (-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I)) + Complex.log (π : ℂ)
          - 1 / 2 * Complex.digamma ((-(1 / 4) : ℂ) + y * I))
        (1 / 2 * Complex.digamma ((3 / 4 : ℂ) - y * I))
      have h3 := norm_sub_le
        (-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I)) + Complex.log (π : ℂ))
        (1 / 2 * Complex.digamma ((-(1 / 4) : ℂ) + y * I))
      have h2 := norm_add_le (-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I)))
        (Complex.log (π : ℂ))
      have h2' : ‖-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I))‖
          = ‖logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I))‖ := norm_neg _
      linarith [h4, h3, h2, h2']
    refine le_trans hstep ?_
    have m1 : ‖(1 / 2 : ℂ) * Complex.digamma ((-(1 / 4) : ℂ) + y * I)‖
        = (1 / 2) * ‖Complex.digamma ((-(1 / 4) : ℂ) + y * I)‖ := by rw [norm_mul]; norm_num
    have m2 : ‖(1 / 2 : ℂ) * Complex.digamma ((3 / 4 : ℂ) - y * I)‖
        = (1 / 2) * ‖Complex.digamma ((3 / 4 : ℂ) - y * I)‖ := by rw [norm_mul]; norm_num
    rw [m1, m2]
    linarith [hc1, hc2, hA, hlogpi, hL0]

  rcases le_or_gt y (3 / 2) with hcB | hcB

  · -- case 2: y ≤ 3 / 2

    have hyL : (5 / 4 : ℝ) ≤ y := le_of_lt hcA
    have hyC : y ≤ (3 / 2 : ℝ) := hcB
    have hRe1hi : (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).re ≤ (1.150 : ℝ) := by
      have h := digamma_re_neg_quarter_le y hypos
      have hl : Real.log (y + 11 / 4) ≤ 1.447 :=
        le_trans (Real.log_le_log (by linarith) (by linarith)) log_seventeen_quarter_le
      have hA1 : (-(1 / 4) : ℝ) / (1 / 16 + (5 / 4 : ℝ) ^ 2) ≤ (-(1 / 4) : ℝ) / (1 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyL]
      have hA2 : (3 / 4 : ℝ) / (9 / 16 + (3 / 2 : ℝ) ^ 2) ≤ (3 / 4 : ℝ) / (9 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      have hA3 : (7 / 4 : ℝ) / (49 / 16 + (3 / 2 : ℝ) ^ 2) ≤ (7 / 4 : ℝ) / (49 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      linarith
    have hRe1lo : -(1.150 : ℝ) ≤ (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).re := by
      have h := digamma_re_neg_quarter_ge y hypos.ne'
      have hy2 : (1 : ℝ) ≤ y ^ 2 := by nlinarith
      have hq : (3 / 4 : ℝ) / (9 / 16 + y ^ 2) ≤ (29 / 60 : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hy2]
      linarith [h, hq]
    have hIm1hi : (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).im ≤ (2.287 : ℝ) := by
      have h := digamma_im_le_neg_quarter y hypos
      have ht1 : y / (1 / 16 + y ^ 2) ≤ (5 / 4 : ℝ) / (1 / 16 + (5 / 4 : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ y - 5 / 4)
          (by nlinarith : (1 / 16 : ℝ) - (5 / 4 : ℝ) * y ≤ 0)]
      have ht2 : y / (9 / 16 + y ^ 2) ≤ (5 / 4 : ℝ) / (9 / 16 + (5 / 4 : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ y - 5 / 4)
          (by nlinarith : (9 / 16 : ℝ) - (5 / 4 : ℝ) * y ≤ 0)]
      have ht3 : y / (49 / 16 + y ^ 2) ≤ 2 / 7 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 7 / 4)]
      have ht4 : y / (121 / 16 + y ^ 2) ≤ 2 / 11 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 11 / 4)]
      have ht5 : y / (13 / 4) ≤ (3 / 2 : ℝ) / (13 / 4) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      linarith
    have hIm1lo : -(2.287 : ℝ) ≤ (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).im := by
      have h := digamma_im_ge (-(1 / 4)) y hypos
      have e : (((-(1 / 4) : ℝ)) : ℂ) + (y : ℂ) * I = (-(1 / 4) : ℂ) + y * I := by push_cast; ring
      rw [e] at h
      linarith
    have hRe2hi : (Complex.digamma ((3 / 4 : ℂ) - y * I)).re ≤ (1.150 : ℝ) := by
      have h := digamma_re_three_quarter_le y hypos
      have hl : Real.log (y + 15 / 4) ≤ 1.659 :=
        le_trans (Real.log_le_log (by linarith) (by linarith)) log_twentyone_quarter_le
      have hB1 : (3 / 4 : ℝ) / (9 / 16 + (3 / 2 : ℝ) ^ 2) ≤ (3 / 4 : ℝ) / (9 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      have hB2 : (7 / 4 : ℝ) / (49 / 16 + (3 / 2 : ℝ) ^ 2) ≤ (7 / 4 : ℝ) / (49 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      have hB3 : (11 / 4 : ℝ) / (121 / 16 + (3 / 2 : ℝ) ^ 2) ≤ (11 / 4 : ℝ) / (121 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      linarith
    have hRe2lo : -(1.150 : ℝ) ≤ (Complex.digamma ((3 / 4 : ℂ) - y * I)).re := by
      have h := digamma_re_three_quarter_ge (-y) (by linarith)
      have e : ((3 / 4 : ℂ) + ((-y : ℝ)) * I) = ((3 / 4 : ℂ) - y * I) := by push_cast; ring
      rw [e] at h
      have e2 : ((-y : ℝ)) ^ 2 = y ^ 2 := by ring
      rw [e2] at h
      have hy2 : (1 : ℝ) ≤ y ^ 2 := by nlinarith
      have hq : (3 / 4 : ℝ) / (9 / 16 + y ^ 2) ≤ (29 / 60 : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hy2]
      linarith [h, hq]
    have hIm2hi : (Complex.digamma ((3 / 4 : ℂ) - y * I)).im ≤ (1.543 : ℝ) := by
      have h := digamma_im_conj_nonpos (3 / 4) y hypos
      have e : (((3 / 4 : ℝ) : ℂ) - (y : ℂ) * I) = ((3 / 4 : ℂ) - y * I) := by push_cast; ring
      rw [e] at h
      linarith
    have hIm2lo : -(1.543 : ℝ) ≤ (Complex.digamma ((3 / 4 : ℂ) - y * I)).im := by
      have h := digamma_im_conj_ge_three_quarter y hypos
      have ht1 : y / (9 / 16 + y ^ 2) ≤ (5 / 4 : ℝ) / (9 / 16 + (5 / 4 : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ y - 5 / 4)
          (by nlinarith : (9 / 16 : ℝ) - (5 / 4 : ℝ) * y ≤ 0)]
      have ht2 : y / (49 / 16 + y ^ 2) ≤ 2 / 7 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 7 / 4)]
      have ht3 : y / (121 / 16 + y ^ 2) ≤ 2 / 11 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 11 / 4)]
      have ht4 : y / (225 / 16 + y ^ 2) ≤ 2 / 15 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 15 / 4)]
      have ht5 : y / (17 / 4) ≤ (3 / 2 : ℝ) / (17 / 4) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      linarith
    have hc1 : ‖Complex.digamma ((-(1 / 4) : ℂ) + y * I)‖ ≤ (2.562 : ℝ) := by
      refine digamma_norm_le (M := 1.150) (Ig := 2.287) (c := 2.562) ?_ ?_ (by norm_num) (by norm_num)
      · rw [abs_le]; exact ⟨hRe1lo, hRe1hi⟩
      · rw [abs_le]; exact ⟨hIm1lo, hIm1hi⟩
    have hc2 : ‖Complex.digamma ((3 / 4 : ℂ) - y * I)‖ ≤ (1.926 : ℝ) := by
      refine digamma_norm_le (M := 1.150) (Ig := 1.543) (c := 1.926) ?_ ?_ (by norm_num) (by norm_num)
      · rw [abs_le]; exact ⟨hRe2lo, hRe2hi⟩
      · rw [abs_le]; exact ⟨hIm2lo, hIm2hi⟩
    have hL0 : (0.688 : ℝ) ≤ Real.log t := by
      rw [ht2y]
      have h2 : Real.log 2 ≤ Real.log (2 * y) :=
        Real.log_le_log (by norm_num) (by linarith)
      have h3 : (0.688 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      linarith
    have hnorm := hfe
    rw [e1, e2] at hnorm
    rw [hnorm]
    have hstep : ‖-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I)) + Complex.log (π : ℂ)
        - 1 / 2 * Complex.digamma ((-(1 / 4) : ℂ) + y * I)
        - 1 / 2 * Complex.digamma ((3 / 4 : ℂ) - y * I)‖
        ≤ ‖logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I))‖ + ‖Complex.log (π : ℂ)‖
          + ‖(1 / 2 : ℂ) * Complex.digamma ((-(1 / 4) : ℂ) + y * I)‖
          + ‖(1 / 2 : ℂ) * Complex.digamma ((3 / 4 : ℂ) - y * I)‖ := by
      have h4 := norm_sub_le
        (-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I)) + Complex.log (π : ℂ)
          - 1 / 2 * Complex.digamma ((-(1 / 4) : ℂ) + y * I))
        (1 / 2 * Complex.digamma ((3 / 4 : ℂ) - y * I))
      have h3 := norm_sub_le
        (-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I)) + Complex.log (π : ℂ))
        (1 / 2 * Complex.digamma ((-(1 / 4) : ℂ) + y * I))
      have h2 := norm_add_le (-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I)))
        (Complex.log (π : ℂ))
      have h2' : ‖-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I))‖
          = ‖logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I))‖ := norm_neg _
      linarith [h4, h3, h2, h2']
    refine le_trans hstep ?_
    have m1 : ‖(1 / 2 : ℂ) * Complex.digamma ((-(1 / 4) : ℂ) + y * I)‖
        = (1 / 2) * ‖Complex.digamma ((-(1 / 4) : ℂ) + y * I)‖ := by rw [norm_mul]; norm_num
    have m2 : ‖(1 / 2 : ℂ) * Complex.digamma ((3 / 4 : ℂ) - y * I)‖
        = (1 / 2) * ‖Complex.digamma ((3 / 4 : ℂ) - y * I)‖ := by rw [norm_mul]; norm_num
    rw [m1, m2]
    linarith [hc1, hc2, hA, hlogpi, hL0]

  rcases le_or_gt y (2) with hcC | hcC

  · -- case 3: y ≤ 2

    have hyL : (3 / 2 : ℝ) ≤ y := le_of_lt hcB
    have hyC : y ≤ (2 : ℝ) := hcC
    have hRe1hi : (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).re ≤ (1.327 : ℝ) := by
      have h := digamma_re_neg_quarter_le y hypos
      have hl : Real.log (y + 11 / 4) ≤ 1.559 :=
        le_trans (Real.log_le_log (by linarith) (by linarith)) log_nineteen_quarter_le
      have hA1 : (-(1 / 4) : ℝ) / (1 / 16 + (3 / 2 : ℝ) ^ 2) ≤ (-(1 / 4) : ℝ) / (1 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyL]
      have hA2 : (3 / 4 : ℝ) / (9 / 16 + (2 : ℝ) ^ 2) ≤ (3 / 4 : ℝ) / (9 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      have hA3 : (7 / 4 : ℝ) / (49 / 16 + (2 : ℝ) ^ 2) ≤ (7 / 4 : ℝ) / (49 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      linarith
    have hRe1lo : -(1.327 : ℝ) ≤ (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).re := by
      have h := digamma_re_neg_quarter_ge y hypos.ne'
      have hy2 : (1 : ℝ) ≤ y ^ 2 := by nlinarith
      have hq : (3 / 4 : ℝ) / (9 / 16 + y ^ 2) ≤ (29 / 60 : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hy2]
      linarith [h, hq]
    have hIm1hi : (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).im ≤ (2.265 : ℝ) := by
      have h := digamma_im_le_neg_quarter y hypos
      have ht1 : y / (1 / 16 + y ^ 2) ≤ (3 / 2 : ℝ) / (1 / 16 + (3 / 2 : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ y - 3 / 2)
          (by nlinarith : (1 / 16 : ℝ) - (3 / 2 : ℝ) * y ≤ 0)]
      have ht2 : y / (9 / 16 + y ^ 2) ≤ (3 / 2 : ℝ) / (9 / 16 + (3 / 2 : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ y - 3 / 2)
          (by nlinarith : (9 / 16 : ℝ) - (3 / 2 : ℝ) * y ≤ 0)]
      have ht3 : y / (49 / 16 + y ^ 2) ≤ 2 / 7 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 7 / 4)]
      have ht4 : y / (121 / 16 + y ^ 2) ≤ 2 / 11 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 11 / 4)]
      have ht5 : y / (13 / 4) ≤ (2 : ℝ) / (13 / 4) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      linarith
    have hIm1lo : -(2.265 : ℝ) ≤ (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).im := by
      have h := digamma_im_ge (-(1 / 4)) y hypos
      have e : (((-(1 / 4) : ℝ)) : ℂ) + (y : ℂ) * I = (-(1 / 4) : ℂ) + y * I := by push_cast; ring
      rw [e] at h
      linarith
    have hRe2hi : (Complex.digamma ((3 / 4 : ℂ) - y * I)).re ≤ (1.150 : ℝ) := by
      have h := digamma_re_three_quarter_le y hypos
      have hl : Real.log (y + 15 / 4) ≤ 1.75 :=
        le_trans (Real.log_le_log (by linarith) (by linarith)) log_twentythree_quarter_le
      have hB1 : (3 / 4 : ℝ) / (9 / 16 + (2 : ℝ) ^ 2) ≤ (3 / 4 : ℝ) / (9 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      have hB2 : (7 / 4 : ℝ) / (49 / 16 + (2 : ℝ) ^ 2) ≤ (7 / 4 : ℝ) / (49 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      have hB3 : (11 / 4 : ℝ) / (121 / 16 + (2 : ℝ) ^ 2) ≤ (11 / 4 : ℝ) / (121 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      linarith
    have hRe2lo : -(1.150 : ℝ) ≤ (Complex.digamma ((3 / 4 : ℂ) - y * I)).re := by
      have h := digamma_re_three_quarter_ge (-y) (by linarith)
      have e : ((3 / 4 : ℂ) + ((-y : ℝ)) * I) = ((3 / 4 : ℂ) - y * I) := by push_cast; ring
      rw [e] at h
      have e2 : ((-y : ℝ)) ^ 2 = y ^ 2 := by ring
      rw [e2] at h
      have hy2 : (1 : ℝ) ≤ y ^ 2 := by nlinarith
      have hq : (3 / 4 : ℝ) / (9 / 16 + y ^ 2) ≤ (29 / 60 : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hy2]
      linarith [h, hq]
    have hIm2hi : (Complex.digamma ((3 / 4 : ℂ) - y * I)).im ≤ (1.605 : ℝ) := by
      have h := digamma_im_conj_nonpos (3 / 4) y hypos
      have e : (((3 / 4 : ℝ) : ℂ) - (y : ℂ) * I) = ((3 / 4 : ℂ) - y * I) := by push_cast; ring
      rw [e] at h
      linarith
    have hIm2lo : -(1.605 : ℝ) ≤ (Complex.digamma ((3 / 4 : ℂ) - y * I)).im := by
      have h := digamma_im_conj_ge_three_quarter y hypos
      have ht1 : y / (9 / 16 + y ^ 2) ≤ (3 / 2 : ℝ) / (9 / 16 + (3 / 2 : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ y - 3 / 2)
          (by nlinarith : (9 / 16 : ℝ) - (3 / 2 : ℝ) * y ≤ 0)]
      have ht2 : y / (49 / 16 + y ^ 2) ≤ 2 / 7 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 7 / 4)]
      have ht3 : y / (121 / 16 + y ^ 2) ≤ 2 / 11 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 11 / 4)]
      have ht4 : y / (225 / 16 + y ^ 2) ≤ 2 / 15 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 15 / 4)]
      have ht5 : y / (17 / 4) ≤ (2 : ℝ) / (17 / 4) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      linarith
    have hc1 : ‖Complex.digamma ((-(1 / 4) : ℂ) + y * I)‖ ≤ (2.627 : ℝ) := by
      refine digamma_norm_le (M := 1.327) (Ig := 2.265) (c := 2.627) ?_ ?_ (by norm_num) (by norm_num)
      · rw [abs_le]; exact ⟨hRe1lo, hRe1hi⟩
      · rw [abs_le]; exact ⟨hIm1lo, hIm1hi⟩
    have hc2 : ‖Complex.digamma ((3 / 4 : ℂ) - y * I)‖ ≤ (1.977 : ℝ) := by
      refine digamma_norm_le (M := 1.150) (Ig := 1.605) (c := 1.977) ?_ ?_ (by norm_num) (by norm_num)
      · rw [abs_le]; exact ⟨hRe2lo, hRe2hi⟩
      · rw [abs_le]; exact ⟨hIm2lo, hIm2hi⟩
    have hL0 : (0.688 : ℝ) ≤ Real.log t := by
      rw [ht2y]
      have h2 : Real.log 2 ≤ Real.log (2 * y) :=
        Real.log_le_log (by norm_num) (by linarith)
      have h3 : (0.688 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      linarith
    have hnorm := hfe
    rw [e1, e2] at hnorm
    rw [hnorm]
    have hstep : ‖-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I)) + Complex.log (π : ℂ)
        - 1 / 2 * Complex.digamma ((-(1 / 4) : ℂ) + y * I)
        - 1 / 2 * Complex.digamma ((3 / 4 : ℂ) - y * I)‖
        ≤ ‖logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I))‖ + ‖Complex.log (π : ℂ)‖
          + ‖(1 / 2 : ℂ) * Complex.digamma ((-(1 / 4) : ℂ) + y * I)‖
          + ‖(1 / 2 : ℂ) * Complex.digamma ((3 / 4 : ℂ) - y * I)‖ := by
      have h4 := norm_sub_le
        (-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I)) + Complex.log (π : ℂ)
          - 1 / 2 * Complex.digamma ((-(1 / 4) : ℂ) + y * I))
        (1 / 2 * Complex.digamma ((3 / 4 : ℂ) - y * I))
      have h3 := norm_sub_le
        (-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I)) + Complex.log (π : ℂ))
        (1 / 2 * Complex.digamma ((-(1 / 4) : ℂ) + y * I))
      have h2 := norm_add_le (-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I)))
        (Complex.log (π : ℂ))
      have h2' : ‖-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I))‖
          = ‖logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I))‖ := norm_neg _
      linarith [h4, h3, h2, h2']
    refine le_trans hstep ?_
    have m1 : ‖(1 / 2 : ℂ) * Complex.digamma ((-(1 / 4) : ℂ) + y * I)‖
        = (1 / 2) * ‖Complex.digamma ((-(1 / 4) : ℂ) + y * I)‖ := by rw [norm_mul]; norm_num
    have m2 : ‖(1 / 2 : ℂ) * Complex.digamma ((3 / 4 : ℂ) - y * I)‖
        = (1 / 2) * ‖Complex.digamma ((3 / 4 : ℂ) - y * I)‖ := by rw [norm_mul]; norm_num
    rw [m1, m2]
    linarith [hc1, hc2, hA, hlogpi, hL0]

  · -- case 4: y ≤ 5 / 2

    have hyL : (2 : ℝ) ≤ y := le_of_lt hcC
    have hyC : y ≤ (5 / 2 : ℝ) := hy25
    have hRe1hi : (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).re ≤ (1.494 : ℝ) := by
      have h := digamma_re_neg_quarter_le y hypos
      have hl : Real.log (y + 11 / 4) ≤ 1.659 :=
        le_trans (Real.log_le_log (by linarith) (by linarith)) log_twentyone_quarter_le
      have hA1 : (-(1 / 4) : ℝ) / (1 / 16 + (2 : ℝ) ^ 2) ≤ (-(1 / 4) : ℝ) / (1 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyL]
      have hA2 : (3 / 4 : ℝ) / (9 / 16 + (5 / 2 : ℝ) ^ 2) ≤ (3 / 4 : ℝ) / (9 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      have hA3 : (7 / 4 : ℝ) / (49 / 16 + (5 / 2 : ℝ) ^ 2) ≤ (7 / 4 : ℝ) / (49 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      linarith
    have hRe1lo : -(1.494 : ℝ) ≤ (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).re := by
      have h := digamma_re_neg_quarter_ge y hypos.ne'
      have hy2 : (1 : ℝ) ≤ y ^ 2 := by nlinarith
      have hq : (3 / 4 : ℝ) / (9 / 16 + y ^ 2) ≤ (29 / 60 : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hy2]
      linarith [h, hq]
    have hIm1hi : (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).im ≤ (2.168 : ℝ) := by
      have h := digamma_im_le_neg_quarter y hypos
      have ht1 : y / (1 / 16 + y ^ 2) ≤ (2 : ℝ) / (1 / 16 + (2 : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ y - 2)
          (by nlinarith : (1 / 16 : ℝ) - (2 : ℝ) * y ≤ 0)]
      have ht2 : y / (9 / 16 + y ^ 2) ≤ (2 : ℝ) / (9 / 16 + (2 : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ y - 2)
          (by nlinarith : (9 / 16 : ℝ) - (2 : ℝ) * y ≤ 0)]
      have ht3 : y / (49 / 16 + y ^ 2) ≤ 2 / 7 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 7 / 4)]
      have ht4 : y / (121 / 16 + y ^ 2) ≤ 2 / 11 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 11 / 4)]
      have ht5 : y / (13 / 4) ≤ (5 / 2 : ℝ) / (13 / 4) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      linarith
    have hIm1lo : -(2.168 : ℝ) ≤ (Complex.digamma ((-(1 / 4) : ℂ) + y * I)).im := by
      have h := digamma_im_ge (-(1 / 4)) y hypos
      have e : (((-(1 / 4) : ℝ)) : ℂ) + (y : ℂ) * I = (-(1 / 4) : ℂ) + y * I := by push_cast; ring
      rw [e] at h
      linarith
    have hRe2hi : (Complex.digamma ((3 / 4 : ℂ) - y * I)).re ≤ (1.382 : ℝ) := by
      have h := digamma_re_three_quarter_le y hypos
      have hl : Real.log (y + 15 / 4) ≤ 1.833 :=
        le_trans (Real.log_le_log (by linarith) (by linarith)) log_twentyfive_quarter_le
      have hB1 : (3 / 4 : ℝ) / (9 / 16 + (5 / 2 : ℝ) ^ 2) ≤ (3 / 4 : ℝ) / (9 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      have hB2 : (7 / 4 : ℝ) / (49 / 16 + (5 / 2 : ℝ) ^ 2) ≤ (7 / 4 : ℝ) / (49 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      have hB3 : (11 / 4 : ℝ) / (121 / 16 + (5 / 2 : ℝ) ^ 2) ≤ (11 / 4 : ℝ) / (121 / 16 + y ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      linarith
    have hRe2lo : -(1.382 : ℝ) ≤ (Complex.digamma ((3 / 4 : ℂ) - y * I)).re := by
      have h := digamma_re_three_quarter_ge (-y) (by linarith)
      have e : ((3 / 4 : ℂ) + ((-y : ℝ)) * I) = ((3 / 4 : ℂ) - y * I) := by push_cast; ring
      rw [e] at h
      have e2 : ((-y : ℝ)) ^ 2 = y ^ 2 := by ring
      rw [e2] at h
      have hy2 : (1 : ℝ) ≤ y ^ 2 := by nlinarith
      have hq : (3 / 4 : ℝ) / (9 / 16 + y ^ 2) ≤ (29 / 60 : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hy2]
      linarith [h, hq]
    have hIm2hi : (Complex.digamma ((3 / 4 : ℂ) - y * I)).im ≤ (1.628 : ℝ) := by
      have h := digamma_im_conj_nonpos (3 / 4) y hypos
      have e : (((3 / 4 : ℝ) : ℂ) - (y : ℂ) * I) = ((3 / 4 : ℂ) - y * I) := by push_cast; ring
      rw [e] at h
      linarith
    have hIm2lo : -(1.628 : ℝ) ≤ (Complex.digamma ((3 / 4 : ℂ) - y * I)).im := by
      have h := digamma_im_conj_ge_three_quarter y hypos
      have ht1 : y / (9 / 16 + y ^ 2) ≤ (2 : ℝ) / (9 / 16 + (2 : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ y - 2)
          (by nlinarith : (9 / 16 : ℝ) - (2 : ℝ) * y ≤ 0)]
      have ht2 : y / (49 / 16 + y ^ 2) ≤ 2 / 7 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 7 / 4)]
      have ht3 : y / (121 / 16 + y ^ 2) ≤ 2 / 11 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 11 / 4)]
      have ht4 : y / (225 / 16 + y ^ 2) ≤ 2 / 15 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y - 15 / 4)]
      have ht5 : y / (17 / 4) ≤ (5 / 2 : ℝ) / (17 / 4) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hyC]
      linarith
    have hc1 : ‖Complex.digamma ((-(1 / 4) : ℂ) + y * I)‖ ≤ (2.635 : ℝ) := by
      refine digamma_norm_le (M := 1.494) (Ig := 2.168) (c := 2.635) ?_ ?_ (by norm_num) (by norm_num)
      · rw [abs_le]; exact ⟨hRe1lo, hRe1hi⟩
      · rw [abs_le]; exact ⟨hIm1lo, hIm1hi⟩
    have hc2 : ‖Complex.digamma ((3 / 4 : ℂ) - y * I)‖ ≤ (2.137 : ℝ) := by
      refine digamma_norm_le (M := 1.382) (Ig := 1.628) (c := 2.137) ?_ ?_ (by norm_num) (by norm_num)
      · rw [abs_le]; exact ⟨hRe2lo, hRe2hi⟩
      · rw [abs_le]; exact ⟨hIm2lo, hIm2hi⟩
    have hL0 : (0.688 : ℝ) ≤ Real.log t := by
      rw [ht2y]
      have h2 : Real.log 2 ≤ Real.log (2 * y) :=
        Real.log_le_log (by norm_num) (by linarith)
      have h3 : (0.688 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      linarith
    have hnorm := hfe
    rw [e1, e2] at hnorm
    rw [hnorm]
    have hstep : ‖-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I)) + Complex.log (π : ℂ)
        - 1 / 2 * Complex.digamma ((-(1 / 4) : ℂ) + y * I)
        - 1 / 2 * Complex.digamma ((3 / 4 : ℂ) - y * I)‖
        ≤ ‖logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I))‖ + ‖Complex.log (π : ℂ)‖
          + ‖(1 / 2 : ℂ) * Complex.digamma ((-(1 / 4) : ℂ) + y * I)‖
          + ‖(1 / 2 : ℂ) * Complex.digamma ((3 / 4 : ℂ) - y * I)‖ := by
      have h4 := norm_sub_le
        (-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I)) + Complex.log (π : ℂ)
          - 1 / 2 * Complex.digamma ((-(1 / 4) : ℂ) + y * I))
        (1 / 2 * Complex.digamma ((3 / 4 : ℂ) - y * I))
      have h3 := norm_sub_le
        (-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I)) + Complex.log (π : ℂ))
        (1 / 2 * Complex.digamma ((-(1 / 4) : ℂ) + y * I))
      have h2 := norm_add_le (-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I)))
        (Complex.log (π : ℂ))
      have h2' : ‖-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I))‖
          = ‖logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * I))‖ := norm_neg _
      linarith [h4, h3, h2, h2']
    refine le_trans hstep ?_
    have m1 : ‖(1 / 2 : ℂ) * Complex.digamma ((-(1 / 4) : ℂ) + y * I)‖
        = (1 / 2) * ‖Complex.digamma ((-(1 / 4) : ℂ) + y * I)‖ := by rw [norm_mul]; norm_num
    have m2 : ‖(1 / 2 : ℂ) * Complex.digamma ((3 / 4 : ℂ) - y * I)‖
        = (1 / 2) * ‖Complex.digamma ((3 / 4 : ℂ) - y * I)‖ := by rw [norm_mul]; norm_num
    rw [m1, m2]
    linarith [hc1, hc2, hA, hlogpi, hL0]


/-- The squared logarithmic majorant divided by the squared size of the contour parameter is
continuous on the positive half line: the logarithm is continuous there and the denominator is
strictly positive. -/
private theorem window_pos_majorant_continuousOn :
    ContinuousOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2)) (Set.Ioi (0 : ℝ)) := by
  have hlog : ContinuousOn (fun t : ℝ => Real.log t + 7) (Set.Ioi (0 : ℝ)) :=
    ContinuousOn.add (ContinuousOn.log continuousOn_id (fun t ht => ne_of_gt ht))
      continuousOn_const
  exact (hlog.pow 2).div (by fun_prop) (fun t _ => ne_of_gt (by positivity))

/-- `log 7 ≤ 1.95`, from the exponential series. -/
private theorem window_pos_log_seven_le : Real.log 7 ≤ 1.95 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  calc (7 : ℝ) ≤ ∑ i ∈ Finset.range 11, (1.95 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp 1.95 := Real.sum_le_exp_of_nonneg (by norm_num) _

/-- On `2 < t ≤ 7/2` the logarithm is at most two, so the squared majorant is at most `81`, and
the squared size `1/4 + t^2` of the contour parameter is at least four, so the majorant is at
most `81/4` there. -/
private theorem window_pos_majorant_low_le {t : ℝ} (h2 : 2 < t) (h5 : t ≤ 7 / 2) :
    (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2) ≤ 81 / 4 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog2 : Real.log t ≤ 2 := by
    have h1 : Real.log t ≤ Real.log 7 := Real.log_le_log ht0 (by linarith)
    linarith [window_pos_log_seven_le]
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hsq : (Real.log t + 7) ^ 2 ≤ 81 := by
    have hprod : (Real.log t - 2) * (Real.log t + 16) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    nlinarith [hprod]
  have hden : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
  have hd4 : (4 : ℝ) ≤ 1 / 4 + t ^ 2 := by nlinarith [sq_nonneg (t - 2)]
  rw [div_le_iff₀ hden]
  linarith

/-- On `7/2 < t ≤ 5` the logarithm is at most two, so the squared majorant is at most `81`, and
the squared size `1/4 + t^2` of the contour parameter is at least `25/2`, so the majorant is at
most `162/25` there. -/
private theorem window_pos_majorant_high_le {t : ℝ} (h2 : 7 / 2 < t) (h5 : t ≤ 5) :
    (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2) ≤ 162 / 25 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog2 : Real.log t ≤ 2 := by
    have h1 : Real.log t ≤ Real.log 7 := Real.log_le_log ht0 (by linarith)
    linarith [window_pos_log_seven_le]
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hsq : (Real.log t + 7) ^ 2 ≤ 81 := by
    have hprod : (Real.log t - 2) * (Real.log t + 16) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    nlinarith [hprod]
  have hden : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
  have hd : (25 / 2 : ℝ) ≤ 1 / 4 + t ^ 2 := by nlinarith [sq_nonneg (t - 7 / 2)]
  rw [div_le_iff₀ hden]
  linarith

/-- LEAF. The lower half of the window: the squared logarithmic majorant divided by the squared
size of the contour parameter has integral at most forty five over `2 < t ≤ 7/2`.  This is the
calculus step on the left half of the window, where `log t` is still small. -/
theorem principal_log_weight_sq_window_pos_majorant_low :
    (∫ t in Set.Ioc (2 : ℝ) (7 / 2), (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2)) ≤ 45 := by
  have hcont : ContinuousOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Icc (2 : ℝ) (7 / 2)) :=
    window_pos_majorant_continuousOn.mono
      (by intro t ht; exact Set.mem_Ioi.mpr (by linarith [ht.1]))
  have hint : IntegrableOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Ioc (2 : ℝ) (7 / 2)) := hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hc : IntegrableOn (fun _ : ℝ => (81 / 4 : ℝ)) (Set.Ioc (2 : ℝ) (7 / 2)) :=
    integrableOn_const (by simp)
  have hmono := setIntegral_mono_on hint hc measurableSet_Ioc
    (fun t ht => window_pos_majorant_low_le ht.1 ht.2)
  have hval : (∫ _t in Set.Ioc (2 : ℝ) (7 / 2), (81 / 4 : ℝ)) = 243 / 8 := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num), smul_eq_mul]
    norm_num
  rw [hval] at hmono
  linarith

/-- LEAF. The upper half of the window: the squared logarithmic majorant divided by the squared
size of the contour parameter has integral at most thirty over `7/2 < t ≤ 5`.  This is the
calculus step on the right half of the window, where the denominator has grown. -/
theorem principal_log_weight_sq_window_pos_majorant_high :
    (∫ t in Set.Ioc (7 / 2) 5, (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2)) ≤ 30 := by
  have hcont : ContinuousOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Icc (7 / 2 : ℝ) 5) :=
    window_pos_majorant_continuousOn.mono
      (by intro t ht; exact Set.mem_Ioi.mpr (by linarith [ht.1]))
  have hint : IntegrableOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Ioc (7 / 2 : ℝ) 5) := hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hc : IntegrableOn (fun _ : ℝ => (162 / 25 : ℝ)) (Set.Ioc (7 / 2 : ℝ) 5) :=
    integrableOn_const (by simp)
  have hmono := setIntegral_mono_on hint hc measurableSet_Ioc
    (fun t ht => window_pos_majorant_high_le ht.1 ht.2)
  have hval : (∫ _t in Set.Ioc (7 / 2 : ℝ) 5, (162 / 25 : ℝ)) = 243 / 25 := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num), smul_eq_mul]
    norm_num
  rw [hval] at hmono
  linarith

/-- The weight is the logarithmic derivative of the zeta function on the left line divided by the
contour parameter, so its squared size is the squared logarithmic derivative divided by the
squared size of the parameter, which is `1/4 + t^2`. -/
private theorem principal_log_weight_sq_window_pos_norm_sq (t : ℝ) :
    ‖principalLogWeight t‖ ^ 2 =
      ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 / (1 / 4 + t ^ 2) := by
  have hden : ‖((-1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [principalLogWeight, norm_div, div_pow, hden]

/-- On the window the squared weight is at most the squared logarithmic majorant divided by the
squared size of the contour parameter.  The denominator is positive there and the majorant is
nonnegative, so the estimate is the pointwise domination squared term by term. -/
private theorem principal_log_weight_sq_window_pos_majorant_le :
    ∀ t ∈ Set.Ioc (2 : ℝ) 5,
      ‖principalLogWeight t‖ ^ 2 ≤ (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2) := by
  intro t ht
  have h2 : (2 : ℝ) ≤ t := le_of_lt ht.1
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hpos : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
  have hb := principal_log_weight_sq_window_pos_pointwise t ht
  have hbn : 0 ≤ Real.log t + 7 := by linarith
  have hb0 : 0 ≤ ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ := norm_nonneg _
  have hsq : ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (Real.log t + 7) ^ 2 := by nlinarith
  rw [principal_log_weight_sq_window_pos_norm_sq t]
  exact div_le_div_of_nonneg_right hsq hpos.le

/-- The squared logarithmic majorant divided by the squared size of the contour parameter is
continuous on the positive half line, where the logarithm is continuous and the denominator is
strictly positive. -/
private theorem principal_log_weight_sq_window_pos_majorant_continuousOn :
    ContinuousOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2)) (Set.Ioi (0 : ℝ)) := by
  have hlog : ContinuousOn (fun t : ℝ => Real.log t + 7) (Set.Ioi (0 : ℝ)) :=
    ContinuousOn.add (ContinuousOn.log continuousOn_id (fun t ht => ne_of_gt ht))
      continuousOn_const
  exact (hlog.pow 2).div (by fun_prop) (fun t _ => ne_of_gt (by positivity))

/-- The window splits at height seven halves into the lower and the upper half, the two halves are
disjoint, and the majorant is integrable on each of them, so its integral over the window is the
sum of the two integrals. -/
private theorem principal_log_weight_sq_window_pos_majorant_split :
    (∫ t in Set.Ioc (2 : ℝ) 5, (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      = (∫ t in Set.Ioc (2 : ℝ) (7 / 2), (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
        + ∫ t in Set.Ioc (7 / 2) 5, (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2) := by
  have hunion : Set.Ioc (2 : ℝ) (7 / 2) ∪ Set.Ioc (7 / 2) 5 = Set.Ioc (2 : ℝ) 5 :=
    Set.Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)
  have hdisj : Disjoint (Set.Ioc (2 : ℝ) (7 / 2)) (Set.Ioc (7 / 2 : ℝ) 5) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [Set.mem_Ioc] at hx hx'
    linarith
  have hlowcc : IntegrableOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Icc (2 : ℝ) (7 / 2)) :=
    (principal_log_weight_sq_window_pos_majorant_continuousOn.mono
      (by intro t ht; exact Set.mem_Ioi.mpr (by linarith [ht.1]))).integrableOn_Icc
  have hlow : IntegrableOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Ioc (2 : ℝ) (7 / 2)) := hlowcc.mono_set Set.Ioc_subset_Icc_self
  have hhighcc : IntegrableOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Icc (7 / 2 : ℝ) 5) :=
    (principal_log_weight_sq_window_pos_majorant_continuousOn.mono
      (by intro t ht; exact Set.mem_Ioi.mpr (by linarith [ht.1]))).integrableOn_Icc
  have hhigh : IntegrableOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Ioc (7 / 2 : ℝ) 5) := hhighcc.mono_set Set.Ioc_subset_Icc_self
  rw [← hunion]
  exact setIntegral_union hdisj measurableSet_Ioc hlow hhigh

/-- The window energy of the logarithmic derivative weight, assembled from the pointwise
domination and the two half window integral estimates: the squared weight is dominated by the
majorant on the window, the majorant integral is the sum of its two half window integrals, and the
two allowances forty five and thirty add up to seventy five. -/
theorem principal_log_weight_sq_window_pos_split :
    (∫ t in Set.Ioc 2 5, ‖principalLogWeight t‖ ^ 2) ≤ 75 := by
  classical
  have hint : IntegrableOn (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) (Set.Ioc (2 : ℝ) 5) :=
    (MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two
      (by norm_num)).integrableOn
  have hmajcc : IntegrableOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Icc (2 : ℝ) 5) :=
    (principal_log_weight_sq_window_pos_majorant_continuousOn.mono
      (by intro t ht; exact Set.mem_Ioi.mpr (by linarith [ht.1]))).integrableOn_Icc
  have hmaj : IntegrableOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Ioc (2 : ℝ) 5) := hmajcc.mono_set Set.Ioc_subset_Icc_self
  have hmono : (∫ t in Set.Ioc (2 : ℝ) 5, ‖principalLogWeight t‖ ^ 2)
      ≤ ∫ t in Set.Ioc (2 : ℝ) 5, (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2) :=
    setIntegral_mono_on hint hmaj measurableSet_Ioc principal_log_weight_sq_window_pos_majorant_le
  rw [principal_log_weight_sq_window_pos_majorant_split] at hmono
  linarith [hmono, principal_log_weight_sq_window_pos_majorant_low,
    principal_log_weight_sq_window_pos_majorant_high]

end LeanLab.HelfgottMajor.Decomp457b

#print axioms LeanLab.HelfgottMajor.Decomp457b.principal_log_weight_sq_window_pos_split
