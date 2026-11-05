import LeanLab.LPZ2007.ZeroFamily373

/-!
Gamma quotient bounds for Lemma 4.1 on P0045 preprint page 5.
These are elementary estimates for the explicit formula, not that formula.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.Gamma373

open Complex Real MeasureTheory

/-- P0045 page 5, the Gamma quotient in Lemma 4.1.
The beta integral at two halves equals pi. -/
theorem beta_half : Complex.betaIntegral (1 / 2) (1 / 2) = (Real.pi : ℂ) := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num)]
  norm_num only [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Complex.Gamma_one, div_one]
  simpa only [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, mul_one_div,
    Complex.sin_pi_div_two, div_one] using Complex.Gamma_mul_Gamma_one_sub (1 / 2)

/-- P0045 page 5, the Gamma quotient in Lemma 4.1.
Real parts at least one half give the uniform beta integral majorant pi. -/
theorem gamma_ratio_le_pi {s t : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re)
    (ht : (1 / 2 : ℝ) ≤ t.re) :
    ‖Complex.Gamma s * Complex.Gamma t / Complex.Gamma (s + t)‖ ≤ Real.pi := by
  rw [← Complex.betaIntegral_eq_Gamma_mul_div s t (by linarith) (by linarith)]
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ ((1 / 2 : ℂ) - 1) *
    (1 - (x : ℂ)) ^ ((1 / 2 : ℂ) - 1)
  have hfint : IntervalIntegrable f volume 0 1 :=
    Complex.betaIntegral_convergent (u := (1 / 2 : ℂ)) (v := (1 / 2 : ℂ))
      (by norm_num) (by norm_num)
  have hint : IntervalIntegrable (fun x => (f x).re) volume 0 1 :=
    ⟨hfint.1.re, hfint.2.re⟩
  have hbound : ∀ᵐ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 →
      ‖(x : ℂ) ^ (s - 1) * (1 - (x : ℂ)) ^ (t - 1)‖ ≤ (f x).re := by
    filter_upwards [volume.ae_ne (1 : ℝ)] with x hx1 hx
    have hx0 : 0 < x := hx.1
    have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have hsub : 0 < 1 - x := by linarith
    have hcast : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; rfl
    have hhalf : ((1 / 2 : ℂ) - 1) = ((-1 / 2 : ℝ) : ℂ) := by norm_num
    have hf : (f x).re = x ^ (-1 / 2 : ℝ) * (1 - x) ^ (-1 / 2 : ℝ) := by
      dsimp [f]
      rw [hcast, hhalf, ← Complex.ofReal_cpow hx0.le,
        ← Complex.ofReal_cpow hsub.le, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hf, norm_mul, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      Complex.norm_cpow_eq_rpow_re_of_pos hsub]
    simp only [Complex.sub_re, Complex.one_re]
    apply mul_le_mul
    · exact Real.rpow_le_rpow_of_exponent_ge hx0 hx.2 (by linarith)
    · exact Real.rpow_le_rpow_of_exponent_ge hsub (by linarith) (by linarith)
    · positivity
    · positivity
  have h := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 1)
    hbound hint
  have heval : ∫ x : ℝ in 0..1, (f x).re = Real.pi := by
    calc
      _ = (∫ x : ℝ in 0..1, f x).re := Complex.reCLM.intervalIntegral_comp_comm hfint
      _ = Real.pi := by
        change (Complex.betaIntegral (1 / 2) (1 / 2)).re = Real.pi
        rw [beta_half, Complex.ofReal_re]
  simpa only [Complex.betaIntegral, heval] using h

/-- P0045 page 5, an individual zero pair term of the explicit formula.
The Gamma quotient times n to the zero sum minus one has norm at most pi n. -/
theorem gamma_power_le {s t : ℂ} (hs0 : (1 / 2 : ℝ) ≤ s.re)
    (ht0 : (1 / 2 : ℝ) ≤ t.re) (hs1 : s.re ≤ 1) (ht1 : t.re ≤ 1)
    {n : ℝ} (hn : 1 ≤ n) :
    ‖(Complex.Gamma s * Complex.Gamma t / Complex.Gamma (s + t)) *
      (n : ℂ) ^ (s + t - 1)‖ ≤ Real.pi * n := by
  have hnp : 0 < n := by linarith
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hnp]
  have hp : n ^ (s + t - 1).re ≤ n := by
    calc
      _ ≤ n ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by
        simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; linarith)
      _ = n := Real.rpow_one _
  exact mul_le_mul (gamma_ratio_le_pi hs0 ht0) hp
    (Real.rpow_nonneg hnp.le _) Real.pi_pos.le

/-- P0045 page 5, Lemma 4.1, the uniform bound for an actual pole or zero pair.
At X at least exp of 2H, each selected real part lies between one half and one. -/
theorem explicit_formula_pair_bound {X H T P : ℝ} (hH : 1 ≤ H)
    (hX : Real.exp (2 * H) ≤ X) {ρ σ : ℂ}
    (hρ : ρ = 1 ∨ ∃ z ∈ EZero X H T P, ρ = z.2.2)
    (hσ : σ = 1 ∨ ∃ z ∈ EZero X H T P, σ = z.2.2)
    {n : ℝ} (hn : 1 ≤ n) :
    ‖(Complex.Gamma ρ * Complex.Gamma σ / Complex.Gamma (ρ + σ)) *
      (n : ℂ) ^ (ρ + σ - 1)‖ ≤ Real.pi * n := by
  have hlog : 2 * H ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hX
  have hlogpos : 0 < Real.log X := by linarith
  have hdiv : H / Real.log X ≤ 1 / 2 := by
    rw [div_le_iff₀ hlogpos]
    linarith
  have hstrip : ∀ w : ℂ, (w = 1 ∨ ∃ z ∈ EZero X H T P, w = z.2.2) →
      (1 / 2 : ℝ) ≤ w.re ∧ w.re ≤ 1 := by
    intro w hw
    rcases hw with rfl | ⟨z, hz, rfl⟩
    · norm_num
    · exact ⟨by linarith [hz.2.2.2.2.1],
        (ZeroFamily373.primitive_zero_re_lt_one hz.1 z.2.1 hz.2.2.1 hz.2.2.2.1).le⟩
  exact gamma_power_le (hstrip ρ hρ).1 (hstrip σ hσ).1 (hstrip ρ hρ).2 (hstrip σ hσ).2 hn

end LeanLab.LPZ2007.Gamma373

#print axioms LeanLab.LPZ2007.Gamma373.beta_half
#print axioms LeanLab.LPZ2007.Gamma373.gamma_ratio_le_pi
#print axioms LeanLab.LPZ2007.Gamma373.gamma_power_le

#print axioms LeanLab.LPZ2007.Gamma373.explicit_formula_pair_bound
