import LeanLab.HelfgottMajor.Decomp457b
import LeanLab.HelfgottMajor.SPLIT_principal_log_weight_sq_short

/-!
Copy of the Weierstrass-product digamma series (`Digamma210.DigammaSeries` of
`LeanLab/Routes/Decomp1551b.lean`, ported from anthropics/formal-math
`zeta23/Zeta23/GammaFacts/Series.lean` at e1a4e65) and of the harmonic-logarithm chain
(`Digamma210`, from `StirlingVert.lean` at the same commit), with the local
`noncomputable def wTerm` inlined as the expression
`(1 + z/(n+1)) * exp (-(z/(n+1))) - 1`, because this unit may not add a definition of any
kind. Statements are otherwise unchanged; `digamma_re_le` is renamed
`digamma_re_le_nine_quarter`.
-/

set_option maxHeartbeats 400000
set_option maxRecDepth 1000

namespace LeanLab.HelfgottMajor.Decomp457b
namespace DigammaBudget
open Complex Filter Topology
open Contour457

lemma one_add_wFactor (n : ℕ) (z : ℂ) :
    1 + ((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1) = (1 + z / (n + 1)) * Complex.exp (-(z / (n + 1))) := by
  ring

lemma norm_natCast_add_one (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- The quadratic tail bound for the Weierstrass factor. -/
lemma norm_wFactor_le {z : ℂ} {n : ℕ} (h : ‖z‖ ≤ (n : ℝ) + 1) :
    ‖((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1)‖ ≤ 3 * (‖z‖ / ((n : ℝ) + 1)) ^ 2 := by
  set w : ℂ := z / ((n : ℂ) + 1) with hwdef
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hwnorm : ‖w‖ = ‖z‖ / ((n : ℝ) + 1) := by
    rw [hwdef, norm_div, norm_natCast_add_one]
  have hwn : ‖w‖ ≤ 1 := by
    rw [hwnorm, div_le_one hn1]
    exact h
  have hr : ‖Complex.exp (-w) - 1 + w‖ ≤ ‖w‖ ^ 2 := by
    have hx : ‖(-w : ℂ)‖ ≤ 1 := by rwa [norm_neg]
    have h2 := norm_exp_sub_one_sub_id_le hx
    rw [norm_neg] at h2
    calc ‖Complex.exp (-w) - 1 + w‖ = ‖Complex.exp (-w) - 1 - (-w)‖ := by ring_nf
      _ ≤ ‖w‖ ^ 2 := h2
  have hident : ((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1) = (Complex.exp (-w) - 1 + w) - w ^ 2
      + w * (Complex.exp (-w) - 1 + w) := by
    ring
  have hnw2 : ‖(w : ℂ) ^ 2‖ = ‖w‖ ^ 2 := norm_pow _ _
  calc ‖((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1)‖
      ≤ ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖ + ‖w * (Complex.exp (-w) - 1 + w)‖ := by
        rw [hident]
        exact norm_add_le _ _
    _ ≤ (‖w‖ ^ 2 + ‖w‖ ^ 2) + ‖w‖ * ‖w‖ ^ 2 := by
        have h1 : ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := by
          calc ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖
              ≤ ‖Complex.exp (-w) - 1 + w‖ + ‖(w : ℂ) ^ 2‖ := norm_sub_le _ _
            _ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := by
                rw [hnw2]
                exact add_le_add hr le_rfl

        have h2 : ‖w * (Complex.exp (-w) - 1 + w)‖ ≤ ‖w‖ * ‖w‖ ^ 2 := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hr (norm_nonneg _)
        linarith
    _ ≤ 3 * ‖w‖ ^ 2 := by nlinarith [norm_nonneg w, hwn, sq_nonneg ‖w‖]
    _ = 3 * (‖z‖ / ((n : ℝ) + 1)) ^ 2 := by rw [hwnorm]

lemma summable_wBound (R : ℝ) : Summable (fun n : ℕ => 3 * (R / ((n : ℝ) + 1)) ^ 2) := by
  have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
    have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
      have := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
      have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
        funext n
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rwa [heq] at this
    have := (summable_nat_add_iff 1).mpr h2
    simpa [add_comm] using this
  have h3 : (fun n : ℕ => 3 * (R / ((n : ℝ) + 1)) ^ 2)
      = fun n : ℕ => (3 * R ^ 2) * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
    funext n
    rw [div_pow]
    ring
  rw [h3]
  exact h1.mul_left _

lemma summable_norm_wFactor (z : ℂ) : Summable (fun n : ℕ => ‖((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1)‖) := by
  refine (summable_wBound ‖z‖).of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_ge_atTop ⌈‖z‖⌉₊] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  refine norm_wFactor_le ?_
  calc ‖z‖ ≤ (⌈‖z‖⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn
    _ ≤ (n : ℝ) + 1 := by linarith

lemma multipliable_one_add_wFactor (z : ℂ) : Multipliable fun n : ℕ => 1 + ((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1) :=
  Complex.multipliable_one_add_of_summable ((summable_norm_wFactor z).of_norm)

/-! ### The finite identity and the Weierstrass product -/

lemma harmonic_cast_eq (N : ℕ) :
    ((harmonic N : ℚ) : ℝ) = ∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1) := by
  rw [harmonic]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [one_div]

/-- The finite identity: (GammaSeq z N)⁻¹ = z·e^{(H_N − log N)z}·∏_{n<N}(1 + ((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1)). -/
lemma inv_gammaSeq_eq {z : ℂ} (_hz : z ∈ Complex.integerComplement) {N : ℕ} (hN : 1 ≤ N) :
    (Complex.GammaSeq z N)⁻¹
      = z * Complex.exp ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1))
            - Real.log N : ℝ) : ℂ) * z)
          * ∏ n ∈ Finset.range N, (1 + ((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1)) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- the product of the Weierstrass factors
  have hprod : ∏ n ∈ Finset.range N, (1 + ((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1))
      = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
          * Complex.exp (-(∑ m ∈ Finset.range N, z / ((m : ℂ) + 1))) := by
    calc ∏ n ∈ Finset.range N, (1 + ((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1))
        = ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
            * Complex.exp (-(z / ((n : ℂ) + 1))) :=
          Finset.prod_congr rfl fun n _ => one_add_wFactor n z
      _ = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
            * ∏ n ∈ Finset.range N, Complex.exp (-(z / ((n : ℂ) + 1))) :=
          Finset.prod_mul_distrib
      _ = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
            * Complex.exp (∑ n ∈ Finset.range N, -(z / ((n : ℂ) + 1))) := by
          rw [Complex.exp_sum]
      _ = _ := by rw [← Finset.sum_neg_distrib]
  -- numeric ingredients
  have hfact_ne : ((N.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hNz : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcpow : (N : ℂ) ^ z = Complex.exp (((Real.log N : ℝ) : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero hNz]
    congr 2
    rw [show ((N : ℂ)) = (((N : ℝ) : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log hNR.le).symm
  have hdenom : ∏ j ∈ Finset.range (N + 1), (z + (j : ℂ))
      = z * ∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1)) := by
    rw [Finset.prod_range_succ']
    rw [Nat.cast_zero, add_zero, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun n _ => ?_
    push_cast
    ring
  have hfactprod : ((N.factorial : ℕ) : ℂ) = ∏ n ∈ Finset.range N, ((n : ℂ) + 1) := by
    rw [show N.factorial = ∏ n ∈ Finset.range N, (n + 1) from
      (Finset.prod_range_add_one_eq_factorial N).symm]
    push_cast
    rfl
  have hfrac : ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
      = (∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1))) / ((N.factorial : ℕ) : ℂ) := by
    have h1 : ∀ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
        = (z + ((n : ℂ) + 1)) / ((n : ℂ) + 1) := by
      intro n _
      have hne : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      field_simp
      ring
    rw [Finset.prod_congr rfl h1, Finset.prod_div_distrib, hfactprod]
  have hsumcast : (((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ)
      = ∑ m ∈ Finset.range N, 1 / ((m : ℂ) + 1) := by
    push_cast
    rfl
  have hzsum : ∑ m ∈ Finset.range N, z / ((m : ℂ) + 1)
      = z * ∑ m ∈ Finset.range N, 1 / ((m : ℂ) + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  -- assemble
  rw [Complex.GammaSeq, hprod, hfrac, hdenom, hcpow, hzsum, ← hsumcast]
  rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub]
  set A : ℂ := ∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1)) with hA
  set E1 : ℂ := Complex.exp ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ) * z)
    with hE1
  set E2 : ℂ := Complex.exp (((Real.log N : ℝ) : ℂ) * z) with hE2
  have hE1ne : E1 ≠ 0 := Complex.exp_ne_zero _
  have hE2ne : E2 ≠ 0 := Complex.exp_ne_zero _
  have hexpneg : Complex.exp (-(z * (((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ)))
      = E1⁻¹ := by
    rw [hE1, ← Complex.exp_neg]
    congr 1
    ring
  rw [hexpneg]
  field_simp

/-- **The Weierstrass product for 1/Γ** on the integer complement:
Γ(z)⁻¹ = z·e^{γz}·∏'ₙ (1 + z/(n+1))e^{−z/(n+1)}. -/
theorem inv_gamma_eq_prod {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    (Complex.Gamma z)⁻¹
      = z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
          * ∏' n : ℕ, (1 + ((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1)) := by
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hL : Tendsto (fun N => (Complex.GammaSeq z N)⁻¹) atTop (𝓝 ((Complex.Gamma z)⁻¹)) :=
    (Complex.GammaSeq_tendsto_Gamma z).inv₀ (Complex.Gamma_ne_zero hzero)
  have hhar : Tendsto (fun N : ℕ =>
      ((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    refine Real.tendsto_harmonic_sub_log.congr fun n => ?_
    rw [harmonic_cast_eq]
  have hexp : Tendsto (fun N : ℕ => Complex.exp
      ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z))
      atTop (𝓝 (Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z))) := by
    have h2 : Tendsto (fun N : ℕ =>
        ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ)))
        atTop (𝓝 ((Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hhar
    exact (Complex.continuous_exp.tendsto _).comp (h2.mul_const z)
  have hP : Tendsto (fun N => ∏ n ∈ Finset.range N, (1 + ((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1))) atTop
      (𝓝 (∏' n : ℕ, (1 + ((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1)))) :=
    (multipliable_one_add_wFactor z).hasProd.tendsto_prod_nat
  have hRHS : Tendsto (fun N : ℕ => z * Complex.exp
      ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z)
      * ∏ n ∈ Finset.range N, (1 + ((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1))) atTop
      (𝓝 (z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
        * ∏' n : ℕ, (1 + ((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1)))) :=
    (tendsto_const_nhds.mul hexp).mul hP
  have heq : ∀ᶠ N in atTop, (Complex.GammaSeq z N)⁻¹
      = z * Complex.exp
        ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z)
      * ∏ n ∈ Finset.range N, (1 + ((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact inv_gammaSeq_eq hz hN
  exact tendsto_nhds_unique (hL.congr' heq) hRHS

/-- The logarithmic derivative of a single Weierstrass factor. -/
lemma logDeriv_one_add_wFactor {z : ℂ} (hz : z ∈ Complex.integerComplement) (n : ℕ) :
    logDeriv (fun s => 1 + ((1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) - 1)) z = 1 / (z + n + 1) - 1 / ((n : ℂ) + 1) := by
  have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
    have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
    push_cast at this ⊢
    convert this using 2
  have hzn' : z + (n : ℂ) + 1 ≠ 0 := by
    rw [add_assoc]
    exact hzn
  have hfun : (fun s => 1 + ((1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) - 1))
      = fun s : ℂ => (1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) := by
    funext s
    exact one_add_wFactor n s
  rw [hfun]
  have h1z : (1 + z / ((n : ℂ) + 1)) ≠ 0 := by
    intro h
    apply hzn
    have h2 := congrArg (fun t => t * ((n : ℂ) + 1)) h
    simp only [add_mul, one_mul, zero_mul] at h2
    rw [div_mul_cancel₀ _ hn1] at h2
    rw [← h2]
    ring
  have hd1 : HasDerivAt (fun s : ℂ => 1 + s / ((n : ℂ) + 1)) (1 / ((n : ℂ) + 1)) z := by
    have h3 := ((hasDerivAt_id z).div_const ((n : ℂ) + 1)).const_add 1
    simpa [one_div] using h3
  have hd2 : HasDerivAt (fun s : ℂ => Complex.exp (-(s / ((n : ℂ) + 1))))
      (-(1 / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1)))) z := by
    have hlin : HasDerivAt (fun s : ℂ => -(s / ((n : ℂ) + 1))) (-(1 / ((n : ℂ) + 1))) z := by
      exact ((hasDerivAt_id z).div_const ((n : ℂ) + 1)).neg
    have h5 := hlin.cexp
    simpa [mul_comm] using h5
  have hprod : HasDerivAt
      (fun s : ℂ => (1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))))
      (1 / ((n : ℂ) + 1) * Complex.exp (-(z / ((n : ℂ) + 1)))
        + (1 + z / ((n : ℂ) + 1)) * (-(1 / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))))) z :=
    hd1.mul hd2
  unfold logDeriv
  rw [Pi.div_apply, hprod.deriv]
  have hexpne : Complex.exp (-(z / ((n : ℂ) + 1))) ≠ 0 := Complex.exp_ne_zero _
  have h3 : (1 : ℂ) + (n : ℂ) + z ≠ 0 := by
    intro h
    apply hzn'
    linear_combination h
  field_simp [h3]
  have h4 : ((1 : ℂ) + (n : ℂ) + z) * ((1 + (n : ℂ) + z)⁻¹) = 1 := mul_inv_cancel₀ h3
  linear_combination (-z) * h4

/-- Summability of the digamma partial-fraction series. -/
theorem summable_digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
  refine Summable.of_norm ?_
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℕ => 2 * ‖z‖ * ((((n : ℝ) + 1) ^ 2)⁻¹)) ?_ ?_
  · have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
      have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
        have h3 := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
        have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
          funext n
          rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rwa [heq] at h3
      have h4 := (summable_nat_add_iff 1).mpr h2
      simpa [add_comm] using h4
    exact h1.mul_left _
  · rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_ge_atTop ⌈2 * ‖z‖⌉₊] with n hn
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
      have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
      push_cast at this ⊢
      convert this using 2
    have hzn' : z + (n : ℂ) + 1 ≠ 0 := by
      rw [add_assoc]
      exact hzn
    have hident : 1 / ((n : ℂ) + 1) - 1 / (z + n + 1)
        = z / (((n : ℂ) + 1) * (z + n + 1)) := by
      field_simp
      ring
    have h2n : 2 * ‖z‖ ≤ (n : ℝ) := by
      calc 2 * ‖z‖ ≤ (⌈2 * ‖z‖⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (n : ℝ) := by exact_mod_cast hn
    have hlow : ((n : ℝ) + 1) / 2 ≤ ‖z + (n : ℂ) + 1‖ := by
      have h1 : ‖((n : ℂ) + 1)‖ - ‖z‖ ≤ ‖z + (n : ℂ) + 1‖ := by
        have h2 := norm_sub_le (z + (n : ℂ) + 1) z
        have h3 : (z + (n : ℂ) + 1) - z = ((n : ℂ) + 1) := by ring
        rw [h3] at h2
        linarith
      rw [norm_natCast_add_one] at h1
      linarith [norm_nonneg z]
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hident, norm_div, norm_mul,
      norm_natCast_add_one]
    calc ‖z‖ / (((n : ℝ) + 1) * ‖z + (n : ℂ) + 1‖)
        ≤ ‖z‖ / (((n : ℝ) + 1) * (((n : ℝ) + 1) / 2)) := by
          gcongr
      _ = 2 * ‖z‖ * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
          field_simp

/-- **The digamma partial-fraction series, HasSum form**:
Σₙ (1/(n+1) − 1/(z+n+1)) converges to ψ(z) + γ + 1/z on the integer complement. -/
theorem hasSum_digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1))
      (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z) := by
  set γc : ℂ := ((Real.eulerMascheroniConstant : ℝ) : ℂ) with hγc
  have hz0 : z ≠ 0 := Complex.integerComplement.ne_zero hz
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hΓne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hzero
  have hopenZ : IsOpen Complex.integerComplement := isOpen_compl_range_intCast
  set U : Set ℂ := Metric.ball (0 : ℂ) (‖z‖ + 1) with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := by
    rw [hU, Metric.mem_ball, dist_zero_right]
    linarith [norm_nonneg z]
  have htend : MultipliableLocallyUniformlyOn (fun (n : ℕ) (s : ℂ) => 1 + ((1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) - 1)) U := by
    refine Summable.multipliableLocallyUniformlyOn_nat_one_add hUopen
      (summable_wBound (‖z‖ + 1)) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop ⌈‖z‖ + 1⌉₊] with n hn x hx
      have hx1 : ‖x‖ ≤ ‖z‖ + 1 := by
        rw [hU, Metric.mem_ball, dist_zero_right] at hx
        linarith
      have hn1 : ‖z‖ + 1 ≤ (n : ℝ) + 1 := by
        calc ‖z‖ + 1 ≤ (⌈‖z‖ + 1⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn
          _ ≤ (n : ℝ) + 1 := by linarith
      calc ‖((1 + x / ((n : ℂ) + 1)) * Complex.exp (-(x / ((n : ℂ) + 1))) - 1)‖ ≤ 3 * (‖x‖ / ((n : ℝ) + 1)) ^ 2 :=
            norm_wFactor_le (le_trans hx1 hn1)
        _ ≤ 3 * ((‖z‖ + 1) / ((n : ℝ) + 1)) ^ 2 := by
            gcongr
    · intro n
      have hc : Continuous (fun z : ℂ =>
          (1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1) := by
        fun_prop
      exact hc.continuousOn
  have hfne : ∀ n : ℕ, (fun s : ℂ => 1 + ((1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) - 1)) z ≠ 0 := by
    intro n
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
      have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
      push_cast at this ⊢
      convert this using 2
    simp only [one_add_wFactor]
    apply mul_ne_zero _ (Complex.exp_ne_zero _)
    intro h
    apply hzn
    have h2 := congrArg (fun t => t * ((n : ℂ) + 1)) h
    simp only [add_mul, one_mul, zero_mul] at h2
    rw [div_mul_cancel₀ _ hn1] at h2
    rw [← h2]
    ring
  have hgne : z * Complex.exp (γc * z) ≠ 0 := mul_ne_zero hz0 (Complex.exp_ne_zero _)
  have hPne : (∏' n : ℕ, (1 + ((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1))) ≠ 0 := by
    intro h
    have h2 := inv_gamma_eq_prod hz
    rw [← hγc, h, mul_zero] at h2
    exact inv_ne_zero hΓne h2
  have hsummable : Summable fun n : ℕ => logDeriv (fun s => 1 + ((1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) - 1)) z := by
    have hcongr : (fun n : ℕ => logDeriv (fun s => 1 + ((1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) - 1)) z)
        = fun n : ℕ => -(1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
      funext n
      rw [logDeriv_one_add_wFactor hz n]
      ring
    rw [hcongr]
    exact (summable_digamma_series hz).neg
  have hlogP : logDeriv (fun s => ∏' n : ℕ, (1 + ((1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) - 1))) z
      = ∑' n : ℕ, logDeriv (fun s => 1 + ((1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) - 1)) z := by
    refine logDeriv_tprod_eq_tsum hUopen hzU hfne ?_ hsummable htend hPne
    intro n
    have hd : Differentiable ℂ fun s : ℂ => 1 + ((1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) - 1) := by
      fun_prop
    exact hd.differentiableOn
  have hgdiff : Differentiable ℂ fun s : ℂ => s * Complex.exp (γc * s) := by
    fun_prop
  have hPdiff : DifferentiableAt ℂ (fun s => ∏' n : ℕ, (1 + ((1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) - 1))) z := by
    have hev : (fun s : ℂ => (Complex.Gamma s)⁻¹ / (s * Complex.exp (γc * s)))
        =ᶠ[nhds z] (fun s => ∏' n : ℕ, (1 + ((1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) - 1))) := by
      filter_upwards [hopenZ.mem_nhds hz] with s hs
      have h2 := inv_gamma_eq_prod hs
      rw [← hγc] at h2
      have hsne : s * Complex.exp (γc * s) ≠ 0 :=
        mul_ne_zero (Complex.integerComplement.ne_zero hs) (Complex.exp_ne_zero _)
      rw [h2]
      exact mul_div_cancel_left₀ _ hsne
    have hd : DifferentiableAt ℂ
        (fun s : ℂ => (Complex.Gamma s)⁻¹ / (s * Complex.exp (γc * s))) z := by
      refine DifferentiableAt.div ?_ (hgdiff z) hgne
      exact Complex.differentiable_one_div_Gamma z
    exact hd.congr_of_eventuallyEq hev.symm
  have hldinv : logDeriv (fun s => (Complex.Gamma s)⁻¹) z = -Complex.digamma z := by
    have h1 : logDeriv ((·⁻¹) ∘ Complex.Gamma) z
        = logDeriv (·⁻¹) (Complex.Gamma z) * deriv Complex.Gamma z := by
      refine logDeriv_comp ?_ (Complex.differentiableAt_Gamma z hzero)
      exact differentiableAt_inv hΓne
    rw [show (fun s => (Complex.Gamma s)⁻¹) = (·⁻¹) ∘ Complex.Gamma from rfl, h1, logDeriv_inv]
    rw [Complex.digamma_def, logDeriv_apply]
    field_simp
  have hev2 : (fun s => (Complex.Gamma s)⁻¹)
      =ᶠ[nhds z] fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + ((1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) - 1)) := by
    filter_upwards [hopenZ.mem_nhds hz] with s hs
    have h2 := inv_gamma_eq_prod hs
    rw [← hγc] at h2
    rw [h2]
  have hlogeq : logDeriv (fun s => (Complex.Gamma s)⁻¹) z
      = logDeriv (fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + ((1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) - 1))) z := by
    unfold logDeriv
    rw [Pi.div_apply, Pi.div_apply, hev2.deriv_eq, hev2.eq_of_nhds]
  have hmul : logDeriv (fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + ((1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) - 1))) z
      = logDeriv (fun s : ℂ => s * Complex.exp (γc * s)) z
        + logDeriv (fun s => ∏' n : ℕ, (1 + ((1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) - 1))) z :=
    logDeriv_mul z hgne hPne (hgdiff z) hPdiff
  have hldg : logDeriv (fun s : ℂ => s * Complex.exp (γc * s)) z = 1 / z + γc := by
    have hder : HasDerivAt (fun s : ℂ => s * Complex.exp (γc * s))
        (1 * Complex.exp (γc * z) + z * (γc * Complex.exp (γc * z))) z := by
      have h1 : HasDerivAt (fun s : ℂ => Complex.exp (γc * s)) (γc * Complex.exp (γc * z)) z := by
        have hlin : HasDerivAt (fun s : ℂ => γc * s) γc z := by
          simpa using (hasDerivAt_id z).const_mul γc
        have h5 := hlin.cexp
        simpa [mul_comm] using h5
      exact (hasDerivAt_id z).mul h1
    unfold logDeriv
    rw [Pi.div_apply, hder.deriv]
    have he : Complex.exp (γc * z) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  have hmain : -Complex.digamma z
      = (1 / z + γc) + ∑' n : ℕ, logDeriv (fun s => 1 + ((1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) - 1)) z := by
    rw [← hldinv, hlogeq, hmul, hldg, hlogP]
  have htsum : ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1))
      = Complex.digamma z + γc + 1 / z := by
    have h1 : ∑' n : ℕ, logDeriv (fun s => 1 + ((1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) - 1)) z
        = ∑' n : ℕ, -(1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
      congr 1
      funext n
      rw [logDeriv_one_add_wFactor hz n]
      ring
    rw [h1, tsum_neg] at hmain
    linear_combination hmain
  have h := (summable_digamma_series hz).hasSum
  rwa [htsum] at h


open Complex Filter Topology
open Contour457
variable {w : ℂ}
lemma natp1_ne_zero (hw : 0 < w.re) (n : ℕ) : (n : ℂ) + 1 + w ≠ 0 := by
  intro h
  have he := congrArg Complex.re h
  simp at he
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith
theorem tendsto_harmonic_sub_clog (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
      - Complex.log ((N : ℂ) + 1 + w)) atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  -- split:  [H_N − Real.log(N+1)] − log(1 + w/(N+1))
  have hdecomp : ∀ N : ℕ, (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
      - Complex.log ((N : ℂ) + 1 + w)
      = (((harmonic N : ℚ) : ℝ) - Real.log ((N : ℝ) + 1) : ℝ)
        - Complex.log (1 + w / ((N : ℂ) + 1)) := by
    intro N
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hN1 : (N : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero N
    have hq' : 1 + w / ((N : ℂ) + 1) = ((N : ℂ) + 1 + w) / ((N : ℂ) + 1) := by
      field_simp
    have hq : 1 + w / ((N : ℂ) + 1) ≠ 0 := by
      rw [hq']; exact div_ne_zero (natp1_ne_zero hw N) hN1
    have hlog : Complex.log ((N : ℂ) + 1 + w)
        = Real.log ((N : ℝ) + 1) + Complex.log (1 + w / ((N : ℂ) + 1)) := by
      rw [← Complex.log_ofReal_mul hN hq, hq']
      congr 1
      push_cast
      field_simp
    rw [hlog, harmonic_cast_eq]
    push_cast
    ring
  simp_rw [hdecomp]
  have h1 : Tendsto (fun N : ℕ => ((((harmonic N : ℚ) : ℝ) - Real.log ((N : ℝ) + 1) : ℝ) : ℂ))
      atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log_add_one
  have h2 : Tendsto (fun N : ℕ => Complex.log (1 + w / ((N : ℂ) + 1))) atTop (𝓝 0) := by
    have hq : Tendsto (fun N : ℕ => w / ((N : ℂ) + 1)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have : (fun N : ℕ => ‖w / ((N : ℂ) + 1)‖) = fun N : ℕ => ‖w‖ * (1 / ((N : ℝ) + 1)) := by
        funext N
        rw [norm_div, show ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        ring
      rw [this]
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ‖w‖
    have hcont : ContinuousAt Complex.log 1 := continuousAt_clog (by simp)
    have := hcont.tendsto.comp (by simpa using hq.const_add 1)
    simpa [Function.comp_def] using this
  simpa using h1.sub h2




open Complex Filter Topology
open Contour457
lemma tendsto_log_sub_sum {z : ℂ} (hz : z ∈ Complex.integerComplement) (hre : 0 < z.re) :
    Tendsto (fun N : ℕ => Complex.log ((N : ℂ) + 1 + z) -
      ∑ n ∈ Finset.range N, 1 / (z + n + 1)) atTop (𝓝 (digamma (z+1))) := by
  have hs := (hasSum_digamma_series hz).tendsto_sum_nat
  have hl := tendsto_harmonic_sub_clog hre
  have heq (N : ℕ) : Complex.log ((N : ℂ) + 1 + z) -
      ∑ n ∈ Finset.range N, 1 / (z + n + 1) =
      (∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1))) -
        ((∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1)) - Complex.log ((N : ℂ) + 1 + z)) := by
    rw [Finset.sum_sub_distrib]
    ring
  simp_rw [heq]
  convert hs.sub hl using 1
  rw [digamma_apply_add_one z (by
    intro m hm
    apply hz
    exact ⟨-(m : ℤ), by simpa using hm.symm⟩)]
  ring

open Complex Filter Topology
open Contour457 MeasureTheory intervalIntegral Set


lemma inv_re_vertical (a u : ℝ) :
    (((a : ℂ) + u * I)⁻¹).re = a / (a ^ 2 + u ^ 2) := by
  rw [Complex.inv_re, Complex.normSq_apply]
  simp
  ring

lemma reciprocal_step (v u t : ℝ) (hv : 0 < v) (ht : 0 ≤ t) :
    (v + t) / ((v + t) ^ 2 + u ^ 2) - v / (v ^ 2 + u ^ 2) ≤ t / (8 * v ^ 2) := by
  have h0 : 0 < v ^ 2 + u ^ 2 := by positivity
  have h1 : 0 < (v + t) ^ 2 + u ^ 2 := by positivity
  rw [sub_le_iff_le_add]
  apply (div_le_iff₀ h1).2
  rw [← sub_nonneg]
  have he : (t / (8 * v^2) + v / (v^2 + u^2)) * ((v+t)^2 + u^2) - (v+t) =
      t * ((u^2 - 3*v^2)^2 + (2*v*t+t^2)*(v^2+u^2) + 8*v^3*t) /
        (8*v^2*(v^2+u^2)) := by
    field_simp
    ring
  rw [he]
  positivity

lemma hasDerivAt_log_norm_vertical (a u x : ℝ) (hx : 0 < a + x) :
    HasDerivAt (fun y : ℝ => Real.log ‖((a + y : ℝ) : ℂ) + u * I‖)
      ((a + x) / ((a + x) ^ 2 + u ^ 2)) x := by
  have heq : (fun y : ℝ => Real.log ‖((a + y : ℝ) : ℂ) + u * I‖) =
      fun y => Real.log ((a + y)^2 + u^2) / 2 := by
    funext y
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero,
      Complex.add_im, Complex.mul_im, mul_one, zero_add]
    rw [Real.log_sqrt (by positivity)]
  rw [heq]
  have hd : HasDerivAt (fun y : ℝ => (a + y)^2 + u^2) (2 * (a + x)) x := by
    convert (((hasDerivAt_id x).const_add a).pow 2).add_const (u^2) using 1 <;> simp only [id_eq, Pi.pow_apply] <;> ring
  convert (hd.log (by positivity)).div_const 2 using 1 <;> field_simp <;> ring

lemma log_norm_step (a u : ℝ) (ha : 0 < a) :
    Real.log ‖((a + 1 : ℝ) : ℂ) + u * I‖ - Real.log ‖(a : ℂ) + u * I‖ ≤
      a / (a^2 + u^2) + 1 / (8 * a^2) := by
  let f : ℝ → ℝ := fun x => (a + x) / ((a + x)^2 + u^2)
  have hc : ContinuousOn f (Icc 0 1) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    have : 0 < a + x := by linarith [hx.1]
    positivity
  have hi : IntervalIntegrable f volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa using hc
  have he : ∫ x in (0 : ℝ)..1, f x =
      Real.log ‖((a + 1 : ℝ) : ℂ) + u * I‖ - Real.log ‖(a : ℂ) + u * I‖ := by
    convert integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_log_norm_vertical a u x (by
        have : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
        linarith [this.1])) hi using 1 <;> simp
  rw [← he]
  calc
    (∫ x in (0 : ℝ)..1, f x) ≤ (∫ x in (0 : ℝ)..1, (a / (a^2 + u^2) + 1 / (8 * a^2))) := by
      apply integral_mono_on (by norm_num) hi (continuous_const.intervalIntegrable _ _)
      intro x hx
      have hs := reciprocal_step a u x ha hx.1
      have ht : x / (8 * a^2) ≤ 1 / (8 * a^2) := by gcongr; exact hx.2
      dsimp [f]
      linarith
    _ = a / (a^2 + u^2) + 1 / (8 * a^2) := by simp

lemma reciprocal_square_telescope (v : ℝ) (hv : 1 < v) :
    1 / (8 * v^2) ≤ 1 / (8*(v-1)) - 1 / (8*v) := by
  have hv0 : 0 < v := by linarith
  have hv1 : 0 < v-1 := by linarith
  apply (le_sub_iff_add_le).2
  field_simp
  nlinarith

lemma log_norm_partial_sum_le (a u : ℝ) (ha : 1 < a) (N : ℕ) :
    Real.log ‖((a + N : ℝ) : ℂ) + u*I‖ -
      (∑ n ∈ Finset.range N, (a+n) / ((a+n)^2 + u^2)) ≤
      Real.log ‖(a : ℂ) + u*I‖ + 1/(8*(a-1)) - 1/(8*(a+N-1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hs := log_norm_step (a+N) u (by linarith)
    have ht := reciprocal_square_telescope (a+N) (by linarith)
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show a + ((N : ℝ) + 1) = a + N + 1 by ring]
    have he : a + (N : ℝ) + 1 - 1 = a + N := by ring
    rw [he]
    linarith

/-- `Re ψ(5/2 + iu) ≤ log ‖5/2 + iu‖ + 1/10`: the copied `digamma_re_le` statement moved
from `9/4` to `5/2` (same proof, `a = 5/2`). -/
theorem digamma_re_le_five_half (u : ℝ) :
    (digamma ((5 / 2 : ℂ) + u * I)).re ≤ Real.log ‖(5 / 2 : ℂ) + u * I‖ + 1 / 10 := by
  let z : ℂ := (3/2 : ℂ) + u*I
  have hz : z ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have he := congrArg Complex.re hn
    norm_num [z] at he
    have h1 : (1 : ℝ) < n := by linarith
    have h2 : (n : ℝ) < 2 := by linarith
    have hn1 : (1 : ℤ) < n := by exact_mod_cast h1
    have hn2 : n < (2 : ℤ) := by exact_mod_cast h2
    omega
  have hre : 0 < z.re := by norm_num [z]
  have hw : z+1 = (5/2 : ℂ) + u*I := by dsimp [z]; ring
  have hl := (Complex.continuous_re.tendsto _).comp (tendsto_log_sub_sum hz hre)
  rw [hw] at hl
  apply le_of_tendsto hl
  apply Filter.Eventually.of_forall
  intro N
  have hb := log_norm_partial_sum_le (5/2) u (by norm_num) N
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hp : 0 ≤ 1 / (8 * ((5/2 : ℝ)+N-1)) := by
    have : 0 < (5/2 : ℝ)+N-1 := by linarith
    positivity
  have he : (N : ℂ)+1+z = (((5/2 : ℝ)+N : ℝ) : ℂ) + u*I := by
    dsimp [z]
    push_cast
    ring
  dsimp only [Function.comp_def]
  rw [he]
  simp only [Complex.sub_re, Complex.log_re]
  have hsum : (∑ n ∈ Finset.range N, 1 / (z+n+1)).re =
      ∑ n ∈ Finset.range N, ((5/2 : ℝ)+n) / (((5/2 : ℝ)+n)^2+u^2) := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [show z+(n:ℂ)+1 = ((((5/2 : ℝ)+n) : ℝ) : ℂ)+u*I by dsimp [z]; push_cast; ring,
      one_div, inv_re_vertical]
  rw [hsum]
  norm_num at hb ⊢
  have hinv : 0 ≤ ((5/2 : ℝ)+N-1)⁻¹ := inv_nonneg.mpr (by linarith)
  linarith
open scoped Real

/-! ### An explicit bound for `ψ(1/2 + it)` -/

/-- `1/2 + it` is not an integer. -/
private theorem half_line_mem_integerComplement (t : ℝ) :
    ((1 / 2 : ℂ) + t * I) ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have he : (n : ℝ) = 1 / 2 := by
    have h := congrArg Complex.re hn
    simpa using h
  have h2 : (2 : ℤ) * n = 1 := by
    have hh : (2 : ℝ) * (n : ℝ) = 1 := by rw [he]; norm_num
    exact_mod_cast hh
  omega

/-- The digamma recurrence, taken from `1/2 + it` up to `5/2 + it`. -/
private theorem digamma_half_shift (t : ℝ) :
    (Complex.digamma ((5 / 2 : ℂ) + t * I)).re =
      (Complex.digamma ((1 / 2 : ℂ) + t * I)).re
        + (((1 / 2 : ℂ) + t * I)⁻¹).re + (((3 / 2 : ℂ) + t * I)⁻¹).re := by
  have hs : ∀ m : ℕ, ((1 / 2 : ℂ) + t * I) ≠ -(m : ℂ) := by
    intro m hm
    exact half_line_mem_integerComplement t ⟨-(m : ℤ), by rw [hm]; push_cast; ring⟩
  have h1 := Complex.digamma_apply_add_one ((1 / 2 : ℂ) + t * I) hs
  have e1 : ((1 / 2 : ℂ) + t * I) + 1 = (3 / 2 : ℂ) + t * I := by push_cast; ring
  rw [e1] at h1
  have hs2 : ∀ m : ℕ, ((3 / 2 : ℂ) + t * I) ≠ -(m : ℂ) := by
    intro m hm
    have hh : (3 / 2 : ℝ) + (m : ℝ) = 0 := by
      have h := congrArg Complex.re hm
      simp at h
      linarith
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have h2 := Complex.digamma_apply_add_one ((3 / 2 : ℂ) + t * I) hs2
  have e2 : ((3 / 2 : ℂ) + t * I) + 1 = (5 / 2 : ℂ) + t * I := by push_cast; ring
  rw [e2] at h2
  have r1 := congrArg Complex.re h1
  have r2 := congrArg Complex.re h2
  simp only [Complex.add_re] at r1 r2
  linarith

/-- Upper bound for the real part of `ψ(1/2 + it)`. -/
private theorem digamma_half_re_le (t : ℝ) (ht : 2 ≤ |t|) :
    (Complex.digamma ((1 / 2 : ℂ) + t * I)).re ≤ Real.log (|t| + 3) + 1 / 4 := by
  have h5 := digamma_re_le_five_half t
  have hs := digamma_half_shift t
  have hp1 : 0 ≤ (((1 / 2 : ℂ) + t * I)⁻¹).re := by
    have h := inv_re_vertical (1 / 2) t
    have e : (((1 / 2 : ℝ)) : ℂ) + t * I = (1 / 2 : ℂ) + t * I := by push_cast; ring
    rw [e] at h
    rw [h]
    positivity
  have hp2 : 0 ≤ (((3 / 2 : ℂ) + t * I)⁻¹).re := by
    have h := inv_re_vertical (3 / 2) t
    have e : (((3 / 2 : ℝ)) : ℂ) + t * I = (3 / 2 : ℂ) + t * I := by push_cast; ring
    rw [e] at h
    rw [h]
    positivity
  have harg : ‖(5 / 2 : ℂ) + t * I‖ ≤ |t| + 3 := by
    have hsq : ‖(5 / 2 : ℂ) + t * I‖ ^ 2 = (5 / 2 : ℝ) ^ 2 + t ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have hle : (5 / 2 : ℝ) ^ 2 + t ^ 2 ≤ (|t| + 3) ^ 2 := by
      nlinarith [abs_nonneg t, sq_abs t]
    nlinarith [norm_nonneg ((5 / 2 : ℂ) + t * I)]
  have hpos : (0 : ℝ) < ‖(5 / 2 : ℂ) + t * I‖ := by
    have h := Complex.re_le_norm ((5 / 2 : ℂ) + t * I)
    have h2 : ((5 / 2 : ℂ) + t * I).re = 5 / 2 := by simp
    rw [h2] at h
    linarith
  have hlog : Real.log ‖(5 / 2 : ℂ) + t * I‖ ≤ Real.log (|t| + 3) :=
    Real.log_le_log hpos harg
  linarith

/-- Lower bound for the real part of `ψ(1/2 + it)`, from the sign of the terms of the
partial-fraction series: `1/(n+1) ≥ ℜ 1/(n + 3/2 + it)`. -/
private theorem digamma_half_re_ge (t : ℝ) (ht : 2 ≤ |t|) :
    -(5 / 4 : ℝ) ≤ (Complex.digamma ((1 / 2 : ℂ) + t * I)).re := by
  set z : ℂ := (1 / 2 : ℂ) + t * I with hz
  have hzc : z ∈ Complex.integerComplement := by
    rw [hz]; exact half_line_mem_integerComplement t
  have h := hasSum_digamma_series hzc
  have hterm : ∀ n : ℕ, 0 ≤ ((1 / ((n : ℂ) + 1) - 1 / (z + n + 1) : ℂ)).re := by
    intro n
    have hnorm : ((n : ℝ) + 3 / 2) ≤ ‖z + (n : ℂ) + 1‖ := by
      have h1 := Complex.re_le_norm (z + (n : ℂ) + 1)
      have h2 : (z + (n : ℂ) + 1).re = (n : ℝ) + 3 / 2 := by rw [hz]; simp; ring
      rw [h2] at h1
      linarith
    have hinv : |((1 / (z + n + 1) : ℂ)).re| ≤ 1 / ((n : ℝ) + 3 / 2) := by
      have h2 := Complex.abs_re_le_norm ((1 / (z + (n : ℂ) + 1) : ℂ))
      rw [norm_div, norm_one] at h2
      have hpos : (0 : ℝ) < (n : ℝ) + 3 / 2 := by positivity
      calc |((1 / (z + n + 1) : ℂ)).re| ≤ 1 / ‖z + (n : ℂ) + 1‖ := h2
        _ ≤ 1 / ((n : ℝ) + 3 / 2) := by
            apply one_div_le_one_div_of_le hpos hnorm
    have hA : ((1 / ((n : ℂ) + 1) : ℂ)).re = 1 / ((n : ℝ) + 1) := by
      have e : ((n : ℂ) + 1 : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) + (0 : ℝ) * I := by push_cast; ring
      rw [one_div, e, inv_re_vertical]
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [Complex.sub_re, hA]
    have h4 : (1 / (z + n + 1) : ℂ).re ≤ 1 / ((n : ℝ) + 3 / 2) := le_trans (le_abs_self _) hinv
    have h5 : 1 / ((n : ℝ) + 3 / 2) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    linarith
  have hnonneg : 0 ≤ ∑' n : ℕ, ((1 / ((n : ℂ) + 1) - 1 / (z + n + 1) : ℂ)).re :=
    tsum_nonneg hterm
  have hL : (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z).re
      = ∑' n : ℕ, ((1 / ((n : ℂ) + 1) - 1 / (z + n + 1) : ℂ)).re := by
    rw [← h.tsum_eq]
    exact Complex.reCLM.map_tsum h.summable
  have hzre : (1 / z : ℂ).re ≤ 1 / 2 := by
    have h1 : (1 / z : ℂ).re ≤ ‖(1 / z : ℂ)‖ := Complex.re_le_norm _
    have h2 : ‖(1 / z : ℂ)‖ = 1 / ‖z‖ := by rw [norm_div, norm_one]
    have h3 : (2 : ℝ) ≤ ‖z‖ := by
      have hsq : ‖z‖ ^ 2 = (1 / 2 : ℝ) ^ 2 + t ^ 2 := by
        rw [hz, Complex.sq_norm, Complex.normSq_apply]
        simp
        ring
      nlinarith [norm_nonneg z, abs_nonneg t, sq_abs t]
    have h4 : 1 / ‖z‖ ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num) h3
    linarith
  have hγ : Real.eulerMascheroniConstant ≤ 2 / 3 := le_of_lt Real.eulerMascheroniConstant_lt_two_thirds
  have hEq : (Complex.digamma z).re
      = (∑' n : ℕ, ((1 / ((n : ℂ) + 1) - 1 / (z + n + 1) : ℂ)).re)
        - Real.eulerMascheroniConstant - (1 / z : ℂ).re := by
    rw [← hL]
    simp only [Complex.add_re, Complex.ofReal_re]
    ring
  rw [hEq]
  linarith

/-- Conjugacy of `ψ` on the line `Re s = 1/2`, from the partial-fraction series. -/
private theorem digamma_half_conj (t : ℝ) :
    Complex.digamma (star ((1 / 2 : ℂ) + t * I)) = star (Complex.digamma ((1 / 2 : ℂ) + t * I)) := by
  set z : ℂ := (1 / 2 : ℂ) + t * I with hz
  have hzc : z ∈ Complex.integerComplement := by rw [hz]; exact half_line_mem_integerComplement t
  have hzsc : star z ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    refine hzc ⟨n, ?_⟩
    have h := congrArg star hn
    simpa using h
  have h1 := hasSum_digamma_series hzsc
  have h2 := HasSum.star (hasSum_digamma_series hzc)
  have h2' : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (star z + (n : ℂ) + 1))
      (star (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z)) := by
    convert h2 using 1
    ext n
    simp
  have huniq := h1.unique h2'
  have hs : star (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z)
      = star (Complex.digamma z) + (Real.eulerMascheroniConstant : ℂ) + 1 / star z := by
    simp [star_div₀, star_add, star_one]
  rw [hs] at huniq
  exact add_right_cancel (add_right_cancel huniq)

/-- The imaginary part of `ψ(1/2 + it)` is `(π/2)·tanh(πt)`, hence at most `π/2` in modulus. -/
private theorem digamma_half_im_eq (t : ℝ) :
    (Complex.digamma ((1 / 2 : ℂ) + t * I)).im
      = Real.pi / 2 * Real.tanh (Real.pi * t) := by
  set z : ℂ := (1 / 2 : ℂ) + t * I with hz
  have hzint : ∀ n : ℤ, z ≠ n := by
    intro n hn
    exact half_line_mem_integerComplement t ⟨n, by rw [← hz]; exact hn.symm⟩
  have h1 := Complex.digamma_one_sub hzint
  have h1s : (1 : ℂ) - z = star z := by
    rw [hz]
    simp
    ring
  rw [h1s] at h1
  have hconj : Complex.digamma (star z) = star (Complex.digamma z) := by
    rw [hz]; exact digamma_half_conj t
  rw [hconj] at h1
  have hcos : Complex.cos (π * z) = -(↑(Real.sinh (π * t)) * I) := by
    have e : π * z = (((π / 2 : ℝ)) : ℂ) + ((π * t : ℝ)) * I := by rw [hz]; push_cast; ring
    rw [e, Complex.cos_add, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast
    ring
  have hsin : Complex.sin (π * z) = ((Real.cosh (π * t) : ℝ) : ℂ) := by
    have e : π * z = (((π / 2 : ℝ)) : ℂ) + ((π * t : ℝ)) * I := by rw [hz]; push_cast; ring
    rw [e, Complex.sin_add, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast
    ring
  have hcot : Complex.cot (π * z)
      = (↑(-(Real.sinh (π * t) / Real.cosh (π * t))) : ℂ) * I := by
    rw [Complex.cot_eq_cos_div_sin, hcos, hsin]
    rw [show (-(↑(Real.sinh (π * t)) * I) : ℂ) = (↑(-(Real.sinh (π * t))) : ℂ) * I by
      push_cast; ring]
    rw [show ((↑(-(Real.sinh (π * t))) : ℂ) * I) / (↑(Real.cosh (π * t)) : ℂ)
        = ((↑(-(Real.sinh (π * t))) : ℂ) / ↑(Real.cosh (π * t))) * I by ring]
    rw [← Complex.ofReal_div]
    ring
  have hstar : (star (Complex.digamma z)).im = -(Complex.digamma z).im := by simp
  have him := congrArg Complex.im h1
  rw [hcot, hstar] at him
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_I_re, Complex.mul_I_im, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, zero_mul, add_zero, sub_zero, Complex.neg_re, Complex.neg_im] at him
  have htanh : Real.sinh (π * t) / Real.cosh (π * t) = Real.tanh (π * t) :=
    (Real.tanh_eq_sinh_div_cosh (π * t)).symm
  rw [hz] at him
  rw [htanh] at him
  have hX : (π : ℝ) * -(Real.tanh (π * t)) = -(π * Real.tanh (π * t)) := by ring
  rw [hX] at him
  have h2 : ((1 / 2 : ℂ) + (t : ℂ) * I).digamma.im = (π * Real.tanh (π * t)) / 2 := by
    linarith
  rw [h2]
  ring

/-- `‖ψ(1/2 + it)‖ ≤ log(|t| + 3) + 9/4`. -/
private theorem norm_digamma_half_le (t : ℝ) (ht : 2 ≤ |t|) :
    ‖Complex.digamma ((1 / 2 : ℂ) + t * I)‖ ≤ Real.log (|t| + 3) + 9 / 4 := by
  have hup := digamma_half_re_le t ht
  have hlow := digamma_half_re_ge t ht
  have him := digamma_half_im_eq t
  have hlog5 : (1 : ℝ) ≤ Real.log (|t| + 3) := by
    have h1 : Real.log 5 ≤ Real.log (|t| + 3) := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
    have h2 : (1 : ℝ) ≤ Real.log 5 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    linarith
  have hre : |(Complex.digamma ((1 / 2 : ℂ) + t * I)).re| ≤ Real.log (|t| + 3) + 1 / 4 := by
    rw [abs_le]
    exact ⟨by linarith, hup⟩
  have himb : |(Complex.digamma ((1 / 2 : ℂ) + t * I)).im| ≤ Real.pi / 2 := by
    rw [him, abs_mul]
    have h1 : |Real.tanh (Real.pi * t)| ≤ 1 := le_of_lt (Real.abs_tanh_lt_one _)
    have h2 : |Real.pi / 2| = Real.pi / 2 := abs_of_pos (by positivity)
    rw [h2]
    nlinarith [Real.pi_pos]
  calc ‖Complex.digamma ((1 / 2 : ℂ) + t * I)‖
      ≤ |(Complex.digamma ((1 / 2 : ℂ) + t * I)).re|
        + |(Complex.digamma ((1 / 2 : ℂ) + t * I)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (Real.log (|t| + 3) + 1 / 4) + Real.pi / 2 := by linarith
    _ ≤ Real.log (|t| + 3) + 9 / 4 := by linarith [Real.pi_lt_four]

/-- `|tan(-π/4 + iy)| = 1`: at `x = -π/4` the moduli of `sin` and `cos` coincide, because
`sin²x = cos²x` and `cosh²y - sinh²y = 1`. -/
private theorem norm_tan_neg_pi_div_four (y : ℝ) :
    ‖Complex.tan ((-(π / 4) : ℝ) + y * I)‖ ≤ 1 := by
  have hsin : ‖Complex.sin ((-(π / 4) : ℝ) + y * I)‖ ^ 2
      = (Real.sin (-(π / 4))) ^ 2 * (Real.cosh y) ^ 2
        + (Real.cos (-(π / 4))) ^ 2 * (Real.sinh y) ^ 2 := by
    have e : Complex.sin ((-(π / 4) : ℝ) + y * I)
        = (((Real.sin (-(π / 4)) * Real.cosh y : ℝ)) : ℂ)
          + (((Real.cos (-(π / 4)) * Real.sinh y : ℝ)) : ℂ) * I := by
      rw [Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
        ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
      push_cast
      ring
    rw [e, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im, mul_zero, mul_one,
      sub_zero, add_zero, Complex.neg_re, Complex.neg_im, zero_mul,
      Complex.sinh_ofReal_re, Complex.cosh_ofReal_re, Complex.sinh_ofReal_im,
      Complex.cosh_ofReal_im]
    ring
  have hcos : ‖Complex.cos ((-(π / 4) : ℝ) + y * I)‖ ^ 2
      = (Real.cos (-(π / 4))) ^ 2 * (Real.cosh y) ^ 2
        + (Real.sin (-(π / 4))) ^ 2 * (Real.sinh y) ^ 2 := by
    have e : Complex.cos ((-(π / 4) : ℝ) + y * I)
        = (((Real.cos (-(π / 4)) * Real.cosh y : ℝ)) : ℂ)
          + (-((Real.sin (-(π / 4)) * Real.sinh y : ℝ))) * I := by
      rw [Complex.cos_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
        ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
      push_cast
      ring
    rw [e, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im, mul_zero, mul_one,
      sub_zero, add_zero, Complex.neg_re, Complex.neg_im, zero_mul,
      Complex.sinh_ofReal_re, Complex.cosh_ofReal_re, Complex.sinh_ofReal_im,
      Complex.cosh_ofReal_im]
    ring
  have hsq : (Real.sin (-(π / 4))) ^ 2 = (Real.cos (-(π / 4))) ^ 2 := by
    rw [Real.sin_neg, Real.cos_neg, neg_sq, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hcosne : Complex.cos ((-(π / 4) : ℝ) + y * I) ≠ 0 := by
    intro h
    rw [h] at hcos
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hcos
    have h1 : 0 < (Real.cos (-(π / 4))) ^ 2 := by
      rw [Real.cos_neg, Real.cos_pi_div_four]
      have hs : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      positivity
    have h2 : 0 < (Real.cos (-(π / 4))) ^ 2 * (Real.cosh y) ^ 2 :=
      mul_pos h1 (by positivity)
    have h3 : 0 ≤ (Real.sin (-(π / 4))) ^ 2 * (Real.sinh y) ^ 2 := by positivity
    linarith
  rw [Complex.tan_eq_sin_div_cos, norm_div]
  have heq : ‖Complex.sin ((-(π / 4) : ℝ) + y * I)‖
      = ‖Complex.cos ((-(π / 4) : ℝ) + y * I)‖ := by
    have h1 : ‖Complex.sin ((-(π / 4) : ℝ) + y * I)‖ ^ 2
        = ‖Complex.cos ((-(π / 4) : ℝ) + y * I)‖ ^ 2 := by
      rw [hsin, hcos, hsq]
    nlinarith [norm_nonneg (Complex.sin ((-(π / 4) : ℝ) + y * I)),
      norm_nonneg (Complex.cos ((-(π / 4) : ℝ) + y * I))]
  have hpos : 0 < ‖Complex.cos ((-(π / 4) : ℝ) + y * I)‖ := norm_pos_iff.2 hcosne
  rw [heq, div_self (ne_of_gt hpos)]

/-! ### The pointwise bound on the left line, from the functional equation -/
open MeasureTheory

/-! ### An explicit bound for `ζ'/ζ` on the line `Re s = 3/2` -/

/-- `log 3 ≤ 1.1`. -/
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
/-- `‖ζ'/ζ(-1/2 + it)‖ ≤ log(|t| + 3) + 21/2` for `|t| ≥ 2`: the functional equation in
logarithmic-derivative form, the `Re s = 3/2` bound, the digamma bound of the previous
section and the exact tangent modulus `|tan(-π/4 + iy)| = 1`. -/
private theorem logDeriv_left_half_le (t : ℝ) (ht : 2 ≤ |t|) :
    ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * I)‖ ≤ Real.log (|t| + 3) + 21 / 2 := by
  set s : ℂ := (-1 / 2 : ℂ) + t * I with hs
  have hsre : s.re = -(1 / 2) := by rw [hs]; simp; norm_num
  have hsint : ∀ n : ℤ, s ≠ n := by
    intro n hn
    have h := congrArg Complex.re hn
    simp at h
    rw [hsre] at h
    have h2 : (2 : ℤ) * n = -1 := by
      have hh : (2 : ℝ) * (n : ℝ) = -1 := by rw [← h]; norm_num
      exact_mod_cast hh
    omega
  have hz : riemannZeta s ≠ 0 := by
    rw [hs]; simpa using LeanLab.PNTPort.ZetaZeros.zeta_left_ne t
  have hFE := logDeriv_riemannZeta_one_sub hsint hz
  have h1 : ‖logDeriv riemannZeta (1 - s)‖ ≤ 4 := by
    have e : (1 : ℂ) - s = (3 / 2 : ℂ) + (-t) * I := by rw [hs]; push_cast; ring
    rw [e]
    simpa using logDeriv_three_half_le (-t)
  have h2 : ‖Complex.log (2 * π)‖ ≤ 2 := by
    rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by nlinarith [Real.pi_gt_three]))]
    exact LeanLab.PNTPort.ZetaZeros.log_two_pi_le
  have h3 : ‖Complex.digamma s‖ ≤ Real.log (|t| + 3) + 11 / 4 := by
    have hsne : ∀ m : ℕ, s ≠ -(m : ℂ) := by
      intro m hm
      have h := congrArg Complex.re hm
      simp at h
      rw [hsre] at h
      have h2 : (2 : ℤ) * (m : ℤ) = 1 := by
        have hh : (2 : ℝ) * (m : ℝ) = 1 := by linarith
        exact_mod_cast hh
      omega
    have hrec := Complex.digamma_apply_add_one s hsne
    have e : s + 1 = (1 / 2 : ℂ) + t * I := by rw [hs]; push_cast; ring
    rw [e] at hrec
    have hb := norm_digamma_half_le t ht
    have hsnorm : ‖s⁻¹‖ ≤ 1 / 2 := by
      have h2 : (2 : ℝ) ≤ ‖s‖ := by
        have hsq : ‖s‖ ^ 2 = (1 / 2 : ℝ) ^ 2 + t ^ 2 := by
          rw [hs, Complex.sq_norm, Complex.normSq_apply]
          simp
          ring
        nlinarith [norm_nonneg s, abs_nonneg t, sq_abs t]
      rw [norm_inv]
      simpa [one_div] using one_div_le_one_div_of_le (a := 2) (b := ‖s‖) (by norm_num) h2
    have hsplit : ‖Complex.digamma s‖
        ≤ ‖Complex.digamma ((1 / 2 : ℂ) + t * I)‖ + ‖s⁻¹‖ := by
      have hEq2 : Complex.digamma s = Complex.digamma ((1 / 2 : ℂ) + t * I) - s⁻¹ := by
        rw [hrec]; ring
      rw [hEq2]
      exact norm_sub_le _ _
    linarith
  have h4 : ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ ≤ π / 2 := by
    have e : π * s / 2 = ((-(π / 4) : ℝ) + ((π * t / 2 : ℝ)) * I) := by
      rw [hs]; push_cast; ring
    rw [e, norm_mul]
    have ht1 : ‖Complex.tan ((-(π / 4) : ℝ) + ((π * t / 2 : ℝ)) * I)‖ ≤ 1 :=
      norm_tan_neg_pi_div_four (π * t / 2)
    have hp : ‖((π : ℂ) / 2)‖ = π / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      norm_num
    rw [hp]
    nlinarith [Real.pi_pos]
  rw [hFE]
  calc ‖-logDeriv riemannZeta (1 - s) + Complex.log (2 * π) - Complex.digamma s
        + (π : ℂ) / 2 * Complex.tan (π * s / 2)‖
      ≤ ‖logDeriv riemannZeta (1 - s)‖ + ‖Complex.log (2 * π)‖ + ‖Complex.digamma s‖
        + ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (by rw [norm_neg])) le_rfl)) le_rfl)
    _ ≤ 4 + 2 + (Real.log (|t| + 3) + 11 / 4) + π / 2 := by linarith
    _ ≤ Real.log (|t| + 3) + 21 / 2 := by linarith [Real.pi_lt_d2]



/-! ### The long-range energy budget from the pointwise bound -/

/-- The weight is the logarithmic derivative divided by `s = -1/2 + it`. -/
private theorem principalLogWeight_norm_sq (t : ℝ) :
    ‖principalLogWeight t‖ ^ 2
      = ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * I)‖ ^ 2 / (1 / 4 + t ^ 2) := by
  have hnorm : ‖(-1 / 2 : ℂ) + t * I‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  unfold principalLogWeight
  rw [norm_div, div_pow, hnorm]

/-- The long range is the union of the two half lines. -/
private theorem sq_long_region :
    ({t : ℝ | 2 < |t|} : Set ℝ) = Set.Ioi 2 ∪ Set.Iio (-2) := by
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Ioi, Set.mem_Iio]
  constructor
  · intro h
    rcases lt_abs.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact lt_abs.mpr (Or.inl h)
    · exact lt_abs.mpr (Or.inr (by linarith))

/-- The primitive of `(log x + 23/2)^2 / x^2` on the positive axis. -/
private theorem hasDerivAt_majorant_primitive (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -((Real.log y) ^ 2 + 25 * Real.log y + 629 / 4) / y)
      ((Real.log x + 23 / 2) ^ 2 / x ^ 2) x := by
  have hL : HasDerivAt (fun y : ℝ => Real.log y) x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hmul : HasDerivAt (fun y : ℝ => Real.log y * Real.log y)
      (x⁻¹ * Real.log x + Real.log x * x⁻¹) x := hL.mul hL
  have hN : HasDerivAt (fun y : ℝ => Real.log y * Real.log y + 25 * Real.log y + 629 / 4)
      (x⁻¹ * Real.log x + Real.log x * x⁻¹ + 25 * x⁻¹) x := by
    have h1 : HasDerivAt (fun y : ℝ => Real.log y * Real.log y + 25 * Real.log y)
        (x⁻¹ * Real.log x + Real.log x * x⁻¹ + 25 * x⁻¹) x :=
      hmul.add (hL.const_mul 25)
    exact h1.add_const (629 / 4)
  have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx.ne'
  have h := hN.neg.mul hinv
  have hxne : x ≠ 0 := hx.ne'
  convert h using 1
  · funext y
    simp only [Pi.mul_apply, Pi.neg_apply]
    ring
  · field_simp
    simp only [Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
    ring

/-- The primitive tends to `0` at infinity. -/
private theorem tendsto_majorant_primitive :
    Tendsto (fun y : ℝ => -((Real.log y) ^ 2 + 25 * Real.log y + 629 / 4) / y)
      atTop (𝓝 0) := by
  have h12 : Tendsto (fun y : ℝ => Real.log y / y ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  have h1 : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) := by
    simpa using (isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  have hs : Tendsto (fun y : ℝ => (Real.log y) ^ 2 / y) atTop (𝓝 0) := by
    have h2 : Tendsto (fun y : ℝ => (Real.log y / y ^ (1 / 2 : ℝ)) ^ 2) atTop (𝓝 0) := by
      simpa using h12.pow 2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [div_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt (le_of_lt hy)]
  have hinv : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hev : (fun y : ℝ => -((Real.log y) ^ 2 + 25 * Real.log y + 629 / 4) / y)
      =ᶠ[atTop] fun y =>
        -((Real.log y) ^ 2 / y) - 25 * (Real.log y / y) - (629 / 4) * y⁻¹ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    field_simp
    ring
  rw [Filter.tendsto_congr' hev]
  have hfin := ((hs.neg).sub (h1.const_mul 25)).sub (hinv.const_mul (629 / 4))
  simpa using hfin

/-- Integrability of the majorant on `(2, ∞)`. -/
private theorem integrableOn_majorant :
    IntegrableOn (fun x : ℝ => (Real.log x + 23 / 2) ^ 2 / x ^ 2) (Set.Ioi 2) := by
  have hmaj : IntegrableOn (fun x : ℝ => 256 * x ^ (-(3 / 2) : ℝ)) (Set.Ioi 2) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 / 2) : ℝ) < -1) (by norm_num : (0:ℝ) < 2)
      ).const_mul 256
  have hcont : ContinuousOn (fun x : ℝ => (Real.log x + 23 / 2) ^ 2 / x ^ 2) (Set.Ioi (2:ℝ)) := by
    apply ContinuousOn.div
    · refine ContinuousOn.pow ?_ 2
      exact (Real.continuousOn_log.mono (fun y hy => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith [Set.mem_Ioi.mp hy])).add continuousOn_const
    · exact ContinuousOn.pow continuousOn_id 2
    · intro x hx
      have hx0 : (0:ℝ) < x := by linarith [Set.mem_Ioi.mp hx]
      positivity
  refine hmaj.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx2 : (2 : ℝ) < x := Set.mem_Ioi.mp hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hlog : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
    have hh := Real.log_le_rpow_div (le_of_lt hx0) (by norm_num : (0:ℝ) < 1 / 4)
    have h2 : x ^ (1 / 4 : ℝ) / (1 / 4) = 4 * x ^ (1 / 4 : ℝ) := by ring
    rwa [h2] at hh
  have hsum : Real.log x + 23 / 2 ≤ 16 * x ^ (1 / 4 : ℝ) := by linarith
  have hlogpos : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hpos : (0 : ℝ) ≤ Real.log x + 23 / 2 := by linarith
  have hsq : (Real.log x + 23 / 2) ^ 2 ≤ 256 * x ^ (1 / 2 : ℝ) := by
    have h16 : (0:ℝ) ≤ 16 * x ^ (1 / 4 : ℝ) := by positivity
    have e : (16 * x ^ (1 / 4 : ℝ)) ^ 2 = 256 * x ^ (1 / 2 : ℝ) := by
      rw [mul_pow,
        show (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) by
          rw [sq, ← Real.rpow_add hx0]
          norm_num]
      norm_num
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg (le_of_lt hx0)]
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  have e2 : x ^ 2 = x ^ (3 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hx0]
    norm_num
  rw [div_le_iff₀ hx2, e2]
  have e3 : 256 * (x ^ (3 / 2 : ℝ))⁻¹ * (x ^ (3 / 2 : ℝ) * x ^ (1 / 2 : ℝ))
      = 256 * x ^ (1 / 2 : ℝ) := by
    field_simp
  rw [e3]
  exact hsq

/-- `∫_2^∞ (log x + 23/2)^2/x^2 ≤ 87.6`. -/
private theorem integral_Ioi_two_majorant :
    ∫ x in Set.Ioi (2 : ℝ), (Real.log x + 23 / 2) ^ 2 / x ^ 2 ≤ 87.6 := by
  have hderiv : ∀ x ∈ Set.Ici (2 : ℝ),
      HasDerivAt (fun y : ℝ => -((Real.log y) ^ 2 + 25 * Real.log y + 629 / 4) / y)
        ((Real.log x + 23 / 2) ^ 2 / x ^ 2) x :=
    fun x hx => hasDerivAt_majorant_primitive x (by linarith [Set.mem_Ici.mp hx])
  have key := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv integrableOn_majorant
    tendsto_majorant_primitive
  rw [key]
  have hlog := Real.log_two_lt_d9
  have hpos2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsq2 : (Real.log 2) ^ 2 ≤ 0.4806 := by nlinarith
  have e : (0 : ℝ) - -((Real.log 2) ^ 2 + 25 * Real.log 2 + 629 / 4) / 2
      = ((Real.log 2) ^ 2 + 25 * Real.log 2 + 629 / 4) / 2 := by ring
  rw [e]
  linarith


/-! ### Closing the long-range leaf -/

/-- Pointwise comparison on the long range. -/
private theorem principalLogWeight_sq_le_majorant (t : ℝ) (ht : 2 < |t|) :
    ‖principalLogWeight t‖ ^ 2 ≤ (Real.log |t| + 23 / 2) ^ 2 / t ^ 2 := by
  have ht2 : (2 : ℝ) ≤ |t| := le_of_lt ht
  have ht0 : (0 : ℝ) < |t| := by linarith
  have htne : t ≠ 0 := by
    intro h0
    rw [h0] at ht
    simp at ht
    linarith
  have hb := logDeriv_left_half_le t ht2
  have hlog : Real.log (|t| + 3) ≤ Real.log |t| + 1 := by
    have hexp : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hle : |t| + 3 ≤ Real.exp 1 * |t| := by nlinarith
    calc Real.log (|t| + 3) ≤ Real.log (Real.exp 1 * |t|) :=
          Real.log_le_log (by positivity) hle
      _ = Real.log |t| + 1 := by
          rw [Real.log_mul (Real.exp_pos 1).ne' ht0.ne', Real.log_exp]
          ring
  have hsq : ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * I)‖ ^ 2
      ≤ (Real.log |t| + 23 / 2) ^ 2 := by
    have h1 : (0 : ℝ) ≤ ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * I)‖ := norm_nonneg _
    have hl : (0 : ℝ) < Real.log |t| := Real.log_pos (by linarith)
    nlinarith
  rw [principalLogWeight_norm_sq]
  refine le_trans (div_le_div_of_nonneg_right hsq (by positivity)) ?_
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  nlinarith [sq_nonneg t]

/-! ### The two half-line energies -/

/-- The energy over the positive half line, from the pointwise majorant and the explicit
primitive `∫_2^∞ (log x + 23/2)²/x² = ((log 2)² + 25 log 2 + 629/4)/2 ≤ 87.6`. -/
private theorem principal_log_weight_sq_Ioi_two :
    (∫ t in Set.Ioi (2 : ℝ), ‖principalLogWeight t‖ ^ 2) ≤ 87.6 := by
  have hint : Integrable (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) :=
    MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two (by norm_num)
  have hmono : (∫ t in Set.Ioi (2 : ℝ), ‖principalLogWeight t‖ ^ 2)
      ≤ ∫ x in Set.Ioi (2 : ℝ), (Real.log x + 23 / 2) ^ 2 / x ^ 2 := by
    refine setIntegral_mono_on hint.integrableOn integrableOn_majorant measurableSet_Ioi ?_
    intro x hx
    have hx2 : (2 : ℝ) < x := hx
    have h0 : (0 : ℝ) < x := by linarith
    have habs : |x| = x := abs_of_pos h0
    have h := principalLogWeight_sq_le_majorant x (by rw [habs]; exact hx2)
    rwa [habs] at h
  linarith [integral_Ioi_two_majorant]

/-- The energy over the negative half line.  The substitution `t ↦ -x` carries it to the
positive half line, where the same majorant applies. -/
private theorem principal_log_weight_sq_Iio_neg_two :
    (∫ t in Set.Iio (-2 : ℝ), ‖principalLogWeight t‖ ^ 2) ≤ 87.6 := by
  have hint : Integrable (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) :=
    MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two (by norm_num)
  have hcomp : Integrable (fun x : ℝ => ‖principalLogWeight (-x)‖ ^ 2) := by
    simpa using hint.comp_neg
  have hstep : (∫ t in Set.Iio (-2 : ℝ), ‖principalLogWeight t‖ ^ 2)
      = ∫ x in Set.Ioi (2 : ℝ), ‖principalLogWeight (-x)‖ ^ 2 := by
    rw [← integral_Iic_eq_integral_Iio]
    exact (integral_comp_neg_Ioi 2 (fun t : ℝ => ‖principalLogWeight t‖ ^ 2)).symm
  rw [hstep]
  have hmono : (∫ x in Set.Ioi (2 : ℝ), ‖principalLogWeight (-x)‖ ^ 2)
      ≤ ∫ x in Set.Ioi (2 : ℝ), (Real.log x + 23 / 2) ^ 2 / x ^ 2 := by
    refine setIntegral_mono_on hcomp.integrableOn integrableOn_majorant measurableSet_Ioi ?_
    intro x hx
    have hx2 : (2 : ℝ) < x := hx
    have h0 : (0 : ℝ) < x := by linarith
    have habs : |x| = x := abs_of_pos h0
    have hsq : (-x) ^ 2 = x ^ 2 := by ring
    have h := principalLogWeight_sq_le_majorant (-x) (by rw [abs_neg, habs]; exact hx2)
    rw [abs_neg, habs, hsq] at h
    exact h
  linarith [integral_Ioi_two_majorant]

end DigammaBudget

/-! ### The leaves of the unit, unchanged -/
open Real MeasureTheory Contour457

/-!
Splitting the numerical square energy budget of `Decomp457b.principal_log_weight_budget`
into two smaller steps.

The bound is the size of the square energy of the logarithmic derivative weight on the
left contour, the norm of `logDeriv riemannZeta` at `-1/2 + it` divided by the norm of
`-1/2 + it`. The split cuts the vertical line at height two and bounds the two pieces of
the energy separately:

* the short range `|t| ≤ 2`, where the weight is largest but the interval is short,
* the long range `2 < |t|`, where only the decay of the weight is paid for.

The two bounds add up to 210, and `210 ≤ (6.01 * sqrt (2 * pi)) ^ 2` because
`2 * pi > 6`, so the square root bound of the split theorem follows by monotonicity of
the square root. No prime sum, no zero sum and no scale appears in either step.
-/


open Real MeasureTheory Contour457

/-- The short range comparison from a uniform pointwise square bound. -/
private theorem principal_log_weight_sq_short_of_pointwise
    (hpoint : ∀ t : ℝ, |t| ≤ 2 → ‖principalLogWeight t‖ ^ 2 ≤ 5) :
    (∫ t in {t : ℝ | |t| ≤ 2}, ‖principalLogWeight t‖ ^ 2) ≤ 20 := by
  classical
  have hset : ({t : ℝ | |t| ≤ 2} : Set ℝ) = Set.Icc (-2) 2 := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
  have hmeas : MeasurableSet ({t : ℝ | |t| ≤ 2} : Set ℝ) := by
    rw [hset]
    exact measurableSet_Icc
  have hint : Integrable (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) :=
    MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two (by norm_num)
  have hconst : IntegrableOn (fun _ : ℝ => (5 : ℝ))
      ({t : ℝ | |t| ≤ 2} : Set ℝ) volume := by
    rw [hset]
    exact integrableOn_const measure_Icc_lt_top.ne
  have hmono := MeasureTheory.setIntegral_mono_on hint.integrableOn hconst hmeas
    (fun t ht => hpoint t ht)
  rw [hset, setIntegral_const] at hmono
  rw [Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul] at hmono
  norm_num at hmono ⊢
  rw [← hset] at hmono
  exact hmono

/-- LEAF. The short range step: the square energy of the logarithmic derivative weight
over `|t| ≤ 2` is at most twenty. This is the piece where the weight is largest and the
interval is short, and it carries the whole numerical size of the small range. -/
theorem principal_log_weight_sq_short :
    (∫ t in {t : ℝ | |t| ≤ 2}, ‖principalLogWeight t‖ ^ 2) ≤ 20 := by
  exact principal_log_weight_sq_short_of_leaves

/-- LEAF. The long range step: the square energy of the logarithmic derivative weight
over `2 < |t|` is at most one hundred and ninety. This is the decay step, where the
weight falls off and only the length of the two half lines is paid for. -/
theorem principal_log_weight_sq_long :
    (∫ t in {t : ℝ | 2 < |t|}, ‖principalLogWeight t‖ ^ 2) ≤ 190 := by
  classical
  have hint : Integrable (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) :=
    MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two (by norm_num)
  have hdisj : Disjoint (Set.Ioi (2 : ℝ)) (Set.Iio (-2)) := by
    rw [Set.disjoint_left]
    intro x hx hy
    rw [Set.mem_Ioi] at hx
    rw [Set.mem_Iio] at hy
    linarith
  rw [DigammaBudget.sq_long_region,
    setIntegral_union hdisj measurableSet_Iio hint.integrableOn hint.integrableOn]
  linarith [DigammaBudget.principal_log_weight_sq_Ioi_two,
    DigammaBudget.principal_log_weight_sq_Iio_neg_two]

/-- The square energy budget, assembled from the two range bounds. The line is cut at
height two, the two pieces add to the whole energy, and the total 210 is below
`(6.01 * sqrt (2 * pi)) ^ 2 = 6.01 ^ 2 * (2 * pi) > 6.01 ^ 2 * 6`. -/
theorem principal_log_weight_budget_split :
    sqrt (∫ t : ℝ, ‖principalLogWeight t‖ ^ 2) ≤ 6.01 * sqrt (2 * π) := by
  classical
  have hset : ({t : ℝ | |t| ≤ 2} : Set ℝ) = Set.Icc (-2) 2 := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
  have hmeas : MeasurableSet ({t : ℝ | |t| ≤ 2} : Set ℝ) := by
    rw [hset]
    exact measurableSet_Icc
  have hcompl : ({t : ℝ | |t| ≤ 2} : Set ℝ)ᶜ = {t : ℝ | 2 < |t|} := by
    ext t
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, abs_le, not_and_or, not_le, lt_abs]
    constructor
    · rintro (h | h)
      · right; linarith
      · left; linarith
    · rintro (h | h)
      · right; linarith
      · left; linarith
  have hint : Integrable (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) :=
    MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two (by norm_num)
  have hsplit := integral_add_compl (f := fun t : ℝ => ‖principalLogWeight t‖ ^ 2) hmeas hint
  have htotal : (∫ t : ℝ, ‖principalLogWeight t‖ ^ 2) ≤ 210 := by
    rw [← hsplit, hcompl]
    linarith [principal_log_weight_sq_short, principal_log_weight_sq_long]
  have hsq : (6.01 * sqrt (2 * π)) ^ 2 = 6.01 ^ 2 * (2 * π) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hsix : (6 : ℝ) < 2 * π := by
    have h := Real.pi_gt_three
    linarith
  have hbig : (210 : ℝ) ≤ (6.01 * sqrt (2 * π)) ^ 2 := by
    have h601 : (6.01 : ℝ) ^ 2 = 36.1201 := by norm_num
    rw [hsq, h601]
    nlinarith [hsix]
  calc sqrt (∫ t : ℝ, ‖principalLogWeight t‖ ^ 2)
      ≤ sqrt ((6.01 * sqrt (2 * π)) ^ 2) := Real.sqrt_le_sqrt (le_trans htotal hbig)
    _ = 6.01 * sqrt (2 * π) := Real.sqrt_sq (by positivity)

end LeanLab.HelfgottMajor.Decomp457b

#print axioms LeanLab.HelfgottMajor.Decomp457b.principal_log_weight_budget_split
