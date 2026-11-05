/-
Gallagher 1970 p.334 displays 21 and 22.
Source https://doi.org/10.1007/bf01403187
AI wrote this Lean code. Codex task335. Goldbach is open.
-/
import LeanLab.Linnik.Decomp335c

open Complex MeasureTheory Finset
open scoped Classical LSeries.notation
open LeanLab.Linnik.Decomp1532b LeanLab.Linnik.Decomp1532b2

namespace LeanLab.Linnik.Decomp335a

/-- Gallagher p.334 display 22. The arithmetic series norm is exactly the
normalized logarithmic derivative norm in the right half plane. -/
theorem poisson_norm_eq_derivative_norm {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (k : ℕ) {r : ℝ} (hr : 0 < r) (v : ℝ) :
    ‖∑' n : ℕ, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) /
      (n : ℂ) ^ (1 + I * v)) * (poissonKernel k (r * Real.log n) : ℂ)‖ =
      (r ^ k / (k.factorial : ℝ)) *
        ‖iteratedDeriv k (fun z => -deriv χ.LFunction z / χ.LFunction z)
          (1 + r + I * v)‖ := by
  rw [← normalized_log_series_eq_poisson]
  have hs : 1 < (1 + (r : ℂ) + I * v).re := by simp; linarith
  rw [iterated_neg_logDeriv_eq_LSeries χ k hs]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- Gallagher p.334 display 22. A derivative lower bound supplies the
arithmetic lower bound by an exact identity. No zero premise is needed. -/
theorem poisson_lower_of_derivative_lower {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (k : ℕ) {r D η : ℝ} (hr : 0 < r) (hD : 0 < D) (v : ℝ)
    (h : η * (k.factorial : ℝ) / (D ^ k * r ^ (k + 1)) ≤
      ‖iteratedDeriv k (fun z => -deriv χ.LFunction z / χ.LFunction z)
        (1 + r + I * v)‖) :
    η / (D ^ k * r) ≤
      ‖∑' n : ℕ, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) /
        (n : ℂ) ^ (1 + I * v)) * (poissonKernel k (r * Real.log n) : ℂ)‖ := by
  rw [poisson_norm_eq_derivative_norm χ k hr v]
  have hh := mul_le_mul_of_nonneg_left h
    (show 0 ≤ r ^ k / (k.factorial : ℝ) by positivity)
  convert hh using 1
  simp only [pow_succ]
  field_simp
  <;> ring

/-- Gallagher p.334 translating the shifted logarithmic derivative back to
minus L prime over L preserves the norm of every derivative. -/
theorem shifted_logDeriv_norm_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (k : ℕ) (r v : ℝ) :
    ‖iteratedDeriv k (logDeriv (LeanLab.PNTPort.DirichletZF.fShift χ v)) ((r : ℂ) - 1 / 2)‖ =
      ‖iteratedDeriv k (fun z => -deriv χ.LFunction z / χ.LFunction z) (1 + r + I * v)‖ := by
  have hfun : logDeriv (LeanLab.PNTPort.DirichletZF.fShift χ v) =
      (fun z => logDeriv χ.LFunction (z + ((3 : ℂ) / 2 + I * v))) := by
    funext z
    change deriv (fun w => χ.LFunction (w + ((3 : ℂ) / 2 + I * v))) z /
      χ.LFunction (z + ((3 : ℂ) / 2 + I * v)) = _
    rw [deriv_comp_add_const]
    rfl
  rw [hfun, iteratedDeriv_comp_add_const]
  have hpoint : ((r : ℂ) - 1 / 2) + ((3 : ℂ) / 2 + I * v) = 1 + r + I * v := by ring
  dsimp only
  rw [hpoint]
  have hneg : (fun z => -deriv χ.LFunction z / χ.LFunction z) =
      (fun z => -logDeriv χ.LFunction z) := by funext z; simp [logDeriv_apply, neg_div]
  rw [hneg, iteratedDeriv_fun_neg, norm_neg]

/-- Gallagher p.334 display 22 for every nonprincipal character in the global
height scale. This includes local logarithmic scales below one. -/
theorem nonprincipal_poisson_global : ∃ E : ℝ, 1 ≤ E ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ v r : ℝ,
        |v| ≤ T → 0 < r → r ≤ 1 / 1600 → 1 ≤ r * Real.log T →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * v)‖ ≤ r) →
        ∀ M : ℕ, E * r * Real.log T ≤ M →
          ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
            (1 / 200 : ℝ) / ((100 : ℝ) ^ k * r) ≤
              ‖∑' n : ℕ, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) /
                (n : ℂ) ^ (1 + I * v)) * (poissonKernel k (r * Real.log n) : ℂ)‖ := by
  obtain ⟨E, hE, hlarge⟩ := LeanLab.Linnik.Decomp335c.nonprincipal_large_logDeriv_global
  refine ⟨E, hE, ?_⟩
  intro T hT q hq hqT χ hχ v r hv hr hrhi hscale hz M hM
  obtain ⟨k, hklo, hkhi, hk⟩ := hlarge T hT q hqT χ hχ v r hv hr hrhi hscale hz M hM
  rw [shifted_logDeriv_norm_eq] at hk
  refine ⟨k, hklo, hkhi, poisson_lower_of_derivative_lower χ k hr (by norm_num) v ?_⟩
  convert hk using 1
  simp only [mul_pow, pow_succ]
  field_simp
  <;> ring

/-- Gallagher 1970 p.334 display 21 and the derivative lower bound
immediately before display 22, restricted to principal characters.
There is no arithmetic series, smoothing kernel, finite window or integral.
The height exclusion and the differentiated finite Euler factors are retained. -/
theorem principal_large_logarithmic_derivative :
    ∃ r₀ E D η : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ E ∧ 1 ≤ D ∧ 0 < η ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, χ = 1 → ∀ v r : ℝ,
        |v| ≤ T → 2 ≤ |v| → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ M : ℕ, E * r * Real.log T ≤ M →
          ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
            η * (k.factorial : ℝ) / (D ^ k * r ^ (k + 1)) ≤
              ‖iteratedDeriv k (fun z => -deriv χ.LFunction z / χ.LFunction z)
                (1 + r + I * v)‖ := by
  obtain ⟨Eζ, hEζ, hzetaLarge⟩ := LeanLab.Linnik.Decomp335c.zeta_large_logDeriv_global
  refine ⟨1 / 1600, max Eζ 1200, 100, 1 / 400,
    by norm_num, by norm_num, hEζ.trans (le_max_left _ _), by norm_num, by norm_num, ?_⟩
  intro T hT q hq hqT χ hχ v r hv hvlo hrlo hrhi hz M hM
  subst χ
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hr : 0 < r := (one_div_pos.mpr hlog).trans_le hrlo
  have hscale : 1 ≤ r * Real.log T := by
    have hh := mul_le_mul_of_nonneg_right hrlo hlog.le
    have he : (1 / Real.log T) * Real.log T = 1 := by field_simp
    rwa [he] at hh
  have hMζ : Eζ * r * Real.log T ≤ M := by
    have hh := mul_le_mul_of_nonneg_right (le_max_left Eζ 1200) (mul_nonneg hr.le hlog.le)
    nlinarith
  have hroot : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ‖ρ - (1 + I * v)‖ ≤ r := by
    obtain ⟨ρ, hρ, hnear⟩ := hz
    have hreabs := (Complex.abs_re_le_norm (ρ - (1 + v * I))).trans hnear
    have himabs := (Complex.abs_im_le_norm (ρ - (1 + v * I))).trans hnear
    have hre : 1 / 2 ≤ ρ.re := by
      norm_num at hreabs
      have hh := (abs_le.mp hreabs).1
      linarith
    have hρne : ρ ≠ 1 := by
      intro he
      rw [he] at himabs
      norm_num at himabs
      linarith
    have hprod : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-ρ))) ≠ 0 := by
      apply prod_ne_zero_iff.mpr
      intro p hp
      have hnorm := LeanLab.Linnik.Decomp335c.norm_prime_cpow_neg_le (Nat.prime_of_mem_primeFactors hp) hre
      intro he
      have hone : (p : ℂ) ^ (-ρ) = 1 := (sub_eq_zero.mp he).symm
      rw [hone, norm_one] at hnorm
      norm_num at hnorm
    change DirichletCharacter.LFunctionTrivChar q ρ = 0 at hρ
    rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hρne] at hρ
    have hζ : riemannZeta ρ = 0 := (mul_eq_zero.mp hρ).resolve_left hprod
    exact ⟨ρ, hζ, by simpa only [mul_comm (v : ℂ) I] using hnear⟩
  obtain ⟨k, hklo, hkhi, hkζ⟩ := hzetaLarge T v r hT hvlo hv hr hrhi hscale hroot M hMζ
  let s : ℂ := 1 + r + I * v
  let e : ℂ → ℂ := fun z => ∑ p ∈ q.primeFactors,
    (Real.log p : ℂ) * (p : ℂ) ^ (-z) / (1 - (p : ℂ) ^ (-z))
  have hs : 1 < s.re := by dsimp [s]; norm_num; linarith
  have hsne : s ≠ 1 := by intro he; rw [he] at hs; norm_num at hs
  have heζ :
      ‖iteratedDeriv k (logDeriv (fun w : ℂ => riemannZeta (w + 3 / 2 + I * v))) ((r : ℂ) - 1 / 2)‖ =
        ‖iteratedDeriv k (fun z => -deriv riemannZeta z / riemannZeta z) s‖ := by
    have hh := shifted_logDeriv_norm_eq (1 : DirichletCharacter ℂ 1) k r v
    have hshift : LeanLab.PNTPort.DirichletZF.fShift (1 : DirichletCharacter ℂ 1) v =
        (fun w : ℂ => riemannZeta (w + 3 / 2 + I * v)) := by
      funext w
      change (1 : DirichletCharacter ℂ 1).LFunction (w + ((3 : ℂ) / 2 + I * v)) = _
      rw [DirichletCharacter.LFunction_modOne_eq]
      congr 1
      ring
    rw [hshift] at hh
    simpa only [DirichletCharacter.LFunction_modOne_eq, s] using hh
  rw [heζ] at hkζ
  have heq : (fun z => -deriv (1 : DirichletCharacter ℂ q).LFunction z /
      (1 : DirichletCharacter ℂ q).LFunction z) =ᶠ[nhds s]
        (fun z => -deriv riemannZeta z / riemannZeta z - e z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    have hzne : z ≠ 1 := by intro he; rw [he] at hz; norm_num at hz
    have hh := LeanLab.Linnik.Decomp335c.principal_logDeriv_eq_zeta_add_euler q
      (by linarith : 1 / 2 ≤ z.re) hzne (riemannZeta_ne_zero_of_one_lt_re hz)
    simpa only [e, logDeriv_apply, neg_add, neg_div, sub_eq_add_neg] using congrArg (fun w : ℂ => -w) hh
  have hζan : AnalyticAt ℂ (fun z => -deriv riemannZeta z / riemannZeta z) s :=
    ((analyticAt_riemannZeta hsne).deriv.neg).div (analyticAt_riemannZeta hsne)
      (riemannZeta_ne_zero_of_one_lt_re hs)
  have hean : AnalyticAt ℂ e s :=
    LeanLab.Linnik.Decomp335c.analyticAt_euler_log_correction q (by linarith)
  have hder := heq.iteratedDeriv_eq k
  rw [iteratedDeriv_fun_sub hζan.contDiffAt hean.contDiffAt] at hder
  have hEuler := LeanLab.Linnik.Decomp335c.iteratedDeriv_euler_log_correction_le q k
    (s := s) hs.le
  have hlogq : Real.log q ≤ Real.log T :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)) hqT
  have hErr : ‖iteratedDeriv k e s‖ ≤ (k.factorial : ℝ) * 3 * Real.log T * 4 ^ k := by
    apply hEuler.trans
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlogq (show 0 ≤ (k.factorial : ℝ) * 3 by positivity))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) k)
    convert hh using 1 <;> ring
  have h1200 : 1200 * r * Real.log T ≤ (k : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (le_max_right Eζ 1200) (mul_nonneg hr.le hlog.le)
    have hk : (M : ℝ) ≤ k := by exact_mod_cast hklo
    nlinarith
  have habs := reciprocal_pole_error_absorbed (C := 6) (massLog := Real.log T) hr
    (show 200 * 6 * r * Real.log T ≤ (k : ℝ) by nlinarith)
  have hp : (4 : ℝ) ^ k ≤ 1 / (200 * r) ^ k := by
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 200 * r) k)).mpr
    rw [← mul_pow]
    exact pow_le_one₀ (by positivity) (by linarith)
  have hquarter : ‖iteratedDeriv k e s‖ ≤ (k.factorial : ℝ) / (4 * (100 * r) ^ (k + 1)) := by
    apply hErr.trans
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ (k.factorial : ℝ) * 3 * Real.log T by positivity)
    apply hh.trans
    convert mul_le_mul_of_nonneg_left habs (show 0 ≤ (k.factorial : ℝ) / 2 by positivity) using 1 <;> ring
  have htri : ‖iteratedDeriv k (fun z => -deriv riemannZeta z / riemannZeta z) s‖ ≤
      ‖iteratedDeriv k (fun z => -deriv (1 : DirichletCharacter ℂ q).LFunction z /
        (1 : DirichletCharacter ℂ q).LFunction z) s‖ + ‖iteratedDeriv k e s‖ := by
    calc
      _ = ‖iteratedDeriv k (fun z => -deriv (1 : DirichletCharacter ℂ q).LFunction z /
          (1 : DirichletCharacter ℂ q).LFunction z) s + iteratedDeriv k e s‖ := by
            rw [hder, sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have htarget : (k.factorial : ℝ) / (4 * (100 * r) ^ (k + 1)) ≤
      ‖iteratedDeriv k (fun z => -deriv (1 : DirichletCharacter ℂ q).LFunction z /
        (1 : DirichletCharacter ℂ q).LFunction z) s‖ := by
    have he : (k.factorial : ℝ) / (2 * (100 * r) ^ (k + 1)) =
        2 * ((k.factorial : ℝ) / (4 * (100 * r) ^ (k + 1))) := by ring
    rw [he] at hkζ
    linarith
  refine ⟨k, hklo, hkhi, ?_⟩
  convert htarget using 1
  simp only [mul_pow, pow_succ]
  field_simp
  <;> ring

/-- Gallagher p.334 monotonicity of the detector constants.
The numerator decreases and the exponential denominator increases. -/
theorem detector_constant_mono {η η' D D' r : ℝ} (k : ℕ)
    (hη : η ≤ η') (hη' : 0 ≤ η') (hD : 1 ≤ D) (hDD' : D ≤ D') (hr : 0 < r) :
    η / (D' ^ k * r) ≤ η' / (D ^ k * r) := by
  have hD0 : 0 < D := by linarith
  have hD'0 : 0 < D' := hD0.trans_le hDD'
  calc
    η / (D' ^ k * r) ≤ η' / (D' ^ k * r) :=
      div_le_div_of_nonneg_right hη (by positivity)
    _ ≤ η' / (D ^ k * r) :=
      div_le_div_of_nonneg_left hη' (by positivity)
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hD0.le hDD' k) hr.le)

/-- Gallagher p.334 display 22. Exact sealed series statement assembled from
the principal derivative estimate and the global nonprincipal detector. -/
theorem poisson_series_detector_of_turan
    (hpower : ∀ n M : ℕ, 0 < n → n ≤ M → ∀ z : Fin n → ℂ, (∃ i, 1 ≤ ‖z i‖) →
      ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧ (1 / 50 : ℝ) ^ M ≤ ‖∑ i, z i ^ ν‖) :
    ∃ r₀ E D η : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ E ∧ 1 ≤ D ∧ 0 < η ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ M : ℕ, E * r * Real.log T ≤ M →
          ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
            η / (D ^ k * r) ≤
              ‖∑' n : ℕ, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) /
                (n : ℂ) ^ (1 + I * v)) * (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)‖ := by
  obtain ⟨rₚ, Eₚ, Dₚ, ηₚ, hrₚ, hrₚhi, hEₚ, hDₚ, hηₚ, hprincipal⟩ :=
    principal_large_logarithmic_derivative
  obtain ⟨Eₙ, hEₙ, hnonprincipal⟩ := nonprincipal_poisson_global
  refine ⟨min rₚ (1 / 1600), max Eₚ Eₙ, max Dₚ 100, min ηₚ (1 / 200),
    lt_min hrₚ (by norm_num), (min_le_left _ _).trans hrₚhi,
    hEₚ.trans (le_max_left _ _), hDₚ.trans (le_max_left _ _),
    lt_min hηₚ (by norm_num), ?_⟩
  intro T hT q hq hqT χ v r hv hχ hrlo hrhi hz M hM
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hr : 0 < r := (one_div_pos.mpr hlog).trans_le hrlo
  have hscale : 1 ≤ r * Real.log T := by
    have hh := mul_le_mul_of_nonneg_right hrlo hlog.le
    have he : (1 / Real.log T) * Real.log T = 1 := by field_simp
    rwa [he] at hh
  have hMp : Eₚ * r * Real.log T ≤ M := by
    have hh := mul_le_mul_of_nonneg_right (le_max_left Eₚ Eₙ) (mul_nonneg hr.le hlog.le)
    nlinarith
  have hMn : Eₙ * r * Real.log T ≤ M := by
    have hh := mul_le_mul_of_nonneg_right (le_max_right Eₚ Eₙ) (mul_nonneg hr.le hlog.le)
    nlinarith
  by_cases hp : χ = 1
  · obtain ⟨k, hklo, hkhi, hk⟩ := hprincipal T hT q hqT χ hp v r hv (hχ hp) hrlo
      (hrhi.trans (min_le_left _ _)) hz M hMp
    refine ⟨k, hklo, hkhi, ?_⟩
    exact (detector_constant_mono k (min_le_left _ _) hηₚ.le hDₚ (le_max_left _ _) hr).trans
      (poisson_lower_of_derivative_lower χ k hr (by linarith) v hk)
  · have hz' : ∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * v)‖ ≤ r := by
      simpa only [mul_comm (v : ℂ) I] using hz
    obtain ⟨k, hklo, hkhi, hk⟩ := hnonprincipal T hT q hqT χ hp v r hv hr
      (hrhi.trans (min_le_right _ _)) hscale hz' M hMn
    refine ⟨k, hklo, hkhi, ?_⟩
    exact (detector_constant_mono k (min_le_right _ _) (by norm_num) (by norm_num : (1 : ℝ) ≤ 100)
      (le_max_right _ _) hr).trans hk

end LeanLab.Linnik.Decomp335a
