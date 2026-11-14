/-
P0069, pages 24 to 27, endpoint smoothing for display 4.1. CODEX task528.
The taper Mellin kernel has rapid decay on every fixed vertical line.
This does not supply the arithmetic mean value for the lower sieve family.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp528a
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

namespace LeanLab.BHP1997.Decomp528d
open Classical Complex MeasureTheory Filter Set Decomp528a
open scoped FourierTransform SchwartzMap Topology

/-- Pages 24 to 27, the weighted logarithmic profile of the explicit taper. -/
noncomputable def logTaper (σ v : ℝ) : ℂ :=
  Real.exp (-σ * v) • (taper 1 (Real.exp (-v)) : ℂ)

/-- Pages 24 to 27, the weighted logarithmic taper is infinitely differentiable. -/
theorem logTaper_contDiff (σ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (logTaper σ) := by
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => taper 1 (Real.exp (-v))) :=
    (taper_contDiff 1).comp (by fun_prop)
  unfold logTaper
  exact (show ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => Real.exp (-σ * v)) by fun_prop).smul
    (Complex.ofRealCLM.contDiff.comp ht)

/-- Pages 24 to 27, the weighted logarithmic taper has compact support. -/
theorem logTaper_hasCompactSupport (σ : ℝ) : HasCompactSupport (logTaper σ) := by
  have he : (2 : ℝ) < Real.exp 2 := by
    have h := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
    linarith
  have hn : Real.exp (-2) < 1 / 2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (inv_lt_inv₀ (Real.exp_pos 2) (by norm_num : (0 : ℝ) < 2)).mpr he
  refine HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)) ?_
  intro v hv
  have hv' : v < -2 ∨ 2 < v := by
    simpa only [mem_Icc, not_and_or, not_le] using hv
  have hz : taper 1 (Real.exp (-v)) = 0 := by
    apply taper_zero (by norm_num : (0 : ℝ) < 1)
    rcases hv' with hv' | hv'
    · right
      have h := Real.exp_le_exp.mpr (by linarith : (2 : ℝ) ≤ -v)
      linarith
    · left
      have h := Real.exp_le_exp.mpr (by linarith : -v ≤ (-2 : ℝ))
      linarith
  simp only [logTaper, hz, Complex.ofReal_zero, smul_zero]

/-- Pages 24 to 27, the explicit weighted logarithmic taper as a Schwartz function. -/
noncomputable def logTaperSchwartz (σ : ℝ) : SchwartzMap ℝ ℂ :=
  (logTaper_hasCompactSupport σ).toSchwartzMap (logTaper_contDiff σ)

/-- Pages 24 to 27, the taper Mellin integral converges at every complex parameter. -/
theorem taper_mellinConvergent (s : ℂ) :
    MellinConvergent (fun u : ℝ => (taper 1 u : ℂ)) s := by
  have hc : Continuous (fun u : ℝ => (taper 1 u : ℂ)) :=
    Complex.continuous_ofReal.comp (taper_contDiff 1).continuous
  have ht : (fun u : ℝ => (taper 1 u : ℂ)) =O[atTop] (fun u : ℝ => u ^ (-(s.re + 1))) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with u hu
    have hz : taper 1 u = 0 := taper_zero (by norm_num) (Or.inr (by linarith))
    simp [hz]
  have hb : (fun u : ℝ => (taper 1 u : ℂ)) =O[𝓝[>] 0] (fun u : ℝ => u ^ (-(s.re - 1))) := by
    apply Asymptotics.IsBigO.of_bound 1
    have he : ∀ᶠ u : ℝ in 𝓝 (0 : ℝ), u < 1 / 2 :=
      eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with u hu
    have hz : taper 1 u = 0 := taper_zero (by norm_num) (Or.inl hu.le)
    simp [hz]
  exact mellinConvergent_of_isBigO_rpow (hc.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    ht (by linarith) hb (by linarith)

/-- Pages 24 to 27, exact Mellin to Fourier normalization of the smooth taper. -/
theorem taper_mellin_eq_fourier (σ t : ℝ) :
    mellin (fun u : ℝ => (taper 1 u : ℂ)) ((σ : ℂ) + t * I) =
      (𝓕 (logTaperSchwartz σ)) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  rfl

/-- Pages 24 to 27, the taper Mellin kernel decays faster than every inverse power
on each fixed vertical line. The estimate keeps the smooth endpoint cancellation. -/
theorem taper_mellin_rapid_decay (σ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      |t| ^ n * ‖mellin (fun u : ℝ => (taper 1 u : ℂ)) ((σ : ℂ) + t * I)‖ ≤ C := by
  let S := 𝓕 (logTaperSchwartz σ)
  let C := (2 * Real.pi) ^ n * (SchwartzMap.seminorm ℂ n 0) S
  refine ⟨C, mul_nonneg (by positivity) (apply_nonneg _ _), ?_⟩
  intro t
  rw [taper_mellin_eq_fourier]
  have h := SchwartzMap.norm_pow_mul_le_seminorm ℂ S n (t / (2 * Real.pi))
  rw [Real.norm_eq_abs] at h
  have hp : |t| ^ n = (2 * Real.pi) ^ n * |t / (2 * Real.pi)| ^ n := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), div_pow]
    field_simp
  rw [hp]
  calc
    _ = (2 * Real.pi) ^ n * (|t / (2 * Real.pi)| ^ n * ‖S (t / (2 * Real.pi))‖) := by ring
    _ ≤ C := mul_le_mul_of_nonneg_left h (by positivity)

/-- Pages 24 to 27, the explicit logarithmic kernel is not the zero function. -/
theorem logTaper_at_zero (σ : ℝ) : logTaper σ 0 = 1 := by
  have ht : taper 1 1 = 1 := taper_one (by norm_num) (by norm_num) (by norm_num)
  simp [logTaper, ht]

/-- Pages 24 to 27, the taper Mellin kernel is absolutely integrable on every vertical line. -/
theorem taper_verticalIntegrable (σ : ℝ) :
    Complex.VerticalIntegrable (mellin (fun u : ℝ => (taper 1 u : ℂ))) σ := by
  unfold Complex.VerticalIntegrable
  simp_rw [taper_mellin_eq_fourier]
  exact (SchwartzMap.integrable (𝓕 (logTaperSchwartz σ))).comp_div
    (by positivity : 2 * Real.pi ≠ 0)

/-- Pages 24 to 27, exact convergent Mellin inversion for the explicit taper. -/
theorem taper_mellin_inversion (σ : ℝ) {r : ℝ} (hr : 0 < r) :
    mellinInv σ (mellin (fun u : ℝ => (taper 1 u : ℂ))) r = (taper 1 r : ℂ) := by
  apply mellinInv_mellin_eq σ _ hr (taper_mellinConvergent (σ : ℂ)) (taper_verticalIntegrable σ)
  exact Complex.continuous_ofReal.continuousAt.comp (taper_contDiff 1).continuous.continuousAt

/-- Pages 24 to 27, Mellin inversion on the imaginary axis with its exact normalization. -/
theorem taper_inverse_integral {r : ℝ} (hr : 0 < r) :
    (taper 1 r : ℂ) = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, (r : ℂ) ^ (-((t : ℂ) * I)) *
        mellin (fun u : ℝ => (taper 1 u : ℂ)) ((t : ℂ) * I) := by
  have h := (taper_mellin_inversion 0 hr).symm
  simpa only [mellinInv, Complex.ofReal_zero, zero_add, smul_eq_mul,
    Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul,
    Complex.ofReal_ofNat] using h

/-- Pages 24 to 27, every term in the finite Mellin smoothing identity is integrable. -/
theorem taper_kernel_term_integrable {r : ℝ} (hr : 0 < r) (c : ℂ) :
    Integrable (fun t : ℝ => (r : ℂ) ^ (-((t : ℂ) * I)) *
      mellin (fun u : ℝ => (taper 1 u : ℂ)) ((t : ℂ) * I) * c) := by
  have hK : Integrable (fun t : ℝ => mellin (fun u : ℝ => (taper 1 u : ℂ)) ((t : ℂ) * I)) := by
    simpa only [Complex.VerticalIntegrable, Complex.ofReal_zero, zero_add] using taper_verticalIntegrable 0
  have hp : Continuous (fun t : ℝ => (r : ℂ) ^ (-((t : ℂ) * I))) :=
    (show Continuous (fun t : ℝ => -((t : ℂ) * I)) by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hr.ne'))
  have hb : ∀ t : ℝ, ‖(r : ℂ) ^ (-((t : ℂ) * I))‖ ≤ 1 := by
    intro t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
    simp
  exact (hK.bdd_mul hp.aestronglyMeasurable (Filter.Eventually.of_forall hb)).mul_const c

/-- Pages 24 to 27, exact finite Mellin smoothing without taking prefix norms.
The support contains only positive indices. Every interchange uses absolute integrability. -/
theorem finite_taper_mellin (S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k)
    (c : ℕ → ℂ) {x : ℝ} (hx : 0 < x) :
    (∑ k ∈ S, (taper x k : ℂ) * c k) =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        mellin (fun u : ℝ => (taper 1 u : ℂ)) ((t : ℂ) * I) *
          ∑ k ∈ S, (((k : ℝ) / x : ℝ) : ℂ) ^ (-((t : ℂ) * I)) * c k := by
  have hkpos (k : ℕ) (hk : k ∈ S) : 0 < (k : ℝ) / x :=
    div_pos (by exact_mod_cast hS k hk) hx
  have he (t : ℝ) : mellin (fun u : ℝ => (taper 1 u : ℂ)) ((t : ℂ) * I) *
        (∑ k ∈ S, (((k : ℝ) / x : ℝ) : ℂ) ^ (-((t : ℂ) * I)) * c k) =
      ∑ k ∈ S, (((k : ℝ) / x : ℝ) : ℂ) ^ (-((t : ℂ) * I)) *
        mellin (fun u : ℝ => (taper 1 u : ℂ)) ((t : ℂ) * I) * c k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_rw [he]
  rw [integral_finsetSum S (fun k hk => taper_kernel_term_integrable (hkpos k hk) (c k)),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_mul_const]
  have h := taper_inverse_integral (hkpos k hk)
  have ht : taper 1 ((k : ℝ) / x) = taper x k := by simp only [taper, div_one]
  rw [ht] at h
  rw [h]
  ring

/-- Pages 24 to 27, the convergent finite smoothing identity yields its norm estimate. -/
theorem finite_taper_mellin_norm_le (S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k)
    (c : ℕ → ℂ) {x : ℝ} (hx : 0 < x) :
    ‖∑ k ∈ S, (taper x k : ℂ) * c k‖ ≤
      (1 / (2 * Real.pi)) * ∫ t : ℝ,
        ‖mellin (fun u : ℝ => (taper 1 u : ℂ)) ((t : ℂ) * I)‖ *
          ‖∑ k ∈ S, (((k : ℝ) / x : ℝ) : ℂ) ^ (-((t : ℂ) * I)) * c k‖ := by
  have hn : ‖(1 / (2 * Real.pi) : ℂ)‖ = (1 / (2 * Real.pi) : ℝ) := by
    norm_num [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [finite_taper_mellin S hS c hx, norm_mul, hn]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [norm_mul] using norm_integral_le_integral_norm
    (fun t : ℝ => mellin (fun u : ℝ => (taper 1 u : ℂ)) ((t : ℂ) * I) *
      ∑ k ∈ S, (((k : ℝ) / x : ℝ) : ℂ) ^ (-((t : ℂ) * I)) * c k)

/-- Pages 24 to 27, positive real bases give the exact Mellin frequency shift. -/
theorem mellin_phase_dirichlet {r x : ℝ} (hr : 0 < r) (hx : 0 < x)
    (s : ℂ) (t : ℝ) (c : ℂ) :
    ((r / x : ℝ) : ℂ) ^ (-((t : ℂ) * I)) * (c / (r : ℂ) ^ s) =
      (x : ℂ) ^ ((t : ℂ) * I) * (c / (r : ℂ) ^ (s + (t : ℂ) * I)) := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hrs : (r : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hrC)
  have hrt : (r : ℂ) ^ ((t : ℂ) * I) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hrC)
  have hxt : (x : ℂ) ^ ((t : ℂ) * I) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hxC)
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hr.le hx.le]
  simp only [Complex.cpow_neg]
  rw [Complex.cpow_add _ _ hrC]
  field_simp [hrs, hrt, hxt]
  <;> ring

/-- Pages 24 to 27, exact Mellin smoothing for a finite Dirichlet polynomial.
The polynomial is evaluated at shifted height inside the absolutely convergent integral. -/
theorem finite_dirichlet_taper_mellin (S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k)
    (c : ℕ → ℂ) {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (∑ k ∈ S, (taper x k : ℂ) * c k / (k : ℂ) ^ s) =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        mellin (fun u : ℝ => (taper 1 u : ℂ)) ((t : ℂ) * I) *
          (x : ℂ) ^ ((t : ℂ) * I) *
          ∑ k ∈ S, c k / (k : ℂ) ^ (s + (t : ℂ) * I) := by
  calc
    _ = ∑ k ∈ S, (taper x k : ℂ) * (c k / (k : ℂ) ^ s) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        mellin (fun u : ℝ => (taper 1 u : ℂ)) ((t : ℂ) * I) *
          ∑ k ∈ S, (((k : ℝ) / x : ℝ) : ℂ) ^ (-((t : ℂ) * I)) * (c k / (k : ℂ) ^ s) :=
      finite_taper_mellin S hS _ hx
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      have he : (∑ k ∈ S, (((k : ℝ) / x : ℝ) : ℂ) ^ (-((t : ℂ) * I)) * (c k / (k : ℂ) ^ s)) =
          (x : ℂ) ^ ((t : ℂ) * I) * ∑ k ∈ S, c k / (k : ℂ) ^ (s + (t : ℂ) * I) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        simpa only [Complex.ofReal_natCast] using
          mellin_phase_dirichlet (by exact_mod_cast hS k hk : (0 : ℝ) < k) hx s t (c k)
      rw [he]
      ring

end LeanLab.BHP1997.Decomp528d
