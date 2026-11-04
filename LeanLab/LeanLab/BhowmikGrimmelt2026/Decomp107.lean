/-
Decomposition of Lemma 7.6 and its written proof on page 29 of P0029.
The original cited declaration is unchanged.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Archimedean84
import LeanLab.BhowmikGrimmelt2026.Scaling107
import LeanLab.BhowmikGrimmelt2026.Integration107
import LeanLab.BhowmikGrimmelt2026.Amplitude107
import LeanLab.BhowmikGrimmelt2026.Poisson

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- LEAF. Page 29 display 7.21. Substitute v = u1 + u2 and sigma = u1 / v. -/
theorem archimedean_coordinates107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) {N T : ℝ} (hT : 1 ≤ T) (hTN : T ≤ N)
    (ρ₁ ρ₂ : ℂ) (hρ₁ : 0 < ρ₁.re) (hρ₁' : ρ₁.re ≤ 1)
    (hρ₂ : 0 < ρ₂.re) (hρ₂' : ρ₂.re ≤ 1) :
    Iphi ϕ G N T ρ₁ ρ₂ = ∫ v in Set.Ioi (0 : ℝ),
      (v : ℂ) ^ (ρ₁ + ρ₂ - 1) * (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂ := by
  have hN : 0 < N := by linarith
  let f : ℝ → ℂ := fun u => (ϕ (u / N) : ℂ) * (u : ℂ) ^ (ρ₁ - 1)
  let g : ℝ → ℂ := fun u => (ϕ (u / N) : ℂ) * (u : ℂ) ^ (ρ₂ - 1)
  let h : ℝ → ℂ := fun v => (GT G T (N - v) : ℂ)
  have hz (ρ : ℂ) (u : ℝ) (hu : u ≤ 0) :
      (ϕ (u / N) : ℂ) * (u : ℂ) ^ (ρ - 1) = 0 := by
    have hzero : ϕ (u / N) = 0 := by
      by_contra hn
      have hs := (hϕ.supp (subset_tsupport ϕ hn)).1
      have : u / N ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu hN.le
      linarith
    simp [hzero]
  have hGc : Continuous G := hG.smooth.continuous
  have hh : Continuous h := by dsimp [h, GT]; fun_prop
  have hconv := positive_convolution107 f g h
    (continuous_cutoff_cpow107 hϕ hN ρ₁) (continuous_cutoff_cpow107 hϕ hN ρ₂) hh
    (compact_cutoff_cpow107 hϕ hN ρ₁) (compact_cutoff_cpow107 hϕ hN ρ₂)
    (hz ρ₁) (hz ρ₂)
  calc
    _ = ∫ u in Set.Ioi (0 : ℝ), ∫ w in Set.Ioi (0 : ℝ), f u * g w * h (u + w) := by
      unfold Iphi
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      apply setIntegral_congr_fun measurableSet_Ioi
      intro w hw
      dsimp [f, g, h]
      rw [show N - u - w = N - (u + w) by ring]
      push_cast
      ring
    _ = ∫ v in Set.Ioi (0 : ℝ), (∫ u in (0 : ℝ)..v, f u * g (v - u)) * h v := hconv
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      have hinner : (∫ u in (0 : ℝ)..v, f u * g (v - u)) =
          (v : ℂ) ^ (ρ₁ + ρ₂ - 1) * Jphi ϕ N v ρ₁ ρ₂ := by
        rw [← beta_scaling107 ϕ N hv ρ₁ ρ₂]
        apply intervalIntegral.integral_congr
        intro u hu
        dsimp [f, g]
        push_cast
        ring
      rw [hinner]
      dsimp [h]
      ring

/-! ## Helpers for the closing of `archimedean_opposite107` (display 7.19, opposite signs).

Repeated integration by parts in `sigma`: the phase derivative is bounded below by
`(|im rho_1| + |im rho_2|) / 25` on `[1/5, 4/5]`, so `k` integrations by parts give a
pointwise bound on `Jphi` with a `(|im rho_1| + |im rho_2|) ^ (-k)` decay, and the outer
integral is bounded by the mass-one kernel `GT`. AI wrote the Lean code. Goldbach is open. -/

section

open Filter

open scoped Topology

/-! ## (0) The kernel facts of the target file, restated locally

`integrable_GT150`, `integral_GT150` and `nonneg_GT150` live in `Decomp107.lean` itself, so the
wip file cannot import them; the same three proofs are re-run here under `107` names. -/

/-- The dilated kernel is integrable. -/
private theorem integrable_GT107 {G : ℝ → ℝ} (hG : IsMajorWeight G) {T : ℝ} (hT : 0 < T) :
    Integrable (GT G T) :=
  (GT_contDiff hG.smooth T).continuous.integrable_of_hasCompactSupport
    (GT_hasCompactSupport hG.supp hT)

/-- The dilated kernel has mass one. -/
private theorem integral_GT107 {G : ℝ → ℝ} (hG : IsMajorWeight G) {T : ℝ} (hT : 0 < T) :
    (∫ x : ℝ, GT G T x) = 1 := by
  simp [GT, integral_const_mul, Measure.integral_comp_div, abs_of_pos hT,
    hG.integral_one, hT.ne']

/-- The positive dilation preserves nonnegativity. -/
private theorem nonneg_GT107 {G : ℝ → ℝ} (hG : IsMajorWeight G) {T : ℝ} (hT : 0 < T) (x : ℝ) :
    0 ≤ GT G T x :=
  mul_nonneg (inv_nonneg.mpr hT.le) (hG.nonneg _)

/-! ## (1) The sigma weight as modulus times phase

Display 7.21 has the inner integral
`J_v = ∫_0^1 phi (v s / N) phi (v (1-s) / N) s^(rho_1-1) (1-s)^(rho_2-1) ds`.
On `0 < s < 1` the two complex powers are `exp ((rho_i - 1) log)` with a real
logarithm, so their phases are `im rho_i * log (s)` and `im rho_i * log (1-s)`. -/

/-- A complex power of a positive real, split into modulus and phase. -/
private theorem cpow_split107 {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ (z - 1) =
      ((x ^ (z.re - 1) : ℝ) : ℂ) * Complex.exp (Complex.I * ((z.im * Real.log x : ℝ) : ℂ)) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hmod : ((x ^ (z.re - 1) : ℝ) : ℂ) =
      Complex.exp (((z.re - 1) * Real.log x : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos hx, Complex.ofReal_exp, mul_comm]
  calc (x : ℂ) ^ (z - 1) = Complex.exp (((Real.log x : ℝ) : ℂ) * (z - 1)) := by
        rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le]
    _ = Complex.exp (((z.re - 1) * Real.log x : ℝ) +
          Complex.I * ((z.im * Real.log x : ℝ) : ℂ)) := by
        congr 1
        apply Complex.ext <;>
          simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im] <;> ring
    _ = Complex.exp (((z.re - 1) * Real.log x : ℝ)) *
          Complex.exp (Complex.I * ((z.im * Real.log x : ℝ) : ℂ)) := Complex.exp_add _ _
    _ = ((x ^ (z.re - 1) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((z.im * Real.log x : ℝ) : ℂ)) := by rw [hmod]

/-- The modulus of the sigma weight of display 7.21, cutoffs included. -/
private noncomputable def amp107 (ϕ : ℝ → ℝ) (N v : ℝ) (ρ₁ ρ₂ : ℂ) (σ : ℝ) : ℝ :=
  σ ^ (ρ₁.re - 1) * (1 - σ) ^ (ρ₂.re - 1) * (ϕ (v * σ / N) * ϕ (v * (1 - σ) / N))

/-- The sigma phase of display 7.21. -/
private noncomputable def phase107 (ρ₁ ρ₂ : ℂ) (σ : ℝ) : ℝ :=
  ρ₁.im * Real.log σ + ρ₂.im * Real.log (1 - σ)

/-- On `0 < s < 1` the sigma integrand of 7.21 factors into modulus and phase. -/
private theorem integrand_split107 {ϕ : ℝ → ℝ} {N v : ℝ} (ρ₁ ρ₂ : ℂ) {σ : ℝ}
    (h0 : 0 < σ) (h1 : σ < 1) :
    ((ϕ (v * σ / N) * ϕ (v * (1 - σ) / N) : ℝ) : ℂ) * (σ : ℂ) ^ (ρ₁ - 1) *
        ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1) =
      (amp107 ϕ N v ρ₁ ρ₂ σ : ℂ) *
        Complex.exp (Complex.I * ((phase107 ρ₁ ρ₂ σ : ℝ) : ℂ)) := by
  have h1' : (0 : ℝ) < 1 - σ := by linarith
  have hphase : Complex.I * ((phase107 ρ₁ ρ₂ σ : ℝ) : ℂ) =
      Complex.I * ((ρ₁.im * Real.log σ : ℝ) : ℂ) +
        Complex.I * ((ρ₂.im * Real.log (1 - σ) : ℝ) : ℂ) := by
    rw [phase107]
    push_cast
    ring_nf
  rw [cpow_split107 h0 ρ₁, cpow_split107 h1' ρ₂, hphase, Complex.exp_add]
  simp only [amp107]
  push_cast
  ring_nf

/-- The inner integral of 7.21 in modulus-phase form, over the open interval. -/
private theorem Jphi_phase107 {ϕ : ℝ → ℝ} (N v : ℝ) (ρ₁ ρ₂ : ℂ) :
    Jphi ϕ N v ρ₁ ρ₂ = ∫ σ in Set.Ioo (0 : ℝ) 1,
      (amp107 ϕ N v ρ₁ ρ₂ σ : ℂ) *
        Complex.exp (Complex.I * ((phase107 ρ₁ ρ₂ σ : ℝ) : ℂ)) := by
  rw [Jphi, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro σ hσ
  exact integrand_split107 ρ₁ ρ₂ hσ.1 hσ.2

/-- The phase has unit modulus, so the modulus of the sigma integrand is `amp107`. -/
private theorem norm_phase_exp107 (x : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [show Complex.I * (x : ℂ) = (x : ℂ) * Complex.I by ring]
  exact Complex.norm_exp_ofReal_mul_I x


/-! ## (2) From a pointwise bound on the inner beta integral to the leaf

The outer `v` integral only contributes the scale `N ^ (Re (rho_1+rho_2) - 1)`: the
kernel `GT G T (N - .)` has mass one and `Jphi` is supported on `v/N in (2/5, 8/5)`,
where `v ^ (re - 1)` is comparable to `N ^ (re - 1)`.  So the whole content of the
opposite-sign leaf sits in the pointwise decay of `Jphi` in the imaginary parts. -/

/-- `v ^ (r - 1)` is comparable to `N ^ (r - 1)` on the effective interval `v/N in [2/5, 8/5]`. -/
private theorem rpow_scale_bound107 {v N r : ℝ} (hN : 0 < N) (h0 : (2 / 5) * N ≤ v)
    (h1 : v ≤ (8 / 5) * N) (hr0 : 0 < r) (hr1 : r ≤ 2) :
    v ^ (r - 1) ≤ (5 / 2) * N ^ (r - 1) := by
  have hv : 0 < v := lt_of_lt_of_le (by positivity) h0
  have hNr : (0 : ℝ) ≤ N ^ (r - 1) := Real.rpow_nonneg hN.le _
  rcases le_total (r - 1) 0 with hneg | hpos
  · have hstep : v ^ (r - 1) ≤ ((2 / 5) * N) ^ (r - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h0 hneg
    have hsplit : ((2 / 5) * N) ^ (r - 1) = (2 / 5 : ℝ) ^ (r - 1) * N ^ (r - 1) :=
      Real.mul_rpow (by norm_num) hN.le
    have hconst : (2 / 5 : ℝ) ^ (r - 1) ≤ 5 / 2 := by
      have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0:ℝ) < 2 / 5)
        (by norm_num : (2 / 5 : ℝ) ≤ 1) (by linarith : (-1 : ℝ) ≤ r - 1)
      have h2 : (2 / 5 : ℝ) ^ (-1 : ℝ) = 5 / 2 := by
        rw [Real.rpow_neg_one]
        norm_num
      linarith [h, h2]
    have hm := mul_le_mul_of_nonneg_right hconst hNr
    linarith [hstep, hm, hsplit]
  · have hstep : v ^ (r - 1) ≤ ((8 / 5) * N) ^ (r - 1) :=
      Real.rpow_le_rpow hv.le h1 hpos
    have hsplit : ((8 / 5) * N) ^ (r - 1) = (8 / 5 : ℝ) ^ (r - 1) * N ^ (r - 1) :=
      Real.mul_rpow (by norm_num) hN.le
    have hconst : (8 / 5 : ℝ) ^ (r - 1) ≤ 5 / 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 8 / 5)
        (by linarith : r - 1 ≤ (1 : ℝ))
      rw [Real.rpow_one] at h
      linarith
    have hm := mul_le_mul_of_nonneg_right hconst hNr
    linarith [hstep, hm, hsplit]

/-- The opposite-sign leaf follows from pointwise decay of `Jphi`. -/
private theorem opposite_of_Jdecay107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    {A : ℝ} (hA : 0 < A)
    (hdec : ∃ Cj : ℝ, ∀ (N v : ℝ), 0 < N → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 → ρ₁.im * ρ₂.im < 0 →
      ‖Jphi ϕ N v ρ₁ ρ₂‖ ≤ Cj * (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A)) :
    ∃ C : ℝ, ∀ N T : ℝ, 1 ≤ T → T ≤ N → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 → ρ₁.im * ρ₂.im < 0 →
      ‖∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (ρ₁ + ρ₂ - 1) *
          (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂‖ ≤
        C * N ^ ((ρ₁ + ρ₂).re - 1) * (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) := by
  obtain ⟨Cj, hCj⟩ := hdec
  refine ⟨max Cj 0 * (5 / 2), ?_⟩
  intro N T hT hTN ρ₁ ρ₂ h₁ h₁' h₂ h₂' hs
  have hT0 : 0 < T := by linarith
  have hN : 0 < N := by linarith
  have hre1 : 0 < (ρ₁ + ρ₂).re := by
    simp only [Complex.add_re]; linarith
  have hre2 : (ρ₁ + ρ₂).re ≤ 2 := by
    simp only [Complex.add_re]; linarith
  have hK0 : (0 : ℝ) ≤ max Cj 0 * (5 / 2) := by positivity
  have hNre : (0 : ℝ) ≤ N ^ ((ρ₁ + ρ₂).re - 1) := Real.rpow_nonneg hN.le _
  have hP : (0 : ℝ) < (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hpt : ∀ v ∈ Set.Ioi (0 : ℝ),
      ‖(v : ℂ) ^ (ρ₁ + ρ₂ - 1) * (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂‖ ≤
        max Cj 0 * (5 / 2) * N ^ ((ρ₁ + ρ₂).re - 1) * (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) *
          GT G T (N - v) := by
    intro v hv
    have hv0 : 0 < v := hv
    have hGT : 0 ≤ GT G T (N - v) := nonneg_GT107 hG hT0 _
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hGT]
    have hCj0 : ‖Jphi ϕ N v ρ₁ ρ₂‖ ≤
        max Cj 0 * (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) :=
      (hCj N v hN ρ₁ ρ₂ h₁ h₁' h₂ h₂' hs).trans
        (mul_le_mul_of_nonneg_right (le_max_left Cj 0) hP.le)
    by_cases hJ : Jphi ϕ N v ρ₁ ρ₂ = 0
    · simp only [hJ, norm_zero, mul_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg hK0 hNre) hP.le) hGT
    · have houtside : ¬ (v ≤ (2 / 5) * N ∨ (8 / 5) * N ≤ v) := by
        intro hout
        exact hJ (Jphi_eq_zero_outside84 hϕ hN hout ρ₁ ρ₂)
      simp only [not_or, not_le] at houtside
      have hscale := rpow_scale_bound107 hN houtside.1.le houtside.2.le hre1 hre2
      have hstep : v ^ ((ρ₁ + ρ₂).re - 1) * GT G T (N - v) * ‖Jphi ϕ N v ρ₁ ρ₂‖ ≤
          (5 / 2 * N ^ ((ρ₁ + ρ₂).re - 1)) * GT G T (N - v) *
            (max Cj 0 * (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A)) :=
        mul_le_mul (mul_le_mul hscale le_rfl hGT (mul_nonneg (by norm_num) hNre)) hCj0
          (norm_nonneg _) (by positivity)
      calc v ^ ((ρ₁ + ρ₂).re - 1) * GT G T (N - v) * ‖Jphi ϕ N v ρ₁ ρ₂‖
          ≤ (5 / 2 * N ^ ((ρ₁ + ρ₂).re - 1)) * GT G T (N - v) *
              (max Cj 0 * (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A)) := hstep
        _ = max Cj 0 * (5 / 2) * N ^ ((ρ₁ + ρ₂).re - 1) *
              (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) * GT G T (N - v) := by ring
  have hInt : Integrable (fun v : ℝ => GT G T (N - v)) :=
    (integrable_GT107 hG hT0).comp_sub_left N
  have hdom : IntegrableOn
      (fun v : ℝ => max Cj 0 * (5 / 2) * N ^ ((ρ₁ + ρ₂).re - 1) *
        (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) * GT G T (N - v)) (Set.Ioi 0) :=
    (hInt.const_mul _).integrableOn
  have hae : ∀ᵐ v : ℝ ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖(v : ℂ) ^ (ρ₁ + ρ₂ - 1) * (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂‖ ≤
        max Cj 0 * (5 / 2) * N ^ ((ρ₁ + ρ₂).re - 1) *
          (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) * GT G T (N - v) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv using hpt v hv
  have hmain := norm_integral_le_of_norm_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ))) hdom hae
  refine hmain.trans ?_
  rw [integral_const_mul]
  have hset : (∫ v in Set.Ioi (0 : ℝ), GT G T (N - v)) ≤ 1 := by
    have h1 : (∫ v in Set.Ioi (0 : ℝ), GT G T (N - v)) ≤ ∫ v : ℝ, GT G T (N - v) :=
      setIntegral_le_integral hInt (Filter.Eventually.of_forall (fun v => nonneg_GT107 hG hT0 (N - v)))
    rwa [integral_sub_left_eq_self (GT G T) volume N, integral_GT107 hG hT0] at h1
  have hfac : (0 : ℝ) ≤ max Cj 0 * (5 / 2) * N ^ ((ρ₁ + ρ₂).re - 1) *
      (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) :=
    mul_nonneg (mul_nonneg hK0 hNre) hP.le
  calc max Cj 0 * (5 / 2) * N ^ ((ρ₁ + ρ₂).re - 1) *
        (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) * (∫ v in Set.Ioi (0 : ℝ), GT G T (N - v))
      ≤ max Cj 0 * (5 / 2) * N ^ ((ρ₁ + ρ₂).re - 1) *
          (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) * 1 := by
        gcongr
    _ = max Cj 0 * (5 / 2) * N ^ ((ρ₁ + ρ₂).re - 1) *
          (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) := by ring


/-! ## (3) What is still missing, stated exactly

Everything in the opposite-sign leaf now rests on one pointwise statement about the inner beta
integral: for opposite signs of `im rho_1`, `im rho_2` it decays faster than any power of
`1 + |im rho_1| + |im rho_2|`, uniformly in `N` and `v`.

It is the paper's "repeated integration by parts in sigma".  With `s = sigma`,

  `J_v = ∫_0^1 a(s) * exp (I * (t_1 log s + t_2 log (1 - s))) ds`,  `a` real, `supp a ⊆ [1/5,4/5]`,

and for `t_1 t_2 < 0` the phase derivative `t_1/s - t_2/(1-s)` has modulus `>= |t_1| + |t_2|`
(`sigma_phase_lower84`, already in the import closure), so `k` integrations by parts produce
`u^{-k}`, `u = |t_1| + |t_2|`: `1/Phi' = s (1-s) / (t_1 (1-s) - t_2 s)`, both `s^{+-1}` stay
bounded on the support, and each step contributes one more power of
`1/|t_1 (1-s) - t_2 s| >= 1/(25 u)` while the amplitude's derivative counts cost only constants
(the real exponents `re rho_i - 1` lie in `(-1,0]`, so `|d/ds (s ^ (re-1))| <= 5`).

Numerics (panel Gauss-Legendre on `[0.19,0.81]`): with `N = v = 1000`, `re = 1/2` and
`rho_1 = re + iT`, `rho_2 = re - iT` one gets `|J| = 6.96e-4, 1.90e-5, 2.08e-7, 5.54e-10` at
`T = 10, 20, 40, 80` — geometric decay, faster than any fixed power.  With equal signs the same
computation gives `|J| * sqrt T ~ 0.24`: only the stationary-phase rate.  That is why the
same-sign leaf carries the weaker `(1 + U T / N)^{-A}` and cannot be obtained pointwise: it needs
`j` integration by parts in `v` against the `j`-fold antiderivatives of `v ↦ GT G T (N - v)`
(unit mass, sup norms `<< T ^ (j-1)`) applied to the `j`-th `v`-derivative of `v ↦ v ^ z * J_v`
(size `<< N ^ (re-1-j) (|z|+1)^j`), which produces the factor `(U T / N)^j`.

Both therefore need the *same* missing piece of library: an iteration of
`intervalIntegral.integral_deriv_mul_eq_sub` with quantitative bounds on the derivatives of the
iterated amplitudes.  In Lean that means, in this order,
  (i) the Leibniz identity and bound for `iteratedDeriv` of a product (Mathlib has no
      `iteratedDeriv_mul`), by induction with `Nat.choose_succ_succ`;
  (ii) bounds for `iteratedDeriv` of `1/g` and of `Phi''/Phi'^2` from `|g| >= u` and
      `|g^(j)| <= K u`;
  (iii) the induction on `k` for the operator `a ↦ (a / (I * Phi'))'`.
-/


/-! ## (4) The reciprocal phase derivative: closed-form derivatives and bounds

For the integration by parts in `sigma` the relevant quantity is

  `1 / Phi' = s (1 - s) / (t_1 (1 - s) - t_2 s)`.

This section handles the second factor: `dph107` is the affine `t_1 (1-s) - t_2 s`, and the
`p`-th derivative of its reciprocal is `(-1)^p p! (dph')^p (1/dph)^(p+1)`; with
`|dph| >= u/25` on `[1/5,4/5]` (which is where `sigma_phase_lower84` is used) this gives
`‖(1/dph)^(p)‖ <= p! 25^(p+1) / u`, i.e. exactly one factor `1/u` regardless of `p`.
That is the quantitative ingredient the iteration needs. -/

/-- The affine factor in the derivative of the sigma phase `t_1 log s + t_2 log (1-s)`. -/
private noncomputable def dph107 (t₁ t₂ σ : ℝ) : ℝ := t₁ * (1 - σ) - t₂ * σ

/-- The reciprocal of the sigma phase derivative, in the affine form used by parts. -/
private noncomputable def phaserec107 (t₁ t₂ σ : ℝ) : ℝ := σ * (1 - σ) / dph107 t₁ t₂ σ

/-- The affine factor is continuous. -/
private theorem continuous_dph107 (t₁ t₂ : ℝ) : Continuous (fun τ => dph107 t₁ t₂ τ) := by
  have hfun : (fun τ : ℝ => dph107 t₁ t₂ τ) = fun τ : ℝ => t₁ - (t₁ + t₂) * τ := by
    funext τ
    simp only [dph107]
    ring
  rw [hfun]
  fun_prop

/-- The derivative of the affine factor. -/
private theorem hasDerivAt_dph107 (t₁ t₂ σ : ℝ) :
    HasDerivAt (fun τ => dph107 t₁ t₂ τ) (-(t₁ + t₂)) σ := by
  have hfun : (fun τ : ℝ => dph107 t₁ t₂ τ) = fun τ : ℝ => t₁ - (t₁ + t₂) * τ := by
    funext τ
    simp only [dph107]
    ring
  rw [hfun]
  have h1 : HasDerivAt (fun τ : ℝ => (t₁ + t₂) * τ) (t₁ + t₂) σ := by
    simpa using (hasDerivAt_id σ).const_mul (t₁ + t₂)
  simpa using h1.const_sub t₁

/-- The affine factor is `s (1-s)` times the phase derivative. -/
private theorem dph_eq_mul107 {t₁ t₂ σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    dph107 t₁ t₂ σ = σ * (1 - σ) * (t₁ / σ - t₂ / (1 - σ)) := by
  have h0' : σ ≠ 0 := h0.ne'
  have h1' : (1 : ℝ) - σ ≠ 0 := by linarith
  simp only [dph107]
  field_simp

/-- Opposite signs bound the affine factor below on the effective sigma interval. -/
private theorem abs_dph_lower107 {t₁ t₂ σ : ℝ} (hprod : t₁ * t₂ < 0) (h0 : 0 < σ) (h1 : σ < 1)
    (h2 : (1 / 5 : ℝ) ≤ σ) (h3 : σ ≤ 4 / 5) :
    (|t₁| + |t₂|) / 25 ≤ |dph107 t₁ t₂ σ| := by
  have hlow := sigma_phase_lower84 hprod h0 h1
  rw [dph_eq_mul107 h0 h1, abs_mul]
  have hspos : (0 : ℝ) < σ * (1 - σ) := by nlinarith
  have hs : (1 / 25 : ℝ) ≤ σ * (1 - σ) := by nlinarith
  rw [abs_of_pos hspos]
  have hmul : (|t₁| + |t₂|) * (1 / 25) ≤ |t₁ / σ - t₂ / (1 - σ)| * (σ * (1 - σ)) :=
    mul_le_mul hlow hs (by norm_num) (abs_nonneg _)
  linarith [hmul]

/-- The `p`-th derivative of the reciprocal of the affine factor, in closed form. -/
private theorem iteratedDeriv_invD107 (t₁ t₂ : ℝ) (p : ℕ) {σ : ℝ}
    (hD : dph107 t₁ t₂ σ ≠ 0) :
    iteratedDeriv p (fun τ => (dph107 t₁ t₂ τ)⁻¹) σ =
      (-1) ^ p * ((p.factorial : ℕ) : ℝ) * (-(t₁ + t₂)) ^ p *
        ((dph107 t₁ t₂ σ)⁻¹) ^ (p + 1) := by
  induction p generalizing σ with
  | zero =>
    rw [iteratedDeriv_zero]
    simp
  | succ p ih =>
    rw [iteratedDeriv_succ]
    have hcont : ContinuousAt (fun τ : ℝ => dph107 t₁ t₂ τ) σ :=
      (continuous_dph107 t₁ t₂).continuousAt
    have hev : ∀ᶠ τ in 𝓝 σ, dph107 t₁ t₂ τ ≠ 0 := hcont.eventually_ne hD
    have hEq : iteratedDeriv p (fun τ => (dph107 t₁ t₂ τ)⁻¹) =ᶠ[𝓝 σ]
        (fun τ => (-1) ^ p * ((p.factorial : ℕ) : ℝ) * (-(t₁ + t₂)) ^ p *
          ((dph107 t₁ t₂ τ)⁻¹) ^ (p + 1)) := by
      filter_upwards [hev] with τ hτ
      exact ih hτ
    rw [hEq.deriv_eq]
    have hbase : HasDerivAt (fun τ : ℝ => (dph107 t₁ t₂ τ)⁻¹)
        ((t₁ + t₂) * ((dph107 t₁ t₂ σ)⁻¹) ^ 2) σ := by
      have h := (hasDerivAt_dph107 t₁ t₂ σ).inv hD
      convert h using 1
      field_simp
    have hfin := (hbase.pow (p + 1)).const_mul
      ((-1) ^ p * ((p.factorial : ℕ) : ℝ) * (-(t₁ + t₂)) ^ p)
    simp only [Pi.pow_apply] at hfin
    rw [hfin.deriv]
    have hf : (((p + 1).factorial : ℕ) : ℝ) = ((p : ℝ) + 1) * ((p.factorial : ℕ) : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hneg : (-1 : ℝ) ^ (p + 1) = (-1) ^ p * (-1) := pow_succ _ p
    have hX : (-(t₁ + t₂)) ^ (p + 1) = (-(t₁ + t₂)) ^ p * (-(t₁ + t₂)) := pow_succ _ p
    have hP : ((dph107 t₁ t₂ σ)⁻¹) ^ (p + 1 + 1) =
        ((dph107 t₁ t₂ σ)⁻¹) ^ p * ((dph107 t₁ t₂ σ)⁻¹) ^ 2 := by
      rw [pow_succ, pow_succ]
      ring
    rw [hf, hneg, hX, hP]
    push_cast
    ring

/-- The `p`-th derivative of the reciprocal of the affine factor is bounded by `p! 25^(p+1)/u`. -/
private theorem iteratedDeriv_invD_bound107 {t₁ t₂ : ℝ} (hprod : t₁ * t₂ < 0) {u : ℝ}
    (hu : u = |t₁| + |t₂|) (hu0 : 0 < u) (p : ℕ) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (1 / 5 : ℝ) (4 / 5)) :
    ‖iteratedDeriv p (fun τ => (dph107 t₁ t₂ τ)⁻¹) σ‖ ≤
      ((p.factorial : ℕ) : ℝ) * (25 : ℝ) ^ (p + 1) / u := by
  have h0 : 0 < σ := by linarith [hσ.1]
  have h1 : σ < 1 := by linarith [hσ.2]
  have hlow : u / 25 ≤ |dph107 t₁ t₂ σ| := by
    rw [hu]
    exact abs_dph_lower107 hprod h0 h1 hσ.1 hσ.2
  have hu25 : 0 < u / 25 := by linarith
  have hDpos : 0 < |dph107 t₁ t₂ σ| := lt_of_lt_of_le hu25 hlow
  have hD : dph107 t₁ t₂ σ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hDpos
    exact lt_irrefl 0 hDpos
  have hfac0 : (0 : ℝ) ≤ ((p.factorial : ℕ) : ℝ) := by positivity
  have ht : |t₁ + t₂| ≤ u := by
    rw [hu]
    exact abs_add_le t₁ t₂
  have hc : |(-1) ^ p * ((p.factorial : ℕ) : ℝ) * (-(t₁ + t₂)) ^ p| ≤
      ((p.factorial : ℕ) : ℝ) * u ^ p := by
    have h1' : |(-1 : ℝ) ^ p| = 1 := by
      rw [abs_pow]
      norm_num
    have h2' : |(((p.factorial : ℕ) : ℝ))| = ((p.factorial : ℕ) : ℝ) := abs_of_nonneg hfac0
    have h3' : |(-(t₁ + t₂)) ^ p| ≤ u ^ p := by
      rw [abs_pow, abs_neg]
      exact pow_le_pow_left₀ (abs_nonneg _) ht p
    calc |(-1) ^ p * ((p.factorial : ℕ) : ℝ) * (-(t₁ + t₂)) ^ p|
        = |(-1) ^ p| * |(((p.factorial : ℕ) : ℝ))| * |(-(t₁ + t₂)) ^ p| := by
          rw [abs_mul, abs_mul]
      _ = 1 * ((p.factorial : ℕ) : ℝ) * |(-(t₁ + t₂)) ^ p| := by rw [h1', h2']
      _ ≤ 1 * ((p.factorial : ℕ) : ℝ) * u ^ p := by nlinarith [h3', hfac0]
      _ = ((p.factorial : ℕ) : ℝ) * u ^ p := by ring
  have hinvle : |(dph107 t₁ t₂ σ)⁻¹| ≤ 25 / u := by
    rw [abs_inv, ← one_div]
    have h := one_div_le_one_div_of_le hu25 hlow
    rwa [one_div_div] at h
  have hP : |((dph107 t₁ t₂ σ)⁻¹) ^ (p + 1)| ≤ (25 / u) ^ (p + 1) := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hinvle (p + 1)
  rw [iteratedDeriv_invD107 t₁ t₂ p hD, Real.norm_eq_abs, abs_mul]
  refine (mul_le_mul hc hP (abs_nonneg _) (by positivity)).trans (le_of_eq ?_)
  have hu' : u ≠ 0 := hu0.ne'
  have hkey : u ^ p * (25 / u) ^ (p + 1) = 25 ^ (p + 1) / u := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_pow]
    have h2' : u ^ p * (u⁻¹) ^ (p + 1) = u⁻¹ := by
      rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hu', one_pow, one_mul]
    calc u ^ p * (25 ^ (p + 1) * u⁻¹ ^ (p + 1))
        = 25 ^ (p + 1) * (u ^ p * u⁻¹ ^ (p + 1)) := by ring
      _ = 25 ^ (p + 1) * u⁻¹ := by rw [h2']
      _ = 25 ^ (p + 1) / u := rfl
  calc ((p.factorial : ℕ) : ℝ) * u ^ p * (25 / u) ^ (p + 1)
      = ((p.factorial : ℕ) : ℝ) * (u ^ p * (25 / u) ^ (p + 1)) := by ring
    _ = ((p.factorial : ℕ) : ℝ) * (25 ^ (p + 1) / u) := by rw [hkey]
    _ = ((p.factorial : ℕ) : ℝ) * 25 ^ (p + 1) / u := by ring

/-! ## (5) Leibniz bounds for `iteratedDeriv`, and derivatives of a real power

Mathlib has the product bound for `iteratedFDeriv` (`norm_iteratedFDeriv_mul_le`) but no
`iteratedDeriv_mul`; the transfer goes through
`norm_iteratedFDeriv_eq_norm_iteratedDeriv`.  `iteratedDeriv_rpow107` is the closed form
`(s^a)^(m) = (∏_{i<m}(a-i)) s^(a-m)`, used to bound the two powers of the sigma amplitude by
constants on `[1/5,4/5]` (that is where the condition `re rho - 1 ∈ (-1,0]` enters). -/

/-- The Leibniz bound for `iteratedDeriv` of a product of complex-valued functions. -/
private theorem norm_iteratedDeriv_mul_le107 {f g : ℝ → ℂ} {n : ℕ}
    (hf : ContDiff ℝ (n : ℕ∞) f) (hg : ContDiff ℝ (n : ℕ∞) g) (x : ℝ) :
    ‖iteratedDeriv n (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedDeriv i f x‖ *
        ‖iteratedDeriv (n - i) g x‖ := by
  calc ‖iteratedDeriv n (fun y => f y * g y) x‖
      = ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
          ‖iteratedFDeriv ℝ (n - i) g x‖ := norm_iteratedFDeriv_mul_le hf hg x le_rfl
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedDeriv i f x‖ *
          ‖iteratedDeriv (n - i) g x‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
          norm_iteratedFDeriv_eq_norm_iteratedDeriv]

/-- The `m`-th derivative of a real power, in closed form. -/
private theorem iteratedDeriv_rpow107 (a : ℝ) {σ : ℝ} (hσ : 0 < σ) (m : ℕ) :
    iteratedDeriv m (fun τ : ℝ => τ ^ a) σ =
      (∏ i ∈ Finset.range m, (a - (i : ℝ))) * σ ^ (a - (m : ℝ)) := by
  induction m generalizing σ with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ]
    have hEq : iteratedDeriv m (fun τ : ℝ => τ ^ a) =ᶠ[𝓝 σ]
        (fun τ => (∏ i ∈ Finset.range m, (a - (i : ℝ))) * τ ^ (a - (m : ℝ))) := by
      filter_upwards [eventually_gt_nhds hσ] with τ hτ
      exact ih hτ
    rw [hEq.deriv_eq]
    have hderiv : HasDerivAt
        (fun τ : ℝ => (∏ i ∈ Finset.range m, (a - (i : ℝ))) * τ ^ (a - (m : ℝ)))
        ((∏ i ∈ Finset.range m, (a - (i : ℝ))) *
          ((a - (m : ℝ)) * σ ^ (a - (m : ℝ) - 1))) σ :=
      (Real.hasDerivAt_rpow_const (Or.inl hσ.ne')).const_mul _
    rw [hderiv.deriv, Finset.prod_range_succ]
    have hexp : σ ^ (a - (m : ℝ) - 1) = σ ^ (a - ((m : ℝ) + 1)) := by
      congr 1
      ring
    rw [hexp]
    push_cast
    ring

/-! ## (6) Two transfers: the Leibniz bound on a set, and the coercion `ℝ → ℂ`

`dph107` has its only zero outside `[0,1]`, so `1/dph` is not globally smooth; the bound for
`phaserec107` must therefore be built with the *within* Leibniz bound.  And the amplitude's
powers are real functions coerced to `ℂ`, so the coercion must be seen not to increase
iterated derivatives (the embedding `Complex.ofRealCLM` is an isometry). -/

/-- The Leibniz bound for `iteratedDerivWithin` on a set. -/
private theorem norm_iteratedDerivWithin_mul_le107 {f g : ℝ → ℂ} {s : Set ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ (n : ℕ∞) f s) (hg : ContDiffOn ℝ (n : ℕ∞) g s)
    (hs : UniqueDiffOn ℝ s) {x : ℝ} (hx : x ∈ s) :
    ‖iteratedDerivWithin n (fun y => f y * g y) s x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedDerivWithin i f s x‖ * ‖iteratedDerivWithin (n - i) g s x‖ := by
  calc ‖iteratedDerivWithin n (fun y => f y * g y) s x‖
      = ‖iteratedFDerivWithin ℝ n (fun y => f y * g y) s x‖ := by
        rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i f s x‖ * ‖iteratedFDerivWithin ℝ (n - i) g s x‖ :=
        norm_iteratedFDerivWithin_mul_le hf hg hs hx le_rfl
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedDerivWithin i f s x‖ * ‖iteratedDerivWithin (n - i) g s x‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
          norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]

/-- The coercion `ℝ → ℂ` does not increase iterated derivatives. -/
private theorem norm_iteratedDeriv_ofReal_le107 {f : ℝ → ℝ} {m : ℕ} {σ : ℝ}
    (hf : ContDiffAt ℝ (m : ℕ∞) f σ) :
    ‖iteratedDeriv m (fun τ : ℝ => ((f τ : ℝ) : ℂ)) σ‖ ≤ ‖iteratedDeriv m f σ‖ := by
  have hcomp : (fun τ : ℝ => ((f τ : ℝ) : ℂ)) = Complex.ofRealCLM ∘ f := by
    funext τ
    simp [Complex.ofRealCLM_apply]
  rw [hcomp]
  calc ‖iteratedDeriv m (Complex.ofRealCLM ∘ f) σ‖
      = ‖iteratedFDeriv ℝ m (Complex.ofRealCLM ∘ f) σ‖ := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    _ ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ m f σ‖ :=
        Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hf le_rfl
    _ = ‖iteratedFDeriv ℝ m f σ‖ := by rw [Complex.ofRealCLM_norm, one_mul]
    _ = ‖iteratedDeriv m f σ‖ := by rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]

/-! ## (7) Derivative bounds for the quadratic `s (1-s)` and for `phaserec107`

`phaserec107 = q * (1/dph)` with `q = s (1-s)` quadratic: `q` contributes at most `2` for every
derivative order (its third derivative vanishes), and `1/dph` contributes one factor `1/u` for
every order (`iteratedDeriv_invD_bound107`).  The within-set Leibniz bound then gives
`‖(phaserec)^(m)‖ <= C m / u` with `C m` independent of `(t_1, t_2)`. -/

/-- The derivative of the quadratic `s (1-s)`. -/
private theorem deriv_quad107 : deriv (fun τ : ℝ => τ * (1 - τ)) = fun τ => 1 - 2 * τ := by
  have hfun : (fun τ : ℝ => τ * (1 - τ)) = fun τ : ℝ => τ - τ ^ 2 := by
    funext x
    ring
  funext τ
  rw [hfun]
  have hsq : HasDerivAt (fun σ : ℝ => σ ^ 2) (2 * τ) τ := by
    simpa using hasDerivAt_pow 2 τ
  have h : HasDerivAt (fun σ : ℝ => σ - σ ^ 2) (1 - 2 * τ) τ := by
    have h0 := (hasDerivAt_id τ).sub hsq
    convert h0 using 1
    funext x
    simp
  exact h.deriv

/-- The derivative of `1 - 2s`. -/
private theorem deriv_quad_snd107 : deriv (fun τ : ℝ => 1 - 2 * τ) = fun _ => (-2 : ℝ) := by
  funext τ
  have h1 : HasDerivAt (fun τ : ℝ => 2 * τ) 2 τ := by
    simpa using (hasDerivAt_id τ).const_mul 2
  have h : HasDerivAt (fun τ : ℝ => 1 - 2 * τ) (-2) τ := by
    simpa using h1.const_sub 1
  exact h.deriv

/-- From the third derivative on the quadratic vanishes. -/
private theorem iteratedDeriv_quad_eq_zero107 (n : ℕ) :
    iteratedDeriv (n + 3) (fun τ : ℝ => τ * (1 - τ)) = fun _ => (0 : ℝ) := by
  induction n with
  | zero =>
    rw [show (0 + 3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ,
      show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one,
      deriv_quad107, deriv_quad_snd107]
    funext τ
    simp
  | succ n ih =>
    rw [show (n + 1 + 3 : ℕ) = (n + 3) + 1 by ring, iteratedDeriv_succ, ih]
    funext τ
    simp

/-- The quadratic is globally smooth as a complex-valued function. -/
private theorem contDiff_quad107 (n : ℕ∞) :
    ContDiff ℝ n (fun τ : ℝ => ((τ * (1 - τ) : ℝ) : ℂ)) := by
  have h1 : ContDiff ℝ n (fun τ : ℝ => τ * (1 - τ)) :=
    contDiff_id.mul (contDiff_const.sub contDiff_id)
  exact Complex.ofRealCLM.contDiff.comp h1

/-- All derivatives of `s (1-s)` are bounded by two on `[0,1]`. -/
private theorem norm_iteratedDeriv_quad107 (i : ℕ) {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    ‖iteratedDeriv i (fun τ : ℝ => ((τ * (1 - τ) : ℝ) : ℂ)) σ‖ ≤ 2 := by
  rcases Nat.lt_or_ge i 3 with hi | hi
  · have hq : ContDiff ℝ ((i : ℕ∞)) (fun τ : ℝ => τ * (1 - τ)) :=
      contDiff_id.mul (contDiff_const.sub contDiff_id)
    refine (norm_iteratedDeriv_ofReal_le107 hq.contDiffAt).trans ?_
    interval_cases i
    · rw [iteratedDeriv_zero, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hσ.1 (by linarith [hσ.2]))]
      nlinarith [hσ.1, hσ.2]
    · rw [iteratedDeriv_one, deriv_quad107, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hσ.1, hσ.2]
    · rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one,
        deriv_quad107, deriv_quad_snd107, Real.norm_eq_abs]
      norm_num
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = n + 3 := ⟨i - 3, by omega⟩
    have hq : ContDiff ℝ (((n + 3) : ℕ∞)) (fun τ : ℝ => τ * (1 - τ)) :=
      contDiff_id.mul (contDiff_const.sub contDiff_id)
    refine (norm_iteratedDeriv_ofReal_le107 hq.contDiffAt).trans ?_
    rw [iteratedDeriv_quad_eq_zero107 n, Real.norm_eq_abs]
    norm_num

/-- The Leibniz bound on a set for real-valued functions. -/
private theorem norm_iteratedDerivWithin_mul_le107_real {f g : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ (n : ℕ∞) f s) (hg : ContDiffOn ℝ (n : ℕ∞) g s)
    (hs : UniqueDiffOn ℝ s) {x : ℝ} (hx : x ∈ s) :
    ‖iteratedDerivWithin n (fun y => f y * g y) s x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedDerivWithin i f s x‖ * ‖iteratedDerivWithin (n - i) g s x‖ := by
  calc ‖iteratedDerivWithin n (fun y => f y * g y) s x‖
      = ‖iteratedFDerivWithin ℝ n (fun y => f y * g y) s x‖ := by
        rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i f s x‖ * ‖iteratedFDerivWithin ℝ (n - i) g s x‖ :=
        norm_iteratedFDerivWithin_mul_le hf hg hs hx le_rfl
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedDerivWithin i f s x‖ * ‖iteratedDerivWithin (n - i) g s x‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
          norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]

/-- All derivatives of the real quadratic `s (1-s)` are bounded by two on `[0,1]`. -/
private theorem norm_iteratedDeriv_quad107_real (i : ℕ) {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    ‖iteratedDeriv i (fun τ : ℝ => τ * (1 - τ)) σ‖ ≤ 2 := by
  rcases Nat.lt_or_ge i 3 with hi | hi
  · interval_cases i
    · rw [iteratedDeriv_zero, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hσ.1 (by linarith [hσ.2]))]
      nlinarith [hσ.1, hσ.2]
    · rw [iteratedDeriv_one, deriv_quad107, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hσ.1, hσ.2]
    · rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one,
        deriv_quad107, deriv_quad_snd107, Real.norm_eq_abs]
      norm_num
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = n + 3 := ⟨i - 3, by omega⟩
    rw [iteratedDeriv_quad_eq_zero107 n, Real.norm_eq_abs]
    norm_num

/-- The reciprocal phase derivative has derivatives bounded by `C m / u`, with `C m` independent
of `(t_1, t_2)`. -/
private theorem norm_iteratedDeriv_phaserec_bound107 {t₁ t₂ : ℝ} (hprod : t₁ * t₂ < 0) {u : ℝ}
    (hu : u = |t₁| + |t₂|) (hu0 : 0 < u) (m : ℕ) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (1/5 : ℝ) (4/5)) :
    ‖iteratedDeriv m (fun τ => ((phaserec107 t₁ t₂ τ : ℝ) : ℂ)) σ‖ ≤
      (2 * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        (((m - i).factorial : ℕ) : ℝ) * 25 ^ (m - i + 1)) / u := by
  have ht1 : t₁ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact lt_irrefl 0 hprod
  have ht2 : t₂ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    exact lt_irrefl 0 hprod
  have hσ01 : σ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hσs : σ ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hs : UniqueDiffOn ℝ (Set.Ioo (0 : ℝ) 1) := uniqueDiffOn_Ioo (0 : ℝ) 1
  have haff_eq : (fun τ : ℝ => dph107 t₁ t₂ τ) = fun τ : ℝ => t₁ - (t₁ + t₂) * τ := by
    funext τ
    simp only [dph107]
    ring
  have hnonzero : ∀ τ ∈ Set.Ioo (0 : ℝ) 1, dph107 t₁ t₂ τ ≠ 0 := by
    intro τ hτ
    have h0 : 0 < τ := by linarith [hτ.1]
    have h1 : τ < 1 := by linarith [hτ.2]
    have hlow := sigma_phase_lower84 hprod h0 h1
    have hPhi : t₁ / τ - t₂ / (1 - τ) ≠ 0 := by
      intro h
      rw [h, abs_zero] at hlow
      have hu' : 0 < |t₁| + |t₂| := by
        have h1' := abs_pos.mpr ht1
        have h2' := abs_pos.mpr ht2
        linarith
      linarith
    rw [dph_eq_mul107 h0 h1]
    exact mul_ne_zero (mul_ne_zero h0.ne' (by linarith : (1 : ℝ) - τ ≠ 0)) hPhi
  have haff_at : ContDiffAt ℝ (m : ℕ∞) (fun τ : ℝ => dph107 t₁ t₂ τ) σ := by
    have h : ContDiff ℝ (m : ℕ∞) (fun τ : ℝ => dph107 t₁ t₂ τ) := by
      rw [haff_eq]
      fun_prop
    exact h.contDiffAt
  have hinv_at : ContDiffAt ℝ (m : ℕ∞) (fun τ : ℝ => (dph107 t₁ t₂ τ)⁻¹) σ :=
    haff_at.inv (hnonzero σ hσs)
  have hq_at : ContDiffAt ℝ (m : ℕ∞) (fun τ : ℝ => τ * (1 - τ)) σ :=
    (contDiff_id.mul (contDiff_const.sub contDiff_id)).contDiffAt
  have hreal_at : ContDiffAt ℝ (m : ℕ∞) (fun τ : ℝ => phaserec107 t₁ t₂ τ) σ := by
    have hfun : (fun τ : ℝ => phaserec107 t₁ t₂ τ) =
        (fun τ : ℝ => τ * (1 - τ)) * fun τ : ℝ => (dph107 t₁ t₂ τ)⁻¹ := by
      funext τ
      simp only [phaserec107, Pi.mul_apply, div_eq_mul_inv]
    rw [hfun]
    exact hq_at.mul hinv_at
  -- the real bound, by the within-set Leibniz bound on an open interval
  have hreal : ‖iteratedDeriv m (fun τ : ℝ => phaserec107 t₁ t₂ τ) σ‖ ≤
      (2 * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        (((m - i).factorial : ℕ) : ℝ) * 25 ^ (m - i + 1)) / u := by
    have hq_cd : ContDiffOn ℝ (m : ℕ∞) (fun τ : ℝ => τ * (1 - τ))
        (Set.Ioo (0 : ℝ) 1) :=
      (contDiff_id.mul (contDiff_const.sub contDiff_id)).contDiffOn
    have haff_cd : ContDiffOn ℝ (m : ℕ∞) (fun τ : ℝ => dph107 t₁ t₂ τ)
        (Set.Ioo (0 : ℝ) 1) := by
      have h : ContDiff ℝ (m : ℕ∞) (fun τ : ℝ => dph107 t₁ t₂ τ) := by
        rw [haff_eq]
        fun_prop
      exact h.contDiffOn
    have hinv_cd : ContDiffOn ℝ (m : ℕ∞) (fun τ : ℝ => (dph107 t₁ t₂ τ)⁻¹)
        (Set.Ioo (0 : ℝ) 1) := haff_cd.inv hnonzero
    have hfun : (fun τ : ℝ => phaserec107 t₁ t₂ τ) =
        (fun τ : ℝ => τ * (1 - τ)) * fun τ : ℝ => (dph107 t₁ t₂ τ)⁻¹ := by
      funext τ
      simp only [phaserec107, Pi.mul_apply, div_eq_mul_inv]
    have hmain := norm_iteratedDerivWithin_mul_le107_real hq_cd hinv_cd hs hσs (n := m)
    rw [← iteratedDerivWithin_eq_iteratedDeriv hs hreal_at hσs, hfun]
    refine hmain.trans ?_
    have hsum : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          ‖iteratedDerivWithin i (fun τ : ℝ => τ * (1 - τ))
            (Set.Ioo (0 : ℝ) 1) σ‖ *
          ‖iteratedDerivWithin (m - i) (fun τ : ℝ => (dph107 t₁ t₂ τ)⁻¹)
            (Set.Ioo (0 : ℝ) 1) σ‖) ≤
        ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * 2 *
          ((((m - i).factorial : ℕ) : ℝ) * 25 ^ (m - i + 1) / u) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hq_at_i : ContDiffAt ℝ (i : ℕ∞) (fun τ : ℝ => τ * (1 - τ)) σ := by
        have h0 : ContDiff ℝ (i : ℕ∞) (fun τ : ℝ => τ * (1 - τ)) :=
          contDiff_id.mul (contDiff_const.sub contDiff_id)
        exact h0.contDiffAt
      have hqi : ‖iteratedDerivWithin i (fun τ : ℝ => τ * (1 - τ))
          (Set.Ioo (0 : ℝ) 1) σ‖ ≤ 2 := by
        rw [iteratedDerivWithin_eq_iteratedDeriv hs hq_at_i hσs]
        exact norm_iteratedDeriv_quad107_real i hσ01
      have hDi : ‖iteratedDerivWithin (m - i) (fun τ : ℝ => (dph107 t₁ t₂ τ)⁻¹)
          (Set.Ioo (0 : ℝ) 1) σ‖ ≤
          (((m - i).factorial : ℕ) : ℝ) * 25 ^ (m - i + 1) / u := by
        rw [iteratedDerivWithin_eq_iteratedDeriv hs
          (by
            have h : ContDiff ℝ (((m - i : ℕ) : ℕ∞)) (fun τ : ℝ => dph107 t₁ t₂ τ) := by
              rw [haff_eq]
              fun_prop
            exact h.contDiffAt.inv (hnonzero σ hσs)) hσs]
        exact iteratedDeriv_invD_bound107 hprod hu hu0 (m - i) hσ
      refine mul_le_mul (mul_le_mul le_rfl hqi (norm_nonneg _) (by positivity)) hDi
        (norm_nonneg _) ?_
      positivity
    refine hsum.trans (le_of_eq ?_)
    rw [Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_eq_mul_inv]
    ring
  exact (norm_iteratedDeriv_ofReal_le107 hreal_at).trans hreal

/-! ## (8) Closed forms for the reciprocal phase derivative

Two facts about `phaserec107` that the integration by parts uses: `phaserec * Phi' = 1` (so the
`f g'` term of the parts identity is exactly `i * A`), and its derivative in closed form. -/

/-- `phaserec107` is the reciprocal of the phase derivative. -/
private theorem phaserec_mul_deriv107 {t₁ t₂ σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1)
    (hD : dph107 t₁ t₂ σ ≠ 0) :
    phaserec107 t₁ t₂ σ * (t₁ / σ - t₂ / (1 - σ)) = 1 := by
  have hσ : σ ≠ 0 := h0.ne'
  have h1' : (1 : ℝ) - σ ≠ 0 := by linarith
  have hDeq : dph107 t₁ t₂ σ = σ * (1 - σ) * (t₁ / σ - t₂ / (1 - σ)) := dph_eq_mul107 h0 h1
  have hΦ : t₁ / σ - t₂ / (1 - σ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hDeq
    exact hD hDeq
  have hX : (1 - σ) * t₁ - σ * t₂ ≠ 0 := by
    intro h
    apply hΦ
    field_simp
    linarith [h]
  simp only [phaserec107]
  rw [hDeq]
  field_simp

/-- The derivative of the reciprocal phase derivative, in closed form. -/
private theorem deriv_phaserec107 {t₁ t₂ σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1)
    (hD : dph107 t₁ t₂ σ ≠ 0) :
    deriv (fun τ : ℝ => phaserec107 t₁ t₂ τ) σ =
      ((1 - 2 * σ) * dph107 t₁ t₂ σ + σ * (1 - σ) * (t₁ + t₂)) /
        (dph107 t₁ t₂ σ) ^ 2 := by
  have hσ : σ ≠ 0 := h0.ne'
  have h1' : (1 : ℝ) - σ ≠ 0 := by linarith
  -- the numerator as a product, then the quotient rule
  have hnum : (fun τ : ℝ => τ * (1 - τ)) = fun τ => τ - τ ^ 2 := by
    funext x
    ring
  have hd : HasDerivAt (fun τ : ℝ => τ * (1 - τ)) (1 - 2 * σ) σ := by
    rw [hnum]
    have hsq : HasDerivAt (fun σ : ℝ => σ ^ 2) (2 * σ) σ := by
      simpa using hasDerivAt_pow 2 σ
    have h0' := (hasDerivAt_id σ).sub hsq
    convert h0' using 1
    funext x
    simp
  have hden : HasDerivAt (fun τ : ℝ => dph107 t₁ t₂ τ) (-(t₁ + t₂)) σ :=
    hasDerivAt_dph107 t₁ t₂ σ
  have hq : HasDerivAt (fun τ : ℝ => phaserec107 t₁ t₂ τ)
      (((1 - 2 * σ) * dph107 t₁ t₂ σ - σ * (1 - σ) * (-(t₁ + t₂))) /
        (dph107 t₁ t₂ σ) ^ 2) σ := by
    have hfun : (fun τ : ℝ => phaserec107 t₁ t₂ τ) =
        (fun τ : ℝ => τ * (1 - τ)) / fun τ : ℝ => dph107 t₁ t₂ τ := by
      funext x
      simp only [phaserec107, Pi.div_apply]
    rw [hfun]
    exact hd.div hden hD
  rw [hq.deriv]
  congr 1
  ring

/-! ## (9) Uniform derivative bounds for the powers of the sigma amplitude

`σ ^ a` with `a = re ρ - 1 ∈ (-1,0]`: the falling factorial is at most `m!` (because
`|a - i| ≤ i + 1`), and `σ ^ (a - m) ≤ (1/σ) ^ (m+1) ≤ 5 ^ (m+1)` on `[1/5,4/5]`.  So all
derivatives of the power are bounded by `m! 5^(m+1)`, uniformly in `a`. -/

/-- Uniform bound for the iterated derivatives of a real power with exponent in `(-1,0]`. -/
private theorem norm_iteratedDeriv_rpow_bound107 {a : ℝ} (ha0 : -1 < a) (ha1 : a ≤ 0) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (1/5 : ℝ) (4/5)) (m : ℕ) :
    ‖iteratedDeriv m (fun τ : ℝ => τ ^ a) σ‖ ≤ ((m.factorial : ℕ) : ℝ) * 5 ^ (m + 1) := by
  have hσ0 : 0 < σ := by linarith [hσ.1]
  have hσ1 : σ ≤ 1 := by linarith [hσ.2]
  have hfac : |∏ i ∈ Finset.range m, (a - (i : ℝ))| ≤ ((m.factorial : ℕ) : ℝ) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_range_succ, Nat.factorial_succ, abs_mul]
      have h1 : |a - (m : ℝ)| ≤ (m : ℝ) + 1 := by
        rw [abs_le]
        constructor <;> linarith
      push_cast
      have h2 : |∏ i ∈ Finset.range m, (a - ↑i)| * |a - ↑m| ≤ ↑(m.factorial) * (↑m + 1) :=
        mul_le_mul ih h1 (abs_nonneg _) (by positivity)
      linarith [h2]
  have hpow : |σ ^ (a - (m : ℝ))| ≤ 5 ^ (m + 1) := by
    have hpos : 0 < σ ^ (a - (m : ℝ)) := Real.rpow_pos_of_pos hσ0 _
    rw [abs_of_pos hpos]
    have hstep : σ ^ (a - (m : ℝ)) ≤ σ ^ (-((m : ℝ) + 1)) := by
      refine Real.rpow_le_rpow_of_exponent_ge hσ0 hσ1 ?_
      linarith
    have hneg : σ ^ (-((m : ℝ) + 1)) = (σ⁻¹) ^ (m + 1) := by
      have hcast : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      have h1 : (σ⁻¹) ^ ((m : ℝ) + 1) = (σ⁻¹) ^ (m + 1) := by
        rw [hcast, Real.rpow_natCast]
      rw [← h1, Real.inv_rpow (le_of_lt hσ0), ← Real.rpow_neg (le_of_lt hσ0)]
    have hinv : σ⁻¹ ≤ 5 := by
      rw [inv_le_comm₀ hσ0 (by norm_num : (0 : ℝ) < 5)]
      norm_num
      linarith [hσ.1]
    calc σ ^ (a - (m : ℝ)) ≤ σ ^ (-((m : ℝ) + 1)) := hstep
      _ = (σ⁻¹) ^ (m + 1) := hneg
      _ ≤ 5 ^ (m + 1) := pow_le_pow_left₀ (by positivity) hinv (m + 1)
  rw [iteratedDeriv_rpow107 a hσ0 m, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul hfac hpow (abs_nonneg _) (by positivity)

/-- Iterated derivatives of a smooth function composed with an affine map. -/
private theorem iteratedDeriv_affine_comp107 {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c d : ℝ) :
    ∀ (m : ℕ) (σ : ℝ),
      iteratedDeriv m (fun x : ℝ => f (c * x + d)) σ = c ^ m * iteratedDeriv m f (c * σ + d)
  | 0, σ => by simp
  | m + 1, σ => by
    rw [iteratedDeriv_succ]
    have hEq : iteratedDeriv m (fun x : ℝ => f (c * x + d)) =
        fun x => c ^ m * iteratedDeriv m f (c * x + d) := by
      funext x
      exact iteratedDeriv_affine_comp107 hf c d m x
    rw [hEq]
    have haff : HasDerivAt (fun x : ℝ => c * x + d) c σ := by
      simpa using ((hasDerivAt_id σ).const_mul c).const_add d
    have hd1 : DifferentiableAt ℝ (iteratedDeriv m f) (c * σ + d) :=
      (ContDiff.differentiable_iteratedDeriv' m (hf.of_le (by simp))).differentiableAt
    have hinnerH : HasDerivAt (fun x : ℝ => iteratedDeriv m f (c * x + d))
        (deriv (iteratedDeriv m f) (c * σ + d) * c) σ := by
      have h : HasDerivAt (iteratedDeriv m f ∘ fun x : ℝ => c * x + d)
          (deriv (iteratedDeriv m f) (c * σ + d) * c) σ :=
        (hd1.hasDerivAt).comp σ haff
      convert h using 1
      funext x
      rfl
    have hderiv : deriv (fun x : ℝ => iteratedDeriv m f (c * x + d)) σ =
        deriv (iteratedDeriv m f) (c * σ + d) * c := hinnerH.deriv
    rw [deriv_const_mul _ hinnerH.differentiableAt, hderiv, iteratedDeriv_succ]
    ring

/-! ## (10) Bounds for the cutoff pair

`φ` is smooth with compact support, so `m! `-free constants bound `|φ^(m)|`; that gives the
uniform bound `‖(φ(v·/N))^(i)‖ ≤ (8/5)^i · M i` on the effective range `v/N ≤ 8/5` (outside which
`Jphi` vanishes anyway), and then the Leibniz bound for the product `ψ`. -/

/-- The derivatives of the cutoff are uniformly bounded. -/
private theorem exists_iteratedDeriv_phi_bound107 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) :
    ∃ M : ℕ → ℝ, ∀ (m : ℕ) (x : ℝ), ‖iteratedDeriv m ϕ x‖ ≤ M m := by
  have hsupp : ∀ m : ℕ, HasCompactSupport (iteratedDeriv m ϕ) := by
    intro m
    induction m with
    | zero => simpa using hϕ.compact
    | succ m ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv
  choose M hM using fun m : ℕ =>
    (hsupp m).exists_bound_of_continuous (hϕ.smooth.continuous_iteratedDeriv m (by simp))
  exact ⟨M, fun m x => hM m x⟩

/-- Uniform bounds for the derivatives of the two cutoff factors of `ψ`. -/
private theorem exists_iteratedDeriv_cutoff_bound107 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {N v : ℝ}
    (hv0 : (2 / 5 : ℝ) ≤ v / N) (hv1 : v / N ≤ 8 / 5) :
    ∃ R : ℕ → ℝ, ∀ (m : ℕ) (σ : ℝ),
      ‖iteratedDeriv m (fun τ : ℝ => ϕ (v * τ / N)) σ‖ ≤ R m := by
  obtain ⟨M, hM⟩ := exists_iteratedDeriv_phi_bound107 hϕ
  refine ⟨fun m => (8 / 5 : ℝ) ^ m * M m, fun m σ => ?_⟩
  have hfac : iteratedDeriv m (fun τ : ℝ => ϕ (v * τ / N)) σ =
      (v / N) ^ m * iteratedDeriv m ϕ (v * σ / N) := by
    have h := iteratedDeriv_affine_comp107 hϕ.smooth (v / N) 0 m σ
    have harg : ∀ x : ℝ, v * x / N = (v / N) * x + 0 := by
      intro x
      ring
    simpa only [harg] using h
  rw [hfac, norm_mul, norm_pow]
  have hnv : ‖v / N‖ = v / N := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [hnv]
  exact mul_le_mul (pow_le_pow_left₀ (by linarith) hv1 m) (hM m (v * σ / N)) (norm_nonneg _)
    (by positivity)

/-- The Leibniz bound for `iteratedDeriv` of a product of real-valued functions. -/
private theorem norm_iteratedDeriv_mul_le107_real {f g : ℝ → ℝ} {n : ℕ}
    (hf : ContDiff ℝ (n : ℕ∞) f) (hg : ContDiff ℝ (n : ℕ∞) g) (x : ℝ) :
    ‖iteratedDeriv n (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedDeriv i f x‖ *
        ‖iteratedDeriv (n - i) g x‖ := by
  calc ‖iteratedDeriv n (fun y => f y * g y) x‖
      = ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
          ‖iteratedFDeriv ℝ (n - i) g x‖ := norm_iteratedFDeriv_mul_le hf hg x le_rfl
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedDeriv i f x‖ *
          ‖iteratedDeriv (n - i) g x‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
          norm_iteratedFDeriv_eq_norm_iteratedDeriv]

/-- Uniform bounds for the derivatives of the cutoff pair `ψ(σ) = φ(vσ/N) φ(v(1-σ)/N)`. -/
private theorem exists_iteratedDeriv_psi_bound107 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) :
    ∃ R : ℕ → ℝ, ∀ (N v : ℝ), 0 < N → (2 / 5 : ℝ) ≤ v / N → v / N ≤ 8 / 5 →
      ∀ (m : ℕ) (σ : ℝ),
      ‖iteratedDeriv m (fun τ : ℝ => ϕ (v * τ / N) * ϕ (v * (1 - τ) / N)) σ‖ ≤ R m := by
  obtain ⟨M, hM⟩ := exists_iteratedDeriv_phi_bound107 hϕ
  set A1 : ℕ → ℝ := fun m => (8 / 5 : ℝ) ^ m * |M m| with hA1
  have hfac1 : ∀ (N v : ℝ), (2 / 5 : ℝ) ≤ v / N → v / N ≤ 8 / 5 → ∀ (m : ℕ) (σ : ℝ),
      ‖iteratedDeriv m (fun τ : ℝ => ϕ (v * τ / N)) σ‖ ≤ A1 m := by
    intro N v hv0 hv1 m σ
    have hfac : iteratedDeriv m (fun τ : ℝ => ϕ (v * τ / N)) σ =
        (v / N) ^ m * iteratedDeriv m ϕ (v * σ / N) := by
      have h := iteratedDeriv_affine_comp107 hϕ.smooth (v / N) 0 m σ
      have harg : ∀ x : ℝ, v * x / N = (v / N) * x + 0 := by
        intro x
        ring
      simpa only [harg] using h
    rw [hfac, norm_mul, norm_pow]
    have hnv : ‖v / N‖ = v / N := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rw [hnv]
    exact mul_le_mul (pow_le_pow_left₀ (by linarith) hv1 m)
      ((hM m (v * σ / N)).trans (le_abs_self _)) (norm_nonneg _) (by positivity)
  have hfac2 : ∀ (N v : ℝ), (2 / 5 : ℝ) ≤ v / N → v / N ≤ 8 / 5 → ∀ (m : ℕ) (σ : ℝ),
      ‖iteratedDeriv m (fun τ : ℝ => ϕ (v * (1 - τ) / N)) σ‖ ≤ A1 m := by
    intro N v hv0 hv1 m σ
    have hfac : iteratedDeriv m (fun τ : ℝ => ϕ (v * (1 - τ) / N)) σ =
        (-(v / N)) ^ m * iteratedDeriv m ϕ (-(v / N) * σ + v / N) := by
      have h := iteratedDeriv_affine_comp107 hϕ.smooth (-(v / N)) (v / N) m σ
      have harg : ∀ x : ℝ, v * (1 - x) / N = (-(v / N)) * x + v / N := by
        intro x
        ring
      simpa only [harg] using h
    rw [hfac, norm_mul, norm_pow]
    have hnv : ‖-(v / N)‖ = v / N := by
      rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rw [hnv]
    exact mul_le_mul (pow_le_pow_left₀ (by linarith) hv1 m)
      ((hM m (-(v / N) * σ + v / N)).trans (le_abs_self _)) (norm_nonneg _) (by positivity)
  refine ⟨fun m => ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * A1 i * A1 (m - i), ?_⟩
  intro N v hN hv0 hv1 m σ
  have hcd1 : ContDiff ℝ (m : ℕ∞) (fun τ : ℝ => ϕ (v * τ / N)) := by
    have h : ContDiff ℝ ((⊤ : ℕ∞)) (fun τ : ℝ => ϕ (v * τ / N)) :=
      hϕ.smooth.comp (by fun_prop)
    exact h.of_le (by simp)
  have hcd2 : ContDiff ℝ (m : ℕ∞) (fun τ : ℝ => ϕ (v * (1 - τ) / N)) := by
    have h : ContDiff ℝ ((⊤ : ℕ∞)) (fun τ : ℝ => ϕ (v * (1 - τ) / N)) :=
      hϕ.smooth.comp (by fun_prop)
    exact h.of_le (by simp)
  refine (norm_iteratedDeriv_mul_le107_real hcd1 hcd2 σ).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul (mul_le_mul le_rfl (hfac1 N v hv0 hv1 i σ) (norm_nonneg _) (by positivity))
    (hfac2 N v hv0 hv1 (m - i) σ) (norm_nonneg _) (by positivity)

/-- The `m`-th derivative of `(1 - s) ^ b`. -/
private theorem iteratedDeriv_one_sub_rpow107 (b : ℝ) {σ : ℝ} (hσ : σ < 1) (m : ℕ) :
    iteratedDeriv m (fun τ : ℝ => (1 - τ) ^ b) σ =
      (-1) ^ m * (∏ i ∈ Finset.range m, (b - (i : ℝ))) *
        (1 - σ) ^ (b - (m : ℝ)) := by
  induction m generalizing σ with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ]
    have hEq : iteratedDeriv m (fun τ : ℝ => (1 - τ) ^ b) =ᶠ[𝓝 σ]
        (fun τ => (-1) ^ m * (∏ i ∈ Finset.range m, (b - (i : ℝ))) *
          (1 - τ) ^ (b - (m : ℝ))) := by
      filter_upwards [eventually_lt_nhds hσ] with τ hτ
      exact ih hτ
    rw [hEq.deriv_eq]
    have hbase : HasDerivAt (fun τ : ℝ => (1 - τ) ^ (b - (m : ℝ)))
        ((b - (m : ℝ)) * (1 - σ) ^ (b - (m : ℝ) - 1) * (-1)) σ := by
      have hinner : HasDerivAt (fun τ : ℝ => 1 - τ) (-1) σ := by
        simpa using (hasDerivAt_id σ).const_sub 1
      have hrw : HasDerivAt (fun y : ℝ => y ^ (b - (m : ℝ)))
          ((b - (m : ℝ)) * (1 - σ) ^ (b - (m : ℝ) - 1)) (1 - σ) :=
        Real.hasDerivAt_rpow_const (Or.inl (by linarith : (1 : ℝ) - σ ≠ 0))
      exact hrw.comp σ hinner
    have hfin := hbase.const_mul ((-1) ^ m * (∏ i ∈ Finset.range m, (b - (i : ℝ))))
    rw [hfin.deriv, Finset.prod_range_succ]
    have hexp : (1 - σ) ^ (b - (m : ℝ) - 1) = (1 - σ) ^ (b - ((m : ℝ) + 1)) := by
      congr 1
      ring
    have hneg : (-1 : ℝ) ^ (m + 1) = (-1) ^ m * (-1) := pow_succ _ m
    rw [hexp, hneg]
    push_cast
    ring

/-- Uniform bound for the derivatives of `(1 - s) ^ b` with `b ∈ (-1,0]`. -/
private theorem norm_iteratedDeriv_one_sub_rpow_bound107 {b : ℝ} (hb0 : -1 < b) (hb1 : b ≤ 0)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (1/5 : ℝ) (4/5)) (m : ℕ) :
    ‖iteratedDeriv m (fun τ : ℝ => (1 - τ) ^ b) σ‖ ≤ ((m.factorial : ℕ) : ℝ) * 5 ^ (m + 1) := by
  have hσ1 : σ < 1 := by linarith [hσ.2]
  have h1σ0 : 0 < 1 - σ := by linarith [hσ.2]
  have h1σ1 : 1 - σ ≤ 1 := by linarith [hσ.1]
  have h1σ15 : (1 / 5 : ℝ) ≤ 1 - σ := by linarith [hσ.2]
  have hfac : |∏ i ∈ Finset.range m, (b - (i : ℝ))| ≤ ((m.factorial : ℕ) : ℝ) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_range_succ, Nat.factorial_succ, abs_mul]
      have h1 : |b - (m : ℝ)| ≤ (m : ℝ) + 1 := by
        rw [abs_le]
        constructor <;> linarith
      push_cast
      have h2 : |∏ i ∈ Finset.range m, (b - ↑i)| * |b - ↑m| ≤ ↑(m.factorial) * (↑m + 1) :=
        mul_le_mul ih h1 (abs_nonneg _) (by positivity)
      linarith [h2]
  have hneg : |(-1 : ℝ) ^ m| = 1 := by
    rw [abs_pow]
    norm_num
  have hpow : |(1 - σ) ^ (b - (m : ℝ))| ≤ 5 ^ (m + 1) := by
    have hpos : 0 < (1 - σ) ^ (b - (m : ℝ)) := Real.rpow_pos_of_pos h1σ0 _
    rw [abs_of_pos hpos]
    have hstep : (1 - σ) ^ (b - (m : ℝ)) ≤ (1 - σ) ^ (-((m : ℝ) + 1)) := by
      refine Real.rpow_le_rpow_of_exponent_ge h1σ0 h1σ1 ?_
      linarith
    have hneg' : (1 - σ) ^ (-((m : ℝ) + 1)) = ((1 - σ)⁻¹) ^ (m + 1) := by
      have hcast : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      have h1 : ((1 - σ)⁻¹) ^ ((m : ℝ) + 1) = ((1 - σ)⁻¹) ^ (m + 1) := by
        rw [hcast, Real.rpow_natCast]
      rw [← h1, Real.inv_rpow (le_of_lt h1σ0), ← Real.rpow_neg (le_of_lt h1σ0)]
    have hinv : (1 - σ)⁻¹ ≤ 5 := by
      rw [inv_le_comm₀ h1σ0 (by norm_num : (0 : ℝ) < 5)]
      norm_num
      linarith
    calc (1 - σ) ^ (b - (m : ℝ)) ≤ (1 - σ) ^ (-((m : ℝ) + 1)) := hstep
      _ = ((1 - σ)⁻¹) ^ (m + 1) := hneg'
      _ ≤ 5 ^ (m + 1) := pow_le_pow_left₀ (by positivity) hinv (m + 1)
  rw [iteratedDeriv_one_sub_rpow107 b hσ1 m, Real.norm_eq_abs, abs_mul, abs_mul, hneg, one_mul]
  exact mul_le_mul hfac hpow (abs_nonneg _) (by positivity)

/-- Uniform derivative bounds for the modulus part of the sigma amplitude of display 7.21, on the
effective range `v/N ∈ [2/5, 8/5]`. -/
private theorem exists_norm_iteratedDeriv_amp_bound107 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) :
    ∃ D : ℕ → ℝ, ∀ (N v : ℝ), 0 < N → (2 / 5 : ℝ) ≤ v / N → v / N ≤ 8 / 5 →
      ∀ (s₁ s₂ : ℝ), 0 < s₁ → s₁ ≤ 1 → 0 < s₂ → s₂ ≤ 1 →
      ∀ (m : ℕ) {σ : ℝ}, σ ∈ Set.Icc (1/5 : ℝ) (4/5) →
      ‖iteratedDeriv m (fun τ => τ ^ (s₁ - 1) * (1 - τ) ^ (s₂ - 1) *
        (ϕ (v * τ / N) * ϕ (v * (1 - τ) / N))) σ‖ ≤ D m := by
  obtain ⟨R, hR⟩ := exists_iteratedDeriv_psi_bound107 hϕ
  set P : ℕ → ℝ := fun i => ((i.factorial : ℕ) : ℝ) * 5 ^ (i + 1) with hP
  refine ⟨fun m => ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * P j * P (i - j)) * R (m - i), ?_⟩
  intro N v hN hv0 hv1 s₁ s₂ h₁ h₁' h₂ h₂' m σ hσ
  have ha0 : -1 < s₁ - 1 := by linarith
  have ha1 : s₁ - 1 ≤ 0 := by linarith
  have hb0 : -1 < s₂ - 1 := by linarith
  have hb1 : s₂ - 1 ≤ 0 := by linarith
  have hσ0 : 0 < σ := by linarith [hσ.1]
  have h1σ : (0 : ℝ) < 1 - σ := by linarith [hσ.2]
  have hσs : σ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have h1σ01 : (1 - σ) ∈ Set.Icc (1/5 : ℝ) (4/5) := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hs : UniqueDiffOn ℝ (Set.Ioo (0 : ℝ) 1) := uniqueDiffOn_Ioo _ _
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 σ := IsOpen.mem_nhds isOpen_Ioo hσs
  have hf1_at : ∀ n : ℕ∞, ContDiffAt ℝ n (fun τ : ℝ => τ ^ (s₁ - 1)) σ :=
    fun n => contDiffAt_id.rpow_const_of_ne (by linarith : σ ≠ 0)
  have hf2_at : ∀ n : ℕ∞, ContDiffAt ℝ n (fun τ : ℝ => (1 - τ) ^ (s₂ - 1)) σ :=
    fun n => (contDiffAt_const.sub contDiffAt_id).rpow_const_of_ne (by linarith : (1 : ℝ) - σ ≠ 0)
  have hpsi_cd : ∀ n : ℕ∞,
      ContDiff ℝ n (fun τ : ℝ => ϕ (v * τ / N) * ϕ (v * (1 - τ) / N)) := by
    intro n
    have h1 : ContDiff ℝ ((⊤ : ℕ∞)) (fun τ : ℝ => ϕ (v * τ / N)) :=
      hϕ.smooth.comp (by fun_prop)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞)) (fun τ : ℝ => ϕ (v * (1 - τ) / N)) :=
      hϕ.smooth.comp (by fun_prop)
    exact (h1.mul h2).of_le (by simp)
  have hpsi_at : ∀ n : ℕ∞,
      ContDiffAt ℝ n (fun τ : ℝ => ϕ (v * τ / N) * ϕ (v * (1 - τ) / N)) σ :=
    fun n => (hpsi_cd n).contDiffAt
  have hfun : (fun τ => τ ^ (s₁ - 1) * (1 - τ) ^ (s₂ - 1) *
        (ϕ (v * τ / N) * ϕ (v * (1 - τ) / N))) =
      (fun τ : ℝ => τ ^ (s₁ - 1) * (1 - τ) ^ (s₂ - 1)) *
        fun τ : ℝ => ϕ (v * τ / N) * ϕ (v * (1 - τ) / N) := by
    funext τ
    rfl
  have hf1_on : ∀ n : ℕ∞, ContDiffOn ℝ n (fun τ : ℝ => τ ^ (s₁ - 1)) (Set.Ioo (0 : ℝ) 1) :=
    fun n => contDiffOn_id.rpow_const_of_ne
      (fun x hx => ne_of_gt (by linarith [hx.1] : (0 : ℝ) < x))
  have hf2_on : ∀ n : ℕ∞,
      ContDiffOn ℝ n (fun τ : ℝ => (1 - τ) ^ (s₂ - 1)) (Set.Ioo (0 : ℝ) 1) :=
    fun n => (contDiffOn_const.sub contDiffOn_id).rpow_const_of_ne
      (fun x hx => ne_of_gt (by linarith [hx.2] : (0 : ℝ) < 1 - x))
  have hamp_at : ContDiffAt ℝ (m : ℕ∞)
        (fun τ => τ ^ (s₁ - 1) * (1 - τ) ^ (s₂ - 1) * (ϕ (v * τ / N) * ϕ (v * (1 - τ) / N))) σ := by
    rw [hfun]
    exact ((hf1_at _).mul (hf2_at _)).mul (hpsi_at _)
  rw [← iteratedDerivWithin_eq_iteratedDeriv hs hamp_at hσs, hfun]
  have hpsi_on : ContDiffOn ℝ (m : ℕ∞)
      (fun τ : ℝ => ϕ (v * τ / N) * ϕ (v * (1 - τ) / N)) (Set.Ioo (0 : ℝ) 1) :=
    (hpsi_cd (m : ℕ∞)).contDiffOn
  refine (norm_iteratedDerivWithin_mul_le107_real ((hf1_on (m : ℕ∞)).mul (hf2_on (m : ℕ∞)))
    hpsi_on hs hσs (n := m)).trans ?_
  refine Finset.sum_le_sum fun i hi => ?_
  have hi_le : i ≤ m := by
    have := Finset.mem_range.mp hi
    omega
  have hstage1 : ‖iteratedDerivWithin i
      (fun τ : ℝ => τ ^ (s₁ - 1) * (1 - τ) ^ (s₂ - 1)) (Set.Ioo (0 : ℝ) 1) σ‖ ≤
      ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * P j * P (i - j) := by
    refine ((norm_iteratedDerivWithin_mul_le107_real (hf1_on (i : ℕ∞)) (hf2_on (i : ℕ∞))
      hs hσs (n := i))).trans ?_
    refine Finset.sum_le_sum fun j _ => ?_
    have hj1 : ‖iteratedDerivWithin j (fun τ : ℝ => τ ^ (s₁ - 1))
        (Set.Ioo (0 : ℝ) 1) σ‖ ≤ P j := by
      rw [iteratedDerivWithin_eq_iteratedDeriv hs (hf1_at (j : ℕ∞)) hσs]
      exact norm_iteratedDeriv_rpow_bound107 ha0 ha1 hσ j
    have hj2 : ‖iteratedDerivWithin (i - j) (fun τ : ℝ => (1 - τ) ^ (s₂ - 1))
        (Set.Ioo (0 : ℝ) 1) σ‖ ≤ P (i - j) := by
      rw [iteratedDerivWithin_eq_iteratedDeriv hs (hf2_at ((i - j : ℕ) : ℕ∞)) hσs]
      exact norm_iteratedDeriv_one_sub_rpow_bound107 hb0 hb1 hσ (i - j)
    exact mul_le_mul (mul_le_mul le_rfl hj1 (norm_nonneg _) (by positivity)) hj2
      (norm_nonneg _) (by positivity)
  have hstage2 : ‖iteratedDerivWithin (m - i)
      (fun τ : ℝ => ϕ (v * τ / N) * ϕ (v * (1 - τ) / N)) (Set.Ioo (0 : ℝ) 1) σ‖ ≤
      R (m - i) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs (hpsi_at ((m - i : ℕ) : ℕ∞)) hσs]
    exact hR N v hN hv0 hv1 (m - i) σ
  exact mul_le_mul (mul_le_mul le_rfl hstage1 (norm_nonneg _) (by positivity)) hstage2
    (norm_nonneg _) (by positivity)

/-- The phase factor of display 7.21. -/
private noncomputable def vexp107 (t₁ t₂ : ℝ) (σ : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((t₁ * Real.log σ + t₂ * Real.log (1 - σ) : ℝ) : ℂ))

/-- Its derivative. -/
private noncomputable def vderiv107 (t₁ t₂ : ℝ) (σ : ℝ) : ℂ :=
  Complex.I * ((t₁ / σ - t₂ / (1 - σ) : ℝ) : ℂ) * vexp107 t₁ t₂ σ

/-! ## (11) One integration by parts in `sigma`

One step of the parts argument, on any interval `[a,b] ⊂ (0,1)`.
-/

/-- One integration by parts in `sigma` for the phase `t₁ log s + t₂ log (1-s)`, on any interval
`[a,b] ⊂ (0,1)`. -/
private theorem IBP_step107 {A : ℝ → ℂ} {t₁ t₂ a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hzan0 : A a * ((phaserec107 t₁ t₂ a : ℝ) : ℂ) = 0)
    (hzan1 : A b * ((phaserec107 t₁ t₂ b : ℝ) : ℂ) = 0)
    (hu_cont : ContinuousOn (fun σ => A σ * ((phaserec107 t₁ t₂ σ : ℝ) : ℂ)) (Set.uIcc a b))
    (hv_cont : ContinuousOn (vexp107 t₁ t₂) (Set.uIcc a b))
    (huu' : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun σ => A σ * ((phaserec107 t₁ t₂ σ : ℝ) : ℂ))
        (deriv (fun σ => A σ * ((phaserec107 t₁ t₂ σ : ℝ) : ℂ)) x) x)
    (hvv' : ∀ x ∈ Set.Ioo a b, HasDerivAt (vexp107 t₁ t₂) (vderiv107 t₁ t₂ x) x)
    (hui : IntervalIntegrable
      (deriv (fun σ => A σ * ((phaserec107 t₁ t₂ σ : ℝ) : ℂ))) volume a b)
    (hvi : IntervalIntegrable (vderiv107 t₁ t₂) volume a b)
    (hne : ∀ x ∈ Set.Icc a b, dph107 t₁ t₂ x ≠ 0) :
    (∫ x in a..b, A x * vexp107 t₁ t₂ x) =
      Complex.I * ∫ x in a..b,
        deriv (fun σ => A σ * ((phaserec107 t₁ t₂ σ : ℝ) : ℂ)) x * vexp107 t₁ t₂ x := by
  have hmin : min a b = a := min_eq_left hab
  have hmax : max a b = b := max_eq_right hab
  have hib : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hmem : ∀ x, x ∈ Set.Ioo (min a b) (max a b) → x ∈ Set.Ioo a b := by
    intro x hx
    rwa [hmin, hmax] at hx
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun σ => A σ * ((phaserec107 t₁ t₂ σ : ℝ) : ℂ))
    (v := vexp107 t₁ t₂)
    (u' := deriv (fun σ => A σ * ((phaserec107 t₁ t₂ σ : ℝ) : ℂ)))
    (v' := vderiv107 t₁ t₂)
    hu_cont hv_cont
    (fun x hx => huu' x (hmem x hx))
    (fun x hx => hvv' x (hmem x hx)) hui hvi
  have hleft : (∫ x in a..b,
      (fun σ => A σ * ((phaserec107 t₁ t₂ σ : ℝ) : ℂ)) x * vderiv107 t₁ t₂ x) =
      Complex.I * ∫ x in a..b, A x * vexp107 t₁ t₂ x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [hib] at hx
    have hx1 : (0 : ℝ) < x := by linarith [hx.1]
    have hx2 : x < 1 := by linarith [hx.2]
    have hr := phaserec_mul_deriv107 (t₁ := t₁) (t₂ := t₂) (σ := x) hx1 hx2 (hne x hx)
    have hrc : ((phaserec107 t₁ t₂ x : ℝ) : ℂ) *
        ((t₁ / x - t₂ / (1 - x) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hr, Complex.ofReal_one]
    unfold vderiv107 vexp107
    calc (A x * ((phaserec107 t₁ t₂ x : ℝ) : ℂ)) *
          (Complex.I * ((t₁ / x - t₂ / (1 - x) : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((t₁ * Real.log x + t₂ * Real.log (1 - x) : ℝ) : ℂ)))
        = Complex.I * (A x *
            Complex.exp (Complex.I * ((t₁ * Real.log x + t₂ * Real.log (1 - x) : ℝ) : ℂ))) *
            (((phaserec107 t₁ t₂ x : ℝ) : ℂ) * ((t₁ / x - t₂ / (1 - x) : ℝ) : ℂ)) := by
          ring
      _ = Complex.I * (A x *
            Complex.exp (Complex.I * ((t₁ * Real.log x + t₂ * Real.log (1 - x) : ℝ) : ℂ))) := by
          rw [hrc, mul_one]
  rw [hleft] at hparts
  have hbnd : A b * ((phaserec107 t₁ t₂ b : ℝ) : ℂ) * vexp107 t₁ t₂ b -
      A a * ((phaserec107 t₁ t₂ a : ℝ) : ℂ) * vexp107 t₁ t₂ a = 0 := by
    rw [hzan1, hzan0]
    ring
  rw [hbnd] at hparts
  simp only [zero_sub] at hparts
  set X : ℂ := ∫ x in a..b, A x * vexp107 t₁ t₂ x with hXdef
  set Y : ℂ := ∫ x in a..b,
    deriv (fun σ => A σ * ((phaserec107 t₁ t₂ σ : ℝ) : ℂ)) x * vexp107 t₁ t₂ x with hYdef
  have hk : Complex.I * X = -Y := by
    rw [hXdef, hYdef]
    exact hparts
  have h3 : Complex.I * (Complex.I * X) = -X := by
    rw [← mul_assoc, Complex.I_mul_I]
    ring
  have h2 : -(Complex.I * (Complex.I * X)) = Complex.I * Y := by
    rw [hk]
    ring
  rw [h3, neg_neg] at h2
  exact h2

/-! ## (12) Smoothness of the reciprocal phase derivative, and the iteration step

The iteration differentiates `A ↦ (A · (1/Φ'))'` on the whole interval `(0,1)`, where `1/Φ'` is
smooth.  This section records that smoothness in the form the induction needs, and the fact that
the induced map sends smooth functions to smooth functions (so every iterate is smooth). -/

/-- `phaserec107`, as a complex-valued function, is smooth on the effective interval. -/
private theorem contDiffOn_phaserec107 {t₁ t₂ : ℝ} (hprod : t₁ * t₂ < 0) :
    ∀ n : ℕ∞,
      ContDiffOn ℝ n (fun τ => ((phaserec107 t₁ t₂ τ : ℝ) : ℂ)) (Set.Ioo (0 : ℝ) 1) := by
  intro n
  have ht1 : t₁ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact lt_irrefl 0 hprod
  have ht2 : t₂ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    exact lt_irrefl 0 hprod
  have haff_eq : (fun τ : ℝ => dph107 t₁ t₂ τ) = fun τ : ℝ => t₁ - (t₁ + t₂) * τ := by
    funext τ
    simp only [dph107]
    ring
  have hne : ∀ τ ∈ Set.Ioo (0 : ℝ) 1, dph107 t₁ t₂ τ ≠ 0 := by
    intro τ hτ
    have h0 : 0 < τ := by linarith [hτ.1]
    have h1 : τ < 1 := by linarith [hτ.2]
    have hlow := sigma_phase_lower84 hprod h0 h1
    have hPhi : t₁ / τ - t₂ / (1 - τ) ≠ 0 := by
      intro h
      rw [h, abs_zero] at hlow
      have hu' : 0 < |t₁| + |t₂| := by
        have h1' := abs_pos.mpr ht1
        have h2' := abs_pos.mpr ht2
        linarith
      linarith
    rw [dph_eq_mul107 h0 h1]
    exact mul_ne_zero (mul_ne_zero h0.ne' (by linarith : (1 : ℝ) - τ ≠ 0)) hPhi
  have haff : ContDiffOn ℝ n (fun τ : ℝ => dph107 t₁ t₂ τ) (Set.Ioo (0 : ℝ) 1) := by
    have h : ContDiff ℝ n (fun τ : ℝ => dph107 t₁ t₂ τ) := by
      rw [haff_eq]
      fun_prop
    exact h.contDiffOn
  have hinv := haff.inv hne
  have hfun : (fun τ => ((phaserec107 t₁ t₂ τ : ℝ) : ℂ)) =
      (fun τ : ℝ => ((τ * (1 - τ) : ℝ) : ℂ)) *
        (fun τ : ℝ => (((dph107 t₁ t₂ τ)⁻¹ : ℝ) : ℂ)) := by
    funext τ
    simp only [phaserec107, Pi.mul_apply, div_eq_mul_inv]
    push_cast
    ring
  rw [hfun]
  exact (contDiff_quad107 n).contDiffOn.mul ((Complex.ofRealCLM.contDiff).comp_contDiffOn hinv)

/-- The iteration preserves smoothness on the effective interval. -/
private theorem contDiffOn_iterStep107 {A : ℝ → ℂ} {t₁ t₂ : ℝ} (hprod : t₁ * t₂ < 0)
    (hA : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A (Set.Ioo (0 : ℝ) 1)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun σ => deriv (fun τ => A τ * ((phaserec107 t₁ t₂ τ : ℝ) : ℂ)) σ)
      (Set.Ioo (0 : ℝ) 1) := by
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun τ => A τ * ((phaserec107 t₁ t₂ τ : ℝ) : ℂ)) (Set.Ioo (0 : ℝ) 1) :=
    hA.mul (contDiffOn_phaserec107 hprod (⊤ : ℕ∞))
  exact hsm.deriv_of_isOpen isOpen_Ioo (by simp)

/-! ## (13) The iterated amplitude of the integration-by-parts scheme

`A₀ = A`, `A_{j+1} = (A_j · 1/Φ')'`.  This section defines the scheme, records that every
iterate is smooth on the effective interval, and relates `iteratedDerivWithin` of a `deriv` to
the next order (the bridge the quantitative induction uses). -/

/-- The iterated amplitude of the integration-by-parts scheme in `sigma`. -/
private noncomputable def iterAmp107 (A : ℝ → ℂ) (t₁ t₂ : ℝ) : ℕ → ℝ → ℂ
  | 0 => A
  | (j + 1) =>
    fun σ => deriv (fun τ => iterAmp107 A t₁ t₂ j τ * ((phaserec107 t₁ t₂ τ : ℝ) : ℂ)) σ

/-- Every iterate is smooth on the effective interval. -/
private theorem contDiffOn_iterAmp107 {A : ℝ → ℂ} {t₁ t₂ : ℝ} (hprod : t₁ * t₂ < 0)
    (hA : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A (Set.Ioo (0 : ℝ) 1)) :
    ∀ j : ℕ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iterAmp107 A t₁ t₂ j)
        (Set.Ioo (0 : ℝ) 1) := by
  intro j
  induction j with
  | zero => simpa [iterAmp107] using hA
  | succ j ih =>
    exact contDiffOn_iterStep107 hprod ih

/-- `iteratedDerivWithin` of a `deriv` is the next order (on an open set). -/
private theorem iteratedDerivWithin_deriv107 {f : ℝ → ℂ} {s : Set ℝ} (hs : IsOpen s) (m : ℕ) {σ : ℝ}
    (hσ : σ ∈ s) :
    iteratedDerivWithin m (fun τ => deriv f τ) s σ = iteratedDerivWithin (m + 1) f s σ := by
  rw [iteratedDerivWithin_succ']
  exact iteratedDerivWithin_congr (fun x hx => (derivWithin_of_isOpen hs hx).symm) hσ

/-! ## (14) The quantitative iteration

Each integration by parts costs exactly one factor `1/u`: if every derivative of `A_j` up to
order `m` is at most `c m / u^j`, then every derivative of `A_{j+1} = (A_j / Φ')'` up to order
`m` is at most `(Σ_i C(m+1,i) c i ĉ (m+1-i)) / u^(j+1)`, where `ĉ` is the bound for `1/Φ'`
(`norm_iteratedDeriv_phaserec_bound107`). -/

/-- The quantitative iteration bound for the amplitudes of the parts scheme. -/
private theorem exists_iterAmp_bound107 {A : ℝ → ℂ} {t₁ t₂ : ℝ} (hprod : t₁ * t₂ < 0) {u : ℝ}
    (hu : u = |t₁| + |t₂|) (hu0 : 0 < u)
    (hAsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A (Set.Ioo (0 : ℝ) 1))
    (hA : ∃ c : ℕ → ℝ, ∀ (m : ℕ) {σ : ℝ}, σ ∈ Set.Ioo (1/5 : ℝ) (4 / 5) →
      ‖iteratedDerivWithin m A (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖ ≤ c m) :
    ∀ j : ℕ, ∃ c : ℕ → ℝ, ∀ (m : ℕ) {σ : ℝ}, σ ∈ Set.Ioo (1/5 : ℝ) (4 / 5) →
      ‖iteratedDerivWithin m (iterAmp107 A t₁ t₂ j) (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖ ≤
        c m / u ^ j := by
  -- the bound for the reciprocal phase derivative, and its smoothness, on the smaller interval
  have hsub : Set.Ioo (1/5 : ℝ) (4 / 5) ⊆ Set.Ioo (0 : ℝ) 1 :=
    Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
  have hrsm : ∀ n : ℕ∞,
      ContDiffOn ℝ n (fun τ => ((phaserec107 t₁ t₂ τ : ℝ) : ℂ)) (Set.Ioo (1/5 : ℝ) (4 / 5)) :=
    fun n => (contDiffOn_phaserec107 hprod n).mono hsub
  set ĉ : ℕ → ℝ := fun p => 2 * (∑ i ∈ Finset.range (p + 1), (p.choose i : ℝ) *
    (((p - i).factorial : ℕ) : ℝ) * 25 ^ (p - i + 1)) with hĉ
  have hrc : ∀ (p : ℕ) {σ : ℝ}, σ ∈ Set.Ioo (1/5 : ℝ) (4 / 5) →
      ‖iteratedDerivWithin p (fun τ => ((phaserec107 t₁ t₂ τ : ℝ) : ℂ))
        (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖ ≤ ĉ p / u := by
    intro p σ hσ
    have hat : ContDiffAt ℝ (p : ℕ∞) (fun τ => ((phaserec107 t₁ t₂ τ : ℝ) : ℂ)) σ :=
      (hrsm (p : ℕ∞)).contDiffAt (IsOpen.mem_nhds isOpen_Ioo hσ)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo _ _) hat hσ]
    exact norm_iteratedDeriv_phaserec_bound107 hprod hu hu0 p ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  intro j
  induction j with
  | zero =>
    obtain ⟨c, hc⟩ := hA
    exact ⟨c, fun m σ hσ => by simpa [iterAmp107] using hc m hσ⟩
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨fun m => ∑ i ∈ Finset.range (m + 2), ((m + 1).choose i : ℝ) * c i * ĉ (m + 1 - i),
      fun m σ hσ => ?_⟩
    -- the `m`-th derivative of `A_{j+1}` is the `(m+1)`-st of `A_j * (1/Φ')`
    have hd : iteratedDerivWithin m (iterAmp107 A t₁ t₂ (j + 1)) (Set.Ioo (1/5 : ℝ) (4 / 5)) σ =
        iteratedDerivWithin (m + 1)
          (fun τ => iterAmp107 A t₁ t₂ j τ * ((phaserec107 t₁ t₂ τ : ℝ) : ℂ))
          (Set.Ioo (1/5 : ℝ) (4 / 5)) σ := by
      simp only [iterAmp107]
      rw [iteratedDerivWithin_deriv107 isOpen_Ioo m hσ]
    rw [hd]
    -- Leibniz
    have hAon : ContDiffOn ℝ (((m + 1 : ℕ) : ℕ∞))
        (iterAmp107 A t₁ t₂ j) (Set.Ioo (1/5 : ℝ) (4 / 5)) :=
      ((contDiffOn_iterAmp107 hprod hAsm) j).mono hsub |>.of_le (by simp)
    have hron : ContDiffOn ℝ (((m + 1 : ℕ) : ℕ∞))
        (fun τ => ((phaserec107 t₁ t₂ τ : ℝ) : ℂ)) (Set.Ioo (1/5 : ℝ) (4 / 5)) :=
      hrsm _
    refine (norm_iteratedDerivWithin_mul_le107 hAon hron (uniqueDiffOn_Ioo _ _) hσ (n := m + 1)).trans ?_
    -- bound each term and sum
    have hterm : ∀ i ∈ Finset.range (m + 2),
        ((m + 1).choose i : ℝ) *
          ‖iteratedDerivWithin i (iterAmp107 A t₁ t₂ j) (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖ *
          ‖iteratedDerivWithin (m + 1 - i) (fun τ => ((phaserec107 t₁ t₂ τ : ℝ) : ℂ))
            (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖ ≤
        ((m + 1).choose i : ℝ) * c i * ĉ (m + 1 - i) / u ^ (j + 1) := by
      intro i hi
      have hi_le : i ≤ m + 1 := by
        have := Finset.mem_range.mp hi
        omega
      have h1 : ‖iteratedDerivWithin i (iterAmp107 A t₁ t₂ j) (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖ ≤
          c i / u ^ j := hc i hσ
      have h2 : ‖iteratedDerivWithin (m + 1 - i) (fun τ => ((phaserec107 t₁ t₂ τ : ℝ) : ℂ))
          (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖ ≤ ĉ (m + 1 - i) / u := hrc (m + 1 - i) hσ
      have huj' : (0 : ℝ) < u ^ j := pow_pos hu0 j
      have hc0 : 0 ≤ c i := by
        have h : 0 ≤ c i / u ^ j := le_trans (norm_nonneg _) h1
        have h2' := mul_nonneg h huj'.le
        rwa [div_mul_cancel₀ _ huj'.ne'] at h2'
      have hĉ0 : 0 ≤ ĉ (m + 1 - i) := by
        have h : 0 ≤ ĉ (m + 1 - i) / u := le_trans (norm_nonneg _) h2
        have h2' := mul_nonneg h hu0.le
        rwa [div_mul_cancel₀ _ hu0.ne'] at h2'
      have hu0' : (0 : ℝ) < u ^ (j + 1) := pow_pos hu0 _
      have huj : (0 : ℝ) < u ^ j := pow_pos hu0 _
      have hsplit : ((m + 1).choose i : ℝ) * (c i / u ^ j) * (ĉ (m + 1 - i) / u) =
          ((m + 1).choose i : ℝ) * c i * ĉ (m + 1 - i) / u ^ (j + 1) := by
        field_simp
        ring
      calc ((m + 1).choose i : ℝ) *
            ‖iteratedDerivWithin i (iterAmp107 A t₁ t₂ j) (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖ *
            ‖iteratedDerivWithin (m + 1 - i) (fun τ => ((phaserec107 t₁ t₂ τ : ℝ) : ℂ))
              (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖
          ≤ ((m + 1).choose i : ℝ) * (c i / u ^ j) * (ĉ (m + 1 - i) / u) := by
            refine mul_le_mul (mul_le_mul le_rfl h1 (norm_nonneg _) (by positivity)) h2
              (norm_nonneg _) (by positivity)
        _ = ((m + 1).choose i : ℝ) * c i * ĉ (m + 1 - i) / u ^ (j + 1) := hsplit
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_div]

/-! ## (15) Support of the iterates, and the fixed phase factors

The iterates stay supported in `[1/5,4/5]`, so every `A_j` vanishes at `1/4` and `7/10` and the
boundary terms of every parts step die.  The phase factor `e^{iΦ}` and its derivative do not
depend on the amplitude, so their continuity, differentiability and integrability are recorded
once. -/

/-- All iterates vanish outside `[1/5,4/5]`. -/
private theorem iterAmp_out107 {A : ℝ → ℂ} (t₁ t₂ : ℝ)
    (hA : ∀ σ, σ ∉ Set.Icc (1/5 : ℝ) (4 / 5) → A σ = 0) :
    ∀ j : ℕ, ∀ σ, σ ∉ Set.Icc (1/5 : ℝ) (4 / 5) → iterAmp107 A t₁ t₂ j σ = 0 := by
  intro j
  induction j with
  | zero => simpa [iterAmp107] using hA
  | succ j ih =>
    intro σ hσ
    simp only [iterAmp107]
    have hopen : ∀ᶠ τ in 𝓝 σ, τ ∉ Set.Icc (1 / 5 : ℝ) (4 / 5) :=
      isClosed_Icc.isOpen_compl.mem_nhds hσ
    have hev : (fun τ => iterAmp107 A t₁ t₂ j τ * ((phaserec107 t₁ t₂ τ : ℝ) : ℂ)) =ᶠ[𝓝 σ]
        (fun _ => 0) := by
      filter_upwards [hopen] with τ hτ
      rw [ih τ hτ]
      simp
    exact hev.deriv_eq.trans (by simp)

/-- The phase is continuous on any interval inside `(0,1)`. -/
private theorem vexp_continuousOn107 (t₁ t₂ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ContinuousOn (vexp107 t₁ t₂) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  unfold vexp107
  have hlog1 : ContinuousOn (fun x : ℝ => Real.log x) (Set.Icc a b) :=
    Real.continuousOn_log.mono (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith [hx.1])
  have hlog2 : ContinuousOn (fun x : ℝ => Real.log (1 - x)) (Set.Icc a b) := by
    have hsub : Set.MapsTo (fun x : ℝ => 1 - x) (Set.Icc a b) ({0}ᶜ) := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith [hx.2]
    exact Real.continuousOn_log.comp (by fun_prop) hsub
  have hΦ : ContinuousOn (fun x : ℝ => t₁ * Real.log x + t₂ * Real.log (1 - x))
      (Set.Icc a b) :=
    (hlog1.const_mul t₁).add (hlog2.const_mul t₂)
  exact Complex.continuous_exp.comp_continuousOn
    ((Complex.continuous_ofReal.comp_continuousOn hΦ).const_mul Complex.I)

/-- The phase has the derivative `vderiv107` on the working interval. -/
private theorem vexp_hasDerivAt107 (t₁ t₂ : ℝ) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (vexp107 t₁ t₂) (vderiv107 t₁ t₂ x) x := by
  intro x hx
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have hlog1 : HasDerivAt (fun y : ℝ => Real.log y) (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log (ne_of_gt hx0)
  have hinner : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have hlog2 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-(1 / (1 - x))) x := by
    have h := hinner.log (by linarith : (1 : ℝ) - x ≠ 0)
    convert h using 1
    ring
  have hΦ : HasDerivAt (fun y : ℝ => t₁ * Real.log y + t₂ * Real.log (1 - y))
      (t₁ / x - t₂ / (1 - x)) x := by
    have h := (hlog1.const_mul t₁).add (hlog2.const_mul t₂)
    convert h using 1
    ring
  have hΦc : HasDerivAt
      (fun y : ℝ => ((t₁ * Real.log y + t₂ * Real.log (1 - y) : ℝ) : ℂ))
      (((t₁ / x - t₂ / (1 - x) : ℝ)) : ℂ) x := by
    have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x := x) hΦ
    convert h using 1
    · funext y
      rfl
    · exact (Complex.ofRealCLM_apply _).symm
  have hmul : HasDerivAt
      (fun y : ℝ => Complex.I * ((t₁ * Real.log y + t₂ * Real.log (1 - y) : ℝ) : ℂ))
      (Complex.I * ((t₁ / x - t₂ / (1 - x) : ℝ) : ℂ)) x :=
    hΦc.const_mul Complex.I
  have hmain : HasDerivAt
      (fun y : ℝ => Complex.exp (Complex.I * ((t₁ * Real.log y + t₂ * Real.log (1 - y) : ℝ) : ℂ)))
      (Complex.exp (Complex.I * ((t₁ * Real.log x + t₂ * Real.log (1 - x) : ℝ) : ℂ)) *
        (Complex.I * ((t₁ / x - t₂ / (1 - x) : ℝ) : ℂ))) x := HasDerivAt.cexp hmul
  convert hmain using 1
  · funext y
    rfl
  · unfold vderiv107 vexp107
    ring

/-- `vderiv107` is continuous on any interval inside `(0,1)`. -/
private theorem vderiv_continuousOn107 (t₁ t₂ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ContinuousOn (vderiv107 t₁ t₂) (Set.Icc a b) := by
  have hinv1 : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Icc a b) :=
    continuousOn_inv₀.mono (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith [hx.1])
  have hinv2 : ContinuousOn (fun x : ℝ => (1 - x)⁻¹) (Set.Icc a b) :=
    continuousOn_inv₀.comp (by fun_prop) (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith [hx.2])
  have hF : ContinuousOn (fun x : ℝ => t₁ / x - t₂ / (1 - x)) (Set.Icc a b) := by
    have h1 : ContinuousOn (fun x : ℝ => t₁ / x) (Set.Icc a b) := by
      simpa [div_eq_mul_inv] using hinv1.const_mul t₁
    have h2 : ContinuousOn (fun x : ℝ => t₂ / (1 - x)) (Set.Icc a b) := by
      simpa [div_eq_mul_inv] using hinv2.const_mul t₂
    exact h1.sub h2
  have hv : ContinuousOn (vexp107 t₁ t₂) (Set.Icc a b) := by
    simpa [Set.uIcc_of_le hab] using vexp_continuousOn107 t₁ t₂ ha hab hb
  unfold vderiv107
  exact ((Complex.continuous_ofReal.comp_continuousOn hF).const_mul Complex.I).mul hv

/-- `vderiv107` is interval-integrable on any interval inside `(0,1)`. -/
private theorem vderiv_intervalIntegrable107 (t₁ t₂ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < 1) : IntervalIntegrable (vderiv107 t₁ t₂) volume a b := by
  have hcont : ContinuousOn (vderiv107 t₁ t₂) (Set.uIcc a b) := by
    simpa [Set.uIcc_of_le hab] using vderiv_continuousOn107 t₁ t₂ ha hab hb
  exact hcont.intervalIntegrable

/-- The `k`-fold integration by parts: `∫ A₀ e^{iΦ} = i^k ∫ A_k e^{iΦ}`. -/
private theorem IBP_iter107 {A : ℝ → ℂ} {t₁ t₂ a b : ℝ} (hprod : t₁ * t₂ < 0)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hne : ∀ x ∈ Set.Icc a b, dph107 t₁ t₂ x ≠ 0)
    (hsm : ∀ j : ℕ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iterAmp107 A t₁ t₂ j) (Set.Ioo (0 : ℝ) 1))
    (hout : ∀ j : ℕ, ∀ σ, σ ∉ Set.Icc (1/5 : ℝ) (4 / 5) → iterAmp107 A t₁ t₂ j σ = 0)
    (hlt : a < 1 / 5) (hgt : 4 / 5 < b) :
    ∀ k : ℕ, (∫ x in a..b, iterAmp107 A t₁ t₂ 0 x * vexp107 t₁ t₂ x) =
      Complex.I ^ k * ∫ x in a..b, iterAmp107 A t₁ t₂ k x * vexp107 t₁ t₂ x := by
  have hsubbig : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) 1 := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hzan0 : iterAmp107 A t₁ t₂ k a * ((phaserec107 t₁ t₂ a : ℝ) : ℂ) = 0 := by
      have h := hout k a (fun hmem => absurd hmem.1 (not_le.mpr hlt))
      rw [h, zero_mul]
    have hzan1 : iterAmp107 A t₁ t₂ k b * ((phaserec107 t₁ t₂ b : ℝ) : ℂ) = 0 := by
      have h := hout k b (fun hmem => absurd hmem.2 (not_le.mpr hgt))
      rw [h, zero_mul]
    have hpc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun σ => iterAmp107 A t₁ t₂ k σ * ((phaserec107 t₁ t₂ σ : ℝ) : ℂ))
        (Set.Ioo (0 : ℝ) 1) :=
      (hsm k).mul (contDiffOn_phaserec107 hprod (⊤ : ℕ∞))
    have hu_cont : ContinuousOn (fun σ => iterAmp107 A t₁ t₂ k σ * ((phaserec107 t₁ t₂ σ : ℝ) : ℂ))
        (Set.uIcc a b) := by
      simpa [Set.uIcc_of_le hab] using hpc.continuousOn.mono hsubbig
    have huu' : ∀ x ∈ Set.Ioo a b,
        HasDerivAt (fun σ => iterAmp107 A t₁ t₂ k σ * ((phaserec107 t₁ t₂ σ : ℝ) : ℂ))
          (deriv (fun σ => iterAmp107 A t₁ t₂ k σ * ((phaserec107 t₁ t₂ σ : ℝ) : ℂ)) x) x := by
      intro x hx
      have hxbig : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun σ => iterAmp107 A t₁ t₂ k σ * ((phaserec107 t₁ t₂ σ : ℝ) : ℂ)) x :=
        hpc.contDiffAt (IsOpen.mem_nhds isOpen_Ioo hxbig)
      exact (hat.differentiableAt (by simp)).hasDerivAt
    have hui : IntervalIntegrable
        (deriv (fun σ => iterAmp107 A t₁ t₂ k σ * ((phaserec107 t₁ t₂ σ : ℝ) : ℂ))) volume a b := by
      have hd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (deriv (fun σ => iterAmp107 A t₁ t₂ k σ * ((phaserec107 t₁ t₂ σ : ℝ) : ℂ)))
          (Set.Ioo (0 : ℝ) 1) :=
        hpc.deriv_of_isOpen isOpen_Ioo (by simp)
      have hcont : ContinuousOn
          (deriv (fun σ => iterAmp107 A t₁ t₂ k σ * ((phaserec107 t₁ t₂ σ : ℝ) : ℂ)))
          (Set.Icc a b) := hd.continuousOn.mono hsubbig
      have hcont' : ContinuousOn
          (deriv (fun σ => iterAmp107 A t₁ t₂ k σ * ((phaserec107 t₁ t₂ σ : ℝ) : ℂ)))
          (Set.uIcc a b) := by
        simpa [Set.uIcc_of_le hab] using hcont
      exact hcont'.intervalIntegrable
    have hstep := IBP_step107 (A := iterAmp107 A t₁ t₂ k) (t₁ := t₁) (t₂ := t₂)
      (a := a) (b := b) ha hab hb hzan0 hzan1 hu_cont
      (vexp_continuousOn107 t₁ t₂ ha hab hb) huu'
      (fun x hx => vexp_hasDerivAt107 t₁ t₂ x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      hui (vderiv_intervalIntegrable107 t₁ t₂ ha hab hb) hne
    rw [ih, hstep, pow_succ]
    simp only [iterAmp107]
    ring

/-- `Jphi` as an interval integral over any `[a,b] ⊃ [1/5,4/5]` inside `(0,1)`. -/
private theorem Jphi_eq_interval107 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {N v : ℝ} (hN : 0 < N) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hlt : a < 1 / 5) (hgt : 4 / 5 < b)
    (ρ₁ ρ₂ : ℂ) :
    Jphi ϕ N v ρ₁ ρ₂ =
      ∫ x in a..b, ((amp107 ϕ N v ρ₁ ρ₂ x : ℝ) : ℂ) * vexp107 ρ₁.im ρ₂.im x := by
  have hzero : ∀ x, x ∉ Set.Ioo a b →
      ((amp107 ϕ N v ρ₁ ρ₂ x : ℝ) : ℂ) * vexp107 ρ₁.im ρ₂.im x = 0 := by
    intro x hx
    have hxout : x ≤ a ∨ b ≤ x := by
      by_contra hcon
      push_neg at hcon
      exact hx ⟨by linarith [hcon.1], by linarith [hcon.2]⟩
    have hψ : ϕ (v * x / N) * ϕ (v * (1 - x) / N) = 0 := by
      by_contra hne
      have hsupp := phi_pair_sigma_support84 hϕ hN hne
      rcases hxout with h1 | h1
      · linarith [hsupp.1, h1]
      · linarith [hsupp.2, h1]
    have hamp : amp107 ϕ N v ρ₁ ρ₂ x = 0 := by
      unfold amp107
      rw [hψ, mul_zero]
    rw [hamp]
    simp
  have hF0 : ∀ x, x ∉ Set.Ioo (0 : ℝ) 1 →
      ((amp107 ϕ N v ρ₁ ρ₂ x : ℝ) : ℂ) * vexp107 ρ₁.im ρ₂.im x = 0 := by
    intro x hx
    exact hzero x (fun hmem => hx ⟨by linarith [hmem.1], by linarith [hmem.2]⟩)
  have h1 : (∫ x in Set.Ioo (0 : ℝ) 1,
      ((amp107 ϕ N v ρ₁ ρ₂ x : ℝ) : ℂ) * vexp107 ρ₁.im ρ₂.im x) = ∫ x : ℝ,
      ((amp107 ϕ N v ρ₁ ρ₂ x : ℝ) : ℂ) * vexp107 ρ₁.im ρ₂.im x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hF0
  have h2 : (∫ x in Set.Ioo a b,
      ((amp107 ϕ N v ρ₁ ρ₂ x : ℝ) : ℂ) * vexp107 ρ₁.im ρ₂.im x) = ∫ x : ℝ,
      ((amp107 ϕ N v ρ₁ ρ₂ x : ℝ) : ℂ) * vexp107 ρ₁.im ρ₂.im x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  have hexp : ∀ x : ℝ, Complex.exp (Complex.I * ((phase107 ρ₁ ρ₂ x : ℝ) : ℂ)) =
      vexp107 ρ₁.im ρ₂.im x := fun x => rfl
  rw [Jphi_phase107]
  simp only [hexp]
  rw [h1, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  exact h2.symm

/-- The phase factor has modulus one. -/
private theorem norm_vexp107 {t₁ t₂ x : ℝ} (hx : 0 < x) (hx1 : x < 1) : ‖vexp107 t₁ t₂ x‖ = 1 := by
  unfold vexp107
  rw [show Complex.I * ((t₁ * Real.log x + t₂ * Real.log (1 - x) : ℝ) : ℂ) =
      ((t₁ * Real.log x + t₂ * Real.log (1 - x) : ℝ) : ℂ) * Complex.I by ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `‖Jphi‖` is bounded by the sup norm of the last iterate, times the length of the interval. -/
private theorem Jphi_norm_le107 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {N v : ℝ} (hN : 0 < N) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hlt : a < 1 / 5) (hgt : 4 / 5 < b)
    {ρ₁ ρ₂ : ℂ} (hprod : ρ₁.im * ρ₂.im < 0)
    (hne : ∀ x ∈ Set.Icc a b, dph107 ρ₁.im ρ₂.im x ≠ 0)
    (hsm : ∀ j : ℕ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (iterAmp107 (fun σ => ((amp107 ϕ N v ρ₁ ρ₂ σ : ℝ) : ℂ)) ρ₁.im ρ₂.im j) (Set.Ioo (0 : ℝ) 1))
    (hout : ∀ j : ℕ, ∀ σ, σ ∉ Set.Icc (1/5 : ℝ) (4 / 5) →
      iterAmp107 (fun σ => ((amp107 ϕ N v ρ₁ ρ₂ σ : ℝ) : ℂ)) ρ₁.im ρ₂.im j σ = 0)
    {k : ℕ} {C : ℝ}
    (hC : ∀ σ ∈ Set.Ioo (1/5 : ℝ) (4 / 5),
      ‖iterAmp107 (fun σ => ((amp107 ϕ N v ρ₁ ρ₂ σ : ℝ) : ℂ)) ρ₁.im ρ₂.im k σ‖ ≤ C) :
    ‖Jphi ϕ N v ρ₁ ρ₂‖ ≤ (b - a) * C := by
  rw [Jphi_eq_interval107 hϕ hN ha hab hb hlt hgt ρ₁ ρ₂]
  have hiter := IBP_iter107 (A := fun σ => ((amp107 ϕ N v ρ₁ ρ₂ σ : ℝ) : ℂ))
    (t₁ := ρ₁.im) (t₂ := ρ₂.im) (a := a) (b := b) hprod ha hab hb hne hsm hout hlt hgt k
  have h0 : (fun x => ((amp107 ϕ N v ρ₁ ρ₂ x : ℝ) : ℂ) * vexp107 ρ₁.im ρ₂.im x) =
      (fun x => iterAmp107 (fun σ => ((amp107 ϕ N v ρ₁ ρ₂ σ : ℝ) : ℂ)) ρ₁.im ρ₂.im 0 x *
        vexp107 ρ₁.im ρ₂.im x) := rfl
  rw [h0, hiter]
  have hI : ‖Complex.I ^ k‖ = 1 := by
    rw [norm_pow, Complex.norm_I, one_pow]
  rw [norm_mul, hI, one_mul]
  have hC0 : 0 ≤ C := by
    have h := hC (1 / 2) ⟨by norm_num, by norm_num⟩
    have h2 : (0 : ℝ) ≤ ‖iterAmp107 (fun σ => ((amp107 ϕ N v ρ₁ ρ₂ σ : ℝ) : ℂ))
        ρ₁.im ρ₂.im k (1 / 2)‖ := norm_nonneg _
    linarith
  refine (intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := a) (b := b) (C := C) ?_).trans_eq ?_
  · have hne1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (1/5 : ℝ) := by
      rw [Filter.Eventually, MeasureTheory.mem_ae_iff]
      simp
    have hne2 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (4/5 : ℝ) := by
      rw [Filter.Eventually, MeasureTheory.mem_ae_iff]
      simp
    filter_upwards [hne1, hne2] with x hxne1 hxne2 hxI
    have hxmem : x ∈ Set.Ioc a b := by rwa [Set.uIoc_of_le hab] at hxI
    have hx0 : 0 < x := by linarith [hxmem.1]
    have hx1 : x < 1 := by linarith [hxmem.2]
    rw [norm_mul, norm_vexp107 hx0 hx1, mul_one]
    by_cases hxin : x ∈ Set.Ioo (1/5 : ℝ) (4 / 5)
    · exact hC x hxin
    · have hxout : x ∉ Set.Icc (1/5 : ℝ) (4 / 5) := by
        rintro ⟨h1, h2⟩
        rcases lt_or_eq_of_le h1 with h | h
        · rcases lt_or_eq_of_le h2 with h2' | h2'
          · exact hxin ⟨h, h2'⟩
          · exact hxne2 h2'
        · exact hxne1 h.symm
      rw [hout k x hxout]
      simp [hC0]
  · rw [abs_of_nonneg (by linarith)]
    ring
/-- The explicit constant sequence of the iteration (depends only on the base bound and the
reciprocal-phase bound). -/
private noncomputable def iterC107 (ĉ : ℕ → ℝ) : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, c₀ => c₀
  | (j + 1), c₀ => fun m =>
      ∑ i ∈ Finset.range (m + 2), ((m + 1).choose i : ℝ) * iterC107 ĉ j c₀ i * ĉ (m + 1 - i)

/-- The iteration bound with an explicit constant sequence. -/
private theorem iterAmp_bound_iterC107 {A : ℝ → ℂ} {t₁ t₂ : ℝ} (hprod : t₁ * t₂ < 0) {u : ℝ}
    (hu0 : 0 < u) {ĉ : ℕ → ℝ}
    (hrc : ∀ (p : ℕ) {σ : ℝ}, σ ∈ Set.Ioo (1/5 : ℝ) (4 / 5) →
      ‖iteratedDerivWithin p (fun τ => ((phaserec107 t₁ t₂ τ : ℝ) : ℂ))
        (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖ ≤ ĉ p / u)
    (hAsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A (Set.Ioo (0 : ℝ) 1))
    {c₀ : ℕ → ℝ}
    (h₀ : ∀ (m : ℕ) {σ : ℝ}, σ ∈ Set.Ioo (1/5 : ℝ) (4 / 5) →
      ‖iteratedDerivWithin m A (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖ ≤ c₀ m) :
    ∀ (j : ℕ) (m : ℕ) {σ : ℝ}, σ ∈ Set.Ioo (1/5 : ℝ) (4 / 5) →
      ‖iteratedDerivWithin m (iterAmp107 A t₁ t₂ j) (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖ ≤
        iterC107 ĉ j c₀ m / u ^ j := by
  have hsub : Set.Ioo (1/5 : ℝ) (4 / 5) ⊆ Set.Ioo (0 : ℝ) 1 :=
    Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
  have hrsm : ∀ n : ℕ∞,
      ContDiffOn ℝ n (fun τ => ((phaserec107 t₁ t₂ τ : ℝ) : ℂ)) (Set.Ioo (1/5 : ℝ) (4 / 5)) :=
    fun n => (contDiffOn_phaserec107 hprod n).mono hsub
  intro j
  induction j with
  | zero =>
    intro m σ hσ
    simpa [iterAmp107, iterC107] using h₀ m hσ
  | succ j ih =>
    intro m σ hσ
    -- the `m`-th derivative of `A_{j+1}` is the `(m+1)`-st of `A_j * (1/Φ')`
    have hd : iteratedDerivWithin m (iterAmp107 A t₁ t₂ (j + 1)) (Set.Ioo (1/5 : ℝ) (4 / 5)) σ =
        iteratedDerivWithin (m + 1)
          (fun τ => iterAmp107 A t₁ t₂ j τ * ((phaserec107 t₁ t₂ τ : ℝ) : ℂ))
          (Set.Ioo (1/5 : ℝ) (4 / 5)) σ := by
      simp only [iterAmp107]
      rw [iteratedDerivWithin_deriv107 isOpen_Ioo m hσ]
    rw [hd]
    -- Leibniz
    have hAon : ContDiffOn ℝ (((m + 1 : ℕ) : ℕ∞))
        (iterAmp107 A t₁ t₂ j) (Set.Ioo (1/5 : ℝ) (4 / 5)) :=
      ((contDiffOn_iterAmp107 hprod hAsm) j).mono hsub |>.of_le (by simp)
    have hron : ContDiffOn ℝ (((m + 1 : ℕ) : ℕ∞))
        (fun τ => ((phaserec107 t₁ t₂ τ : ℝ) : ℂ)) (Set.Ioo (1/5 : ℝ) (4 / 5)) :=
      hrsm _
    refine (norm_iteratedDerivWithin_mul_le107 hAon hron (uniqueDiffOn_Ioo _ _) hσ (n := m + 1)).trans ?_
    -- bound each term and sum
    have hterm : ∀ i ∈ Finset.range (m + 2),
        ((m + 1).choose i : ℝ) *
          ‖iteratedDerivWithin i (iterAmp107 A t₁ t₂ j) (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖ *
          ‖iteratedDerivWithin (m + 1 - i) (fun τ => ((phaserec107 t₁ t₂ τ : ℝ) : ℂ))
            (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖ ≤
        ((m + 1).choose i : ℝ) * iterC107 ĉ j c₀ i * ĉ (m + 1 - i) / u ^ (j + 1) := by
      intro i hi
      have hi_le : i ≤ m + 1 := by
        have := Finset.mem_range.mp hi
        omega
      have h1 : ‖iteratedDerivWithin i (iterAmp107 A t₁ t₂ j) (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖ ≤
          iterC107 ĉ j c₀ i / u ^ j := ih i hσ
      have h2 : ‖iteratedDerivWithin (m + 1 - i) (fun τ => ((phaserec107 t₁ t₂ τ : ℝ) : ℂ))
          (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖ ≤ ĉ (m + 1 - i) / u := hrc (m + 1 - i) hσ
      have huj' : (0 : ℝ) < u ^ j := pow_pos hu0 j
      have hc0 : 0 ≤ iterC107 ĉ j c₀ i := by
        have h : 0 ≤ iterC107 ĉ j c₀ i / u ^ j := le_trans (norm_nonneg _) h1
        have h2' := mul_nonneg h huj'.le
        rwa [div_mul_cancel₀ _ huj'.ne'] at h2'
      have hĉ0 : 0 ≤ ĉ (m + 1 - i) := by
        have h : 0 ≤ ĉ (m + 1 - i) / u := le_trans (norm_nonneg _) h2
        have h2' := mul_nonneg h hu0.le
        rwa [div_mul_cancel₀ _ hu0.ne'] at h2'
      have hu0' : (0 : ℝ) < u ^ (j + 1) := pow_pos hu0 _
      have huj : (0 : ℝ) < u ^ j := pow_pos hu0 _
      have hsplit : ((m + 1).choose i : ℝ) * (iterC107 ĉ j c₀ i / u ^ j) * (ĉ (m + 1 - i) / u) =
          ((m + 1).choose i : ℝ) * iterC107 ĉ j c₀ i * ĉ (m + 1 - i) / u ^ (j + 1) := by
        field_simp
        ring
      calc ((m + 1).choose i : ℝ) *
            ‖iteratedDerivWithin i (iterAmp107 A t₁ t₂ j) (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖ *
            ‖iteratedDerivWithin (m + 1 - i) (fun τ => ((phaserec107 t₁ t₂ τ : ℝ) : ℂ))
              (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖
          ≤ ((m + 1).choose i : ℝ) * (iterC107 ĉ j c₀ i / u ^ j) * (ĉ (m + 1 - i) / u) := by
            refine mul_le_mul (mul_le_mul le_rfl h1 (norm_nonneg _) (by positivity)) h2
              (norm_nonneg _) (by positivity)
        _ = ((m + 1).choose i : ℝ) * iterC107 ĉ j c₀ i * ĉ (m + 1 - i) / u ^ (j + 1) := hsplit
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    simp only [iterC107]
    rw [Finset.sum_div]

/-- In the regime `u ≥ 1`, the `k`-fold gain `u^{-k}` dominates `2^A (1+u)^{-A}` when `k ≥ A`. -/
private theorem decay_ge_one107 {c0 : ℝ} (hc0 : 0 ≤ c0) {u : ℝ} (hu : 1 ≤ u) {A : ℝ} (hA : 0 < A)
    {k : ℕ} (hk : A ≤ (k : ℝ)) :
    c0 / u ^ k ≤ 2 ^ A * c0 * (1 + u) ^ (-A) := by
  have hu0 : 0 < u := by linarith
  have h1u : (0 : ℝ) < 1 + u := by linarith
  have h2A : (0 : ℝ) < 2 ^ A := Real.rpow_pos_of_pos (by norm_num) A
  have huk : (0 : ℝ) < u ^ k := pow_pos hu0 k
  have h1uA : (0 : ℝ) < (1 + u) ^ A := Real.rpow_pos_of_pos h1u A
  have hpow : (1 + u) ^ A ≤ 2 ^ A * u ^ k := by
    have h2 : (1 + u : ℝ) ^ A ≤ (2 * u) ^ A :=
      Real.rpow_le_rpow (by linarith) (by linarith) hA.le
    have h3 : (2 * u : ℝ) ^ A = 2 ^ A * u ^ A := Real.mul_rpow (by norm_num) (by linarith)
    have h4 : u ^ A ≤ u ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le hu hk
    have h5 : u ^ (k : ℝ) = u ^ k := Real.rpow_natCast u k
    rw [h3] at h2
    rw [h5] at h4
    calc (1 + u) ^ A ≤ 2 ^ A * u ^ A := h2
      _ ≤ 2 ^ A * u ^ k := by
          refine mul_le_mul_of_nonneg_left h4 (le_of_lt h2A)
  have key : (1 + u) ^ A * (u ^ k)⁻¹ ≤ 2 ^ A := by
    have h := mul_le_mul_of_nonneg_right hpow (le_of_lt (inv_pos.mpr huk))
    rwa [mul_assoc, mul_inv_cancel₀ huk.ne', mul_one] at h
  have key2 : (u ^ k)⁻¹ ≤ 2 ^ A * ((1 + u) ^ A)⁻¹ := by
    have h := mul_le_mul_of_nonneg_right key (le_of_lt (inv_pos.mpr h1uA))
    have heq : (1 + u) ^ A * (u ^ k)⁻¹ * ((1 + u) ^ A)⁻¹ = (u ^ k)⁻¹ := by
      field_simp
    rw [heq] at h
    exact h
  calc c0 / u ^ k = c0 * (u ^ k)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ c0 * (2 ^ A * ((1 + u) ^ A)⁻¹) := mul_le_mul_of_nonneg_left key2 hc0
    _ = 2 ^ A * c0 * (1 + u) ^ (-A) := by
        rw [Real.rpow_neg (le_of_lt h1u)]
        ring

/-- In the regime `u < 1` the constant factor `2^A` alone dominates. -/
private theorem decay_lt_one107 {c0 : ℝ} (hc0 : 0 ≤ c0) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    {A : ℝ} (hA : 0 < A) :
    c0 ≤ 2 ^ A * c0 * (1 + u) ^ (-A) := by
  have h1u : (0 : ℝ) < 1 + u := by linarith
  have h2A : (0 : ℝ) < 2 ^ A := Real.rpow_pos_of_pos (by norm_num) A
  have h2 : (2 : ℝ) ^ (-A) ≤ (1 + u) ^ (-A) :=
    Real.rpow_le_rpow_of_nonpos h1u (by linarith) (by linarith)
  have h22 : (2 : ℝ) ^ A * 2 ^ (-A) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hprod : 1 ≤ 2 ^ A * (1 + u) ^ (-A) := by
    calc (1 : ℝ) = 2 ^ A * 2 ^ (-A) := h22.symm
      _ ≤ 2 ^ A * (1 + u) ^ (-A) := mul_le_mul_of_nonneg_left h2 (le_of_lt h2A)
  calc c0 = c0 * 1 := by ring
    _ ≤ c0 * (2 ^ A * (1 + u) ^ (-A)) := mul_le_mul_of_nonneg_left hprod hc0
    _ = 2 ^ A * c0 * (1 + u) ^ (-A) := by ring

/-- The explicit uniform constant for the reciprocal phase derivative. -/
private noncomputable def pC107 : ℕ → ℝ := fun p =>
  2 * (∑ i ∈ Finset.range (p + 1), (p.choose i : ℝ) * (((p - i).factorial : ℕ) : ℝ) *
    25 ^ (p - i + 1))

/-- `Jphi` is bounded by the sup norm of the `k`-th iterate, divided by `u^k`. -/
private theorem Jphi_norm_le_uniform107 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (D : ℕ → ℝ)
    (hD : ∀ (N v : ℝ), 0 < N → (2 / 5 : ℝ) ≤ v / N → v / N ≤ 8 / 5 →
      ∀ (s₁ s₂ : ℝ), 0 < s₁ → s₁ ≤ 1 → 0 < s₂ → s₂ ≤ 1 →
      ∀ (m : ℕ) {σ : ℝ}, σ ∈ Set.Icc (1 / 5 : ℝ) (4 / 5) →
        ‖iteratedDeriv m (fun τ => τ ^ (s₁ - 1) * (1 - τ) ^ (s₂ - 1) *
          (ϕ (v * τ / N) * ϕ (v * (1 - τ) / N))) σ‖ ≤ D m)
    (k : ℕ) :
    ∀ (N v : ℝ), 0 < N → (2 / 5 : ℝ) ≤ v / N → v / N ≤ 8 / 5 → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 → ρ₁.im * ρ₂.im < 0 →
      ‖Jphi ϕ N v ρ₁ ρ₂‖ ≤ (17 / 20 - 3 / 16) *
        (iterC107 pC107 k D 0 / (|ρ₁.im| + |ρ₂.im|) ^ k) := by
  intro N v hN hv0 hv1 ρ₁ ρ₂ h₁ h₁' h₂ h₂' hprod
  set u : ℝ := |ρ₁.im| + |ρ₂.im| with hu
  set A0 : ℝ → ℂ := fun σ => ((amp107 ϕ N v ρ₁ ρ₂ σ : ℝ) : ℂ) with hA0
  have hu0 : 0 < u := by
    have h1 : ρ₁.im ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hprod
      linarith [hprod]
    have h2 : ρ₂.im ≠ 0 := by
      rintro h
      rw [h, mul_zero] at hprod
      linarith [hprod]
    have h3 : 0 < |ρ₁.im| := abs_pos.mpr h1
    have h4 : 0 < |ρ₂.im| := abs_pos.mpr h2
    rw [hu]
    linarith
  have hA0out : ∀ σ, σ ∉ Set.Icc (1/5 : ℝ) (4 / 5) → A0 σ = 0 := by
    intro σ hσ
    have hψ : ϕ (v * σ / N) * ϕ (v * (1 - σ) / N) = 0 := by
      by_contra hne
      obtain ⟨h1, h2⟩ := phi_pair_sigma_support84 hϕ hN hne
      exact hσ ⟨h1.le, h2.le⟩
    simp only [hA0, amp107, hψ, mul_zero, Complex.ofReal_zero]
  have hpsi_cd : ∀ n : ℕ∞, ContDiff ℝ n (fun τ : ℝ => ϕ (v * τ / N) * ϕ (v * (1 - τ) / N)) := by
    intro n
    have h1 : ContDiff ℝ ((⊤ : ℕ∞)) (fun τ : ℝ => ϕ (v * τ / N)) := hϕ.smooth.comp (by fun_prop)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞)) (fun τ : ℝ => ϕ (v * (1 - τ) / N)) :=
      hϕ.smooth.comp (by fun_prop)
    exact (h1.mul h2).of_le (by simp)
  have hA0sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A0 (Set.Ioo (0 : ℝ) 1) := by
    have hq1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun τ : ℝ => τ ^ (ρ₁.re - 1))
        (Set.Ioo (0 : ℝ) 1) :=
      contDiffOn_id.rpow_const_of_ne (fun x hx => ne_of_gt hx.1)
    have hq2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun τ : ℝ => (1 - τ) ^ (ρ₂.re - 1))
        (Set.Ioo (0 : ℝ) 1) :=
      (contDiffOn_const.sub contDiffOn_id).rpow_const_of_ne
        (fun x hx => ne_of_gt (by linarith [hx.2] : (0 : ℝ) < 1 - x))
    have hreal : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun τ : ℝ => τ ^ (ρ₁.re - 1) * (1 - τ) ^ (ρ₂.re - 1) *
          (ϕ (v * τ / N) * ϕ (v * (1 - τ) / N))) (Set.Ioo (0 : ℝ) 1) :=
      (hq1.mul hq2).mul (hpsi_cd ⊤).contDiffOn
    have hcast := (Complex.ofRealCLM.contDiff).comp_contDiffOn hreal
    convert hcast using 1
    funext τ
    simp only [A0, amp107, Function.comp_apply, Complex.ofRealCLM_apply]
  have hsm : ∀ j : ℕ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iterAmp107 A0 ρ₁.im ρ₂.im j)
      (Set.Ioo (0 : ℝ) 1) := contDiffOn_iterAmp107 hprod hA0sm
  have hout : ∀ j : ℕ, ∀ σ, σ ∉ Set.Icc (1/5 : ℝ) (4 / 5) →
      iterAmp107 A0 ρ₁.im ρ₂.im j σ = 0 := iterAmp_out107 ρ₁.im ρ₂.im hA0out
  have hne : ∀ x ∈ Set.Icc (3/16 : ℝ) (17/20), dph107 ρ₁.im ρ₂.im x ≠ 0 := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hx1 : x < 1 := by linarith [hx.2]
    have hlow := sigma_phase_lower84 hprod hx0 hx1
    have hPhi : ρ₁.im / x - ρ₂.im / (1 - x) ≠ 0 := by
      intro h
      rw [h, abs_zero] at hlow
      rw [← hu] at hlow
      linarith [hu0]
    rw [dph_eq_mul107 hx0 hx1]
    exact mul_ne_zero (mul_ne_zero hx0.ne' (by linarith : (1 : ℝ) - x ≠ 0)) hPhi
  have hbase : ∀ (m : ℕ) {σ : ℝ}, σ ∈ Set.Ioo (1/5 : ℝ) (4 / 5) →
      ‖iteratedDerivWithin m A0 (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖ ≤ D m := by
    intro m σ hσ
    have hσbig : σ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hat : ContDiffAt ℝ (m : ℕ∞) A0 σ :=
      (hA0sm.contDiffAt (IsOpen.mem_nhds isOpen_Ioo hσbig)).of_le (by simp)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo _ _) hat hσ]
    have hA0fun : A0 = fun τ : ℝ => (((τ ^ (ρ₁.re - 1) * (1 - τ) ^ (ρ₂.re - 1) *
        (ϕ (v * τ / N) * ϕ (v * (1 - τ) / N))) : ℝ) : ℂ) := rfl
    rw [hA0fun]
    have hfat : ContDiffAt ℝ (m : ℕ∞)
        (fun τ : ℝ => τ ^ (ρ₁.re - 1) * (1 - τ) ^ (ρ₂.re - 1) *
          (ϕ (v * τ / N) * ϕ (v * (1 - τ) / N))) σ := by
      have hp1 : ContDiffAt ℝ (m : ℕ∞) (fun τ : ℝ => τ ^ (ρ₁.re - 1)) σ :=
        contDiffAt_id.rpow_const_of_ne (by linarith [hσ.1] : σ ≠ 0)
      have hp2 : ContDiffAt ℝ (m : ℕ∞) (fun τ : ℝ => (1 - τ) ^ (ρ₂.re - 1)) σ :=
        (contDiffAt_const.sub contDiffAt_id).rpow_const_of_ne
          (by linarith [hσ.2] : (1 : ℝ) - σ ≠ 0)
      exact (hp1.mul hp2).mul (hpsi_cd (m : ℕ∞)).contDiffAt
    exact (norm_iteratedDeriv_ofReal_le107 hfat).trans
      (hD N v hN hv0 hv1 ρ₁.re ρ₂.re h₁ h₁' h₂ h₂' m ⟨hσ.1.le, hσ.2.le⟩)
  have hrc : ∀ (p : ℕ) {σ : ℝ}, σ ∈ Set.Ioo (1/5 : ℝ) (4 / 5) →
      ‖iteratedDerivWithin p (fun τ => ((phaserec107 ρ₁.im ρ₂.im τ : ℝ) : ℂ))
        (Set.Ioo (1/5 : ℝ) (4 / 5)) σ‖ ≤ pC107 p / u := by
    intro p σ hσ
    have hsub : Set.Ioo (1/5 : ℝ) (4 / 5) ⊆ Set.Ioo (0 : ℝ) 1 :=
      Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
    have hon : ContDiffOn ℝ (p : ℕ∞) (fun τ => ((phaserec107 ρ₁.im ρ₂.im τ : ℝ) : ℂ))
        (Set.Ioo (1/5 : ℝ) (4 / 5)) := (contDiffOn_phaserec107 hprod (p : ℕ∞)).mono hsub
    have hat : ContDiffAt ℝ (p : ℕ∞) (fun τ => ((phaserec107 ρ₁.im ρ₂.im τ : ℝ) : ℂ)) σ :=
      hon.contDiffAt (IsOpen.mem_nhds isOpen_Ioo hσ)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo _ _) hat hσ]
    have hbig := norm_iteratedDeriv_phaserec_bound107 hprod hu hu0 p
      (⟨by linarith [hσ.1], by linarith [hσ.2]⟩ : σ ∈ Set.Icc (1/5 : ℝ) (4/5))
    simpa only [pC107] using hbig
  have hbound := Jphi_norm_le107 hϕ hN (by norm_num : (0:ℝ) < 3/16)
    (by norm_num : (3/16 : ℝ) ≤ 17/20) (by norm_num : (17/20 : ℝ) < 1)
    (by norm_num : (3/16 : ℝ) < 1/5) (by norm_num : (4/5 : ℝ) < 17/20)
    hprod hne hsm hout (k := k) (C := iterC107 pC107 k D 0 / u ^ k)
    (fun σ hσ => iterAmp_bound_iterC107 hprod hu0 hrc hA0sm hbase k 0 hσ)
  simpa [hu] using hbound

/-- `pC107` is nonnegative. -/
private theorem pC107_nonneg (p : ℕ) : 0 ≤ pC107 p := by
  simp only [pC107]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg ?_)
  intro i hi
  positivity

/-- `iterC107` is nonnegative for nonnegative inputs. -/
private theorem iterC107_nonneg {ĉ : ℕ → ℝ} (hĉ : ∀ p, 0 ≤ ĉ p) {c₀ : ℕ → ℝ} (h₀ : ∀ m, 0 ≤ c₀ m)
    (j m : ℕ) : 0 ≤ iterC107 ĉ j c₀ m := by
  induction j generalizing m with
  | zero => simpa only [iterC107] using h₀ m
  | succ j ih =>
    have h := Finset.sum_nonneg (s := Finset.range (m + 2))
      (f := fun i => ((m + 1).choose i : ℝ) * iterC107 ĉ j c₀ i * ĉ (m + 1 - i))
      (fun i hi => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ih i)) (hĉ _))
    simpa only [iterC107] using h

/-- The pointwise decay of the inner beta integral, opposite signs, unconditionally. -/
private theorem JphiDecay107_proof {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {A : ℝ} (hA : 0 < A) :
    ∃ Cj : ℝ, ∀ (N v : ℝ), 0 < N → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 → ρ₁.im * ρ₂.im < 0 →
      ‖Jphi ϕ N v ρ₁ ρ₂‖ ≤ Cj * (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) := by
  obtain ⟨D, hD⟩ := exists_norm_iteratedDeriv_amp_bound107 hϕ
  obtain ⟨k, hk⟩ : ∃ k : ℕ, A ≤ (k : ℝ) := ⟨Nat.ceil A, by exact_mod_cast Nat.le_ceil A⟩
  set c₀ : ℕ → ℝ := fun m => max (D m) 0 with hc₀def
  have hc₀ : ∀ m, 0 ≤ c₀ m := fun m => le_max_right _ _
  have hDb : ∀ (N v : ℝ), 0 < N → (2 / 5 : ℝ) ≤ v / N → v / N ≤ 8 / 5 →
      ∀ (s₁ s₂ : ℝ), 0 < s₁ → s₁ ≤ 1 → 0 < s₂ → s₂ ≤ 1 →
      ∀ (m : ℕ) {σ : ℝ}, σ ∈ Set.Icc (1 / 5 : ℝ) (4 / 5) →
        ‖iteratedDeriv m (fun τ => τ ^ (s₁ - 1) * (1 - τ) ^ (s₂ - 1) *
          (ϕ (v * τ / N) * ϕ (v * (1 - τ) / N))) σ‖ ≤ c₀ m := by
    intro N v hN hv0 hv1 s₁ s₂ h₁ h₁' h₂ h₂' m σ hσ
    exact (hD N v hN hv0 hv1 s₁ s₂ h₁ h₁' h₂ h₂' m hσ).trans (le_max_left _ _)
  have hĉ : ∀ p, 0 ≤ pC107 p := pC107_nonneg
  have hiter : (0 : ℝ) ≤ iterC107 pC107 k c₀ 0 := iterC107_nonneg hĉ hc₀ k 0
  have hCj0 : (0 : ℝ) ≤ (53 / 80) * 2 ^ A * (iterC107 pC107 k c₀ 0 + c₀ 0 + 1) := by
    have h2A : (0 : ℝ) < 2 ^ A := Real.rpow_pos_of_pos (by norm_num) A
    have hsum : (0 : ℝ) ≤ iterC107 pC107 k c₀ 0 + c₀ 0 + 1 := by
      have := hc₀ 0; linarith
    exact mul_nonneg (mul_nonneg (by norm_num) h2A.le) hsum
  refine ⟨(53 / 80) * 2 ^ A * (iterC107 pC107 k c₀ 0 + c₀ 0 + 1), ?_⟩
  intro N v hN ρ₁ ρ₂ h₁ h₁' h₂ h₂' hprod
  set u : ℝ := |ρ₁.im| + |ρ₂.im| with hu
  have hu0 : 0 < u := by
    have h1 : ρ₁.im ≠ 0 := by
      rintro h; rw [h, zero_mul] at hprod; linarith
    have h2 : ρ₂.im ≠ 0 := by
      rintro h; rw [h, mul_zero] at hprod; linarith
    have h3 : 0 < |ρ₁.im| := abs_pos.mpr h1
    have h4 : 0 < |ρ₂.im| := abs_pos.mpr h2
    rw [hu]; linarith
  have h1u : (0 : ℝ) < 1 + u := by linarith
  have hP : (0 : ℝ) < (1 + u) ^ (-A) := Real.rpow_pos_of_pos h1u _
  have h2A : (0 : ℝ) < 2 ^ A := Real.rpow_pos_of_pos (by norm_num) A
  by_cases hrange : (2 / 5 : ℝ) ≤ v / N ∧ v / N ≤ 8 / 5
  · have hb := Jphi_norm_le_uniform107 hϕ c₀ hDb k N v hN hrange.1 hrange.2
      ρ₁ ρ₂ h₁ h₁' h₂ h₂' hprod
    rw [← hu] at hb
    rcases lt_or_ge u 1 with hu1 | hu1
    · -- small `u`: the zeroth iterate suffices
      have hb0 := Jphi_norm_le_uniform107 hϕ c₀ hDb 0 N v hN hrange.1 hrange.2
        ρ₁ ρ₂ h₁ h₁' h₂ h₂' hprod
      rw [← hu] at hb0
      have h0 : iterC107 pC107 0 c₀ 0 = c₀ 0 := by simp only [iterC107]
      have hstep : iterC107 pC107 0 c₀ 0 / u ^ (0 : ℕ) ≤
          2 ^ A * (iterC107 pC107 k c₀ 0 + c₀ 0 + 1) * (1 + u) ^ (-A) := by
        rw [h0, pow_zero, div_one]
        have hd := decay_lt_one107 (hc₀ 0) hu0 hu1 hA
        have hle : c₀ 0 ≤ iterC107 pC107 k c₀ 0 + c₀ 0 + 1 := by linarith [hiter]
        refine hd.trans ?_
        calc 2 ^ A * c₀ 0 * (1 + u) ^ (-A) = c₀ 0 * (2 ^ A * (1 + u) ^ (-A)) := by ring
          _ ≤ (iterC107 pC107 k c₀ 0 + c₀ 0 + 1) * (2 ^ A * (1 + u) ^ (-A)) :=
              mul_le_mul_of_nonneg_right hle (mul_nonneg h2A.le hP.le)
          _ = 2 ^ A * (iterC107 pC107 k c₀ 0 + c₀ 0 + 1) * (1 + u) ^ (-A) := by ring
      refine hb0.trans ?_
      have hconst : (17 / 20 - 3 / 16 : ℝ) = 53 / 80 := by norm_num
      rw [hconst]
      calc (53 / 80) * (iterC107 pC107 0 c₀ 0 / u ^ (0 : ℕ))
          ≤ (53 / 80) * (2 ^ A * (iterC107 pC107 k c₀ 0 + c₀ 0 + 1) * (1 + u) ^ (-A)) :=
            mul_le_mul_of_nonneg_left hstep (by norm_num)
        _ = (53 / 80) * 2 ^ A * (iterC107 pC107 k c₀ 0 + c₀ 0 + 1) * (1 + u) ^ (-A) := by ring
        _ = (53 / 80) * 2 ^ A * (iterC107 pC107 k c₀ 0 + c₀ 0 + 1) *
              (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) := by rw [← hu]
    · -- large `u`: `k` integrations by parts
      have hd := decay_ge_one107 (c0 := iterC107 pC107 k c₀ 0) hiter hu1 hA hk
      refine hb.trans ?_
      have hconst : (17 / 20 - 3 / 16 : ℝ) = 53 / 80 := by norm_num
      rw [hconst]
      have hle : iterC107 pC107 k c₀ 0 ≤ iterC107 pC107 k c₀ 0 + c₀ 0 + 1 := by
        have := hc₀ 0; linarith
      calc (53 / 80) * (iterC107 pC107 k c₀ 0 / u ^ k)
          ≤ (53 / 80) * (2 ^ A * iterC107 pC107 k c₀ 0 * (1 + u) ^ (-A)) :=
            mul_le_mul_of_nonneg_left hd (by norm_num)
        _ = (53 / 80) * 2 ^ A * iterC107 pC107 k c₀ 0 * (1 + u) ^ (-A) := by ring
        _ ≤ (53 / 80) * 2 ^ A * (iterC107 pC107 k c₀ 0 + c₀ 0 + 1) * (1 + u) ^ (-A) := by
            have hnn : (0 : ℝ) ≤ (53 / 80) * 2 ^ A * (1 + u) ^ (-A) :=
              mul_nonneg (mul_nonneg (by norm_num) h2A.le) hP.le
            calc (53 / 80) * 2 ^ A * iterC107 pC107 k c₀ 0 * (1 + u) ^ (-A)
                = iterC107 pC107 k c₀ 0 * ((53 / 80) * 2 ^ A * (1 + u) ^ (-A)) := by ring
              _ ≤ (iterC107 pC107 k c₀ 0 + c₀ 0 + 1) *
                    ((53 / 80) * 2 ^ A * (1 + u) ^ (-A)) :=
                  mul_le_mul_of_nonneg_right hle hnn
              _ = (53 / 80) * 2 ^ A * (iterC107 pC107 k c₀ 0 + c₀ 0 + 1) *
                    (1 + u) ^ (-A) := by ring
        _ = (53 / 80) * 2 ^ A * (iterC107 pC107 k c₀ 0 + c₀ 0 + 1) *
              (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) := by rw [← hu]
  · -- outside the support range `Jphi` vanishes
    have hout : v ≤ (2 / 5) * N ∨ (8 / 5) * N ≤ v := by
      rcases not_and_or.mp hrange with h | h
      · left
        have h1 : v / N < 2 / 5 := not_le.mp h
        have h2 := (div_lt_iff₀ hN).mp h1
        linarith
      · right
        have h1 : 8 / 5 < v / N := not_le.mp h
        have h2 := (lt_div_iff₀ hN).mp h1
        linarith
    rw [Jphi_eq_zero_outside84 hϕ hN hout ρ₁ ρ₂, norm_zero]
    exact mul_nonneg hCj0 hP.le

end

/-- LEAF. Page 29 proof of 7.19, opposite signs.
Repeated integration by parts in sigma, followed by the outer absolute integral. -/
theorem archimedean_opposite107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ N T : ℝ, 1 ≤ T → T ≤ N → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 → ρ₁.im * ρ₂.im < 0 →
      ‖∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (ρ₁ + ρ₂ - 1) *
          (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂‖ ≤
        C * N ^ ((ρ₁ + ρ₂).re - 1) * (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) :=
  opposite_of_Jdecay107 hϕ hG hA (JphiDecay107_proof hϕ hA)

/-- LEAF. Page 29 proof of 7.19, equal signs including zero.
Repeated integration by parts in v gives decay at scale T / N. -/
theorem archimedean_same107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ N T : ℝ, 1 ≤ T → T ≤ N → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 → 0 ≤ ρ₁.im * ρ₂.im →
      ‖∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (ρ₁ + ρ₂ - 1) *
          (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂‖ ≤
        C * N ^ ((ρ₁ + ρ₂).re - 1) *
          (1 + (|ρ₁.im| + |ρ₂.im|) * T / N) ^ (-A) := by
  sorry

/-- Page 29 proof of 7.20. The normalized dilated kernel is integrable. -/
theorem integrable_GT150 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    {T : ℝ} (hT : 0 < T) : Integrable (GT G T) :=
  (GT_contDiff hG.smooth T).continuous.integrable_of_hasCompactSupport
    (GT_hasCompactSupport hG.supp hT)

/-- Page 29 proof of 7.20. The dilated kernel has mass one. -/
theorem integral_GT150 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    {T : ℝ} (hT : 0 < T) : (∫ x : ℝ, GT G T x) = 1 := by
  simp [GT, integral_const_mul, Measure.integral_comp_div, abs_of_pos hT,
    hG.integral_one, hT.ne']

/-- Page 29 proof of 7.20. The positive dilation preserves nonnegativity. -/
theorem nonneg_GT150 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    {T : ℝ} (hT : 0 < T) (x : ℝ) : 0 ≤ GT G T x :=
  mul_nonneg (inv_nonneg.mpr hT.le) (hG.nonneg _)

/-- Page 29 proof of 7.20. Real base complex powers are measurable at fixed exponent. -/
theorem measurable_real_cpow150 (z : ℂ) : Measurable (fun x : ℝ => (x : ℂ) ^ z) := by
  apply measurable_of_continuousOn_compl_singleton (0 : ℝ)
  intro x hx
  exact (Complex.continuousAt_ofReal_cpow_const x z
    (Or.inr (by simpa using hx))).continuousWithinAt

/-- Page 29 display 7.21. The inner integral is measurable in its outer variable. -/
theorem measurable_Jphi150 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (N : ℝ) (ρ₁ ρ₂ : ℂ) : Measurable (fun v : ℝ => Jphi ϕ N v ρ₁ ρ₂) := by
  have ha : Measurable (fun p : ℝ × ℝ =>
      ((ϕ (p.1 * p.2 / N) * ϕ (p.1 * (1 - p.2) / N) : ℝ) : ℂ)) := by
    have hc := hϕ.smooth.continuous
    fun_prop
  have hb : Measurable (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (ρ₁ - 1)) :=
    (measurable_real_cpow150 _).comp measurable_snd
  have hc : Measurable (fun p : ℝ × ℝ => ((1 - p.2 : ℝ) : ℂ) ^ (ρ₂ - 1)) :=
    (measurable_real_cpow150 _).comp (measurable_const.sub measurable_snd)
  have hi := (((ha.mul hb).mul hc).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))).measurable
  simpa only [Pi.mul_apply, Jphi, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hi

/-- Page 29 proof of 7.20. Extend the normalized Taylor estimate by zero outside positive v.
The support gap controls the baseline term outside the effective v interval. -/
theorem global_beta_taylor150 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 0 < N → ∀ v : ℝ, ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 →
      ‖(if 0 < v then ((v / N : ℝ) : ℂ) ^ (ρ₁ + ρ₂ - 1) * Jphi ϕ N v ρ₁ ρ₂ else 0) -
        Bphi ϕ ρ₁ ρ₂‖ ≤ C * (1 + |(ρ₁ + ρ₂).im|) * |v / N - 1| := by
  obtain ⟨CA, hCA, hA⟩ := weighted_beta_taylor107 hϕ
  obtain ⟨CJ, hCJ, hJ⟩ := Jphi_uniform107 hϕ
  refine ⟨CA + 2 * CJ, by positivity, ?_⟩
  intro N hN v ρ₁ ρ₂ h₁ h₁' h₂ h₂'
  have hB : ‖Bphi ϕ ρ₁ ρ₂‖ ≤ CJ := by
    have h := hJ 1 (by norm_num) 1 ρ₁ ρ₂ h₁ h₂
    rwa [Jphi_at_N ϕ (by norm_num)] at h
  by_cases hv : v / N ∈ Set.Icc (2 / 5 : ℝ) (8 / 5)
  · have hv0 : 0 < v := by
      have hh := (le_div_iff₀ hN).mp hv.1
      nlinarith
    rw [if_pos hv0]
    exact (hA N hN v hv ρ₁ ρ₂ h₁ h₁' h₂ h₂').trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : CA ≤ CA + 2 * CJ) (by positivity))
        (abs_nonneg _))
  · have hout : v / N < 2 / 5 ∨ 8 / 5 < v / N := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hv
    have hd : (1 / 2 : ℝ) ≤ |v / N - 1| := by
      rcases hout with hl | hu
      · linarith [neg_le_abs (v / N - 1)]
      · linarith [le_abs_self (v / N - 1)]
    have hz : (if 0 < v then ((v / N : ℝ) : ℂ) ^ (ρ₁ + ρ₂ - 1) *
        Jphi ϕ N v ρ₁ ρ₂ else 0) = 0 := by
      split_ifs
      · rw [Jphi_eq_zero_outside84 hϕ hN (by
          rcases hout with hl | hu
          · exact Or.inl ((div_le_iff₀ hN).mp hl.le)
          · exact Or.inr ((le_div_iff₀ hN).mp hu.le))]
        simp
      · rfl
    rw [hz, zero_sub, norm_neg]
    calc
      _ ≤ CJ := hB
      _ ≤ (2 * CJ) * |v / N - 1| := by nlinarith
      _ ≤ (CA + 2 * CJ) * |v / N - 1| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ (CA + 2 * CJ) * (1 + |(ρ₁ + ρ₂).im|) * |v / N - 1| := by
        have hf : 1 ≤ 1 + |(ρ₁ + ρ₂).im| := by linarith [abs_nonneg (ρ₁ + ρ₂).im]
        have hm := mul_le_mul_of_nonneg_left hf (show 0 ≤ CA + 2 * CJ by positivity)
        exact mul_le_mul_of_nonneg_right (by simpa only [mul_one] using hm) (abs_nonneg _)

/-- LEAF. Page 29 proof of 7.20.
Normalize by N, extend the cutoff by zero, and integrate against the unit mass kernel. -/
theorem archimedean_taylor107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) :
    ∃ C : ℝ, ∀ N T : ℝ, 1 ≤ T → T ≤ N → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 → |(ρ₁ + ρ₂).im| * T ≤ N →
      ‖(∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (ρ₁ + ρ₂ - 1) *
          (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂) -
          Bphi ϕ ρ₁ ρ₂ * (N : ℂ) ^ (ρ₁ + ρ₂ - 1)‖ ≤
        C * N ^ ((ρ₁ + ρ₂).re - 1) * (1 + |(ρ₁ + ρ₂).im|) * T / N := by
  obtain ⟨C, hC, hbound⟩ := global_beta_taylor150 hϕ
  refine ⟨2 * C, ?_⟩
  intro N T hT hTN ρ₁ ρ₂ h₁ h₁' h₂ h₂' _hfreq
  have hT0 : 0 < T := by linarith
  have hN : 0 < N := by linarith
  let z : ℂ := ρ₁ + ρ₂ - 1
  let B : ℂ := Bphi ϕ ρ₁ ρ₂
  let F : ℝ → ℂ := fun v =>
    if 0 < v then ((v / N : ℝ) : ℂ) ^ z * Jphi ϕ N v ρ₁ ρ₂ else 0
  let k : ℝ → ℝ := fun v => GT G T (N - v)
  let D : ℝ := 2 * C * (1 + |(ρ₁ + ρ₂).im|) * T / N
  have hk : Integrable k := (integrable_GT150 hG hT0).comp_sub_left N
  have hkn (v : ℝ) : 0 ≤ k v := nonneg_GT150 hG hT0 _
  have hki : (∫ v : ℝ, k v) = 1 := by
    dsimp [k]
    rw [integral_sub_left_eq_self (GT G T) volume N, integral_GT150 hG hT0]
  have hFm : Measurable F := by
    dsimp [F]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      (((measurable_real_cpow150 z).comp (measurable_id.div_const N)).mul
        (measurable_Jphi150 hϕ N ρ₁ ρ₂)) measurable_const
  have hkm : Measurable k := by
    have hc := (GT_contDiff hG.smooth T).continuous
    exact (hc.comp (continuous_const.sub continuous_id)).measurable
  have hpoint (v : ℝ) : ‖(F v - B) * (k v : ℂ)‖ ≤ D * k v := by
    by_cases hz : k v = 0
    · simp [hz]
    have hdist : |N - v| ≤ 2 * T := by
      by_contra hh
      exact hz (GT_eq_zero hG.supp hT0 (lt_of_not_ge hh))
    have hdist' : |v / N - 1| ≤ 2 * T / N := by
      rw [show v / N - 1 = -(N - v) / N by field_simp [hN.ne']; ring, abs_div, abs_neg, abs_of_pos hN]
      exact div_le_div_of_nonneg_right hdist hN.le
    have he := hbound N hN v ρ₁ ρ₂ h₁ h₁' h₂ h₂'
    change ‖F v - B‖ ≤ C * (1 + |(ρ₁ + ρ₂).im|) * |v / N - 1| at he
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hkn v)]
    calc
      _ ≤ (C * (1 + |(ρ₁ + ρ₂).im|) * (2 * T / N)) * k v :=
        mul_le_mul_of_nonneg_right
          (he.trans (mul_le_mul_of_nonneg_left hdist' (by positivity))) (hkn v)
      _ = D * k v := by dsimp [D]; ring
  have herror : Integrable (fun v : ℝ => (F v - B) * (k v : ℂ)) :=
    (hk.const_mul D).mono'
      ((hFm.sub measurable_const).mul (Complex.continuous_ofReal.measurable.comp hkm)).aestronglyMeasurable
      (Filter.Eventually.of_forall hpoint)
  have hbase : Integrable (fun v : ℝ => B * (k v : ℂ)) := hk.ofReal.const_mul B
  have hF : Integrable (fun v : ℝ => F v * (k v : ℂ)) := by
    convert herror.add hbase using 1
    ext v
    simp only [Pi.add_apply]
    ring
  have hbaseint : (∫ v : ℝ, B * (k v : ℂ)) = B := by
    have hcast : (∫ v : ℝ, (k v : ℂ)) = Complex.ofReal (∫ v : ℝ, k v) := integral_ofReal
    rw [integral_const_mul, hcast, hki]
    simp
  have hdiff : (∫ v : ℝ, F v * (k v : ℂ)) - B =
      ∫ v : ℝ, (F v - B) * (k v : ℂ) := by
    calc
      _ = (∫ v : ℝ, F v * (k v : ℂ)) - (∫ v : ℝ, B * (k v : ℂ)) := by rw [hbaseint]
      _ = ∫ v : ℝ, F v * (k v : ℂ) - B * (k v : ℂ) := (integral_sub hF hbase).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with v
        ring
  have herr : ‖(∫ v : ℝ, F v * (k v : ℂ)) - B‖ ≤ D := by
    rw [hdiff]
    have hi := norm_integral_le_of_norm_le (hk.const_mul D) (Filter.Eventually.of_forall hpoint)
    simpa only [integral_const_mul, hki, mul_one] using hi
  have houter : (∫ v in Set.Ioi (0 : ℝ),
      (v : ℂ) ^ (ρ₁ + ρ₂ - 1) * (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂) =
      (N : ℂ) ^ z * ∫ v : ℝ, F v * (k v : ℂ) := by
    calc
      _ = ∫ v in Set.Ioi (0 : ℝ), (N : ℂ) ^ z * (F v * (k v : ℂ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v hv
        have hp : (v : ℂ) ^ z = (N : ℂ) ^ z * ((v / N : ℝ) : ℂ) ^ z := by
          calc
            _ = ((N * (v / N) : ℝ) : ℂ) ^ z := by rw [mul_div_cancel₀ v hN.ne']
            _ = _ := by
              simpa only [Complex.ofReal_mul] using
                Complex.mul_cpow_ofReal_nonneg hN.le (div_nonneg (show 0 ≤ v from hv.le) hN.le) z
        dsimp [F, k]
        rw [if_pos (show 0 < v from hv)]
        change (v : ℂ) ^ z * (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂ = _
        rw [hp]
        ring
      _ = ∫ v : ℝ, (N : ℂ) ^ z * (F v * (k v : ℂ)) := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro v hv
        have hv' : ¬ 0 < v := by simpa using hv
        simp [F, hv']
      _ = _ := integral_const_mul _ _
  rw [houter]
  change ‖(N : ℂ) ^ z * (∫ v : ℝ, F v * (k v : ℂ)) - B * (N : ℂ) ^ z‖ ≤ _
  rw [show (N : ℂ) ^ z * (∫ v : ℝ, F v * (k v : ℂ)) - B * (N : ℂ) ^ z =
    (N : ℂ) ^ z * ((∫ v : ℝ, F v * (k v : ℂ)) - B) by ring,
    norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN]
  calc
    _ ≤ N ^ z.re * D := mul_le_mul_of_nonneg_left herr (Real.rpow_nonneg hN.le _)
    _ = _ := by dsimp [D, z]; ring

/-- LEAF. Page 29 proof of 7.19. The unscaled decay is stronger since T is at most N. -/
theorem archimedean_decay_compare107 {A N T U : ℝ} (hA : 0 < A)
    (hT : 1 ≤ T) (hTN : T ≤ N) (hU : 0 ≤ U) :
    (1 + U) ^ (-A) ≤ (1 + U * T / N) ^ (-A) := by
  have hN : 0 < N := by linarith
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  have : U * T / N ≤ U := (div_le_iff₀ hN).mpr (mul_le_mul_of_nonneg_left hTN hU)
  linarith

/-- CONDITIONAL on the two remaining oscillatory leaves above. Exact existing Lemma76 proposition.
The assembly has no direct sorry and does not invoke the original cited lemma76. -/
theorem lemma76_decomposed107 : Lemma76 := by
  intro ϕ G hϕ hG
  constructor
  · intro A hA
    obtain ⟨C₁, hC₁⟩ := archimedean_opposite107 hϕ hG A hA
    obtain ⟨C₂, hC₂⟩ := archimedean_same107 hϕ hG A hA
    refine ⟨max (max C₁ C₂) 0, ?_⟩
    intro N T hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂'
    rw [archimedean_coordinates107 hϕ hG hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂']
    have hN : 0 < N := by linarith
    have hpow : 0 ≤ N ^ ((ρ₁ + ρ₂).re - 1) := Real.rpow_nonneg (by linarith) _
    by_cases hs : ρ₁.im * ρ₂.im < 0
    · have hb := hC₁ N T hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂' hs
      apply hb.trans
      have hc : C₁ ≤ max (max C₁ C₂) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
      calc
        C₁ * N ^ ((ρ₁ + ρ₂).re - 1) * (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) ≤
            max (max C₁ C₂) 0 * N ^ ((ρ₁ + ρ₂).re - 1) *
              (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) := by
          gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (archimedean_decay_compare107 hA hT hTN (by positivity))
          (mul_nonneg (le_max_right _ _) hpow)
    · exact (hC₂ N T hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂' (le_of_not_gt hs)).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (le_trans (le_max_right C₁ C₂) (le_max_left _ _)) hpow)
          (Real.rpow_nonneg (by positivity) _))
  · obtain ⟨C, hC⟩ := archimedean_taylor107 hϕ hG
    refine ⟨C, ?_⟩
    intro N T hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂' hs
    rw [archimedean_coordinates107 hϕ hG hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂']
    exact hC N T hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂' hs

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.archimedean_coordinates107
#print axioms LeanLab.BhowmikGrimmelt2026.archimedean_opposite107
#print axioms LeanLab.BhowmikGrimmelt2026.archimedean_same107
#print axioms LeanLab.BhowmikGrimmelt2026.archimedean_taylor107
#print axioms LeanLab.BhowmikGrimmelt2026.archimedean_decay_compare107
#print axioms LeanLab.BhowmikGrimmelt2026.lemma76_decomposed107

#print axioms LeanLab.BhowmikGrimmelt2026.integrable_GT150
#print axioms LeanLab.BhowmikGrimmelt2026.integral_GT150
#print axioms LeanLab.BhowmikGrimmelt2026.nonneg_GT150
#print axioms LeanLab.BhowmikGrimmelt2026.measurable_real_cpow150

#print axioms LeanLab.BhowmikGrimmelt2026.measurable_Jphi150
#print axioms LeanLab.BhowmikGrimmelt2026.global_beta_taylor150
