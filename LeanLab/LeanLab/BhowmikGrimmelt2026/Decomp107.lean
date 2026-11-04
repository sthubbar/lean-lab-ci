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

/-! ## Helpers for the closing of `archimedean_same107` (display 7.19, equal signs).

The `v`-direction integration by parts against the phase `e^{i τ log v}`, the Fubini step that
puts the `σ`-integral outside, and the assembly of the equal-sign leaf.  AI wrote the Lean code.
Goldbach is open. -/

open Filter

open scoped Topology

private theorem abs_add_of_mul_nonneg107' {t₁ t₂ : ℝ} (h : 0 ≤ t₁ * t₂) :
    |t₁ + t₂| = |t₁| + |t₂| := by
  rcases mul_nonneg_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg (by linarith)]
  · rw [abs_of_nonpos h1, abs_of_nonpos h2, abs_of_nonpos (by linarith)]
    ring

private theorem hasDerivAt_phase107' {τ : ℝ} {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w : ℝ => τ * Real.log w) (τ / v) v := by
  have h := (Real.hasDerivAt_log hv.ne').const_mul τ
  have h2 : τ * v⁻¹ = τ / v := by ring
  rwa [h2] at h

private theorem hasDerivAt_cexp_phase107' {τ : ℝ} {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w : ℝ => Complex.exp (Complex.I * ((τ * Real.log w : ℝ) : ℂ)))
      (Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) *
        (Complex.I * ((τ / v : ℝ) : ℂ))) v := by
  have hp : HasDerivAt (fun w : ℝ => τ * Real.log w) (τ / v) v := hasDerivAt_phase107' hv
  have h1 : HasDerivAt (fun w : ℝ => Complex.I * ((τ * Real.log w : ℝ) : ℂ))
      (Complex.I * ((τ / v : ℝ) : ℂ)) v := by
    have h := hp.ofReal_comp
    simpa using h.const_mul Complex.I
  exact h1.cexp

/-- `u = e^{iΦ} · (v/τ)(-i)` has derivative `e^{iΦ}(1 - i/τ)`. -/
private theorem hasDerivAt_ephase_id107' {τ : ℝ} (hτ : τ ≠ 0) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w : ℝ => Complex.exp (Complex.I * ((τ * Real.log w : ℝ) : ℂ)) *
        (((w / τ : ℝ) : ℂ) * (-Complex.I)))
      (Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) * (1 - Complex.I / (τ : ℂ))) v := by
  have hII : (Complex.I : ℂ) * Complex.I = -1 := Complex.I_mul_I
  have hlin : HasDerivAt (fun w : ℝ => ((w / τ : ℝ) : ℂ) * (-Complex.I))
      (((τ : ℝ)⁻¹ : ℝ) * (-Complex.I) : ℂ) v := by
    have h : HasDerivAt (fun w : ℝ => (w / τ : ℝ)) (τ⁻¹) v := by
      simpa using (hasDerivAt_id v).div_const τ
    simpa using h.ofReal_comp.mul_const (-Complex.I)
  have hprod := (hasDerivAt_cexp_phase107' (τ := τ) hv).mul hlin
  have hkey : ((τ / v : ℝ) : ℂ) * ((v / τ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    have h : τ / v * (v / τ) = 1 := by field_simp
    rw [h]
    norm_num
  have hterm : Complex.I * ((τ / v : ℝ) : ℂ) * (((v / τ : ℝ) : ℂ) * (-Complex.I)) = 1 := by
    have hassoc : Complex.I * ((τ / v : ℝ) : ℂ) * (((v / τ : ℝ) : ℂ) * (-Complex.I))
        = (Complex.I * (-Complex.I)) * (((τ / v : ℝ) : ℂ) * ((v / τ : ℝ) : ℂ)) := by ring
    rw [hassoc, hkey, mul_neg, hII]
    norm_num
  have hlin2 : (((τ : ℝ)⁻¹ : ℝ) * (-Complex.I) : ℂ) = -(Complex.I / (τ : ℂ)) := by
    have hinv : (((τ : ℝ)⁻¹ : ℝ) : ℂ) = (τ : ℂ)⁻¹ := by
      rw [← Complex.ofReal_inv]
    rw [hinv, div_eq_mul_inv]
    ring
  rw [hlin2] at hprod
  have hval : Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) * (Complex.I * ((τ / v : ℝ) : ℂ)) *
        (((v / τ : ℝ) : ℂ) * (-Complex.I)) +
        Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) * (-(Complex.I / (τ : ℂ))) =
      Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) * (1 - Complex.I / (τ : ℂ)) := by
    rw [show Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) *
          (Complex.I * ((τ / v : ℝ) : ℂ)) * (((v / τ : ℝ) : ℂ) * (-Complex.I)) =
        Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) *
          (Complex.I * ((τ / v : ℝ) : ℂ) * (((v / τ : ℝ) : ℂ) * (-Complex.I))) from by ring,
      hterm, mul_one]
    ring
  rw [← hval]
  exact hprod

private theorem one_sub_I_div_ne_zero107' {τ : ℝ} (hτ : τ ≠ 0) :
    (1 - Complex.I / (τ : ℂ)) ≠ 0 := by
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have hnum : ((τ : ℂ) - Complex.I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.div_re, Complex.div_im] at hre
    exact absurd hre hτ
  have heq : 1 - Complex.I / (τ : ℂ) = ((τ : ℂ) - Complex.I) / (τ : ℂ) := by
    field_simp
  rw [heq]
  exact div_ne_zero hnum hτc

/-- One integration by parts against the phase `e^{iΦ}`: with `f` vanishing at both endpoints,
`∫ e^{iΦ} f = -(1-i/τ)⁻¹ ∫ e^{iΦ} (v/τ)(-i) f'`. -/
private theorem ibp_v_phase_step107' {τ a b : ℝ} (hτ : τ ≠ 0) (ha : 0 < a) (hab : a ≤ b)
    {f f' : ℝ → ℂ} (hf : ∀ v ∈ Set.uIcc a b, HasDerivAt f (f' v) v)
    (hf' : IntervalIntegrable f' volume a b)
    (hfa : f a = 0) (hfb : f b = 0) :
    ∫ v in a..b, Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) * f v
      = -(1 - Complex.I / (τ : ℂ))⁻¹ *
        ∫ v in a..b, Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) *
          ((((v / τ : ℝ) : ℂ) * (-Complex.I)) * f' v) := by
  have hne := one_sub_I_div_ne_zero107' hτ
  have hdiff : ∀ v ∈ Set.uIcc a b, HasDerivAt
      (fun w : ℝ => Complex.exp (Complex.I * ((τ * Real.log w : ℝ) : ℂ)) *
        (((w / τ : ℝ) : ℂ) * (-Complex.I)))
      (Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) * (1 - Complex.I / (τ : ℂ))) v := by
    intro v hv
    rw [Set.uIcc_of_le hab] at hv
    have hv0 : 0 < v := lt_of_lt_of_le ha (Set.mem_Icc.mp hv).1
    exact hasDerivAt_ephase_id107' hτ hv0
  have hcont : ContinuousOn
      (fun v : ℝ => Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) *
        (1 - Complex.I / (τ : ℂ))) (Set.uIcc a b) := by
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.cexp
    apply ContinuousOn.const_mul
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact ContinuousOn.mul continuousOn_const
      (Real.continuousOn_log.mono (fun x hx => by
        have hx' : x ∈ Set.Icc a b := Set.uIcc_of_le hab ▸ hx
        have hx0 : 0 < x := lt_of_lt_of_le ha hx'.1
        simpa [Set.mem_compl_iff] using hx0.ne'))
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun w : ℝ => Complex.exp (Complex.I * ((τ * Real.log w : ℝ) : ℂ)) *
      (((w / τ : ℝ) : ℂ) * (-Complex.I)))
    (u' := fun v : ℝ => Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) *
      (1 - Complex.I / (τ : ℂ)))
    (v := f) (v' := f') hdiff hf hcont.intervalIntegrable hf'
  rw [hfa, hfb] at hparts
  simp only [mul_zero, sub_zero, sub_self] at hparts
  -- hparts : ∫ v, u v * f' v = -∫ v, u' v * f v
  have hleft : ∫ v in a..b, (fun w : ℝ => Complex.exp (Complex.I * ((τ * Real.log w : ℝ) : ℂ)) *
        (((w / τ : ℝ) : ℂ) * (-Complex.I))) v * f' v
      = ∫ v in a..b, Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) *
          ((((v / τ : ℝ) : ℂ) * (-Complex.I)) * f' v) := by
    apply intervalIntegral.integral_congr
    intro v _
    ring
  have hright : ∫ v in a..b, (fun v : ℝ => Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) *
        (1 - Complex.I / (τ : ℂ))) v * f v
      = (1 - Complex.I / (τ : ℂ)) *
        ∫ v in a..b, Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) * f v := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _
    ring
  rw [hleft, hright] at hparts
  rw [hparts]
  have hX : ∀ X : ℂ, -(1 - Complex.I / (τ : ℂ))⁻¹ * (0 - (1 - Complex.I / (τ : ℂ)) * X) = X := by
    intro X
    field_simp
    ring
  exact (hX _).symm

/-- The `k`-fold iteration of the by-parts step: the family satisfies `f (j+1) = Λ (g j)`
with `g j` the derivative of `f j`, so every `f j` may be replaced by `f k` under `e^{iΦ}`. -/
private theorem ibp_v_phase_iter107' {τ a b : ℝ} (hτ : τ ≠ 0) (ha : 0 < a) (hab : a ≤ b)
    (k : ℕ) : ∀ (f g : ℕ → ℝ → ℂ),
    (∀ j, j ≤ k → ∀ v ∈ Set.uIcc a b, HasDerivAt (f j) (g j v) v) →
    (∀ j, j < k → ∀ v ∈ Set.uIcc a b,
      f (j + 1) v = -(1 - Complex.I / (τ : ℂ))⁻¹ *
        ((((v / τ : ℝ) : ℂ) * (-Complex.I)) * g j v)) →
    (∀ j, j < k → IntervalIntegrable (g j) volume a b) →
    (∀ j, j ≤ k → f j a = 0) → (∀ j, j ≤ k → f j b = 0) →
    ∫ v in a..b, Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) * f 0 v
      = ∫ v in a..b, Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) * f k v := by
  induction k with
  | zero =>
    intro f g hder hform hint hza hzb
    simp
  | succ k ih =>
    intro f g hder hform hint hza hzb
    have hstep : ∫ v in a..b, Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) * f 0 v
        = ∫ v in a..b, Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) * f 1 v := by
      rw [ibp_v_phase_step107' (τ := τ) (a := a) (b := b) hτ ha hab
        (hder 0 (Nat.zero_le _)) (hint 0 (Nat.succ_pos k))
        (hza 0 (Nat.zero_le _)) (hzb 0 (Nat.zero_le _))]
      rw [show -(1 - Complex.I / (τ : ℂ))⁻¹ *
          ∫ v in a..b, Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) *
            ((((v / τ : ℝ) : ℂ) * (-Complex.I)) * g 0 v)
          = ∫ v in a..b, Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) *
            (-(1 - Complex.I / (τ : ℂ))⁻¹ *
              ((((v / τ : ℝ) : ℂ) * (-Complex.I)) * g 0 v)) from by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro v _
        ring]
      apply intervalIntegral.integral_congr
      intro v hv
      have h := hform 0 (Nat.succ_pos k) v hv
      simp only [Pi.mul_apply]
      rw [show f 1 v = -(1 - Complex.I / (τ : ℂ))⁻¹ *
        ((((v / τ : ℝ) : ℂ) * (-Complex.I)) * g 0 v) from h]
    have hih := ih (f := fun j => f (j + 1)) (g := fun j => g (j + 1))
      (fun j hj v hv => hder (j + 1) (by omega) v hv)
      (fun j hj v hv => hform (j + 1) (by omega) v hv)
      (fun j hj => hint (j + 1) (by omega))
      (fun j hj => hza (j + 1) (by omega))
      (fun j hj => hzb (j + 1) (by omega))
    rw [hstep, hih]

/-- Combinatorial core of the `v`-direction bound: a sequence with the recursion
`J (r+1) l ≤ κ J r (l+1) + (l/τ) J r l` (a by-parts step either raises the derivative level,
gaining `κ`, or keeps it at the price `l/τ ≤ n/τ`) satisfies
`J r l ≤ 2^r Σ_i binom r i κ^i (n/τ)^{r-i} J 0 (l+i)`.  The binomial form matches the `κ`-gains
against the index `i` (which carries the `N^{σ₀-1-i}` decay of the amplitude `ψ`), not against
`n`; the `2^r` is the constant of the doubling of the two branches. -/
private theorem star_bound107'' (n : ℕ) (κ τ : ℝ) (hκ : 0 ≤ κ) (hτ : 0 < τ)
    (J : ℕ → ℕ → ℝ) (hJ0 : ∀ l, 0 ≤ J 0 l)
    (hJ : ∀ r l, J (r + 1) l ≤ κ * J r (l + 1) + ((l : ℝ) / τ) * J r l) :
    ∀ r l : ℕ, l + r ≤ n →
      J r l ≤ 2 ^ r * ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * κ ^ i * ((n : ℝ) / τ) ^ (r - i) *
        J 0 (l + i) := by
  have keyA : ∀ (r l i : ℕ), i ≤ r → (l : ℝ) ≤ (n : ℝ) → 0 ≤ κ →
      κ * (((r.choose i : ℝ) * κ ^ i * ((n : ℝ) / τ) ^ (r - i)) * J 0 (l + 1 + i)) ≤
        (((r + 1).choose (i + 1) : ℝ) * κ ^ (i + 1) * ((n : ℝ) / τ) ^ ((r + 1) - (i + 1))) *
          J 0 (l + i + 1) := by
    intro r l i hir _ hk
    have hchooseA : (r.choose i : ℝ) ≤ ((r + 1).choose (i + 1) : ℝ) := by
      have h := Nat.choose_succ_succ r i
      have h2 : r.choose i ≤ (r + 1).choose (i + 1) := by rw [h]; exact Nat.le_add_right _ _
      exact_mod_cast h2
    have hexpA : ((r + 1) - (i + 1)) = r - i := by omega
    have hcoef : κ * ((r.choose i : ℝ) * κ ^ i) ≤ ((r + 1).choose (i + 1) : ℝ) * κ ^ (i + 1) := by
      have heq : κ * ((r.choose i : ℝ) * κ ^ i) = (r.choose i : ℝ) * κ ^ (i + 1) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hchooseA (pow_nonneg hk _)
    have hX : (0 : ℝ) ≤ ((n : ℝ) / τ) ^ (r - i) * J 0 (l + 1 + i) :=
      mul_nonneg (pow_nonneg (by positivity) _) (hJ0 _)
    rw [hexpA]
    calc κ * (((r.choose i : ℝ) * κ ^ i * ((n : ℝ) / τ) ^ (r - i)) * J 0 (l + 1 + i))
        = (κ * ((r.choose i : ℝ) * κ ^ i)) * (((n : ℝ) / τ) ^ (r - i) * J 0 (l + 1 + i)) := by ring
      _ ≤ (((r + 1).choose (i + 1) : ℝ) * κ ^ (i + 1)) *
            (((n : ℝ) / τ) ^ (r - i) * J 0 (l + 1 + i)) := mul_le_mul_of_nonneg_right hcoef hX
      _ = _ := by ring
  have keyB : ∀ (r l i : ℕ), i ≤ r → (l : ℝ) ≤ (n : ℝ) → 0 < τ →
      ((l : ℝ) / τ) * (((r.choose i : ℝ) * κ ^ i * ((n : ℝ) / τ) ^ (r - i)) * J 0 (l + i)) ≤
        (((r + 1).choose i : ℝ) * κ ^ i * ((n : ℝ) / τ) ^ ((r + 1) - i)) * J 0 (l + i) := by
    intro r l i hir hln hτpos
    have hchooseB : (r.choose i : ℝ) ≤ ((r + 1).choose i : ℝ) := by
      have h : r.choose i ≤ (r + 1).choose i := Nat.choose_le_choose i (Nat.le_succ r)
      exact_mod_cast h
    have hpow2 : ((n : ℝ) / τ) ^ ((r + 1) - i) = ((n : ℝ) / τ) ^ (r - i) * ((n : ℝ) / τ) := by
      rw [show ((r + 1) - i) = ((r - i) + 1) from by omega, pow_succ]
    rw [hpow2]
    have hX : (0 : ℝ) ≤ ((n : ℝ) / τ) ^ (r - i) * J 0 (l + i) :=
      mul_nonneg (pow_nonneg (by positivity) _) (hJ0 _)
    have hlτ : ((l : ℝ) / τ) ≤ ((n : ℝ) / τ) := div_le_div_of_nonneg_right hln hτpos.le
    have hcoef : ((l : ℝ) / τ) * ((r.choose i : ℝ) * κ ^ i)
        ≤ ((n : ℝ) / τ) * (((r + 1).choose i : ℝ) * κ ^ i) :=
      mul_le_mul hlτ (mul_le_mul_of_nonneg_right hchooseB (pow_nonneg hκ _))
        (mul_nonneg (by exact_mod_cast Nat.zero_le _) (pow_nonneg hκ _)) (by positivity)
    calc ((l : ℝ) / τ) * ((r.choose i : ℝ) * κ ^ i * ((n : ℝ) / τ) ^ (r - i) * J 0 (l + i))
        = (((l : ℝ) / τ) * ((r.choose i : ℝ) * κ ^ i)) * (((n : ℝ) / τ) ^ (r - i) * J 0 (l + i)) := by
          ring
      _ ≤ (((n : ℝ) / τ) * (((r + 1).choose i : ℝ) * κ ^ i)) *
            (((n : ℝ) / τ) ^ (r - i) * J 0 (l + i)) := mul_le_mul_of_nonneg_right hcoef hX
      _ = _ := by ring
  intro r
  induction r with
  | zero =>
    intro l _
    simp
  | succ r ih =>
    intro l hl
    have hl1 : l + 1 + r ≤ n := by omega
    have hl0 : l + r ≤ n := by omega
    have hln : l ≤ n := by omega
    have hlnr : (l : ℝ) ≤ (n : ℝ) := by exact_mod_cast hln
    have hb : (0 : ℝ) ≤ (l : ℝ) / τ := by positivity
    have h2r : (0 : ℝ) ≤ 2 ^ r := by positivity
    have h1 := ih (l + 1) hl1
    have h0 := ih l hl0
    -- the target, with the two branches collapsed
    have htarget : (2 : ℝ) ^ r * ∑ j ∈ Finset.range (r + 2),
          ((r + 1).choose j : ℝ) * κ ^ j * ((n : ℝ) / τ) ^ ((r + 1) - j) * J 0 (l + j)
        = 2 ^ r * (∑ j ∈ Finset.range (r + 2),
            ((r + 1).choose j : ℝ) * κ ^ j * ((n : ℝ) / τ) ^ ((r + 1) - j) * J 0 (l + j)) := rfl
    -- branch A
    have hAshift : ∑ j ∈ Finset.range (r + 2),
          ((r + 1).choose j : ℝ) * κ ^ j * ((n : ℝ) / τ) ^ ((r + 1) - j) * J 0 (l + j) =
        (∑ i ∈ Finset.range (r + 1),
          ((r + 1).choose (i + 1) : ℝ) * κ ^ (i + 1) * ((n : ℝ) / τ) ^ ((r + 1) - (i + 1)) *
            J 0 (l + i + 1)) +
        ((r + 1).choose 0 : ℝ) * κ ^ 0 * ((n : ℝ) / τ) ^ ((r + 1) - 0) * J 0 (l + 0) := by
      rw [Finset.sum_range_succ']
      rfl
    have hA : κ * J r (l + 1) ≤ 2 ^ r * ∑ j ∈ Finset.range (r + 2),
          ((r + 1).choose j : ℝ) * κ ^ j * ((n : ℝ) / τ) ^ ((r + 1) - j) * J 0 (l + j) := by
      refine (mul_le_mul_of_nonneg_left h1 hκ).trans ?_
      have hcol : κ * (2 ^ r * ∑ i ∈ Finset.range (r + 1),
            (r.choose i : ℝ) * κ ^ i * ((n : ℝ) / τ) ^ (r - i) * J 0 (l + 1 + i))
          = 2 ^ r * ∑ i ∈ Finset.range (r + 1),
              κ * (((r.choose i : ℝ) * κ ^ i * ((n : ℝ) / τ) ^ (r - i)) * J 0 (l + 1 + i)) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hcol]
      refine mul_le_mul_of_nonneg_left ?_ h2r
      refine (Finset.sum_le_sum fun i hi => keyA r l i (by
        have hi2 := Finset.mem_range.mp hi; omega) hlnr hκ).trans ?_
      rw [hAshift]
      have hnn : (0 : ℝ) ≤ ((r + 1).choose 0 : ℝ) * κ ^ 0 * ((n : ℝ) / τ) ^ ((r + 1) - 0) * J 0 (l + 0) := by
        refine mul_nonneg (mul_nonneg (mul_nonneg ?_ (pow_nonneg hκ 0)) (pow_nonneg (by positivity) _)) (hJ0 _)
        exact_mod_cast Nat.zero_le _
      linarith
    -- branch B
    have hB : ((l : ℝ) / τ) * J r l ≤ 2 ^ r * ∑ j ∈ Finset.range (r + 2),
          ((r + 1).choose j : ℝ) * κ ^ j * ((n : ℝ) / τ) ^ ((r + 1) - j) * J 0 (l + j) := by
      refine (mul_le_mul_of_nonneg_left h0 hb).trans ?_
      have hcol : ((l : ℝ) / τ) * (2 ^ r * ∑ i ∈ Finset.range (r + 1),
            (r.choose i : ℝ) * κ ^ i * ((n : ℝ) / τ) ^ (r - i) * J 0 (l + i))
          = 2 ^ r * ∑ i ∈ Finset.range (r + 1),
              ((l : ℝ) / τ) * (((r.choose i : ℝ) * κ ^ i * ((n : ℝ) / τ) ^ (r - i)) * J 0 (l + i)) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hcol]
      refine mul_le_mul_of_nonneg_left ?_ h2r
      refine (Finset.sum_le_sum fun i hi => keyB r l i (by
        have hi2 := Finset.mem_range.mp hi; omega) hlnr hτ).trans ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (Nat.le_succ (r + 1)))
        (fun i _ _ => mul_nonneg (mul_nonneg (mul_nonneg (by exact_mod_cast Nat.zero_le _)
          (pow_nonneg hκ _)) (pow_nonneg (by positivity) _)) (hJ0 _))
    refine (hJ r l).trans ?_
    refine (add_le_add hA hB).trans ?_
    rw [← add_mul]
    have : (2 : ℝ) ^ r + 2 ^ r = 2 ^ (r + 1) := by ring
    rw [this]

/-- The Euler identity for the `l`-th derivative of `v ↦ v * g v`: the operator `K g = v · g'`
satisfies `(K g)^(l) = v · g^(l+1) + l · g^(l)`.  Stated as `(v · g)^(l) = v · g^(l) + l · g^(l-1)`,
which is the form the by-parts recursion needs. -/
private theorem iteratedDeriv_mul_id107 {g : ℝ → ℂ} (hg : ∀ m : ℕ, ContDiff ℝ (m : ℕ∞) g) :
    ∀ (l : ℕ) (v : ℝ),
      iteratedDeriv l (fun w : ℝ => (w : ℂ) * g w) v
        = (v : ℂ) * iteratedDeriv l g v + (l : ℂ) * iteratedDeriv (l - 1) g v := by
  intro l
  induction l with
  | zero =>
    intro v
    simp
  | succ l ih =>
    intro v
    rw [iteratedDeriv_succ]
    have hEq : iteratedDeriv l (fun w : ℝ => (w : ℂ) * g w) =ᶠ[nhds v]
        ((fun w : ℝ => (w : ℂ) * iteratedDeriv l g w) +
          fun w => (l : ℂ) * iteratedDeriv (l - 1) g w) := by
      filter_upwards [] with w
      exact ih w
    rw [hEq.deriv_eq]
    have h1 : HasDerivAt (fun w : ℝ => iteratedDeriv l g w) (iteratedDeriv (l + 1) g v) v := by
      have hd : DifferentiableAt ℝ (fun w : ℝ => iteratedDeriv l g w) v :=
        ((hg (l + 1)).differentiable_iteratedDeriv' l).differentiableAt
      have h := hd.hasDerivAt
      rw [← iteratedDeriv_succ] at h
      exact h
    have h2 : HasDerivAt (fun w : ℝ => (l : ℂ) * iteratedDeriv (l - 1) g w)
        ((l : ℂ) * iteratedDeriv l g v) v := by
      rcases Nat.eq_zero_or_pos l with h0 | hpos
      · subst h0
        simp only [Nat.cast_zero, zero_mul]
        exact hasDerivAt_const v 0
      · have hlt : ((l - 1 : ℕ) : WithTop ℕ∞) < ((l : ℕ) : WithTop ℕ∞) := by
          have h : l - 1 < l := by omega
          exact_mod_cast h
        have hd : DifferentiableAt ℝ (fun w : ℝ => iteratedDeriv (l - 1) g w) v :=
          ((hg l).differentiable_iteratedDeriv (l - 1) hlt).differentiableAt
        have h := hd.hasDerivAt.const_mul ((l : ℂ))
        have he : deriv (iteratedDeriv (l - 1) g) v = iteratedDeriv l g v := by
          rw [← iteratedDeriv_succ, show l - 1 + 1 = l from by omega]
        rwa [he] at h
    have hin : HasDerivAt (fun w : ℝ => ((w : ℝ) : ℂ)) (1 : ℂ) v := by
      simpa using (hasDerivAt_id v).ofReal_comp
    have hA : HasDerivAt (fun w : ℝ => (w : ℂ) * iteratedDeriv l g w)
        (1 * iteratedDeriv l g v + (v : ℂ) * iteratedDeriv (l + 1) g v) v := hin.mul h1
    have hsum := hA.add h2
    rw [hsum.deriv]
    push_cast
    ring

/-- `deriv` commutes with `iteratedDeriv`: `l` derivatives of `deriv g` are `l+1` of `g`. -/
private theorem iteratedDeriv_deriv107 {g : ℝ → ℂ} (l : ℕ) :
    iteratedDeriv l (deriv g) = iteratedDeriv (l + 1) g :=
  (iteratedDeriv_succ' (n := l) (f := g)).symm

/-- The recursion of the by-parts scheme on the derivative integrals
`J_{r,l} = ∫_a^b ‖(f_r)^{(l)}‖`: with `f_{r+1} = c · (v · f_r')` and `|v| ≤ V` on `[a,b]`,

  `J_{r+1,l} ≤ ‖c‖ (V J_{r,l+1} + l J_{r,l})`,

which is `iteratedDeriv_mul_id107` after Leibniz on the linear factor. -/
private theorem iterNorm_rec107 {c : ℂ} {a b V : ℝ} (hab : a ≤ b) (hVc : 0 ≤ V)
    (hV : ∀ v ∈ Set.uIcc a b, |v| ≤ V)
    {f : ℕ → ℝ → ℂ} (hf : ∀ r v, f (r + 1) v = c * ((v : ℂ) * deriv (f r) v))
    (hsm : ∀ r (n : ℕ∞), ContDiff ℝ n (f r)) :
    ∀ r l, ∫ v in a..b, ‖iteratedDeriv l (f (r + 1)) v‖ ≤
      ‖c‖ * ((∫ v in a..b, V * ‖iteratedDeriv (l + 1) (f r) v‖) +
        ∫ v in a..b, (l : ℝ) * ‖iteratedDeriv l (f r) v‖) := by
  intro r l
  have hcd : ∀ n : ℕ, ContDiff ℝ (n : ℕ∞) (deriv (f r)) := by
    intro n
    exact (hsm r ((n : ℕ∞) + 1)).deriv'
  have hfun : f (r + 1) = fun w : ℝ => c * ((w : ℂ) * deriv (f r) w) := by
    funext w
    exact hf r w
  have hpt : ∀ v, iteratedDeriv l (f (r + 1)) v
      = c * ((v : ℂ) * iteratedDeriv (l + 1) (f r) v + (l : ℂ) * iteratedDeriv l (f r) v) := by
    intro v
    rw [hfun, iteratedDeriv_const_mul_field]
    congr 1
    rcases l with _ | l
    · simp [iteratedDeriv_one]
    · have h := iteratedDeriv_mul_id107 hcd (l + 1) v
      rw [h, iteratedDeriv_deriv107 (g := f r) (l + 1),
        show l + 1 - 1 = l from by omega, iteratedDeriv_deriv107 (g := f r) l]
      try ring
  have hcont1 : Continuous (fun v => ‖iteratedDeriv (l + 1) (f r) v‖) :=
    ((hsm r ((l : ℕ∞) + 1)).continuous_iteratedDeriv (l + 1) le_rfl).norm
  have hcont0 : Continuous (fun v => ‖iteratedDeriv l (f r) v‖) :=
    ((hsm r (l : ℕ∞)).continuous_iteratedDeriv l le_rfl).norm
  have hcontL : Continuous (fun v => ‖iteratedDeriv l (f (r + 1)) v‖) :=
    ((hsm (r + 1) (l : ℕ∞)).continuous_iteratedDeriv l le_rfl).norm
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (a := a) (b := b) hab
    (f := fun v => ‖iteratedDeriv l (f (r + 1)) v‖)
    (g := fun v => ‖c‖ * (V * ‖iteratedDeriv (l + 1) (f r) v‖ +
      (l : ℝ) * ‖iteratedDeriv l (f r) v‖))
    (hcontL.intervalIntegrable a b)
    ((((hcont1.const_mul V).add (hcont0.const_mul (l : ℝ))).const_mul ‖c‖).intervalIntegrable a b)
    (fun x hx => by
      have hx' : x ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact hx
      rw [hpt x, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg c)
      have h1 : (0 : ℝ) ≤ ‖iteratedDeriv (l + 1) (f r) x‖ := norm_nonneg _
      have h2 : |x| ≤ V := hV x hx'
      calc ‖(x : ℂ) * iteratedDeriv (l + 1) (f r) x + (l : ℂ) * iteratedDeriv l (f r) x‖
          ≤ ‖(x : ℂ) * iteratedDeriv (l + 1) (f r) x‖ +
              ‖(l : ℂ) * iteratedDeriv l (f r) x‖ := norm_add_le _ _
        _ = |x| * ‖iteratedDeriv (l + 1) (f r) x‖ + (l : ℝ) * ‖iteratedDeriv l (f r) x‖ := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
        _ ≤ V * ‖iteratedDeriv (l + 1) (f r) x‖ + (l : ℝ) * ‖iteratedDeriv l (f r) x‖ := by
            have h3 := mul_le_mul_of_nonneg_right h2 h1
            linarith
    )
  have h1i : IntervalIntegrable (fun v => V * ‖iteratedDeriv (l + 1) (f r) v‖) volume a b :=
    (hcont1.const_mul V).intervalIntegrable a b
  have h0i : IntervalIntegrable (fun v => (l : ℝ) * ‖iteratedDeriv l (f r) v‖) volume a b :=
    (hcont0.const_mul ((l : ℝ))).intervalIntegrable a b
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add h1i h0i]

/-- The recursion in the shape consumed by `star_bound107''`: with `κ = ‖c‖ V` and `‖c‖ ≤ 1/τ`,
`J (r+1) l ≤ κ J r (l+1) + (l/τ) J r l` for `J r l = ∫_a^b ‖(f r)^(l)‖`. -/
private theorem iterNorm_star107 {c : ℂ} {a b V τ : ℝ} (hab : a ≤ b) (hVc : 0 ≤ V)
    (hτ : 0 < τ) (hc : ‖c‖ ≤ 1 / τ)
    (hV : ∀ v ∈ Set.uIcc a b, |v| ≤ V)
    {f : ℕ → ℝ → ℂ} (hf : ∀ r v, f (r + 1) v = c * ((v : ℂ) * deriv (f r) v))
    (hsm : ∀ r (n : ℕ∞), ContDiff ℝ n (f r)) :
    ∀ r l, (∫ v in a..b, ‖iteratedDeriv l (f (r + 1)) v‖)
      ≤ (‖c‖ * V) * (∫ v in a..b, ‖iteratedDeriv (l + 1) (f r) v‖) +
        ((l : ℝ) / τ) * (∫ v in a..b, ‖iteratedDeriv l (f r) v‖) := by
  intro r l
  have hcont1 : Continuous (fun v => ‖iteratedDeriv (l + 1) (f r) v‖) :=
    ((hsm r ((l : ℕ∞) + 1)).continuous_iteratedDeriv (l + 1) le_rfl).norm
  have hcont0 : Continuous (fun v => ‖iteratedDeriv l (f r) v‖) :=
    ((hsm r (l : ℕ∞)).continuous_iteratedDeriv l le_rfl).norm
  have h1i : IntervalIntegrable (fun v => V * ‖iteratedDeriv (l + 1) (f r) v‖) volume a b :=
    (hcont1.const_mul V).intervalIntegrable a b
  have h0i : IntervalIntegrable (fun v => (l : ℝ) * ‖iteratedDeriv l (f r) v‖) volume a b :=
    (hcont0.const_mul ((l : ℝ))).intervalIntegrable a b
  have hmain := iterNorm_rec107 hab hVc hV hf hsm r l
  simp only [intervalIntegral.integral_const_mul] at hmain
  set A := ∫ v in a..b, ‖iteratedDeriv (l + 1) (f r) v‖ with hA
  set B := ∫ v in a..b, ‖iteratedDeriv l (f r) v‖ with hB
  have hA0 : (0 : ℝ) ≤ A := by
    rw [hA]; exact intervalIntegral.integral_nonneg hab (fun x _ => norm_nonneg _)
  have hB0 : (0 : ℝ) ≤ B := by
    rw [hB]; exact intervalIntegral.integral_nonneg hab (fun x _ => norm_nonneg _)
  have hcl : ‖c‖ * (l : ℝ) ≤ (l : ℝ) / τ := by
    have hl : (0 : ℝ) ≤ (l : ℝ) := by positivity
    calc ‖c‖ * (l : ℝ) ≤ (1 / τ) * l := mul_le_mul_of_nonneg_right hc hl
      _ = (l : ℝ) / τ := by ring
  have hgoal : ‖c‖ * (V * A + (l : ℝ) * B) ≤ (‖c‖ * V) * A + ((l : ℝ) / τ) * B := by
    nlinarith [hcl, hA0, hB0, hVc, hτ, norm_nonneg c]
  exact hmain.trans hgoal

/-! ## The kernel's `v`-derivatives, and their integral

`G_T x = T⁻¹ G (x/T)`, so `(G_T)^(m) x = T^{-(m+1)} G^(m) (x/T)` and hence, after the two affine
substitutions `y ↦ y/T` and `w ↦ N - w`,

  `‖(G_T(N - ·))^(m) v‖ = T^{-(m+1)} ‖G^(m)((N-v)/T)‖` and
  `∫_ℝ ‖(G_T(N - ·))^(m)‖ = T^{-m} ∫_ℝ ‖G^(m)‖`.

Only the inequality `≤` over the window `[N-2T-1, N+2T+1]` is needed for `J_{0,i}`; the interval
integral is bounded by the integral over `ℝ`. -/

/-- A public copy of the file's affine-composition formula for `iteratedDeriv` (the version in
`Decomp107.lean` is `private`, so it cannot be used from this file). -/
private theorem iteratedDeriv_affine_comp107b {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (c d : ℝ) : ∀ (m : ℕ) (σ : ℝ),
      iteratedDeriv m (fun x : ℝ => f (c * x + d)) σ = c ^ m * iteratedDeriv m f (c * σ + d)
  | 0, σ => by simp
  | m + 1, σ => by
    rw [iteratedDeriv_succ]
    have hEq : iteratedDeriv m (fun x : ℝ => f (c * x + d)) =
        fun x => c ^ m * iteratedDeriv m f (c * x + d) := by
      funext x
      exact iteratedDeriv_affine_comp107b hf c d m x
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

/-- If `g` vanishes on an open set, so does every iterated derivative. -/
private theorem iteratedDeriv_GT_shift107 {G : ℝ → ℝ} (hG : IsMajorWeight G) {T : ℝ}
    (m : ℕ) (N v : ℝ) :
    iteratedDeriv m (fun w : ℝ => GT G T (N - w)) v
      = (-1) ^ m * (T⁻¹) ^ (m + 1) * iteratedDeriv m G ((N - v) / T) := by
  have hGT : ∀ (m : ℕ) (y : ℝ), iteratedDeriv m (GT G T) y
      = (T⁻¹) ^ (m + 1) * iteratedDeriv m G (y / T) := by
    intro m y
    have hfun : GT G T = fun y : ℝ => T⁻¹ * G (T⁻¹ * y + 0) := by
      funext y
      simp only [GT, zero_add]
      congr 2
      ring
    rw [hfun]
    rw [show iteratedDeriv m (fun y : ℝ => T⁻¹ * G (T⁻¹ * y + 0)) y
        = T⁻¹ * iteratedDeriv m (fun y : ℝ => G (T⁻¹ * y + 0)) y from by
      simpa using iteratedDeriv_const_mul_field (n := m) (T⁻¹)
        (fun y : ℝ => G (T⁻¹ * y + 0)) (x := y)]
    rw [iteratedDeriv_affine_comp107b hG.smooth (T⁻¹) 0 m y]
    rw [show (T⁻¹ * y + 0) = y / T by rw [add_zero, inv_mul_eq_div]]
    ring
  have hshift : ∀ (m : ℕ) (v : ℝ), iteratedDeriv m (fun w : ℝ => GT G T (N - w)) v
      = (-1) ^ m * iteratedDeriv m (GT G T) (N - v) := by
    intro m v
    have hfun : (fun w : ℝ => GT G T (N - w)) = fun w : ℝ => GT G T ((-1) * w + N) := by
      funext w
      congr 1
      ring
    rw [hfun, iteratedDeriv_affine_comp107b (GT_contDiff hG.smooth T) (-1) N m v]
    rw [show (-1 : ℝ) * v + N = N - v by ring]
  rw [hshift m v, hGT m (N - v)]
  ring

/-- The window integral of the `m`-th `v`-derivative of the shifted kernel is at most
`T^{-m} ∫ ‖G^(m)‖`. -/
noncomputable def joint107 (ϕ G : ℝ → ℝ) (T N : ℝ) (ρ₁ ρ₂ : ℂ) (v σ : ℝ) : ℂ :=
  (v : ℂ) ^ (ρ₁ + ρ₂ - 1) * (GT G T (N - v) : ℂ) *
    (((amp107 ϕ N v ρ₁ ρ₂ σ : ℝ) : ℂ) * vexp107 ρ₁.im ρ₂.im σ)

/-- The joint integrand is continuous at every point of `(0, ∞) × (0, 1)`. -/
theorem continuousAt_joint107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G) (T N : ℝ)
    {ρ₁ ρ₂ : ℂ} {p : ℝ × ℝ} (h1 : 0 < p.1) (h2 : 0 < p.2) (h3 : p.2 < 1) :
    ContinuousAt (Function.uncurry (joint107 ϕ G T N ρ₁ ρ₂)) p := by
  have hc : ContinuousAt (fun q : ℝ × ℝ => ((q.1 : ℝ) : ℂ) ^ (ρ₁ + ρ₂ - 1)) p :=
    (Complex.continuousAt_ofReal_cpow_const p.1 (ρ₁ + ρ₂ - 1) (Or.inr (ne_of_gt h1))).comp
      continuousAt_fst
  have hGTc : Continuous (fun a : ℝ => (GT G T (N - a) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((GT_contDiff hG.smooth T).continuous.comp (by fun_prop))
  have hGT : ContinuousAt (fun q : ℝ × ℝ => (GT G T (N - q.1) : ℂ)) p :=
    hGTc.continuousAt.comp continuousAt_fst
  have hpow1 : ContinuousAt (fun q : ℝ × ℝ => q.2 ^ (ρ₁.re - 1)) p :=
    (Real.continuousAt_rpow_const p.2 (ρ₁.re - 1) (Or.inl (ne_of_gt h2))).comp
      continuousAt_snd
  have h1m : ContinuousAt (fun q : ℝ × ℝ => (1 : ℝ) - q.2) p := by fun_prop
  have hpow2 : ContinuousAt (fun q : ℝ × ℝ => (1 - q.2) ^ (ρ₂.re - 1)) p :=
    (Real.continuousAt_rpow_const (1 - p.2) (ρ₂.re - 1) (Or.inl (by linarith))).comp
      (f := fun q : ℝ × ℝ => (1 : ℝ) - q.2) h1m
  have hψ : ContinuousAt (fun q : ℝ × ℝ => ϕ (q.1 * q.2 / N) * ϕ (q.1 * (1 - q.2) / N)) p := by
    have h2' : Continuous (fun q : ℝ × ℝ => ϕ (q.1 * q.2 / N)) :=
      hϕ.smooth.continuous.comp (by fun_prop)
    have h3' : Continuous (fun q : ℝ × ℝ => ϕ (q.1 * (1 - q.2) / N)) :=
      hϕ.smooth.continuous.comp (by fun_prop)
    exact (h2'.mul h3').continuousAt
  have hamp : ContinuousAt (fun q : ℝ × ℝ => ((amp107 ϕ N q.1 ρ₁ ρ₂ q.2 : ℝ) : ℂ)) p := by
    have hreal : ContinuousAt (fun q : ℝ × ℝ => amp107 ϕ N q.1 ρ₁ ρ₂ q.2) p := by
      simp only [amp107]
      have heq : ((fun q : ℝ × ℝ => q.2 ^ (ρ₁.re - 1)) *
          (fun q : ℝ × ℝ => (1 - q.2) ^ (ρ₂.re - 1))) *
          (fun q : ℝ × ℝ => ϕ (q.1 * q.2 / N) * ϕ (q.1 * (1 - q.2) / N)) =
          (fun q : ℝ × ℝ => q.2 ^ (ρ₁.re - 1) * (1 - q.2) ^ (ρ₂.re - 1) *
            (ϕ (q.1 * q.2 / N) * ϕ (q.1 * (1 - q.2) / N))) := by
        funext q
        simp only [Pi.mul_apply]
      rw [← heq]
      exact (hpow1.mul hpow2).mul hψ
    exact Complex.continuous_ofReal.continuousAt.comp hreal
  have hvexp : ContinuousAt (fun q : ℝ × ℝ => vexp107 ρ₁.im ρ₂.im q.2) p := by
    have hlog1 : ContinuousAt (fun q : ℝ × ℝ => Real.log q.2) p :=
      (Real.continuousAt_log (ne_of_gt h2)).comp continuousAt_snd
    have hlog2 : ContinuousAt (fun q : ℝ × ℝ => Real.log (1 - q.2)) p :=
      (Real.continuousAt_log (by linarith : (1 : ℝ) - p.2 ≠ 0)).comp
        (f := fun q : ℝ × ℝ => (1 : ℝ) - q.2) h1m
    have harg : ContinuousAt
        (fun q : ℝ × ℝ => ((ρ₁.im * Real.log q.2 + ρ₂.im * Real.log (1 - q.2) : ℝ) : ℂ)) p := by
      have hmul1 : ContinuousAt (fun q : ℝ × ℝ => ρ₁.im * Real.log q.2) p :=
        continuousAt_const.mul hlog1
      have hmul2 : ContinuousAt (fun q : ℝ × ℝ => ρ₂.im * Real.log (1 - q.2)) p :=
        continuousAt_const.mul hlog2
      have hsum : ContinuousAt
          (fun q : ℝ × ℝ => ρ₁.im * Real.log q.2 + ρ₂.im * Real.log (1 - q.2)) p :=
        hmul1.add hmul2
      exact Complex.continuous_ofReal.continuousAt.comp hsum
    exact Complex.continuous_exp.continuousAt.comp (continuousAt_const.mul harg)
  have huncurry : Function.uncurry (joint107 ϕ G T N ρ₁ ρ₂)
      = fun q : ℝ × ℝ => (q.1 : ℂ) ^ (ρ₁ + ρ₂ - 1) * (GT G T (N - q.1) : ℂ) *
          (((amp107 ϕ N q.1 ρ₁ ρ₂ q.2 : ℝ) : ℂ) * vexp107 ρ₁.im ρ₂.im q.2) := rfl
  rw [huncurry]
  have heq : ((fun q : ℝ × ℝ => (q.1 : ℂ) ^ (ρ₁ + ρ₂ - 1)) *
      (fun q : ℝ × ℝ => (GT G T (N - q.1) : ℂ))) *
      ((fun q : ℝ × ℝ => ((amp107 ϕ N q.1 ρ₁ ρ₂ q.2 : ℝ) : ℂ)) *
        (fun q : ℝ × ℝ => vexp107 ρ₁.im ρ₂.im q.2)) =
      (fun q : ℝ × ℝ => (q.1 : ℂ) ^ (ρ₁ + ρ₂ - 1) * (GT G T (N - q.1) : ℂ) *
        (((amp107 ϕ N q.1 ρ₁ ρ₂ q.2 : ℝ) : ℂ) * vexp107 ρ₁.im ρ₂.im q.2)) := by
    funext q
    simp only [Pi.mul_apply]
  rw [← heq]
  exact (hc.mul hGT).mul (hamp.mul hvexp)

/-- The joint integrand is continuous on a box inside `(0, ∞) × (0, 1)`. -/
theorem continuousOn_joint107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G) (T N : ℝ)
    {α β a b : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (ρ₁ ρ₂ : ℂ) :
    ContinuousOn (Function.uncurry (joint107 ϕ G T N ρ₁ ρ₂)) (Set.uIcc α β ×ˢ Set.uIcc a b) := by
  intro p hp
  refine (continuousAt_joint107 hϕ hG T N ?_ ?_ ?_).continuousWithinAt
  · have h := hp.1
    rw [Set.uIcc_of_le hαβ] at h
    linarith [h.1]
  · have h := hp.2
    rw [Set.uIcc_of_le hab] at h
    linarith [h.1]
  · have h := hp.2
    rw [Set.uIcc_of_le hab] at h
    linarith [h.2]

/-- Fubini for the equal-sign leaf: the two interval integrations commute. -/
theorem joint_swap107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G) {T N : ℝ}
    {α β a b : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (ρ₁ ρ₂ : ℂ) :
    ∫ v in α..β, ∫ σ in a..b, joint107 ϕ G T N ρ₁ ρ₂ v σ
      = ∫ σ in a..b, ∫ v in α..β, joint107 ϕ G T N ρ₁ ρ₂ v σ := by
  refine MeasureTheory.intervalIntegral_intervalIntegral_swap ?_
  refine ((continuousOn_joint107 hϕ hG T N hα hαβ ha hab hb ρ₁ ρ₂).integrableOn_compact
    (isCompact_uIcc.prod isCompact_uIcc)).mono_set ?_
  exact Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc

/-! ## (21) The `v`-derivative chain of the complex power

The equal-sign leaf's integrand is complex, so the by-parts lemmas above take a `ℂ`-valued
amplitude against the real kernel. The phase factor `v ↦ v ^ (ρ₁ + ρ₂ - 1)` then has an explicit
`j`-th derivative chain, bounded by `(1 + ‖c‖) ^ j · j! · v ^ (c.re - j)`. -/

/-- The derivative of a complex power at a positive real point. -/
theorem exists_cutoff_vderiv_bound107 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧ ∀ (N : ℝ), 0 < N → ∀ (m : ℕ) (σ : ℝ), 0 < σ → σ ≤ 4 / 5 →
      ∀ v : ℝ, ‖iteratedDeriv m (fun w : ℝ => ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) v‖
        ≤ D m / N ^ m := by
  obtain ⟨R, hR⟩ := exists_iteratedDeriv_phi_bound107 hϕ
  set R' : ℕ → ℝ := fun m => max (R m) 0 with hR'def
  have hR'0 : ∀ m, 0 ≤ R' m := fun m => le_max_right _ _
  have hR'b : ∀ (m : ℕ) (x : ℝ), ‖iteratedDeriv m ϕ x‖ ≤ R' m := fun m x =>
    (hR m x).trans (le_max_left _ _)
  refine ⟨fun m => ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * R' i * R' (m - i),
    fun m => Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hR'0 i)) (hR'0 (m - i)), ?_⟩
  intro N hN m σ hσ0 hσ1 v
  have h1m0 : (0 : ℝ) < 1 - σ := by linarith
  have hfac : ∀ (c : ℝ), 0 < c → c ≤ 1 → ∀ (i : ℕ) (x : ℝ),
      ‖iteratedDeriv i (fun w : ℝ => ϕ (w * c / N)) x‖ ≤ R' i / N ^ i := by
    intro c hc0 hc1 i x
    have hfun : (fun w : ℝ => ϕ (w * c / N)) = fun w : ℝ => ϕ (c / N * w + 0) := by
      funext w
      congr 1
      ring
    rw [hfun, iteratedDeriv_affine_comp107 hϕ.smooth (c / N) 0 i x, norm_mul, norm_pow,
      Real.norm_eq_abs, abs_of_pos (div_pos hc0 hN)]
    have hle : c / N ≤ 1 / N := by gcongr
    have hpow : (c / N) ^ i ≤ (1 / N) ^ i := pow_le_pow_left₀ (by positivity) hle i
    have hone : (1 / N : ℝ) ^ i = 1 / N ^ i := by rw [div_pow, one_pow]
    have hstep : (c / N) ^ i * ‖iteratedDeriv i ϕ (c / N * x + 0)‖ ≤ (1 / N) ^ i * R' i :=
      mul_le_mul hpow (hR'b i _) (norm_nonneg _) (by positivity)
    calc (c / N) ^ i * ‖iteratedDeriv i ϕ (c / N * x + 0)‖ ≤ (1 / N) ^ i * R' i := hstep
      _ = R' i / N ^ i := by rw [hone]; ring
  have hcd1 : ContDiff ℝ (m : ℕ∞) (fun w : ℝ => ϕ (w * σ / N)) :=
    (hϕ.smooth.comp ((contDiff_id.mul contDiff_const).div_const N)).of_le
      (by rw [WithTop.coe_le_coe]; exact le_top)
  have hcd2 : ContDiff ℝ (m : ℕ∞) (fun w : ℝ => ϕ (w * (1 - σ) / N)) :=
    (hϕ.smooth.comp ((contDiff_id.mul contDiff_const).div_const N)).of_le
      (by rw [WithTop.coe_le_coe]; exact le_top)
  have hmain := norm_iteratedDeriv_mul_le107_real
    (f := fun w : ℝ => ϕ (w * σ / N)) (g := fun w : ℝ => ϕ (w * (1 - σ) / N)) (n := m)
    hcd1 hcd2 v
  refine hmain.trans ?_
  have hterm : ∀ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * ‖iteratedDeriv i (fun w : ℝ => ϕ (w * σ / N)) v‖ *
        ‖iteratedDeriv (m - i) (fun w : ℝ => ϕ (w * (1 - σ) / N)) v‖
      ≤ (m.choose i : ℝ) * R' i * R' (m - i) / N ^ m := by
    intro i hi
    have hi_le : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hb1 := hfac σ hσ0 (by linarith) i v
    have hb2 := hfac (1 - σ) h1m0 (by linarith) (m - i) v
    have hsub : i + (m - i) = m := Nat.add_sub_cancel' hi_le
    have hkey : R' i / N ^ i * (R' (m - i) / N ^ (m - i)) = R' i * R' (m - i) / N ^ m := by
      rw [div_mul_div_comm, ← pow_add, hsub]
    calc (m.choose i : ℝ) * ‖iteratedDeriv i (fun w : ℝ => ϕ (w * σ / N)) v‖ *
          ‖iteratedDeriv (m - i) (fun w : ℝ => ϕ (w * (1 - σ) / N)) v‖
        ≤ (m.choose i : ℝ) * (R' i / N ^ i) * (R' (m - i) / N ^ (m - i)) := by
          refine mul_le_mul (mul_le_mul le_rfl hb1 (norm_nonneg _) (Nat.cast_nonneg _)) hb2
            (norm_nonneg _) ?_
          exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (hR'0 i) (by positivity))
      _ = (m.choose i : ℝ) * R' i * R' (m - i) / N ^ m := by
          rw [show (m.choose i : ℝ) * (R' i / N ^ i) * (R' (m - i) / N ^ (m - i))
              = (m.choose i : ℝ) * (R' i / N ^ i * (R' (m - i) / N ^ (m - i))) from by ring,
            hkey]
          ring
  calc ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedDeriv i (fun w : ℝ => ϕ (w * σ / N)) v‖ *
          ‖iteratedDeriv (m - i) (fun w : ℝ => ϕ (w * (1 - σ) / N)) v‖
      ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * R' i * R' (m - i) / N ^ m :=
        Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * R' i * R' (m - i)) / N ^ m :=
        (Finset.sum_div _ _ _).symm



/-! ## (23) The `v`-amplitude of the equal-sign leaf

`archimedean_same107` integrates by parts in `v` against the phase `e^{i tau log v}`,
`tau = (rho_1 + rho_2).im`.  The amplitude is
`A_sigma v = v ^ (s0 - 1) phi (v sigma / N) phi (v (1 - sigma) / N) G_T (N - v)`,
`s0 = (rho_1 + rho_2).re`.  This section checks that it is globally smooth (the cutoffs vanish
on `v <= 2N/5`, so the singular power at `v = 0` is multiplied by zero) and that it is supported
in `[2N/5, 8N/5]`. -/

/-- The cutoff vanishes below `1/5`. -/
private theorem phi_zero_le107' {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {x : ℝ} (hx : x ≤ 1 / 5) :
    ϕ x = 0 := by
  by_contra h
  have hmem : x ∈ tsupport ϕ := subset_tsupport ϕ h
  have hs := hϕ.supp hmem
  linarith [hs.1]

/-- The cutoff vanishes above `4/5`. -/
private theorem pair_zero_of_v_out107' {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {N : ℝ} (hN : 0 < N)
    {v σ : ℝ} (hv : v ≤ 2 * N / 5 ∨ 8 * N / 5 ≤ v) :
    ϕ (v * σ / N) * ϕ (v * (1 - σ) / N) = 0 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := phi_pair_support84 hϕ hN hne
  rcases hv with h | h <;> linarith

/-- The cutoff pair vanishes for nonpositive `v` and `0 < sigma`. -/
private theorem pair_zero_of_v_nonpos107' {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {N : ℝ} (hN : 0 < N)
    {v σ : ℝ} (hσ : 0 < σ) (hv : v ≤ 0) :
    ϕ (v * σ / N) * ϕ (v * (1 - σ) / N) = 0 := by
  have h : v * σ / N ≤ 1 / 5 := by
    have h2 : v * σ ≤ 0 := by nlinarith
    have : v * σ / N ≤ 0 := div_nonpos_of_nonpos_of_nonneg h2 (le_of_lt hN)
    linarith
  rw [phi_zero_le107' hϕ h, zero_mul]

/-- The `v`-amplitude of the equal-sign leaf is smooth everywhere: for `0 < sigma <= 4/5` the
cutoff pair vanishes on a neighbourhood of every `v <= 0`. -/
private theorem contDiff_afun107' {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    {N T b σ : ℝ} (hN : 0 < N) (hσ : 0 < σ) :
    ∀ n : ℕ∞, ContDiff ℝ n (fun v : ℝ =>
      ((v ^ b * (ϕ (v * σ / N) * ϕ (v * (1 - σ) / N)) * GT G T (N - v) : ℝ) : ℂ)) := by
  intro n
  rw [contDiff_iff_contDiffAt]
  intro v
  rcases lt_or_ge 0 v with hv | hv
  · have h1 : ContDiffAt ℝ n (fun w : ℝ => w ^ b) v :=
      contDiffAt_id.rpow_const_of_ne (ne_of_gt hv)
    have h2 : ContDiffAt ℝ n (fun w : ℝ => ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) v := by
      have ha : ContDiffAt ℝ n (fun w : ℝ => ϕ (w * σ / N)) v :=
        (hϕ.smooth.contDiffAt.comp v ((contDiffAt_id.mul contDiffAt_const).div_const N)).of_le
          (by simp)
      have hb : ContDiffAt ℝ n (fun w : ℝ => ϕ (w * (1 - σ) / N)) v :=
        (hϕ.smooth.contDiffAt.comp v ((contDiffAt_id.mul contDiffAt_const).div_const N)).of_le
          (by simp)
      exact ha.mul hb
    have h3 : ContDiffAt ℝ n (fun w : ℝ => GT G T (N - w)) v := by
      have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ => GT G T (N - w)) := by
        have hfun : (fun w : ℝ => GT G T (N - w)) = fun w : ℝ => T⁻¹ * G ((N - w) / T) := by
          funext w
          simp only [GT]
        rw [hfun]
        exact contDiff_const.mul (hG.smooth.comp ((contDiff_const.sub contDiff_id).div_const T))
      exact hs.contDiffAt.of_le (by simp)
    have h4 : ContDiffAt ℝ n (fun w : ℝ => (w ^ b * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) *
        GT G T (N - w) : ℝ)) v := ((h1.mul h2).mul h3)
    exact (Complex.ofRealCLM.contDiff.contDiffAt).comp v h4
  · have hlt : v < N / 5 := by
      have : (0 : ℝ) < N / 5 := by positivity
      linarith
    have hev : (fun w : ℝ => ((w ^ b * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) *
        GT G T (N - w) : ℝ) : ℂ)) =ᶠ[𝓝 v] 0 := by
      filter_upwards [eventually_lt_nhds hlt] with w hw
      have hzero : ϕ (w * σ / N) * ϕ (w * (1 - σ) / N) = 0 := by
        rcases lt_or_ge w 0 with hw0 | hw0
        · exact pair_zero_of_v_nonpos107' hϕ hN hσ hw0.le
        · exact pair_zero_of_v_out107' hϕ hN (Or.inl (by linarith))
      simp [hzero]
    exact (contDiffAt_const (c := (0 : ℂ)) (x := v)).congr_of_eventuallyEq hev


/-- On the effective window `[N/8, 9N/5]` the closed form of `iteratedDeriv` of a real power
gives the bound `m! 8^(m+1) N ^ (a - m)` for every exponent `a` in `(-1, 1]`. -/
private theorem rpow_vbound107' {a N v : ℝ} (ha0 : -1 < a) (ha1 : a ≤ 1) (hN : 0 < N)
    {m : ℕ} (hv : v ∈ Set.Icc (N / 8) (9 * N / 5)) :
    ‖iteratedDeriv m (fun w : ℝ => w ^ a) v‖ ≤
      ((m.factorial : ℕ) : ℝ) * (8 : ℝ) ^ ((m : ℝ) + 1) * N ^ (a - (m : ℝ)) := by
  have hv0 : 0 < v := by linarith [hv.1]
  rw [iteratedDeriv_rpow107 a hv0 m, Real.norm_eq_abs, abs_mul]
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
  have hpow : |v ^ (a - (m : ℝ))| ≤ (8 : ℝ) ^ ((m : ℝ) + 1) * N ^ (a - (m : ℝ)) := by
    have hpos : (0 : ℝ) < v ^ (a - (m : ℝ)) := Real.rpow_pos_of_pos hv0 _
    rw [abs_of_pos hpos]
    have hNp : (0 : ℝ) ≤ N ^ (a - (m : ℝ)) := Real.rpow_nonneg hN.le _
    rcases le_or_gt 0 (a - (m : ℝ)) with h | h
    · have hstep : v ^ (a - (m : ℝ)) ≤ ((9 / 5 : ℝ) * N) ^ (a - (m : ℝ)) :=
        Real.rpow_le_rpow hv0.le (by linarith [hv.2]) h
      have hsplit : ((9 / 5 : ℝ) * N) ^ (a - (m : ℝ)) =
          (9 / 5 : ℝ) ^ (a - (m : ℝ)) * N ^ (a - (m : ℝ)) :=
        Real.mul_rpow (by norm_num) hN.le
      have hconst : (9 / 5 : ℝ) ^ (a - (m : ℝ)) ≤ (8 : ℝ) ^ ((m : ℝ) + 1) := by
        have hle1 : (9 / 5 : ℝ) ^ (a - (m : ℝ)) ≤ (9 / 5 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (x := (9 / 5 : ℝ)) (by norm_num : (1 : ℝ) ≤ 9 / 5)
            (by linarith)
        rw [Real.rpow_one] at hle1
        have hbase : (9 / 5 : ℝ) ≤ (8 : ℝ) ^ ((m : ℝ) + 1) := by
          have h1 : (8 : ℝ) ^ (1 : ℝ) ≤ (8 : ℝ) ^ ((m : ℝ) + 1) :=
            Real.rpow_le_rpow_of_exponent_le (x := (8 : ℝ)) (by norm_num : (1 : ℝ) ≤ 8)
              (by linarith [Nat.cast_nonneg (α := ℝ) m])
          rw [Real.rpow_one] at h1
          linarith
        linarith
      calc v ^ (a - (m : ℝ)) ≤ (9 / 5 : ℝ) ^ (a - (m : ℝ)) * N ^ (a - (m : ℝ)) := by
            rw [← hsplit]; exact hstep
        _ ≤ (8 : ℝ) ^ ((m : ℝ) + 1) * N ^ (a - (m : ℝ)) :=
            mul_le_mul_of_nonneg_right hconst hNp
    · have hstep : v ^ (a - (m : ℝ)) ≤ ((1 / 8 : ℝ) * N) ^ (a - (m : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith [hv.1]) (by linarith [hv.1]) h.le
      have hsplit : ((1 / 8 : ℝ) * N) ^ (a - (m : ℝ)) =
          (1 / 8 : ℝ) ^ (a - (m : ℝ)) * N ^ (a - (m : ℝ)) :=
        Real.mul_rpow (by norm_num) hN.le
      have hconst : (1 / 8 : ℝ) ^ (a - (m : ℝ)) ≤ (8 : ℝ) ^ ((m : ℝ) + 1) := by
        have heq : (1 / 8 : ℝ) ^ (a - (m : ℝ)) = (8 : ℝ) ^ ((m : ℝ) - a) := by
          rw [show (1 / 8 : ℝ) = (8 : ℝ)⁻¹ by norm_num,
            Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 8),
            ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8)]
          congr 1
          ring
        rw [heq]
        refine Real.rpow_le_rpow_of_exponent_le (x := (8 : ℝ)) (by norm_num) ?_
        linarith
      calc v ^ (a - (m : ℝ)) ≤ (1 / 8 : ℝ) ^ (a - (m : ℝ)) * N ^ (a - (m : ℝ)) := by
            rw [← hsplit]; exact hstep
        _ ≤ (8 : ℝ) ^ ((m : ℝ) + 1) * N ^ (a - (m : ℝ)) :=
            mul_le_mul_of_nonneg_right hconst hNp
  have hNn : (0 : ℝ) ≤ N ^ (a - (m : ℝ)) := Real.rpow_nonneg hN.le _
  calc |∏ i ∈ Finset.range m, (a - (i : ℝ))| * |v ^ (a - (m : ℝ))|
      ≤ ((m.factorial : ℕ) : ℝ) * ((8 : ℝ) ^ ((m : ℝ) + 1) * N ^ (a - (m : ℝ))) :=
        mul_le_mul hfac hpow (abs_nonneg _) (by positivity)
    _ = ((m.factorial : ℕ) : ℝ) * (8 : ℝ) ^ ((m : ℝ) + 1) * N ^ (a - (m : ℝ)) := by ring

/-- The `m`-th derivative of the dilated kernel is `(1/T)^m` times a bounded factor. -/
private theorem integral_norm_ker_deriv107' {G : ℝ → ℝ} (hG : IsMajorWeight G) {T : ℝ}
    (hT : 0 < T) (l : ℕ) (N : ℝ) :
    (∫ v : ℝ, ‖iteratedDeriv l (fun w : ℝ => GT G T (N - w)) v‖)
      = (1 / T) ^ l * ∫ x : ℝ, ‖iteratedDeriv l G x‖ := by
  have hT1 : (0 : ℝ) < T := hT
  have hpt : ∀ v : ℝ, ‖iteratedDeriv l (fun w : ℝ => GT G T (N - w)) v‖
      = (T⁻¹) ^ (l + 1) * ‖iteratedDeriv l G ((N - v) / T)‖ := by
    intro v
    rw [iteratedDeriv_GT_shift107 hG l N v, norm_mul, norm_mul]
    rw [show ‖((-1 : ℝ) ^ l : ℝ)‖ = 1 from by
      rw [Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow]]
    rw [show ‖((T⁻¹) ^ (l + 1) : ℝ)‖ = (T⁻¹) ^ (l + 1) from by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by positivity) _)]]
    ring
  rw [show (fun v : ℝ => ‖iteratedDeriv l (fun w : ℝ => GT G T (N - w)) v‖)
      = fun v : ℝ => (T⁻¹) ^ (l + 1) * ‖iteratedDeriv l G ((N - v) / T)‖ from by
    funext v
    exact hpt v]
  rw [integral_const_mul]
  have hsub : (∫ v : ℝ, ‖iteratedDeriv l G ((N - v) / T)‖)
      = ∫ u : ℝ, ‖iteratedDeriv l G (u / T)‖ := by
    have h1 : (∫ v : ℝ, (fun u : ℝ => ‖iteratedDeriv l G (u / T)‖) (N - v))
        = ∫ u : ℝ, ‖iteratedDeriv l G (u / T)‖ :=
      integral_sub_left_eq_self (fun u : ℝ => ‖iteratedDeriv l G (u / T)‖) volume N
    simpa only [sub_div] using h1
  have hcomp : (∫ u : ℝ, ‖iteratedDeriv l G (u / T)‖)
      = T * ∫ x : ℝ, ‖iteratedDeriv l G x‖ := by
    rw [Measure.integral_comp_div (g := fun z : ℝ => ‖iteratedDeriv l G z‖) (a := T),
      abs_of_pos hT1]
    rfl
  rw [hsub, hcomp]
  have hcoef : (T⁻¹) ^ (l + 1) * (T * ∫ x : ℝ, ‖iteratedDeriv l G x‖)
      = (1 / T) ^ l * ∫ x : ℝ, ‖iteratedDeriv l G x‖ := by
    have h1 : (T⁻¹) ^ (l + 1) * T = (T⁻¹) ^ l := by
      rw [pow_succ]
      field_simp
    calc (T⁻¹) ^ (l + 1) * (T * ∫ x : ℝ, ‖iteratedDeriv l G x‖)
        = ((T⁻¹) ^ (l + 1) * T) * ∫ x : ℝ, ‖iteratedDeriv l G x‖ := by ring
      _ = (T⁻¹) ^ l * ∫ x : ℝ, ‖iteratedDeriv l G x‖ := by rw [h1]
      _ = (1 / T) ^ l * ∫ x : ℝ, ‖iteratedDeriv l G x‖ := by rw [one_div]
  exact hcoef

/-- The `v`-derivatives of `v ↦ v ^ a φ(vσ/N) φ(v(1-σ)/N)` on the effective window: each
derivative costs one factor `1/N`, and the size is `N ^ a`. -/
private theorem pfun_deriv_bound107' {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (r : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (N a σ : ℝ), 0 < N → 0 < σ → σ ≤ 4 / 5 → a ∈ Set.Ioc (-1) 1 →
      ∀ (j : ℕ), j ≤ r → ∀ v ∈ Set.Icc (N / 8) (9 * N / 5),
      ‖iteratedDeriv j (fun w : ℝ => w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N))) v‖
        ≤ K * N ^ a * (K / N) ^ j := by
  obtain ⟨D, hD0, hD⟩ := exists_cutoff_vderiv_bound107 hϕ
  set Ds : ℝ := ∑ i ∈ Finset.range (r + 1), D i with hDs
  set Ps : ℝ := ((r.factorial : ℕ) : ℝ) * (8 : ℝ) ^ (r + 1) with hPs
  have hDs0 : (0 : ℝ) ≤ Ds := by
    rw [hDs]
    exact Finset.sum_nonneg (fun i _ => hD0 i)
  have hPs0 : (0 : ℝ) ≤ Ps := by
    rw [hPs]
    exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
  have hDle : ∀ i, i ≤ r → D i ≤ Ds := by
    intro i hi
    rw [hDs]
    exact Finset.single_le_sum (f := D) (fun k _ => hD0 k) (Finset.mem_range.mpr (by omega))
  have hPle : ∀ i, i ≤ r → ((i.factorial : ℕ) : ℝ) * (8 : ℝ) ^ (i + 1) ≤ Ps := by
    intro i hi
    rw [hPs]
    have h1 : ((i.factorial : ℕ) : ℝ) ≤ ((r.factorial : ℕ) : ℝ) := by
      have : i.factorial ≤ r.factorial := Nat.factorial_le hi
      exact_mod_cast this
    have h2 : (8 : ℝ) ^ (i + 1) ≤ (8 : ℝ) ^ (r + 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 8) (by omega)
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hKmain : (1 : ℝ) ≤ Ps * Ds * 2 ^ r + 1 := by
    have h0 : (0 : ℝ) ≤ Ps * Ds * 2 ^ r := by positivity
    linarith
  refine ⟨Ps * Ds * 2 ^ r + 1, hKmain, ?_⟩
  intro N a σ hN hσ hσ1 ha j hj v hv
  have hv0 : 0 < v := by linarith [hv.1]
  have hNa : (0 : ℝ) ≤ N ^ a := Real.rpow_nonneg hN.le _
  have hψcd : ∀ n : ℕ∞, ContDiff ℝ n (fun w : ℝ => ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) := by
    intro n
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ => ϕ (w * σ / N)) :=
      hϕ.smooth.comp ((contDiff_id.mul contDiff_const).div_const N)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ => ϕ (w * (1 - σ) / N)) :=
      hϕ.smooth.comp ((contDiff_id.mul contDiff_const).div_const N)
    exact (h1.mul h2).of_le (WithTop.coe_le_coe.mpr le_top)
  have hPcdOn : ContDiffOn ℝ (j : ℕ∞) (fun w : ℝ => w ^ a) (Set.Ioi 0) :=
    (contDiffOn_id.rpow_const_of_ne (fun x hx => ne_of_gt hx)).of_le le_top
  have hPcdAt : ∀ i, i ≤ j → ContDiffAt ℝ (i : ℕ∞) (fun w : ℝ => w ^ a) v := fun i _ =>
    (contDiffAt_id.rpow_const_of_ne (ne_of_gt hv0)).of_le le_top
  have hleib := norm_iteratedDerivWithin_mul_le107_real (s := Set.Ioi (0 : ℝ))
    (f := fun w : ℝ => w ^ a) (g := fun w : ℝ => ϕ (w * σ / N) * ϕ (w * (1 - σ) / N))
    (n := j) hPcdOn (hψcd (j : ℕ∞)).contDiffOn (uniqueDiffOn_Ioi 0) hv0
  have hconv : ‖iteratedDerivWithin j
      (fun w : ℝ => w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N))) (Set.Ioi 0) v‖
      = ‖iteratedDeriv j
        (fun w : ℝ => w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N))) v‖ :=
    congrArg (fun z : ℝ => ‖z‖)
      (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
        ((hPcdAt j le_rfl).mul ((hψcd (j : ℕ∞)).contDiffAt)) hv0)
  rw [hconv] at hleib
  have hterm : ∀ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) *
          ‖iteratedDerivWithin i (fun w : ℝ => w ^ a) (Set.Ioi 0) v‖ *
        ‖iteratedDerivWithin (j - i)
          (fun w : ℝ => ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) (Set.Ioi 0) v‖
      ≤ (j.choose i : ℝ) * N ^ a * (1 / N) ^ j * (Ps * Ds) := by
    intro i hi
    have hir : i ≤ r := by
      have := Finset.mem_range.mp hi
      omega
    have hij : i ≤ j := by
      have := Finset.mem_range.mp hi
      omega
    have hconvP : ‖iteratedDerivWithin i (fun w : ℝ => w ^ a) (Set.Ioi 0) v‖
        = ‖iteratedDeriv i (fun w : ℝ => w ^ a) v‖ :=
      congrArg (fun z : ℝ => ‖z‖)
        (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0) (hPcdAt i hij) hv0)
    have hconvψ : ‖iteratedDerivWithin (j - i)
        (fun w : ℝ => ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) (Set.Ioi 0) v‖
        = ‖iteratedDeriv (j - i)
          (fun w : ℝ => ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) v‖ :=
      congrArg (fun z : ℝ => ‖z‖)
        (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
          ((hψcd ((j - i : ℕ) : ℕ∞)).contDiffAt) hv0)
    rw [hconvP, hconvψ]
    have h8 : (8 : ℝ) ^ ((i : ℝ) + 1) = (8 : ℝ) ^ (i + 1) := by
      rw [show ((i : ℝ) + 1) = ((i + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have h1 : ‖iteratedDeriv i (fun w : ℝ => w ^ a) v‖
        ≤ (Ps * (1 / N) ^ i) * N ^ a := by
      refine (rpow_vbound107' ha.1 ha.2 hN hv).trans ?_
      rw [h8]
      have hile : ((i.factorial : ℕ) : ℝ) * (8 : ℝ) ^ (i + 1) ≤ Ps := hPle i hir
      have hna : (0 : ℝ) ≤ N ^ a * (1 / N) ^ i := by positivity
      have hrw : N ^ (a - (i : ℝ)) = N ^ a * (1 / N) ^ i := by
        have hNi : N ^ (i : ℝ) = N ^ i := Real.rpow_natCast N i
        rw [Real.rpow_sub hN, hNi, div_pow, one_pow, mul_one_div]
      calc ((i.factorial : ℕ) : ℝ) * (8 : ℝ) ^ (i + 1) * N ^ (a - (i : ℝ))
          = (((i.factorial : ℕ) : ℝ) * (8 : ℝ) ^ (i + 1)) * (N ^ a * (1 / N) ^ i) := by
            rw [hrw, mul_assoc]
        _ ≤ Ps * (N ^ a * (1 / N) ^ i) := mul_le_mul_of_nonneg_right hile hna
        _ = (Ps * (1 / N) ^ i) * N ^ a := by ring
    have h2 : ‖iteratedDeriv (j - i) (fun w : ℝ => ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) v‖
        ≤ Ds * (1 / N) ^ (j - i) := by
      have hNi : (0 : ℝ) < N ^ (j - i) := by positivity
      have heq : Ds * (1 / N) ^ (j - i) = Ds / N ^ (j - i) := by
        rw [div_pow, one_pow, mul_one_div]
      rw [heq]
      exact (hD N hN (j - i) σ hσ hσ1 v).trans
        (div_le_div_of_nonneg_right (hDle (j - i) (by omega)) hNi.le)
    have hpowmul : (1 / N) ^ i * (1 / N) ^ (j - i) = (1 / N) ^ j := by
      rw [← pow_add]
      congr 1
      omega
    calc (j.choose i : ℝ) * ‖iteratedDeriv i (fun w : ℝ => w ^ a) v‖ *
          ‖iteratedDeriv (j - i) (fun w : ℝ => ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) v‖
        ≤ (j.choose i : ℝ) * ((Ps * (1 / N) ^ i) * N ^ a) * (Ds * (1 / N) ^ (j - i)) := by
          refine mul_le_mul (mul_le_mul le_rfl h1 (norm_nonneg _) (Nat.cast_nonneg _)) h2
            (norm_nonneg _) (by positivity)
      _ = (j.choose i : ℝ) * N ^ a * ((1 / N) ^ i * (1 / N) ^ (j - i)) * (Ps * Ds) := by ring
      _ = (j.choose i : ℝ) * N ^ a * (1 / N) ^ j * (Ps * Ds) := by rw [hpowmul]
  refine (hleib.trans (Finset.sum_le_sum hterm)).trans ?_
  have hsum2 : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * N ^ a * (1 / N) ^ j * (Ps * Ds)
      = (2 : ℝ) ^ j * N ^ a * (1 / N) ^ j * (Ps * Ds) := by
    have hch : ((∑ i ∈ Finset.range (j + 1), j.choose i : ℕ) : ℝ) = (2 : ℝ) ^ j := by
      rw [Nat.sum_range_choose]
      push_cast
      ring
    have hch' : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
      rw [← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring
    calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * N ^ a * (1 / N) ^ j * (Ps * Ds)
        = (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) *
            (N ^ a * (1 / N) ^ j * (Ps * Ds)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => by ring
      _ = (2 : ℝ) ^ j * N ^ a * (1 / N) ^ j * (Ps * Ds) := by rw [hch']; ring
  rw [hsum2]
  have h2j : (2 : ℝ) ^ j ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hstep1 : (2 : ℝ) ^ j * N ^ a * (1 / N) ^ j * (Ps * Ds)
      ≤ (Ps * Ds * 2 ^ r) * (N ^ a * (1 / N) ^ j) := by
    calc (2 : ℝ) ^ j * N ^ a * (1 / N) ^ j * (Ps * Ds)
        = 2 ^ j * (N ^ a * (1 / N) ^ j * (Ps * Ds)) := by ring
      _ ≤ 2 ^ r * (N ^ a * (1 / N) ^ j * (Ps * Ds)) :=
          mul_le_mul_of_nonneg_right h2j (by positivity)
      _ = (Ps * Ds * 2 ^ r) * (N ^ a * (1 / N) ^ j) := by ring
  refine hstep1.trans ?_
  have hK1 : (1 : ℝ) ≤ Ps * Ds * 2 ^ r + 1 := by
    have h0 : (0 : ℝ) ≤ Ps * Ds * 2 ^ r := by positivity
    linarith
  have hexp : (1 / N) ^ j ≤ ((Ps * Ds * 2 ^ r + 1) / N) ^ j := by
    have hle : (1 / N : ℝ) ≤ (Ps * Ds * 2 ^ r + 1) / N := by
      rw [div_le_div_iff_of_pos_right hN]
      linarith
    exact pow_le_pow_left₀ (by positivity) hle j
  calc (Ps * Ds * 2 ^ r) * (N ^ a * (1 / N) ^ j)
      ≤ (Ps * Ds * 2 ^ r + 1) * (N ^ a * ((Ps * Ds * 2 ^ r + 1) / N) ^ j) := by
        refine mul_le_mul (by linarith) ?_ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hexp hNa
    _ = (Ps * Ds * 2 ^ r + 1) * N ^ a * ((Ps * Ds * 2 ^ r + 1) / N) ^ j := by ring

/-- The base bound of the `v`-direction by-parts scheme: the integral of `‖A^{(k)}‖` over the
effective window grows only like `N ^ a (1/N + 1/T) ^ k`, because the kernel factor is
*integrated* (`∫‖(G_T(N-·))^{(l)}‖ = T^{-l} ∫‖G^{(l)}‖`) rather than estimated by a supremum
times the length of the window. -/
private theorem afun_integral_deriv_bound107' {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (r : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (N T a σ : ℝ), 0 < N → 1 ≤ T → 0 < σ → σ ≤ 4 / 5 →
      a ∈ Set.Ioc (-1) 1 → ∀ (k : ℕ), k ≤ r →
      (∫ v in (N / 8)..(9 * N / 5), ‖iteratedDeriv k (fun w : ℝ =>
        ((w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) * GT G T (N - w) : ℝ) : ℂ)) v‖)
        ≤ K * N ^ a * (K * (1 / N + 1 / T)) ^ k := by
  obtain ⟨Kp, hKp1, hKp⟩ := pfun_deriv_bound107' hϕ r
  set Gs : ℝ := ∑ l ∈ Finset.range (r + 1), ∫ x : ℝ, ‖iteratedDeriv l G x‖ with hGs
  have hGint0 : ∀ l : ℕ, (0 : ℝ) ≤ ∫ x : ℝ, ‖iteratedDeriv l G x‖ := fun l =>
    integral_nonneg (fun x => norm_nonneg _)
  have hGs0 : (0 : ℝ) ≤ Gs := by
    rw [hGs]
    exact Finset.sum_nonneg (fun l _ => hGint0 l)
  have hGsle : ∀ l, l ≤ r → (∫ x : ℝ, ‖iteratedDeriv l G x‖) ≤ Gs := by
    intro l hl
    rw [hGs]
    exact Finset.single_le_sum (f := fun l => ∫ x : ℝ, ‖iteratedDeriv l G x‖)
      (fun l _ => hGint0 l) (Finset.mem_range.mpr (by omega))
  have hKmain : (1 : ℝ) ≤ 2 ^ r * Kp * Gs + Kp + 1 := by
    have h0 : (0 : ℝ) ≤ 2 ^ r * Kp * Gs := by positivity
    linarith
  refine ⟨2 ^ r * Kp * Gs + Kp + 1, hKmain, ?_⟩
  intro N T a σ hN hT hσ hσ1 ha k hk
  have hT0 : (0 : ℝ) < T := by linarith
  have hab : N / 8 ≤ 9 * N / 5 := by linarith
  have hNa : (0 : ℝ) ≤ N ^ a := Real.rpow_nonneg hN.le _
  -- smoothness of the kernel factor and its derivatives
  have hκsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ => GT G T (N - w)) := by
    have hfun : (fun w : ℝ => GT G T (N - w)) = fun w : ℝ => T⁻¹ * G ((N - w) / T) := by
      funext w
      simp only [GT]
    rw [hfun]
    exact contDiff_const.mul (hG.smooth.comp ((contDiff_const.sub contDiff_id).div_const T))
  have hκcd : ∀ n : ℕ∞, ContDiff ℝ n (fun w : ℝ => GT G T (N - w)) := fun n =>
    hκsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hκcont : ∀ l : ℕ, Continuous (fun v : ℝ =>
      ‖iteratedDeriv l (fun w : ℝ => GT G T (N - w)) v‖) := fun l =>
    ((hκcd (l : ℕ∞)).continuous_iteratedDeriv l le_rfl).norm
  have hcs0 : HasCompactSupport (fun w : ℝ => GT G T (N - w)) := by
    apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (N - 2 * T) (N + 2 * T))
      isCompact_Icc
    intro x hx
    by_contra hxK
    apply hx
    refine GT_eq_zero hG.supp hT0 ?_
    simp only [Set.mem_Icc, not_and_or, not_le] at hxK
    rcases hxK with h | h
    · rw [abs_of_pos (by linarith)]
      linarith
    · rw [abs_of_neg (by linarith)]
      linarith
  have hκcs : ∀ l : ℕ, HasCompactSupport (iteratedDeriv l (fun w : ℝ => GT G T (N - w))) := by
    intro l
    induction l with
    | zero => simpa using hcs0
    | succ l ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hκInt : ∀ l : ℕ, Integrable (fun v : ℝ =>
      ‖iteratedDeriv l (fun w : ℝ => GT G T (N - w)) v‖) := fun l =>
    (hκcont l).integrable_of_hasCompactSupport ((hκcs l).norm)
  have hκbbox : ∀ l, l ≤ r → (∫ v in (N / 8)..(9 * N / 5),
      ‖iteratedDeriv l (fun w : ℝ => GT G T (N - w)) v‖) ≤ (1 / T) ^ l * Gs := by
    intro l hl
    have h1 : (∫ v in (N / 8)..(9 * N / 5),
        ‖iteratedDeriv l (fun w : ℝ => GT G T (N - w)) v‖)
        ≤ ∫ v : ℝ, ‖iteratedDeriv l (fun w : ℝ => GT G T (N - w)) v‖ := by
      rw [intervalIntegral.integral_of_le hab]
      exact setIntegral_le_integral (hκInt l) (Eventually.of_forall (fun x => norm_nonneg _))
    have h2 : (∫ v : ℝ, ‖iteratedDeriv l (fun w : ℝ => GT G T (N - w)) v‖)
        = (1 / T) ^ l * ∫ x : ℝ, ‖iteratedDeriv l G x‖ :=
      integral_norm_ker_deriv107' hG hT0 l N
    rw [h2] at h1
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left (hGsle l hl) (by positivity)
  -- the pointwise Leibniz bound on the window
  have hpt : ∀ v ∈ Set.Icc (N / 8) (9 * N / 5),
      ‖iteratedDeriv k (fun w : ℝ =>
        ((w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) * GT G T (N - w) : ℝ) : ℂ)) v‖
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (Kp * N ^ a * (Kp / N) ^ i) *
          ‖iteratedDeriv (k - i) (fun w : ℝ => GT G T (N - w)) v‖ := by
    intro v hv
    have hv0 : 0 < v := by
      have h1 : (0 : ℝ) < N / 8 := by positivity
      linarith [hv.1]
    have hvmem : v ∈ Set.Ioi (0 : ℝ) := hv0
    have hψcd : ∀ n : ℕ∞, ContDiff ℝ n (fun w : ℝ => ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) := by
      intro n
      have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ => ϕ (w * σ / N)) :=
        hϕ.smooth.comp ((contDiff_id.mul contDiff_const).div_const N)
      have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ => ϕ (w * (1 - σ) / N)) :=
        hϕ.smooth.comp ((contDiff_id.mul contDiff_const).div_const N)
      exact (h1.mul h2).of_le (WithTop.coe_le_coe.mpr le_top)
    have hcdA : ContDiffAt ℝ (k : ℕ∞)
        (fun w : ℝ => w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) * GT G T (N - w)) v := by
      have h1 : ContDiffAt ℝ (k : ℕ∞) (fun w : ℝ => w ^ a) v :=
        (contDiffAt_id.rpow_const_of_ne (ne_of_gt hv0)).of_le le_top
      exact (h1.mul ((hψcd (k : ℕ∞)).contDiffAt)).mul ((hκcd (k : ℕ∞)).contDiffAt)
    have hcast : ‖iteratedDeriv k (fun w : ℝ =>
        ((w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) * GT G T (N - w) : ℝ) : ℂ)) v‖
        ≤ ‖iteratedDeriv k (fun w : ℝ =>
          w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) * GT G T (N - w)) v‖ :=
      norm_iteratedDeriv_ofReal_le107 hcdA
    have hPcdOn : ContDiffOn ℝ (k : ℕ∞)
        (fun w : ℝ => w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N))) (Set.Ioi 0) := by
      have h1 : ContDiffOn ℝ (k : ℕ∞) (fun w : ℝ => w ^ a) (Set.Ioi 0) :=
        (contDiffOn_id.rpow_const_of_ne (fun x hx => ne_of_gt hx)).of_le le_top
      exact h1.mul ((hψcd (k : ℕ∞)).contDiffOn)
    have hleib := norm_iteratedDerivWithin_mul_le107_real (s := Set.Ioi (0 : ℝ))
      (f := fun w : ℝ => w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)))
      (g := fun w : ℝ => GT G T (N - w)) (n := k) hPcdOn (hκcd (k : ℕ∞)).contDiffOn
      (uniqueDiffOn_Ioi 0) hvmem
    have hconv : ‖iteratedDerivWithin k (fun w : ℝ =>
        w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) * GT G T (N - w)) (Set.Ioi 0) v‖
        = ‖iteratedDeriv k (fun w : ℝ =>
          w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) * GT G T (N - w)) v‖ :=
      congrArg (fun z : ℝ => ‖z‖)
        (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0) hcdA hvmem)
    rw [hconv] at hleib
    refine hcast.trans (hleib.trans (Finset.sum_le_sum ?_))
    intro i hi
    have hik : i ≤ r := by
      have := Finset.mem_range.mp hi
      omega
    have hcdP : ContDiffAt ℝ (i : ℕ∞)
        (fun w : ℝ => w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N))) v :=
      ((contDiffAt_id.rpow_const_of_ne (ne_of_gt hv0)).of_le le_top).mul
        ((hψcd (i : ℕ∞)).contDiffAt)
    have hconvP : ‖iteratedDerivWithin i
        (fun w : ℝ => w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N))) (Set.Ioi 0) v‖
        = ‖iteratedDeriv i
          (fun w : ℝ => w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N))) v‖ :=
      congrArg (fun z : ℝ => ‖z‖)
        (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0) hcdP hvmem)
    have hconvκ : ‖iteratedDerivWithin (k - i) (fun w : ℝ => GT G T (N - w)) (Set.Ioi 0) v‖
        = ‖iteratedDeriv (k - i) (fun w : ℝ => GT G T (N - w)) v‖ :=
      congrArg (fun z : ℝ => ‖z‖)
        (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
          ((hκcd ((k - i : ℕ) : ℕ∞)).contDiffAt) hvmem)
    rw [hconvP, hconvκ]
    have hPi : ‖iteratedDeriv i
        (fun w : ℝ => w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N))) v‖
        ≤ Kp * N ^ a * (Kp / N) ^ i :=
      hKp N a σ hN hσ hσ1 ha i hik v ⟨by linarith [hv.1], by linarith [hv.2]⟩
    refine mul_le_mul_of_nonneg_right (mul_le_mul le_rfl hPi (norm_nonneg _) (by positivity))
      (norm_nonneg _)
  -- integrate the pointwise bound
  have hcont1 : IntervalIntegrable (fun v : ℝ => ‖iteratedDeriv k (fun w : ℝ =>
      ((w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) * GT G T (N - w) : ℝ) : ℂ)) v‖)
      volume (N / 8) (9 * N / 5) := by
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ =>
        ((w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) * GT G T (N - w) : ℝ) : ℂ)) :=
      contDiff_afun107' hϕ hG hN hσ (⊤ : ℕ∞)
    exact (((hsm.continuous_iteratedDeriv k (WithTop.coe_le_coe.mpr le_top))).norm).intervalIntegrable
      _ _
  have hsumcont : Continuous (fun v : ℝ => ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * (Kp * N ^ a * (Kp / N) ^ i) *
        ‖iteratedDeriv (k - i) (fun w : ℝ => GT G T (N - w)) v‖) := by
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact continuous_const.mul (hκcont (k - i))
  have hmono : (∫ v in (N / 8)..(9 * N / 5), ‖iteratedDeriv k (fun w : ℝ =>
      ((w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) * GT G T (N - w) : ℝ) : ℂ)) v‖)
      ≤ ∫ v in (N / 8)..(9 * N / 5), ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * (Kp * N ^ a * (Kp / N) ^ i) *
            ‖iteratedDeriv (k - i) (fun w : ℝ => GT G T (N - w)) v‖ :=
    intervalIntegral.integral_mono_on (μ := volume) (a := N / 8) (b := 9 * N / 5) hab
      hcont1 (hsumcont.intervalIntegrable _ _) hpt
  have hsum_int : (∫ v in (N / 8)..(9 * N / 5), ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (Kp * N ^ a * (Kp / N) ^ i) *
          ‖iteratedDeriv (k - i) (fun w : ℝ => GT G T (N - w)) v‖)
      = ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (Kp * N ^ a * (Kp / N) ^ i) *
          (∫ v in (N / 8)..(9 * N / 5),
            ‖iteratedDeriv (k - i) (fun w : ℝ => GT G T (N - w)) v‖) := by
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [intervalIntegral.integral_const_mul]
    · intro i _
      exact (continuous_const.mul (hκcont (k - i))).intervalIntegrable _ _
  have hstepA : (∫ v in (N / 8)..(9 * N / 5), ‖iteratedDeriv k (fun w : ℝ =>
      ((w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) * GT G T (N - w) : ℝ) : ℂ)) v‖)
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (Kp * N ^ a * (Kp / N) ^ i) *
          (∫ v in (N / 8)..(9 * N / 5),
            ‖iteratedDeriv (k - i) (fun w : ℝ => GT G T (N - w)) v‖) :=
    hmono.trans (le_of_eq hsum_int)
  have hstepB : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (Kp * N ^ a * (Kp / N) ^ i) *
        (∫ v in (N / 8)..(9 * N / 5), ‖iteratedDeriv (k - i) (fun w : ℝ => GT G T (N - w)) v‖)
      ≤ 2 ^ k * Kp * N ^ a * Gs * (Kp * (1 / N + 1 / T)) ^ k := by
    have hterm : ∀ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (Kp * N ^ a * (Kp / N) ^ i) *
          (∫ v in (N / 8)..(9 * N / 5), ‖iteratedDeriv (k - i) (fun w : ℝ => GT G T (N - w)) v‖)
        ≤ Kp * N ^ a * Gs * ((k.choose i : ℝ) * (Kp * (1 / N + 1 / T)) ^ k) := by
      intro i hi
      have hbbox := hκbbox (k - i) (by omega)
      have h1 : (k.choose i : ℝ) * (Kp * N ^ a * (Kp / N) ^ i) *
          (∫ v in (N / 8)..(9 * N / 5), ‖iteratedDeriv (k - i) (fun w : ℝ => GT G T (N - w)) v‖)
          ≤ (k.choose i : ℝ) * (Kp * N ^ a * (Kp / N) ^ i) * ((1 / T) ^ (k - i) * Gs) :=
        mul_le_mul_of_nonneg_left hbbox (by positivity)
      have hK0 : (0 : ℝ) ≤ Kp := le_trans zero_le_one hKp1
      have hb0 : (0 : ℝ) ≤ (1 / N) := by positivity
      have hc0 : (0 : ℝ) ≤ 1 / T := by positivity
      have hbase : (Kp / N) ^ i * (1 / T) ^ (k - i) ≤ (Kp * (1 / N + 1 / T)) ^ k := by
        have hsplit : Kp * (1 / N + 1 / T) = Kp / N + Kp / T := by
          rw [mul_add]
          ring
        have hle1 : Kp / N ≤ Kp * (1 / N + 1 / T) := by
          rw [hsplit]
          have : (0 : ℝ) ≤ Kp / T := by positivity
          linarith
        have hle2 : 1 / T ≤ Kp * (1 / N + 1 / T) := by
          rw [hsplit]
          have h2 : (0 : ℝ) ≤ Kp / N := by positivity
          have h3 : (1 / T : ℝ) ≤ Kp / T := by
            rw [div_le_div_iff_of_pos_right hT0]
            linarith
          linarith
        have h1 : (Kp / N) ^ i ≤ (Kp * (1 / N + 1 / T)) ^ i :=
          pow_le_pow_left₀ (by positivity) hle1 i
        have h2 : (1 / T) ^ (k - i) ≤ (Kp * (1 / N + 1 / T)) ^ (k - i) :=
          pow_le_pow_left₀ (by positivity) hle2 (k - i)
        calc (Kp / N) ^ i * (1 / T) ^ (k - i)
            ≤ (Kp * (1 / N + 1 / T)) ^ i * (Kp * (1 / N + 1 / T)) ^ (k - i) :=
              mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = (Kp * (1 / N + 1 / T)) ^ (i + (k - i)) := by rw [← pow_add]
          _ = (Kp * (1 / N + 1 / T)) ^ k := by
              rw [show i + (k - i) = k from
                Nat.add_sub_cancel' (by have := Finset.mem_range.mp hi; omega)]
      have h2 : Kp * N ^ a * (Kp / N) ^ i * ((1 / T) ^ (k - i) * Gs)
          = Kp * N ^ a * Gs * ((Kp / N) ^ i * (1 / T) ^ (k - i)) := by ring
      calc (k.choose i : ℝ) * (Kp * N ^ a * (Kp / N) ^ i) *
            (∫ v in (N / 8)..(9 * N / 5), ‖iteratedDeriv (k - i) (fun w : ℝ => GT G T (N - w)) v‖)
          ≤ (k.choose i : ℝ) * (Kp * N ^ a * (Kp / N) ^ i) * ((1 / T) ^ (k - i) * Gs) := h1
        _ = (k.choose i : ℝ) * (Kp * N ^ a * Gs * ((Kp / N) ^ i * (1 / T) ^ (k - i))) := by ring
        _ ≤ (k.choose i : ℝ) * (Kp * N ^ a * Gs * (Kp * (1 / N + 1 / T)) ^ k) := by
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            exact mul_le_mul_of_nonneg_left hbase (by positivity)
        _ = Kp * N ^ a * Gs * ((k.choose i : ℝ) * (Kp * (1 / N + 1 / T)) ^ k) := by ring
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    have hsum2 : ∑ i ∈ Finset.range (k + 1),
        Kp * N ^ a * Gs * ((k.choose i : ℝ) * (Kp * (1 / N + 1 / T)) ^ k)
        = (Kp * N ^ a * Gs * (Kp * (1 / N + 1 / T)) ^ k) *
            ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) := by
      rw [Finset.mul_sum (s := Finset.range (k + 1))
        (f := fun i => (k.choose i : ℝ))]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hsum2]
    have hch : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = (2 : ℝ) ^ k := by
      rw [← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring
    rw [hch]
    ring
  refine hstepA.trans (hstepB.trans ?_)
  have h2k : (2 : ℝ) ^ k ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hKpLe : Kp ≤ 2 ^ r * Kp * Gs + Kp + 1 := by
    have h0 : (0 : ℝ) ≤ 2 ^ r * Kp * Gs := by positivity
    linarith
  have hC2 : 2 ^ r * Kp * Gs ≤ 2 ^ r * Kp * Gs + Kp + 1 := by
    have h0 : (0 : ℝ) ≤ Kp + 1 := by linarith
    linarith
  have hXk : (Kp * (1 / N + 1 / T)) ^ k ≤
      ((2 ^ r * Kp * Gs + Kp + 1) * (1 / N + 1 / T)) ^ k := by
    refine pow_le_pow_left₀ (by positivity) ?_ k
    exact mul_le_mul_of_nonneg_right hKpLe (by positivity)
  calc 2 ^ k * Kp * N ^ a * Gs * (Kp * (1 / N + 1 / T)) ^ k
      = (2 ^ k * Kp * Gs) * (N ^ a * (Kp * (1 / N + 1 / T)) ^ k) := by ring
    _ ≤ (2 ^ r * Kp * Gs) * (N ^ a * ((2 ^ r * Kp * Gs + Kp + 1) * (1 / N + 1 / T)) ^ k) := by
        refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · have h1 : (2 : ℝ) ^ k * Kp ≤ 2 ^ r * Kp :=
            mul_le_mul_of_nonneg_right h2k (by linarith)
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
        · exact mul_le_mul_of_nonneg_left hXk hNa
    _ ≤ (2 ^ r * Kp * Gs + Kp + 1) * N ^ a *
          ((2 ^ r * Kp * Gs + Kp + 1) * (1 / N + 1 / T)) ^ k := by
        have hZ := mul_le_mul_of_nonneg_right hC2
          (show (0 : ℝ) ≤ N ^ a *
            ((2 ^ r * Kp * Gs + Kp + 1) * (1 / N + 1 / T)) ^ k by positivity)
        calc (2 ^ r * Kp * Gs) *
              (N ^ a * ((2 ^ r * Kp * Gs + Kp + 1) * (1 / N + 1 / T)) ^ k)
            ≤ (2 ^ r * Kp * Gs + Kp + 1) *
                (N ^ a * ((2 ^ r * Kp * Gs + Kp + 1) * (1 / N + 1 / T)) ^ k) := hZ
          _ = (2 ^ r * Kp * Gs + Kp + 1) * N ^ a *
                ((2 ^ r * Kp * Gs + Kp + 1) * (1 / N + 1 / T)) ^ k := by ring


/-- A function that vanishes on a neighbourhood of a point has all its iterated derivatives zero
there — the form in which the boundary terms of the `v`-direction by-parts step disappear. -/
private theorem afun_eq_zero_lt107' {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) {N T a σ v : ℝ} (hN : 0 < N)
    (hσ : 0 < σ) (hσ1 : σ ≤ 4 / 5) (hv : v < N / 4) :
    (fun w : ℝ => ((w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) * GT G T (N - w) : ℝ) : ℂ)) v
      = 0 := by
  have harg : v * σ / N ≤ 1 / 5 := by
    apply div_le_iff₀ hN |>.mpr
    nlinarith
  have hzero : ϕ (v * σ / N) = 0 := phi_zero_le107' hϕ harg
  show ((v ^ a * (ϕ (v * σ / N) * ϕ (v * (1 - σ) / N)) * GT G T (N - v) : ℝ) : ℂ) = 0
  simp [hzero]

/-- The equal-sign amplitude vanishes on the open set `8N/5 < v` (there the cutoff pair is zero). -/
private theorem afun_eq_zero_gt107' {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) {N T a σ v : ℝ} (hN : 0 < N)
    (hσ : 0 < σ) (hσ1 : σ ≤ 4 / 5) (hv : 8 * N / 5 < v) :
    (fun w : ℝ => ((w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) * GT G T (N - w) : ℝ) : ℂ)) v
      = 0 := by
  have hzero : ϕ (v * σ / N) * ϕ (v * (1 - σ) / N) = 0 := by
    refine pair_zero_of_v_out107' hϕ hN (Or.inr ?_)
    linarith
  show ((v ^ a * (ϕ (v * σ / N) * ϕ (v * (1 - σ) / N)) * GT G T (N - v) : ℝ) : ℂ) = 0
  simp [hzero]

/-- All `v`-derivatives of the equal-sign amplitude vanish at every point of the two open sets
`v < N/4` and `8N/5 < v`: this is what makes the boundary terms at `N/8` and `9N/5` vanish. -/
private theorem ibp_L1_bound107' {A : ℝ → ℂ} {f : ℕ → ℝ → ℂ} {c : ℂ} {a b V τ M D : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hV0 : 0 ≤ V) (hV : ∀ v ∈ Set.uIcc a b, |v| ≤ V)
    (hτ : 0 < τ) (hc : ‖c‖ ≤ 1 / τ)
    (hcdef : c = -(1 - Complex.I / (τ : ℂ))⁻¹ * (-(Complex.I / (τ : ℂ))))
    (hf : ∀ r v, f (r + 1) v = c * ((v : ℂ) * deriv (f r) v))
    (hsm : ∀ r (n : ℕ∞), ContDiff ℝ n (f r)) (hf0 : f 0 = A)
    (hvan : ∀ j : ℕ, f j a = 0) (hvan' : ∀ j : ℕ, f j b = 0)
    (hM0 : 0 ≤ M) (hD0 : 0 ≤ D) (k : ℕ)
    (hbase : ∀ l, l ≤ k → (∫ v in a..b, ‖iteratedDeriv l A v‖) ≤ M * D ^ l) :
    ‖∫ v in a..b, Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) * A v‖
      ≤ 2 ^ k * ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * (V / τ) ^ i * ((k : ℝ) / τ) ^ (k - i) * (M * D ^ i) := by
  have hτne : τ ≠ 0 := hτ.ne'
  have hstep : ∀ j, j < k → ∀ v ∈ Set.uIcc a b,
      f (j + 1) v = -(1 - Complex.I / (τ : ℂ))⁻¹ *
        ((((v / τ : ℝ) : ℂ) * (-Complex.I)) * deriv (f j) v) := by
    intro j hj v hv
    rw [hf j v, hcdef]
    push_cast
    ring
  have hder : ∀ j, j ≤ k → ∀ v ∈ Set.uIcc a b, HasDerivAt (f j) (deriv (f j) v) v := by
    intro j hj v hv
    exact (((hsm j (⊤ : ℕ∞))).differentiable (by simp)).differentiableAt.hasDerivAt
  have hint : ∀ j, j < k → IntervalIntegrable (deriv (f j)) volume a b := by
    intro j hj
    have hc1 : Continuous (deriv (f j)) := by
      have h := (hsm j (1 : ℕ∞)).continuous_iteratedDeriv 1 le_rfl
      rwa [iteratedDeriv_one] at h
    exact hc1.intervalIntegrable a b
  have hiter := ibp_v_phase_iter107' (τ := τ) (a := a) (b := b) hτne ha hab k f
    (fun j => deriv (f j)) hder hstep hint (fun j _ => hvan j) (fun j _ => hvan' j)
  rw [hf0] at hiter
  have hJrec : ∀ r l, (∫ v in a..b, ‖iteratedDeriv l (f (r + 1)) v‖)
      ≤ (‖c‖ * V) * (∫ v in a..b, ‖iteratedDeriv (l + 1) (f r) v‖) +
        ((l : ℝ) / τ) * (∫ v in a..b, ‖iteratedDeriv l (f r) v‖) :=
    fun r l => iterNorm_star107 hab hV0 hτ hc hV hf
      (fun r n => hsm r n) r l
  have hstar := star_bound107'' k (‖c‖ * V) τ (by positivity) hτ
    (fun r l => ∫ v in a..b, ‖iteratedDeriv l (f r) v‖)
    (fun l => intervalIntegral.integral_nonneg hab (fun x _ => norm_nonneg _)) hJrec k 0
    (by omega)
  have hbase' : ∀ i, i ≤ k → (∫ v in a..b, ‖iteratedDeriv i (f 0) v‖) ≤ M * D ^ i := by
    intro i hi
    rw [hf0]
    exact hbase i hi
  have hsum_le : ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * (‖c‖ * V) ^ i * ((k : ℝ) / τ) ^ (k - i) *
        (∫ v in a..b, ‖iteratedDeriv i (f 0) v‖)
      ≤ ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * (V / τ) ^ i * ((k : ℝ) / τ) ^ (k - i) * (M * D ^ i) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hik : i ≤ k := by
      have := Finset.mem_range.mp hi
      omega
    have h1 : (‖c‖ * V) ^ i ≤ (V / τ) ^ i := by
      refine pow_le_pow_left₀ (by positivity) ?_ i
      calc ‖c‖ * V ≤ (1 / τ) * V := mul_le_mul_of_nonneg_right hc hV0
        _ = V / τ := by ring
    have h3 : (∫ v in a..b, ‖iteratedDeriv i (f 0) v‖) ≤ M * D ^ i := hbase' i hik
    have hb0 : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
    have hb1 : (0 : ℝ) ≤ (V / τ) ^ i := by positivity
    have hb2 : (0 : ℝ) ≤ ((k : ℝ) / τ) ^ (k - i) := by positivity
    have e1 : (k.choose i : ℝ) * (‖c‖ * V) ^ i ≤ (k.choose i : ℝ) * (V / τ) ^ i :=
      mul_le_mul_of_nonneg_left h1 hb0
    have e2 : (k.choose i : ℝ) * (‖c‖ * V) ^ i * ((k : ℝ) / τ) ^ (k - i)
        ≤ (k.choose i : ℝ) * (V / τ) ^ i * ((k : ℝ) / τ) ^ (k - i) :=
      mul_le_mul_of_nonneg_right e1 hb2
    exact mul_le_mul e2 h3
      (intervalIntegral.integral_nonneg hab (fun x _ => norm_nonneg _)) (by positivity)
  have hnorm : ‖∫ v in a..b, Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) * f k v‖
      ≤ ∫ v in a..b, ‖iteratedDeriv 0 (f k) v‖ := by
    have h1 : ‖∫ v in a..b,
        (fun v : ℝ => Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) * f k v) v‖
        ≤ ∫ v in a..b, ‖Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) * f k v‖ := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
      exact MeasureTheory.norm_integral_le_integral_norm
        (f := fun v : ℝ => Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) * f k v)
    refine h1.trans ?_
    refine le_of_eq (intervalIntegral.integral_congr fun v hv => ?_)
    rw [iteratedDeriv_zero, norm_mul]
    have hexp : ‖Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ))‖ = 1 := by
      rw [show Complex.I * ((τ * Real.log v : ℝ) : ℂ) = ((τ * Real.log v : ℝ) : ℂ) * Complex.I
        from by ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [hexp, one_mul]
  rw [hiter]
  refine hnorm.trans (hstar.trans ?_)
  simpa only [Nat.zero_add] using mul_le_mul_of_nonneg_left hsum_le (by positivity)


/-- A function that vanishes near a point has zero derivative there (the step that propagates the
vanishing of the amplitude on the open sets `v < N/4` and `8N/5 < v` to the whole by-parts
family). -/
private theorem deriv_eq_zero_of_eventually107' {f : ℝ → ℂ} {x : ℝ}
    (h : ∀ᶠ y in 𝓝 x, f y = 0) : deriv f x = 0 := by
  have hev : f =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := h
  rw [hev.deriv_eq]
  simp

/-- The constant of the by-parts step, `c = -(1-I/τ)⁻¹(-(I/τ))`, has `‖c‖ ≤ 1/τ` for `τ > 0`. -/
private theorem norm_c_ibp107' {τ : ℝ} (hτ : 0 < τ) :
    ‖-(1 - Complex.I / (τ : ℂ))⁻¹ * (-(Complex.I / (τ : ℂ)))‖ ≤ 1 / τ := by
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hinv : ‖(1 - Complex.I / (τ : ℂ))‖ = Real.sqrt (τ ^ 2 + 1) / τ := by
    have heq : (1 - Complex.I / (τ : ℂ)) = ((τ : ℂ) - Complex.I) / (τ : ℂ) := by
      field_simp
    rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
    congr 1
    have hsq : ‖((τ : ℂ) - Complex.I)‖ ^ 2 = τ ^ 2 + 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have hnn : (0 : ℝ) ≤ ‖((τ : ℂ) - Complex.I)‖ := norm_nonneg _
    calc ‖((τ : ℂ) - Complex.I)‖ = Real.sqrt (‖((τ : ℂ) - Complex.I)‖ ^ 2) :=
          (Real.sqrt_sq hnn).symm
      _ = Real.sqrt (τ ^ 2 + 1) := by rw [hsq]
  have hge : (1 : ℝ) ≤ Real.sqrt (τ ^ 2 + 1) / τ := by
    rw [le_div_iff₀ hτ, one_mul]
    have h1 : τ ≤ Real.sqrt (τ ^ 2 + 1) := by
      have h2 : Real.sqrt (τ ^ 2) ≤ Real.sqrt (τ ^ 2 + 1) :=
        Real.sqrt_le_sqrt (by linarith [sq_nonneg τ])
      rwa [Real.sqrt_sq (le_of_lt hτ)] at h2
    linarith
  have hnorm0 : (0 : ℝ) < ‖(1 - Complex.I / (τ : ℂ))‖ := by
    rw [hinv]
    exact div_pos (Real.sqrt_pos.mpr (by positivity)) hτ
  rw [norm_mul, norm_neg, norm_inv, norm_neg, norm_div, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hτ, one_div]
  rw [hinv]
  -- `(sqrt (τ²+1)/τ)⁻¹ * (1/τ) ≤ 1/τ` because the first factor is at most one
  have hle : (Real.sqrt (τ ^ 2 + 1) / τ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact hge
  calc (Real.sqrt (τ ^ 2 + 1) / τ)⁻¹ * τ⁻¹ ≤ 1 * τ⁻¹ := by
        refine mul_le_mul_of_nonneg_right hle (by positivity)
    _ = τ⁻¹ := one_mul _


/-- Collapsing the binomial sum of `ibp_L1_bound107'`: with `W = V·D + k` every term is at most
`C(k,i) · M · (W/τ)^k`, so the whole sum is `2^k · 2^k · M · (W/τ)^k`. -/
private theorem ibp_sum_collapse107' {V M D τ : ℝ} (hV0 : 0 ≤ V) (hM0 : 0 ≤ M)
    (hD0 : 0 ≤ D) (hτ : 0 < τ) (k : ℕ) :
    2 ^ k * ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (V / τ) ^ i * ((k : ℝ) / τ) ^ (k - i) * (M * D ^ i)
      ≤ (2 * 2) ^ k * (M * (((V * D + (k : ℝ)) / τ) ^ k)) := by
  have hW0 : (0 : ℝ) ≤ V * D + (k : ℝ) := by positivity
  have hWτ : (0 : ℝ) ≤ (V * D + (k : ℝ)) / τ := by positivity
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * (V / τ) ^ i * ((k : ℝ) / τ) ^ (k - i) * (M * D ^ i)
      ≤ (k.choose i : ℝ) * (M * (((V * D + (k : ℝ)) / τ) ^ k)) := by
    intro i hi
    have hik : i ≤ k := by
      have := Finset.mem_range.mp hi
      omega
    have h1 : (V / τ) ^ i * D ^ i = ((V * D) / τ) ^ i := by
      rw [← mul_pow]
      congr 1
      ring
    have h2 : ((V * D) / τ) ^ i ≤ ((V * D + (k : ℝ)) / τ) ^ i := by
      refine pow_le_pow_left₀ (by positivity) ?_ i
      rw [div_le_div_iff_of_pos_right hτ]
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have h3 : ((k : ℝ) / τ) ^ (k - i) ≤ ((V * D + (k : ℝ)) / τ) ^ (k - i) := by
      refine pow_le_pow_left₀ (by positivity) ?_ (k - i)
      rw [div_le_div_iff_of_pos_right hτ]
      have h1 : (0 : ℝ) ≤ V * D := mul_nonneg hV0 hD0
      linarith
    have h4 : ((V * D) / τ) ^ i * ((k : ℝ) / τ) ^ (k - i)
        ≤ (((V * D + (k : ℝ)) / τ) ^ i) * (((V * D + (k : ℝ)) / τ) ^ (k - i)) :=
      mul_le_mul h2 h3 (by positivity) (by positivity)
    have h5 : (((V * D + (k : ℝ)) / τ) ^ i) * (((V * D + (k : ℝ)) / τ) ^ (k - i))
        = ((V * D + (k : ℝ)) / τ) ^ k := by
      rw [← pow_add, Nat.add_sub_cancel' hik]
    have hb0 : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
    calc (k.choose i : ℝ) * (V / τ) ^ i * ((k : ℝ) / τ) ^ (k - i) * (M * D ^ i)
        = (k.choose i : ℝ) * (((V / τ) ^ i * D ^ i) * ((k : ℝ) / τ) ^ (k - i)) * M := by
          ring
      _ = (k.choose i : ℝ) * ((((V * D) / τ) ^ i) * ((k : ℝ) / τ) ^ (k - i)) * M := by
          rw [h1]
      _ ≤ (k.choose i : ℝ) * (((V * D + (k : ℝ)) / τ) ^ k) * M := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hb0) hM0
          rw [← h5]
          exact h4
      _ = (k.choose i : ℝ) * (M * (((V * D + (k : ℝ)) / τ) ^ k)) := by ring
  have hsum : ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (M * (((V * D + (k : ℝ)) / τ) ^ k))
      = (2 : ℝ) ^ k * (M * (((V * D + (k : ℝ)) / τ) ^ k)) := by
    rw [← Finset.sum_mul]
    congr 1
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    ring
  calc 2 ^ k * ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (V / τ) ^ i * ((k : ℝ) / τ) ^ (k - i) * (M * D ^ i)
      ≤ 2 ^ k * ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * (M * (((V * D + (k : ℝ)) / τ) ^ k)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _ = 2 ^ k * ((2 : ℝ) ^ k * (M * (((V * D + (k : ℝ)) / τ) ^ k))) := by rw [hsum]
    _ = (2 * 2) ^ k * (M * (((V * D + (k : ℝ)) / τ) ^ k)) := by
        rw [mul_pow]
        ring




/-- The final arithmetic step of the `v`-direction estimate: if the gain scale `VD` satisfies
`VD ≤ (18 K_b/5) (N/T)` and `k ≤ r`, then the collapsed bound is at most
`C · ((C·N)/(T τ))^k` with `C = (2·2)^r K_b (18K_b/5 + r)^r + K_b + 1`. -/
private theorem v_ibp_bound107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G) (r : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (N T a σ τ : ℝ), 0 < N → 1 ≤ T → T ≤ N → 0 < σ → σ ≤ 4 / 5 →
      a ∈ Set.Ioc (-1) 1 → 0 < τ → ∀ (k : ℕ), k ≤ r →
      ‖∫ v in (N / 8)..(9 * N / 5),
          Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) *
            ((v ^ a * (ϕ (v * σ / N) * ϕ (v * (1 - σ) / N)) * GT G T (N - v) : ℝ) : ℂ)‖
        ≤ K * N ^ a * (K * N / (T * τ)) ^ k := by
  obtain ⟨Kb, hKb1, hKb⟩ := afun_integral_deriv_bound107' hϕ hG r
  set K : ℝ := (2 * 2) ^ r * Kb * ((18 * Kb / 5 + (r : ℝ)) ^ r) + 1 with hK
  have hK1 : 1 ≤ K := by
    rw [hK]
    have h0 : (0 : ℝ) ≤ (2 * 2) ^ r * Kb * ((18 * Kb / 5 + (r : ℝ)) ^ r) := by positivity
    linarith
  refine ⟨K, hK1, ?_⟩
  intro N T a σ τ hN hT hTN hσ hσ1 ha hτ k hkr
  have hT0 : (0 : ℝ) < T := by linarith
  have hNT : (1 : ℝ) ≤ N / T := by rw [le_div_iff₀ hT0]; linarith
  have hNa : (0 : ℝ) ≤ N ^ a := Real.rpow_nonneg hN.le _
  have hKb0 : (0 : ℝ) ≤ Kb := by linarith
  set A : ℝ → ℂ := fun w =>
    ((w ^ a * (ϕ (w * σ / N) * ϕ (w * (1 - σ) / N)) * GT G T (N - w) : ℝ) : ℂ) with hA
  set c : ℂ := -(1 - Complex.I / (τ : ℂ))⁻¹ * (-(Complex.I / (τ : ℂ))) with hcdef
  set f : ℕ → ℝ → ℂ :=
    fun j => Nat.rec A (fun _ prev => fun v => c * ((v : ℂ) * deriv prev v)) j with hf
  have hfrec : ∀ (j : ℕ) (v : ℝ), f (j + 1) v = c * ((v : ℂ) * deriv (f j) v) := fun j v => rfl
  have hf0 : f 0 = A := rfl
  have hsm : ∀ j (n : ℕ∞), ContDiff ℝ n (f j) := by
    intro j
    induction j with
    | zero =>
      intro n
      rw [hf0, hA]
      exact contDiff_afun107' (T := T) (b := a) hϕ hG hN hσ n
    | succ j ih =>
      intro n
      have hd : ContDiff ℝ n (deriv (f j)) := (ih (n + 1)).deriv'
      have hfun : f (j + 1) = fun v : ℝ => c * ((v : ℂ) * deriv (f j) v) := by
        funext v
        exact hfrec j v
      rw [hfun]
      have hv : ContDiff ℝ n (fun v : ℝ => (v : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp contDiff_id
      exact contDiff_const.mul (hv.mul hd)
  have hvanish : ∀ j (v : ℝ), (v < N / 4 ∨ 8 * N / 5 < v) → f j v = 0 := by
    intro j
    induction j with
    | zero =>
      intro v hv
      rw [hf0]
      rcases hv with hv | hv
      · exact afun_eq_zero_lt107' hϕ hN hσ hσ1 hv
      · exact afun_eq_zero_gt107' hϕ hN hσ hσ1 hv
    | succ j ih =>
      intro v hv
      rw [hfrec j v]
      have hd : deriv (f j) v = 0 := by
        refine deriv_eq_zero_of_eventually107' ?_
        rcases hv with hv | hv
        · have hopen : IsOpen {y : ℝ | y < N / 4} := isOpen_lt continuous_id continuous_const
          filter_upwards [hopen.mem_nhds hv] with y hy
          exact ih y (Or.inl hy)
        · have hopen : IsOpen {y : ℝ | 8 * N / 5 < y} := isOpen_lt continuous_const continuous_id
          filter_upwards [hopen.mem_nhds hv] with y hy
          exact ih y (Or.inr hy)
      rw [hd, mul_zero, mul_zero]
  have hvanA : ∀ j : ℕ, f j (N / 8) = 0 := by
    intro j
    refine hvanish j _ (Or.inl ?_)
    linarith
  have hvanB : ∀ j : ℕ, f j (9 * N / 5) = 0 := by
    intro j
    refine hvanish j _ (Or.inr ?_)
    linarith
  have hV : ∀ v ∈ Set.uIcc (N / 8) (9 * N / 5), |v| ≤ 9 * N / 5 := by
    intro v hv
    rw [Set.uIcc_of_le (by linarith : N / 8 ≤ 9 * N / 5)] at hv
    have hv0 : 0 ≤ v := by linarith [hv.1]
    rw [abs_of_nonneg hv0]
    exact hv.2
  have hbase : ∀ l, l ≤ k → (∫ v in (N / 8)..(9 * N / 5),
      ‖iteratedDeriv l A v‖) ≤ (Kb * N ^ a) * (Kb * (1 / N + 1 / T)) ^ l := by
    intro l hl
    have h1 := hKb N T a σ hN hT hσ hσ1 ha l (le_trans hl hkr)
    simpa only [hA] using h1
  have hM0 : (0 : ℝ) ≤ Kb * N ^ a := by positivity
  have hD0 : (0 : ℝ) ≤ Kb * (1 / N + 1 / T) := by positivity
  have hmain := ibp_L1_bound107' (A := A) (f := f) (c := c) (τ := τ)
    (a := N / 8) (b := 9 * N / 5) (V := 9 * N / 5) (M := Kb * N ^ a)
    (D := Kb * (1 / N + 1 / T))
    (show (0 : ℝ) < N / 8 by positivity)
    (show N / 8 ≤ 9 * N / 5 by linarith)
    (by positivity) hV hτ (norm_c_ibp107' hτ) rfl hfrec hsm hf0 hvanA hvanB hM0 hD0 k hbase
  have hcol := ibp_sum_collapse107' (V := 9 * N / 5) (M := Kb * N ^ a)
    (D := Kb * (1 / N + 1 / T)) (τ := τ) (by positivity) hM0 hD0 hτ k
  -- (a) the gain scale
  have hVD : (9 * N / 5) * (Kb * (1 / N + 1 / T)) ≤ (18 * Kb / 5) * (N / T) := by
    have h1 : (1 / N : ℝ) ≤ 1 / T := one_div_le_one_div_of_le hT0 hTN
    have h4 : (9 * N / 5) * (1 / N) = 9 / 5 := by field_simp
    have h5 : (9 * N / 5) * (1 / T) = 9 / 5 * (N / T) := by field_simp
    have h2 : (9 * N / 5) * (1 / N + 1 / T) ≤ 18 / 5 * (N / T) := by
      rw [mul_add, h4, h5]
      nlinarith [hNT]
    calc (9 * N / 5) * (Kb * (1 / N + 1 / T)) = Kb * ((9 * N / 5) * (1 / N + 1 / T)) := by ring
      _ ≤ Kb * (18 / 5 * (N / T)) := mul_le_mul_of_nonneg_left h2 hKb0
      _ = (18 * Kb / 5) * (N / T) := by ring
  have hgain : (9 * N / 5) * (Kb * (1 / N + 1 / T)) + (k : ℝ) ≤
      (18 * Kb / 5 + (r : ℝ)) * (N / T) := by
    have hk : (k : ℝ) ≤ (r : ℝ) := by exact_mod_cast hkr
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have hkrT : (r : ℝ) ≤ (r : ℝ) * (N / T) := by
      calc (r : ℝ) = (r : ℝ) * 1 := by ring
        _ ≤ (r : ℝ) * (N / T) := mul_le_mul_of_nonneg_left hNT hr0
    nlinarith [hVD, hk, hkrT]
  have hstep : (((9 * N / 5) * (Kb * (1 / N + 1 / T)) + (k : ℝ)) / τ) ^ k
      ≤ ((18 * Kb / 5 + (r : ℝ)) * (N / (T * τ))) ^ k := by
    refine pow_le_pow_left₀ (by positivity) ?_ k
    have h2 : ((18 * Kb / 5 + (r : ℝ)) * (N / T)) / τ
        = (18 * Kb / 5 + (r : ℝ)) * (N / (T * τ)) := by
      field_simp
    rw [← h2]
    exact div_le_div_of_nonneg_right hgain hτ.le
  have hcoef : (2 * 2) ^ k * Kb * ((18 * Kb / 5 + (r : ℝ)) ^ k)
      ≤ (2 * 2) ^ r * Kb * ((18 * Kb / 5 + (r : ℝ)) ^ r) := by
    have h1 : (2 * 2 : ℝ) ^ k ≤ (2 * 2) ^ r := pow_le_pow_right₀ (by norm_num) hkr
    have hbase1 : (1 : ℝ) ≤ 18 * Kb / 5 + (r : ℝ) := by
      have h0 : (0 : ℝ) ≤ 18 * Kb / 5 := by positivity
      linarith [Nat.cast_nonneg (α := ℝ) r]
    have h2 : (18 * Kb / 5 + (r : ℝ)) ^ k ≤ (18 * Kb / 5 + (r : ℝ)) ^ r :=
      pow_le_pow_right₀ hbase1 hkr
    calc (2 * 2) ^ k * Kb * ((18 * Kb / 5 + (r : ℝ)) ^ k)
        = ((2 * 2) ^ k * Kb) * ((18 * Kb / 5 + (r : ℝ)) ^ k) := by ring
      _ ≤ ((2 * 2) ^ r * Kb) * ((18 * Kb / 5 + (r : ℝ)) ^ r) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right h1 hKb0) h2 (by positivity) ?_
          exact mul_nonneg (by positivity) hKb0
      _ = (2 * 2) ^ r * Kb * ((18 * Kb / 5 + (r : ℝ)) ^ r) := by ring
  have hC0le : (2 * 2) ^ r * Kb * ((18 * Kb / 5 + (r : ℝ)) ^ r) ≤ K := by
    rw [hK]
    linarith
  calc ‖∫ v in (N / 8)..(9 * N / 5),
        Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) *
          ((v ^ a * (ϕ (v * σ / N) * ϕ (v * (1 - σ) / N)) * GT G T (N - v) : ℝ) : ℂ)‖
      = ‖∫ v in (N / 8)..(9 * N / 5),
          Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) * A v‖ := by rw [hA]
    _ ≤ (2 * 2) ^ k * ((Kb * N ^ a) *
          ((((9 * N / 5) * (Kb * (1 / N + 1 / T)) + (k : ℝ)) / τ) ^ k)) := hmain.trans hcol
    _ ≤ (2 * 2) ^ k * ((Kb * N ^ a) *
          (((18 * Kb / 5 + (r : ℝ)) * (N / (T * τ))) ^ k)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep hM0) (by positivity)
    _ = ((2 * 2) ^ k * Kb * ((18 * Kb / 5 + (r : ℝ)) ^ k)) * N ^ a *
          ((N / (T * τ)) ^ k) := by
        have hZ : ((18 * Kb / 5 + (r : ℝ)) * (N / (T * τ))) ^ k
            = ((18 * Kb / 5 + (r : ℝ)) ^ k) * ((N / (T * τ)) ^ k) := mul_pow _ _ _
        rw [hZ]
        ring
    _ ≤ ((2 * 2) ^ r * Kb * ((18 * Kb / 5 + (r : ℝ)) ^ r)) * N ^ a *
          ((N / (T * τ)) ^ k) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hNa) (by positivity)
    _ ≤ K * N ^ a * ((N / (T * τ)) ^ k) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hNa) (by positivity)
        linarith
    _ ≤ K * N ^ a * ((K * N / (T * τ)) ^ k) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine pow_le_pow_left₀ (by positivity) ?_ k
        have h0 : (0 : ℝ) ≤ N / (T * τ) := by positivity
        have h1 : N / (T * τ) ≤ K * (N / (T * τ)) := by
          calc N / (T * τ) = 1 * (N / (T * τ)) := by ring
            _ ≤ K * (N / (T * τ)) := mul_le_mul_of_nonneg_right hK1 h0
        calc N / (T * τ) ≤ K * (N / (T * τ)) := h1
          _ = K * N / (T * τ) := by ring

/-! ## The phase sign and the inner `v`-integral of the equal-sign leaf -/

/-- For a real-valued amplitude, reversing the sign of the phase does not change the norm. -/
private theorem norm_integral_exp_phase_abs107 {F : ℝ → ℂ} (hF : ∀ v, (starRingEnd ℂ) (F v) = F v)
    (c : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    ‖∫ v in s, Complex.exp (Complex.I * ((c * Real.log v : ℝ) : ℂ)) * F v‖
      = ‖∫ v in s, Complex.exp (Complex.I * ((|c| * Real.log v : ℝ) : ℂ)) * F v‖ := by
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc]
  · rw [abs_of_nonpos hc]
    have hpt : ∀ v : ℝ, Complex.exp (Complex.I * ((-c * Real.log v : ℝ) : ℂ)) * F v
        = (starRingEnd ℂ) (Complex.exp (Complex.I * ((c * Real.log v : ℝ) : ℂ)) * F v) := by
      intro v
      have hsw : (starRingEnd ℂ) (Complex.I * ((c * Real.log v : ℝ) : ℂ))
          = Complex.I * ((-c * Real.log v : ℝ) : ℂ) := by
        rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
        push_cast
        ring
      rw [map_mul, hF v, ← Complex.exp_conj, hsw]
    have hstar : ∫ v in s, Complex.exp (Complex.I * ((-c * Real.log v : ℝ) : ℂ)) * F v
        = (starRingEnd ℂ)
            (∫ v in s, Complex.exp (Complex.I * ((c * Real.log v : ℝ) : ℂ)) * F v) := by
      rw [show (∫ v in s, Complex.exp (Complex.I * ((-c * Real.log v : ℝ) : ℂ)) * F v)
          = ∫ v in s, (starRingEnd ℂ)
              (Complex.exp (Complex.I * ((c * Real.log v : ℝ) : ℂ)) * F v) from by
        apply setIntegral_congr_fun hs
        intro v _
        exact hpt v]
      exact integral_conj (μ := volume.restrict s) (𝕜 := ℂ)
        (f := fun v : ℝ => Complex.exp (Complex.I * ((c * Real.log v : ℝ) : ℂ)) * F v)
    rw [hstar, Complex.norm_conj]

/-- The inner `v`-integral of the equal-sign leaf, in the shape of the by-parts estimate. -/
private theorem inner_v_bound107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G) (r : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (N T : ℝ) (ρ₁ ρ₂ : ℂ) (σ : ℝ), 0 < N → 1 ≤ T → T ≤ N →
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 →
      0 < σ → σ ≤ 4 / 5 → 0 < |(ρ₁ + ρ₂).im| → ∀ k : ℕ, k ≤ r →
      ‖∫ v in (N / 8)..(9 * N / 5), (v : ℂ) ^ (ρ₁ + ρ₂ - 1) * (GT G T (N - v) : ℂ) *
        (((ϕ (v * σ / N)) * (ϕ (v * (1 - σ) / N)) : ℝ) : ℂ)‖
        ≤ K * N ^ ((ρ₁ + ρ₂).re - 1) * (K * N / (T * |(ρ₁ + ρ₂).im|)) ^ k := by
  obtain ⟨K, hK1, hK⟩ := v_ibp_bound107 hϕ hG r
  refine ⟨K, hK1, ?_⟩
  intro N T ρ₁ ρ₂ σ hN hT hTN h₁ h₁' h₂ h₂' hσ hσ1 hτ k hkr
  set S : ℂ := ρ₁ + ρ₂ with hS
  set a : ℝ := S.re - 1 with ha
  have hSre : a ∈ Set.Ioc (-1) 1 := by
    constructor
    · rw [ha, hS]
      simp only [Complex.add_re]
      linarith
    · rw [ha, hS]
      simp only [Complex.add_re]
      linarith
  have htime : ∀ v ∈ Set.uIcc (N / 8) (9 * N / 5), (v : ℂ) ^ (S - 1) * (GT G T (N - v) : ℂ) *
        (((ϕ (v * σ / N)) * (ϕ (v * (1 - σ) / N)) : ℝ) : ℂ)
      = Complex.exp (Complex.I * ((S.im * Real.log v : ℝ) : ℂ)) *
        ((v ^ a * (ϕ (v * σ / N) * ϕ (v * (1 - σ) / N)) * GT G T (N - v) : ℝ) : ℂ) := by
    intro v hv
    have hv0 : 0 < v := by
      have hv' := Set.uIcc_of_le (by linarith : N / 8 ≤ 9 * N / 5) ▸ hv
      linarith [hv'.1]
    rw [cpow_split107 hv0 S, ha]
    push_cast
    ring
  have hEq : ∫ v in (N / 8)..(9 * N / 5), (v : ℂ) ^ (S - 1) * (GT G T (N - v) : ℂ) *
        (((ϕ (v * σ / N)) * (ϕ (v * (1 - σ) / N)) : ℝ) : ℂ)
      = ∫ v in (N / 8)..(9 * N / 5), Complex.exp (Complex.I * ((S.im * Real.log v : ℝ) : ℂ)) *
        ((v ^ a * (ϕ (v * σ / N) * ϕ (v * (1 - σ) / N)) * GT G T (N - v) : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro v hv
    exact htime v hv
  rw [hEq]
  have hab : N / 8 ≤ 9 * N / 5 := by linarith
  rw [intervalIntegral.integral_of_le hab]
  rw [norm_integral_exp_phase_abs107
    (F := fun v : ℝ => ((v ^ a * (ϕ (v * σ / N) * ϕ (v * (1 - σ) / N)) * GT G T (N - v) : ℝ) : ℂ))
    (fun v => Complex.conj_ofReal _) (S.im) (Set.Ioc (N / 8) (9 * N / 5)) measurableSet_Ioc]
  have hfin := hK N T a σ |S.im| hN hT hTN hσ hσ1 hSre hτ k hkr
  rw [intervalIntegral.integral_of_le hab] at hfin
  simpa only [hS, ha] using hfin

/-! ## The equal-sign leaf -/

/-- On the sigma support `[1/5, 4/5]` a complex power costs at most five. -/
private theorem cpow_norm_le_five107 {σ : ℝ} (h0 : 0 < σ) (hlo : (1 / 5 : ℝ) ≤ σ)
    (hhi : σ ≤ 4 / 5) {ρ : ℂ} (hρ : 0 < ρ.re) : ‖(σ : ℂ) ^ (ρ - 1)‖ ≤ 5 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos h0, Complex.sub_re, Complex.one_re]
  rcases le_total ρ.re 1 with hle | hle
  · have hexp : ρ.re - 1 ≤ 0 := by linarith
    have h1 : σ ^ (ρ.re - 1) ≤ (1 / 5 : ℝ) ^ (ρ.re - 1) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hlo hexp
    have h2 : (1 / 5 : ℝ) ^ (ρ.re - 1) = 5 ^ (1 - ρ.re) := by
      rw [show (1 / 5 : ℝ) = 5 ^ (-1 : ℝ) by rw [Real.rpow_neg_one]; norm_num]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
      congr 1
      ring
    have h3 : (5 : ℝ) ^ (1 - ρ.re) ≤ 5 ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_one] at h3
    linarith [h1, h2, h3]
  · have h1 : σ ^ (ρ.re - 1) ≤ (4 / 5 : ℝ) ^ (ρ.re - 1) :=
      Real.rpow_le_rpow h0.le hhi (by linarith)
    have h2 : (4 / 5 : ℝ) ^ (ρ.re - 1) ≤ 1 :=
      Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)
    linarith

/-- Factoring the joint integrand into the sigma weight and the `v`-amplitude. -/
private theorem joint107_factor {ϕ G : ℝ → ℝ} {N T : ℝ} (ρ₁ ρ₂ : ℂ) {v σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    joint107 ϕ G T N ρ₁ ρ₂ v σ
      = ((σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1)) *
          ((v : ℂ) ^ (ρ₁ + ρ₂ - 1) * (GT G T (N - v) : ℂ) *
            (((ϕ (v * σ / N)) * (ϕ (v * (1 - σ) / N)) : ℝ) : ℂ)) := by
  have h1m : (0 : ℝ) < 1 - σ := by linarith
  simp only [joint107, vexp107, amp107]
  rw [cpow_split107 hσ0 ρ₁, cpow_split107 h1m ρ₂]
  rw [show Complex.exp (Complex.I * (((ρ₁.im * Real.log σ + ρ₂.im * Real.log (1 - σ) : ℝ)) : ℂ))
      = Complex.exp (Complex.I * ((ρ₁.im * Real.log σ : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((ρ₂.im * Real.log (1 - σ) : ℝ) : ℂ)) from by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring]
  push_cast
  ring

set_option maxHeartbeats 2000000 in
private theorem same_leaf107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ N T : ℝ, 1 ≤ T → T ≤ N → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 → 0 ≤ ρ₁.im * ρ₂.im →
      ‖∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (ρ₁ + ρ₂ - 1) *
          (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂‖ ≤
        C * N ^ ((ρ₁ + ρ₂).re - 1) *
          (1 + (|ρ₁.im| + |ρ₂.im|) * T / N) ^ (-A) := by
  set r : ℕ := Nat.ceil A with hr
  have hAr : A ≤ (r : ℝ) := by
    rw [hr]
    exact_mod_cast Nat.le_ceil A
  obtain ⟨Ki, hKi1, hKi⟩ := inner_v_bound107 hϕ hG r
  obtain ⟨CJ, hCJ0, hCJ⟩ := Jphi_uniform107 hϕ
  have hKi0 : (0 : ℝ) ≤ Ki := by linarith
  have hKip : ∀ n : ℕ, (1 : ℝ) ≤ Ki ^ n := fun n => one_le_pow₀ hKi1
  set Cval : ℝ := 15 * Ki ^ (r + 1) * 2 ^ A + 15 * Ki * 2 ^ A + (5 / 2) * CJ + 1 with hCval
  have hCval0 : (0 : ℝ) ≤ Cval := by positivity
  have hterm1 : (0 : ℝ) ≤ 15 * Ki ^ (r + 1) * 2 ^ A :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hKi0 _))
      (le_of_lt (Real.rpow_pos_of_pos (by norm_num) A))
  have hterm2 : (0 : ℝ) ≤ 15 * Ki * 2 ^ A :=
    mul_nonneg (mul_nonneg (by norm_num) hKi0) (le_of_lt (Real.rpow_pos_of_pos (by norm_num) A))
  have hterm3 : (0 : ℝ) ≤ (5 / 2) * CJ := by positivity
  refine ⟨Cval, ?_⟩
  intro N T hT hTN ρ₁ ρ₂ h₁ h₁' h₂ h₂' hsign
  have hN : 0 < N := by linarith
  have hT0 : 0 < T := by linarith
  set S : ℂ := ρ₁ + ρ₂ with hS
  set a : ℝ := S.re - 1 with ha
  have hSre : S.re = ρ₁.re + ρ₂.re := by simp [hS, Complex.add_re]
  have hSre1 : 0 < S.re := by rw [hSre]; linarith
  have hSre2 : S.re ≤ 2 := by rw [hSre]; linarith
  have hUeq : |S.im| = |ρ₁.im| + |ρ₂.im| := by
    rw [hS, Complex.add_im]
    exact abs_add_of_mul_nonneg107' hsign
  set U : ℝ := |ρ₁.im| + |ρ₂.im| with hU
  have hU0 : 0 ≤ U := by positivity
  have hUT0 : (0 : ℝ) ≤ U * T / N := by positivity
  have hare : a = (ρ₁ + ρ₂).re - 1 := by rw [ha, hS]
  set F : ℝ → ℂ := fun v =>
    (v : ℂ) ^ (S - 1) * (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂ with hF
  have hNas : (0 : ℝ) ≤ N ^ (S.re - 1) := Real.rpow_nonneg hN.le _
  -- `Jphi` vanishes off the effective `v` window
  have hzero : ∀ v : ℝ, (v ≤ (2 / 5) * N ∨ (8 / 5) * N ≤ v) → F v = 0 := by
    intro v hv
    have hJ : Jphi ϕ N v ρ₁ ρ₂ = 0 := Jphi_eq_zero_outside84 hϕ hN hv ρ₁ ρ₂
    simp only [hF, hJ, mul_zero]
  rcases eq_or_lt_of_le hU0 with hUz | hUp
  · -- `U = 0`: the crude absolute bound
    have hscale : ∀ v : ℝ, 0 < v → v ^ (S.re - 1) ≤ (5 / 2) * N ^ (S.re - 1) ∨ F v = 0 := by
      intro v hv0
      by_cases hout : v ≤ (2 / 5) * N ∨ (8 / 5) * N ≤ v
      · exact Or.inr (hzero v hout)
      · push_neg at hout
        exact Or.inl (rpow_scale_bound107 hN hout.1.le hout.2.le hSre1 hSre2)
    have hpt : ∀ v ∈ Set.Ioi (0 : ℝ),
        ‖F v‖ ≤ (5 / 2) * N ^ (S.re - 1) * (CJ * GT G T (N - v)) := by
      intro v hv
      have hv0 : 0 < v := hv
      have hGT := nonneg_GT107 hG hT0 (N - v)
      rcases hscale v hv0 with hs | hFv
      · have hnorm : ‖F v‖ =
            v ^ (S.re - 1) * GT G T (N - v) * ‖Jphi ϕ N v ρ₁ ρ₂‖ := by
          rw [hF, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv0, Complex.sub_re,
            Complex.one_re, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hGT]
        rw [hnorm]
        have hJb := hCJ N hN v ρ₁ ρ₂ h₁ h₂
        have hJ0 : (0 : ℝ) ≤ ‖Jphi ϕ N v ρ₁ ρ₂‖ := norm_nonneg _
        have hs1 : v ^ (S.re - 1) * GT G T (N - v)
            ≤ (5 / 2) * N ^ (S.re - 1) * GT G T (N - v) :=
          mul_le_mul_of_nonneg_right hs hGT
        calc v ^ (S.re - 1) * GT G T (N - v) * ‖Jphi ϕ N v ρ₁ ρ₂‖
            = (v ^ (S.re - 1) * GT G T (N - v)) * ‖Jphi ϕ N v ρ₁ ρ₂‖ := by ring
          _ ≤ ((5 / 2) * N ^ (S.re - 1) * GT G T (N - v)) * CJ :=
              mul_le_mul hs1 hJb hJ0 (by positivity)
          _ = (5 / 2) * N ^ (S.re - 1) * (CJ * GT G T (N - v)) := by ring
      · rw [hFv, norm_zero]
        positivity
    have hIntble : IntegrableOn (fun v : ℝ =>
        (5 / 2) * N ^ (S.re - 1) * (CJ * GT G T (N - v))) (Set.Ioi 0) :=
      ((((integrable_GT107 hG hT0).comp_sub_left N).const_mul CJ).const_mul
        ((5 / 2) * N ^ (S.re - 1))).integrableOn
    have hgt_int : ∫ v in Set.Ioi (0 : ℝ), GT G T (N - v) ≤ 1 := by
      have hile : Integrable (fun v : ℝ => GT G T (N - v)) volume :=
        (integrable_GT107 hG hT0).comp_sub_left N
      have hle : ∫ v in Set.Ioi (0 : ℝ), GT G T (N - v) ≤ ∫ v : ℝ, GT G T (N - v) :=
        setIntegral_le_integral hile
          (Filter.Eventually.of_forall (fun v => nonneg_GT107 hG hT0 (N - v)))
      rwa [integral_sub_left_eq_self (GT G T) volume N, integral_GT107 hG hT0] at hle
    have hInt : ∫ v in Set.Ioi (0 : ℝ), (5 / 2) * N ^ (S.re - 1) * (CJ * GT G T (N - v))
        ≤ (5 / 2) * N ^ (S.re - 1) * (CJ * 1) := by
      rw [integral_const_mul, integral_const_mul]
      have hfac : (0 : ℝ) ≤ (5 / 2) * N ^ (S.re - 1) * CJ := by positivity
      nlinarith [hgt_int]
    have hdom : ∀ᵐ v ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ‖F v‖ ≤ (5 / 2) * N ^ (S.re - 1) * (CJ * GT G T (N - v)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv using hpt v hv
    have hmain := (norm_integral_le_of_norm_le
      (μ := volume.restrict (Set.Ioi (0 : ℝ))) hIntble hdom).trans hInt
    have hone : (1 + (|ρ₁.im| + |ρ₂.im|) * T / N) ^ (-A) = 1 := by
      rw [← hU, ← hUz]
      norm_num
    rw [hone, mul_one]
    have hstep2 : (5 / 2) * N ^ (S.re - 1) * (CJ * 1) ≤ Cval * N ^ ((ρ₁ + ρ₂).re - 1) := by
      rw [← hare]
      have hCJ' : (5 / 2) * CJ ≤ Cval := by
        rw [hCval]
        linarith [hterm1, hterm2]
      calc (5 / 2) * N ^ a * (CJ * 1) = ((5 / 2) * CJ) * N ^ a := by ring
        _ ≤ Cval * N ^ a := mul_le_mul_of_nonneg_right hCJ' hNas
    exact hmain.trans hstep2
  · -- `U > 0`
    have hSp : 0 < |S.im| := by rw [hUeq, hU]; exact hUp
    have hkey : ∀ k : ℕ, k ≤ r → ‖∫ v in Set.Ioi (0 : ℝ), F v‖
        ≤ 15 * (Ki * N ^ a * (Ki * N / (T * |S.im|)) ^ k) := by
      intro k hkr
      -- restrict the outer integral to the finite window
      have hind : ∫ v in Set.Ioi (0 : ℝ), F v = ∫ v in (N / 8)..(9 * N / 5), F v := by
        have h1 : (Set.Ioi (0 : ℝ)).indicator F = F := by
          funext v
          by_cases hv : v ∈ Set.Ioi (0 : ℝ)
          · rw [Set.indicator_of_mem hv]
          · rw [Set.indicator_of_notMem hv]
            refine (hzero v (Or.inl ?_)).symm
            have hle : v ≤ 0 := le_of_not_gt hv
            linarith
        have h2 : (Set.Ioc (N / 8) (9 * N / 5)).indicator F = F := by
          funext v
          by_cases hv : v ∈ Set.Ioc (N / 8) (9 * N / 5)
          · rw [Set.indicator_of_mem hv]
          · rw [Set.indicator_of_notMem hv]
            rw [Set.mem_Ioc] at hv
            rcases not_and_or.mp hv with h | h
            · refine (hzero v (Or.inl (by have := (not_lt.mp h : v ≤ N / 8); linarith))).symm
            · refine (hzero v (Or.inr (by have := (not_le.mp h : 9 * N / 5 < v); linarith))).symm
        calc ∫ v in Set.Ioi (0 : ℝ), F v = ∫ v, (Set.Ioi (0 : ℝ)).indicator F v :=
              (integral_indicator measurableSet_Ioi).symm
          _ = ∫ v, F v := by rw [h1]
          _ = ∫ v, (Set.Ioc (N / 8) (9 * N / 5)).indicator F v := by rw [h2]
          _ = ∫ v in (N / 8)..(9 * N / 5), F v := by
              rw [integral_indicator measurableSet_Ioc,
                intervalIntegral.integral_of_le (by linarith : N / 8 ≤ 9 * N / 5)]
      -- `Jphi` restricted to the sigma window
      have hJphi : ∀ v : ℝ, Jphi ϕ N v ρ₁ ρ₂ = ∫ σ in (1 / 5)..(4 / 5),
          (((ϕ (v * σ / N)) * (ϕ (v * (1 - σ) / N)) : ℝ) : ℂ) *
            (σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1) := by
        intro v
        have hg : ∀ σ : ℝ, (σ ≤ 1 / 5 ∨ 4 / 5 ≤ σ) →
            (((ϕ (v * σ / N)) * (ϕ (v * (1 - σ) / N)) : ℝ) : ℂ) *
              (σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1) = 0 := by
          intro σ hσ
          have hz : ϕ (v * σ / N) * ϕ (v * (1 - σ) / N) = 0 := by
            by_contra hne
            have hs := phi_pair_sigma_support84 hϕ hN hne
            rcases hσ with h | h
            · linarith [hs.1]
            · linarith [hs.2]
          simp only [hz, Complex.ofReal_zero, zero_mul]
        unfold Jphi
        have hA1 : ∫ σ in (0 : ℝ)..1,
            (((ϕ (v * σ / N)) * (ϕ (v * (1 - σ) / N)) : ℝ) : ℂ) *
              (σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1)
            = ∫ σ : ℝ, (((ϕ (v * σ / N)) * (ϕ (v * (1 - σ) / N)) : ℝ) : ℂ) *
              (σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1) := by
          rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
          rw [← integral_indicator measurableSet_Ioc]
          refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
          by_cases hσ : σ ∈ Set.Ioc (0 : ℝ) 1
          · rw [Set.indicator_of_mem hσ]
          · rw [Set.indicator_of_notMem hσ]
            refine (hg σ ?_).symm
            rw [Set.mem_Ioc] at hσ
            rcases not_and_or.mp hσ with h | h
            · exact Or.inl (by linarith)
            · exact Or.inr (by linarith)
        have hA2 : ∫ σ in (1 / 5)..(4 / 5),
            (((ϕ (v * σ / N)) * (ϕ (v * (1 - σ) / N)) : ℝ) : ℂ) *
              (σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1)
            = ∫ σ : ℝ, (((ϕ (v * σ / N)) * (ϕ (v * (1 - σ) / N)) : ℝ) : ℂ) *
              (σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1) := by
          rw [intervalIntegral.integral_of_le (by norm_num : (1 / 5 : ℝ) ≤ 4 / 5)]
          rw [← integral_indicator measurableSet_Ioc]
          refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
          by_cases hσ : σ ∈ Set.Ioc (1 / 5 : ℝ) (4 / 5)
          · rw [Set.indicator_of_mem hσ]
          · rw [Set.indicator_of_notMem hσ]
            refine (hg σ ?_).symm
            rw [Set.mem_Ioc] at hσ
            rcases not_and_or.mp hσ with h | h
            · exact Or.inl (by linarith)
            · exact Or.inr (by linarith)
        rw [hA1, hA2]
      -- `F` as an iterated integral of the joint integrand
      have hFv : ∀ v : ℝ, F v = ∫ σ in (1 / 5)..(4 / 5),
          joint107 ϕ G T N ρ₁ ρ₂ v σ := by
        intro v
        simp only [hF]
        rw [hJphi v]
        rw [show (v : ℂ) ^ (S - 1) * (GT G T (N - v) : ℂ) *
            (∫ σ in (1 / 5)..(4 / 5),
              (((ϕ (v * σ / N)) * (ϕ (v * (1 - σ) / N)) : ℝ) : ℂ) *
                (σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1))
            = ∫ σ in (1 / 5)..(4 / 5),
              (v : ℂ) ^ (S - 1) * (GT G T (N - v) : ℂ) *
                ((((ϕ (v * σ / N)) * (ϕ (v * (1 - σ) / N)) : ℝ) : ℂ) *
                  (σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1)) from by
          rw [intervalIntegral.integral_const_mul]]
        apply intervalIntegral.integral_congr
        intro σ hσ
        beta_reduce
        rw [Set.uIcc_of_le (by norm_num : (1 / 5 : ℝ) ≤ 4 / 5)] at hσ
        have hσ0 : 0 < σ := by linarith [hσ.1]
        have hσ1 : σ < 1 := by linarith [hσ.2]
        rw [joint107_factor ρ₁ ρ₂ hσ0 hσ1]
        rw [show ((ρ₁ + ρ₂ - 1)) = (S - 1) from by rw [hS]]
        ring
      -- the inner bound
      have hinner : ∀ σ ∈ Set.uIoc (1 / 5 : ℝ) (4 / 5),
          ‖∫ v in (N / 8)..(9 * N / 5), joint107 ϕ G T N ρ₁ ρ₂ v σ‖
            ≤ 25 * (Ki * N ^ a * (Ki * N / (T * |S.im|)) ^ k) := by
        intro σ hσ
        rw [Set.uIoc_of_le (by norm_num : (1 / 5 : ℝ) ≤ 4 / 5)] at hσ
        have hσ0 : 0 < σ := by linarith [hσ.1]
        have hσ2 : σ ≤ 4 / 5 := hσ.2
        have hσlo : (1 / 5 : ℝ) ≤ σ := by linarith [hσ.1]
        have hσ1m : 0 < 1 - σ := by linarith
        have hσ1lo : (1 / 5 : ℝ) ≤ 1 - σ := by linarith
        have hσ1hi : 1 - σ ≤ 4 / 5 := by linarith
        have hpull : ∫ v in (N / 8)..(9 * N / 5), joint107 ϕ G T N ρ₁ ρ₂ v σ
            = ((σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1)) *
              ∫ v in (N / 8)..(9 * N / 5), (v : ℂ) ^ (S - 1) * (GT G T (N - v) : ℂ) *
                (((ϕ (v * σ / N)) * (ϕ (v * (1 - σ) / N)) : ℝ) : ℂ) := by
          rw [show ∫ v in (N / 8)..(9 * N / 5), joint107 ϕ G T N ρ₁ ρ₂ v σ
              = ∫ v in (N / 8)..(9 * N / 5),
                ((σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1)) *
                  ((v : ℂ) ^ (S - 1) * (GT G T (N - v) : ℂ) *
                    (((ϕ (v * σ / N)) * (ϕ (v * (1 - σ) / N)) : ℝ) : ℂ)) from by
            apply intervalIntegral.integral_congr
            intro v hv
            beta_reduce
            rw [joint107_factor ρ₁ ρ₂ hσ0 (by linarith)]]
          rw [intervalIntegral.integral_const_mul]
        rw [hpull]
        have hc1 : ‖(σ : ℂ) ^ (ρ₁ - 1)‖ ≤ 5 := cpow_norm_le_five107 hσ0 hσlo hσ2 h₁
        have hc2 : ‖((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1)‖ ≤ 5 :=
          cpow_norm_le_five107 hσ1m hσ1lo hσ1hi h₂
        have hcb : ‖(σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1)‖ ≤ 25 := by
          rw [norm_mul]
          nlinarith [hc1, hc2, norm_nonneg ((σ : ℂ) ^ (ρ₁ - 1)),
            norm_nonneg (((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1))]
        have hib := hKi N T ρ₁ ρ₂ σ hN hT hTN h₁ h₁' h₂ h₂' hσ0 hσ2 hSp k hkr
        have hnn : (0 : ℝ) ≤ Ki * N ^ a * (Ki * N / (T * |S.im|)) ^ k := by positivity
        calc ‖((σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1)) *
              ∫ v in (N / 8)..(9 * N / 5), (v : ℂ) ^ (S - 1) * (GT G T (N - v) : ℂ) *
                (((ϕ (v * σ / N)) * (ϕ (v * (1 - σ) / N)) : ℝ) : ℂ)‖
            = ‖(σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1)‖ *
              ‖∫ v in (N / 8)..(9 * N / 5), (v : ℂ) ^ (S - 1) * (GT G T (N - v) : ℂ) *
                (((ϕ (v * σ / N)) * (ϕ (v * (1 - σ) / N)) : ℝ) : ℂ)‖ := norm_mul _ _
          _ ≤ 25 * (Ki * N ^ a * (Ki * N / (T * |S.im|)) ^ k) :=
              mul_le_mul hcb hib (norm_nonneg _) (by positivity)
      calc ‖∫ v in Set.Ioi (0 : ℝ), F v‖
          = ‖∫ v in (N / 8)..(9 * N / 5), F v‖ := by rw [hind]
        _ = ‖∫ v in (N / 8)..(9 * N / 5),
              ∫ σ in (1 / 5)..(4 / 5), joint107 ϕ G T N ρ₁ ρ₂ v σ‖ := by
            rw [intervalIntegral.integral_congr (fun v _ => hFv v)]
        _ = ‖∫ σ in (1 / 5)..(4 / 5),
              ∫ v in (N / 8)..(9 * N / 5), joint107 ϕ G T N ρ₁ ρ₂ v σ‖ := by
            rw [joint_swap107 hϕ hG (α := N / 8) (β := 9 * N / 5) (a := 1 / 5) (b := 4 / 5)
              (by positivity) (by linarith) (by norm_num) (by norm_num) (by norm_num) ρ₁ ρ₂]
        _ ≤ (25 * (Ki * N ^ a * (Ki * N / (T * |S.im|)) ^ k)) * |4 / 5 - 1 / 5| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hinner
        _ = 15 * (Ki * N ^ a * (Ki * N / (T * |S.im|)) ^ k) := by
            rw [show |(4 : ℝ) / 5 - 1 / 5| = 3 / 5 by norm_num]
            ring
    have hshape : (ρ₁ + ρ₂).re - 1 = a := by rw [ha, hS]
    rcases le_total (U * T / N) 1 with hsmall | hbig
    · -- small gain scale: `k = 0`
      have h0 := hkey 0 (Nat.zero_le r)
      rw [pow_zero, mul_one] at h0
      have hx1 : (1 : ℝ) ≤ 1 + U * T / N := by linarith
      have hone : (1 + (|ρ₁.im| + |ρ₂.im|) * T / N) ^ (-A) = (1 + U * T / N) ^ (-A) := by
        rw [← hU]
      rw [hone]
      have hxa2 : (2 : ℝ) ^ (-A) ≤ (1 + U * T / N) ^ (-A) :=
        Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < 1 + U * T / N)
          (by linarith : 1 + U * T / N ≤ 2) (by linarith : -A ≤ 0)
      have hxa2' : (0 : ℝ) ≤ (2 : ℝ) ^ (-A) := by positivity
      have hprod : (2 : ℝ) ^ A * 2 ^ (-A) = 1 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
      have hprod2 : (0 : ℝ) ≤ (2 : ℝ) ^ A := by positivity
      have hKi2 : (0 : ℝ) ≤ 15 * Ki := by positivity
      have hCge : 15 * Ki * (2 : ℝ) ^ A ≤ Cval := by
        rw [hCval]
        have h1 : (0 : ℝ) ≤ 15 * Ki ^ (r + 1) * 2 ^ A := hterm1
        have h2 : (0 : ℝ) ≤ (5 / 2) * CJ + 1 := by linarith
        linarith
      have hsmall' : 15 * (Ki * N ^ a) ≤ Cval * N ^ a * (1 + U * T / N) ^ (-A) := by
        have hc : 15 * Ki ≤ Cval * (1 + U * T / N) ^ (-A) := by
          calc 15 * Ki = 15 * Ki * ((2 : ℝ) ^ A * 2 ^ (-A)) := by rw [hprod, mul_one]
            _ = (15 * Ki * (2 : ℝ) ^ A) * 2 ^ (-A) := by ring
            _ ≤ Cval * (1 + U * T / N) ^ (-A) :=
                mul_le_mul hCge hxa2 hxa2' hCval0
        calc 15 * (Ki * N ^ a) = (15 * Ki) * N ^ a := by ring
          _ ≤ (Cval * (1 + U * T / N) ^ (-A)) * N ^ a :=
              mul_le_mul_of_nonneg_right hc hNas
          _ = Cval * N ^ a * (1 + U * T / N) ^ (-A) := by ring
      rw [← hshape]
      exact h0.trans hsmall'
    · -- large gain scale: `k = r`
      have h0 := hkey r le_rfl
      have hx1 : (1 : ℝ) ≤ U * T / N := hbig
      have hxpos : (0 : ℝ) < U * T / N := by
        have : (0 : ℝ) < U := hUp
        positivity
      have hone : (1 + (|ρ₁.im| + |ρ₂.im|) * T / N) ^ (-A) = (1 + U * T / N) ^ (-A) := by
        rw [← hU]
      rw [hone]
      have hrewrite : (Ki * N / (T * |S.im|)) ^ r = Ki ^ r * (U * T / N) ^ (-(r : ℝ)) := by
        rw [hUeq]
        have hTU : (0 : ℝ) < T * U := by positivity
        have hNr : N / (T * U) = (U * T / N)⁻¹ := by
          rw [inv_div]
          congr 1
          ring
        rw [show Ki * N / (T * U) = Ki * (N / (T * U)) by ring, mul_pow, hNr]
        rw [show ((U * T / N)⁻¹) = (U * T / N) ^ (-1 : ℝ) from (Real.rpow_neg_one _).symm]
        have hstep3 : ((U * T / N) ^ (-1 : ℝ)) ^ r = (U * T / N) ^ (-(r : ℝ)) := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul (le_of_lt hxpos)]
          congr 1
          push_cast
          ring
        rw [hstep3]
      rw [hrewrite] at h0
      have hxmono : (U * T / N) ^ (-(r : ℝ)) ≤ (U * T / N) ^ (-A) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      have hxleA : (U * T / N) ^ (-A) ≤ 2 ^ A * (1 + U * T / N) ^ (-A) := by
        have h2 : (1 + U * T / N) ≤ 2 * (U * T / N) := by linarith
        have h3 : (2 * (U * T / N)) ^ (-A) ≤ (1 + U * T / N) ^ (-A) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) h2 (by linarith)
        rw [Real.mul_rpow (by norm_num) hxpos.le] at h3
        have h4 : (2 : ℝ) ^ (-A) * 2 ^ A = 1 := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          norm_num
        have h2A : (0 : ℝ) < (2 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) _
        have h2mA : (0 : ℝ) < (2 : ℝ) ^ (-A) := Real.rpow_pos_of_pos (by norm_num) _
        have hxA : (0 : ℝ) < (U * T / N) ^ (-A) := Real.rpow_pos_of_pos hxpos _
        have : (2 : ℝ) ^ (-A) * (U * T / N) ^ (-A) ≤ (1 + U * T / N) ^ (-A) := h3
        nlinarith [this, h4, h2A, h2mA, hxA]
      have hKipos : (0 : ℝ) ≤ Ki := hKi0
      have hstep : 15 * (Ki * N ^ a * (Ki ^ r * (U * T / N) ^ (-(r : ℝ))))
          ≤ Cval * N ^ a * (1 + U * T / N) ^ (-A) := by
        have hzr : (U * T / N) ^ (-(r : ℝ)) ≤ 2 ^ A * (1 + U * T / N) ^ (-A) :=
          hxmono.trans hxleA
        have hCge : 15 * Ki ^ (r + 1) * 2 ^ A ≤ Cval := by
          rw [hCval]
          linarith [hterm2, hterm3]
        have hxp : (0 : ℝ) ≤ (1 + U * T / N) ^ (-A) :=
          le_of_lt (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < 1 + U * T / N) (-A))
        have hPa : (0 : ℝ) ≤ N ^ a := Real.rpow_nonneg hN.le _
        calc 15 * (Ki * N ^ a * (Ki ^ r * (U * T / N) ^ (-(r : ℝ))))
            = (15 * Ki ^ (r + 1)) * N ^ a * (U * T / N) ^ (-(r : ℝ)) := by
              rw [pow_succ]; ring
          _ ≤ (15 * Ki ^ (r + 1)) * N ^ a * (2 ^ A * (1 + U * T / N) ^ (-A)) := by
              exact mul_le_mul_of_nonneg_left hzr (by positivity)
          _ = (15 * Ki ^ (r + 1) * 2 ^ A) * N ^ a * (1 + U * T / N) ^ (-A) := by ring
          _ ≤ Cval * N ^ a * (1 + U * T / N) ^ (-A) := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCge hPa) (by positivity)
      rw [← hshape]
      exact h0.trans hstep

/-- LEAF. Page 29 proof of 7.19, equal signs including zero.
Repeated integration by parts in v gives decay at scale T / N. -/
theorem archimedean_same107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ N T : ℝ, 1 ≤ T → T ≤ N → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 → 0 ≤ ρ₁.im * ρ₂.im →
      ‖∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (ρ₁ + ρ₂ - 1) *
          (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂‖ ≤
        C * N ^ ((ρ₁ + ρ₂).re - 1) *
          (1 + (|ρ₁.im| + |ρ₂.im|) * T / N) ^ (-A) :=
  same_leaf107 hϕ hG A hA

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
