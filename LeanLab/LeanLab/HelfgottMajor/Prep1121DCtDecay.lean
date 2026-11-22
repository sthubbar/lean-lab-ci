import LeanLab.HelfgottMajor.Prep1121ContourShift
import LeanLab.Linnik.ExplicitFormula.ZeroSum

/-!
PREP deepening 2026-11-21, session CLAUDE-prep1121 HM-contour-p2. Pieces for four leaves of
`Prep1121ContourShift`: `contMellin_decay_strip`, `line_two_integrable`, `horizontal_tendsto`
and `zero_sum_summable`.

P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 32, the
continuation of G_δ by display 4.14, s G_δ(s) = M(-t f'(t))(s), and page 33, display 4.7, the
shift of the line of integration. The decay of G_δ on Re s ≥ 1/2 is two integrations by parts
of the Gaussian Mellin integral; the recurrence of display 4.14 carries it to -1/2 ≤ Re s.
That decay then gives the integrability on Re s = 2, the vanishing of the horizontal sides at
the good heights of `Linnik.ExplicitFormula.good_heights`, and, against the convergent sum
Σ m(ρ)/|(ρ + 1)(ρ + 2)| of `Linnik.ExplicitFormula.summable_zterm`, the convergence of the zero
sum of display 4.1. Each final result, named after its parent leaf with suffix `_of_pieces`,
has the parent's exact statement and no sorry of its own.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121DCtDecay
open Real MeasureTheory Set Filter LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123
open LeanLab.HelfgottMajor.MainLemma41Split123 LeanLab.Linnik.ExplicitFormula
open scoped Topology Interval

/-- LEAF: P0014 page 32, the Gaussian Mellin transform G_δ(s) = ∫ t^(s-1) e^(-t²/2) e(δt) dt
on the strip 1/2 ≤ Re s ≤ 5/2 decays like (1 + t²)⁻¹ in the height t, uniformly in σ: two
integrations by parts, the boundary terms vanishing for Re s above 0. MEDIUM: a public port of
the private `pcsB_mellin_decay_strip` of SPLIT_principal_contour_identity, which has exactly
this statement, through its helper `pcsB_line_constant_uniform`. -/
private theorem abs_im_le_norm_add_nat (s : ℂ) (k : ℕ) : |s.im| ≤ ‖s + (k : ℂ)‖ := by
  have him : (s + (k : ℂ)).im = s.im := by simp
  have hsq : ‖s + (k : ℂ)‖ ^ 2 = (s + (k : ℂ)).re ^ 2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, him]
    ring
  have h1 : s.im ^ 2 ≤ ‖s + (k : ℂ)‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (s + (k : ℂ)).re]
  have h2 : |s.im| ^ 2 ≤ ‖s + (k : ℂ)‖ ^ 2 := by
    rwa [sq_abs]
  simpa using (sq_le_sq.mp h2)

/-- A constant bound for the Gaussian Mellin transform on the wide strip of real parts
`[1/2, 13/2]`, uniform in the imaginary part. -/
private theorem line_const_uniform (δ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 13 / 2 →
      ‖Decomp269a.gaussianMellin δ s‖ ≤ B := by
  have hint1 : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) * Real.exp (-x ^ 2 / 2))
      (Set.Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
      (s := -(1 / 2 : ℝ)) (by norm_num)
    refine h.congr_fun ?_ measurableSet_Ioi
    intro x _
    simp only [show -(1 / 2 : ℝ) * x ^ 2 = -x ^ 2 / 2 by ring]
  have hint2 : IntegrableOn (fun x : ℝ => x ^ (11 / 2 : ℝ) * Real.exp (-x ^ 2 / 2))
      (Set.Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
      (s := (11 / 2 : ℝ)) (by linarith)
    refine h.congr_fun ?_ measurableSet_Ioi
    intro x _
    simp only [show -(1 / 2 : ℝ) * x ^ 2 = -x ^ 2 / 2 by ring]
  set g : ℝ → ℝ := fun x =>
    x ^ (-(1 / 2 : ℝ)) * Real.exp (-x ^ 2 / 2) +
      x ^ (11 / 2 : ℝ) * Real.exp (-x ^ 2 / 2) with hg
  have hsum : IntegrableOn g (Set.Ioi (0 : ℝ)) := by
    rw [hg]
    exact hint1.add hint2
  refine ⟨∫ x in Set.Ioi (0 : ℝ), g x, setIntegral_nonneg measurableSet_Ioi ?_, ?_⟩
  · intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have h1 : (0 : ℝ) ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
    have h2 : (0 : ℝ) ≤ x ^ (11 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
    have h3 : (0 : ℝ) < Real.exp (-x ^ 2 / 2) := Real.exp_pos _
    have h4 : (0 : ℝ) ≤ x ^ (-(1 / 2 : ℝ)) * Real.exp (-x ^ 2 / 2) := mul_nonneg h1 h3.le
    have h5 : (0 : ℝ) ≤ x ^ (11 / 2 : ℝ) * Real.exp (-x ^ 2 / 2) := mul_nonneg h2 h3.le
    rw [hg]
    linarith
  · intro s hs1 hs2
    refine (Gaussian269.mellin_norm_le δ s).trans ?_
    have hint : IntegrableOn (fun x : ℝ => x ^ (s.re - 1) * Real.exp (-x ^ 2 / 2))
        (Set.Ioi (0 : ℝ)) := by
      have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
        (s := s.re - 1) (by linarith)
      refine h.congr_fun ?_ measurableSet_Ioi
      intro x _
      simp only [show -(1 / 2 : ℝ) * x ^ 2 = -x ^ 2 / 2 by ring]
    refine setIntegral_mono_on hint hsum measurableSet_Ioi ?_
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hlo : (0 : ℝ) ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
    have hhi : (0 : ℝ) ≤ x ^ (11 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
    have hexp : (0 : ℝ) < Real.exp (-x ^ 2 / 2) := Real.exp_pos _
    have hkey : x ^ (s.re - 1) ≤ x ^ (-(1 / 2 : ℝ)) + x ^ (11 / 2 : ℝ) := by
      rcases le_or_gt x 1 with h1 | h1
      · have hle : x ^ (s.re - 1) ≤ x ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hx0 h1 (by linarith)
        linarith
      · have hle : x ^ (s.re - 1) ≤ x ^ (11 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
        linarith
    have hfac : x ^ (s.re - 1) * Real.exp (-x ^ 2 / 2) ≤
        (x ^ (-(1 / 2 : ℝ)) + x ^ (11 / 2 : ℝ)) * Real.exp (-x ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hkey hexp.le
    rw [hg]
    calc x ^ (s.re - 1) * Real.exp (-x ^ 2 / 2)
        ≤ (x ^ (-(1 / 2 : ℝ)) + x ^ (11 / 2 : ℝ)) * Real.exp (-x ^ 2 / 2) := hfac
      _ = x ^ (-(1 / 2 : ℝ)) * Real.exp (-x ^ 2 / 2) +
          x ^ (11 / 2 : ℝ) * Real.exp (-x ^ 2 / 2) := by ring

/-- One integration by parts in norms: the recurrence at a point of positive real part
bounds the transform by the two shifted values. -/
private theorem recurrence_norm (δ : ℝ) {s : ℂ} (hs : 0 < s.re) :
    ‖Decomp269a.gaussianMellin δ s‖ * ‖s‖ ≤
      ‖Decomp269a.gaussianMellin δ (s + 2)‖ +
        ‖(2 * π * Complex.I * δ : ℂ)‖ * ‖Decomp269a.gaussianMellin δ (s + 1)‖ := by
  have h := Continuation457.gaussian_mellin_recurrence δ s hs
  have he : ‖Decomp269a.gaussianMellin δ s‖ * ‖s‖ = ‖s * Decomp269a.gaussianMellin δ s‖ := by
    rw [norm_mul, mul_comm]
  rw [he, h]
  calc ‖Decomp269a.gaussianMellin δ (s + 2) -
        (2 * π * Complex.I * δ) * Decomp269a.gaussianMellin δ (s + 1)‖
      ≤ ‖Decomp269a.gaussianMellin δ (s + 2)‖ +
        ‖(2 * π * Complex.I * δ) * Decomp269a.gaussianMellin δ (s + 1)‖ := norm_sub_le _ _
    _ = ‖Decomp269a.gaussianMellin δ (s + 2)‖ +
        ‖(2 * π * Complex.I * δ : ℂ)‖ * ‖Decomp269a.gaussianMellin δ (s + 1)‖ := by rw [norm_mul]

/-- Two integrations by parts on the strip: the transform times the modulus times the
imaginary part is at most the uniform constant. -/
private theorem decay_step (δ : ℝ) {B c : ℝ}
    (hB : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 13 / 2 → ‖Decomp269a.gaussianMellin δ z‖ ≤ B)
    (hc : c = ‖(2 * π * Complex.I * δ : ℂ)‖) {s : ℂ}
    (hs1 : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 5 / 2) :
    ‖Decomp269a.gaussianMellin δ s‖ * ‖s‖ * |s.im| ≤ (B + c * B) * (1 + c) := by
  have hs0 : 0 < s.re := by linarith
  have hc0 : (0 : ℝ) ≤ c := by rw [hc]; exact norm_nonneg _
  have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) (hB s hs1 (by linarith))
  have hshift : ∀ k : ℕ, k ≤ 4 → ‖Decomp269a.gaussianMellin δ (s + (k : ℂ))‖ ≤ B := by
    intro k hk
    refine hB _ ?_ ?_
    · have hr : (s + (k : ℂ)).re = s.re + (k : ℝ) := by simp
      rw [hr]; linarith
    · have hr : (s + (k : ℂ)).re = s.re + (k : ℝ) := by simp
      have hk4 : (k : ℝ) ≤ 4 := by exact_mod_cast hk
      rw [hr]; linarith
  have h1 : ‖Decomp269a.gaussianMellin δ (s + 1)‖ ≤ B := by simpa using hshift 1 (by norm_num)
  have h2 : ‖Decomp269a.gaussianMellin δ (s + 2)‖ ≤ B := by simpa using hshift 2 (by norm_num)
  have h3 : ‖Decomp269a.gaussianMellin δ (s + 3)‖ ≤ B := by simpa using hshift 3 (by norm_num)
  have h4 : ‖Decomp269a.gaussianMellin δ (s + 4)‖ ≤ B := by simpa using hshift 4 (by norm_num)
  have e31 : (s + 1) + 2 = s + 3 := by ring
  have e21 : (s + 1) + 1 = s + 2 := by ring
  have e42 : (s + 2) + 2 = s + 4 := by ring
  have e32 : (s + 2) + 1 = s + 3 := by ring
  have hr1 : (0 : ℝ) < (s + 1).re := by
    have hh : (s + 1).re = s.re + 1 := by simp
    linarith
  have hr2 : (0 : ℝ) < (s + 2).re := by
    have hh : (s + 2).re = s.re + 2 := by simp
    linarith
  -- the recurrence at `s+1` and at `s+2`, with the shifts normalised
  have r1 : ‖Decomp269a.gaussianMellin δ (s + 1)‖ * ‖s + 1‖ ≤
      ‖Decomp269a.gaussianMellin δ (s + 3)‖ + c * ‖Decomp269a.gaussianMellin δ (s + 2)‖ := by
    have h := recurrence_norm δ (s := s + 1) hr1
    rw [← hc] at h
    rwa [e31, e21] at h
  have r2 : ‖Decomp269a.gaussianMellin δ (s + 2)‖ * ‖s + 2‖ ≤
      ‖Decomp269a.gaussianMellin δ (s + 4)‖ + c * ‖Decomp269a.gaussianMellin δ (s + 3)‖ := by
    have h := recurrence_norm δ (s := s + 2) hr2
    rw [← hc] at h
    rwa [e42, e32] at h
  have n1 : ‖Decomp269a.gaussianMellin δ (s + 1)‖ * |s.im| ≤ B + c * B := by
    have him : |s.im| ≤ ‖s + 1‖ := by simpa using abs_im_le_norm_add_nat s 1
    have hb : ‖Decomp269a.gaussianMellin δ (s + 1)‖ * ‖s + 1‖ ≤ B + c * B := by
      linarith [r1, mul_le_mul_of_nonneg_left h2 hc0]
    exact (mul_le_mul_of_nonneg_left him (norm_nonneg _)).trans hb
  have n2 : ‖Decomp269a.gaussianMellin δ (s + 2)‖ * |s.im| ≤ B + c * B := by
    have him : |s.im| ≤ ‖s + 2‖ := by simpa using abs_im_le_norm_add_nat s 2
    have hb : ‖Decomp269a.gaussianMellin δ (s + 2)‖ * ‖s + 2‖ ≤ B + c * B := by
      linarith [r2, mul_le_mul_of_nonneg_left h3 hc0]
    exact (mul_le_mul_of_nonneg_left him (norm_nonneg _)).trans hb
  -- the recurrence at `s`, multiplied through by the imaginary part
  have r0 : ‖Decomp269a.gaussianMellin δ s‖ * ‖s‖ ≤
      ‖Decomp269a.gaussianMellin δ (s + 2)‖ + c * ‖Decomp269a.gaussianMellin δ (s + 1)‖ := by
    have h := recurrence_norm δ (s := s) hs0
    rw [← hc] at h
    exact h
  have hmul : ‖Decomp269a.gaussianMellin δ s‖ * ‖s‖ * |s.im| ≤
      ‖Decomp269a.gaussianMellin δ (s + 2)‖ * |s.im| + c * (‖Decomp269a.gaussianMellin δ (s + 1)‖ * |s.im|) := by
    have h := mul_le_mul_of_nonneg_right r0 (abs_nonneg s.im)
    calc ‖Decomp269a.gaussianMellin δ s‖ * ‖s‖ * |s.im| ≤
        (‖Decomp269a.gaussianMellin δ (s + 2)‖ + c * ‖Decomp269a.gaussianMellin δ (s + 1)‖) * |s.im| := h
      _ = ‖Decomp269a.gaussianMellin δ (s + 2)‖ * |s.im| +
          c * (‖Decomp269a.gaussianMellin δ (s + 1)‖ * |s.im|) := by ring
  have hY : (0 : ℝ) ≤ B + c * B := by nlinarith
  calc ‖Decomp269a.gaussianMellin δ s‖ * ‖s‖ * |s.im|
      ≤ (B + c * B) + c * (B + c * B) := by
        linarith [hmul, n2, mul_le_mul_of_nonneg_left n1 hc0]
    _ = (B + c * B) * (1 + c) := by ring

/-- Quadratic decay of the Gaussian Mellin transform to the right of the critical line,
uniform on `1/2 ≤ Re s ≤ 5/2`, by two integrations by parts. -/

theorem gaussianMellin_decay_right (δ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 5 / 2 → ∀ t : ℝ,
      ‖Decomp269a.gaussianMellin δ ((σ : ℂ) + t * Complex.I)‖ ≤ K / (1 + t ^ 2) := by
  obtain ⟨B, hB0, hB⟩ := line_const_uniform δ
  set c : ℝ := ‖(2 * π * Complex.I * δ : ℂ)‖ with hc
  have hc0 : (0 : ℝ) ≤ c := by rw [hc]; exact norm_nonneg _
  have hY : (0 : ℝ) ≤ (B + c * B) * (1 + c) := by
    have : (0 : ℝ) ≤ B + c * B := by nlinarith
    have : (0 : ℝ) ≤ 1 + c := by linarith
    exact mul_nonneg ‹(0 : ℝ) ≤ B + c * B› ‹(0 : ℝ) ≤ 1 + c›
  refine ⟨2 * ((B + c * B) * (1 + c)) + 2 * B + 1, by linarith, ?_⟩
  intro σ hσ1 hσ2 t
  set s : ℂ := (σ : ℂ) + t * Complex.I with hsdef
  have hsr : s.re = σ := by rw [hsdef]; simp
  have hsi : s.im = t := by rw [hsdef]; simp
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ 2)]
  by_cases ht : 1 ≤ |t|
  · have hstep : ‖Decomp269a.gaussianMellin δ s‖ * ‖s‖ * |s.im| ≤ (B + c * B) * (1 + c) :=
      decay_step δ hB hc (s := s) (by rw [hsr]; exact hσ1) (by rw [hsr]; exact hσ2)
    have ht2 : (1 : ℝ) ≤ t ^ 2 := by
      have hs := sq_abs t
      nlinarith [abs_nonneg t]
    have hnorm : ‖Decomp269a.gaussianMellin δ s‖ * t ^ 2 ≤ (B + c * B) * (1 + c) := by
      have hle : t ^ 2 ≤ ‖s‖ * |s.im| := by
        have h1 : |s.im| ≤ ‖s‖ := by simpa using abs_im_le_norm_add_nat s 0
        have hsq : t ^ 2 = |s.im| ^ 2 := by rw [← hsi, ← sq_abs]
        rw [hsq, sq]
        exact mul_le_mul_of_nonneg_right h1 (abs_nonneg s.im)
      calc ‖Decomp269a.gaussianMellin δ s‖ * t ^ 2
          ≤ ‖Decomp269a.gaussianMellin δ s‖ * (‖s‖ * |s.im|) :=
            mul_le_mul_of_nonneg_left hle (norm_nonneg _)
        _ = ‖Decomp269a.gaussianMellin δ s‖ * ‖s‖ * |s.im| := by ring
        _ ≤ (B + c * B) * (1 + c) := hstep
    have h2le : 1 + t ^ 2 ≤ 2 * t ^ 2 := by linarith
    calc ‖Decomp269a.gaussianMellin δ s‖ * (1 + t ^ 2)
        ≤ ‖Decomp269a.gaussianMellin δ s‖ * (2 * t ^ 2) :=
          mul_le_mul_of_nonneg_left h2le (norm_nonneg _)
      _ = 2 * (‖Decomp269a.gaussianMellin δ s‖ * t ^ 2) := by ring
      _ ≤ 2 * ((B + c * B) * (1 + c)) := by linarith
      _ ≤ 2 * ((B + c * B) * (1 + c)) + 2 * B + 1 := by linarith
  · have ht1 : |t| < 1 := lt_of_not_ge ht
    have ht2 : t ^ 2 < 1 := by
      have hs := sq_abs t
      nlinarith [abs_nonneg t]
    have hBs : ‖Decomp269a.gaussianMellin δ s‖ ≤ B := by
      refine hB s ?_ ?_
      · rw [hsr]; linarith
      · rw [hsr]; linarith
    have hfac : 1 + t ^ 2 ≤ 2 := by linarith
    calc ‖Decomp269a.gaussianMellin δ s‖ * (1 + t ^ 2)
        ≤ B * (1 + t ^ 2) := mul_le_mul_of_nonneg_right hBs (by positivity)
      _ ≤ B * 2 := by nlinarith
      _ ≤ 2 * ((B + c * B) * (1 + c)) + 2 * B + 1 := by linarith

/-- PROVED, the exact statement of `Prep1121ContourShift.contMellin_decay_strip`. P0014 page
32, display 4.14: for Re s ≥ 1/2 the continuation is G_δ itself; for -1/2 ≤ Re s < 1/2 it is
(G_δ(s + 2) - 2πiδ G_δ(s + 1))/s with |s| ≥ |y| ≥ 1, as in `pcsB_cont_decay_strip`. -/
theorem contMellin_decay_strip_of_pieces (δ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ y : ℝ, 1 ≤ |y| →
      ‖contMellin δ ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ K / (1 + y ^ 2) := by
  obtain ⟨K1, hK1, hK1'⟩ := gaussianMellin_decay_right δ
  set c : ℝ := ‖(2 * π * Complex.I * δ : ℂ)‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  refine ⟨K1 + c * K1, by positivity, fun σ hσ t ht => ?_⟩
  have hden : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rcases le_or_gt (1 / 2) σ with hs | hs
  · rw [Route669.contMellin_eq_gaussianMellin δ _ (by simp; linarith)]
    refine (hK1' σ hs (by linarith [hσ.2]) t).trans ?_
    apply div_le_div_of_nonneg_right _ hden.le
    nlinarith [mul_nonneg hc0 hK1.le]
  · set s : ℂ := (σ : ℂ) + t * Complex.I with hsd
    have hsre : s.re = σ := by rw [hsd]; simp
    have hsim : s.im = t := by rw [hsd]; simp
    have hsnorm : 1 ≤ ‖s‖ := by
      have h1 : |t| ≤ ‖s‖ := by rw [← hsim]; exact Complex.abs_im_le_norm s
      linarith
    have e1 : s + 1 = ((σ + 1 : ℝ) : ℂ) + t * Complex.I := by rw [hsd]; push_cast; ring
    have e2 : s + 2 = ((σ + 2 : ℝ) : ℂ) + t * Complex.I := by rw [hsd]; push_cast; ring
    have hb1 : ‖Decomp269a.gaussianMellin δ (s + 1)‖ ≤ K1 / (1 + t ^ 2) := by
      rw [e1]; exact hK1' (σ + 1) (by linarith [hσ.1]) (by linarith) t
    have hb2 : ‖Decomp269a.gaussianMellin δ (s + 2)‖ ≤ K1 / (1 + t ^ 2) := by
      rw [e2]; exact hK1' (σ + 2) (by linarith [hσ.1]) (by linarith) t
    have hnumle : ‖Decomp269a.gaussianMellin δ (s + 2) -
        (2 * π * Complex.I * δ) * Decomp269a.gaussianMellin δ (s + 1)‖ ≤
          (K1 + c * K1) / (1 + t ^ 2) := by
      calc _ ≤ ‖Decomp269a.gaussianMellin δ (s + 2)‖ +
              ‖(2 * π * Complex.I * δ) * Decomp269a.gaussianMellin δ (s + 1)‖ := norm_sub_le _ _
        _ = ‖Decomp269a.gaussianMellin δ (s + 2)‖ +
              c * ‖Decomp269a.gaussianMellin δ (s + 1)‖ := by rw [norm_mul, hc]
        _ ≤ K1 / (1 + t ^ 2) + c * (K1 / (1 + t ^ 2)) :=
            add_le_add hb2 (mul_le_mul_of_nonneg_left hb1 hc0)
        _ = (K1 + c * K1) / (1 + t ^ 2) := by ring
    rw [Route669.contMellin_eq δ s (by rw [hsre]; linarith [hσ.1]), Contour457.continuedGaussian,
      norm_div]
    calc _ ≤ ((K1 + c * K1) / (1 + t ^ 2)) / ‖s‖ :=
          div_le_div_of_nonneg_right hnumle (norm_nonneg _)
      _ ≤ ((K1 + c * K1) / (1 + t ^ 2)) / 1 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hsnorm
      _ = _ := by ring

open scoped LSeries.notation ArithmeticFunction in
private lemma summable_vonMangoldt_div_sq :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2) := by
  have hs : (1 : ℝ) < ((2 : ℂ)).re := by norm_num
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (2 : ℂ)) hs
  refine h.norm.congr (fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hcast : ((n : ℕ) : ℂ) = ((n : ℝ) : ℂ) := by push_cast; ring
    rw [LSeries.term_of_ne_zero hn, norm_div, hcast,
      Complex.norm_cpow_eq_rpow_re_of_pos hnpos,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    norm_num

open scoped LSeries.notation ArithmeticFunction in
private lemma term_norm_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hsr : s.re = 2)
    (n : ℕ) :
    ‖LSeries.term (↗χ * ↗Λ) s n‖ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hcast : ((n : ℕ) : ℂ) = ((n : ℝ) : ℂ) := by push_cast; ring
    rw [LSeries.term_of_ne_zero hn, norm_div, hcast,
      Complex.norm_cpow_eq_rpow_re_of_pos hnpos, hsr]
    simp only [Real.rpow_two]
    have hfn : ‖(↗χ * ↗Λ) n‖ ≤ ArithmeticFunction.vonMangoldt n := by
      have h1 : ‖χ (n : ZMod q)‖ ≤ 1 := χ.norm_le_one (n : ZMod q)
      have h2 : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      have h3 : (↗χ * ↗Λ) n = χ (n : ZMod q) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) := rfl
      rw [h3, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h2]
      nlinarith
    exact div_le_div_of_nonneg_right hfn (by positivity)

open scoped LSeries.notation ArithmeticFunction in
/-- LEAF: P0014 page 32, display 4.4: on the line Re s = 2 of absolute convergence,
|L'/L(s, χ)| = |Σ χ(n) Λ(n) n^(-s)| is at most Σ Λ(n) n^(-2) = -ζ'/ζ(2), a bound uniform in
the height τ. EASY: `DirichletCharacter.LSeries_twist_vonMangoldt_eq` and the termwise norm
bound of an absolutely convergent Dirichlet series. -/
theorem logDeriv_line_two_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ,
      ‖deriv χ.LFunction ((2 : ℂ) + τ * Complex.I) / χ.LFunction ((2 : ℂ) + τ * Complex.I)‖ ≤
        B := by

  refine ⟨∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2, ?_, ?_⟩
  · refine tsum_nonneg (fun n => ?_)
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  intro τ
  set s : ℂ := (2 : ℂ) + τ * Complex.I with hsdef
  have hsr : s.re = 2 := by simp [hsdef]
  have hs : (1 : ℝ) < s.re := by rw [hsr]; norm_num
  have hLne : LSeries (↗χ) s ≠ 0 := DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs
  have hderiv : deriv χ.LFunction s = deriv (LSeries (↗χ)) s :=
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs
  have hval : χ.LFunction s = LSeries (↗χ) s := DirichletCharacter.LFunction_eq_LSeries χ hs
  have htwist : LSeries (↗χ * ↗Λ) s = -deriv (LSeries (↗χ)) s / LSeries (↗χ) s :=
    DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have hratio : deriv (LSeries (↗χ)) s / LSeries (↗χ) s = - LSeries (↗χ * ↗Λ) s := by
    rw [htwist]
    ring
  have hsumm : LSeriesSummable (↗χ * ↗Λ) s :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  have hbound : ‖LSeries (↗χ * ↗Λ) s‖ ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 := by
    have hnorm := norm_tsum_le_tsum_norm hsumm.norm
    exact hnorm.trans (Summable.tsum_le_tsum (fun n => term_norm_le q χ hsr n)
      hsumm.norm summable_vonMangoldt_div_sq)
  calc ‖deriv χ.LFunction s / χ.LFunction s‖
      = ‖deriv (LSeries (↗χ)) s / LSeries (↗χ) s‖ := by rw [hderiv, hval]
    _ = ‖- LSeries (↗χ * ↗Λ) s‖ := by rw [hratio]
    _ = ‖LSeries (↗χ * ↗Λ) s‖ := norm_neg _
    _ ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 := hbound

/-- PROVED. The integrand is continuous on the line Re s = 2: L(s, χ) is analytic and nonzero
there, Mathlib `LFunction_ne_zero_of_one_le_re`, and G_δ is holomorphic on Re s above -1
away from 0. -/
theorem line_two_continuous {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ) {x : ℝ}
    (hx : 1 ≤ x) :
    Continuous (fun τ : ℝ => contourIntegrand χ δ x ((2 : ℂ) + τ * Complex.I)) := by
  have hx0 : 0 < x := by linarith
  refine continuous_iff_continuousAt.mpr fun τ => ?_
  set s : ℂ := (2 : ℂ) + τ * Complex.I with hsd
  have hsre : s.re = 2 := by rw [hsd]; simp
  have hs1 : s ≠ 1 := by intro h; have := congrArg Complex.re h; rw [hsre] at this; norm_num at this
  have hs0 : s ≠ 0 := by intro h; have := congrArg Complex.re h; rw [hsre] at this; norm_num at this
  have hA := analyticAt_LFunction χ (s := s) (Or.inl hs1)
  have hL : χ.LFunction s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) (by rw [hsre]; norm_num)
  have hd : DifferentiableAt ℂ (contourIntegrand χ δ x) s := by
    have := ((hA.deriv.differentiableAt.div hA.differentiableAt hL).mul
      (Route669.contMellin_differentiableAt δ s (by rw [hsre]; norm_num) hs0)).mul
      (differentiableAt_id.const_cpow (c := (x : ℂ)) (Or.inl (by exact_mod_cast hx0.ne')))
    exact this
  exact ContinuousAt.comp (f := fun τ : ℝ => (2 : ℂ) + τ * Complex.I) hd.continuousAt
    (by fun_prop)

/-- PROVED, the exact statement of `Prep1121ContourShift.line_two_integrable`. P0014 page 32,
display 4.4: |F(2 + iτ)| ≤ B |G_δ(2 + iτ)| x², and G_δ decays like (1 + τ²)⁻¹ there. -/
theorem line_two_integrable_of_pieces {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ)
    {x : ℝ} (hx : 1 ≤ x) :
    Integrable (fun τ : ℝ => contourIntegrand χ δ x ((2 : ℂ) + τ * Complex.I)) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨B, hB0, hB⟩ := logDeriv_line_two_bound χ
  obtain ⟨K, hK, hKd⟩ := gaussianMellin_decay_right δ
  refine Integrable.mono' (g := fun τ : ℝ => (B * K * x ^ 2) * (1 + τ ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul _) (line_two_continuous χ δ hx).aestronglyMeasurable ?_
  filter_upwards with τ
  have hG : ‖contMellin δ ((2 : ℂ) + τ * Complex.I)‖ ≤ K / (1 + τ ^ 2) := by
    rw [Route669.contMellin_eq_gaussianMellin δ _ (by simp)]
    have := hKd 2 (by norm_num) (by norm_num) τ
    simpa using this
  have hpow : ‖(x : ℂ) ^ ((2 : ℂ) + τ * Complex.I)‖ = x ^ 2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp
  rw [contourIntegrand, norm_mul, norm_mul, hpow]
  have h1 := hB τ
  calc _ ≤ B * (K / (1 + τ ^ 2)) * x ^ 2 := by
        gcongr
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- PROVED. P0014 page 33, display 4.7: one horizontal side at height y with |y| ≥ 1. If
|L'/L| ≤ B on the segment and |G_δ| ≤ K/(1 + y²) there, then, with |x^s| ≤ x², the side
integral is at most (5/2) B K x²/(1 + y²), as `pcsB_horiz_bound` for ζ. -/
theorem horiz_side_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ) {x : ℝ}
    (hx : 1 ≤ x) {K B y : ℝ} (hK : 0 < K) (hB0 : 0 ≤ B) (hy : 1 ≤ |y|)
    (hdec : ∀ σ ∈ Icc (-1 / 2 : ℝ) 2,
      ‖contMellin δ ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ K / (1 + y ^ 2))
    (hB : ∀ σ ∈ Icc (-1 / 2 : ℝ) 2,
      ‖deriv χ.LFunction (σ + y * Complex.I) / χ.LFunction (σ + y * Complex.I)‖ ≤ B) :
    ‖∫ σ in (-1 / 2 : ℝ)..2, contourIntegrand χ δ x ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      5 / 2 * (B * K * x ^ 2 / (1 + y ^ 2)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hden : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have hb : ∀ σ ∈ Ι (-1 / 2 : ℝ) 2,
      ‖contourIntegrand χ δ x ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ B * K * x ^ 2 / (1 + y ^ 2) := by
    intro σ hσ
    rw [uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 2)] at hσ
    have hσ' : σ ∈ Icc (-1 / 2 : ℝ) 2 := ⟨hσ.1.le, hσ.2⟩
    have hpow : ‖(x : ℂ) ^ ((σ : ℂ) + (y : ℂ) * Complex.I)‖ = x ^ σ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp
    have hpowle : x ^ σ ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hσ'.2
    rw [Real.rpow_two] at hpowle
    rw [contourIntegrand, norm_mul, norm_mul, hpow]
    have h1 := hB σ hσ'
    have h2 := hdec σ hσ'
    calc _ ≤ B * (K / (1 + y ^ 2)) * x ^ 2 := by
          gcongr
      _ = _ := by ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have hlen : |(2 : ℝ) - (-1 / 2)| = 5 / 2 := by norm_num
  rw [hlen] at hint
  linarith

/-- PROVED. P0014 page 33, display 4.7, the size of the horizontal sides: with T = max n 5 and
Y n in [T, T + 1], log²(T + 2)/(1 + (Y n)²) tends to 0: log(T + 2)/T → 0 from
`isLittleO_log_rpow_atTop`, and 1 + (Y n)² ≥ T². -/
theorem log_sq_ratio_tendsto (Y : ℕ → ℝ)
    (hYI : ∀ n : ℕ, Y n ∈ Icc (max (n : ℝ) 5) (max (n : ℝ) 5 + 1)) :
    Tendsto (fun n : ℕ => Real.log (max (n : ℝ) 5 + 2) ^ 2 / (1 + Y n ^ 2)) atTop (𝓝 0) := by
  have hlogdiv : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
    simpa [Real.rpow_one] using
      (isLittleO_log_rpow_atTop (r := 1) one_pos).tendsto_div_nhds_zero
  have hT : Tendsto (fun n : ℕ => max (n : ℝ) 5 + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2
      (tendsto_atTop_mono (fun n => le_max_left _ _) tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun n : ℕ =>
      4 * (Real.log (max (n : ℝ) 5 + 2) / (max (n : ℝ) 5 + 2)) ^ 2) atTop (𝓝 0) := by
    simpa using ((hlogdiv.comp hT).pow 2).const_mul 4
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hlim
  have h5 : (5 : ℝ) ≤ max (n : ℝ) 5 := le_max_right _ _
  have hY := hYI n
  set T := max (n : ℝ) 5
  set L := Real.log (T + 2)
  have hTY : T ^ 2 ≤ 1 + Y n ^ 2 := by nlinarith [hY.1]
  have hT0 : (0 : ℝ) < T ^ 2 := by positivity
  calc L ^ 2 / (1 + Y n ^ 2) ≤ L ^ 2 / T ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg _) hT0 hTY
    _ ≤ 4 * (L / (T + 2)) ^ 2 := by
        rw [div_pow, div_le_iff₀ hT0,
          show 4 * (L ^ 2 / (T + 2) ^ 2) * T ^ 2 = L ^ 2 * (4 * T ^ 2 / (T + 2) ^ 2) by ring]
        refine le_mul_of_one_le_right (sq_nonneg _) ?_
        rw [le_div_iff₀ (by positivity)]
        nlinarith

/-- PROVED, the exact statement of `Prep1121ContourShift.horizontal_tendsto`. P0014 page 33,
display 4.7: both horizontal sides are at most (5/2) C K x² log²(T + 2)/(1 + (Y n)²) by
`horiz_side_bound`, which tends to 0 by `log_sq_ratio_tendsto`. -/
theorem horizontal_tendsto_of_pieces {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ)
    {x : ℝ} (hx : 1 ≤ x)
    (hdec : ∃ K : ℝ, 0 < K ∧ ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ y : ℝ, 1 ≤ |y| →
      ‖contMellin δ ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ K / (1 + y ^ 2))
    {C : ℝ} (hC : 0 ≤ C) (Y : ℕ → ℝ)
    (hYI : ∀ n : ℕ, Y n ∈ Icc (max (n : ℝ) 5) (max (n : ℝ) 5 + 1))
    (hB : ∀ n : ℕ, ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ τ ∈ ({Y n, -Y n} : Set ℝ),
      ‖deriv χ.LFunction (σ + τ * Complex.I) / χ.LFunction (σ + τ * Complex.I)‖ ≤
        C * Real.log (max (n : ℝ) 5 + 2) ^ 2) :
    Tendsto (fun n : ℕ => ∫ σ in (-1 / 2 : ℝ)..2,
        contourIntegrand χ δ x ((σ : ℂ) + (Y n : ℂ) * Complex.I)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫ σ in (-1 / 2 : ℝ)..2,
        contourIntegrand χ δ x ((σ : ℂ) + ((-Y n : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) := by
  obtain ⟨K, hK, hKd⟩ := hdec
  have hY1 : ∀ n : ℕ, 1 ≤ |Y n| := fun n => by
    have h5 : (5 : ℝ) ≤ max (n : ℝ) 5 := le_max_right _ _
    have := (hYI n).1
    rw [abs_of_nonneg (by linarith)]; linarith
  have hlim := (log_sq_ratio_tendsto Y hYI).const_mul (5 / 2 * (C * K * x ^ 2))
  rw [mul_zero] at hlim
  have hbound : ∀ n : ℕ, ∀ y : ℝ, y ^ 2 = Y n ^ 2 → 1 ≤ |y| →
      (∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ‖deriv χ.LFunction (σ + y * Complex.I) /
        χ.LFunction (σ + y * Complex.I)‖ ≤ C * Real.log (max (n : ℝ) 5 + 2) ^ 2) →
      ‖∫ σ in (-1 / 2 : ℝ)..2, contourIntegrand χ δ x ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        5 / 2 * (C * K * x ^ 2) *
          (Real.log (max (n : ℝ) 5 + 2) ^ 2 / (1 + Y n ^ 2)) := by
    intro n y hy2 hy hBy
    have h := horiz_side_bound χ δ hx hK (mul_nonneg hC (sq_nonneg _)) hy
      (fun σ hσ => hKd σ hσ y hy) hBy
    rw [hy2] at h
    refine h.trans (le_of_eq ?_)
    ring
  constructor
  · refine squeeze_zero_norm (fun n => hbound n (Y n) rfl (hY1 n)
      (fun σ hσ => hB n σ hσ (Y n) (by simp))) hlim
  · refine squeeze_zero_norm (fun n => hbound n (-Y n) (by ring) (by rw [abs_neg]; exact hY1 n)
      (fun σ hσ => hB n σ hσ (-Y n) (by simp))) hlim

/-- PROVED. P0014 page 31, display 4.1: for a zero ρ with 0 < Re ρ < 1 and |Im ρ| ≥ 1, the
zero term m(ρ) G_δ(ρ) x^ρ is at most 12 K times m(ρ) |x^ρ| / |(ρ + 1)(ρ + 2)|, the norm of
the Linnik zero term `zterm`, since |(ρ + 1)(ρ + 2)| ≤ 12 (1 + Im ρ²). -/
theorem zeroTerm_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ x : ℝ) {K : ℝ}
    (hK : 0 < K)
    (hKd : ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ y : ℝ, 1 ≤ |y| →
      ‖contMellin δ ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ K / (1 + y ^ 2))
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him : 1 ≤ |ρ.im|) :
    ‖zeroTerm χ δ x ρ‖ ≤ 12 * K * ‖zterm χ x ρ‖ := by
  have hρ : ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I := (Complex.re_add_im ρ).symm
  have hG : ‖gaussianMellin δ ρ‖ ≤ K / (1 + ρ.im ^ 2) := by
    rw [show gaussianMellin δ ρ = contMellin δ ρ from (Route669.contMellin_eq_gaussianMellin δ ρ h0).symm]
    have := hKd ρ.re ⟨by linarith, by linarith⟩ ρ.im him
    rwa [← hρ] at this
  have hn1 : ‖ρ + 1‖ ≤ 3 * |ρ.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero]
    rw [abs_of_pos (by linarith)]; linarith
  have hn2 : ‖ρ + 2‖ ≤ 4 * |ρ.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have h2re : (ρ + 2).re = ρ.re + 2 := by simp
    have h2im : (ρ + 2).im = ρ.im := by simp
    rw [h2re, h2im, abs_of_pos (by linarith)]; linarith
  have hP : ‖(ρ + 1) * (ρ + 2)‖ ≤ 12 * (1 + ρ.im ^ 2) := by
    rw [norm_mul]
    have hsq : |ρ.im| ^ 2 = ρ.im ^ 2 := sq_abs _
    nlinarith [norm_nonneg (ρ + 1), norm_nonneg (ρ + 2), abs_nonneg ρ.im]
  have hPpos : 0 < ‖(ρ + 1) * (ρ + 2)‖ := by
    rw [norm_pos_iff]
    refine mul_ne_zero ?_ ?_ <;> intro h <;> have := congrArg Complex.re h <;> simp at this <;>
      linarith
  have hden : (0 : ℝ) < 1 + ρ.im ^ 2 := by positivity
  have hGle : ‖gaussianMellin δ ρ‖ ≤ 12 * K / ‖(ρ + 1) * (ρ + 2)‖ := by
    refine hG.trans ?_
    rw [div_le_div_iff₀ hden hPpos]
    nlinarith
  simp only [zeroTerm, zterm, mult, nsmul_eq_mul, norm_mul, norm_div, Complex.norm_natCast]
  have hn : (0 : ℝ) ≤ (analyticOrderNatAt χ.LFunction ρ : ℝ) := Nat.cast_nonneg _
  have hxp : 0 ≤ ‖(x : ℂ) ^ ρ‖ := norm_nonneg _
  calc (analyticOrderNatAt χ.LFunction ρ : ℝ) * (‖gaussianMellin δ ρ‖ * ‖(x : ℂ) ^ ρ‖)
      ≤ (analyticOrderNatAt χ.LFunction ρ : ℝ) *
          (12 * K / ‖(ρ + 1) * (ρ + 2)‖ * ‖(x : ℂ) ^ ρ‖) := by gcongr
    _ = _ := by rw [norm_mul] at hPpos ⊢; field_simp

/-- PROVED, the exact statement of `Prep1121ContourShift.zero_sum_summable`. P0014 page 31,
display 4.1: the zeros with |Im ρ| < 1 are finitely many, `zeros_rect_finite`, and the other
terms are at most 12 K |zterm|, summable by `Linnik.ExplicitFormula.summable_zterm`. -/
theorem zero_sum_summable_of_pieces {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1} => zeroTerm χ δ x ρ.val) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨K, hK, hKd⟩ := contMellin_decay_strip_of_pieces δ
  let ι := {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}
  let i : ι → Zall χ := fun ρ => ⟨ρ.val, ρ.2.1, by linarith [ρ.2.2.1],
    by intro h; have := ρ.2.2.2; rw [h] at this; simp at this⟩
  have hi : Function.Injective i := by
    intro a b h
    have h2 : (i a).val = (i b).val := congrArg Subtype.val h
    exact Subtype.ext h2
  have hs : Summable (fun ρ : Zall χ => ‖zterm χ x ρ‖) :=
    summable_norm_iff.mpr (summable_zterm hχ hx0)
  have hg : Summable (fun ρ : ι => 12 * K * ‖zterm χ x ρ.val‖) :=
    (hs.comp_injective hi).mul_left (12 * K)
  refine Summable.of_norm_bounded_eventually hg ?_
  have hfin : {ρ : ι | ¬ ‖zeroTerm χ δ x ρ.val‖ ≤ 12 * K * ‖zterm χ x ρ.val‖}.Finite := by
    refine ((zeros_rect_finite hχ 1).preimage (f := fun ρ : ι => ρ.val)
      (Subtype.val_injective.injOn)).subset ?_
    intro ρ hρ
    simp only [Set.mem_setOf_eq] at hρ ⊢
    refine ⟨⟨ρ.2.1, by linarith [ρ.2.2.1], ?_⟩, ?_⟩
    · intro h; simp only at h; have h2 := ρ.2.2.2; rw [h] at h2; simp at h2
    · by_contra hlt
      exact hρ (zeroTerm_norm_le χ δ x hK hKd ρ.2.2.1 ρ.2.2.2 (by linarith [not_le.mp hlt]))
  exact Filter.eventually_cofinite.mpr hfin

end LeanLab.HelfgottMajor.Prep1121DCtDecay

#print axioms LeanLab.HelfgottMajor.Prep1121DCtDecay.contMellin_decay_strip_of_pieces
#print axioms LeanLab.HelfgottMajor.Prep1121DCtDecay.line_two_continuous
#print axioms LeanLab.HelfgottMajor.Prep1121DCtDecay.line_two_integrable_of_pieces
#print axioms LeanLab.HelfgottMajor.Prep1121DCtDecay.horiz_side_bound
#print axioms LeanLab.HelfgottMajor.Prep1121DCtDecay.log_sq_ratio_tendsto
#print axioms LeanLab.HelfgottMajor.Prep1121DCtDecay.horizontal_tendsto_of_pieces
#print axioms LeanLab.HelfgottMajor.Prep1121DCtDecay.zeroTerm_norm_le
#print axioms LeanLab.HelfgottMajor.Prep1121DCtDecay.zero_sum_summable_of_pieces
