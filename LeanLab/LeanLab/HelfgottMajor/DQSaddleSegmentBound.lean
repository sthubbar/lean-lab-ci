/-
CITED WALL, session CLOUD-cited-saddle_segment_bound, 2026-11-20.
Target: `Decomp639Contour.saddle_segment_bound`, P0014 page 23, displays 3.56 and 3.57.

DECISION: FORMALIZE. The leaf is not a result cited from elsewhere: it is Helfgott's own
argument of Section 3.7, pages 18 to 23. Its only outside inputs are the rigorous numerical
bounds of Appendix A, displays A.2, A.14, A.29 and A.32. `DQ6Decisions.lean` already holds
the whole bound as the named hypothesis `SaddleSegmentBoundDQ6`. This file splits the proof
into six steps, each tied to a page and display, and assembles the exact sealed
statement from them with no further sorry. Four steps are LEAF lemmas; the two radius
facts, displays 3.50 and 3.53, are PROVED. The Gaussian half line integral, the splitting
of the contour at the saddle radius, the power bounds of display 3.48 and every constant of
display 3.57 are PROVED below. The leaves were tested numerically, see
notes/burst-20261120/saddle_segment_bound.md.

Source: https://arxiv.org/abs/1305.2897, the copy papers/P0014.pdf.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottMajor.Decomp639Contour

namespace LeanLab.HelfgottMajor.DQSaddleSegmentBound
open Real MeasureTheory Set Decomp511a Decomp639Contour

/-- The saddle radius r0 = |u0,+| of P0014 page 17, display 3.32:
r0 = ell / sqrt 2 * sqrt (ups rho ^ 2 - ups rho). -/
noncomputable def saddleRadius (δ τ : ℝ) : ℝ :=
  ell δ / sqrt 2 * sqrt (BookE.ups (rho δ τ) ^ 2 - BookE.ups (rho δ τ))

/-- The curvature eta of P0014 page 21, display 3.46, with j rho = sqrt (1 + rho ^ 2) as in
display A.15 and Upsilon as in display 3.25. -/
noncomputable def eta (ρ : ℝ) : ℝ :=
  1 / 2 * sqrt (2 * sqrt (1 + ρ ^ 2) / (BookE.ups ρ ^ 2 - BookE.ups ρ)) *
      (1 + upsilon ρ ^ 2) - upsilon ρ ^ 2 / 2 + 1 / 2 - 1 / (2 * BookE.ups ρ) -
    ρ / (sqrt (1 + ρ ^ 2) + 1) * upsilon ρ

/-! ## The six steps: four LEAF lemmas and two proved radius facts -/

/-- LEAF: P0014 pages 18 to 21, displays 3.37, 3.39, 3.42 to 3.46, and the value of
exp of minus Re phi at u0,+ after display 3.47. On the limacon C2 the kernel is at most
r ^ (sigma - 1) times exp of minus E rho times the height times the Gaussian factor
exp of minus eta times (r - r0) ^ 2, the form eta ell^2 rho^2 nu^2 with nu = (r - r0) / (ell rho)
of display 3.38. The phase lower bound of display 3.44 is the content. -/
theorem phase_lower_bound (δ : ℝ) (s : ℂ) (hsign : δ * s.im < 0) (r : ℝ)
    (hr : r ∈ Icc (initialRadius δ s.im) (realEndpoint δ s.im)) :
    ‖contourKernel δ s (saddlePath δ s.im r)‖ ≤
      r ^ (s.re - 1) * exp (-BookE.E (rho δ s.im) * |s.im|) *
        exp (-eta (rho δ s.im) * (r - saddleRadius δ s.im) ^ 2) := by
  sorry

/-- LEAF: P0014 page 22, the arc length bound after display 3.48, from display 3.35 and the
choice theta minus = pi / 4 of display 3.55: |du/dr| is at most sqrt (1 + 2 c0 ^ 2). -/
theorem arc_length_bound (δ τ r : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|)
    (hr : r ∈ Icc (initialRadius δ τ) (realEndpoint δ τ)) :
    ‖deriv (saddlePath δ τ) r‖ ≤ sqrt (1 + 2 * c0 (rho δ τ) ^ 2) := by
  sorry

/-- P0014 page 18, displays 3.33 and 3.34, with page 20: c1 r0 / ell equals
Upsilon cos theta0 = sqrt (1/2 + 1/(2 upsilon)) Upsilon. PROVED. -/
theorem c1_mul_radius (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    c1 (rho δ τ) * saddleRadius δ τ / ell δ =
      sqrt (1 / 2 + 1 / (2 * BookE.ups (rho δ τ))) * upsilon (rho δ τ) := by
  have hρ := rho_pos δ τ hδ hτ
  have hυ : 1 < BookE.ups (rho δ τ) := ups_gt_one _ hρ
  have hL := ell_pos δ hδ
  have hY : 0 < BookE.ups (rho δ τ) ^ 2 - BookE.ups (rho δ τ) := by nlinarith
  have hX : 0 ≤ 1 + 1 / BookE.ups (rho δ τ) := by positivity
  have hsY : sqrt (BookE.ups (rho δ τ) ^ 2 - BookE.ups (rho δ τ)) ≠ 0 :=
    (sqrt_pos.mpr hY).ne'
  have hs2 : sqrt 2 ≠ 0 := by positivity
  have hhalf : 1 / 2 + 1 / (2 * BookE.ups (rho δ τ)) = (1 + 1 / BookE.ups (rho δ τ)) / 2 := by
    ring
  unfold c1 saddleRadius
  rw [hhalf, sqrt_div hX, sqrt_div hX]
  field_simp

/-- P0014 pages 17 and 20, displays 3.31, 3.41 and 3.50: the saddle radius r0 lies
between the radius r minus of display 3.58 and the real endpoint c0 ell / c1, that is
alpha0 is at most 0 and 0 is at most alpha1. PROVED from display 3.34. -/
theorem saddleRadius_mem (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    initialRadius δ τ ≤ saddleRadius δ τ ∧ saddleRadius δ τ ≤ realEndpoint δ τ := by
  have hρ := rho_pos δ τ hδ hτ
  have hυ : 1 < BookE.ups (rho δ τ) := ups_gt_one _ hρ
  have hL := ell_pos δ hδ
  have hc1 := c1_pos _ hρ
  have hk := c1_mul_radius δ τ hδ hτ
  have hr0 : saddleRadius δ τ = ell δ / c1 (rho δ τ) *
      (sqrt (1 / 2 + 1 / (2 * BookE.ups (rho δ τ))) * upsilon (rho δ τ)) := by
    rw [← hk]; field_simp
  have hpos : 0 < ell δ / c1 (rho δ τ) := div_pos hL hc1
  have hsin : sqrt (1 / 2 - 1 / (2 * BookE.ups (rho δ τ))) ≤ 1 / sqrt 2 := by
    rw [show (1 : ℝ) / sqrt 2 = sqrt (1 / 2) by rw [sqrt_div zero_le_one, sqrt_one]]
    apply sqrt_le_sqrt
    have : 0 < 1 / (2 * BookE.ups (rho δ τ)) := by positivity
    linarith
  have hsin0 : 0 ≤ sqrt (1 / 2 - 1 / (2 * BookE.ups (rho δ τ))) := sqrt_nonneg _
  unfold initialRadius realEndpoint
  rw [hr0]
  unfold c0
  constructor
  · apply mul_le_mul_of_nonneg_left _ hpos.le
    linarith
  · rw [mul_div_assoc', div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hc1.le
    apply mul_le_mul_of_nonneg_left _ hL.le
    linarith

/-- P0014 page 23, display 3.53 with A.14: nu0 / (alpha0 + nu0) = r0 / r minus is
at most 7.83, the constant printed in display 3.57. PROVED from c0 at least 1 and
Upsilon below 1; the true ratio is at most 1 / (1 - 1 / sqrt 2), about 3.42. -/
theorem saddleRadius_le_initial (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    saddleRadius δ τ ≤ 7.83 * initialRadius δ τ := by
  have hρ := rho_pos δ τ hδ hτ
  have hυ : 1 < BookE.ups (rho δ τ) := ups_gt_one _ hρ
  have hL := ell_pos δ hδ
  have hc1 := c1_pos _ hρ
  have hk := c1_mul_radius δ τ hδ hτ
  have hr0 : saddleRadius δ τ = ell δ / c1 (rho δ τ) *
      (sqrt (1 / 2 + 1 / (2 * BookE.ups (rho δ τ))) * upsilon (rho δ τ)) := by
    rw [← hk]; field_simp
  have hpos : 0 < ell δ / c1 (rho δ τ) := div_pos hL hc1
  have hcos : sqrt (1 / 2 + 1 / (2 * BookE.ups (rho δ τ))) ≤ 1 := by
    rw [show (1 : ℝ) = sqrt 1 by rw [sqrt_one]]
    apply sqrt_le_sqrt
    have : 1 / (2 * BookE.ups (rho δ τ)) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hU0 := (upsilon_pos _ hρ).le
  have hU1 := (upsilon_lt_one _ hρ).le
  have hk1 : sqrt (1 / 2 + 1 / (2 * BookE.ups (rho δ τ))) * upsilon (rho δ τ) ≤ 1 := by
    calc _ ≤ 1 * 1 := mul_le_mul hcos hU1 hU0 zero_le_one
      _ = 1 := one_mul 1
  have hc0 := c0_ge_one _ hρ
  have hs2 : (1.414 : ℝ) ≤ sqrt 2 := by
    rw [show (1.414 : ℝ) = sqrt (1.414 ^ 2) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by norm_num)
  have hinv : 1 / sqrt 2 ≤ 0.7073 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  unfold initialRadius
  rw [hr0, show 7.83 * (ell δ / c1 (rho δ τ) * (c0 (rho δ τ) - 1 / sqrt 2)) =
    ell δ / c1 (rho δ τ) * (7.83 * (c0 (rho δ τ) - 1 / sqrt 2)) by ring]
  apply mul_le_mul_of_nonneg_left _ hpos.le
  linarith

/-- LEAF: P0014 page 23, the bound after display 3.55, by A.29: eta is positive and
(1 + 2 c0 ^ 2) / eta is at most min 5 (0.86 rho). Appendix A, page 66, display A.29. -/
theorem eta_bound (ρ : ℝ) (hρ : 0 < ρ) :
    0 < eta ρ ∧ (1 + 2 * c0 ρ ^ 2) / eta ρ ≤ min 5 (0.86 * ρ) := by
  sorry

/-- LEAF: P0014 page 23, the bound on r0 from A.32 and display 3.32:
r0 is at least 2/3 times min (tau / ell) (sqrt tau). -/
theorem saddleRadius_lower (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    2 / 3 * min (|τ| / ell δ) (sqrt |τ|) ≤ saddleRadius δ τ := by
  sorry

/-! ## Proved steps -/

/-- P0014 page 22 before display 3.49: the Gaussian over a half line,
the integral of exp of minus eta x ^ 2 over 0 to w is at most sqrt pi / (2 sqrt eta). PROVED. -/
theorem gaussian_initial_le (η w : ℝ) (hη : 0 < η) (hw : 0 ≤ w) :
    ∫ x in (0 : ℝ)..w, exp (-η * x ^ 2) ≤ sqrt π / (2 * sqrt η) := by
  rw [intervalIntegral.integral_of_le hw]
  have hint : IntegrableOn (fun x : ℝ => exp (-η * x ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq hη).integrableOn
  have hle : ∫ x in Ioc 0 w, exp (-η * x ^ 2) ≤ ∫ x in Ioi (0 : ℝ), exp (-η * x ^ 2) :=
    setIntegral_mono_set hint
      (Filter.Eventually.of_forall (fun x => (exp_pos _).le))
      (Filter.Eventually.of_forall (fun x hx => hx.1))
  rw [integral_gaussian_Ioi, sqrt_div pi_pos.le] at hle
  calc _ ≤ _ := hle
    _ = sqrt π / (2 * sqrt η) := by ring

/-- The right half of the split in display 3.49. PROVED. -/
theorem gaussian_right_le (η c v : ℝ) (hη : 0 < η) (hcv : c ≤ v) :
    ∫ r in c..v, exp (-η * (r - c) ^ 2) ≤ sqrt π / (2 * sqrt η) := by
  rw [intervalIntegral.integral_comp_sub_right (fun x => exp (-η * x ^ 2)) c, sub_self]
  exact gaussian_initial_le η _ hη (by linarith)

/-- The left half of the split in display 3.49. PROVED. -/
theorem gaussian_left_le (η c u : ℝ) (hη : 0 < η) (huc : u ≤ c) :
    ∫ r in u..c, exp (-η * (r - c) ^ 2) ≤ sqrt π / (2 * sqrt η) := by
  have h : ∀ r : ℝ, exp (-η * (r - c) ^ 2) = exp (-η * (c - r) ^ 2) := by
    intro r; congr 2; ring
  simp_rw [h]
  rw [intervalIntegral.integral_comp_sub_left (fun x => exp (-η * x ^ 2)) c, sub_self]
  exact gaussian_initial_le η _ hη (by linarith)

/-- P0014 page 22, display 3.49 bounds: one half of the contour with a constant times the
Gaussian majorant. PROVED. -/
theorem piece_bound (f : ℝ → ℂ) (K η c u v : ℝ) (hη : 0 < η) (hK : 0 ≤ K) (huv : u ≤ v)
    (hside : v = c ∨ u = c)
    (hpt : ∀ r ∈ Icc u v, ‖f r‖ ≤ K * exp (-η * (r - c) ^ 2)) :
    ‖∫ r in u..v, f r‖ ≤ K * (sqrt π / (2 * sqrt η)) := by
  have hg : IntervalIntegrable (fun r => K * exp (-η * (r - c) ^ 2)) volume u v :=
    (by fun_prop : Continuous fun r : ℝ => K * exp (-η * (r - c) ^ 2)).intervalIntegrable _ _
  have h1 := intervalIntegral.norm_integral_le_of_norm_le huv
    (Filter.Eventually.of_forall (fun r hr => hpt r (Ioc_subset_Icc_self hr))) hg
  rw [intervalIntegral.integral_const_mul] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hK)
  rcases hside with h | h
  · subst h; exact gaussian_left_le η v u hη huv
  · subst h; exact gaussian_right_le η u v hη huv

/-- The constant of display 3.57: sqrt pi / 2 times sqrt (min 5 (0.86 rho)) is at most
min 2 (3.3 sqrt tau / ell). PROVED from the A.29 leaf. -/
theorem constant_le (δ : ℝ) (s : ℂ) (hδ : δ ≠ 0) (hτ : 0 < |s.im|) :
    sqrt (1 + 2 * c0 (rho δ s.im) ^ 2) * (sqrt π / (2 * sqrt (eta (rho δ s.im)))) ≤
      min 2 (3.3 * sqrt |s.im| / (2 * π * |δ|)) := by
  set ρ := rho δ s.im with hρdef
  have hρ : 0 < ρ := rho_pos δ s.im hδ hτ
  obtain ⟨hη, hA⟩ := eta_bound ρ hρ
  set X := sqrt ((1 + 2 * c0 ρ ^ 2) / eta ρ)
  have hX : sqrt (1 + 2 * c0 ρ ^ 2) * (sqrt π / (2 * sqrt (eta ρ))) = sqrt π / 2 * X := by
    simp only [X]
    rw [sqrt_div (by positivity)]
    field_simp
  rw [hX]
  have hpi : sqrt π ≤ 1.78 := by
    rw [show (1.78 : ℝ) = sqrt (1.78 ^ 2) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by have := pi_lt_d2; norm_num at this ⊢; linarith)
  have hX0 : 0 ≤ X := sqrt_nonneg _
  have hX5 : X ≤ sqrt 5 := sqrt_le_sqrt (hA.trans (min_le_left _ _))
  have hXr : X ≤ sqrt (0.86 * ρ) := sqrt_le_sqrt (hA.trans (min_le_right _ _))
  have hs5 : sqrt 5 ≤ 2.237 := by
    rw [show (2.237 : ℝ) = sqrt (2.237 ^ 2) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by norm_num)
  have hs86 : sqrt 0.86 ≤ 0.93 := by
    rw [show (0.93 : ℝ) = sqrt (0.93 ^ 2) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by norm_num)
  have hpd : 0 < π * |δ| := mul_pos pi_pos (abs_pos.mpr hδ)
  have hsρ : sqrt ρ = sqrt |s.im| / (π * |δ|) := by
    rw [hρdef, rho, sqrt_div (abs_nonneg _), show (π * δ) ^ 2 = (π * |δ|) ^ 2 by
      rw [mul_pow, mul_pow, sq_abs], sqrt_sq hpd.le]
  have hsp : 0 ≤ sqrt π := sqrt_nonneg _
  apply le_min
  · nlinarith
  · have h1 : X ≤ 0.93 * (sqrt |s.im| / (π * |δ|)) := by
      rw [← hsρ, sqrt_mul (by norm_num)] at *
      exact hXr.trans (mul_le_mul_of_nonneg_right hs86 (sqrt_nonneg _))
    have h2 : 3.3 * sqrt |s.im| / (2 * π * |δ|) = 1.65 * (sqrt |s.im| / (π * |δ|)) := by
      field_simp; ring
    rw [h2]
    have hq : 0 ≤ sqrt |s.im| / (π * |δ|) := div_nonneg (sqrt_nonneg _) hpd.le
    nlinarith

/-- P0014 page 23: r0 ^ (sigma - 1) is at most ((3/2) / min (tau / ell) (sqrt tau)) ^ (1 - sigma)
for sigma at most 1. PROVED from the A.32 leaf. -/
theorem radius_power_le (δ : ℝ) (s : ℂ) (hδ : δ ≠ 0) (hτ : 0 < |s.im|) (hσ1 : s.re ≤ 1) :
    saddleRadius δ s.im ^ (s.re - 1) ≤
      ((3 / 2 : ℝ) / min (|s.im| / (2 * π * |δ|)) (sqrt |s.im|)) ^ (1 - s.re) := by
  set m := min (|s.im| / (2 * π * |δ|)) (sqrt |s.im|)
  have hm : 0 < m := lt_min (div_pos hτ (by positivity)) (sqrt_pos.mpr hτ)
  have hlow : 2 / 3 * m ≤ saddleRadius δ s.im := saddleRadius_lower δ s.im hδ hτ
  have h1 : saddleRadius δ s.im ^ (s.re - 1) ≤ (2 / 3 * m) ^ (s.re - 1) :=
    rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
  have h2 : (2 / 3 * m) ^ (s.re - 1) = ((3 / 2 : ℝ) / m) ^ (1 - s.re) := by
    rw [show s.re - 1 = -(1 - s.re) by ring, rpow_neg (by positivity),
      ← inv_rpow (by positivity)]
    congr 1
    field_simp
  exact h1.trans h2.le

/-! ## Assembly -/

/-- P0014 page 23, displays 3.56 and 3.57, exactly the statement of
`Decomp639Contour.saddle_segment_bound`, assembled from the steps above with no further
sorry. CONDITIONAL ON the four leaves phase_lower_bound, arc_length_bound, eta_bound and
saddleRadius_lower. -/
theorem saddle_segment_bound_of_leaves (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖saddleIntegral δ s‖ ≤ mainCoefficient s.re |s.im| δ *
      exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) := by
  have hδ : δ ≠ 0 := by intro h; simp [h] at hsign
  have hτ : 0 < |s.im| := by linarith
  set σ := s.re with hσdef
  set a := initialRadius δ s.im
  set b := realEndpoint δ s.im
  set r0 := saddleRadius δ s.im
  set ρ := rho δ s.im with hρdef
  set η := eta ρ
  set γ := saddlePath δ s.im
  set B := exp (-BookE.E ρ * |s.im|)
  set Λ := sqrt (1 + 2 * c0 ρ ^ 2)
  set G := sqrt π / (2 * sqrt η)
  set P := (7.83 : ℝ) ^ (1 - σ)
  have hρ : 0 < ρ := rho_pos δ s.im hδ hτ
  have hη : 0 < η := (eta_bound ρ hρ).1
  have ha0 : 0 < a := initialRadius_pos δ s.im hδ hτ
  obtain ⟨har0, hr0b⟩ := saddleRadius_mem δ s.im hδ hτ
  have hr0 : 0 < r0 := ha0.trans_le har0
  have hab : a ≤ b := har0.trans hr0b
  -- integrability, as in `saddleIntegral_eq_sub`
  have hcd : ∀ r ∈ Icc a b, ContDiffAt ℝ 2 γ r := fun r hr =>
    saddlePath_contDiffAt δ s.im r hδ hτ hr
  have hγc : ContinuousOn γ (Icc a b) := fun r hr =>
    (hcd r hr).continuousAt.continuousWithinAt
  have hdc : ContinuousOn (deriv γ) (Icc a b) := fun r hr =>
    ((hcd r hr).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hkc : ContinuousOn (fun r => contourKernel δ s (γ r)) (Icc a b) :=
    (contourKernel_differentiable δ s).continuousOn.comp hγc
      (fun r hr => saddlePath_re_pos δ s.im r hδ hτ hr)
  have hint : IntervalIntegrable (fun r => contourKernel δ s (γ r) * deriv γ r) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hkc.mul hdc
  have hint1 : IntervalIntegrable (fun r => contourKernel δ s (γ r) * deriv γ r) volume a r0 :=
    hint.mono_set (by rw [uIcc_of_le hab, uIcc_of_le har0]; exact Icc_subset_Icc le_rfl hr0b)
  have hint2 : IntervalIntegrable (fun r => contourKernel δ s (γ r) * deriv γ r) volume r0 b :=
    hint.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hr0b]; exact Icc_subset_Icc har0 le_rfl)
  have hsplit : saddleIntegral δ s =
      (∫ r in a..r0, contourKernel δ s (γ r) * deriv γ r) +
        ∫ r in r0..b, contourKernel δ s (γ r) * deriv γ r :=
    (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
  -- pointwise bound
  have hpt : ∀ r ∈ Icc a b, ‖contourKernel δ s (γ r) * deriv γ r‖ ≤
      r ^ (σ - 1) * B * exp (-η * (r - r0) ^ 2) * Λ := by
    intro r hr
    rw [norm_mul]
    exact mul_le_mul (phase_lower_bound δ s hsign r hr) (arc_length_bound δ s.im r hδ hτ hr)
      (norm_nonneg _) (by have := ha0.trans_le hr.1; positivity)
  -- power bounds of display 3.48
  have h783 : r0 ≤ 7.83 * a := saddleRadius_le_initial δ s.im hδ hτ
  have hpow1 : ∀ r ∈ Icc a r0, r ^ (σ - 1) ≤ P * r0 ^ (σ - 1) := by
    intro r hr
    have hlow : r0 / 7.83 ≤ r := by
      rw [div_le_iff₀ (by norm_num)]; linarith [hr.1]
    have h1 : r ^ (σ - 1) ≤ (r0 / 7.83) ^ (σ - 1) :=
      rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
    have h2 : (r0 / 7.83) ^ (σ - 1) = P * r0 ^ (σ - 1) := by
      rw [div_rpow hr0.le (by norm_num), show σ - 1 = -(1 - σ) by ring,
        rpow_neg (by norm_num : (0 : ℝ) ≤ 7.83)]
      simp only [P]
      field_simp
    exact h1.trans h2.le
  have hpow2 : ∀ r ∈ Icc r0 b, r ^ (σ - 1) ≤ r0 ^ (σ - 1) := fun r hr =>
    rpow_le_rpow_of_nonpos hr0 hr.1 (by linarith)
  -- the two halves
  have hI1 : ‖∫ r in a..r0, contourKernel δ s (γ r) * deriv γ r‖ ≤
      (P * r0 ^ (σ - 1) * B * Λ) * G := by
    apply piece_bound _ _ η r0 a r0 hη (by positivity) har0 (Or.inl rfl)
    intro r hr
    have hrab : r ∈ Icc a b := ⟨hr.1, hr.2.trans hr0b⟩
    have hrp : 0 < r := ha0.trans_le hr.1
    calc _ ≤ r ^ (σ - 1) * B * exp (-η * (r - r0) ^ 2) * Λ := hpt r hrab
      _ ≤ P * r0 ^ (σ - 1) * B * exp (-η * (r - r0) ^ 2) * Λ := by
        gcongr
        exact hpow1 r hr
      _ = _ := by ring
  have hI2 : ‖∫ r in r0..b, contourKernel δ s (γ r) * deriv γ r‖ ≤
      (r0 ^ (σ - 1) * B * Λ) * G := by
    apply piece_bound _ _ η r0 r0 b hη (by positivity) hr0b (Or.inr rfl)
    intro r hr
    have hrab : r ∈ Icc a b := ⟨har0.trans hr.1, hr.2⟩
    have hrp : 0 < r := hr0.trans_le hr.1
    calc _ ≤ r ^ (σ - 1) * B * exp (-η * (r - r0) ^ 2) * Λ := hpt r hrab
      _ ≤ r0 ^ (σ - 1) * B * exp (-η * (r - r0) ^ 2) * Λ := by
        have hB0 : 0 ≤ B := (exp_pos _).le
        apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
        exact mul_le_mul_of_nonneg_right (hpow2 r hr) hB0
      _ = _ := by ring
  -- constants of display 3.57
  have hK : Λ * G ≤ min 2 (3.3 * sqrt |s.im| / (2 * π * |δ|)) := constant_le δ s hδ hτ
  have hR := radius_power_le δ s hδ hτ hσ1
  have hM : P + 1 ≤ 1 + max ((7.83 : ℝ) ^ (1 - σ)) ((1.63 : ℝ) ^ (σ - 1)) := by
    simp only [P]; linarith [le_max_left ((7.83 : ℝ) ^ (1 - σ)) ((1.63 : ℝ) ^ (σ - 1))]
  have hE : exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) = B := rfl
  rw [hE, hsplit]
  unfold mainCoefficient
  have hB : 0 ≤ B := (exp_pos _).le
  have hP : 0 ≤ P := by positivity
  have hR0 : 0 ≤ r0 ^ (σ - 1) := by positivity
  have hΛG : 0 ≤ Λ * G := by positivity
  calc _ ≤ ‖∫ r in a..r0, contourKernel δ s (γ r) * deriv γ r‖ +
        ‖∫ r in r0..b, contourKernel δ s (γ r) * deriv γ r‖ := norm_add_le _ _
    _ ≤ (P * r0 ^ (σ - 1) * B * Λ) * G + (r0 ^ (σ - 1) * B * Λ) * G := add_le_add hI1 hI2
    _ = (P + 1) * r0 ^ (σ - 1) * (B * (Λ * G)) := by ring
    _ ≤ (1 + max ((7.83 : ℝ) ^ (1 - σ)) ((1.63 : ℝ) ^ (σ - 1))) *
          ((3 / 2 : ℝ) / min (|s.im| / (2 * π * |δ|)) (sqrt |s.im|)) ^ (1 - σ) *
          (B * min 2 (3.3 * sqrt |s.im| / (2 * π * |δ|))) := by
        gcongr ?_ * ?_ * (B * ?_)
    _ = _ := by ring

/-- Twin check: the assembled theorem has exactly the type of the sealed leaf. -/
theorem saddle_segment_bound_twin :
    (∀ (δ : ℝ) (s : ℂ), 0 < s.re → s.re ≤ 1 → 100 ≤ |s.im| → δ * s.im < 0 →
      ‖saddleIntegral δ s‖ ≤ mainCoefficient s.re |s.im| δ *
        exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|)) :=
  fun δ s h0 h1 ht hs => saddle_segment_bound_of_leaves δ s h0 h1 ht hs

end LeanLab.HelfgottMajor.DQSaddleSegmentBound

#print axioms LeanLab.HelfgottMajor.DQSaddleSegmentBound.gaussian_initial_le
#print axioms LeanLab.HelfgottMajor.DQSaddleSegmentBound.piece_bound
#print axioms LeanLab.HelfgottMajor.DQSaddleSegmentBound.saddle_segment_bound_of_leaves
