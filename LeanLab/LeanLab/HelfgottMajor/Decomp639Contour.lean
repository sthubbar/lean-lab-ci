import LeanLab.HelfgottMajor.ContourKernel669
import LeanLab.HelfgottMajor.DQSaddleSegmentBound
import LeanLab.HelfgottMajor.Prep1121A33Window

/-!
The original two contour bound statements, with their statements unchanged.
Shared definitions and proved geometric lemmas moved verbatim to ContourKernel669.
The saddle proof reuses the assembly supplied by the requested base branch.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp639Contour
open Real MeasureTheory Set SplitGaussian123 Decomp511a Filter
open scoped Topology

/-- LEAF: P0014 page 23, displays 3.56 and 3.57.
The central limacon integral has the printed main coefficient and saddle exponent.
OPEN. This requires the quantitative phase and arc length estimates of Section 3.7. -/
theorem saddle_segment_bound (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖saddleIntegral δ s‖ ≤ mainCoefficient s.re |s.im| δ *
      exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) := by
  exact DQSaddleSegmentBound.saddle_segment_bound_of_leaves δ s hσ0 hσ1 ht hsign


/-- P0014 displays 3.32 and 3.61. The central saddle radius is at most the square root
of the absolute height, for every nonzero shift and height. -/
private theorem saddleRadius_le_sqrt (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    DQSaddleSegmentBound.saddleRadius δ τ ≤ sqrt |τ| := by
  set ρ := rho δ τ with hρdef
  have hρ : 0 < ρ := rho_pos δ τ hδ hτ
  have hu := ups_gt_one ρ hρ
  have hj : sqrt (1 + ρ ^ 2) ≤ 1 + ρ := by
    simpa only [Real.norm_eq_abs, abs_of_pos hρ] using sqrt_one_add_norm_sq_le ρ
  have hU : BookE.ups ρ ^ 2 = (1 + sqrt (1 + ρ ^ 2)) / 2 := by
    unfold BookE.ups
    rw [sq_sqrt (by positivity)]
  have hY0 : 0 ≤ BookE.ups ρ ^ 2 - BookE.ups ρ := by nlinarith
  have hY : 2 * (BookE.ups ρ ^ 2 - BookE.ups ρ) ≤ ρ := by nlinarith
  have hr0sq : DQSaddleSegmentBound.saddleRadius δ τ ^ 2 =
      ell δ ^ 2 / 2 * (BookE.ups ρ ^ 2 - BookE.ups ρ) := by
    rw [DQSaddleSegmentBound.saddleRadius, ← hρdef, mul_pow, div_pow, sq_sqrt hY0,
      sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hM := mul_le_mul_of_nonneg_left hY (sq_nonneg (ell δ))
  have hell := ell_sq_mul_rho δ τ hδ
  rw [← hρdef] at hell
  apply le_sqrt_of_sq_le
  rw [hr0sq]
  nlinarith only [hM, hell]

/-- P0014 page 67, second bound of display A.33. This half of the named numerical
input is elementary and needs no interval computation. -/
private theorem a33_second (ρ : ℝ) (hρ : 0 < ρ) :
    (c0 ρ - 1 / sqrt 2) / (c1 ρ * sqrt ρ) ≤ 1 / 2 := by
  let τ : ℝ := π ^ 2 * ρ
  have ht : 0 < τ := mul_pos (sq_pos_of_pos pi_pos) hρ
  have hτ : 0 < |τ| := abs_pos.mpr ht.ne'
  have hd : (1 : ℝ) ≠ 0 := by norm_num
  have hρid : rho 1 τ = ρ := by
    simp only [rho, mul_one, abs_of_pos ht]
    dsimp only [τ]
    field_simp
  have hi : initialRadius 1 τ ≤ sqrt |τ| :=
    (DQSaddleSegmentBound.saddleRadius_mem 1 τ hd hτ).1.trans (saddleRadius_le_sqrt 1 τ hd hτ)
  have hE := ell_mul_sqrt_rho 1 τ hd
  rw [hρid] at hE
  have hc := c1_pos ρ hρ
  have hL := ell_pos 1 hd
  have hs : 0 < sqrt ρ := sqrt_pos.mpr hρ
  have hst : sqrt |τ| ≠ 0 := (sqrt_pos.mpr hτ).ne'
  calc
    (c0 ρ - 1 / sqrt 2) / (c1 ρ * sqrt ρ) =
        initialRadius 1 τ / (ell 1 * sqrt ρ) := by
      rw [initialRadius, hρid]
      field_simp
      <;> ring
    _ ≤ sqrt |τ| / (ell 1 * sqrt ρ) := div_le_div_of_nonneg_right hi (by positivity)
    _ = 1 / 2 := by
      rw [hE]
      field_simp


/-- P0014 page 16, display 3.25 and page 67, display A.33.
For `ρ > 0` the parameter `u = 1/υ(ρ)` lies in `(0,1)`. -/
private theorem u_mem (ρ : ℝ) (hρ : 0 < ρ) : 0 < 1 / BookE.ups ρ ∧ 1 / BookE.ups ρ < 1 := by
  have hv := ups_gt_one ρ hρ
  exact ⟨by positivity, by rw [div_lt_one (by linarith)]; exact hv⟩

/-- P0014 page 16, display 3.25.
`√(1+ρ²) = 2υ² - 1` and `ρ² = 4υ²(υ²-1)`. -/
private theorem ups_sq (ρ : ℝ) (hρ : 0 < ρ) :
    √(1 + ρ ^ 2) = 2 * BookE.ups ρ ^ 2 - 1 ∧
      ρ ^ 2 = 4 * BookE.ups ρ ^ 2 * (BookE.ups ρ ^ 2 - 1) := by
  have hs : 0 ≤ √(1 + ρ ^ 2) := sqrt_nonneg _
  have hv : BookE.ups ρ ^ 2 = (1 + √(1 + ρ ^ 2)) / 2 := by
    unfold BookE.ups
    rw [sq_sqrt (by positivity)]
  have h1 : √(1 + ρ ^ 2) = 2 * BookE.ups ρ ^ 2 - 1 := by rw [hv]; ring
  refine ⟨h1, ?_⟩
  have h2 := sq_sqrt (show (0:ℝ) ≤ 1 + ρ ^ 2 by positivity)
  rw [h1] at h2
  nlinarith [h2]

/-- P0014 page 16, display 3.25; Mathlib lookup plus the half angle formula.
`tan (arctan X / 2) = X / (1 + √(1 + X²))` for `X > 0`. -/
private theorem tan_half_arctan (X : ℝ) (hX : 0 < X) :
    tan (arctan X / 2) = X / (1 + √(1 + X ^ 2)) := by
  set θ := arctan X / 2 with hθ
  have e1 : arctan X = 2 * θ := by rw [hθ]; ring
  have hc : 0 < cos θ := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [neg_pi_div_two_lt_arctan X, pi_pos]
    · linarith [arctan_lt_pi_div_two X, pi_pos]
  have hS : 0 < √(1 + X ^ 2) := sqrt_pos.mpr (by positivity)
  have hs := sin_arctan X
  have hco := cos_arctan X
  rw [e1, sin_two_mul] at hs
  rw [e1, cos_two_mul] at hco
  rw [eq_div_iff hS.ne'] at hs hco
  rw [tan_eq_sin_div_cos, div_eq_div_iff hc.ne' (by positivity)]
  linear_combination cos θ * hs - sin θ * hco

/-- P0014 page 16, display 3.25 and page 18, display 3.34; one clear idea.
In the variable `u = 1/υ`, `Υ(ρ) = (2-u)√(1+u) / (√(1-u) u + √(4-2u²))`:
the argument of the arctangent is `X = (2υ-1)a/b` and `√(1+X²) = √(4υ²-2)/b`. -/
private theorem upsilon_u (ρ : ℝ) (hρ : 0 < ρ) :
    let u := 1 / BookE.ups ρ
    upsilon ρ = (2 - u) * √(1 + u) / (√(1 - u) * u + √(4 - 2 * u ^ 2)) := by
  intro u
  have hv := ups_gt_one ρ hρ
  obtain ⟨hs1, hρ2⟩ := ups_sq ρ hρ
  set v := BookE.ups ρ with hvdef
  have hv0 : 0 < v := by linarith
  have hu : u * v = 1 := by simp only [u, ← hvdef]; field_simp
  have hu0 : 0 < u := by simp only [u, ← hvdef]; positivity
  have hu1 : u < 1 := by simp only [u, ← hvdef]; rw [div_lt_one hv0]; exact hv
  set r := √(v ^ 2 - 1) with hrdef
  have hr2 : r ^ 2 = v ^ 2 - 1 := sq_sqrt (by nlinarith)
  have hr0 : 0 < r := sqrt_pos.mpr (by nlinarith)
  have hρr : ρ = 2 * v * r := by
    have h : ρ ^ 2 = (2 * v * r) ^ 2 := by rw [hρ2, mul_pow, mul_pow, hr2]; ring
    exact (pow_left_inj₀ hρ.le (by positivity) two_ne_zero).mp h
  unfold upsilon
  rw [← hvdef, hs1]
  set X := 2 * v * (v + (2 * v ^ 2 - 1)) / ρ with hXdef
  have hX : X = (2 * v - 1) * (v + 1) / r := by
    rw [hXdef, hρr]
    field_simp
    ring
  have hX0 : 0 < X := by rw [hX]; apply div_pos _ hr0; nlinarith
  rw [tan_half_arctan X hX0]
  set T := √(2 * v * (2 * v ^ 2 - 1) * (v + 1)) with hTdef
  have hT0 : 0 ≤ T := sqrt_nonneg _
  have hT : √(1 + X ^ 2) = T / r := by
    have e : 1 + X ^ 2 = 2 * v * (2 * v ^ 2 - 1) * (v + 1) / r ^ 2 := by
      rw [hX, hr2]
      have : v ^ 2 - 1 ≠ 0 := by nlinarith
      field_simp
      rw [hr2]
      ring
    rw [e, sqrt_div' _ (sq_nonneg r), sqrt_sq hr0.le]
  set a := √(1 + u) with hadef
  set b := √(1 - u) with hbdef
  set R := √(4 - 2 * u ^ 2) with hRdef
  have ha2 : a ^ 2 = 1 + u := sq_sqrt (by linarith)
  have hb2 : b ^ 2 = 1 - u := sq_sqrt (by linarith)
  have hR2 : R ^ 2 = 4 - 2 * u ^ 2 := sq_sqrt (by nlinarith)
  have hT2 : T ^ 2 = 2 * v * (2 * v ^ 2 - 1) * (v + 1) := sq_sqrt (by
    have : 0 ≤ 2 * v ^ 2 - 1 := by nlinarith
    positivity)
  have ha0 : 0 ≤ a := sqrt_nonneg _
  have hb0 : 0 < b := sqrt_pos.mpr (by linarith)
  have hR0 : 0 ≤ R := sqrt_nonneg _
  have h1 : a * r = b * (v + 1) := by
    refine (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp ?_
    rw [mul_pow, mul_pow, ha2, hb2, hr2]
    have hu' : u = 1 / v := by simp only [u, ← hvdef]
    rw [hu']
    field_simp
    ring
  have h2 : r * v * R = b * T := by
    refine (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp ?_
    rw [mul_pow, mul_pow, mul_pow, hR2, hb2, hr2, hT2]
    have hu' : u = 1 / v := by simp only [u, ← hvdef]
    rw [hu']
    field_simp
    ring
  have h3 : a * T = (v + 1) * v * R := by
    apply mul_left_cancel₀ hb0.ne'
    linear_combination v * R * h1 - a * h2
  rw [hT, hX]
  have L : (2 * v - 1) * (v + 1) / r / (1 + T / r) = (2 * v - 1) * (v + 1) / (r + T) := by
    field_simp
  rw [L, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (v + 1) * (2 * b + R) * hu - (2 - u) * h1 - (2 - u) * h3

/-- P0014 page 18, display 3.34; pure calculation.
`c0 ρ = (√(1+u) Υ + √(1-u))/√2` with `u = 1/υ`. -/
private theorem c0_u (ρ : ℝ) (hρ : 0 < ρ) :
    let u := 1 / BookE.ups ρ
    c0 ρ = (√(1 + u) * upsilon ρ + √(1 - u)) / √2 := by
  intro u
  have hv := ups_gt_one ρ hρ
  have hv0 : 0 < BookE.ups ρ := by linarith
  have hu1 : 0 ≤ 1 - u := by
    have : u < 1 := by simp only [u]; rw [div_lt_one hv0]; exact hv
    linarith
  have e1 : (1:ℝ) / 2 + 1 / (2 * BookE.ups ρ) = (1 + u) / 2 := by simp only [u]; ring
  have e2 : (1:ℝ) / 2 - 1 / (2 * BookE.ups ρ) = (1 - u) / 2 := by simp only [u]; ring
  unfold c0
  rw [e1, e2, sqrt_div' _ (by norm_num : (0:ℝ) ≤ 2), sqrt_div' _ (by norm_num : (0:ℝ) ≤ 2)]
  ring

/-- P0014 page 18, display 3.34 and page 16, display 3.25; pure calculation.
`c1 ρ · ρ = 2(1+u) Υ / u` with `u = 1/υ`, from `ρ = 2υ√(υ²-1)`. -/
private theorem c1_mul_rho_u (ρ : ℝ) (hρ : 0 < ρ) :
    let u := 1 / BookE.ups ρ
    c1 ρ * ρ = 2 * (1 + u) * upsilon ρ / u := by
  intro u
  have hv := ups_gt_one ρ hρ
  set v := BookE.ups ρ with hvdef
  have hv0 : 0 < v := by linarith
  have hρ2 := (ups_sq ρ hρ).2
  rw [← hvdef] at hρ2
  have hd : 0 < v ^ 2 - v := by nlinarith
  have key : √((1 + 1 / v) / (v ^ 2 - v)) * ρ = 2 * (v + 1) := by
    rw [← sqrt_sq hρ.le, ← sqrt_mul (by positivity), hρ2]
    rw [show (1 + 1 / v) / (v ^ 2 - v) * (4 * v ^ 2 * (v ^ 2 - 1)) = (2 * (v + 1)) ^ 2 by
      field_simp
      ring]
    exact sqrt_sq (by linarith)
  unfold c1
  rw [← hvdef]
  calc √((1 + 1 / v) / (v ^ 2 - v)) * upsilon ρ * ρ =
      (√((1 + 1 / v) / (v ^ 2 - v)) * ρ) * upsilon ρ := by ring
    _ = 2 * (1 + u) * upsilon ρ / u := by
      rw [key]
      simp only [u, ← hvdef]
      field_simp

/-- P0014 page 67, display A.33; pure calculation with the relations
`a² = 1+u`, `b² = 1-u`, `R² = 4-2u²`. Given the three closed forms, the first line of A.33
is `Prep1121A33Cells.a33G u`. Checked by a Groebner reduction in sympy. -/
private theorem a33_quotient_eq (u U c0v c1r : ℝ) (hu0 : 0 < u) (hu1 : u < 1)
    (hU : U = (2 - u) * √(1 + u) / (√(1 - u) * u + √(4 - 2 * u ^ 2)))
    (h0 : c0v = (√(1 + u) * U + √(1 - u)) / √2)
    (h1 : c1r = 2 * (1 + u) * U / u) :
    (c0v - 1 / √2) / (√2 * c1r) = Prep1121A33Cells.a33G u := by
  subst hU h0 h1
  unfold Prep1121A33Cells.a33G
  set a := √(1 + u) with hadef
  set b := √(1 - u) with hbdef
  set R := √(4 - 2 * u ^ 2) with hRdef
  have ha2 : a ^ 2 = 1 + u := sq_sqrt (by linarith)
  have hb2 : b ^ 2 = 1 - u := sq_sqrt (by linarith)
  have hR2 : R ^ 2 = 4 - 2 * u ^ 2 := sq_sqrt (by nlinarith)
  have hs2 : √(2:ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  have ha0 : 0 < a := sqrt_pos.mpr (by linarith)
  have hb0 : 0 ≤ b := sqrt_nonneg _
  have hb1 : b ≤ 1 := sqrt_le_one.mpr (by linarith)
  have hR1 : 1 < R := by
    rw [hRdef, show (1:ℝ) = √1 by simp]
    exact sqrt_lt_sqrt (by norm_num) (by nlinarith)
  have hQ : 0 < R - b * u := by nlinarith
  have hQ' : 0 < b * u + R := by nlinarith
  have hs0 : 0 < √(2:ℝ) := by positivity
  field_simp
  rw [hs2, div_eq_div_iff (by linarith) (by nlinarith)]
  linear_combination (-4 * R * u + 8 * R + 4 * b * u ^ 2 - 8 * b * u) * ha2 +
    (-4 * b * u ^ 2 + 4 * u ^ 2) * hb2 + (4 * b - 4) * hR2

/-- P0014 page 67, display A.33, first line, in the variable `u = 1/υ(ρ)`. -/
private theorem a33_first_eq (ρ : ℝ) (hρ : 0 < ρ) :
    (c0 ρ - 1 / √2) / (√2 * c1 ρ * ρ) = Prep1121A33Cells.a33G (1 / BookE.ups ρ) := by
  have hu := u_mem ρ hρ
  rw [mul_assoc]
  exact a33_quotient_eq _ _ _ _ hu.1 hu.2 (upsilon_u ρ hρ) (c0_u ρ hρ) (c1_mul_rho_u ρ hρ)

/-- P0014 page 67, display A.33, first line:
`(c0 - 1/√2)/(√2 c1 ρ) ≤ 0.0763896` for every `ρ > 0`. -/
private theorem a33_first (ρ : ℝ) (hρ : 0 < ρ) :
    (c0 ρ - 1 / √2) / (√2 * c1 ρ * ρ) ≤ 0.0763896 := by
  have hB : ((Prep1121A33Cells.a33B : ℚ) : ℝ) = 0.0763896 := by norm_num [Prep1121A33Cells.a33B]
  rw [a33_first_eq ρ hρ, ← hB]
  obtain ⟨h0, h1⟩ := u_mem ρ hρ
  by_cases hw : 1 / 2 ≤ 1 / BookE.ups ρ ∧ 1 / BookE.ups ρ ≤ 4 / 5
  · exact Prep1121A33Window.a33G_le_window _ hw.1 hw.2
  · apply Prep1121A33Cells.a33G_le_outside _ h0 h1.le
    by_contra hc
    push_neg at hc
    exact hw ⟨hc.1, hc.2⟩


/-- P0014 page 67, display A.33, both lines: the numerical input of page 24 holds.
The first line is proved by certified interval arithmetic in `Prep1121A33Cells` and
`Prep1121A33Window`, the second by the saddle radius comparison. -/
private theorem helfgottA33_holds : ∀ ρ : ℝ, 0 < ρ →
    (c0 ρ - 1 / sqrt 2) / (sqrt 2 * c1 ρ * ρ) ≤ 0.0763896 ∧
    (c0 ρ - 1 / sqrt 2) / (c1 ρ * sqrt ρ) ≤ 1 / 2 :=
  fun ρ hρ => ⟨a33_first ρ hρ, a33_second ρ hρ⟩

/-- P0014 page 24, the display after 3.60: by A.33, `ℓ r₋ / √2 ≤ 0.07639 ℓ² ρ`, and
`ℓ² ρ = 4 |τ|`, so the phase cost is at most `0.30556 |τ|`. CONDITIONAL ON `HelfgottA33`. -/
private theorem initialRadius_phase_of_A33 (hA : ∀ ρ : ℝ, 0 < ρ →
      (c0 ρ - 1 / sqrt 2) / (sqrt 2 * c1 ρ * ρ) ≤ 0.0763896 ∧
      (c0 ρ - 1 / sqrt 2) / (c1 ρ * sqrt ρ) ≤ 1 / 2) (δ τ : ℝ) (hδ : δ ≠ 0)
    (hτ : 0 < |τ|) :
    ell δ * initialRadius δ τ / sqrt 2 ≤ 0.30556 * |τ| := by
  have hρ := rho_pos δ τ hδ hτ
  have hc := c1_pos _ hρ
  have hL := ell_pos δ hδ
  have hs : 0 < sqrt (2:ℝ) := by positivity
  have hs2 : sqrt (2:ℝ) * sqrt 2 = 2 := mul_self_sqrt (by norm_num)
  have hX := (hA _ hρ).1
  rw [div_le_iff₀ (by positivity)] at hX
  have he := ell_sq_mul_rho δ τ hδ
  have hkey : ell δ * initialRadius δ τ / sqrt 2 =
      ell δ ^ 2 * (c0 (rho δ τ) - 1 / sqrt 2) / (c1 (rho δ τ) * sqrt 2) := by
    unfold initialRadius
    field_simp
  have hb : ell δ ^ 2 * (c0 (rho δ τ) - 1 / sqrt 2) / (c1 (rho δ τ) * sqrt 2) ≤
      ell δ ^ 2 * (0.0763896 * (sqrt 2 * c1 (rho δ τ) * rho δ τ)) /
        (c1 (rho δ τ) * sqrt 2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hX (by positivity)
  have hc2 : ell δ ^ 2 * (0.0763896 * (sqrt 2 * c1 (rho δ τ) * rho δ τ)) /
        (c1 (rho δ τ) * sqrt 2) = 0.0763896 * (ell δ ^ 2 * rho δ τ) := by
    field_simp
  rw [hkey]
  calc _ ≤ _ := hb
    _ = _ := hc2
    _ ≤ _ := by rw [he]; nlinarith


/-- P0014 page 24, display 3.61: `r₋ ≤ √ρ ℓ / 2 ≤ √τ`, from 3.58 and the second line of A.33.
CONDITIONAL ON `HelfgottA33`. -/
private theorem initialRadius_le_sqrt_of_A33 (hA : ∀ ρ : ℝ, 0 < ρ →
      (c0 ρ - 1 / sqrt 2) / (sqrt 2 * c1 ρ * ρ) ≤ 0.0763896 ∧
      (c0 ρ - 1 / sqrt 2) / (c1 ρ * sqrt ρ) ≤ 1 / 2) (δ τ : ℝ) (hδ : δ ≠ 0)
    (hτ : 0 < |τ|) :
    initialRadius δ τ ≤ sqrt |τ| := by
  have hρ := rho_pos δ τ hδ hτ
  have hc := c1_pos _ hρ
  have hL := ell_pos δ hδ
  have hsr : 0 < sqrt (rho δ τ) := sqrt_pos.mpr hρ
  have hX := (hA _ hρ).2
  rw [div_le_iff₀ (by positivity)] at hX
  have hm := ell_mul_sqrt_rho δ τ hδ
  have hkey : initialRadius δ τ = ell δ / c1 (rho δ τ) * (c0 (rho δ τ) - 1 / sqrt 2) := rfl
  rw [hkey]
  calc _ ≤ ell δ / c1 (rho δ τ) * (1 / 2 * (c1 (rho δ τ) * sqrt (rho δ τ))) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = ell δ * sqrt (rho δ τ) / 2 := by field_simp
    _ = _ := by rw [hm]; ring


/-- P0014 page 24 before display 3.59: the direction w = (1 + i)/√2, conjugated for negative
height, in real and imaginary parts. -/
private theorem rayDirection_explicit (τ : ℝ) :
    rayDirection τ = ((1 / sqrt 2 : ℝ) : ℂ) +
      (((if 0 ≤ τ then 1 else -1) / sqrt 2 : ℝ) : ℂ) * Complex.I := by
  unfold rayDirection
  split_ifs <;> push_cast <;> ring

/-- P0014 page 24 before display 3.59: arg w = ±π/4 for the ray direction. -/
private theorem rayDirection_arg (τ : ℝ) :
    Complex.arg (rayDirection τ) = if 0 ≤ τ then π / 4 else -(π / 4) := by
  rw [rayDirection_eq_exp, Complex.exp_mul_I]
  apply Complex.arg_cos_add_sin_mul_I
  split_ifs <;> constructor <;> linarith [pi_pos]

/-- P0014 page 24, display 3.60: on the ray, the real part of `-z²/2 + 2πiδz` with `z = r w`
is `-2πδ r · Im w`, since `w²` is purely imaginary. -/
private theorem ray_exponent_re (δ τ r : ℝ) :
    (-((r:ℂ) * rayDirection τ) ^ 2 / 2 + 2 * π * Complex.I * δ * (r * rayDirection τ)).re =
      -(2 * π * δ * r * ((if 0 ≤ τ then 1 else -1) / sqrt 2)) := by
  rw [rayDirection_explicit]
  have h2 : sqrt (2:ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  have hs : sqrt (2:ℝ) ≠ 0 := by positivity
  split_ifs <;>
  · simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
    field_simp
    rw [h2]; ring

/-- P0014 page 24, display 3.60: on C1, `|z^{s-1} e^{-z²/2} e(δz)| = r^{σ-1} e^{ℓ r/√2 - π|τ|/4}`
when `δ τ < 0`, for every exponent with imaginary part τ. -/
private theorem ray_kernel_norm (δ τ : ℝ) (z : ℂ) (r : ℝ) (hr : 0 < r) (hz : z.im = τ)
    (hsign : δ * τ < 0) :
    ‖contourKernel δ z (r * rayDirection τ) * rayDirection τ‖ =
      r ^ (z.re - 1) * exp (ell δ * r / sqrt 2 - π / 4 * |τ|) := by
  have hw := rayDirection_norm τ
  have hne : (r:ℂ) * rayDirection τ ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast hr.ne') ?_
    intro h; rw [h, norm_zero] at hw; norm_num at hw
  unfold contourKernel
  rw [norm_mul, hw, mul_one, norm_mul, Complex.norm_cpow_of_ne_zero hne, Complex.norm_exp,
    ray_exponent_re, norm_mul, hw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, mul_one,
    Complex.arg_real_mul _ hr, rayDirection_arg]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero, hz]
  rw [div_eq_mul_inv, ← exp_neg, mul_assoc, ← exp_add]
  congr 2
  unfold ell
  rcases lt_or_gt_of_ne (show τ ≠ 0 by rintro rfl; simp at hsign) with h | h
  · have hd : 0 < δ := by nlinarith
    simp only [show ¬ (0 ≤ τ) from not_le.mpr h, ↓reduceIte]
    rw [abs_of_neg h, abs_of_pos hd]; ring
  · have hd : δ < 0 := by nlinarith
    simp only [h.le, ↓reduceIte]
    rw [abs_of_pos h, abs_of_neg hd]; ring

/-- P0014 page 25, after display 3.63: `∫_0^a A e^{L r/√2 - K} dr` in closed form. -/
private theorem ray_exp_integral (L A K a : ℝ) (hL : 0 < L) (ha : 0 ≤ a) :
    ∫ r in Ioo 0 a, A * exp (L * r / sqrt 2 - K) =
      A * (sqrt 2 / L) * (exp (L * a / sqrt 2 - K) - exp (-K)) := by
  have hs : 0 < sqrt (2:ℝ) := by positivity
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha]
  have hD : ∀ x ∈ uIcc 0 a, HasDerivAt
      (fun r => A * (sqrt 2 / L) * exp (L * r / sqrt 2 - K))
      (A * exp (L * x / sqrt 2 - K)) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => L * r / sqrt 2 - K) (L / sqrt 2) x := by
      simpa using (((hasDerivAt_id x).const_mul L).div_const (sqrt 2)).sub_const K
    convert (h1.exp).const_mul (A * (sqrt 2 / L)) using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hD
    ((by fun_prop : Continuous fun r : ℝ => A * exp (L * r / sqrt 2 - K)).intervalIntegrable _ _)]
  simp only [mul_zero, zero_div, zero_sub]
  ring


/-- PROVED, formerly the LEAF of this file. P0014 pages 24 and 25, displays 3.59, 3.60 and 3.63
with the bounds after 3.63.
Integration by parts on C1 from 0 to `w r₋`: the boundary term is at most
`r₋^σ / τ · e^{ℓ r₋ / √2 - π τ / 4}`, and the two integrals of display 3.63 are at most
`(r₋^{σ+2} + √2 r₋^σ) / τ · e^{ℓ r₋ / √2 - π τ / 4}` by `|s| ≥ τ` and
`∫_0^{r₋} e^{ℓ t / √2} dt ≤ min(√2 / ℓ, r₋) e^{ℓ r₋ / √2}`.
The exponent keeps the `√2` of display 3.60; the printed `ℓ r₋ / 2` on page 25 is a typo
that the paper's final line does not use. -/
private theorem initial_ibp_bound (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖initialIntegral δ s‖ ≤
      (initialRadius δ s.im ^ (s.re + 2) + (1 + sqrt 2) * initialRadius δ s.im ^ s.re) /
        |s.im| * exp (ell δ * initialRadius δ s.im / sqrt 2 - π / 4 * |s.im|) := by
  set τ := s.im with hτdef
  set σ := s.re with hσdef
  have hd : δ ≠ 0 := by intro h; simp [h] at hsign
  have hτ : 0 < |τ| := by linarith
  set a := initialRadius δ τ with hadef
  have ha : 0 < a := initialRadius_pos δ τ hd hτ
  set w := rayDirection τ with hwdef
  have hL : 0 < ell δ := ell_pos δ hd
  have hs2 : 0 < sqrt (2:ℝ) := by positivity
  set E := exp (ell δ * a / sqrt 2 - π / 4 * |τ|) with hE
  have hE0 : 0 < E := exp_pos _
  have hker : ∀ (z : ℂ), z.im = τ → ∀ r ∈ Ioo 0 a,
      ‖contourKernel δ z (r * w) * w‖ ≤ r ^ (z.re - 1) * exp (ell δ * r / sqrt 2 - π / 4 * |τ|) :=
    fun z hz r hr => (ray_kernel_norm δ τ z r hr.1 hz hsign).le
  -- boundary term
  have hB : ‖contourKernel δ s (a * w) * (a * w)‖ ≤ a ^ σ * E := by
    have h := ray_kernel_norm δ τ s a ha rfl hsign
    have hm : ‖contourKernel δ s (a * w) * (a * w)‖ =
        ‖contourKernel δ s (a * w) * w‖ * a := by
      rw [show contourKernel δ s (a * w) * (a * w) = (contourKernel δ s (a * w) * w) * a by ring,
        norm_mul (contourKernel δ s (a * w) * w), Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    rw [hm, h, mul_right_comm, ← rpow_add_one ha.ne', sub_add_cancel]
  -- the s + 2 integral
  have hI2 : ‖∫ r in Ioo 0 a, contourKernel δ (s + 2) (r * w) * w‖ ≤ a ^ (σ + 2) * E := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo 0 a)
      (C := a ^ (σ + 1) * E) measure_Ioo_lt_top (fun r hr => by
        refine (hker (s + 2) (by simp [hτdef]) r hr).trans ?_
        have hre : (s + 2).re - 1 = σ + 1 := by simp [hσdef]; ring
        rw [hre]
        apply mul_le_mul (rpow_le_rpow hr.1.le hr.2.le (by linarith))
          (exp_le_exp.mpr ?_) (exp_pos _).le (by positivity)
        have := mul_le_mul_of_nonneg_left hr.2.le hL.le
        have := div_le_div_of_nonneg_right this hs2.le
        linarith)
    rw [volume_real_Ioo_of_le ha.le, sub_zero] at h
    calc _ ≤ _ := h
      _ = a ^ (σ + 1 + 1) * E := by rw [rpow_add_one ha.ne' (σ + 1)]; ring
      _ = _ := by rw [show σ + 1 + 1 = σ + 2 by ring]
  -- the s + 1 integral
  have hI1 : ‖(2 * π * Complex.I * δ) *
      ∫ r in Ioo 0 a, contourKernel δ (s + 1) (r * w) * w‖ ≤ sqrt 2 * a ^ σ * E := by
    have hc : ‖(2 * π * Complex.I * δ : ℂ)‖ = ell δ := by
      unfold ell
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
    have hg : IntegrableOn (fun r : ℝ => a ^ σ * exp (ell δ * r / sqrt 2 - π / 4 * |τ|))
        (Ioo 0 a) :=
      (by fun_prop : Continuous fun r : ℝ => a ^ σ * exp (ell δ * r / sqrt 2 - π / 4 * |τ|)
        ).integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have h := norm_integral_le_of_norm_le hg (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      refine (hker (s + 1) (by simp [hτdef]) r hr).trans ?_
      have hre : (s + 1).re - 1 = σ := by simp [hσdef]
      rw [hre]
      exact mul_le_mul_of_nonneg_right (rpow_le_rpow hr.1.le hr.2.le hσ0.le) (exp_pos _).le)
    rw [ray_exp_integral (ell δ) (a ^ σ) (π / 4 * |τ|) a hL ha.le, ← hE] at h
    rw [norm_mul, hc]
    calc _ ≤ ell δ * (a ^ σ * (sqrt 2 / ell δ) *
          (E - exp (-(π / 4 * |τ|)))) :=
          mul_le_mul_of_nonneg_left h hL.le
      _ = sqrt 2 * a ^ σ * (E - exp (-(π / 4 * |τ|))) := by field_simp
      _ ≤ _ := by
          have : 0 ≤ sqrt 2 * a ^ σ := by positivity
          nlinarith [exp_pos (-(π / 4 * |τ|))]
  -- assemble
  have hrec := finite_ray_recurrence δ τ s a hσ0 ha
  have hsn : |τ| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hmain : ‖s‖ * ‖initialIntegral δ s‖ ≤
      (a ^ σ + a ^ (σ + 2) + sqrt 2 * a ^ σ) * E := by
    rw [← norm_mul]
    unfold initialIntegral
    rw [hrec]
    calc _ ≤ ‖contourKernel δ s (a * w) * (a * w) +
            ∫ r in Ioo 0 a, contourKernel δ (s + 2) (r * w) * w‖ +
          ‖(2 * π * Complex.I * δ) *
            ∫ r in Ioo 0 a, contourKernel δ (s + 1) (r * w) * w‖ := norm_sub_le _ _
      _ ≤ ‖contourKernel δ s (a * w) * (a * w)‖ +
            ‖∫ r in Ioo 0 a, contourKernel δ (s + 2) (r * w) * w‖ +
          ‖(2 * π * Complex.I * δ) *
            ∫ r in Ioo 0 a, contourKernel δ (s + 1) (r * w) * w‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ a ^ σ * E + a ^ (σ + 2) * E + sqrt 2 * a ^ σ * E := by gcongr
      _ = _ := by ring
  have hN := norm_nonneg (initialIntegral δ s)
  rw [div_mul_eq_mul_div, le_div_iff₀ hτ]
  calc ‖initialIntegral δ s‖ * |τ| ≤ ‖s‖ * ‖initialIntegral δ s‖ := by nlinarith
    _ ≤ _ := hmain
    _ = _ := by ring

/-- P0014 page 25, the conclusion after display 3.63, assembled with no sorry from the
named hypothesis A.33 and the LEAF `initial_ibp_bound`. The statement after the hypothesis
is word for word that of `Decomp639Contour.initial_segment_bound`.
CONDITIONAL ON `HelfgottA33` and on the LEAF `initial_ibp_bound`. -/
private theorem initial_segment_bound_of_A33 (hA : ∀ ρ : ℝ, 0 < ρ →
      (c0 ρ - 1 / sqrt 2) / (sqrt 2 * c1 ρ * ρ) ≤ 0.0763896 ∧
      (c0 ρ - 1 / sqrt 2) / (c1 ρ * sqrt ρ) ≤ 1 / 2) (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖initialIntegral δ s‖ ≤ firstCoefficient s.re |s.im| *
      exp (-0.4798 * |s.im|) := by
  have hd : δ ≠ 0 := by intro h; simp [h] at hsign
  have hτ : 0 < |s.im| := by linarith
  have hr := initialRadius_pos δ s.im hd hτ
  have hphase := initialRadius_phase_of_A33 hA δ s.im hd hτ
  have hrad := initialRadius_le_sqrt_of_A33 hA δ s.im hd hτ
  have hpre := initial_radius_prefactor s.re |s.im| (initialRadius δ s.im) hσ0.le hτ hr hrad
  have hexp := initial_phase_cost |s.im| (ell δ) (initialRadius δ s.im) (abs_nonneg _) hphase
  have hpre0 : 0 ≤ (initialRadius δ s.im ^ (s.re + 2) +
      (1 + sqrt 2) * initialRadius δ s.im ^ s.re) / |s.im| := by positivity
  have hF0 : 0 ≤ firstCoefficient s.re |s.im| := by
    unfold firstCoefficient; positivity
  calc _ ≤ _ := initial_ibp_bound δ s hσ0 hσ1 ht hsign
    _ ≤ _ := mul_le_mul hpre hexp (exp_pos _).le hF0


/-- LEAF: P0014 pages 24 to 25, displays 3.59 to 3.63 and the bound after 3.63.
Integration by parts on C1 gives the uniform first coefficient on the critical strip.
OPEN. The phase cost uses A.33 and the radius bound of display 3.61. -/
theorem initial_segment_bound (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖initialIntegral δ s‖ ≤ firstCoefficient s.re |s.im| *
      exp (-0.4798 * |s.im|) :=
  initial_segment_bound_of_A33 helfgottA33_holds δ s hσ0 hσ1 ht hsign

end LeanLab.HelfgottMajor.Decomp639Contour

#print axioms LeanLab.HelfgottMajor.Decomp639Contour.saddle_segment_bound
#print axioms LeanLab.HelfgottMajor.Decomp639Contour.initial_segment_bound
