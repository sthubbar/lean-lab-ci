import LeanLab.HelfgottMajor.Prep1121A33Window
import LeanLab.HelfgottMajor.Radius669
import LeanLab.HelfgottMajor.DQInitialSegmentBoundDecisions

/-!
P0014 page 67, display A.33, first line, and the route step
`Decomp639Contour.initial_segment_bound`.

Change of variables. With `υ = υ(ρ)` of display 3.25 and `u = 1/υ`, which lies in `(0,1)` for
`ρ > 0`, put `a = √(1+u)`, `b = √(1-u)`, `R = √(4-2u²)`. Then
`ρ = 2υ√(υ²-1)`, `Υ(ρ) = (2-u) a/(b u + R)` by the half angle formula for
`tan (arctan X / 2)`, `c0 = (a Υ + b)/√2`, `c1 ρ = 2(1+u) Υ/u`, and the first line of A.33 is
`a33G u ≤ 0.0763896`, which `Prep1121A33Cells` and `Prep1121A33Window` prove on `[0,1]`.
The paper instead runs bisection on `ρ ∈ [0.1, 25]` with hand bounds outside; here the same
statement is checked by certified interval arithmetic, so it is a faithful replacement of a
numerical step, not a new argument.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121A33Reduce

open Real LeanLab.HelfgottMajor.Decomp639Contour LeanLab.HelfgottMajor.Prep1121A33Cells

/-- P0014 page 16, display 3.25 and page 67, display A.33.
For `ρ > 0` the parameter `u = 1/υ(ρ)` lies in `(0,1)`. -/
theorem u_mem (ρ : ℝ) (hρ : 0 < ρ) : 0 < 1 / BookE.ups ρ ∧ 1 / BookE.ups ρ < 1 := by
  have hv := ups_gt_one ρ hρ
  exact ⟨by positivity, by rw [div_lt_one (by linarith)]; exact hv⟩

/-- P0014 page 16, display 3.25.
`√(1+ρ²) = 2υ² - 1` and `ρ² = 4υ²(υ²-1)`. -/
theorem ups_sq (ρ : ℝ) (hρ : 0 < ρ) :
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
theorem tan_half_arctan (X : ℝ) (hX : 0 < X) :
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
theorem upsilon_u (ρ : ℝ) (hρ : 0 < ρ) :
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
theorem c0_u (ρ : ℝ) (hρ : 0 < ρ) :
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
theorem c1_mul_rho_u (ρ : ℝ) (hρ : 0 < ρ) :
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
is `a33G u`. Checked by a Groebner reduction in sympy. -/
theorem a33_quotient_eq (u U c0v c1r : ℝ) (hu0 : 0 < u) (hu1 : u < 1)
    (hU : U = (2 - u) * √(1 + u) / (√(1 - u) * u + √(4 - 2 * u ^ 2)))
    (h0 : c0v = (√(1 + u) * U + √(1 - u)) / √2)
    (h1 : c1r = 2 * (1 + u) * U / u) :
    (c0v - 1 / √2) / (√2 * c1r) = a33G u := by
  subst hU h0 h1
  unfold a33G
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
theorem a33_first_eq (ρ : ℝ) (hρ : 0 < ρ) :
    (c0 ρ - 1 / √2) / (√2 * c1 ρ * ρ) = a33G (1 / BookE.ups ρ) := by
  have hu := u_mem ρ hρ
  rw [mul_assoc]
  exact a33_quotient_eq _ _ _ _ hu.1 hu.2 (upsilon_u ρ hρ) (c0_u ρ hρ) (c1_mul_rho_u ρ hρ)

/-- P0014 page 67, display A.33, first line:
`(c0 - 1/√2)/(√2 c1 ρ) ≤ 0.0763896` for every `ρ > 0`. -/
theorem a33_first (ρ : ℝ) (hρ : 0 < ρ) :
    (c0 ρ - 1 / √2) / (√2 * c1 ρ * ρ) ≤ 0.0763896 := by
  have hB : ((a33B : ℚ) : ℝ) = 0.0763896 := by norm_num [a33B]
  rw [a33_first_eq ρ hρ, ← hB]
  obtain ⟨h0, h1⟩ := u_mem ρ hρ
  by_cases hw : 1 / 2 ≤ 1 / BookE.ups ρ ∧ 1 / BookE.ups ρ ≤ 4 / 5
  · exact Prep1121A33Window.a33G_le_window _ hw.1 hw.2
  · apply a33G_le_outside _ h0 h1.le
    by_contra hc
    push_neg at hc
    exact hw ⟨hc.1, hc.2⟩

/-- P0014 page 67, display A.33, both lines: the named hypothesis of
`DQInitialSegmentBoundDecisions` holds. The second line is `Radius669.a33_second`. -/
theorem helfgottA33_holds : DQInitialSegmentBound.HelfgottA33 :=
  fun ρ hρ => ⟨a33_first ρ hρ, Radius669.a33_second ρ hρ⟩

/-- The route step `Decomp639Contour.initial_segment_bound`, P0014 pages 24 and 25,
displays 3.59 to 3.63, with exactly the sealed statement, from A.33 and the proved
integration by parts `DQInitialSegmentBound.initial_ibp_bound`. -/
theorem initial_segment_bound_step : type_of% @Decomp639Contour.initial_segment_bound :=
  DQInitialSegmentBound.initial_segment_bound_twin helfgottA33_holds

end LeanLab.HelfgottMajor.Prep1121A33Reduce

#print axioms LeanLab.HelfgottMajor.Prep1121A33Reduce.a33_first
#print axioms LeanLab.HelfgottMajor.Prep1121A33Reduce.helfgottA33_holds
#print axioms LeanLab.HelfgottMajor.Prep1121A33Reduce.initial_segment_bound_step
