import Mathlib
import LeanLab.Pintz2018.Section9

/-!
# Pintz 2018, certificate targets for the paper's own numerics

Two SEALED TARGET statements recording numerical claims of arXiv 1804.09084v2:
Lemma 5, display (6.25) p. 29, which is Condition 2 (4.26)-(4.27) p. 15 for `G` of (4.19) p. 14
with `A0 = 13`, `B0 = 1.25`; and the Case 1 extremal bound of Section 9, displays (9.7)-(9.13)
pp. 39-40, with `λ0 = 0.68`, `x = 0.7`, `ϕ = 1/3`, `Λ0 = 1.311`.
These are TARGET certificates of the paper's numerics, not original results.
AI wrote the Lean code.
-/

namespace LeanLab.Pintz2018

open Finset

/-- `g(u) = (2-u)^3 (4+6u+u^2)/30`, display (4.18) p. 14. -/
noncomputable def gP (u : ℝ) : ℝ := (2 - u) ^ 3 * (4 + 6 * u + u ^ 2) / 30

/-- `G(z) = ∫_0^2 e^{-zu} g(u) du`, display (4.19) p. 14, complex argument. -/
noncomputable def Gc (z : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..2, Complex.exp (-z * u) * (gP u : ℂ)

/-- `G` of (4.19) on the real line, as a real integral. -/
noncomputable def GR (y : ℝ) : ℝ := ∫ u in (0 : ℝ)..2, Real.exp (-y * u) * gP u

/-- Case 1 constants of (9.7)-(9.9) p. 39-40: `G(-λ0/x)` with `λ0 = 0.68`, `x = 0.7`. -/
noncomputable def Gm1 : ℝ := GR (-(0.68 / 0.7))
/-- `G((Λ0-λ0)/x)` with `Λ0 = 1.311`. -/
noncomputable def GL1 : ℝ := GR ((1.311 - 0.68) / 0.7)
/-- `ξ = f(0)ϕ/(2F(-λ0))`, (4.31) p. 16, with `f(0) = 16x/15` (4.25) and `ϕ = 1/3` p. 39. -/
noncomputable def xi1 : ℝ := (16 * 0.7 / 15) * (1 / 3) / (2 * Gm1)
/-- `ψ = F(Λ0-λ0)/F(-λ0)`, (4.31) p. 16. -/
noncomputable def psi1 : ℝ := GL1 / Gm1
/-- `Δ = ψ - ξ`, (4.31) p. 16. -/
noncomputable def Delta1 : ℝ := psi1 - xi1
/-- `D0 = F(-λ0)(1-ξ)/(2Δ)`, the bound on `∑ (G((λj-λ0)/x) - G((Λ0-λ0)/x))` obtained from
Theorem J (4.36) p. 17 as in (9.9) p. 40; the paper prints `D0 ≤ 2.4438`. -/
noncomputable def D01 : ℝ := Gm1 * (1 - xi1) / (2 * Delta1)

/-- The real part of the transform, in the coordinates of display 6.4. -/
theorem Gc_re_integral (x t : ℝ) :
    (Gc ((x : ℂ) + (t : ℂ) * Complex.I)).re =
      ∫ u in (0 : ℝ)..2, Real.exp (-x * u) * gP u * Real.cos (t * u) := by
  have hc : Continuous (fun u : ℝ =>
      Complex.exp (-((x : ℂ) + (t : ℂ) * Complex.I) * u) * (gP u : ℂ)) := by
    unfold gP
    fun_prop
  unfold Gc
  have hr := intervalIntegral.intervalIntegral_re
    (𝕜 := ℂ) (μ := MeasureTheory.volume) (a := 0) (b := 2)
    (hc.intervalIntegrable 0 2)
  refine hr.symm.trans ?_
  apply intervalIntegral.integral_congr
  intro u _
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Real.cos_neg]
  ring

/-- The real and complex definitions agree on the real axis, display 4.19. -/
theorem Gc_ofReal_re (x : ℝ) : (Gc (x : ℂ)).re = GR x := by
  simpa [GR] using Gc_re_integral x 0

/-- Positivity of the real transform, display 6.3. -/
theorem GR_pos (x : ℝ) : 0 < GR x := by
  unfold GR
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((by unfold gP; fun_prop :
      Continuous (fun u : ℝ => Real.exp (-x * u) * gP u)).intervalIntegrable _ _)
    ?_ (by norm_num)
  intro u hu
  apply mul_pos (Real.exp_pos _)
  unfold gP
  have : 0 < 2 - u := by linarith [hu.2]
  have hu0 : 0 < u := hu.1
  positivity

/-- The double-integral comparison underlying Lemma 4, displays 6.19 to 6.24. -/
theorem Gc_ratio_mono_of_cos_antitone (t x y : ℝ) (hxy : x ≤ y)
    (hcos : AntitoneOn (fun u : ℝ => Real.cos (t * u)) (Set.Icc 0 2)) :
    (Gc ((x : ℂ) + (t : ℂ) * Complex.I)).re / GR x ≤
      (Gc ((y : ℂ) + (t : ℂ) * Complex.I)).re / GR y := by
  let f := fun u : ℝ => Real.exp (-y * u) * gP u
  let g := fun u : ℝ => Real.exp (-x * u) * gP u
  let c := fun u : ℝ => Real.cos (t * u)
  have hf : Continuous f := by dsimp [f]; unfold gP; fun_prop
  have hg : Continuous g := by dsimp [g]; unfold gP; fun_prop
  have hc : Continuous c := by dsimp [c]; fun_prop
  have hgp : ∀ u ∈ Set.Icc (0 : ℝ) 2, 0 ≤ gP u := by
    intro u hu
    unfold gP
    have h0 := hu.1
    have h2 : 0 ≤ 2 - u := by linarith [hu.2]
    positivity
  have hweight : ∀ u v : ℝ,
      f u * g v - g u * f v =
        gP u * gP v * (Real.exp (-y * u - x * v) - Real.exp (-x * u - y * v)) := by
    intro u v
    dsimp [f, g]
    simp only [sub_eq_add_neg, Real.exp_add, neg_mul]
    ring
  have hcross : ∀ u ∈ Set.Icc (0 : ℝ) 2, ∀ v ∈ Set.Icc (0 : ℝ) 2,
      0 ≤ (f u * g v - g u * f v) * (c u - c v) := by
    intro u hu v hv
    rw [hweight]
    rcases le_total u v with huv | hvu
    · have he : Real.exp (-x * u - y * v) ≤ Real.exp (-y * u - x * v) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr huv)]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (hgp u hu) (hgp v hv)) (sub_nonneg.mpr he))
        (sub_nonneg.mpr (hcos hu hv huv))
    · have he : Real.exp (-y * u - x * v) ≤ Real.exp (-x * u - y * v) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hvu)]
      exact mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hgp u hu) (hgp v hv))
          (sub_nonpos.mpr he))
        (sub_nonpos.mpr (hcos hv hu hvu))
  have hinner (u : ℝ) :
      (∫ v in (0 : ℝ)..2, (f u * g v - g u * f v) * (c u - c v)) =
        f u * c u * (∫ v in (0 : ℝ)..2, g v) -
        g u * c u * (∫ v in (0 : ℝ)..2, f v) -
        f u * (∫ v in (0 : ℝ)..2, g v * c v) +
        g u * (∫ v in (0 : ℝ)..2, f v * c v) := by
    calc
      _ = ∫ v in (0 : ℝ)..2,
          (f u * c u * g v - g u * c u * f v) -
            f u * (g v * c v) + g u * (f v * c v) := by
        apply intervalIntegral.integral_congr
        intro v _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
          intervalIntegral.integral_sub]
        · simp only [intervalIntegral.integral_const_mul]
        all_goals apply Continuous.intervalIntegrable; fun_prop
  have hdouble : 0 ≤ ∫ u in (0 : ℝ)..2,
      (f u * c u * (∫ v in (0 : ℝ)..2, g v) -
        g u * c u * (∫ v in (0 : ℝ)..2, f v) -
        f u * (∫ v in (0 : ℝ)..2, g v * c v) +
        g u * (∫ v in (0 : ℝ)..2, f v * c v)) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    rw [← hinner]
    exact intervalIntegral.integral_nonneg (by norm_num) (hcross u hu)
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_sub] at hdouble
  · simp only [intervalIntegral.integral_mul_const] at hdouble
    rw [Gc_re_integral, Gc_re_integral, div_le_div_iff₀ (GR_pos x) (GR_pos y)]
    change (∫ u in (0 : ℝ)..2, g u * c u) * (∫ u in (0 : ℝ)..2, f u) ≤
      (∫ u in (0 : ℝ)..2, f u * c u) * (∫ u in (0 : ℝ)..2, g u)
    nlinarith
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-- Lemma 4 on page 28, for the kernel in display 4.19. -/
theorem Gc_ratio_mono_small_frequency (t x y : ℝ) (hxy : x ≤ y)
    (ht : |t| ≤ Real.pi / 2) :
    (Gc ((x : ℂ) + (t : ℂ) * Complex.I)).re / GR x ≤
      (Gc ((y : ℂ) + (t : ℂ) * Complex.I)).re / GR y := by
  apply Gc_ratio_mono_of_cos_antitone t x y hxy
  intro u hu v hv huv
  have hcos (w : ℝ) : Real.cos (t * w) = Real.cos (|t| * w) := by
    rcases le_total 0 t with ht0 | ht0
    · rw [abs_of_nonneg ht0]
    · rw [abs_of_nonpos ht0, neg_mul, Real.cos_neg]
  change Real.cos (t * v) ≤ Real.cos (t * u)
  rw [hcos, hcos]
  apply Real.cos_le_cos_of_nonneg_of_le_pi
    (mul_nonneg (abs_nonneg t) hu.1) ?_
    (mul_le_mul_of_nonneg_left huv (abs_nonneg t))
  nlinarith [mul_le_mul_of_nonneg_left hv.2 (abs_nonneg t)]

/-- The denominator-cleared complex transform in display 6.1, including its value at zero. -/
theorem Gc_scaled_formula (z : ℂ) :
    z ^ 6 * Gc z = 16 / 15 * z ^ 5 - 8 / 3 * z ^ 3 + 4 * z ^ 2 - 4 +
      4 * Complex.exp (-2 * z) * (z + 1) ^ 2 := by
  let c5 := z ^ 5 / 30
  let c4 := z ^ 4 / 6
  let c3 := -2 * z ^ 5 / 3 + 2 * z ^ 3 / 3
  let c2 := 4 * z ^ 5 / 3 - 2 * z ^ 4 + 2 * z ^ 2
  let c1 := 8 * z ^ 4 / 3 - 4 * z ^ 3 + 4 * z
  let c0 := -16 * z ^ 5 / 15 + 8 * z ^ 3 / 3 - 4 * z ^ 2 + 4
  let p := fun u : ℂ => c5 * u ^ 5 + c4 * u ^ 4 + c3 * u ^ 3 +
    c2 * u ^ 2 + c1 * u + c0
  have hp (u : ℂ) : HasDerivAt p
      (5 * c5 * u ^ 4 + 4 * c4 * u ^ 3 + 3 * c3 * u ^ 2 + 2 * c2 * u + c1) u := by
    convert ((((((hasDerivAt_pow 5 u).const_mul c5).add
      ((hasDerivAt_pow 4 u).const_mul c4)).add
      ((hasDerivAt_pow 3 u).const_mul c3)).add
      ((hasDerivAt_pow 2 u).const_mul c2)).add
      ((hasDerivAt_id u).const_mul c1)).add_const c0 using 1
    · rfl
    · simp
      ring
  have hF (u : ℝ) : HasDerivAt (fun u : ℝ => Complex.exp (-z * u) * p u)
      (z ^ 6 * (Complex.exp (-z * u) * (gP u : ℂ))) u := by
    convert ((((hasDerivAt_id (u : ℂ)).const_mul (-z)).cexp).mul (hp u)).comp_ofReal using 1
    · rfl
    · dsimp [p, c5, c4, c3, c2, c1, c0]
      unfold gP
      push_cast
      ring
  calc
    z ^ 6 * Gc z = ∫ u in (0 : ℝ)..2, z ^ 6 * (Complex.exp (-z * u) * (gP u : ℂ)) := by
      rw [intervalIntegral.integral_const_mul]
      rfl
    _ = Complex.exp (-z * 2) * p 2 - Complex.exp (-z * 0) * p 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hF u)
        ((by unfold gP; fun_prop : Continuous
          (fun u : ℝ => z ^ 6 * (Complex.exp (-z * u) * (gP u : ℂ)))).intervalIntegrable _ _)
    _ = _ := by
      rw [show -z * 2 = -2 * z by ring]
      dsimp [p, c5, c4, c3, c2, c1, c0]
      simp
      ring

/-- The explicit expression of display 6.1 away from its removable singularity. -/
theorem Gc_formula (z : ℂ) (hz : z ≠ 0) :
    Gc z = 16 / (15 * z) - 8 / (3 * z ^ 3) + 4 / z ^ 4 - 4 / z ^ 6 +
      4 * Complex.exp (-2 * z) * (z + 1) ^ 2 / z ^ 6 := by
  apply (mul_left_cancel₀ (pow_ne_zero 6 hz))
  rw [Gc_scaled_formula]
  field_simp

/-- SEALED TARGET certificate of Condition 2 for `G`, Lemma 5, arXiv 1804.09084v2 p.29
display 6.25; numerically tested min margin 0 at the corner a = b = 0 only, slopes at least
0.0075 in b and 0.024 in a on the box pi/2 < |t| < 8 -/
theorem G_condition2 (a b t : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 13) (hb0 : 0 ≤ b) (hb : b ≤ 5 / 4) :
    (Gc ((-b : ℂ) + (t : ℂ) * Complex.I)).re / (Gc (-b : ℂ)).re
      ≤ (Gc ((a : ℂ) + (t : ℂ) * Complex.I)).re / (Gc (a : ℂ)).re := by
  by_cases hab : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    simp
  by_cases ht : |t| ≤ Real.pi / 2
  · simpa only [← Complex.ofReal_neg, Gc_ofReal_re] using
      Gc_ratio_mono_small_frequency t (-b) a (by linarith) ht
  · have ht0 : t ≠ 0 := by
      intro ht0
      subst t
      apply ht
      simp only [abs_zero]
      positivity
    have hz (x : ℝ) : (x : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      simp at hi
      exact ht0 hi
    simp only [← Complex.ofReal_neg, Gc_ofReal_re]
    rw [Gc_formula _ (hz (-b)), Gc_formula _ (hz a)]
    apply (div_le_div_iff₀ (GR_pos (-b)) (GR_pos a)).mpr
    sorry

/-- Vacuity instance for `G_condition2`: the hypotheses hold at `a = b = 0`, and there the
inequality is an equality. -/
theorem G_condition2_vacuity (t : ℝ) :
    (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 13 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 5 / 4 ∧
    (Gc ((-(0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re / (Gc (-(0 : ℝ) : ℂ)).re
      ≤ (Gc (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re / (Gc ((0 : ℝ) : ℂ)).re := by
  refine ⟨le_rfl, by norm_num, le_rfl, by norm_num, ?_⟩
  simp

/-- The denominator-cleared real specialization of display 6.1, valid also at zero. -/
theorem GR_scaled_formula (y : ℝ) :
    y ^ 6 * GR y = 16 / 15 * y ^ 5 - 8 / 3 * y ^ 3 + 4 * y ^ 2 - 4 +
      4 * Real.exp (-2 * y) * (y + 1) ^ 2 := by
  have h := congrArg Complex.re (Gc_scaled_formula (y : ℂ))
  norm_num [← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im, Complex.exp_re,
    pow_two, Gc_ofReal_re] at h
  simpa only [pow_two, neg_mul] using h

/-- Real-axis monotonicity in display 6.3. -/
theorem GR_antitone : Antitone GR := by
  intro x y hxy
  unfold GR
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((by unfold gP; fun_prop :
      Continuous (fun u : ℝ => Real.exp (-y * u) * gP u)).intervalIntegrable _ _)
    ((by unfold gP; fun_prop :
      Continuous (fun u : ℝ => Real.exp (-x * u) * gP u)).intervalIntegrable _ _)
  intro u hu
  have h0 := hu.1
  have h2 : 0 ≤ 2 - u := by linarith [hu.2]
  have hgp : 0 ≤ gP u := by unfold gP; positivity
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (by nlinarith)) hgp

/-- Certified enclosures of the transforms used in display 9.8. -/
theorem case1_transform_bounds :
    1.5699 < Gm1 ∧ Gm1 < 1.57 ∧ 0.5881937 < GL1 ∧ GL1 < 0.5881938 := by
  have helo := exp_ge_T (68 / 35) (by norm_num)
  have hehi := exp_le_T (68 / 35) (by norm_num) (by norm_num)
  have hLlo := expneg_lower (631 / 350) (by norm_num) (by norm_num)
  have hLhi := expneg_upper (631 / 350) (by norm_num)
  simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    at helo hehi hLlo hLhi
  norm_num at helo hehi hLlo hLhi
  have he : 6.97866 < Real.exp (68 / 35) ∧ Real.exp (68 / 35) < 6.97867 := by
    constructor <;> linarith
  have hL : 0.16482727973 < Real.exp (-(631 / 350)) ∧
      Real.exp (-(631 / 350)) < 0.16482727974 := by
    constructor <;> linarith
  have hm := GR_scaled_formula (-(0.68 / 0.7))
  have hl := GR_scaled_formula ((1.311 - 0.68) / 0.7)
  norm_num at hm hl
  dsimp [Gm1, GL1]
  norm_num
  constructor
  · nlinarith [he.1]
  constructor
  · nlinarith [he.2]
  constructor <;> nlinarith [hL.1, hL.2]

/-- A rational upper bound for the budget in display 9.9. -/
theorem D01_lt : D01 < 2.447 := by
  obtain ⟨hmlo, hmhi, hLlo, _⟩ := case1_transform_bounds
  have hmpos : 0 < Gm1 := by linarith
  have hxi : xi1 * Gm1 = 28 / 225 := by
    unfold xi1
    field_simp
    ring
  have hdelta : Delta1 * Gm1 = GL1 - 28 / 225 := by
    unfold Delta1 psi1
    rw [sub_mul, div_mul_cancel₀ _ hmpos.ne', hxi]
  have hdpos : 0 < Delta1 := by nlinarith
  unfold D01
  rw [div_lt_iff₀ (mul_pos (by norm_num) hdpos)]
  apply (mul_lt_mul_iff_right₀ hmpos).mp
  nlinarith [mul_nonneg (sub_nonneg.mpr hmhi.le) hmpos.le]

/-- The Laplace cost is concave in the exponential objective coordinate, as in 8.11. -/
theorem GR_E_mix (l₀ l₁ l a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hl : E l = a * E l₀ + b * E l₁) :
    a * GR ((l₀ - 0.68) / 0.7) + b * GR ((l₁ - 0.68) / 0.7) ≤
      GR ((l - 0.68) / 0.7) := by
  have hkernel (r u : ℝ) :
      Real.exp (-((r - 0.68) / 0.7) * u) * gP u =
        (Real.exp ((0.68 / 0.7) * u) * gP u) * (E r) ^ ((2 / 5 : ℝ) * u) := by
    rw [Real.rpow_def_of_pos (E_pos _), show Real.log (E r) = -(25 / 7) * r by
      exact Real.log_exp _]
    rw [show -((r - 0.68) / 0.7) * u =
      (0.68 / 0.7) * u + (-(25 / 7) * r) * ((2 / 5 : ℝ) * u) by ring, Real.exp_add]
    ring
  unfold GR
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add]
  · apply intervalIntegral.integral_mono_on (by norm_num)
      ((by unfold gP; fun_prop : Continuous (fun u : ℝ =>
        a * (Real.exp (-((l₀ - 0.68) / 0.7) * u) * gP u) +
        b * (Real.exp (-((l₁ - 0.68) / 0.7) * u) * gP u))).intervalIntegrable _ _)
      ((by unfold gP; fun_prop : Continuous (fun u : ℝ =>
        Real.exp (-((l - 0.68) / 0.7) * u) * gP u)).intervalIntegrable _ _)
    intro u hu
    have h0 := hu.1
    have h2 : 0 ≤ 2 - u := by linarith [hu.2]
    have hw : 0 ≤ Real.exp ((0.68 / 0.7) * u) * gP u := by unfold gP; positivity
    have hc := (Real.concaveOn_rpow
      (show 0 ≤ (2 / 5 : ℝ) * u by positivity)
      (show (2 / 5 : ℝ) * u ≤ 1 by linarith [hu.2])).2
      (show E l₀ ∈ Set.Ici 0 from (E_pos _).le)
      (show E l₁ ∈ Set.Ici 0 from (E_pos _).le) ha hb hab
    simp only [smul_eq_mul] at hc
    rw [← hl] at hc
    rw [hkernel, hkernel, hkernel]
    nlinarith [mul_le_mul_of_nonneg_left hc hw]
  all_goals apply Continuous.intervalIntegrable; unfold gP; fun_prop

/-- Endpoint affine upper bounds propagate through the concave cost in display 8.11. -/
theorem case1_chord (lo hi l m c : ℝ) (hlohi : lo < hi)
    (hlo : lo ≤ l) (hhi : l ≤ hi) (hm : 0 ≤ m)
    (hleft : E lo - E 1.311 ≤ m * (GR ((lo - 0.68) / 0.7) - GL1) + c)
    (hright : E hi - E 1.311 ≤ m * (GR ((hi - 0.68) / 0.7) - GL1) + c) :
    E l - E 1.311 ≤ m * (GR ((l - 0.68) / 0.7) - GL1) + c := by
  have hE : StrictAnti E := by
    intro x y hxy
    unfold E
    exact Real.exp_lt_exp.mpr (by linarith)
  have hd : 0 < E lo - E hi := sub_pos.mpr (hE hlohi)
  let a := (E l - E hi) / (E lo - E hi)
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr (hE.antitone hhi)) hd.le
  have ha1 : a ≤ 1 := (div_le_one hd).mpr (by linarith [hE.antitone hlo])
  have hb : 0 ≤ 1 - a := by linarith
  have hmix : E l = a * E lo + (1 - a) * E hi := by
    have h := div_mul_cancel₀ (E l - E hi) hd.ne'
    change a * (E lo - E hi) = E l - E hi at h
    nlinarith
  have hcost := GR_E_mix lo hi l a (1 - a) ha hb (by ring) hmix
  calc
    E l - E 1.311 = a * (E lo - E 1.311) + (1 - a) * (E hi - E 1.311) := by
      nlinarith [hmix]
    _ ≤ a * (m * (GR ((lo - 0.68) / 0.7) - GL1) + c) +
        (1 - a) * (m * (GR ((hi - 0.68) / 0.7) - GL1) + c) :=
      add_le_add (mul_le_mul_of_nonneg_left hleft ha) (mul_le_mul_of_nonneg_left hright hb)
    _ = m * (a * GR ((lo - 0.68) / 0.7) + (1 - a) * GR ((hi - 0.68) / 0.7) - GL1) + c := by
      ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hcost hm]

/-- Additional real transform enclosures at the two interior chord endpoints. -/
theorem case1_interior_bounds :
    0.8746954 < GR ((0.702 - 0.68) / 0.7) ∧
    GR ((0.702 - 0.68) / 0.7) < 0.8746955 ∧
    0.712269 < GR ((1 - 0.68) / 0.7) := by
  have hs := Real.exp_bound (x := -(11 / 175)) (by norm_num) (n := 15) (by norm_num)
  have hm := Real.exp_bound (x := -(32 / 35)) (by norm_num) (n := 20) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hs hm
  norm_num at hs hm
  have hslo := (abs_le.mp hs).1
  have hshi := (abs_le.mp hs).2
  have hmlo := (abs_le.mp hm).1
  have hform := GR_scaled_formula ((0.702 - 0.68) / 0.7)
  have hform1 := GR_scaled_formula ((1 - 0.68) / 0.7)
  norm_num at hform hform1 ⊢
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The unshifted Laplace transform in display 4.25. -/
theorem GR_zero : GR 0 = 8 / 9 := by
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) 2,
      HasDerivAt (fun u : ℝ => (32 * u - 40 / 3 * u ^ 3 + 5 * u ^ 4 - 1 / 6 * u ^ 6) / 30)
        (gP x) x := by
    intro x _
    have h := (((((hasDerivAt_id x).const_mul 32).sub ((hasDerivAt_pow 3 x).const_mul (40 / 3))).add
      ((hasDerivAt_pow 4 x).const_mul 5)).sub ((hasDerivAt_pow 6 x).const_mul (1 / 6))).div_const 30
    convert h using 1
    · funext y; simp
    · unfold gP; simp; ring
  simp only [GR, neg_zero, zero_mul, Real.exp_zero, one_mul]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by unfold gP; fun_prop : Continuous gP).intervalIntegrable _ _)]
  norm_num

/-- Rational affine bounds at the endpoints of the Case 1 chords. -/
theorem case1_chord_endpoints :
    (E 0.68 - E 1.311 ≤ 0.3289 * (GR ((0.68 - 0.68) / 0.7) - GL1) - 0.0199) ∧
    (E 0.702 - E 1.311 ≤ 0.3289 * (GR ((0.702 - 0.68) / 0.7) - GL1) - 0.0219) ∧
    (E 1 - E 1.311 ≤ 0.3289 * (GR ((1 - 0.68) / 0.7) - GL1) - 0.0219) ∧
    (E 1 - E 1.311 ≤ 0.1521 * (GR ((1 - 0.68) / 0.7) - GL1)) := by
  have h1 := E_upper 0.68 (by norm_num) (by norm_num)
  have h2 := E_upper 0.702 (by norm_num) (by norm_num)
  have hmid := E_upper 1 (by norm_num) (by norm_num)
  have h3 := E_lower 1.311 (by norm_num) (by norm_num)
  simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1 h2 hmid h3
  norm_num at h1 h2 hmid h3
  have hw1 : E 0.68 - E 1.311 ≤ 0.078904 := by linarith
  have hw2 : E 0.702 - E 1.311 ≤ 0.072242 := by linarith
  have hwmid : E 1 - E 1.311 ≤ 0.018857 := by linarith
  obtain ⟨_, _, hLlo, hLhi⟩ := case1_transform_bounds
  obtain ⟨hslo, _, hmlo⟩ := case1_interior_bounds
  norm_num only [sub_self, zero_div, GR_zero]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Two affine majorants of the objective in terms of the Laplace cost. -/
theorem case1_piecewise_bound (l : ℝ) (hlo : 0.68 ≤ l) (hhi : l ≤ 1.311) :
    E l - E 1.311 ≤ 0.1521 * (GR ((l - 0.68) / 0.7) - GL1) +
      (if l < 1 then 0.1768 * (GR ((l - 0.68) / 0.7) - GL1) - 0.0219 else 0) +
      (if l < 0.702 then 0.002 else 0) := by
  obtain ⟨hleft, hsmall, hmid, hmid'⟩ := case1_chord_endpoints
  by_cases h : l < 1
  · by_cases hs : l < 0.702
    · have hbound := case1_chord 0.68 0.702 l 0.3289 (-0.0199)
        (by norm_num) hlo hs.le (by norm_num) hleft (by linarith)
      simp only [h, hs, ite_true]
      linarith
    · have hbound := case1_chord 0.702 1 l 0.3289 (-0.0219)
        (by norm_num) (le_of_not_gt hs) h.le (by norm_num) hsmall hmid
      simp only [h, hs, ite_true, ite_false]
      linarith
  · have hs : ¬ l < 0.702 := by linarith
    have hbound := case1_chord 1 1.311 l 0.1521 0
      (by norm_num) (le_of_not_gt h) hhi (by norm_num) (by linarith)
      (by simp [GL1])
    simp only [h, hs, ite_false]
    linarith

/-- Caps on the individual costs from display 9.11. -/
theorem case1_cost_cap (l : ℝ) (hlo : 0.68 ≤ l) :
    GR ((l - 0.68) / 0.7) - GL1 ≤ 0.286502 + if l < 0.702 then 0.014194 else 0 := by
  obtain ⟨_, _, hLlo, _⟩ := case1_transform_bounds
  obtain ⟨_, hshi, _⟩ := case1_interior_bounds
  by_cases hs : l < 0.702
  · have h := GR_antitone (show 0 ≤ (l - 0.68) / 0.7 from
      div_nonneg (by linarith) (by norm_num))
    rw [GR_zero] at h
    simp only [hs, ite_true]
    linarith
  · have h := GR_antitone
      (show (0.702 - 0.68) / 0.7 ≤ (l - 0.68) / 0.7 from
        div_le_div_of_nonneg_right (by linarith) (by norm_num))
    simp only [hs, ite_false]
    linarith

/-- SEALED TARGET certificate of the Case 1 bound `S' < 0.612`, arXiv 1804.09084v2 p.40
display 9.13, with the constraints of (9.11) from Theorems E and F; numerically tested
maximum 0.6105899 by the Theorem K greedy and by direct optimisation over N up to 20 -/
theorem pintz_section9_certificate {ι : Type*} (s : Finset ι) (l : ι → ℝ)
    (hlo : ∀ j ∈ s, 0.68 ≤ l j) (hhi : ∀ j ∈ s, l j ≤ 1.311)
    (htwo : (s.filter fun j => l j < 0.702).card ≤ 2)
    (hD : ∑ j ∈ s, (GR ((l j - 0.68) / 0.7) - GL1) ≤ D01) :
    ∑ j ∈ s, (E (l j) - E 1.311) < 0.612 := by
  classical
  let c := fun j => GR ((l j - 0.68) / 0.7) - GL1
  let u := s.filter fun j => l j < 1
  let v := s.filter fun j => l j < 0.702
  have hbudget : ∑ j ∈ s, c j < 2.447 := lt_of_le_of_lt hD D01_lt
  have htwo' : (v.card : ℝ) ≤ 2 := by exact_mod_cast htwo
  have hpoint : ∀ j ∈ s, E (l j) - E 1.311 ≤ 0.1521 * c j +
      (if l j < 1 then 0.1768 * c j - 0.0219 else 0) +
      (if l j < 0.702 then 0.002 else 0) := by
    intro j hj
    exact case1_piecewise_bound (l j) (hlo j hj) (hhi j hj)
  have hsum := Finset.sum_le_sum hpoint
  have hsum_eq : (∑ j ∈ s, (0.1521 * c j +
      (if l j < 1 then 0.1768 * c j - 0.0219 else 0) +
      (if l j < 0.702 then 0.002 else 0))) =
      0.1521 * (∑ j ∈ s, c j) + 0.1768 * (∑ j ∈ u, c j) -
        0.0219 * u.card + 0.002 * v.card := by
    simp only [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, u, v]
    ring
  rw [hsum_eq] at hsum
  have hfilter : u.filter (fun j => l j < 0.702) = v := by
    ext j
    simp only [u, v, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hj, _⟩, hs⟩
      exact ⟨hj, hs⟩
    · rintro ⟨hj, hs⟩
      exact ⟨⟨hj, by linarith⟩, hs⟩
  have hcap : (∑ j ∈ u, c j) ≤ 0.286502 * u.card + 0.014194 * v.card := by
    calc
      (∑ j ∈ u, c j) ≤ ∑ j ∈ u,
          (0.286502 + if l j < 0.702 then 0.014194 else 0) := by
        apply Finset.sum_le_sum
        intro j hj
        exact case1_cost_cap (l j) (hlo j (Finset.mem_filter.mp hj).1)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, hfilter]
        simp [mul_comm]
  have hnonneg : ∀ j ∈ s, 0 ≤ c j := by
    intro j hj
    apply sub_nonneg.mpr
    apply GR_antitone
    exact div_le_div_of_nonneg_right (by linarith [hhi j hj]) (by norm_num)
  have hsub : (∑ j ∈ u, c j) ≤ ∑ j ∈ s, c j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun j hj _ => hnonneg j hj)
  by_cases hn : u.card ≤ 8
  · have hn' : (u.card : ℝ) ≤ 8 := by exact_mod_cast hn
    linarith
  · have hn' : (9 : ℝ) ≤ u.card := by exact_mod_cast (show 9 ≤ u.card by omega)
    linarith

/-! ### Vacuity for `pintz_section9_certificate` -/

theorem gP_nonneg (u : ℝ) (h0 : 0 ≤ u) (h2 : u ≤ 2) : 0 ≤ gP u := by
  unfold gP
  have : 0 ≤ 2 - u := by linarith
  positivity

theorem gP_cont : Continuous gP := by
  unfold gP; fun_prop

attribute [fun_prop] gP_cont

theorem gP_integral : ∫ u in (0 : ℝ)..2, gP u = 8 / 9 := by
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) 2,
      HasDerivAt (fun u : ℝ => (32 * u - 40 / 3 * u ^ 3 + 5 * u ^ 4 - 1 / 6 * u ^ 6) / 30)
        (gP x) x := by
    intro x _
    have h := (((((hasDerivAt_id x).const_mul 32).sub ((hasDerivAt_pow 3 x).const_mul (40 / 3))).add
      ((hasDerivAt_pow 4 x).const_mul 5)).sub ((hasDerivAt_pow 6 x).const_mul (1 / 6))).div_const 30
    convert h using 1
    · funext y; simp
    · unfold gP; simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (gP_cont.intervalIntegrable _ _)]
  norm_num

theorem GR_lower_neg (y : ℝ) (hy : y ≤ 0) : 8 / 9 ≤ GR y := by
  rw [← gP_integral]
  unfold GR
  apply intervalIntegral.integral_mono_on (by norm_num) (gP_cont.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun u => Real.exp (-y * u) * gP u).intervalIntegrable _ _)
  intro u hu
  have h1 : 1 ≤ Real.exp (-y * u) := Real.one_le_exp (by nlinarith [hu.1])
  nlinarith [gP_nonneg u hu.1 hu.2]

theorem GR_lower_pos (y : ℝ) (hy : 0 ≤ y) : Real.exp (-(2 * y)) * (8 / 9) ≤ GR y := by
  rw [← gP_integral, ← intervalIntegral.integral_const_mul]
  unfold GR
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((by fun_prop : Continuous fun u => Real.exp (-(2 * y)) * gP u).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun u => Real.exp (-y * u) * gP u).intervalIntegrable _ _)
  intro u hu
  have h1 : Real.exp (-(2 * y)) ≤ Real.exp (-y * u) :=
    Real.exp_le_exp.mpr (by nlinarith [hu.2])
  exact mul_le_mul_of_nonneg_right h1 (gP_nonneg u hu.1 hu.2)

theorem D01_nonneg : 0 ≤ D01 := by
  have hm : 8 / 9 ≤ Gm1 := GR_lower_neg _ (by norm_num)
  have hL0 := GR_lower_pos ((1.311 - 0.68) / 0.7) (by norm_num)
  have he := expneg_lower (2 * ((1.311 - 0.68) / 0.7)) (by norm_num) (by norm_num)
  simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at he
  norm_num at he hL0
  have hL : (16 * 0.7 / 15) * (1 / 3) / 2 ≤ GL1 := by
    unfold GL1; norm_num; nlinarith
  have hmpos : 0 < Gm1 := by linarith
  have hxi : xi1 ≤ 1 := by
    unfold xi1
    rw [div_le_one (by positivity)]
    norm_num; linarith
  have hDel : 0 ≤ Delta1 := by
    unfold Delta1 psi1 xi1
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) hmpos]
    norm_num at hL ⊢; nlinarith
  unfold D01
  apply div_nonneg _ (by positivity)
  exact mul_nonneg hmpos.le (by linarith)

/-- Vacuity instance for `pintz_section9_certificate`: the one-point family `λ1 = Λ0 = 1.311`
satisfies every hypothesis. -/
theorem pintz_section9_certificate_vacuity :
    (∀ j ∈ ({0} : Finset ℕ), (0.68 : ℝ) ≤ (fun _ => (1.311 : ℝ)) j) ∧
    (∀ j ∈ ({0} : Finset ℕ), (fun _ => (1.311 : ℝ)) j ≤ 1.311) ∧
    (({0} : Finset ℕ).filter fun j => (fun _ => (1.311 : ℝ)) j < 0.702).card ≤ 2 ∧
    ∑ j ∈ ({0} : Finset ℕ), (GR (((fun _ => (1.311 : ℝ)) j - 0.68) / 0.7) - GL1) ≤ D01 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · norm_num
  · simp only [Finset.sum_singleton]
    unfold GL1
    simpa using D01_nonneg

end LeanLab.Pintz2018
