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

/-- The positive auxiliary margin in display 6.18 on page 28.
The rational bound is certified from convexity and Taylor enclosures. -/
theorem lemma3_aux_margin (b : ℝ) (hb0 : 0.14 ≤ b) (hb1 : b ≤ 1.25) :
    0.027 < 16 * b - 975 / 1024 * (Real.exp (2 * b) + 1) := by
  have hsmall := exp_le_T 0.28 (by norm_num) (by norm_num)
  have hlarge := exp_le_T 2.5 (by norm_num) (by norm_num)
  norm_num [T15, Finset.sum_range_succ, Nat.factorial] at hsmall hlarge
  have hs : Real.exp 0.28 < 1.324 := by linarith
  have hl : Real.exp 2.5 < 12.183 := by linarith
  let a := (1.25 - b) / 1.11
  let c := (b - 0.14) / 1.11
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hb1) (by norm_num)
  have hc : 0 ≤ c := div_nonneg (sub_nonneg.mpr hb0) (by norm_num)
  have hac : a + c = 1 := by dsimp [a, c]; ring
  have hmix : a * 0.28 + c * 2.5 = 2 * b := by dsimp [a, c]; ring
  have he := convexOn_exp.2 (Set.mem_univ (0.28 : ℝ))
    (Set.mem_univ (2.5 : ℝ)) ha hc hac
  simp only [smul_eq_mul, hmix] at he
  have hbound := add_le_add (mul_le_mul_of_nonneg_left hs.le ha)
    (mul_le_mul_of_nonneg_left hl.le hc)
  have hlinear := he.trans hbound
  dsimp [a, c] at hlinear
  have hmargin : (1393 / 51200 : ℝ) ≤
      16 * b - 975 / 1024 * (Real.exp (2 * b) + 1) := by
    linear_combination (975 / 1024 : ℝ) * hlinear + (506581 / 75776 : ℝ) * hb0
  exact lt_of_lt_of_le (by norm_num) hmargin

/-- The imaginary-axis square identity underlying display 4.21 on page 15. -/
theorem Gc_imaginary_scaled (t : ℝ) :
    t ^ 6 * (Gc ((t : ℂ) * Complex.I)).re =
      8 * (Real.sin t - t * Real.cos t) ^ 2 := by
  have h := congrArg Complex.re (Gc_scaled_formula ((t : ℂ) * Complex.I))
  norm_num [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im,
    pow_succ, Real.cos_neg, Real.sin_neg] at h
  rw [Real.cos_two_mul, Real.sin_two_mul] at h
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- The norm majorant for the last three terms in display 6.1.
This is the first inequality of display 6.16 before specializing the real part. -/
theorem Gc_re_upper (z : ℂ) (hz : z ≠ 0) :
    (Gc z).re ≤ (16 / (15 * z) - 8 / (3 * z ^ 3)).re +
      4 / ‖z‖ ^ 4 + 4 / ‖z‖ ^ 6 +
      4 * Real.exp (-2 * z.re) * ‖z + 1‖ ^ 2 / ‖z‖ ^ 6 := by
  have h4 := Complex.re_le_norm (4 / z ^ 4)
  have h6 := Complex.re_le_norm (-(4 / z ^ 6))
  have he := Complex.re_le_norm (4 * Complex.exp (-2 * z) * (z + 1) ^ 2 / z ^ 6)
  norm_num [norm_div, norm_mul, norm_pow, Complex.norm_exp, Complex.mul_re] at h4 h6 he
  rw [Gc_formula z hz]
  simp only [Complex.add_re, Complex.sub_re]
  simp only [neg_mul] at he ⊢
  linarith


/-- The complex derivative in display 6.2 on page 26, away from zero. -/
theorem Gc_hasDerivAt (z : ℂ) (hz : z ≠ 0) :
    HasDerivAt Gc (-16 / (15 * z ^ 2) + 8 / z ^ 4 - 16 / z ^ 5 + 24 / z ^ 7 -
      8 * Complex.exp (-2 * z) / z ^ 4 * (1 + 4 / z + 6 / z ^ 2 + 3 / z ^ 3)) z := by
  have hi := hasDerivAt_id z
  have h := (((((hi.inv hz).const_mul (16 / 15 : ℂ)).sub
    (((hi.pow 3).inv (pow_ne_zero 3 hz)).const_mul (8 / 3))).add
    (((hi.pow 4).inv (pow_ne_zero 4 hz)).const_mul 4)).sub
    (((hi.pow 6).inv (pow_ne_zero 6 hz)).const_mul 4)).add
    (((((hi.const_mul (-2)).cexp).mul ((hi.add_const 1).pow 2)).const_mul 4).div
      (hi.pow 6) (pow_ne_zero 6 hz))
  have hg : Gc =ᶠ[nhds z] (fun w : ℂ =>
      16 / 15 * w⁻¹ - 8 / 3 * (w ^ 3)⁻¹ + 4 * (w ^ 4)⁻¹ - 4 * (w ^ 6)⁻¹ +
        4 * (Complex.exp (-2 * w) * (w + 1) ^ 2) / w ^ 6) := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    rw [Gc_formula w hw]
    field_simp
  dsimp at h
  convert h.congr_of_eventuallyEq hg using 1; norm_num; field_simp; ring

/-- The sign conclusion of Lemma 3 on pages 27 to 28. -/
theorem Gc_left_tail_negative (b t : ℝ) (hb0 : 0.14 ≤ b) (hb1 : b ≤ 1.25)
    (ht : 8 ≤ |t|) : (Gc ((-b : ℂ) + (t : ℂ) * Complex.I)).re < 0 := by
  let z : ℂ := (-b : ℂ) + (t : ℂ) * Complex.I
  let q : ℝ := ‖z‖ ^ 2
  have hb : 0 ≤ b := by linarith
  have ht2 : (64 : ℝ) ≤ t ^ 2 := by nlinarith [sq_abs t, sq_nonneg (|t| - 8)]
  have hzre : z.re = -b := by simp [z]
  have hzim : z.im = t := by simp [z]
  have hq : q = b ^ 2 + t ^ 2 := by
    dsimp [q]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hzre, hzim]
    ring
  have hq64 : 64 ≤ q := by nlinarith [sq_nonneg b]
  have hqpos : 0 < q := by linarith
  have hz : z ≠ 0 := by intro h; simp [q, h] at hqpos
  have hlead : (16 / (15 * z)).re = -16 * b / (15 * q) := by
    have hn : Complex.normSq z = q := Complex.normSq_eq_norm_sq z
    norm_num [Complex.div_re, Complex.normSq_mul, Complex.mul_re, Complex.mul_im,
      hzre, hzim, hn]
    field_simp; ring

  have h3re : (z ^ 3).re = b * (3 * t ^ 2 - b ^ 2) := by
    simp [z, pow_succ, Complex.mul_re, Complex.mul_im]
    ring
  have hpoly : 0 ≤ b * (3 * t ^ 2 - b ^ 2) := by
    apply mul_nonneg hb
    have hb2 : b ^ 2 ≤ (1.25 : ℝ) ^ 2 := (sq_le_sq₀ hb (by norm_num)).mpr hb1
    nlinarith
  have h3 : 0 ≤ (8 / (3 * z ^ 3)).re := by
    norm_num [Complex.div_re, Complex.mul_re, Complex.mul_im, h3re]
    apply div_nonneg
    · nlinarith only [hpoly]
    · have hn0 := Complex.normSq_nonneg z
      positivity
  have hnorm : ‖z + 1‖ ^ 2 ≤ q + 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      hzre, hzim, add_zero]
    nlinarith [hq]
  have hu := Gc_re_upper z hz
  rw [Complex.sub_re, hlead, hzre] at hu
  have he : 0 ≤ Real.exp (2 * b) := (Real.exp_pos _).le
  have hn4 : ‖z‖ ^ 4 = q ^ 2 := by dsimp [q]; ring
  have hn6 : ‖z‖ ^ 6 = q ^ 3 := by dsimp [q]; ring
  rw [hn4, hn6] at hu
  have hupper : (Gc z).re ≤ -16 * b / (15 * q) + 4 / q ^ 2 + 4 / q ^ 3 +
      4 * Real.exp (2 * b) * (q + 1) / q ^ 3 := by
    have hterm := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 4 * Real.exp (2 * b) by positivity))
      (show 0 ≤ q ^ 3 by positivity)
    simp only [mul_neg, neg_mul, neg_neg] at hu
    linear_combination hu + h3 + hterm
  have hr : 0 < 1 / q := by positivity
  have hr64 : 1 / q ≤ 1 / 64 := (div_le_div_iff₀ hqpos (by norm_num)).mpr (by linarith)
  have hr2 : (1 / q) ^ 2 ≤ (1 / 64 : ℝ) ^ 2 :=
    (sq_le_sq₀ hr.le (by norm_num)).mpr hr64
  have hcoef : 4 * (1 / q) + 4 * (1 / q) ^ 2 ≤ 65 / 1024 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ Real.exp (2 * b) + 1 by positivity)
  have hmargin := lemma3_aux_margin b hb0 hb1
  have hid : q * (-16 * b / (15 * q) + 4 / q ^ 2 + 4 / q ^ 3 +
      4 * Real.exp (2 * b) * (q + 1) / q ^ 3) =
      -16 * b / 15 + (4 * (1 / q) + 4 * (1 / q) ^ 2) * (Real.exp (2 * b) + 1) := by
    field_simp
    ring
  have hneg : q * (Gc z).re < 0 := by
    have h := mul_le_mul_of_nonneg_left hupper hqpos.le
    rw [hid] at h
    linarith
  exact (mul_lt_mul_iff_right₀ hqpos).mp (by simpa only [mul_zero] using hneg)

/-- A positive derivative on a strip sufficient for the high-frequency comparison.
Derived from display 6.2 and the norm estimates of display 6.8. -/
theorem Gc_deriv_tail_positive (a t : ℝ) (ha0 : -0.14 ≤ a) (ha1 : a ≤ 13)
    (ht : 14 ≤ |t|) :
    0 < (deriv Gc ((a : ℂ) + (t : ℂ) * Complex.I)).re := by
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  let r : ℝ := ‖z‖
  have hzre : z.re = a := by simp [z]
  have hzim : z.im = t := by simp [z]
  have hq : r ^ 2 = a ^ 2 + t ^ 2 := by
    dsimp [r]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hzre, hzim]
    ring
  have ht2 : (196 : ℝ) ≤ t ^ 2 := by nlinarith only [ht, sq_abs t, sq_nonneg (|t| - 14)]
  have hr : 14 ≤ r := by nlinarith only [hq, ht2, norm_nonneg z, sq_nonneg a]
  have hrpos : 0 < r := by linarith only [hr]
  have hz : z ≠ 0 := by intro h; simp [r, h] at hrpos
  have hr4 : 0 < r ^ 4 := by positivity
  have hir : 0 ≤ 1 / r := by positivity
  have hir14 : 1 / r ≤ 1 / 14 :=
    (div_le_div_iff₀ hrpos (by norm_num)).mpr (by linarith only [hr])
  have hir3 : 1 / r ^ 3 ≤ 1 / 2744 := by
    have h := pow_le_pow_left₀ hir hir14 3
    norm_num [div_pow] at h ⊢
    exact h
  have hir2 : 1 / r ^ 2 ≤ 1 / 196 := by
    have h := pow_le_pow_left₀ hir hir14 2
    norm_num [div_pow] at h ⊢
    exact h
  have hpoly : ‖(1 : ℂ) + 4 / z + 6 / z ^ 2 + 3 / z ^ 3‖ ≤ 4 / 3 := by
    calc
      _ ≤ ‖(1 : ℂ) + 4 / z + 6 / z ^ 2‖ + ‖3 / z ^ 3‖ := norm_add_le _ _
      _ ≤ (‖(1 : ℂ) + 4 / z‖ + ‖6 / z ^ 2‖) + ‖3 / z ^ 3‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ((‖(1 : ℂ)‖ + ‖4 / z‖) + ‖6 / z ^ 2‖) + ‖3 / z ^ 3‖ := by
        gcongr
        exact norm_add_le _ _
      _ = 1 + 4 / r + 6 / r ^ 2 + 3 / r ^ 3 := by
        norm_num [norm_div, norm_pow, r]
      _ ≤ 4 / 3 := by
        have hbound : 1 + 4 / r + 6 / r ^ 2 + 3 / r ^ 3 ≤
            1 + 4 / 14 + 6 / 196 + 3 / 2744 := by
          linear_combination 4 * hir14 + 6 * hir2 + 3 * hir3
        exact hbound.trans (by norm_num)
  have hexp : ‖Complex.exp (-2 * z)‖ ≤ 4 / 3 := by
    rw [Complex.norm_exp]
    norm_num [Complex.mul_re, hzre]
    have h := exp_le_T 0.28 (by norm_num) (by norm_num)
    norm_num [T15, Finset.sum_range_succ, Nat.factorial] at h
    have hbound : Real.exp 0.28 ≤ 4 / 3 := by linarith only [h]
    exact (Real.exp_le_exp.mpr (by linarith only [ha0])).trans hbound
  have hrem : ‖8 * Complex.exp (-2 * z) / z ^ 4 *
      (1 + 4 / z + 6 / z ^ 2 + 3 / z ^ 3)‖ ≤ (128 / 9) / r ^ 4 := by
    calc
      _ = (8 * ‖Complex.exp (-2 * z)‖ / r ^ 4) *
          ‖(1 : ℂ) + 4 / z + 6 / z ^ 2 + 3 / z ^ 3‖ := by
        norm_num [norm_mul, norm_div, norm_pow, r]
      _ ≤ (8 * (4 / 3) / r ^ 4) * (4 / 3) := by gcongr
      _ = _ := by ring
  have hmain : (-16 / (15 * z ^ 2)).re =
      16 * (t ^ 2 - a ^ 2) / (15 * r ^ 4) := by
    have hn : Complex.normSq (15 * z ^ 2) = 225 * r ^ 4 := by
      simp [Complex.normSq_eq_norm_sq, r]
      ring
    rw [Complex.div_re, hn]
    norm_num [Complex.mul_re, Complex.mul_im, pow_two, hzre, hzim]
    field_simp; ring

  have h8 := (abs_le.mp (Complex.abs_re_le_norm (8 / z ^ 4))).1
  have h16 := Complex.re_le_norm (16 / z ^ 5)
  have h24 := (abs_le.mp (Complex.abs_re_le_norm (24 / z ^ 7))).1
  have he := (Complex.re_le_norm (8 * Complex.exp (-2 * z) / z ^ 4 *
    (1 + 4 / z + 6 / z ^ 2 + 3 / z ^ 3))).trans hrem
  norm_num [norm_div, norm_pow] at h8 h16 h24
  change -(8 / r ^ 4) ≤ (8 / z ^ 4).re at h8
  change (16 / z ^ 5).re ≤ 16 / r ^ 5 at h16
  change -(24 / r ^ 7) ≤ (24 / z ^ 7).re at h24
  have hd := congrArg Complex.re (Gc_hasDerivAt z hz).deriv
  simp only [Complex.add_re, Complex.sub_re] at hd
  rw [hmain] at hd
  have hlow : 16 * (t ^ 2 - a ^ 2) / (15 * r ^ 4) -
      8 / r ^ 4 - 16 / r ^ 5 - 24 / r ^ 7 - (128 / 9) / r ^ 4 ≤ (deriv Gc z).re := by
    linarith only [hd, h8, h16, h24, he]
  have hid : r ^ 4 * (16 * (t ^ 2 - a ^ 2) / (15 * r ^ 4) -
      8 / r ^ 4 - 16 / r ^ 5 - 24 / r ^ 7 - (128 / 9) / r ^ 4) =
      16 * (t ^ 2 - a ^ 2) / 15 - 8 - 16 / r - 24 / r ^ 3 - 128 / 9 := by
    field_simp

  have ha2 : a ^ 2 ≤ 169 := by nlinarith only [ha0, ha1, mul_nonneg (sub_nonneg.mpr ha1) (show 0 ≤ a + 13 by linarith only [ha0])]
  have hprod : 0 < r ^ 4 * (deriv Gc z).re := by
    have h := mul_le_mul_of_nonneg_left hlow hr4.le
    rw [hid] at h
    have hmin : (5 : ℝ) ≤ r ^ 4 * (deriv Gc z).re := by
      linear_combination h + (16 / 15 : ℝ) * ht2 + (16 / 15 : ℝ) * ha2 +
        16 * hir14 + 24 * hir3
    exact lt_of_lt_of_le (by norm_num) hmin
  exact (mul_lt_mul_iff_right₀ hr4).mp (by simpa only [mul_zero] using hprod)

/-- Imaginary-axis positivity in display 4.21 on page 15. -/
theorem Gc_imaginary_nonneg (t : ℝ) : 0 ≤ (Gc ((t : ℂ) * Complex.I)).re := by
  by_cases ht : t = 0
  · subst t
    have h := (GR_pos 0).le
    rw [← Gc_ofReal_re 0] at h
    simpa only [Complex.ofReal_zero, zero_mul] using h
  · have hpow : 0 < t ^ 6 := by positivity
    apply nonneg_of_mul_nonneg_right ?_ hpow
    rw [Gc_imaginary_scaled]
    positivity

/-- The unnormalized numerator increases on a strip at high frequencies.
Derived from display 6.2 and the estimates of display 6.8. -/
theorem Gc_re_mono_tail (t : ℝ) (ht : 14 ≤ |t|) :
    MonotoneOn (fun x : ℝ => (Gc ((x : ℂ) + (t : ℂ) * Complex.I)).re)
      (Set.Icc (-0.14) 13) := by
  have ht0 : t ≠ 0 := by intro h; subst t; norm_num at ht
  have hd (x : ℝ) : HasDerivAt
      (fun y : ℝ => (Gc ((y : ℂ) + (t : ℂ) * Complex.I)).re)
      (deriv Gc ((x : ℂ) + (t : ℂ) * Complex.I)).re x := by
    have hz : (x : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      simp at hi
      exact ht0 hi
    have h := Gc_hasDerivAt ((x : ℂ) + (t : ℂ) * Complex.I) hz
    simpa only [Function.comp_apply, id_eq, mul_one, h.deriv] using
      (h.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const
        ((t : ℂ) * Complex.I))).real_of_complex
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).hasDerivWithinAt)
  intro x hx
  exact (Gc_deriv_tail_positive x t (interior_subset hx).1 (interior_subset hx).2 ht).le

/-- Condition 2 at all frequencies of absolute value at least fourteen.
This covers the infinite tails and the entire box 6.26 on page 29. -/
theorem G_condition2_high_frequency (a b t : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 13)
    (hb0 : 0 ≤ b) (hb : b ≤ 5 / 4) (ht : 14 ≤ |t|) :
    (Gc ((-b : ℂ) + (t : ℂ) * Complex.I)).re / (Gc (-b : ℂ)).re
      ≤ (Gc ((a : ℂ) + (t : ℂ) * Complex.I)).re / (Gc (a : ℂ)).re := by
  have hmono := Gc_re_mono_tail t ht
  have hzero : (0 : ℝ) ∈ Set.Icc (-0.14) 13 := by norm_num
  have haI : a ∈ Set.Icc (-0.14) 13 := ⟨by linarith, ha⟩
  have hn0 : 0 ≤ (Gc (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
    simpa only [Complex.ofReal_zero, zero_add] using Gc_imaginary_nonneg t
  have hright :
      (Gc (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re / GR 0 ≤
        (Gc ((a : ℂ) + (t : ℂ) * Complex.I)).re / GR a := by
    apply (div_le_div_iff₀ (GR_pos 0) (GR_pos a)).mpr
    calc
      _ ≤ (Gc (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re * GR 0 :=
        mul_le_mul_of_nonneg_left (GR_antitone ha0) hn0
      _ ≤ _ := mul_le_mul_of_nonneg_right (hmono hzero haI ha0) (GR_pos 0).le
  have hleft :
      (Gc ((-b : ℂ) + (t : ℂ) * Complex.I)).re / GR (-b) ≤
        (Gc (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re / GR 0 := by
    by_cases hb14 : 0.14 ≤ b
    · have hn := Gc_left_tail_negative b t hb14 (by linarith) (by linarith)
      exact (div_nonpos_of_nonpos_of_nonneg hn.le (GR_pos (-b)).le).trans
        (div_nonneg hn0 (GR_pos 0).le)
    · have hbI : -b ∈ Set.Icc (-0.14) 13 := ⟨by linarith, by linarith⟩
      apply (div_le_div_iff₀ (GR_pos (-b)) (GR_pos 0)).mpr
      calc
        _ ≤ (Gc (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re * GR 0 := by
          simpa only [Complex.ofReal_neg] using
            mul_le_mul_of_nonneg_right (hmono hbI hzero (by linarith)) (GR_pos 0).le
        _ ≤ _ := mul_le_mul_of_nonneg_left (GR_antitone (show -b ≤ 0 by linarith)) hn0
  simpa only [← Complex.ofReal_neg, Gc_ofReal_re] using hleft.trans hright

/-- A positive derivative on the small real strip at frequencies at least eight.
Derived from display 6.2 by the same norm method as display 6.8. -/
theorem Gc_deriv_eight_small (a t : ℝ) (ha0 : -0.14 ≤ a) (ha1 : a ≤ 0.5)
    (ht : 8 ≤ |t|) :
    0 < (deriv Gc ((a : ℂ) + (t : ℂ) * Complex.I)).re := by
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  let r : ℝ := ‖z‖
  have hzre : z.re = a := by simp [z]
  have hzim : z.im = t := by simp [z]
  have hq : r ^ 2 = a ^ 2 + t ^ 2 := by
    dsimp [r]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hzre, hzim]
    ring
  have ht2 : (64 : ℝ) ≤ t ^ 2 := by nlinarith only [ht, sq_abs t, sq_nonneg (|t| - 8)]
  have hr : 8 ≤ r := by nlinarith only [hq, ht2, norm_nonneg z, sq_nonneg a]
  have hrpos : 0 < r := by linarith only [hr]
  have hz : z ≠ 0 := by intro h; simp [r, h] at hrpos
  have hr4 : 0 < r ^ 4 := by positivity
  have hir : 0 ≤ 1 / r := by positivity
  have hir8 : 1 / r ≤ 1 / 8 :=
    (div_le_div_iff₀ hrpos (by norm_num)).mpr (by linarith only [hr])
  have hir3 : 1 / r ^ 3 ≤ 1 / 512 := by
    have h := pow_le_pow_left₀ hir hir8 3
    norm_num [div_pow] at h ⊢
    exact h
  have hir2 : 1 / r ^ 2 ≤ 1 / 64 := by
    have h := pow_le_pow_left₀ hir hir8 2
    norm_num [div_pow] at h ⊢
    exact h
  have hpoly : ‖(1 : ℂ) + 4 / z + 6 / z ^ 2 + 3 / z ^ 3‖ ≤ 8 / 5 := by
    calc
      _ ≤ ‖(1 : ℂ) + 4 / z + 6 / z ^ 2‖ + ‖3 / z ^ 3‖ := norm_add_le _ _
      _ ≤ (‖(1 : ℂ) + 4 / z‖ + ‖6 / z ^ 2‖) + ‖3 / z ^ 3‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ((‖(1 : ℂ)‖ + ‖4 / z‖) + ‖6 / z ^ 2‖) + ‖3 / z ^ 3‖ := by
        gcongr
        exact norm_add_le _ _
      _ = 1 + 4 / r + 6 / r ^ 2 + 3 / r ^ 3 := by
        norm_num [norm_div, norm_pow, r]
      _ ≤ 8 / 5 := by
        have hbound : 1 + 4 / r + 6 / r ^ 2 + 3 / r ^ 3 ≤
            1 + 4 / 8 + 6 / 64 + 3 / 512 := by
          linear_combination 4 * hir8 + 6 * hir2 + 3 * hir3
        exact hbound.trans (by norm_num)
  have hexp : ‖Complex.exp (-2 * z)‖ ≤ 4 / 3 := by
    rw [Complex.norm_exp]
    norm_num [Complex.mul_re, hzre]
    have h := exp_le_T 0.28 (by norm_num) (by norm_num)
    norm_num [T15, Finset.sum_range_succ, Nat.factorial] at h
    have hbound : Real.exp 0.28 ≤ 4 / 3 := by linarith only [h]
    exact (Real.exp_le_exp.mpr (by linarith only [ha0])).trans hbound
  have hrem : ‖8 * Complex.exp (-2 * z) / z ^ 4 *
      (1 + 4 / z + 6 / z ^ 2 + 3 / z ^ 3)‖ ≤ (256 / 15) / r ^ 4 := by
    calc
      _ = (8 * ‖Complex.exp (-2 * z)‖ / r ^ 4) *
          ‖(1 : ℂ) + 4 / z + 6 / z ^ 2 + 3 / z ^ 3‖ := by
        norm_num [norm_mul, norm_div, norm_pow, r]
      _ ≤ (8 * (4 / 3) / r ^ 4) * (8 / 5) := by gcongr
      _ = _ := by ring
  have hmain : (-16 / (15 * z ^ 2)).re =
      16 * (t ^ 2 - a ^ 2) / (15 * r ^ 4) := by
    have hn : Complex.normSq (15 * z ^ 2) = 225 * r ^ 4 := by
      simp [Complex.normSq_eq_norm_sq, r]
      ring
    rw [Complex.div_re, hn]
    norm_num [Complex.mul_re, Complex.mul_im, pow_two, hzre, hzim]
    field_simp; ring

  have h8 := (abs_le.mp (Complex.abs_re_le_norm (8 / z ^ 4))).1
  have h16 := Complex.re_le_norm (16 / z ^ 5)
  have h24 := (abs_le.mp (Complex.abs_re_le_norm (24 / z ^ 7))).1
  have he := (Complex.re_le_norm (8 * Complex.exp (-2 * z) / z ^ 4 *
    (1 + 4 / z + 6 / z ^ 2 + 3 / z ^ 3))).trans hrem
  norm_num [norm_div, norm_pow] at h8 h16 h24
  change -(8 / r ^ 4) ≤ (8 / z ^ 4).re at h8
  change (16 / z ^ 5).re ≤ 16 / r ^ 5 at h16
  change -(24 / r ^ 7) ≤ (24 / z ^ 7).re at h24
  have hd := congrArg Complex.re (Gc_hasDerivAt z hz).deriv
  simp only [Complex.add_re, Complex.sub_re] at hd
  rw [hmain] at hd
  have hlow : 16 * (t ^ 2 - a ^ 2) / (15 * r ^ 4) -
      8 / r ^ 4 - 16 / r ^ 5 - 24 / r ^ 7 - (256 / 15) / r ^ 4 ≤ (deriv Gc z).re := by
    linarith only [hd, h8, h16, h24, he]
  have hid : r ^ 4 * (16 * (t ^ 2 - a ^ 2) / (15 * r ^ 4) -
      8 / r ^ 4 - 16 / r ^ 5 - 24 / r ^ 7 - (256 / 15) / r ^ 4) =
      16 * (t ^ 2 - a ^ 2) / 15 - 8 - 16 / r - 24 / r ^ 3 - 256 / 15 := by
    field_simp

  have ha2 : a ^ 2 ≤ 0.25 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr ha1) (show 0 ≤ a + 0.5 by linarith only [ha0])]
  have hprod : 0 < r ^ 4 * (deriv Gc z).re := by
    have h := mul_le_mul_of_nonneg_left hlow hr4.le
    rw [hid] at h
    have hmin : (40 : ℝ) ≤ r ^ 4 * (deriv Gc z).re := by
      linear_combination h + (16 / 15 : ℝ) * ht2 + (16 / 15 : ℝ) * ha2 +
        16 * hir8 + 24 * hir3
    exact lt_of_lt_of_le (by norm_num) hmin
  exact (mul_lt_mul_iff_right₀ hr4).mp (by simpa only [mul_zero] using hprod)

/-- The lower norm majorant complementary to the estimate from display 6.1. -/
theorem Gc_re_lower (z : ℂ) (hz : z ≠ 0) :
    (16 / (15 * z) - 8 / (3 * z ^ 3)).re -
      4 / ‖z‖ ^ 4 - 4 / ‖z‖ ^ 6 -
      4 * Real.exp (-2 * z.re) * ‖z + 1‖ ^ 2 / ‖z‖ ^ 6 ≤ (Gc z).re := by
  have h4 := (abs_le.mp (Complex.abs_re_le_norm (4 / z ^ 4))).1
  have h6 := Complex.re_le_norm (4 / z ^ 6)
  have he := (abs_le.mp (Complex.abs_re_le_norm
    (4 * Complex.exp (-2 * z) * (z + 1) ^ 2 / z ^ 6))).1
  norm_num [norm_div, norm_mul, norm_pow, Complex.norm_exp, Complex.mul_re] at h4 h6 he
  rw [Gc_formula z hz]
  simp only [Complex.add_re, Complex.sub_re]
  simp only [neg_mul] at he ⊢
  linear_combination h4 + h6 + he

/-- The numerator comparison for larger positive arguments at frequencies at least eight.
Derived from displays 4.21 and 6.1 by rational norm bounds. -/
theorem Gc_large_argument_compare (a t : ℝ) (ha0 : 0.5 ≤ a) (ha1 : a ≤ 13)
    (ht : 8 ≤ |t|) :
    (Gc ((t : ℂ) * Complex.I)).re ≤
      (Gc ((a : ℂ) + (t : ℂ) * Complex.I)).re := by
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  let y : ℝ := t ^ 2
  let q : ℝ := ‖z‖ ^ 2
  have ha : 0 ≤ a := by linarith only [ha0]
  have hy64 : 64 ≤ y := by dsimp [y]; nlinarith only [ht, sq_abs t, sq_nonneg (|t| - 8)]
  have hypos : 0 < y := by linarith only [hy64]
  have hzre : z.re = a := by simp [z]
  have hzim : z.im = t := by simp [z]
  have hq : q = a ^ 2 + y := by
    dsimp [q, y]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hzre, hzim]
    ring
  have hyq : y ≤ q := by nlinarith only [hq, sq_nonneg a]
  have hqpos : 0 < q := hypos.trans_le hyq
  have hz : z ≠ 0 := by intro h; simp [q, h] at hqpos
  have hlead : (16 / (15 * z)).re = 16 * a / (15 * q) := by
    have hn : Complex.normSq z = q := Complex.normSq_eq_norm_sq z
    norm_num [Complex.div_re, Complex.normSq_mul, Complex.mul_re, Complex.mul_im,
      hzre, hzim, hn]
    field_simp; ring

  have ha2 : a ^ 2 ≤ 169 := by
    have h : a ^ 2 ≤ (13 : ℝ) ^ 2 := (sq_le_sq₀ ha (by norm_num)).mpr ha1
    norm_num at h
    exact h
  have h3re : (z ^ 3).re = a * (a ^ 2 - 3 * y) := by
    simp [z, y, pow_succ, Complex.mul_re, Complex.mul_im]
    ring
  have hpoly : a * (a ^ 2 - 3 * y) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha (by linarith only [ha2, hy64])
  have h3 : (8 / (3 * z ^ 3)).re ≤ 0 := by
    norm_num [Complex.div_re, Complex.mul_re, Complex.mul_im, h3re]
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith only [hpoly]
    · have hn0 := Complex.normSq_nonneg z
      positivity
  have hnorm : ‖z + 1‖ ^ 2 ≤ q + 27 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      hzre, hzim, add_zero]
    have hq' : q = a ^ 2 + t ^ 2 := hq
    nlinarith only [hq', ha1]
  have hexp : Real.exp (-2 * a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [ha])
  have hrem : 4 * Real.exp (-2 * a) * ‖z + 1‖ ^ 2 / q ^ 3 ≤ 4 * (q + 27) / q ^ 3 := by
    gcongr
    linarith only [hexp]
  have hn4 : ‖z‖ ^ 4 = q ^ 2 := by dsimp [q]; ring
  have hn6 : ‖z‖ ^ 6 = q ^ 3 := by dsimp [q]; ring
  have hlower := Gc_re_lower z hz
  rw [Complex.sub_re, hlead, hzre, hn4, hn6] at hlower
  have hlow : 16 * a / (15 * q) - 8 / q ^ 2 - 112 / q ^ 3 ≤ (Gc z).re := by
    have h : 16 * a / (15 * q) - 4 / q ^ 2 - 4 / q ^ 3 -
        4 * (q + 27) / q ^ 3 ≤ (Gc z).re := by
      linear_combination hlower + h3 + hrem
    convert h using 1; field_simp; ring
  have hacompare : (0.5 : ℝ) / (y + 0.25) ≤ a / q := by
    rw [div_le_div_iff₀ (by positivity : 0 < y + 0.25) hqpos]
    rw [hq]
    have hp := mul_nonneg (show 0 ≤ a - 0.5 by linarith only [ha0])
      (show 0 ≤ y - 0.5 * a by linarith only [hy64, ha1])
    nlinarith only [hp]
  have hq2 : 1 / q ^ 2 ≤ 1 / y ^ 2 := by gcongr
  have hq3 : 1 / q ^ 3 ≤ 1 / y ^ 3 := by gcongr
  have hsimple : 8 / (15 * (y + 0.25)) - 8 / y ^ 2 - 112 / y ^ 3 ≤ (Gc z).re := by
    have h : (16 / 15 : ℝ) * (0.5 / (y + 0.25)) - 8 / y ^ 2 - 112 / y ^ 3 ≤
        (Gc z).re := by
      linear_combination hlow + (16 / 15 : ℝ) * hacompare + 8 * hq2 + 112 * hq3
    convert h using 1; field_simp; ring
  have hzero_upper : (Gc ((t : ℂ) * Complex.I)).re ≤ 8 / y ^ 2 + 8 / y ^ 3 := by
    have hs := Gc_imaginary_scaled t
    have hid : (Real.sin t - t * Real.cos t) ^ 2 +
        (t * Real.sin t + Real.cos t) ^ 2 = 1 + y := by
      have htrig := Real.sin_sq_add_cos_sq t
      have hmul := congrArg (fun x : ℝ => t ^ 2 * x) htrig
      dsimp [y]
      nlinarith only [htrig, hmul]
    have hsq : (Real.sin t - t * Real.cos t) ^ 2 ≤ 1 + y := by
      nlinarith only [hid, sq_nonneg (t * Real.sin t + Real.cos t)]
    have hy3 : 0 < y ^ 3 := by positivity
    apply (mul_le_mul_iff_right₀ hy3).mp
    have hidy : y ^ 3 * (8 / y ^ 2 + 8 / y ^ 3) = 8 * (1 + y) := by field_simp; ring
    rw [hidy]
    have hty : y ^ 3 = t ^ 6 := by dsimp [y]; ring
    rw [hty, hs]
    exact mul_le_mul_of_nonneg_left hsq (by norm_num)
  have hnumeric : 8 / y ^ 2 + 8 / y ^ 3 ≤
      8 / (15 * (y + 0.25)) - 8 / y ^ 2 - 112 / y ^ 3 := by
    have hp : 0 ≤ (y - 64) * y ^ 2 := mul_nonneg (sub_nonneg.mpr hy64) (sq_nonneg y)
    have hp2 : 0 ≤ (y - 64) * y := mul_nonneg (sub_nonneg.mpr hy64) hypos.le
    have hpoly : 0 ≤ 8 * y ^ 3 - 240 * y ^ 2 - 1860 * y - 450 := by
      nlinarith only [hy64, hp, hp2]
    apply (mul_le_mul_iff_right₀ (show 0 < 15 * (y + 0.25) * y ^ 3 by positivity)).mp
    field_simp
    nlinarith only [hpoly]
  exact hzero_upper.trans (hnumeric.trans hsimple)

/-- The numerator increases on the small real strip at frequencies at least eight. -/
theorem Gc_re_mono_eight_small (t : ℝ) (ht : 8 ≤ |t|) :
    MonotoneOn (fun x : ℝ => (Gc ((x : ℂ) + (t : ℂ) * Complex.I)).re)
      (Set.Icc (-0.14) 0.5) := by
  have ht0 : t ≠ 0 := by intro h; subst t; norm_num at ht
  have hd (x : ℝ) : HasDerivAt
      (fun y : ℝ => (Gc ((y : ℂ) + (t : ℂ) * Complex.I)).re)
      (deriv Gc ((x : ℂ) + (t : ℂ) * Complex.I)).re x := by
    have hz : (x : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      simp at hi
      exact ht0 hi
    have h := Gc_hasDerivAt ((x : ℂ) + (t : ℂ) * Complex.I) hz
    simpa only [Function.comp_apply, id_eq, mul_one, h.deriv] using
      (h.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const
        ((t : ℂ) * Complex.I))).real_of_complex
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).hasDerivWithinAt)
  intro x hx
  exact (Gc_deriv_eight_small x t (interior_subset hx).1 (interior_subset hx).2 ht).le

/-- Condition 2 for every absolute frequency at least eight.
This certifies both boxes 6.26 and 6.27 and all infinite tails on page 29. -/
theorem G_condition2_eight (a b t : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 13)
    (hb0 : 0 ≤ b) (hb : b ≤ 5 / 4) (ht : 8 ≤ |t|) :
    (Gc ((-b : ℂ) + (t : ℂ) * Complex.I)).re / (Gc (-b : ℂ)).re
      ≤ (Gc ((a : ℂ) + (t : ℂ) * Complex.I)).re / (Gc (a : ℂ)).re := by
  have hmono := Gc_re_mono_eight_small t ht
  have hzero : (0 : ℝ) ∈ Set.Icc (-0.14) 0.5 := by norm_num
  have hn0 : 0 ≤ (Gc (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
    simpa only [Complex.ofReal_zero, zero_add] using Gc_imaginary_nonneg t
  have hnum : (Gc (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re ≤
      (Gc ((a : ℂ) + (t : ℂ) * Complex.I)).re := by
    by_cases ha5 : a ≤ 0.5
    · exact hmono hzero ⟨by linarith, ha5⟩ ha0
    · simpa only [Complex.ofReal_zero, zero_add] using
        Gc_large_argument_compare a t (le_of_not_ge ha5) ha ht
  have hright :
      (Gc (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re / GR 0 ≤
        (Gc ((a : ℂ) + (t : ℂ) * Complex.I)).re / GR a := by
    apply (div_le_div_iff₀ (GR_pos 0) (GR_pos a)).mpr
    calc
      _ ≤ (Gc (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re * GR 0 :=
        mul_le_mul_of_nonneg_left (GR_antitone ha0) hn0
      _ ≤ _ := mul_le_mul_of_nonneg_right hnum (GR_pos 0).le
  have hleft :
      (Gc ((-b : ℂ) + (t : ℂ) * Complex.I)).re / GR (-b) ≤
        (Gc (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re / GR 0 := by
    by_cases hb14 : 0.14 ≤ b
    · have hn := Gc_left_tail_negative b t hb14 (by linarith) (by linarith)
      exact (div_nonpos_of_nonpos_of_nonneg hn.le (GR_pos (-b)).le).trans
        (div_nonneg hn0 (GR_pos 0).le)
    · have hbI : -b ∈ Set.Icc (-0.14) 0.5 := ⟨by linarith, by linarith⟩
      apply (div_le_div_iff₀ (GR_pos (-b)) (GR_pos 0)).mpr
      calc
        _ ≤ (Gc (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re * GR 0 := by
          simpa only [Complex.ofReal_neg] using
            mul_le_mul_of_nonneg_right (hmono hbI hzero (by linarith)) (GR_pos 0).le
        _ ≤ _ := mul_le_mul_of_nonneg_left (GR_antitone (show -b ≤ 0 by linarith)) hn0
  simpa only [← Complex.ofReal_neg, Gc_ofReal_re] using hleft.trans hright

/-- Differentiation of the integral in display 4.19, including its removable singularity.
This is the first derivative integral used in display 6.3 on page 26. -/
theorem Gc_hasDerivAt_integral (z : ℂ) :
    HasDerivAt Gc
      (∫ u in (0 : ℝ)..2, -(u : ℂ) * Complex.exp (-z * u) * (gP u : ℂ)) z := by
  let C : ℝ := (32 / 3) * Real.exp (2 * (‖z‖ + 1))
  have hd (x : ℂ) (u : ℝ) : HasDerivAt
      (fun w : ℂ => Complex.exp (-w * u) * (gP u : ℂ))
      (-(u : ℂ) * Complex.exp (-x * u) * (gP u : ℂ)) x := by
    convert ((((hasDerivAt_id x).neg).mul_const (u : ℂ)).cexp).mul_const (gP u : ℂ) using 1
    · rfl
    · dsimp
      ring
  have hc (x : ℂ) : Continuous (fun u : ℝ => Complex.exp (-x * u) * (gP u : ℂ)) := by
    unfold gP
    fun_prop
  have hc' (x : ℂ) : Continuous
      (fun u : ℝ => -(u : ℂ) * Complex.exp (-x * u) * (gP u : ℂ)) := by
    unfold gP
    fun_prop
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x : ℂ => fun u : ℝ => Complex.exp (-x * u) * (gP u : ℂ))
    (F' := fun x : ℂ => fun u : ℝ => -(u : ℂ) * Complex.exp (-x * u) * (gP u : ℂ))
    (x₀ := z) (s := Metric.ball z 1) (bound := fun _ => C)
    (a := (0 : ℝ)) (b := 2) (μ := MeasureTheory.volume)
    (Metric.ball_mem_nhds z (by norm_num))
    (Filter.Eventually.of_forall (fun x => (hc x).aestronglyMeasurable))
    ((hc z).intervalIntegrable 0 2) (hc' z).aestronglyMeasurable
    ?_ (intervalIntegrable_const) ?_).2
  · apply Filter.Eventually.of_forall
    intro u hu x hx
    have hu' : u ∈ Set.Ioc (0 : ℝ) 2 := by
      simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using hu
    have hu0 : 0 ≤ u := hu'.1.le
    have hu2 : u ≤ 2 := hu'.2
    have hgp0 := gP_nonneg u hu0 hu2
    have hgp : gP u ≤ 16 / 3 := by
      have hp : 4 + 6 * u + u ^ 2 ≤ 20 := by
        nlinarith only [hu2, (sq_le_sq₀ hu0 (by norm_num : (0 : ℝ) ≤ 2)).mpr hu2]
      have hcube : (2 - u) ^ 3 ≤ 8 := by
        have h := pow_le_pow_left₀ (show 0 ≤ 2 - u by linarith only [hu2])
          (show 2 - u ≤ 2 by linarith only [hu0]) 3
        norm_num at h
        exact h
      unfold gP
      have hp0 : 0 ≤ 4 + 6 * u + u ^ 2 := by positivity
      have hm := mul_le_mul hcube hp hp0 (by norm_num : (0 : ℝ) ≤ 8)
      nlinarith only [hm]
    have hx1 : ‖x - z‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hxnorm : ‖x‖ ≤ ‖z‖ + 1 := by
      have h := norm_add_le (x - z) z
      rw [sub_add_cancel] at h
      linarith only [h, hx1]
    have harg : (-x * (u : ℂ)).re ≤ 2 * (‖z‖ + 1) := by
      calc
        _ ≤ ‖-x * (u : ℂ)‖ := Complex.re_le_norm _
        _ = ‖x‖ * u := by simp [Real.norm_eq_abs, abs_of_nonneg hu0]
        _ ≤ (‖z‖ + 1) * 2 :=
          mul_le_mul hxnorm hu2 hu0 (by positivity)
        _ = _ := by ring
    have he := Real.exp_le_exp.mpr harg
    calc
      ‖-(u : ℂ) * Complex.exp (-x * u) * (gP u : ℂ)‖ =
          u * Real.exp (-x * (u : ℂ)).re * gP u := by
        simp [Complex.norm_exp, Real.norm_eq_abs, abs_of_nonneg hu0,
          abs_of_nonneg hgp0]
      _ ≤ 2 * Real.exp (2 * (‖z‖ + 1)) * (16 / 3) := by gcongr
      _ = C := by dsimp [C]; ring
  · exact Filter.Eventually.of_forall (fun u _ x _ => hd x u)

/-- The real derivative integral in display 6.3, including zero. -/
theorem GR_hasDerivAt_integral (x : ℝ) :
    HasDerivAt GR (∫ u in (0 : ℝ)..2, -u * Real.exp (-x * u) * gP u) x := by
  have h := (Gc_hasDerivAt_integral (x : ℂ)).real_of_complex
  have hc : Continuous
      (fun u : ℝ => -(u : ℂ) * Complex.exp (-(x : ℂ) * u) * (gP u : ℂ)) := by
    unfold gP
    fun_prop
  have hre : (∫ u in (0 : ℝ)..2,
      -(u : ℂ) * Complex.exp (-(x : ℂ) * u) * (gP u : ℂ)).re =
        ∫ u in (0 : ℝ)..2, -u * Real.exp (-x * u) * gP u := by
    have hr := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (μ := MeasureTheory.volume)
      (a := 0) (b := 2) (hc.intervalIntegrable 0 2)
    refine hr.symm.trans ?_
    apply intervalIntegral.integral_congr
    intro u _
    simp [Complex.mul_re, Complex.mul_im, Complex.exp_re]
  rw [hre] at h
  simpa only [Gc_ofReal_re] using h

/-- The strict sign of the real derivative in display 6.3 on page 26. -/
theorem GR_deriv_neg (x : ℝ) : deriv GR x < 0 := by
  rw [(GR_hasDerivAt_integral x).deriv]
  have hi : 0 < ∫ u in (0 : ℝ)..2, u * Real.exp (-x * u) * gP u := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      ((by unfold gP; fun_prop : Continuous
        (fun u : ℝ => u * Real.exp (-x * u) * gP u)).intervalIntegrable 0 2)
      ?_ (by norm_num)
    intro u hu
    have hu0 : 0 < u := hu.1
    have h2 : 0 < 2 - u := by linarith only [hu.2]
    unfold gP
    positivity
  have hid : (fun u : ℝ => -u * Real.exp (-x * u) * gP u) =
      (fun u => -(u * Real.exp (-x * u) * gP u)) := by funext u; ring
  rw [hid, intervalIntegral.integral_neg]
  linarith only [hi]

/-- The derivative at the removable singularity, evaluated from display 4.19. -/
theorem GR_deriv_zero : deriv GR 0 = -16 / 35 := by
  rw [(GR_hasDerivAt_integral 0).deriv]
  simp only [neg_zero, zero_mul, Real.exp_zero, mul_one]
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) 2,
      HasDerivAt (fun u : ℝ => -8 / 15 * u ^ 2 + 1 / 3 * u ^ 4 -
        2 / 15 * u ^ 5 + 1 / 210 * u ^ 7) (-x * gP x) x := by
    intro x _
    have h := (((((hasDerivAt_pow 2 x).const_mul (-8 / 15)).add
      ((hasDerivAt_pow 4 x).const_mul (1 / 3))).sub
      ((hasDerivAt_pow 5 x).const_mul (2 / 15))).add
      ((hasDerivAt_pow 7 x).const_mul (1 / 210)))
    convert h using 1; unfold gP; norm_num; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by unfold gP; fun_prop : Continuous (fun u : ℝ => -u * gP u)).intervalIntegrable 0 2)]
  norm_num

/-- Strict decrease of the real transform, as in display 6.3 on page 26. -/
theorem GR_strictAnti : StrictAnti GR := by
  exact strictAnti_of_deriv_neg GR_deriv_neg

/-- Convexity of the real transform, a consequence of display 6.3 on page 26. -/
theorem GR_convex : ConvexOn ℝ Set.univ GR := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  unfold GR
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add]
  · apply intervalIntegral.integral_mono_on (by norm_num)
      ((by unfold gP; fun_prop : Continuous (fun u : ℝ =>
        Real.exp (-(a * x + b * y) * u) * gP u)).intervalIntegrable 0 2)
      ((by unfold gP; fun_prop : Continuous (fun u : ℝ =>
        a * (Real.exp (-x * u) * gP u) + b * (Real.exp (-y * u) * gP u))).intervalIntegrable 0 2)
    intro u hu
    have h := convexOn_exp.2 (Set.mem_univ (-x * u)) (Set.mem_univ (-y * u)) ha hb hab
    simp only [smul_eq_mul] at h
    rw [show -(a * x + b * y) * u = a * (-x * u) + b * (-y * u) by ring]
    have hm := mul_le_mul_of_nonneg_right h (gP_nonneg u hu.1 hu.2)
    linear_combination hm
  all_goals apply Continuous.intervalIntegrable; unfold gP; fun_prop


/-- The printed derivative estimate of display 6.7 on page 26. -/
theorem lemma1_derivative_bound (a t : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 13)
    (ht : 14 ≤ |t|) :
    9 / ‖((a : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4 < (deriv Gc ((a : ℂ) + (t : ℂ) * Complex.I)).re := by
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  let r : ℝ := ‖z‖
  have hzre : z.re = a := by simp [z]
  have hzim : z.im = t := by simp [z]
  have hq : r ^ 2 = a ^ 2 + t ^ 2 := by
    dsimp [r]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hzre, hzim]
    ring
  have ht2 : (196 : ℝ) ≤ t ^ 2 := by nlinarith only [ht, sq_abs t, sq_nonneg (|t| - 14)]
  have hr : 14 ≤ r := by nlinarith only [hq, ht2, norm_nonneg z, sq_nonneg a]
  have hrpos : 0 < r := by linarith only [hr]
  have hz : z ≠ 0 := by intro h; simp [r, h] at hrpos
  have hr4 : 0 < r ^ 4 := by positivity
  have hir : 0 ≤ 1 / r := by positivity
  have hir14 : 1 / r ≤ 1 / 14 :=
    (div_le_div_iff₀ hrpos (by norm_num)).mpr (by linarith only [hr])
  have hir3 : 1 / r ^ 3 ≤ 1 / 2744 := by
    have h := pow_le_pow_left₀ hir hir14 3
    norm_num [div_pow] at h ⊢
    exact h
  have hir2 : 1 / r ^ 2 ≤ 1 / 196 := by
    have h := pow_le_pow_left₀ hir hir14 2
    norm_num [div_pow] at h ⊢
    exact h
  have hpoly : ‖(1 : ℂ) + 4 / z + 6 / z ^ 2 + 3 / z ^ 3‖ ≤ 33 / 25 := by
    calc
      _ ≤ ‖(1 : ℂ) + 4 / z + 6 / z ^ 2‖ + ‖3 / z ^ 3‖ := norm_add_le _ _
      _ ≤ (‖(1 : ℂ) + 4 / z‖ + ‖6 / z ^ 2‖) + ‖3 / z ^ 3‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ((‖(1 : ℂ)‖ + ‖4 / z‖) + ‖6 / z ^ 2‖) + ‖3 / z ^ 3‖ := by
        gcongr
        exact norm_add_le _ _
      _ = 1 + 4 / r + 6 / r ^ 2 + 3 / r ^ 3 := by
        norm_num [norm_div, norm_pow, r]
      _ ≤ 33 / 25 := by
        have hbound : 1 + 4 / r + 6 / r ^ 2 + 3 / r ^ 3 ≤
            1 + 4 / 14 + 6 / 196 + 3 / 2744 := by
          linear_combination 4 * hir14 + 6 * hir2 + 3 * hir3
        exact hbound.trans (by norm_num)
  have hexp : ‖Complex.exp (-2 * z)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simpa [Complex.mul_re, hzre] using (show -2 * a ≤ 0 by linarith only [ha0])
  have hrem : ‖8 * Complex.exp (-2 * z) / z ^ 4 *
      (1 + 4 / z + 6 / z ^ 2 + 3 / z ^ 3)‖ ≤ (264 / 25) / r ^ 4 := by
    calc
      _ = (8 * ‖Complex.exp (-2 * z)‖ / r ^ 4) *
          ‖(1 : ℂ) + 4 / z + 6 / z ^ 2 + 3 / z ^ 3‖ := by
        norm_num [norm_mul, norm_div, norm_pow, r]
      _ ≤ (8 * 1 / r ^ 4) * (33 / 25) := by gcongr
      _ = _ := by ring
  have hmain : (-16 / (15 * z ^ 2)).re =
      16 * (t ^ 2 - a ^ 2) / (15 * r ^ 4) := by
    have hn : Complex.normSq (15 * z ^ 2) = 225 * r ^ 4 := by
      simp [Complex.normSq_eq_norm_sq, r]
      ring
    rw [Complex.div_re, hn]
    norm_num [Complex.mul_re, Complex.mul_im, pow_two, hzre, hzim]
    field_simp; ring

  have h8 := (abs_le.mp (Complex.abs_re_le_norm (8 / z ^ 4))).1
  have h16 := Complex.re_le_norm (16 / z ^ 5)
  have h24 := (abs_le.mp (Complex.abs_re_le_norm (24 / z ^ 7))).1
  have he := (Complex.re_le_norm (8 * Complex.exp (-2 * z) / z ^ 4 *
    (1 + 4 / z + 6 / z ^ 2 + 3 / z ^ 3))).trans hrem
  norm_num [norm_div, norm_pow] at h8 h16 h24
  change -(8 / r ^ 4) ≤ (8 / z ^ 4).re at h8
  change (16 / z ^ 5).re ≤ 16 / r ^ 5 at h16
  change -(24 / r ^ 7) ≤ (24 / z ^ 7).re at h24
  have hd := congrArg Complex.re (Gc_hasDerivAt z hz).deriv
  simp only [Complex.add_re, Complex.sub_re] at hd
  rw [hmain] at hd
  have hlow : 16 * (t ^ 2 - a ^ 2) / (15 * r ^ 4) -
      8 / r ^ 4 - 16 / r ^ 5 - 24 / r ^ 7 - (264 / 25) / r ^ 4 ≤ (deriv Gc z).re := by
    linarith only [hd, h8, h16, h24, he]
  have hid : r ^ 4 * (16 * (t ^ 2 - a ^ 2) / (15 * r ^ 4) -
      8 / r ^ 4 - 16 / r ^ 5 - 24 / r ^ 7 - (264 / 25) / r ^ 4) =
      16 * (t ^ 2 - a ^ 2) / 15 - 8 - 16 / r - 24 / r ^ 3 - 264 / 25 := by
    field_simp

  have ha2 : a ^ 2 ≤ 169 := by nlinarith only [ha0, ha1, mul_nonneg (sub_nonneg.mpr ha1) (show 0 ≤ a + 13 by linarith only [ha0])]
  have hprod : 9 < r ^ 4 * (deriv Gc z).re := by
    have h := mul_le_mul_of_nonneg_left hlow hr4.le
    rw [hid] at h
    have hmin : (9.05 : ℝ) ≤ r ^ 4 * (deriv Gc z).re := by
      linear_combination h + (16 / 15 : ℝ) * ht2 + (16 / 15 : ℝ) * ha2 +
        16 * hir14 + 24 * hir3
    exact lt_of_lt_of_le (by norm_num) hmin
  change 9 / r ^ 4 < (deriv Gc z).re
  apply (mul_lt_mul_iff_right₀ hr4).mp
  rw [show r ^ 4 * (9 / r ^ 4) = 9 by field_simp]
  exact hprod

/-- Lemma 1, display 6.6 on page 26, with the determinant written explicitly. -/
theorem lemma1_phi_bound (a t : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 13) (ht : 14 ≤ |t|) :
    9 * GR a / ‖((a : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4 <
      (deriv Gc ((a : ℂ) + (t : ℂ) * Complex.I)).re * GR a -
        (Gc ((a : ℂ) + (t : ℂ) * Complex.I)).re * deriv GR a ∧
      0 < 9 * GR a / ‖((a : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4 := by
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  have hz : z ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [z] at hi
    rw [hi] at ht
    norm_num at ht
  have hr : 0 < ‖z‖ ^ 4 := pow_pos (norm_pos_iff.mpr hz) 4
  have hn := Gc_re_mono_tail t ht (show (0 : ℝ) ∈ Set.Icc (-0.14) 13 by norm_num)
    (show a ∈ Set.Icc (-0.14) 13 from ⟨by linarith only [ha0], ha1⟩) ha0
  have hnum : 0 ≤ (Gc z).re := by
    have h0 := Gc_imaginary_nonneg t
    have hn' : (Gc ((t : ℂ) * Complex.I)).re ≤ (Gc z).re := by
      simpa only [Complex.ofReal_zero, zero_add] using hn
    exact h0.trans hn'
  have hcor := mul_nonpos_of_nonneg_of_nonpos hnum (GR_deriv_neg a).le
  refine ⟨?_, div_pos (mul_pos (by norm_num) (GR_pos a)) hr⟩
  calc
    9 * GR a / ‖z‖ ^ 4 = (9 / ‖z‖ ^ 4) * GR a := by ring
    _ < (deriv Gc z).re * GR a :=
      mul_lt_mul_of_pos_right (lemma1_derivative_bound a t ha0 ha1 ht) (GR_pos a)
    _ ≤ _ := by linarith only [hcor]

/-- The real specialization of display 6.2 away from zero. -/
theorem GR_deriv_formula (y : ℝ) (hy : y ≠ 0) :
    deriv GR y = -16 / (15 * y ^ 2) + 8 / y ^ 4 - 16 / y ^ 5 + 24 / y ^ 7 -
      8 * Real.exp (-2 * y) / y ^ 4 * (1 + 4 / y + 6 / y ^ 2 + 3 / y ^ 3) := by
  have hz : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have h := (Gc_hasDerivAt (y : ℂ) hz).real_of_complex
  simp only [Gc_ofReal_re] at h
  rw [h.deriv]
  have heq : (-16 / (15 * (y : ℂ) ^ 2) + 8 / (y : ℂ) ^ 4 -
      16 / (y : ℂ) ^ 5 + 24 / (y : ℂ) ^ 7 -
      8 * Complex.exp (-2 * (y : ℂ)) / (y : ℂ) ^ 4 *
        (1 + 4 / (y : ℂ) + 6 / (y : ℂ) ^ 2 + 3 / (y : ℂ) ^ 3)) =
      ((-16 / (15 * y ^ 2) + 8 / y ^ 4 - 16 / y ^ 5 + 24 / y ^ 7 -
        8 * Real.exp (-2 * y) / y ^ 4 * (1 + 4 / y + 6 / y ^ 2 + 3 / y ^ 3) : ℝ) : ℂ) := by
    push_cast; rfl

  rw [heq, Complex.ofReal_re]

/-- Certified endpoint values used in displays 6.11 and 6.12 on page 27.
The enclosure of h differs from the printed lower bound in display 6.11. -/
theorem lemma2_endpoint_bounds :
    0.0043 < (8 / 9 : ℝ) * GR (-1.25) + 1.25 * deriv GR (-1.25) ∧
      (8 / 9 : ℝ) * GR (-1.25) + 1.25 * deriv GR (-1.25) < 0.0044 ∧
      |deriv GR (-1.25)| < 1.36 := by
  have helo := exp_ge_T 2.5 (by norm_num)
  have hehi := exp_le_T 2.5 (by norm_num) (by norm_num)
  norm_num [T15, Finset.sum_range_succ, Nat.factorial] at helo hehi
  have he : 12.18249 < Real.exp 2.5 ∧ Real.exp 2.5 < 12.1825 := by
    constructor <;> linarith only [helo, hehi]
  have hg := GR_scaled_formula (-1.25)
  have hd := GR_deriv_formula (-1.25) (by norm_num)
  norm_num at hg hd
  have hh : (8 / 9 : ℝ) * GR (-1.25) + 1.25 * deriv GR (-1.25) =
      (630592 - 51712 * Real.exp 2.5) / 140625 := by
    nlinarith only [hg, hd]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith only [hh, he.1, he.2]
  · nlinarith only [hh, he.1, he.2]
  · rw [abs_lt]
    constructor <;> nlinarith only [hd, he.1, he.2]

/-- QUESTION on page 27, display 6.11.
The endpoint inequality printed there is false for the transform in display 4.19.
This does not assert that Lemma 2 or Condition 2 is false. -/
theorem lemma2_printed_endpoint_false :
    ¬ (1 / 90 < (8 / 9 : ℝ) * GR (-1.25) + 1.25 * deriv GR (-1.25)) := by
  obtain ⟨_, hh, _⟩ := lemma2_endpoint_bounds
  linarith only [hh]

/-- The cosine premise of the small-frequency method cannot extend to frequency pi.
This is an obstruction to that method, not a counterexample to Condition 2. -/
theorem cosine_antitone_obstruction :
    ¬ AntitoneOn (fun u : ℝ => Real.cos (Real.pi * u)) (Set.Icc 0 2) := by
  intro h
  have hh := h (show (1 : ℝ) ∈ Set.Icc 0 2 by norm_num)
    (show (2 : ℝ) ∈ Set.Icc 0 2 by norm_num) (by norm_num : (1 : ℝ) ≤ 2)
  norm_num [show Real.pi * (2 : ℝ) = 2 * Real.pi by ring, Real.cos_two_pi] at hh

/-- SEALED TARGET certificate of Condition 2 for `G`, Lemma 5, arXiv 1804.09084v2 p.29
display 6.25; numerically tested min margin 0 at the corner a = b = 0 only, slopes at least
0.0075 in b and 0.024 in a on the box pi/2 < |t| < 8 -/
theorem G_condition2 (a b t : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 13) (hb0 : 0 ≤ b) (hb : b ≤ 5 / 4) :
    (Gc ((-b : ℂ) + (t : ℂ) * Complex.I)).re / (Gc (-b : ℂ)).re
      ≤ (Gc ((a : ℂ) + (t : ℂ) * Complex.I)).re / (Gc (a : ℂ)).re := by
  by_cases htail : 8 ≤ |t|
  · exact G_condition2_eight a b t ha0 ha hb0 hb htail
  have ht8 : |t| < 8 := lt_of_not_ge htail
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

end LeanLab.Pintz2018
