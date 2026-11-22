import LeanLab.ExceptionalSet.DQLemma9Decisions

/-!
Prep 2026-11-21, ExceptionalSet route step ES-cited, the `U1539.lemma9` part.
`DQLemma9Decisions` proves `Lemma9` from the paper's `Theorem2`, `Lemma4` and two open LEAF
statements about the trapezoid `trapL9` of P0082 page 370, J. Brüdern and A. Perelli,
Ann. Inst. Fourier 48 (1998), doi 10.5802/aif.1621. Neither leaf cites another work, so both
are split here in place, and every piece is PROVED: the file has no sorry.

* `trapezoid_coeff_split` has exactly the type of `DQLemma9.leaf_trapezoid_coeff_l9`.
* `trapezoid_series_split` has exactly the type of `DQLemma9.leaf_trapezoid_series_l9`.

The written argument for display 40: `ψ` is continuous and piecewise linear with slope
`± 4/Δ`, so two integrations by parts give `c_h = -(π² h² Δ)⁻¹ (1 - e(-hΔ/4) -
e(-h(1/2 - Δ/4)) + e(-h/2))` for `h ≠ 0`, whence `|c_h| ≤ 4/(π² Δ h²)`. The formula was
checked numerically against a Riemann sum to 1e-10 for several `Δ` and `h`.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Prep1121Trapezoid

open Real
open LeanLab.ExceptionalSet.U1539 (eC hcheck norm_eC)
open LeanLab.ExceptionalSet.DQLemma9 (trapL9)

/-- PROVED. P0082 page 370 display 40, one integration by parts done twice: for an affine
`c₀ + c₁ t`, `∫_a^b (c₀ + c₁ t) e^{-wt} dt = G(b) - G(a)` with
`G(t) = -(c₀ + c₁ t) e^{-wt}/w - c₁ e^{-wt}/w²`, `w ≠ 0`. A fundamental theorem of calculus
lookup. -/
theorem leaf_affine_exp_integral (a b : ℝ) (c₀ c₁ w : ℂ) (hw : w ≠ 0) :
    ∫ t in a..b, (c₀ + c₁ * (t : ℂ)) * Complex.exp (-(w * t)) =
      (-(c₀ + c₁ * (b : ℂ)) * Complex.exp (-(w * b)) / w - c₁ * Complex.exp (-(w * b)) / w ^ 2) -
      (-(c₀ + c₁ * (a : ℂ)) * Complex.exp (-(w * a)) / w - c₁ * Complex.exp (-(w * a)) / w ^ 2) := by
  have hE : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(w * t)))
      (Complex.exp (-(w * t)) * (-w)) t := by
    intro t
    have hc : HasDerivAt (fun z : ℂ => -w * z) (-w) (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).const_mul (-w)
    have hc' := hc.comp_ofReal.cexp
    simp only [neg_mul] at hc'
    exact hc'
  have hL : ∀ t : ℝ, HasDerivAt (fun t : ℝ => c₀ + c₁ * (t : ℂ)) c₁ t := by
    intro t
    have hc : HasDerivAt (fun z : ℂ => c₀ + c₁ * z) c₁ (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).const_mul c₁).const_add c₀
    exact hc.comp_ofReal
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => (-(c₀ + c₁ * (t : ℂ))) * Complex.exp (-(w * t)) / w -
      c₁ * Complex.exp (-(w * t)) / w ^ 2)
  · intro t _
    have hG := (((hL t).neg.mul (hE t)).div_const w).sub ((hE t).const_mul c₁ |>.div_const (w ^ 2))
    refine hG.congr_deriv ?_
    simp only [Pi.neg_apply]
    field_simp
    ring
  · apply Continuous.intervalIntegrable
    fun_prop

/-- On `[0, Δ/4]` the trapezoid is the ramp `4t/Δ`. PROVED. -/
theorem trap_piece_rise (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (t : ℝ) (h0 : 0 ≤ t)
    (h1 : t ≤ Δ / 4) : trapL9 Δ t = 4 * t / Δ := by
  have hf : Int.fract t = t := Int.fract_eq_self.mpr ⟨h0, by linarith⟩
  unfold trapL9
  rw [hf]
  have hA : 4 * t / Δ ≤ 4 * (1 / 2 - t) / Δ := div_le_div_of_nonneg_right (by linarith) hΔ0.le
  have hB : 4 * t / Δ ≤ 1 := by rw [div_le_one hΔ0]; linarith
  rw [min_eq_left hA, min_eq_right hB, max_eq_right (by positivity)]

/-- On `[Δ/4, 1/2 - Δ/4]` the trapezoid is `1`. PROVED. -/
theorem trap_piece_flat (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (t : ℝ) (h0 : Δ / 4 ≤ t)
    (h1 : t ≤ 1 / 2 - Δ / 4) : trapL9 Δ t = 1 := by
  have hf : Int.fract t = t := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  unfold trapL9
  rw [hf]
  have hA : 1 ≤ 4 * t / Δ := by rw [le_div_iff₀ hΔ0]; linarith
  have hB : 1 ≤ 4 * (1 / 2 - t) / Δ := by rw [le_div_iff₀ hΔ0]; linarith
  rw [min_eq_left (le_min hA hB), max_eq_right zero_le_one]

/-- On `[1/2 - Δ/4, 1/2]` the trapezoid is the ramp `4(1/2 - t)/Δ`. PROVED. -/
theorem trap_piece_fall (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (t : ℝ) (h0 : 1 / 2 - Δ / 4 ≤ t)
    (h1 : t ≤ 1 / 2) : trapL9 Δ t = 4 * (1 / 2 - t) / Δ := by
  have hf : Int.fract t = t := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  unfold trapL9
  rw [hf]
  have hA : 4 * (1 / 2 - t) / Δ ≤ 4 * t / Δ := div_le_div_of_nonneg_right (by linarith) hΔ0.le
  have hB : 4 * (1 / 2 - t) / Δ ≤ 1 := by rw [div_le_one hΔ0]; linarith
  have hC : 0 ≤ 4 * (1 / 2 - t) / Δ := div_nonneg (by linarith) hΔ0.le
  rw [min_eq_right hA, min_eq_right hB, max_eq_right hC]

/-- PROVED. P0082 page 370, `ψ` is continuous. The two pieces of `trapL9` agree at the jumps
of `Int.fract`: at an integer both the left limit, where `1/2 - {β} → -1/2`, and the value,
where `{β} = 0`, give `0` after `max 0`. -/
theorem leaf_trap_continuous (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    Continuous (trapL9 Δ) := by
  set G : ℝ → ℝ := fun t => max 0 (min 1 (min (4 * t / Δ) (4 * (1 / 2 - t) / Δ))) with hGdef
  have hG : Continuous G := by
    rw [hGdef]
    fun_prop
  have h0 : G 0 = 0 :=
    le_antisymm (max_le le_rfl (min_le_of_right_le (min_le_of_left_le (by simp))))
      (le_max_left _ _)
  have h1 : G 1 = 0 :=
    le_antisymm (max_le le_rfl (min_le_of_right_le (min_le_of_right_le
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hΔ0.le)))) (le_max_left _ _)
  have : trapL9 Δ = G ∘ Int.fract := rfl
  rw [this]
  exact hG.continuousOn.comp_fract'' (h0.trans h1.symm)

/-- `ψ` is `1`-periodic. PROVED. -/
theorem trap_periodic (Δ : ℝ) : Function.Periodic (trapL9 Δ) 1 := by
  intro β
  simp only [trapL9, Int.fract_add_one]

/-- `0 ≤ ψ ≤ 1`. PROVED. -/
theorem trap_bounds (Δ β : ℝ) : 0 ≤ trapL9 Δ β ∧ trapL9 Δ β ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- `ψ = 0` on `[1/2, 1]`. PROVED. -/
theorem trap_zero_upper (Δ : ℝ) (hΔ0 : 0 < Δ) (t : ℝ) (ht : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    trapL9 Δ t = 0 := by
  have hf : 1 / 2 ≤ Int.fract t ∨ Int.fract t = 0 := by
    rcases eq_or_lt_of_le ht1 with h | h
    · right; rw [h]; simp
    · left
      rw [Int.fract_eq_self.mpr ⟨by linarith, h⟩]
      exact ht
  apply le_antisymm _ (le_max_left _ _)
  rcases hf with hf | hf
  · exact max_le le_rfl (min_le_of_right_le (min_le_of_right_le
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hΔ0.le)))
  · exact max_le le_rfl (min_le_of_right_le (min_le_of_left_le (by rw [hf]; simp)))

/-- P0082 page 370 display 40, the exact coefficient, from the leaves above. For `h ≠ 0` the Fourier
coefficient of the trapezoid, which has slope `4/Δ` on `[0, Δ/4]`, slope `0` up to
`1/2 - Δ/4`, slope `-4/Δ` up to `1/2` and is `0` on `[1/2, 1]`, is the second difference of
its derivative jumps over `(2πih)²`. Two integrations by parts on four intervals. -/
theorem leaf_trap_coeff_formula (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (h : ℤ) (hh : h ≠ 0) :
    hcheck (fun t => (trapL9 Δ t : ℂ)) h =
      -(((1 / (Real.pi ^ 2 * (h : ℝ) ^ 2 * Δ) : ℝ)) : ℂ) *
        (1 - eC (-((h : ℝ) * (Δ / 4))) - eC (-((h : ℝ) * (1 / 2 - Δ / 4)))
          + eC (-((h : ℝ) / 2))) := by
  set w : ℂ := 2 * Real.pi * Complex.I * (h : ℂ) with hwdef
  have hw : w ≠ 0 := by
    have : (h : ℂ) ≠ 0 := by exact_mod_cast hh
    rw [hwdef]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) this
  have heC : ∀ t : ℝ, eC (-(t * h)) = Complex.exp (-(w * t)) := by
    intro t; unfold eC; congr 1; rw [hwdef]; push_cast; ring
  have hcont : Continuous (fun α : ℝ => (trapL9 Δ α : ℂ) * eC (-(α * h))) := by
    have := Complex.continuous_ofReal.comp (leaf_trap_continuous Δ hΔ0 hΔ1)
    unfold eC
    fun_prop
  have hii : ∀ a b : ℝ, IntervalIntegrable
      (fun α : ℝ => (trapL9 Δ α : ℂ) * eC (-(α * h))) MeasureTheory.volume a b :=
    fun a b => hcont.intervalIntegrable a b
  set d : ℝ := Δ / 4 with hd
  unfold hcheck
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2) (hii _ _) (hii _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := 1 / 2 - d)
      (hii _ _) (hii _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := d) (hii _ _) (hii _ _)]
  have hd0 : 0 ≤ d := by positivity
  have hdd : d ≤ 1 / 2 - d := by rw [hd]; linarith
  have hI1 : ∫ α in (0 : ℝ)..d, (trapL9 Δ α : ℂ) * eC (-(α * h)) =
      ∫ α in (0 : ℝ)..d, ((0 : ℂ) + ((4 / Δ : ℝ) : ℂ) * (α : ℂ)) * Complex.exp (-(w * α)) := by
    refine intervalIntegral.integral_congr (fun α hα => ?_)
    rw [Set.uIcc_of_le hd0] at hα
    rw [trap_piece_rise Δ hΔ0 hΔ1 α hα.1 hα.2, heC]
    push_cast; ring
  have hI2 : ∫ α in d..(1 / 2 - d), (trapL9 Δ α : ℂ) * eC (-(α * h)) =
      ∫ α in d..(1 / 2 - d), ((1 : ℂ) + (0 : ℂ) * (α : ℂ)) * Complex.exp (-(w * α)) := by
    refine intervalIntegral.integral_congr (fun α hα => ?_)
    rw [Set.uIcc_of_le hdd] at hα
    rw [trap_piece_flat Δ hΔ0 hΔ1 α hα.1 hα.2, heC]
    push_cast; ring
  have hI3 : ∫ α in (1 / 2 - d)..(1 / 2), (trapL9 Δ α : ℂ) * eC (-(α * h)) =
      ∫ α in (1 / 2 - d)..(1 / 2),
        (((2 / Δ : ℝ) : ℂ) + ((-4 / Δ : ℝ) : ℂ) * (α : ℂ)) * Complex.exp (-(w * α)) := by
    refine intervalIntegral.integral_congr (fun α hα => ?_)
    rw [Set.uIcc_of_le (by linarith)] at hα
    rw [trap_piece_fall Δ hΔ0 hΔ1 α hα.1 hα.2, heC]
    push_cast; ring
  have hI4 : ∫ α in (1 / 2 : ℝ)..1, (trapL9 Δ α : ℂ) * eC (-(α * h)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) (fun α hα => ?_)]
    · simp
    · rw [Set.uIcc_of_le (by norm_num)] at hα
      simp [trap_zero_upper Δ hΔ0 α hα.1 hα.2]
  rw [hI1, hI2, hI3, hI4, leaf_affine_exp_integral _ _ _ _ _ hw,
    leaf_affine_exp_integral _ _ _ _ _ hw, leaf_affine_exp_integral _ _ _ _ _ hw]
  have e1 : eC (-((h : ℝ) * (Δ / 4))) = Complex.exp (-(w * d)) := by
    rw [← heC d, hd, mul_comm]
  have e2 : eC (-((h : ℝ) * (1 / 2 - Δ / 4))) = Complex.exp (-(w * (1 / 2 - d : ℝ))) := by
    rw [← heC, hd, mul_comm]
  have e3 : eC (-((h : ℝ) / 2)) = Complex.exp (-(w * (1 / 2 : ℝ))) := by
    rw [← heC]; congr 1; ring
  rw [e1, e2, e3]
  have hw2 : w ^ 2 = -(4 * (Real.pi : ℂ) ^ 2 * (h : ℂ) ^ 2) := by
    rw [hwdef]; ring_nf; rw [Complex.I_sq]; ring
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have hΔ' : (Δ : ℂ) ≠ 0 := by exact_mod_cast hΔ0.ne'
  rw [hw2]
  push_cast
  simp only [mul_zero, neg_zero, Complex.exp_zero]
  rw [hd]
  push_cast
  field_simp
  ring

/-- P0082 page 370, `|c_h| ≤ ∫_0^1 ψ ≤ 1/2`, since `0 ≤ ψ ≤ 1` and `ψ = 0` on
`[1/2, 1]`. PROVED from the continuity above. -/
theorem leaf_trap_coeff_le_half (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (h : ℤ) :
    ‖hcheck (fun t => (trapL9 Δ t : ℂ)) h‖ ≤ 1 / 2 := by
  have hc : Continuous (fun α : ℝ => (trapL9 Δ α : ℂ) * eC (-(α * h))) := by
    have := Complex.continuous_ofReal.comp (leaf_trap_continuous Δ hΔ0 hΔ1)
    unfold eC
    fun_prop
  unfold hcheck
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hz : ∫ α in (1 / 2 : ℝ)..1, (trapL9 Δ α : ℂ) * eC (-(α * h)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) (fun α hα => ?_)]
    · simp
    · rw [Set.uIcc_of_le (by norm_num)] at hα
      simp [trap_zero_upper Δ hΔ0 α hα.1 hα.2]
  rw [hz, add_zero]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1 / 2) (C := 1)
    (f := fun α : ℝ => (trapL9 Δ α : ℂ) * eC (-(α * h))) (fun α _ => by
      rw [norm_mul, norm_eC, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (trap_bounds Δ α).1]
      exact (trap_bounds Δ α).2)
  simpa using hb

/-- The four term second difference has norm at most four. PROVED. -/
theorem four_term_le (x y z : ℝ) : ‖(1 : ℂ) - eC x - eC y + eC z‖ ≤ 4 := by
  calc ‖(1 : ℂ) - eC x - eC y + eC z‖ ≤ ‖(1 : ℂ) - eC x - eC y‖ + ‖eC z‖ := norm_add_le _ _
    _ ≤ (‖(1 : ℂ) - eC x‖ + ‖eC y‖) + ‖eC z‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ((‖(1 : ℂ)‖ + ‖eC x‖) + ‖eC y‖) + ‖eC z‖ := by gcongr; exact norm_sub_le _ _
    _ = 4 := by simp [norm_eC]; norm_num

/-- `4/π² ≤ 41/100`, the numerical step after display 40. PROVED. -/
theorem four_div_pi_sq_le : 4 / Real.pi ^ 2 ≤ 41 / 100 := by
  have hpi := Real.pi_gt_d2
  have hp : (0 : ℝ) < Real.pi ^ 2 := by positivity
  rw [div_le_div_iff₀ hp (by norm_num)]
  nlinarith

/-- P0082 page 370 display 40. Exactly the type of `DQLemma9.leaf_trapezoid_coeff_l9`.
PROVED from `leaf_trap_coeff_formula` and `leaf_trap_coeff_le_half`, both proved above. -/
theorem trapezoid_coeff_split (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (h : ℤ) :
    ‖hcheck (fun t => (trapL9 Δ t : ℂ)) h‖ ≤ 1 / 2 ∧
      (h ≠ 0 → ‖hcheck (fun t => (trapL9 Δ t : ℂ)) h‖ ≤ 41 / 100 / (Δ * (h : ℝ) ^ 2)) := by
  refine ⟨leaf_trap_coeff_le_half Δ hΔ0 hΔ1 h, fun hh => ?_⟩
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  have hh2 : 0 < (h : ℝ) ^ 2 := by positivity
  have hpi : 0 < Real.pi ^ 2 := by positivity
  have hD : 0 < Real.pi ^ 2 * (h : ℝ) ^ 2 * Δ := by positivity
  rw [leaf_trap_coeff_formula Δ hΔ0 hΔ1 h hh, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h4 := four_term_le (-((h : ℝ) * (Δ / 4))) (-((h : ℝ) * (1 / 2 - Δ / 4))) (-((h : ℝ) / 2))
  calc 1 / (Real.pi ^ 2 * (h : ℝ) ^ 2 * Δ) *
        ‖(1 : ℂ) - eC (-((h : ℝ) * (Δ / 4))) - eC (-((h : ℝ) * (1 / 2 - Δ / 4)))
          + eC (-((h : ℝ) / 2))‖
      ≤ 1 / (Real.pi ^ 2 * (h : ℝ) ^ 2 * Δ) * 4 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (4 / Real.pi ^ 2) / (Δ * (h : ℝ) ^ 2) := by field_simp
    _ ≤ 41 / 100 / (Δ * (h : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right four_div_pi_sq_le (by positivity)

/-- PROVED. Fourier inversion with absolutely summable coefficients, page 370 below display 39.
For a continuous `1`-periodic `g : ℝ → ℂ` whose coefficients `hcheck g h` are absolutely
summable, the Fourier series converges to `g` at every point. A bridge from `hcheck` and
`eC` to Mathlib's `fourierCoeff` on `AddCircle 1` and `hasSum_fourier_series_of_summable`. -/
theorem leaf_fourier_inversion (g : ℝ → ℂ) (hc : Continuous g) (hp : Function.Periodic g 1)
    (hs : Summable (fun h : ℤ => ‖hcheck g h‖)) (β : ℝ) :
    HasSum (fun h : ℤ => hcheck g h * eC (h * β)) (g β) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hg01 : g 0 = g (0 + 1) := by rw [hp 0]
  let F : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨AddCircle.liftIco 1 0 g, AddCircle.liftIco_continuous hg01 hc.continuousOn⟩
  have hval : ∀ x : ℝ, F (x : AddCircle (1 : ℝ)) = g x := by
    intro x
    have hfr : g (Int.fract x) = g x := by
      have := hp.sub_int_mul_eq (x := x) ⌊x⌋
      rw [mul_one] at this
      rw [Int.fract, this]
    have hmem : Int.fract x ∈ Set.Ico (0 : ℝ) (0 + 1) :=
      ⟨Int.fract_nonneg x, by rw [zero_add]; exact Int.fract_lt_one x⟩
    show AddCircle.liftIco 1 0 g (x : AddCircle (1 : ℝ)) = g x
    rw [← AddCircle.coe_fract x, AddCircle.liftIco_coe_apply hmem, hfr]
  have hcoef : ∀ n : ℤ, fourierCoeff F n = hcheck g n := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral _ _ 0]
    unfold hcheck
    rw [div_one, one_smul, zero_add]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [hval, fourier_coe_apply, smul_eq_mul, mul_comm]
    unfold eC
    congr 2
    push_cast
    ring
  have hsum : Summable (fourierCoeff F) := by
    refine Summable.of_norm ?_
    simpa only [hcoef] using hs
  have H := has_pointwise_sum_fourier_series_of_summable hsum (β : AddCircle (1 : ℝ))
  rw [hval] at H
  refine H.congr_fun ?_
  intro n
  rw [hcoef, fourier_coe_apply, smul_eq_mul]
  unfold eC
  congr 2
  push_cast
  ring

/-- The coefficients of `ψ` are absolutely summable, from display 40. PROVED. -/
theorem trap_coeff_summable (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    Summable (fun h : ℤ => ‖hcheck (fun t => (trapL9 Δ t : ℂ)) h‖) := by
  have hz : Summable (fun h : ℤ => if h = 0 then (1 / 2 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) (fun h hh => by
      simp only [Finset.mem_singleton] at hh; simp [hh])
  have hq : Summable (fun h : ℤ => 41 / 100 / Δ * (1 / (h : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun h => ?_) (hz.add hq)
  obtain ⟨h1, h2⟩ := trapezoid_coeff_split Δ hΔ0 hΔ1 h
  by_cases hh : h = 0
  · subst hh; simpa using h1
  · have hpos : 0 ≤ 41 / 100 / Δ * (1 / (h : ℝ) ^ 2) := by positivity
    simp only [hh, ite_false, zero_add]
    calc ‖hcheck (fun t => (trapL9 Δ t : ℂ)) h‖ ≤ 41 / 100 / (Δ * (h : ℝ) ^ 2) := h2 hh
      _ = 41 / 100 / Δ * (1 / (h : ℝ) ^ 2) := by field_simp

/-- P0082 page 370, `ψ(α) = Σ_h c_h e(hα)`. Exactly the type of
`DQLemma9.leaf_trapezoid_series_l9`. PROVED, no sorry in this file. -/
theorem trapezoid_series_split (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (β : ℝ) :
    HasSum (fun h : ℤ => hcheck (fun t => (trapL9 Δ t : ℂ)) h * eC (h * β))
      (trapL9 Δ β : ℂ) := by
  have hc : Continuous (fun t => (trapL9 Δ t : ℂ)) :=
    Complex.continuous_ofReal.comp (leaf_trap_continuous Δ hΔ0 hΔ1)
  have hp : Function.Periodic (fun t => (trapL9 Δ t : ℂ)) 1 := fun t => by
    simp only [trap_periodic Δ t]
  exact leaf_fourier_inversion _ hc hp (trap_coeff_summable Δ hΔ0 hΔ1) β

/-- Twin checks: the two splits have exactly the types of the open leaves on main. -/
example : True :=
  let _a : type_of% @LeanLab.ExceptionalSet.DQLemma9.leaf_trapezoid_coeff_l9 :=
    trapezoid_coeff_split
  let _b : type_of% @LeanLab.ExceptionalSet.DQLemma9.leaf_trapezoid_series_l9 :=
    trapezoid_series_split
  trivial

#print axioms trapezoid_coeff_split
#print axioms trapezoid_series_split

end LeanLab.ExceptionalSet.Prep1121Trapezoid
