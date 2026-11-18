/-
The high branch quadrature for `leaf_variation_high_integral` of
`SPLIT_leaf_two_variation_quadrature`, P0069 page 51, the set E2.

The branch of the `two_variation_bound` majorant with `1 ≤ a + 3 b` is the kernel
`1/(a b (99/100 - a - b)(1 - a - b))` on the discarded set. Its integral over the box is about
1.4922 and the target is `3/2`. The proof cuts the region into strips in `a` at the vertices of
the polygon left by the Lemma 33 bands, bounds the kernel on each band of each strip by a
polynomial with third order error, integrates the polynomial exactly, and adds the pieces, which
come to less than 1.4946. The rational coefficients of the cells were computed exactly outside
Lean and every one is rechecked here by `ring` and `norm_num`. No new definition.

This lives in its own module only to keep the memory of each build under the lab cap.
-/
import LeanLab.BHP1997.DensitySlope517

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d Decomp514a
open MeasureTheory Set
open scoped BigOperators

set_option maxHeartbeats 400000

/-- The branch of the majorant of `two_variation_bound` taken when `1 ≤ a + 3 b` lies between
zero and `10^4`. -/
private theorem piece_high_bound {ε : ℝ} (hε8 : ε ≤ 1/10^8) (a b : ℝ) :
    0 ≤ (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0) ∧
      (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0) ≤ 10^4 := by
  by_cases h1 : 1 ≤ a+3*b
  · have hb := two_variation_bound hε8 a b
    rw [ite_eq_left h1] at hb ⊢
    exact hb
  · rw [ite_eq_right h1]
    norm_num

/-! ### the high leaf: generic steps -/

private theorem hv_mIio {f : ℝ → ℝ} {M : ℝ}
    (hm : Measurable f) (hM : ∀ x, ‖f x‖ ≤ M) (lo hi : ℝ) :
    IntervalIntegrable f volume lo hi := by
  refine ⟨Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
      hm.aestronglyMeasurable ?_,
    Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
      hm.aestronglyMeasurable ?_⟩
  · exact Filter.Eventually.of_forall hM
  · exact Filter.Eventually.of_forall hM

private theorem hv_abs_bound {ε : ℝ} (hε8 : ε ≤ 1/10^8) (a b : ℝ) :
    |(if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)| ≤ 10^4 := by
  have h := piece_high_bound hε8 a b
  rw [abs_of_nonneg h.1]
  exact h.2

private theorem hv_measurable (ε : ℝ) :
    Measurable (fun p : ℝ × ℝ => if 1 ≤ p.1 + 3*p.2 then
      (if lowerTwoDiscarded ε p.1 p.2 then 1/(p.1*p.2*(99/100-p.1-p.2)*(1-p.1-p.2)) else 0)
        else 0) := by
  refine Measurable.ite ?_ (Measurable.ite (two_density_region_measurable ε) (by fun_prop)
    measurable_const) measurable_const
  exact measurableSet_le measurable_const (by fun_prop)

/-- The high branch region: the constraints of `lowerTwoDiscarded` that matter when
`1 ≤ a + 3 b`, with the excluded Lemma 33 bands weakened to fixed rational constants. -/
private theorem hv_region {ε a b : ℝ} (hε8 : ε ≤ 1/10^8) (hD : lowerTwoDiscarded ε a b) :
    b ≤ a ∧ a ≤ 1/2 ∧ a+2*b ≤ 1 ∧
      ¬(b ≤ 142/625 ∧ |4*a+3*b-2| ≤ 12497/100000) ∧
      ¬(b ≤ 142/625 ∧ |4*a+b-2| ≤ 12497/100000) := by
  unfold lowerTwoDiscarded at hD
  obtain ⟨hb, hba, ha, hs, hne⟩ := hD
  have hε' : ε ≤ 1/100000000 := by norm_num at hε8 ⊢; exact hε8
  refine ⟨hba, ha, hs, ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    apply hne
    right; right; right
    unfold upperPairRegion
    refine ⟨hba, ha, hb, ?_, Or.inr (Or.inl ?_)⟩
    · norm_num; linarith
    · refine h2.trans ?_
      norm_num; linarith
  · rintro ⟨h1, h2⟩
    apply hne
    right; right; right
    unfold upperPairRegion
    refine ⟨hba, ha, hb, ?_, Or.inr (Or.inr ?_)⟩
    · norm_num; linarith
    · refine h2.trans ?_
      norm_num; linarith

/-- The high branch integrand is interval integrable in `b` for fixed `a`. -/
private theorem hv_Fint {ε : ℝ} (hε8 : ε ≤ 1/10^8) (a x y : ℝ) :
    IntervalIntegrable (fun b : ℝ => (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0))
      volume x y := by
  refine hv_mIio (M := 10^4) ?_ (fun b => ?_) x y
  · refine Measurable.ite ?_ (Measurable.ite ((two_density_region_measurable ε).preimage
      (measurable_const.prodMk measurable_id)) (by fun_prop) measurable_const) measurable_const
    exact measurableSet_le measurable_const (by fun_prop)
  · rw [Real.norm_eq_abs]
    exact hv_abs_bound hε8 a b

/-- The inner integral of the high branch integrand is interval integrable in `a`. -/
private theorem hv_Iint {ε : ℝ} (hε8 : ε ≤ 1/10^8) (x y : ℝ) :
    IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0))
      volume x y := by
  have h4 := four_density_level (fun (a : ℝ) (b : ℝ) => (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0))
    (hv_measurable ε) (fun a b => hv_abs_bound hε8 a b) (1/10) (1/2)
  refine hv_mIio (M := 10^4 * |(1/2:ℝ) - 1/10|) h4.1 (fun z => ?_) x y
  rw [Real.norm_eq_abs]
  exact h4.2 z

/-- Where the open slice misses the high branch region the slice integral is at most zero. -/
private theorem hv_zero {ε a x y : ℝ} (hε8 : ε ≤ 1/10^8) (hxy : x ≤ y)
    (hz : ∀ b, x < b → b < y → 1 ≤ a+3*b → lowerTwoDiscarded ε a b → False) :
    (∫ b in x..y, (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ 0 := by
  have hne : ∀ᵐ b : ℝ ∂volume, b ≠ y := by
    have h : ({y} : Set ℝ)ᶜ ∈ ae (volume : Measure ℝ) := by
      rw [MeasureTheory.compl_mem_ae_iff]
      exact MeasureTheory.measure_singleton y
    exact h
  rw [show (∫ b in x..y, (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0))
      = ∫ b in x..y, ((0:ℝ)) from
    intervalIntegral.integral_congr_ae (by
      filter_upwards [hne] with b hb hmem
      have h2 : b ∈ Set.uIoc x y := hmem
      rw [Set.uIoc_of_le hxy] at h2
      by_cases h1 : 1 ≤ a+3*b
      · rw [ite_eq_left h1, ite_eq_right]
        intro hD
        exact (hz b h2.1 (lt_of_le_of_ne h2.2 hb) h1 hD).elim
      · rw [ite_eq_right h1])]
  rw [intervalIntegral.integral_zero]

/-- Outer step: a pointwise polynomial bound of the inner integral on `[A0, A1]` integrates. -/
private theorem hv_outer {ε A0 A1 v c0 c1 c2 c3 c4 c5 c6 : ℝ} (hε8 : ε ≤ 1/10^8) (hle : A0 ≤ A1)
    (hpt : ∀ a, A0 ≤ a → a ≤ A1 →
      (∫ b in (1/10:ℝ)..(1/2:ℝ), (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0))
        ≤ c0 + c1*a + c2*a^2 + c3*a^3 + c4*a^4 + c5*a^5 + c6*a^6)
    (hv : c0*(A1-A0) + c1*(A1^2-A0^2)/2 + c2*(A1^3-A0^3)/3 + c3*(A1^4-A0^4)/4
        + c4*(A1^5-A0^5)/5 + c5*(A1^6-A0^6)/6 + c6*(A1^7-A0^7)/7 ≤ v) :
    (∫ a in A0..A1, ∫ b in (1/10:ℝ)..(1/2:ℝ), (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ v := by
  have hcont : Continuous (fun a : ℝ => c0 + c1*a + c2*a^2 + c3*a^3 + c4*a^4 + c5*a^5 + c6*a^6) := by
    fun_prop
  have hmono := intervalIntegral.integral_mono_on hle (hv_Iint (ε := ε) hε8 A0 A1)
    (hcont.intervalIntegrable A0 A1) (fun a ha => hpt a ha.1 ha.2)
  have hd : ∀ x ∈ Set.uIcc A0 A1, HasDerivAt
      (fun a : ℝ => c0*a + c1*a^2/2 + c2*a^3/3 + c3*a^4/4 + c4*a^5/5 + c5*a^6/6 + c6*a^7/7)
      (c0 + c1*x + c2*x^2 + c3*x^3 + c4*x^4 + c5*x^5 + c6*x^6) x := by
    intro x _
    have h := (((((((hasDerivAt_id x).const_mul c0).add
      ((hasDerivAt_pow 2 x).const_mul (c1/2))).add
      ((hasDerivAt_pow 3 x).const_mul (c2/3))).add
      ((hasDerivAt_pow 4 x).const_mul (c3/4))).add
      ((hasDerivAt_pow 5 x).const_mul (c4/5))).add
      ((hasDerivAt_pow 6 x).const_mul (c5/6))).add
      ((hasDerivAt_pow 7 x).const_mul (c6/7))
    convert h using 1
    · funext a
      simp only [Pi.add_apply, id]
      ring
    · norm_num
      ring
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable A0 A1)
  rw [hF] at hmono
  refine hmono.trans (le_trans (le_of_eq ?_) hv)
  ring

/-- Integral of a quartic. -/
private theorem hv_int_quartic (k0 k1 k2 k3 k4 l h : ℝ) :
    (∫ b in l..h, (k0 + k1*b + k2*b^2 + k3*b^3 + k4*b^4))
      = k0*(h-l) + k1*(h^2-l^2)/2 + k2*(h^3-l^3)/3 + k3*(h^4-l^4)/4 + k4*(h^5-l^5)/5 := by
  have hd : ∀ x ∈ Set.uIcc l h,
      HasDerivAt (fun b : ℝ => k0*b + k1/2*b^2 + k2/3*b^3 + k3/4*b^4 + k4/5*b^5)
        (k0 + k1*x + k2*x^2 + k3*x^3 + k4*x^4) x := by
    intro x _
    have h1 := (hasDerivAt_id x).const_mul k0
    have h2 := (hasDerivAt_pow 2 x).const_mul (k1/2)
    have h3 := (hasDerivAt_pow 3 x).const_mul (k2/3)
    have h4 := (hasDerivAt_pow 4 x).const_mul (k3/4)
    have h5 := (hasDerivAt_pow 5 x).const_mul (k4/5)
    have hs := (((h1.add h2).add h3).add h4).add h5
    refine (hs.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun b => ?_)
    · push_cast; ring
    · simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

private theorem hv_fa {a A0 A1 : ℝ} (hA0 : 0 < A0) (ha0 : A0 ≤ a) (ha1 : a ≤ A1) :
    1/a ≤ 1/A0 - (a-A0)/(A0*A1) := by
  have ha : 0 < a := lt_of_lt_of_le hA0 ha0
  have hA1 : 0 < A1 := lt_of_lt_of_le ha ha1
  have e : 1/A0 - (a-A0)/(A0*A1) - 1/a = (a-A0)*(A1-a)/(a*A0*A1) := by
    field_simp; ring
  have : 0 ≤ (a-A0)*(A1-a)/(a*A0*A1) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  linarith

private theorem hv_fb {b b0 bm : ℝ} (hbm : 0 < bm) (hb0 : 0 < b0) (hb : bm ≤ b) :
    1/b ≤ 2/b0+1/bm + (-1/b0^2 - 2/(b0*bm))*b + 1/(b0^2*bm)*b^2 := by
  have hbp : 0 < b := lt_of_lt_of_le hbm hb
  have e : 2/b0+1/bm + (-1/b0^2 - 2/(b0*bm))*b + 1/(b0^2*bm)*b^2 - 1/b
      = (b-b0)^2*(b-bm)/(b0^2*bm*b) := by
    field_simp; ring
  have : 0 ≤ (b-b0)^2*(b-bm)/(b0^2*bm*b) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by positivity)
  linarith

private theorem hv_fy {y y0 ym : ℝ} (hy0 : 0 < y0) (hym : 1/8 ≤ ym) (hy : ym ≤ y) :
    1/((y-49/10000)*(y+51/10000)) ≤
      1/y0^2 - 2*(y-y0)/y0^3 + (2*ym+y0)/(y0^3*ym^2)*(y-y0)^2 := by
  have hymp : 0 < ym := by linarith
  have hyp : 0 < y := lt_of_lt_of_le hymp hy
  have h1 : 1/((y-49/10000)*(y+51/10000)) ≤ 1/y^2 := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have e : 1/y0^2 - 2*(y-y0)/y0^3 + (2*ym+y0)/(y0^3*ym^2)*(y-y0)^2 - 1/y^2
      = (y-y0)^2*((y-ym)*(2*ym*y + y0*(y+ym)))/(y0^3*ym^2*y^2) := by
    field_simp; ring
  have : 0 ≤ (y-y0)^2*((y-ym)*(2*ym*y + y0*(y+ym)))/(y0^3*ym^2*y^2) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (by positivity)))
      (by positivity)
  linarith

/-- Pointwise polynomial majorant of the high branch kernel on a cell: the chord of `1/a` on
`[A0, A1]`, the second order expansion of `1/b` at `b0` with the remainder bounded at `bm`, and
the second order expansion of `1/y^2` at `y0` with the remainder bounded at `ym`, where
`y = 9949/10000 - a - b` and `(99/100 - s)(1 - s) ≥ (9949/10000 - s)^2` once `y ≥ 1/8`. -/
private theorem hv_major {a b A0 A1 b0 bm y0 ym : ℝ} (hA0 : 0 < A0) (ha0 : A0 ≤ a) (ha1 : a ≤ A1)
    (hbm : 0 < bm) (hb0 : 0 < b0) (hy0 : 0 < y0) (hym : 1/8 ≤ ym) (hb : bm ≤ b)
    (hy : ym ≤ 9949/10000 - a - b) :
    0 ≤ 1/(a*b*(99/100-a-b)*(1-a-b)) ∧
    1/(a*b*(99/100-a-b)*(1-a-b)) ≤
      (1/A0 - (a-A0)/(A0*A1)) *
        ((2/b0+1/bm + (-1/b0^2 - 2/(b0*bm))*b + 1/(b0^2*bm)*b^2) *
         ((1/y0^2 - 2*(9949/10000-a-y0)/y0^3 + (2*ym+y0)/(y0^3*ym^2)*(9949/10000-a-y0)^2)
           + (2/y0^3 - 2*((2*ym+y0)/(y0^3*ym^2))*(9949/10000-a-y0))*b
           + (2*ym+y0)/(y0^3*ym^2)*b^2)) := by
  have ha : 0 < a := lt_of_lt_of_le hA0 ha0
  have hbp : 0 < b := lt_of_lt_of_le hbm hb
  have h99 : 0 < 99/100-a-b := by linarith
  have h1 : 0 < 1-a-b := by linarith
  have hfa := hv_fa hA0 ha0 ha1
  have hfb := hv_fb hbm hb0 hb
  have hfy := hv_fy (y := 9949/10000 - a - b) hy0 hym hy
  have e1 : (9949/10000 - a - b - 49/10000)*(9949/10000 - a - b + 51/10000)
      = (99/100-a-b)*(1-a-b) := by ring
  have e2 : 1/y0^2 - 2*(9949/10000 - a - b-y0)/y0^3
        + (2*ym+y0)/(y0^3*ym^2)*(9949/10000 - a - b-y0)^2
      = (1/y0^2 - 2*(9949/10000-a-y0)/y0^3 + (2*ym+y0)/(y0^3*ym^2)*(9949/10000-a-y0)^2)
           + (2/y0^3 - 2*((2*ym+y0)/(y0^3*ym^2))*(9949/10000-a-y0))*b
           + (2*ym+y0)/(y0^3*ym^2)*b^2 := by ring
  rw [e1, e2] at hfy
  have e3 : 1/(a*b*(99/100-a-b)*(1-a-b))
      = (1/a) * ((1/b) * (1/((99/100-a-b)*(1-a-b)))) := by
    field_simp
  have n1 : (0:ℝ) ≤ 1/a := by positivity
  have n2 : (0:ℝ) ≤ 1/b := by positivity
  have n3 : (0:ℝ) ≤ 1/((99/100-a-b)*(1-a-b)) := by positivity
  refine ⟨by positivity, ?_⟩
  rw [e3]
  exact mul_le_mul hfa (mul_le_mul hfb hfy n3 (n2.trans hfb)) (mul_nonneg n2 n3) (n1.trans hfa)

/-- Band step: on a band `[l, h]` of `b` inside a cell, the slice integral of the high branch
integrand is at most the exact integral of the polynomial majorant of `hv_major`. -/
private theorem hv_band {ε a A0 A1 b0 bm y0 ym l h p0 p1 p2 q0 q1 q2 : ℝ} (hε8 : ε ≤ 1/10^8)
    (hA0 : 0 < A0) (ha0 : A0 ≤ a) (ha1 : a ≤ A1)
    (hbm : 0 < bm) (hb0 : 0 < b0) (hy0 : 0 < y0) (hym : 1/8 ≤ ym)
    (hl : bm ≤ l) (hlh : l ≤ h) (hh : ym ≤ 9949/10000 - a - h)
    (hp0 : p0 = 2/b0+1/bm) (hp1 : p1 = -1/b0^2 - 2/(b0*bm)) (hp2 : p2 = 1/(b0^2*bm))
    (hq0 : q0 = 1/y0^2 - 2*(9949/10000-a-y0)/y0^3
      + (2*ym+y0)/(y0^3*ym^2)*(9949/10000-a-y0)^2)
    (hq1 : q1 = 2/y0^3 - 2*((2*ym+y0)/(y0^3*ym^2))*(9949/10000-a-y0))
    (hq2 : q2 = (2*ym+y0)/(y0^3*ym^2)) :
    (∫ b in l..h, (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0))
      ≤ (1/A0 - (a-A0)/(A0*A1)) *
        ((p0*q0)*(h-l) + (p0*q1+p1*q0)*(h^2-l^2)/2 + (p0*q2+p1*q1+p2*q0)*(h^3-l^3)/3
          + (p1*q2+p2*q1)*(h^4-l^4)/4 + (p2*q2)*(h^5-l^5)/5) := by
  have hpt : ∀ b ∈ Set.Icc l h, (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)
      ≤ (1/A0 - (a-A0)/(A0*A1)) * ((p0 + p1*b + p2*b^2) * (q0 + q1*b + q2*b^2)) := by
    intro b hb
    have key := hv_major (a := a) (b := b) hA0 ha0 ha1 hbm hb0 hy0 hym (hl.trans hb.1)
      (by linarith [hb.2])
    rw [← hp0, ← hp1, ← hp2, ← hq0, ← hq1, ← hq2] at key
    by_cases h1 : 1 ≤ a+3*b
    · by_cases h2 : lowerTwoDiscarded ε a b
      · rw [ite_eq_left h1, ite_eq_left h2]; exact key.2
      · rw [ite_eq_left h1, ite_eq_right h2]; exact key.1.trans key.2
    · rw [ite_eq_right h1]; exact key.1.trans key.2
  have e : (fun b : ℝ =>
        (1/A0 - (a-A0)/(A0*A1)) * ((p0 + p1*b + p2*b^2) * (q0 + q1*b + q2*b^2)))
      = fun b : ℝ => (1/A0 - (a-A0)/(A0*A1)) * ((p0*q0) + (p0*q1+p1*q0)*b
          + (p0*q2+p1*q1+p2*q0)*b^2 + (p1*q2+p2*q1)*b^3 + (p2*q2)*b^4) := by
    funext b; ring
  have hmono := intervalIntegral.integral_mono_on hlh (hv_Fint hε8 a l h)
    (Continuous.intervalIntegrable (by fun_prop) l h) hpt
  rw [e, intervalIntegral.integral_const_mul, hv_int_quartic] at hmono
  exact hmono

/-! ### the high leaf: the cells, generated by an exact rational computation -/

private theorem hv_piece_left {ε : ℝ} (hε8 : ε ≤ 1/10^8) :
    (∫ a in (1/10:ℝ)..(1/4:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (0:ℝ) := by
  refine hv_outer (c0 := (0:ℝ)) (c1 := (0:ℝ)) (c2 := (0:ℝ)) (c3 := (0:ℝ)) (c4 := (0:ℝ)) (c5 := (0:ℝ)) (c6 := (0:ℝ)) hε8 (by norm_num) (fun a ha0 ha1 => ?_) (by norm_num)
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a (1/10:ℝ) (1/4:ℝ)) (hv_Fint (ε := ε) hε8 a (1/4:ℝ) (1/2:ℝ))
  have s0 := hv_zero (ε := ε) (a := a) (x := (1/10:ℝ)) (y := (1/4:ℝ)) hε8 (by norm_num) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    linarith)
  have s1 := hv_zero (ε := ε) (a := a) (x := (1/4:ℝ)) (y := (1/2:ℝ)) hε8 (by norm_num) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    linarith)
  linarith [e1, s0, s1]

private theorem hv_piece_0 {ε : ℝ} (hε8 : ε ≤ 1/10^8) :
    (∫ a in (1/4:ℝ)..(341/1250:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (227957/10000000:ℝ) := by
  refine hv_outer (c0 := (-212858556761345015232812500/1732254003809149475924379:ℝ)) (c1 := (3271314237259856733587500000/1732254003809149475924379:ℝ)) (c2 := (-22620698586246951612500000000/1732254003809149475924379:ℝ)) (c3 := (28587505470767750000000000000/577418001269716491974793:ℝ)) (c4 := (-181579198771621093750000000000/1732254003809149475924379:ℝ)) (c5 := (6735060371093750000000000000/55879161413198370191109:ℝ)) (c6 := (-9612695312500000000000000000/157477636709922679629489:ℝ)) hε8 (by norm_num) (fun a ha0 ha1 => ?_) (by norm_num)
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a (1/10:ℝ) ((1/3:ℝ) + (-1/3:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1/3:ℝ) + (-1/3:ℝ)*a) (1/2:ℝ))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((1/3:ℝ) + (-1/3:ℝ)*a) ((0:ℝ) + (1:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((0:ℝ) + (1:ℝ)*a) (1/2:ℝ))
  have s0 := hv_zero (ε := ε) (a := a) (x := (1/10:ℝ)) (y := ((1/3:ℝ) + (-1/3:ℝ)*a)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  have s1 : (∫ b in ((1/3:ℝ) + (-1/3:ℝ)*a)..((0:ℝ) + (1:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (-212858556761345015232812500/1732254003809149475924379:ℝ) + (3271314237259856733587500000/1732254003809149475924379:ℝ)*a + (-22620698586246951612500000000/1732254003809149475924379:ℝ)*a^2 + (28587505470767750000000000000/577418001269716491974793:ℝ)*a^3 + (-181579198771621093750000000000/1732254003809149475924379:ℝ)*a^4 + (6735060371093750000000000000/55879161413198370191109:ℝ)*a^5 + (-9612695312500000000000000000/157477636709922679629489:ℝ)*a^6 := by
    refine (hv_band (A0 := (1/4:ℝ)) (A1 := (341/1250:ℝ)) (b0 := (129/500:ℝ)) (bm := (303/1250:ℝ)) (y0 := (59/125:ℝ)) (ym := (4493/10000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s2 := hv_zero (ε := ε) (a := a) (x := ((0:ℝ) + (1:ℝ)*a)) (y := (1/2:ℝ)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  linarith [e1, e2, s0, s1, s2]

private theorem hv_piece_1 {ε : ℝ} (hε8 : ε ≤ 1/10^8) :
    (∫ a in (341/1250:ℝ)..(739/2500:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (139477/2000000:ℝ) := by
  refine hv_outer (c0 := (-477099160541345656991654961687979797335562500000/2714297199578635605443256520319702888734157079:ℝ)) (c1 := (356396850035032808068216045914099727499957750000000/133000562779353144666719569495665441547973696871:ℝ)) (c2 := (-2347744582336682028158086242305710053626875000000000/133000562779353144666719569495665441547973696871:ℝ)) (c3 := (251773050811679177710956409767162488642500000000000/4030320084222822565658168772595922471150718087:ℝ)) (c4 := (-710316192569459716231233532910594500000000000000000/5782633164319701942031285630246323545564073777:ℝ)) (c5 := (561144707107560329878208895489512500000000000000000/4290340734817843376345792564376304566063667641:ℝ)) (c6 := (-105224929486175145063297869000000000000000000000000/1727280036095495385282072331112538201921736323:ℝ)) hε8 (by norm_num) (fun a ha0 ha1 => ?_) (by norm_num)
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a (1/10:ℝ) ((1/3:ℝ) + (-1/3:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1/3:ℝ) + (-1/3:ℝ)*a) (1/2:ℝ))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((1/3:ℝ) + (-1/3:ℝ)*a) ((1/6:ℝ) + (1/3:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1/6:ℝ) + (1/3:ℝ)*a) (1/2:ℝ))
  have e3 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((1/6:ℝ) + (1/3:ℝ)*a) ((0:ℝ) + (1:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((0:ℝ) + (1:ℝ)*a) (1/2:ℝ))
  have s0 := hv_zero (ε := ε) (a := a) (x := (1/10:ℝ)) (y := ((1/3:ℝ) + (-1/3:ℝ)*a)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  have s1 : (∫ b in ((1/3:ℝ) + (-1/3:ℝ)*a)..((1/6:ℝ) + (1/3:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (-1651334037378945262000000000/64650422011182954567434847:ℝ) + (18127595424088516048000000000/64650422011182954567434847:ℝ)*a + (-92970362700468560000000000000/64650422011182954567434847:ℝ)*a^2 + (87361407203070160000000000000/21550140670394318189144949:ℝ)*a^3 + (-346289771527000000000000000000/64650422011182954567434847:ℝ)*a^4 + (218720378900000000000000000000/64650422011182954567434847:ℝ)*a^5 + (-106016000000000000000000000000/64650422011182954567434847:ℝ)*a^6 := by
    refine (hv_band (A0 := (341/1250:ℝ)) (A1 := (739/2500:ℝ)) (b0 := (1/4:ℝ)) (bm := (587/2500:ℝ)) (y0 := (457/1000:ℝ)) (ym := (4341/10000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s2 : (∫ b in ((1/6:ℝ) + (1/3:ℝ)*a)..((0:ℝ) + (1:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (-128743967572130792726562500000/856978390181929418900710983:ℝ) + (100750010788293453116593750000000/41991941118914541526134838167:ℝ)*a + (-680861236194389257296875000000000/41991941118914541526134838167:ℝ)*a^2 + (8259245538731289062500000000000/141387007134392395710891711:ℝ)*a^3 + (-214487117885937500000000000000000/1825736570387588762005862529:ℝ)*a^4 + (172586133007812500000000000000000/1354578745771436823423704457:ℝ)*a^5 + (-32328125000000000000000000000000/545349884661227812027725171:ℝ)*a^6 := by
    refine (hv_band (A0 := (341/1250:ℝ)) (A1 := (739/2500:ℝ)) (b0 := (277/1000:ℝ)) (bm := (161/625:ℝ)) (y0 := (217/500:ℝ)) (ym := (4037/10000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s3 := hv_zero (ε := ε) (a := a) (x := ((0:ℝ) + (1:ℝ)*a)) (y := (1/2:ℝ)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  linarith [e1, e2, e3, s0, s1, s2, s3]

private theorem hv_piece_2 {ε : ℝ} (hε8 : ε ≤ 1/10^8) :
    (∫ a in (739/2500:ℝ)..(199/625:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (151057/1250000:ℝ) := by
  refine hv_outer (c0 := (-42223776140712237856699997480980063632812500/153513630157669845215860456724084470654293:ℝ)) (c1 := (89894309776530685358689113393915489765625000/21930518593952835030837208103440638664899:ℝ)) (c2 := (-563038832166470040882814024715654375000000000/21930518593952835030837208103440638664899:ℝ)) (c3 := (4365221502182929255585795199618773437500000000/51171210052556615071953485574694823551431:ℝ)) (c4 := (-2197070847893666068557257888503906250000000000/13955784559788167746896405156734951877663:ℝ)) (c5 := (24152736280767102907538184772460937500000000000/153513630157669845215860456724084470654293:ℝ)) (c6 := (-954294770582355796780515625000000000000000000/13955784559788167746896405156734951877663:ℝ)) hε8 (by norm_num) (fun a ha0 ha1 => ?_) (by norm_num)
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a (1/10:ℝ) ((1/3:ℝ) + (-1/3:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1/3:ℝ) + (-1/3:ℝ)*a) (1/2:ℝ))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((1/3:ℝ) + (-1/3:ℝ)*a) ((1/6:ℝ) + (1/3:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1/6:ℝ) + (1/3:ℝ)*a) (1/2:ℝ))
  have e3 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((1/6:ℝ) + (1/3:ℝ)*a) ((0:ℝ) + (1:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((0:ℝ) + (1:ℝ)*a) (1/2:ℝ))
  have s0 := hv_zero (ε := ε) (a := a) (x := (1/10:ℝ)) (y := ((1/3:ℝ) + (-1/3:ℝ)*a)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  have s1 : (∫ b in ((1/3:ℝ) + (-1/3:ℝ)*a)..((1/6:ℝ) + (1/3:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (-1536313844764743828125000/46947916992852696586689:ℝ) + (7487105053243768437500000/20120535854079727108581:ℝ)*a + (-12490887130120937500000000/6706845284693242369527:ℝ)*a^2 + (692700278142156250000000000/140843750978558089760067:ℝ)*a^3 + (-871563354054687500000000000/140843750978558089760067:ℝ)*a^4 + (5637589843750000000000000/1422664151298566563233:ℝ)*a^5 + (-258625000000000000000000000/140843750978558089760067:ℝ)*a^6 := by
    refine (hv_band (A0 := (739/2500:ℝ)) (A1 := (199/625:ℝ)) (b0 := (1/4:ℝ)) (bm := (142/625:ℝ)) (y0 := (217/500:ℝ)) (ym := (4037/10000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s2 : (∫ b in ((1/6:ℝ) + (1/3:ℝ)*a)..((0:ℝ) + (1:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (-380693905549799151333007812500/1571003898887195752994891019:ℝ) + (5855034431184576701767578125000/1571003898887195752994891019:ℝ)*a + (-37407722915492338867187500000000/1571003898887195752994891019:ℝ)*a^2 + (42096611260328520507812500000000/523667966295731917664963673:ℝ)*a^3 + (-1963659827575683593750000000000/12983503296588394652850339:ℝ)*a^4 + (240945098342895507812500000000000/1571003898887195752994891019:ℝ)*a^5 + (-9503662109375000000000000000000/142818536262472341181353729:ℝ)*a^6 := by
    refine (hv_band (A0 := (739/2500:ℝ)) (A1 := (199/625:ℝ)) (b0 := (73/250:ℝ)) (bm := (663/2500:ℝ)) (y0 := (99/250:ℝ)) (ym := (3581/10000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s3 := hv_zero (ε := ε) (a := a) (x := ((0:ℝ) + (1:ℝ)*a)) (y := (1/2:ℝ)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  linarith [e1, e2, e3, s0, s1, s2, s3]

private theorem hv_piece_3 {ε : ℝ} (hε8 : ε ≤ 1/10^8) :
    (∫ a in (199/625:ℝ)..(1/3:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (67233/625000:ℝ) := by
  refine hv_outer (c0 := (-47628284023357913700828538683529528662250574070680211905986/143145978071421085005048817955241579623128628042871696381:ℝ)) (c1 := (357527515275468714838037881039280135303940206971048871091673750/71143551101496279247509262523755065072694928137307233101357:ℝ)) (c2 := (-4426960235581323821003251304932886139733029125968290953083984375/142287102202992558495018525047510130145389856274614466202714:ℝ)) (c3 := (14349545619667297689442154451795392436995093810459975396728515625/142287102202992558495018525047510130145389856274614466202714:ℝ)) (c4 := (-1834153972267038303249946955765565087026533790844439697265625000/10163364443070897035358466074822152153242132591043890443051:ℝ)) (c5 := (725121328113035798732632895691654117827120303807067871093750000/4184914770676251720441721324926768533687936949253366653021:ℝ)) (c6 := (-1689417373352171040943846320586230194371601837158203125000000000/23714517033832093082503087507918355024231642712435744367119:ℝ)) hε8 (by norm_num) (fun a ha0 ha1 => ?_) (by norm_num)
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a (1/10:ℝ) ((142/625:ℝ) + (0:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((142/625:ℝ) + (0:ℝ)*a) (1/2:ℝ))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((142/625:ℝ) + (0:ℝ)*a) ((284/1875:ℝ) + (1/3:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((284/1875:ℝ) + (1/3:ℝ)*a) (1/2:ℝ))
  have e3 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((284/1875:ℝ) + (1/3:ℝ)*a) ((142/1875:ℝ) + (2/3:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((142/1875:ℝ) + (2/3:ℝ)*a) (1/2:ℝ))
  have e4 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((142/1875:ℝ) + (2/3:ℝ)*a) ((0:ℝ) + (1:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((0:ℝ) + (1:ℝ)*a) (1/2:ℝ))
  have s0 := hv_zero (ε := ε) (a := a) (x := (1/10:ℝ)) (y := ((142/625:ℝ) + (0:ℝ)*a)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  have s1 : (∫ b in ((142/625:ℝ) + (0:ℝ)*a)..((284/1875:ℝ) + (1/3:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (-999777256736233340222/39292453824934552767:ℝ) + (6291160419736164719191250/19528349550992472725199:ℝ)*a + (-65715351890263256041015625/39056699101984945450398:ℝ)*a^2 + (175607519227132098388671875/39056699101984945450398:ℝ)*a^3 + (-16546204613592529296875000/2789764221570353246457:ℝ)*a^4 + (76181849177551269531250000/19528349550992472725199:ℝ)*a^5 + (-8762298583984375000000000/6509449850330824241733:ℝ)*a^6 := by
    refine (hv_band (A0 := (199/625:ℝ)) (A1 := (1/3:ℝ)) (b0 := (49/200:ℝ)) (bm := (142/625:ℝ)) (y0 := (53/125:ℝ)) (ym := (3989/10000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s2 : (∫ b in ((284/1875:ℝ) + (1/3:ℝ)*a)..((142/1875:ℝ) + (2/3:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (-599763747747222205170124400/7429727153381272558970067:ℝ) + (8777148444562197268096000000/7429727153381272558970067:ℝ)*a + (-52533181579272428979101562500/7429727153381272558970067:ℝ)*a^2 + (23387815324218437011718750000/1061389593340181794138581:ℝ)*a^3 + (-278870146848243408203125000000/7429727153381272558970067:ℝ)*a^4 + (14999907991943359375000000000/437042773728310150527651:ℝ)*a^5 + (-4845715332031250000000000000/353796531113393931379527:ℝ)*a^6 := by
    refine (hv_band (A0 := (199/625:ℝ)) (A1 := (1/3:ℝ)) (b0 := (139/500:ℝ)) (bm := (161/625:ℝ)) (y0 := (391/1000:ℝ)) (ym := (909/2500:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s3 : (∫ b in ((142/1875:ℝ) + (2/3:ℝ)*a)..((0:ℝ) + (1:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (-147290334779911774557053480/650128032511220904134607:ℝ) + (2289703774958713604454700000/650128032511220904134607:ℝ)*a + (-14536624589817875768339843750/650128032511220904134607:ℝ)*a^2 + (48316167136135947265625000000/650128032511220904134607:ℝ)*a^3 + (-89068705311406738281250000000/650128032511220904134607:ℝ)*a^4 + (87798367616943359375000000000/650128032511220904134607:ℝ)*a^5 + (-12178496093750000000000000000/216709344170406968044869:ℝ)*a^6 := by
    refine (hv_band (A0 := (199/625:ℝ)) (A1 := (1/3:ℝ)) (b0 := (311/1000:ℝ)) (bm := (36/125:ℝ)) (y0 := (179/500:ℝ)) (ym := (1641/5000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s4 := hv_zero (ε := ε) (a := a) (x := ((0:ℝ) + (1:ℝ)*a)) (y := (1/2:ℝ)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  linarith [e1, e2, e3, e4, s0, s1, s2, s3, s4]

private theorem hv_piece_4 {ε : ℝ} (hε8 : ε ≤ 1/10^8) :
    (∫ a in (1/3:ℝ)..(144337/400000:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (2094347/10000000:ℝ) := by
  refine hv_outer (c0 := (742887261419794973617989281850153635171145647093507660568710047/17308388499777266678377446464970943125904690551887562527610000:ℝ)) (c1 := (-38992473415931136502645365967258925431907231441887572320213215/122642295655564632463931620666079825577838950196231871624208:ℝ)) (c2 := (249496358315959892380947197036080141355047780189709204637934375/214624017397238106811880336165639694761218162843405775342364:ℝ)) (c3 := (-110807732980890647393797297226839864194408976917443108802734375/53656004349309526702970084041409923690304540710851443835591:ℝ)) (c4 := (102569088561605656590347787991037271995647498677860102539062500/53656004349309526702970084041409923690304540710851443835591:ℝ)) (c5 := (-90997068135970089689364990560804732829223094075761718750000000/53656004349309526702970084041409923690304540710851443835591:ℝ)) (c6 := (22041999309081251554484644828416983786008507812500000000000000/17885334783103175567656694680469974563434846903617147945197:ℝ)) hε8 (by norm_num) (fun a ha0 ha1 => ?_) (by norm_num)
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a (1/10:ℝ) ((142/625:ℝ) + (0:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((142/625:ℝ) + (0:ℝ)*a) (1/2:ℝ))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((142/625:ℝ) + (0:ℝ)*a) ((1193/3750:ℝ) + (-1/6:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1193/3750:ℝ) + (-1/6:ℝ)*a) (1/2:ℝ))
  have e3 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((1193/3750:ℝ) + (-1/6:ℝ)*a) ((767/1875:ℝ) + (-1/3:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((767/1875:ℝ) + (-1/3:ℝ)*a) (1/2:ℝ))
  have e4 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((767/1875:ℝ) + (-1/3:ℝ)*a) ((1/2:ℝ) + (-1/2:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1/2:ℝ) + (-1/2:ℝ)*a) (1/2:ℝ))
  have s0 := hv_zero (ε := ε) (a := a) (x := (1/10:ℝ)) (y := ((142/625:ℝ) + (0:ℝ)*a)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  have s1 : (∫ b in ((142/625:ℝ) + (0:ℝ)*a)..((1193/3750:ℝ) + (-1/6:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (1255162409609929567938042643/70191614077489340127090000:ℝ) + (-2291834525631721753666285/16043797503426134886192:ℝ)*a + (14378249061177317473628125/28076645630995736050836:ℝ)*a^2 + (-68396811813712052734375/84568209731914867623:ℝ)*a^3 + (2997591934169682617187500/7019161407748934012709:ℝ)*a^4 + (-176782930097656250000000/7019161407748934012709:ℝ)*a^5 + (207898437500000000000000/2339720469249644670903:ℝ)*a^6 := by
    refine (hv_band (A0 := (1/3:ℝ)) (A1 := (144337/400000:ℝ)) (b0 := (49/200:ℝ)) (bm := (142/625:ℝ)) (y0 := (81/200:ℝ)) (ym := (47/125:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s2 : (∫ b in ((1193/3750:ℝ) + (-1/6:ℝ)*a)..((767/1875:ℝ) + (-1/3:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (459750535031873223849525650/33773310585419522888798667:ℝ) + (-103638218777946664014578750000/1046972628148005209552758677:ℝ)*a + (372753870573082256501269531250/1046972628148005209552758677:ℝ)*a^2 + (-645101297660517563476562500000/1046972628148005209552758677:ℝ)*a^3 + (585842907207493896484375000000/1046972628148005209552758677:ℝ)*a^4 + (-566841933847656250000000000000/1046972628148005209552758677:ℝ)*a^5 + (1765625000000000000000000000/4204709349991988793384573:ℝ)*a^6 := by
    refine (hv_band (A0 := (1/3:ℝ)) (A1 := (144337/400000:ℝ)) (b0 := (139/500:ℝ)) (bm := (2579/10000:ℝ)) (y0 := (93/250:ℝ)) (ym := (863/2500:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s3 : (∫ b in ((767/1875:ℝ) + (-1/3:ℝ)*a)..((1/2:ℝ) + (-1/2:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (224441796696354520982062621400/19643300051733570677554659789:ℝ) + (-1494845096153081921217477500000/19643300051733570677554659789:ℝ)*a + (5781883502262346155742578125000/19643300051733570677554659789:ℝ)*a^2 + (-12575937136394699886718750000000/19643300051733570677554659789:ℝ)*a^3 + (18169810505578530273437500000000/19643300051733570677554659789:ℝ)*a^4 + (-22183930337265625000000000000000/19643300051733570677554659789:ℝ)*a^5 + (100812500000000000000000000000/139314184764067877145777729:ℝ)*a^6 := by
    refine (hv_band (A0 := (1/3:ℝ)) (A1 := (144337/400000:ℝ)) (b0 := (311/1000:ℝ)) (bm := (2887/10000:ℝ)) (y0 := (339/1000:ℝ)) (ym := (393/1250:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s4 := hv_zero (ε := ε) (a := a) (x := ((1/2:ℝ) + (-1/2:ℝ)*a)) (y := (1/2:ℝ)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  linarith [e1, e2, e3, e4, s0, s1, s2, s3, s4]

private theorem hv_piece_5 {ε : ℝ} (hε8 : ε ≤ 1/10^8) :
    (∫ a in (144337/400000:ℝ)..(37499/100000:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (55387/500000:ℝ) := by
  refine hv_outer (c0 := (-17872055696501284518998698262843017301205770734897114699943773799254843729495/251988530123614149223384090243436195156731589040221429824068666743571901824:ℝ)) (c1 := (1597217961789943597159624142334293888838714114421161417738546549087467173484375/2062031141591896140743138559893832793403075904958597682444276188129318285908:ℝ)) (c2 := (-12673448820277862100864616023906436040386379291786729234170226480492031250000000/3608554497785818246300492479814207388455382833677545944277483329226307000339:ℝ)) (c3 := (30219278386401966468457911987438659192958143892918496560218781400390625000000000/3608554497785818246300492479814207388455382833677545944277483329226307000339:ℝ)) (c4 := (-1012684427086072657379587705877208667640180570723436244845228271484375000000000/97528499940157249900013310265248848336631968477771512007499549438548837847:ℝ)) (c5 := (26785671749460911870250011640937025797963099766717377437255859375000000000000000/3608554497785818246300492479814207388455382833677545944277483329226307000339:ℝ)) (c6 := (-16737474379641264514581154412914561671798876630371093750000000000000000000000/5410126683337058840030723358042289937714217141945346243294577704986967017:ℝ)) hε8 (by norm_num) (fun a ha0 ha1 => ?_) (by norm_num)
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a (1/10:ℝ) ((212497/300000:ℝ) + (-4/3:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((212497/300000:ℝ) + (-4/3:ℝ)*a) (1/2:ℝ))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((212497/300000:ℝ) + (-4/3:ℝ)*a) ((287497/450000:ℝ) + (-19/18:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((287497/450000:ℝ) + (-19/18:ℝ)*a) (1/2:ℝ))
  have e3 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((287497/450000:ℝ) + (-19/18:ℝ)*a) ((512497/900000:ℝ) + (-7/9:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((512497/900000:ℝ) + (-7/9:ℝ)*a) (1/2:ℝ))
  have e4 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((512497/900000:ℝ) + (-7/9:ℝ)*a) ((1/2:ℝ) + (-1/2:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1/2:ℝ) + (-1/2:ℝ)*a) (1/2:ℝ))
  have s0 := hv_zero (ε := ε) (a := a) (x := (1/10:ℝ)) (y := ((212497/300000:ℝ) + (-4/3:ℝ)*a)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  have s1 : (∫ b in ((212497/300000:ℝ) + (-4/3:ℝ)*a)..((287497/450000:ℝ) + (-19/18:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (-243770637603511915767747484097555/4991985239353365113012375524224:ℝ) + (471026962438963669211724303752828125/813849593553328306080798847183644:ℝ)*a + (-562058532092309778396307906250000000/203462398388332076520199711795911:ℝ)*a^2 + (17726847353979179594140625000000000/2642368810238078915846749503843:ℝ)*a^3 + (-245503388063559058837890625000000000/29066056912618868074314244542273:ℝ)*a^4 + (1119651848750732421875000000000000000/203462398388332076520199711795911:ℝ)*a^5 + (-339752441406250000000000000000000000/203462398388332076520199711795911:ℝ)*a^6 := by
    refine (hv_band (A0 := (144337/400000:ℝ)) (A1 := (37499/100000:ℝ)) (b0 := (233/1000:ℝ)) (bm := (2083/10000:ℝ)) (y0 := (197/500:ℝ)) (ym := (47/125:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s2 : (∫ b in ((287497/450000:ℝ) + (-19/18:ℝ)*a)..((512497/900000:ℝ) + (-7/9:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (-96081203760075326510657756816771785/6701715369030663278385061093629201:ℝ) + (14084649135568228936465714288934000000/106270057994629089128677397341834473:ℝ)*a + (-366720607058349314944675291000000000000/743890405962403623900741781392841311:ℝ)*a^2 + (680984390243138498929925000000000000000/743890405962403623900741781392841311:ℝ)*a^3 + (-453660197879124208906250000000000000000/743890405962403623900741781392841311:ℝ)*a^4 + (110665534101812500000000000000000000000/743890405962403623900741781392841311:ℝ)*a^5 + (-160718000000000000000000000000000000000/743890405962403623900741781392841311:ℝ)*a^6 := by
    refine (hv_band (A0 := (144337/400000:ℝ)) (A1 := (37499/100000:ℝ)) (b0 := (133/500:ℝ)) (bm := (243/1000:ℝ)) (y0 := (359/1000:ℝ)) (ym := (3421/10000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s3 : (∫ b in ((512497/900000:ℝ) + (-7/9:ℝ)*a)..((1/2:ℝ) + (-1/2:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (-53805607407765330713445515138629025/6938296433805404287577703424900221:ℝ) + (17124314704566081847520813649880000000/270593560918410767215530433571108619:ℝ)*a + (-9919629255111126812154815000000000000/38656222988344395316504347653015517:ℝ)*a^2 + (203002716968829148502125000000000000000/270593560918410767215530433571108619:ℝ)*a^3 + (-359139608517640897656250000000000000000/270593560918410767215530433571108619:ℝ)*a^4 + (479239726335312500000000000000000000000/270593560918410767215530433571108619:ℝ)*a^5 + (-70000000000000000000000000000000000/57955356804114535706903069944551:ℝ)*a^6 := by
    refine (hv_band (A0 := (144337/400000:ℝ)) (A1 := (37499/100000:ℝ)) (b0 := (299/1000:ℝ)) (bm := (2777/10000:ℝ)) (y0 := (163/500:ℝ)) (ym := (1537/5000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s4 := hv_zero (ε := ε) (a := a) (x := ((1/2:ℝ) + (-1/2:ℝ)*a)) (y := (1/2:ℝ)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  linarith [e1, e2, e3, e4, s0, s1, s2, s3, s4]

private theorem hv_piece_6 {ε : ℝ} (hε8 : ε ≤ 1/10^8) :
    (∫ a in (37499/100000:ℝ)..(314779/800000:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (779831/5000000:ℝ) := by
  refine hv_outer (c0 := (25279492148507981750947307937136432114027653204978276202560888671875/1098276470634363239002863172063830589064166664840472900512739025441:ℝ)) (c1 := (-39190206910745386146925435437655244580194174724927753489223951123046875/267613366677906509237030992926220053535301943999461896758270742532457:ℝ)) (c2 := (153641681484792706761339359867566555587657033024622651553173112792968750/267613366677906509237030992926220053535301943999461896758270742532457:ℝ)) (c3 := (-60977705750189334850789157524677993786159207781308881652733459472656250/47225888237277619277123116398744715329759166588140334722047778093963:ℝ)) (c4 := (554062684118628679332263240788418595947570766056320233537292480468750000/267613366677906509237030992926220053535301943999461896758270742532457:ℝ)) (c5 := (-2558707805529596189200890234563023879660229550927691650390625000000000/1200059940259670445009107591597399343207632035872026442862200639159:ℝ)) (c6 := (724374734813931208538837267085152417116945014291992187500000000000000000/802840100033719527711092978778660160605905831998385690274812227597371:ℝ)) hε8 (by norm_num) (fun a ha0 ha1 => ?_) (by norm_num)
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a (1/10:ℝ) ((1/3:ℝ) + (-1/3:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1/3:ℝ) + (-1/3:ℝ)*a) (1/2:ℝ))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((1/3:ℝ) + (-1/3:ℝ)*a) ((7/18:ℝ) + (-7/18:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((7/18:ℝ) + (-7/18:ℝ)*a) (1/2:ℝ))
  have e3 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((7/18:ℝ) + (-7/18:ℝ)*a) ((4/9:ℝ) + (-4/9:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((4/9:ℝ) + (-4/9:ℝ)*a) (1/2:ℝ))
  have e4 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((4/9:ℝ) + (-4/9:ℝ)*a) ((1/2:ℝ) + (-1/2:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1/2:ℝ) + (-1/2:ℝ)*a) (1/2:ℝ))
  have s0 := hv_zero (ε := ε) (a := a) (x := (1/10:ℝ)) (y := ((1/3:ℝ) + (-1/3:ℝ)*a)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  have s1 : (∫ b in ((1/3:ℝ) + (-1/3:ℝ)*a)..((7/18:ℝ) + (-7/18:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (21671003597360852415400000000000000/3014256495734420094969755146103979:ℝ) + (-33549049720254795519710800000000000000/734473832793953696474297003934002883:ℝ)*a + (132018538365903156247825000000000000000/734473832793953696474297003934002883:ℝ)*a^2 + (-7506353845572984950000000000000000000/18516147045225723440528495897495871:ℝ)*a^3 + (477925011083189781250000000000000000000/734473832793953696474297003934002883:ℝ)*a^4 + (-2206898797000000000000000000000000000/3293604631363021060422856519883421:ℝ)*a^5 + (89235200000000000000000000000000000000/314774499768837298488984430257429807:ℝ)*a^6 := by
    refine (hv_band (A0 := (37499/100000:ℝ)) (A1 := (314779/800000:ℝ)) (b0 := (223/1000:ℝ)) (bm := (2021/10000:ℝ)) (y0 := (389/1000:ℝ)) (ym := (731/2000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s2 : (∫ b in ((7/18:ℝ) + (-7/18:ℝ)*a)..((4/9:ℝ) + (-4/9:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (2093524257906526345676901250000000000/276127304304300206627060798494687569:ℝ) + (-4441363495870220950114696250000000000/92042434768100068875686932831562523:ℝ)*a + (2486575995818770992260937500000000000/13148919252585724125098133261651789:ℝ)*a^2 + (-16774089166584023107812500000000000000/39446757757757172375294399784955367:ℝ)*a^3 + (62749011951261869140625000000000000000/92042434768100068875686932831562523:ℝ)*a^4 + (-64607613790062500000000000000000000000/92042434768100068875686932831562523:ℝ)*a^5 + (82006900000000000000000000000000000000/276127304304300206627060798494687569:ℝ)*a^6 := by
    refine (hv_band (A0 := (37499/100000:ℝ)) (A1 := (314779/800000:ℝ)) (b0 := (257/1000:ℝ)) (bm := (1179/5000:ℝ)) (y0 := (177/500:ℝ)) (ym := (1659/5000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s3 : (∫ b in ((4/9:ℝ) + (-4/9:ℝ)*a)..((1/2:ℝ) + (-1/2:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (259028264097443567059228515625/31411897434209305947777354819:ℝ) + (-1649510515068049140652978515625/31411897434209305947777354819:ℝ)*a + (6447719353787592115646972656250/31411897434209305947777354819:ℝ)*a^2 + (-4822392929357684987487792968750/10470632478069768649259118273:ℝ)*a^3 + (23180126407015101623535156250000/31411897434209305947777354819:ℝ)*a^4 + (-3411158503778076171875000000000/4487413919172757992539622117:ℝ)*a^5 + (206284179687500000000000000000/641059131310393998934231731:ℝ)*a^6 := by
    refine (hv_band (A0 := (37499/100000:ℝ)) (A1 := (314779/800000:ℝ)) (b0 := (291/1000:ℝ)) (bm := (539/2000:ℝ)) (y0 := (8/25:ℝ)) (ym := (2981/10000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s4 := hv_zero (ε := ε) (a := a) (x := ((1/2:ℝ) + (-1/2:ℝ)*a)) (y := (1/2:ℝ)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  linarith [e1, e2, e3, e4, s0, s1, s2, s3, s4]

private theorem hv_piece_7 {ε : ℝ} (hε8 : ε ≤ 1/10^8) :
    (∫ a in (314779/800000:ℝ)..(164783/400000:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (395747/2500000:ℝ) := by
  refine hv_outer (c0 := (66317033929749119399106843460959148579141571857828846156250000000/2410562714092405016516405522396319471873874052490847255719593781:ℝ)) (c1 := (-44766580148476797297710930737596458503314939007191373924718750000000/240252750504543033312801750398833174030096113898254443153386180173:ℝ)) (c2 := (15906928220184059852504595339725620220014996188679868664062500000000/21841159136776639392072886399893924911826919445295858468489652743:ℝ)) (c3 := (-91967955301961888478437070845543978899882717198966408203125000000000/55442942424125315379877327015115347853099103207289486881550656963:ℝ)) (c4 := (57329443749232155318892594557230845623910822123867187500000000000000/21841159136776639392072886399893924911826919445295858468489652743:ℝ)) (c5 := (-87744660918503319520853258237022266689013015175781250000000000000000/34321821500649004758971678628404739147156587699750634736198025739:ℝ)) (c6 := (735891970523774564694292923387938543402978125000000000000000000000000/720758251513629099938405251196499522090288341694763329460158540519:ℝ)) hε8 (by norm_num) (fun a ha0 ha1 => ?_) (by norm_num)
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a (1/10:ℝ) ((1/3:ℝ) + (-1/3:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1/3:ℝ) + (-1/3:ℝ)*a) (1/2:ℝ))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((1/3:ℝ) + (-1/3:ℝ)*a) ((7/18:ℝ) + (-7/18:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((7/18:ℝ) + (-7/18:ℝ)*a) (1/2:ℝ))
  have e3 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((7/18:ℝ) + (-7/18:ℝ)*a) ((4/9:ℝ) + (-4/9:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((4/9:ℝ) + (-4/9:ℝ)*a) (1/2:ℝ))
  have e4 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((4/9:ℝ) + (-4/9:ℝ)*a) ((1/2:ℝ) + (-1/2:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1/2:ℝ) + (-1/2:ℝ)*a) (1/2:ℝ))
  have s0 := hv_zero (ε := ε) (a := a) (x := (1/10:ℝ)) (y := ((1/3:ℝ) + (-1/3:ℝ)*a)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  have s1 : (∫ b in ((1/3:ℝ) + (-1/3:ℝ)*a)..((7/18:ℝ) + (-7/18:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (58885204538610119014062500000000/6832848435072114446341913762199:ℝ) + (-119277807473013540378368750000000000/2043021682086562219456232214897501:ℝ)*a + (42517422931622515758007812500000000/185729243826051110859657474081591:ℝ)*a^2 + (-82136044618326229638671875000000000/157155514006658632265864016530577:ℝ)*a^3 + (153690120772852905273437500000000000/185729243826051110859657474081591:ℝ)*a^4 + (-235098469288574218750000000000000000/291860240298080317065176030699643:ℝ)*a^5 + (72982890625000000000000000000000000/227002409120729135495136912766389:ℝ)*a^6 := by
    refine (hv_band (A0 := (314779/800000:ℝ)) (A1 := (164783/400000:ℝ)) (b0 := (27/125:ℝ)) (bm := (49/250:ℝ)) (y0 := (377/1000:ℝ)) (ym := (1771/5000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s2 : (∫ b in ((7/18:ℝ) + (-7/18:ℝ)*a)..((4/9:ℝ) + (-4/9:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (21400567399635499303655781250000000/2378382420985541254627883757540819:ℝ) + (-48268886324015130716062343750000000/792794140328513751542627919180273:ℝ)*a + (188780390878870278474218750000000000/792794140328513751542627919180273:ℝ)*a^2 + (-1290109596008708877148437500000000000/2378382420985541254627883757540819:ℝ)*a^3 + (680732414315161499023437500000000000/792794140328513751542627919180273:ℝ)*a^4 + (-663477211416992187500000000000000000/792794140328513751542627919180273:ℝ)*a^5 + (795408906250000000000000000000000000/2378382420985541254627883757540819:ℝ)*a^6 := by
    refine (hv_band (A0 := (314779/800000:ℝ)) (A1 := (164783/400000:ℝ)) (b0 := (249/1000:ℝ)) (bm := (1143/5000:ℝ)) (y0 := (43/125:ℝ)) (ym := (643/2000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s3 : (∫ b in ((4/9:ℝ) + (-4/9:ℝ)*a)..((1/2:ℝ) + (-1/2:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (30113811339384019950518000000000000/3043302702999726514862517205299363:ℝ) + (-884411438077017487047328000000000000/13187645046332148231070907889630573:ℝ)*a + (3445387045112201631511750000000000000/13187645046332148231070907889630573:ℝ)*a^2 + (-23488999934569668442750000000000000000/39562935138996444693212723668891719:ℝ)*a^3 + (12379110881779041250000000000000000000/13187645046332148231070907889630573:ℝ)*a^4 + (-12055156493095000000000000000000000000/13187645046332148231070907889630573:ℝ)*a^5 + (14442730400000000000000000000000000000/39562935138996444693212723668891719:ℝ)*a^6 := by
    refine (hv_band (A0 := (314779/800000:ℝ)) (A1 := (164783/400000:ℝ)) (b0 := (141/500:ℝ)) (bm := (2613/10000:ℝ)) (y0 := (31/100:ℝ)) (ym := (2889/10000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s4 := hv_zero (ε := ε) (a := a) (x := ((1/2:ℝ) + (-1/2:ℝ)*a)) (y := (1/2:ℝ)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  linarith [e1, e2, e3, e4, s0, s1, s2, s3, s4]

private theorem hv_piece_8 {ε : ℝ} (hε8 : ε ≤ 1/10^8) :
    (∫ a in (164783/400000:ℝ)..(462509/1100000:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (30741/500000:ℝ) := by
  refine hv_outer (c0 := (39295677475031984966970351982232903194255028702081934272240692069/294573789774488036945071379564153992146260253843335295243072:ℝ)) (c1 := (-406130997248304759434604657634131283456694747645035482760629996875/237604330431308746781166065591841191778351431166086488144176:ℝ)) (c2 := (7144261624232464728174869862337350299933988258827230837584423828125/787064344553710223712612592272973947765789115737661491977583:ℝ)) (c3 := (-160704300762088556807112687867609467309144497268266035030975341796875/6296514756429681789700900738183791582126312925901291935820664:ℝ)) (c4 := (2014114419401155188751712902522778308526011836894959301471710205078125/50372118051437454317607205905470332657010503407210335486565312:ℝ)) (c5 := (-103862710172075226762541547101866851437141066759573519229888916015625/3148257378214840894850450369091895791063156462950645967910332:ℝ)) (c6 := (165535112954557211821498996187247980447280734777450561523437500000/14850270651956796673822879099490074486146964447880405509011:ℝ)) hε8 (by norm_num) (fun a ha0 ha1 => ?_) (by norm_num)
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a (1/10:ℝ) ((1/3:ℝ) + (-1/3:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1/3:ℝ) + (-1/3:ℝ)*a) (1/2:ℝ))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((1/3:ℝ) + (-1/3:ℝ)*a) ((187503/100000:ℝ) + (-4:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((187503/100000:ℝ) + (-4:ℝ)*a) (1/2:ℝ))
  have e3 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((187503/100000:ℝ) + (-4:ℝ)*a) ((142/625:ℝ) + (0:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((142/625:ℝ) + (0:ℝ)*a) (1/2:ℝ))
  have e4 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((142/625:ℝ) + (0:ℝ)*a) ((909/2500:ℝ) + (-1/4:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((909/2500:ℝ) + (-1/4:ℝ)*a) (1/2:ℝ))
  have e5 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((909/2500:ℝ) + (-1/4:ℝ)*a) ((1/2:ℝ) + (-1/2:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1/2:ℝ) + (-1/2:ℝ)*a) (1/2:ℝ))
  have s0 := hv_zero (ε := ε) (a := a) (x := (1/10:ℝ)) (y := ((1/3:ℝ) + (-1/3:ℝ)*a)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  have s1 : (∫ b in ((1/3:ℝ) + (-1/3:ℝ)*a)..((187503/100000:ℝ) + (-4:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (36257293953718675946648431843862/271984391974375846541280981:ℝ) + (-36497380927939821252500822787718400000/21361454006209233691917960890037:ℝ)*a + (30822124141940513645677490244800000000000/3396471186987268157014955781515883:ℝ)*a^2 + (-86673915449944665475553080000000000000000/3396471186987268157014955781515883:ℝ)*a^3 + (45264420747997030921000000000000000000000/1132157062329089385671651927171961:ℝ)*a^4 + (-112039406836401440000000000000000000000000/3396471186987268157014955781515883:ℝ)*a^5 + (714225248000000000000000000000000000000/64084362018627701075753882670111:ℝ)*a^6 := by
    refine (hv_band (A0 := (164783/400000:ℝ)) (A1 := (462509/1100000:ℝ)) (b0 := (21/100:ℝ)) (bm := (1931/10000:ℝ)) (y0 := (371/1000:ℝ)) (ym := (3557/10000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s2 := hv_zero (ε := ε) (a := a) (x := ((187503/100000:ℝ) + (-4:ℝ)*a)) (y := ((142/625:ℝ) + (0:ℝ)*a)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  have s3 : (∫ b in ((142/625:ℝ) + (0:ℝ)*a)..((909/2500:ℝ) + (-1/4:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (750768188004049428588941328125/13232600853181967947795140672:ℝ) + (-26274565350713564518900146484375/59546703839318855765078133024:ℝ)*a + (20386880814133877917633056640625/14886675959829713941269533256:ℝ)*a^2 + (-112639191001654669284820556640625/59546703839318855765078133024:ℝ)*a^3 + (132716422530059039592742919921875/119093407678637711530156266048:ℝ)*a^4 + (-3866594604857265949249267578125/7443337979914856970634766628:ℝ)*a^5 + (700636953115463256835937500000/1860834494978714242658691657:ℝ)*a^6 := by
    refine (hv_band (A0 := (164783/400000:ℝ)) (A1 := (462509/1100000:ℝ)) (b0 := (61/250:ℝ)) (bm := (142/625:ℝ)) (y0 := (42/125:ℝ)) (ym := (3159/10000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s4 : (∫ b in ((909/2500:ℝ) + (-1/4:ℝ)*a)..((1/2:ℝ) + (-1/2:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (16064374496106351515652578125/456929320705694930607306288:ℝ) + (-42281954162416986708711669921875/156269827681347666267698750496:ℝ)*a + (38331684463469693019866943359375/39067456920336916566924687624:ℝ)*a^2 + (-317755591358429101085662841796875/156269827681347666267698750496:ℝ)*a^3 + (113420034423785507678985595703125/39067456920336916566924687624:ℝ)*a^4 + (-29464730662859976291656494140625/9766864230084229141731171906:ℝ)*a^5 + (7263778150081634521484375000000/4883432115042114570865585953:ℝ)*a^6 := by
    refine (hv_band (A0 := (164783/400000:ℝ)) (A1 := (462509/1100000:ℝ)) (b0 := (69/250:ℝ)) (bm := (323/1250:ℝ)) (y0 := (38/125:ℝ)) (ym := (1423/5000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s5 := hv_zero (ε := ε) (a := a) (x := ((1/2:ℝ) + (-1/2:ℝ)*a)) (y := (1/2:ℝ)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  linarith [e1, e2, e3, e4, e5, s0, s1, s2, s3, s4, s5]

private theorem hv_piece_9 {ε : ℝ} (hε8 : ε ≤ 1/10^8) :
    (∫ a in (462509/1100000:ℝ)..(3937583/8800000:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (731693/5000000:ℝ) := by
  refine hv_outer (c0 := (13851670223884179679603008718349323228933660567400000000/117648493262241125913522061819950350703008155525191747:ℝ)) (c1 := (-3518205954856847169224435486550404774582957000000000000/3878521755898059096050177862196165407791477654676651:ℝ)) (c2 := (1030705865571580292241306277807657823367566796875000000000/352945479786723377740566185459851052109024466575575241:ℝ)) (c3 := (-1697992260451217140129902044536397045523437500000000000000/352945479786723377740566185459851052109024466575575241:ℝ)) (c4 := (1757939724543242247862024828345262678527832031250000000000/352945479786723377740566185459851052109024466575575241:ℝ)) (c5 := (-1521327733345007948265455068570054931640625000000000000000/352945479786723377740566185459851052109024466575575241:ℝ)) (c6 := (107533475511748068342795247460937500000000000000000000000/50420782826674768248652312208550150301289209510796463:ℝ)) hε8 (by norm_num) (fun a ha0 ha1 => ?_) (by norm_num)
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a (1/10:ℝ) ((142/625:ℝ) + (0:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((142/625:ℝ) + (0:ℝ)*a) (1/2:ℝ))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((142/625:ℝ) + (0:ℝ)*a) ((909/2500:ℝ) + (-1/4:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((909/2500:ℝ) + (-1/4:ℝ)*a) (1/2:ℝ))
  have e3 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((909/2500:ℝ) + (-1/4:ℝ)*a) ((1/2:ℝ) + (-1/2:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1/2:ℝ) + (-1/2:ℝ)*a) (1/2:ℝ))
  have s0 := hv_zero (ε := ε) (a := a) (x := (1/10:ℝ)) (y := ((142/625:ℝ) + (0:ℝ)*a)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  have s1 : (∫ b in ((142/625:ℝ) + (0:ℝ)*a)..((909/2500:ℝ) + (-1/4:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (1449641565415863387173678600000000/19541599495215657320800972668789:ℝ) + (-3755393807530787812400576500000000000/6624602228878107831751529734719471:ℝ)*a + (11217531261037484614915234375000000000/6624602228878107831751529734719471:ℝ)*a^2 + (-14921691439950945611328125000000000000/6624602228878107831751529734719471:ℝ)*a^3 + (8702835003881955261230468750000000000/6624602228878107831751529734719471:ℝ)*a^4 + (-4235437893765869140625000000000000000/6624602228878107831751529734719471:ℝ)*a^5 + (2857041601562500000000000000000000000/6624602228878107831751529734719471:ℝ)*a^6 := by
    refine (hv_band (A0 := (462509/1100000:ℝ)) (A1 := (3937583/8800000:ℝ)) (b0 := (243/1000:ℝ)) (bm := (142/625:ℝ)) (y0 := (321/1000:ℝ)) (ym := (2957/10000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s2 : (∫ b in ((909/2500:ℝ) + (-1/4:ℝ)*a)..((1/2:ℝ) + (-1/2:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (114104748302925121660045833200000000/2619759907513481883833835137366199:ℝ) + (-381976462522674586456070500000000000/1122754246077206521643072201728371:ℝ)*a + (28929625411211010691983593750000000000/23577839167621336954504516236295791:ℝ)*a^2 + (-4640215579673277763671875000000000000/1813679935970872073423424325868907:ℝ)*a^3 + (28820404255520974121093750000000000000/7859279722540445651501505412098597:ℝ)*a^4 + (-86554866625739746093750000000000000000/23577839167621336954504516236295791:ℝ)*a^5 + (50716015625000000000000000000000000/29807634851607252786984217745001:ℝ)*a^6 := by
    refine (hv_band (A0 := (462509/1100000:ℝ)) (A1 := (3937583/8800000:ℝ)) (b0 := (271/1000:ℝ)) (bm := (2517/10000:ℝ)) (y0 := (147/500:ℝ)) (ym := (2711/10000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s3 := hv_zero (ε := ε) (a := a) (x := ((1/2:ℝ) + (-1/2:ℝ)*a)) (y := (1/2:ℝ)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  linarith [e1, e2, e3, s0, s1, s2, s3]

private theorem hv_piece_10 {ε : ℝ} (hε8 : ε ≤ 1/10^8) :
    (∫ a in (3937583/8800000:ℝ)..(189777/400000:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (613941/5000000:ℝ) := by
  refine hv_outer (c0 := (3280487454078782574654176875000/17185075521587764717193204301:ℝ)) (c1 := (-190266286381249166883406250000000/131752245665506196165147899641:ℝ)) (c2 := (587963310158569340673828125000000/131752245665506196165147899641:ℝ)) (c3 := (-2835809552531415308380126953125000/395256736996518588495443698923:ℝ)) (c4 := (976133442811166763305664062500000/131752245665506196165147899641:ℝ)) (c5 := (-803226162384033203125000000000000/131752245665506196165147899641:ℝ)) (c6 := (1079858398437500000000000000000000/395256736996518588495443698923:ℝ)) hε8 (by norm_num) (fun a ha0 ha1 => ?_) (by norm_num)
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a (1/10:ℝ) ((142/625:ℝ) + (0:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((142/625:ℝ) + (0:ℝ)*a) (1/2:ℝ))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((142/625:ℝ) + (0:ℝ)*a) ((1/2:ℝ) + (-1/2:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1/2:ℝ) + (-1/2:ℝ)*a) (1/2:ℝ))
  have s0 := hv_zero (ε := ε) (a := a) (x := (1/10:ℝ)) (y := ((142/625:ℝ) + (0:ℝ)*a)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  have s1 : (∫ b in ((142/625:ℝ) + (0:ℝ)*a)..((1/2:ℝ) + (-1/2:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (3280487454078782574654176875000/17185075521587764717193204301:ℝ) + (-190266286381249166883406250000000/131752245665506196165147899641:ℝ)*a + (587963310158569340673828125000000/131752245665506196165147899641:ℝ)*a^2 + (-2835809552531415308380126953125000/395256736996518588495443698923:ℝ)*a^3 + (976133442811166763305664062500000/131752245665506196165147899641:ℝ)*a^4 + (-803226162384033203125000000000000/131752245665506196165147899641:ℝ)*a^5 + (1079858398437500000000000000000000/395256736996518588495443698923:ℝ)*a^6 := by
    refine (hv_band (A0 := (3937583/8800000:ℝ)) (A1 := (189777/400000:ℝ)) (b0 := (63/250:ℝ)) (bm := (142/625:ℝ)) (y0 := (289/1000:ℝ)) (ym := (161/625:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s2 := hv_zero (ε := ε) (a := a) (x := ((1/2:ℝ) + (-1/2:ℝ)*a)) (y := (1/2:ℝ)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  linarith [e1, e2, s0, s1, s2]

private theorem hv_piece_11 {ε : ℝ} (hε8 : ε ≤ 1/10^8) :
    (∫ a in (189777/400000:ℝ)..(537491/1100000:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (971443/10000000:ℝ) := by
  refine hv_outer (c0 := (-24216348802596716116293098678751780986868221/41355992488887259338333716152709971968:ℝ)) (c1 := (34225286088300994018360759708976722065690625/5169499061110907417291714519088746496:ℝ)) (c2 := (-11261551016747902896765517736101652880859375/363480402734360677778323677123427488:ℝ)) (c3 := (6967148028510334990389680116777191162109375/90870100683590169444580919280856872:ℝ)) (c4 := (-21036507215827160897392954826354980468750/199276536586820547027589735265037:ℝ)) (c5 := (867969464215966821365036964416503906250000/11358762585448771180572614910107109:ℝ)) (c6 := (-1930560628918649673461914062500000000000/85404229965780234440395600827873:ℝ)) hε8 (by norm_num) (fun a ha0 ha1 => ?_) (by norm_num)
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a (1/10:ℝ) ((212497/100000:ℝ) + (-4:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((212497/100000:ℝ) + (-4:ℝ)*a) (1/2:ℝ))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((212497/100000:ℝ) + (-4:ℝ)*a) ((262497/200000:ℝ) + (-9/4:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((262497/200000:ℝ) + (-9/4:ℝ)*a) (1/2:ℝ))
  have e3 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((262497/200000:ℝ) + (-9/4:ℝ)*a) ((1/2:ℝ) + (-1/2:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1/2:ℝ) + (-1/2:ℝ)*a) (1/2:ℝ))
  have s0 := hv_zero (ε := ε) (a := a) (x := (1/10:ℝ)) (y := ((212497/100000:ℝ) + (-4:ℝ)*a)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  have s1 : (∫ b in ((212497/100000:ℝ) + (-4:ℝ)*a)..((262497/200000:ℝ) + (-9/4:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (-507065498495162587921030704325453475/890083004169876046908427026432:ℝ) + (717315817299275731465447470463984375/111260375521234505863553378304:ℝ)*a + (-236197590918323513885276871337890625/7822995153836801193531096912:ℝ)*a^2 + (2983855227610818713016510009765625/39913240580800006089444372:ℝ)*a^3 + (-883281260823317575454711914062500/8577845563417545168345501:ℝ)*a^4 + (5207652861600160598754882812500000/69848171016400010656527651:ℝ)*a^5 + (-220102596282958984375000000000000/9978310145200001522361093:ℝ)*a^6 := by
    refine (hv_band (A0 := (189777/400000:ℝ)) (A1 := (537491/1100000:ℝ)) (b0 := (26/125:ℝ)) (bm := (213/1250:ℝ)) (y0 := (153/500:ℝ)) (ym := (1377/5000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s2 : (∫ b in ((262497/200000:ℝ) + (-9/4:ℝ)*a)..((1/2:ℝ) + (-1/2:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (-592101095111140107707227220744164319/37297670283058001277346879537152:ℝ) + (269534905697394099097183087347415625/1554069595127416719889453314048:ℝ)*a + (-9589363912694361954328872412109375/12141168711932943124136354016:ℝ)*a^2 + (245343259752963362367401123046875/128251782168305737226792472:ℝ)*a^3 + (-5751092617723641395568847656250/2218780831859090483212053:ℝ)*a^4 + (234897832085261344909667968750000/126470507415968157543087021:ℝ)*a^5 + (-88924310684204101562500000000000/162604938106244773983969027:ℝ)*a^6 := by
    refine (hv_band (A0 := (189777/400000:ℝ)) (A1 := (537491/1100000:ℝ)) (b0 := (119/500:ℝ)) (bm := (213/1000:ℝ)) (y0 := (34/125:ℝ)) (ym := (501/2000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s3 := hv_zero (ε := ε) (a := a) (x := ((1/2:ℝ) + (-1/2:ℝ)*a)) (y := (1/2:ℝ)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  linarith [e1, e2, e3, s0, s1, s2, s3]

private theorem hv_piece_12 {ε : ℝ} (hε8 : ε ≤ 1/10^8) :
    (∫ a in (537491/1100000:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (556697/5000000:ℝ) := by
  refine hv_outer (c0 := (2623485004415551784198330422788392999500845500000/26443473757404639903112543767015215917243211379:ℝ)) (c1 := (-481167625375708582173307407618212280438365500000/596469332873788869995019784218388328960373189:ℝ)) (c2 := (248501657113465692949141635968335565940237575000000/79330421272213919709337631301045647751729634137:ℝ)) (c3 := (-561018966107210718278172296540818744741023437500000/79330421272213919709337631301045647751729634137:ℝ)) (c4 := (776795927091959168815450979348646717475585937500000/79330421272213919709337631301045647751729634137:ℝ)) (c5 := (-592504330079729491144587279630134609375000000000000/79330421272213919709337631301045647751729634137:ℝ)) (c6 := (10844150067249290219683638517578125000000000000000/4666495368953759982902213605943861632454684361:ℝ)) hε8 (by norm_num) (fun a ha0 ha1 => ?_) (by norm_num)
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a (1/10:ℝ) ((1/3:ℝ) + (-1/3:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1/3:ℝ) + (-1/3:ℝ)*a) (1/2:ℝ))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((1/3:ℝ) + (-1/3:ℝ)*a) ((5/12:ℝ) + (-5/12:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((5/12:ℝ) + (-5/12:ℝ)*a) (1/2:ℝ))
  have e3 := intervalIntegral.integral_add_adjacent_intervals (hv_Fint (ε := ε) hε8 a ((5/12:ℝ) + (-5/12:ℝ)*a) ((1/2:ℝ) + (-1/2:ℝ)*a)) (hv_Fint (ε := ε) hε8 a ((1/2:ℝ) + (-1/2:ℝ)*a) (1/2:ℝ))
  have s0 := hv_zero (ε := ε) (a := a) (x := (1/10:ℝ)) (y := ((1/3:ℝ) + (-1/3:ℝ)*a)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  have s1 : (∫ b in ((1/3:ℝ) + (-1/3:ℝ)*a)..((5/12:ℝ) + (-5/12:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (6113368718219311704004000000/129300090789598988109554277:ℝ) + (-1123828648057284392264000000/2916543401269150107734307:ℝ)*a + (581501631686605186621600000000/387900272368796964328662831:ℝ)*a^2 + (-1313785684721606367875000000000/387900272368796964328662831:ℝ)*a^3 + (1818392095273055820312500000000/387900272368796964328662831:ℝ)*a^4 + (-1385797719451093750000000000000/387900272368796964328662831:ℝ)*a^5 + (25342281250000000000000000000/22817663080517468489921343:ℝ)*a^6 := by
    refine (hv_band (A0 := (537491/1100000:ℝ)) (A1 := (1/2:ℝ)) (b0 := (19/100:ℝ)) (bm := (833/5000:ℝ)) (y0 := (311/1000:ℝ)) (ym := (573/2000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s2 : (∫ b in ((5/12:ℝ) + (-5/12:ℝ)*a)..((1/2:ℝ) + (-1/2:ℝ)*a), (if 1 ≤ a+3*b then (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ (462380119141952488801562500000/8903810155044717084546428517:ℝ) + (-11255235685570660299045312500000/26711430465134151253639285551:ℝ)*a + (43630128726382969270140625000000/26711430465134151253639285551:ℝ)*a^2 + (-98431917991457205133789062500000/26711430465134151253639285551:ℝ)*a^3 + (136338406880748335571289062500000/26711430465134151253639285551:ℝ)*a^4 + (-104074524973076171875000000000000/26711430465134151253639285551:ℝ)*a^5 + (32406002685546875000000000000000/26711430465134151253639285551:ℝ)*a^6 := by
    refine (hv_band (A0 := (537491/1100000:ℝ)) (A1 := (1/2:ℝ)) (b0 := (29/125:ℝ)) (bm := (2083/10000:ℝ)) (y0 := (269/1000:ℝ)) (ym := (2449/10000:ℝ)) hε8 (by norm_num) ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) rfl rfl rfl rfl rfl rfl).trans (le_of_eq ?_)
    ring
  have s3 := hv_zero (ε := ε) (a := a) (x := ((1/2:ℝ) + (-1/2:ℝ)*a)) (y := (1/2:ℝ)) hε8 (by linarith) (fun b hb0 hb1 h1 hD => by
    obtain ⟨r1, r2, r3, rX, rY⟩ := hv_region hε8 hD
    first | linarith | exact rX ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩ | exact rY ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  linarith [e1, e2, e3, s0, s1, s2, s3]

/-- P0069 page 51, the set E2: the branch of the majorant taken when `1 ≤ a + 3 b`, integrated
over the box, is at most `3/2`. The cells above add up to less than 1.4946. -/
theorem variation_high_integral_le {ε : ℝ} (hε8 : ε ≤ 1/10^8) :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ 3/2 := by
  have p0 := hv_piece_left (ε := ε) hε8
  have p1 := hv_piece_0 (ε := ε) hε8
  have p2 := hv_piece_1 (ε := ε) hε8
  have p3 := hv_piece_2 (ε := ε) hε8
  have p4 := hv_piece_3 (ε := ε) hε8
  have p5 := hv_piece_4 (ε := ε) hε8
  have p6 := hv_piece_5 (ε := ε) hε8
  have p7 := hv_piece_6 (ε := ε) hε8
  have p8 := hv_piece_7 (ε := ε) hε8
  have p9 := hv_piece_8 (ε := ε) hε8
  have p10 := hv_piece_9 (ε := ε) hε8
  have p11 := hv_piece_10 (ε := ε) hε8
  have p12 := hv_piece_11 (ε := ε) hε8
  have p13 := hv_piece_12 (ε := ε) hε8
  have a0 := intervalIntegral.integral_add_adjacent_intervals (hv_Iint (ε := ε) hε8 (1/10:ℝ) (1/4:ℝ)) (hv_Iint (ε := ε) hε8 (1/4:ℝ) (1/2:ℝ))
  have a1 := intervalIntegral.integral_add_adjacent_intervals (hv_Iint (ε := ε) hε8 (1/4:ℝ) (341/1250:ℝ)) (hv_Iint (ε := ε) hε8 (341/1250:ℝ) (1/2:ℝ))
  have a2 := intervalIntegral.integral_add_adjacent_intervals (hv_Iint (ε := ε) hε8 (341/1250:ℝ) (739/2500:ℝ)) (hv_Iint (ε := ε) hε8 (739/2500:ℝ) (1/2:ℝ))
  have a3 := intervalIntegral.integral_add_adjacent_intervals (hv_Iint (ε := ε) hε8 (739/2500:ℝ) (199/625:ℝ)) (hv_Iint (ε := ε) hε8 (199/625:ℝ) (1/2:ℝ))
  have a4 := intervalIntegral.integral_add_adjacent_intervals (hv_Iint (ε := ε) hε8 (199/625:ℝ) (1/3:ℝ)) (hv_Iint (ε := ε) hε8 (1/3:ℝ) (1/2:ℝ))
  have a5 := intervalIntegral.integral_add_adjacent_intervals (hv_Iint (ε := ε) hε8 (1/3:ℝ) (144337/400000:ℝ)) (hv_Iint (ε := ε) hε8 (144337/400000:ℝ) (1/2:ℝ))
  have a6 := intervalIntegral.integral_add_adjacent_intervals (hv_Iint (ε := ε) hε8 (144337/400000:ℝ) (37499/100000:ℝ)) (hv_Iint (ε := ε) hε8 (37499/100000:ℝ) (1/2:ℝ))
  have a7 := intervalIntegral.integral_add_adjacent_intervals (hv_Iint (ε := ε) hε8 (37499/100000:ℝ) (314779/800000:ℝ)) (hv_Iint (ε := ε) hε8 (314779/800000:ℝ) (1/2:ℝ))
  have a8 := intervalIntegral.integral_add_adjacent_intervals (hv_Iint (ε := ε) hε8 (314779/800000:ℝ) (164783/400000:ℝ)) (hv_Iint (ε := ε) hε8 (164783/400000:ℝ) (1/2:ℝ))
  have a9 := intervalIntegral.integral_add_adjacent_intervals (hv_Iint (ε := ε) hε8 (164783/400000:ℝ) (462509/1100000:ℝ)) (hv_Iint (ε := ε) hε8 (462509/1100000:ℝ) (1/2:ℝ))
  have a10 := intervalIntegral.integral_add_adjacent_intervals (hv_Iint (ε := ε) hε8 (462509/1100000:ℝ) (3937583/8800000:ℝ)) (hv_Iint (ε := ε) hε8 (3937583/8800000:ℝ) (1/2:ℝ))
  have a11 := intervalIntegral.integral_add_adjacent_intervals (hv_Iint (ε := ε) hε8 (3937583/8800000:ℝ) (189777/400000:ℝ)) (hv_Iint (ε := ε) hε8 (189777/400000:ℝ) (1/2:ℝ))
  have a12 := intervalIntegral.integral_add_adjacent_intervals (hv_Iint (ε := ε) hε8 (189777/400000:ℝ) (537491/1100000:ℝ)) (hv_Iint (ε := ε) hε8 (537491/1100000:ℝ) (1/2:ℝ))
  have hC : (0:ℝ) + (227957/10000000:ℝ) + (139477/2000000:ℝ) + (151057/1250000:ℝ) + (67233/625000:ℝ) + (2094347/10000000:ℝ) + (55387/500000:ℝ) + (779831/5000000:ℝ) + (395747/2500000:ℝ) + (30741/500000:ℝ) + (731693/5000000:ℝ) + (613941/5000000:ℝ) + (971443/10000000:ℝ) + (556697/5000000:ℝ) ≤ (3/2:ℝ) := by norm_num
  linarith [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, hC]

end LeanLab.BHP1997.LowerShortC165
