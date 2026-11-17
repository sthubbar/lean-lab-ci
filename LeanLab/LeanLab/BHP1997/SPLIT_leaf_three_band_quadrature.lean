/-
The quadrature of `leaf_three_band_quadrature` of `SPLIT_leaf_two_region_quadrature`: the split of
the integral of `1 / (a b^2)` over the three band union into five convex pieces.

The target asks for `13/10`. Its region is a disjunction of three bands, two of which carry a
further disjunction inside them. This file removes those inner disjunctions: it fixes five convex
pieces, each one fixed branch of one of the three bands, all of them inside the target region,
whose union carries an integral of about `1.3941`. The target is cut into

* `leaf_band_union_membership`, the geometric step: a point of one of the five fixed branches is a
  point of the target region. Linear arithmetic only.
* `leaf_band_union_quadrature`, the computation: the integral of `1 / (a b^2)` over the union of
  the five pieces is at least `13/10`. A floating point quadrature gives about `1.3941`, so the
  margin is about `0.094`; a grid sum over small rectangles inside each of the five pieces would
  prove it, since every piece is an explicit polygon cut out by rational linear inequalities.
* `leaf_band_union_integrand_bound`, the pointwise bound `1000` that the twofold monotonicity
  lemma needs for both integrands.

The assembly `leaf_three_band_quadrature_split` does nothing but compare the two integrands
pointwise, through the membership leaf and the nonnegativity of `1 / (a b^2)` on the region, apply
`slope_two_mono` and add the two numbers.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_two_region_quadrature

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d Decomp514a
open scoped BigOperators

set_option maxHeartbeats 400000


private lemma one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - x⁻¹ ≤ Real.log x := by
  have h1 : 0 < x⁻¹ := by positivity
  have h2 : Real.log x⁻¹ ≤ x⁻¹ - 1 := Real.log_le_sub_one_of_pos h1
  have h3 : Real.log x⁻¹ = -Real.log x := Real.log_inv x
  linarith

/-- `log (8/5) ≥ 3/8`. -/
private lemma log_eight_fifths_ge : (3/8:ℝ) ≤ Real.log (8/5) := by
  have h := one_sub_inv_le_log (by norm_num : (0:ℝ) < 8/5)
  have h' : ((8/5:ℝ))⁻¹ = 5/8 := by norm_num
  rw [h'] at h
  linarith

/-- The `b`-integral of `1 / (a b^2)` over the fixed interval `[1/8, 1/4]`. -/
private lemma one_div_mul_sq_integral (a : ℝ) (ha : a ≠ 0) :
    (∫ b in (1/8:ℝ)..(1/4), (1:ℝ)/(a*b^2)) = 4 * a⁻¹ := by
  have hcongr : (∫ b in (1/8:ℝ)..(1/4), (1:ℝ)/(a*b^2))
      = ∫ b in (1/8:ℝ)..(1/4), a⁻¹ * (b:ℝ) ^ (-2:ℤ) := by
    apply intervalIntegral.integral_congr
    intro b hb
    have h0 : (0:ℝ) ∉ Set.uIcc (1/8:ℝ) (1/4) := by
      rw [Set.uIcc_of_le (by norm_num : (1/8:ℝ) ≤ 1/4)]
      simp
    have hb0 : b ≠ 0 := fun h => h0 (h ▸ hb)
    change (1:ℝ)/(a*b^2) = a⁻¹ * (b:ℝ) ^ (-2:ℤ)
    rw [show (-2:ℤ) = -(2:ℤ) from rfl, zpow_neg, zpow_ofNat]
    field_simp
  rw [hcongr, intervalIntegral.integral_const_mul]
  rw [integral_zpow (n := -2) (Or.inr ⟨by norm_num, by
    rw [Set.uIcc_of_le (by norm_num : (1/8:ℝ) ≤ 1/4)]
    simp⟩)]
  norm_num
  ring

/-- Trimming an interval integral to a subinterval on which the integrand vanishes away from one
endpoint. -/
private lemma interval_trim {φ : ℝ → ℝ} {c d l h : ℝ} (hcl : c ≤ l) (hlh : l ≤ h) (hhd : h ≤ d)
    (hzero : ∀ x, c < x → x ≤ d → ¬ (l < x ∧ x ≤ h) → x ≠ l → φ x = 0) :
    (∫ x in c..d, φ x) = ∫ x in l..h, φ x := by
  rw [intervalIntegral.integral_of_le (le_trans hcl (le_trans hlh hhd)),
    intervalIntegral.integral_of_le hlh]
  apply MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
    measurableSet_Ioc.nullMeasurableSet (Set.Ioc_subset_Ioc hcl hhd)
  have hne : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), x ≠ l := by
    simpa using (Set.countable_singleton l).ae_notMem (MeasureTheory.volume : MeasureTheory.Measure ℝ)
  filter_upwards [hne] with x hxl hx
  exact hzero x hx.1.1 hx.1.2 hx.2 hxl

/-- The `b`-integral of `1 / (a b^2)` over an interval of positive numbers. -/
private lemma integral_inv_sq_box (a l h : ℝ) (ha : a ≠ 0) (hl : 0 < l) (hlh : l ≤ h) :
    (∫ b in l..h, (1:ℝ)/(a*b^2)) = (1/a)*(1/l - 1/h) := by
  have hle : ∀ b ∈ Set.uIcc l h, l ≤ b ∧ b ≤ h := by
    intro b hb
    rw [Set.uIcc_of_le hlh] at hb
    exact hb
  have hderiv : ∀ b ∈ Set.uIcc l h, HasDerivAt (fun b : ℝ => -(1/(a*b))) (1/(a*b^2)) b := by
    intro b hb
    obtain ⟨hb1, hb2⟩ := hle b hb
    have hb0 : b ≠ 0 := by linarith
    have hlin : HasDerivAt (fun b : ℝ => a*b) a b := by
      simpa using (hasDerivAt_id b).const_mul a
    have hneg := (hlin.inv (mul_ne_zero ha hb0)).neg
    convert hneg using 1
    · ext s
      simp [div_eq_mul_inv]
    · have h1 : a*b ≠ 0 := mul_ne_zero ha hb0
      field_simp <;> ring
  have hint : IntervalIntegrable (fun b : ℝ => 1/(a*b^2)) MeasureTheory.volume l h := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_const.mul (continuousOn_id.pow 2)
    · intro b hb
      obtain ⟨hb1, hb2⟩ := hle b hb
      have hb0 : b ≠ 0 := by linarith
      exact mul_ne_zero ha (pow_ne_zero 2 hb0)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hl0 : l ≠ 0 := ne_of_gt hl
  have hh0 : h ≠ 0 := by intro hc'; rw [hc'] at hlh; linarith
  field_simp <;> ring

/-- `∫ 1/a^2` over an interval of positive numbers. -/
private lemma integral_inv_sq_alone {A1 A2 : ℝ} (hA1 : 0 < A1) (hAA : A1 ≤ A2) :
    (∫ a in A1..A2, 1/(a*a)) = 1/A1 - 1/A2 := by
  have hle : ∀ b ∈ Set.uIcc A1 A2, A1 ≤ b ∧ b ≤ A2 := by
    intro b hb
    rw [Set.uIcc_of_le hAA] at hb
    exact hb
  have hderiv : ∀ b ∈ Set.uIcc A1 A2, HasDerivAt (fun b : ℝ => -(1/b)) (1/(b*b)) b := by
    intro b hb
    obtain ⟨hb1, hb2⟩ := hle b hb
    have hb0 : b ≠ 0 := by linarith
    have hneg := ((hasDerivAt_id b).inv hb0).neg
    convert hneg using 1
    · ext s
      simp [div_eq_mul_inv]
    · simp only [id_eq]
      field_simp <;> ring
  have hint : IntervalIntegrable (fun b : ℝ => 1/(b*b)) MeasureTheory.volume A1 A2 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_id.mul continuousOn_id
    · intro b hb
      obtain ⟨hb1, hb2⟩ := hle b hb
      have hb0 : b ≠ 0 := by linarith
      exact mul_ne_zero hb0 hb0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h1 : A1 ≠ 0 := ne_of_gt hA1
  have h2 : A2 ≠ 0 := by intro hc'; rw [hc'] at hAA; linarith
  field_simp <;> ring

/-- `∫ 1/(a(c + e a))` over an interval where `c + e a` stays positive. -/
private lemma integral_inv_mul_inv {c e A1 A2 : ℝ} (hc : c ≠ 0) (hA1 : 0 < A1) (hAA : A1 ≤ A2)
    (hpos : ∀ a, A1 ≤ a → a ≤ A2 → 0 < c + e*a) :
    (∫ a in A1..A2, 1/(a*(c+e*a))) =
      (1/c)*(Real.log (A2/A1) - Real.log ((c+e*A2)/(c+e*A1))) := by
  have hle : ∀ a ∈ Set.uIcc A1 A2, A1 ≤ a ∧ a ≤ A2 := by
    intro a ha
    rw [Set.uIcc_of_le hAA] at ha
    exact ha
  have hderiv : ∀ a ∈ Set.uIcc A1 A2,
      HasDerivAt (fun a : ℝ => (1/c)*Real.log a - (1/c)*Real.log (c+e*a)) (1/(a*(c+e*a))) a := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := hle a ha
    have ha0 : a ≠ 0 := by linarith
    have hca : c + e*a ≠ 0 := ne_of_gt (hpos a ha1 ha2)
    have hlin : HasDerivAt (fun a : ℝ => c + e*a) e a := by
      simpa using ((hasDerivAt_id a).const_mul e).const_add c
    have hl1 : HasDerivAt Real.log a⁻¹ a := Real.hasDerivAt_log ha0
    have hl2 : HasDerivAt (fun a : ℝ => Real.log (c+e*a)) (e/(c+e*a)) a := hlin.log hca
    have hcomb := (hl1.const_mul (1/c)).sub (hl2.const_mul (1/c))
    have h2' : a*e + c ≠ 0 := by
      rw [show a*e + c = c + e*a from by ring]
      exact hca
    have hderiv_eq : (1/c) * a⁻¹ - (1/c) * (e/(c+e*a)) = 1/(a*(c+e*a)) := by
      have h1 : a ≠ 0 := ha0
      have h3 : c ≠ 0 := hc
      have h2'' : c + e*a ≠ 0 := hca
      have hd : (c + a*e) ≠ 0 := by
        rw [show c + a*e = a*e + c from by ring]
        exact h2'
      field_simp <;> ring
    rw [hderiv_eq] at hcomb
    exact hcomb
  have hint : IntervalIntegrable (fun a : ℝ => 1/(a*(c+e*a))) MeasureTheory.volume A1 A2 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_id.mul (continuousOn_const.add (continuousOn_id.const_mul e))
    · intro a ha
      obtain ⟨ha1, ha2⟩ := hle a ha
      have ha0 : a ≠ 0 := by linarith
      exact mul_ne_zero ha0 (ne_of_gt (hpos a ha1 ha2))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h1 : A1 ≠ 0 := ne_of_gt hA1
  have h2 : A2 ≠ 0 := by intro hc'; rw [hc'] at hAA; linarith
  have h3 : c + e*A1 ≠ 0 := ne_of_gt (hpos A1 le_rfl hAA)
  have h4 : c + e*A2 ≠ 0 := ne_of_gt (hpos A2 hAA le_rfl)
  have hL : Real.log (A2/A1) = Real.log A2 - Real.log A1 := Real.log_div h2 h1
  have hR : Real.log ((c+e*A2)/(c+e*A1)) = Real.log (c+e*A2) - Real.log (c+e*A1) :=
    Real.log_div h4 h3
  rw [hL, hR]
  ring

/-- The logarithmic mean bound: `2 (x - 1) / (x + 1) ≤ log x` for `x ≥ 1`. -/
private lemma log_first {x : ℝ} (hx : 1 ≤ x) : 2*(x-1)/(x+1) ≤ Real.log x := by
  have hx0 : 0 < x := by linarith
  have hx1 : (0:ℝ) < x + 1 := by linarith
  have hderiv : ∀ t ∈ Set.uIcc (1:ℝ) x, HasDerivAt (fun t : ℝ => -4/(t+1)) (4/(t+1)^2) t := by
    intro t ht
    have ht1 : (1:ℝ) ≤ t := by
      rcases le_total (1:ℝ) x with h | h
      · rw [Set.uIcc_of_le h] at ht; exact ht.1
      · rw [Set.uIcc_of_ge h] at ht; linarith [ht.1, ht.2]
    have hne : t + 1 ≠ 0 := by positivity
    have hb : HasDerivAt (fun t : ℝ => t + 1) 1 t := by
      simpa using (hasDerivAt_id t).add_const (1:ℝ)
    have hinv := hb.inv hne
    have hmul := hinv.const_mul (-4)
    have heq : -4 * (-1/(t+1)^2) = 4/(t+1)^2 := by
      have h2 : (t+1)^2 ≠ 0 := by positivity
      field_simp
    rw [heq] at hmul
    simpa [div_eq_mul_inv] using hmul
  have hint : IntervalIntegrable (fun t : ℝ => 4/(t+1)^2) MeasureTheory.volume (1:ℝ) x := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact (continuousOn_id.add continuousOn_const).pow 2
    · intro t ht
      have ht1 : (1:ℝ) ≤ t := by
        rcases le_total (1:ℝ) x with h | h
        · rw [Set.uIcc_of_le h] at ht; linarith [ht.1, ht.2]
        · rw [Set.uIcc_of_ge h] at ht; linarith [ht.1, ht.2]
      have h2 : (0:ℝ) < (t+1)^2 := by positivity
      linarith
  have hint2 : IntervalIntegrable (fun t : ℝ => t⁻¹) MeasureTheory.volume (1:ℝ) x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht1 : (1:ℝ) ≤ t := by
      rcases le_total (1:ℝ) x with h | h
      · rw [Set.uIcc_of_le h] at ht; linarith [ht.1, ht.2]
      · rw [Set.uIcc_of_ge h] at ht; linarith [ht.1, ht.2]
    have ht0 : (0:ℝ) < t := by linarith
    exact (continuousAt_inv₀ (ne_of_gt ht0)).continuousWithinAt
  have hval : (∫ t in (1:ℝ)..x, (4:ℝ)/(t+1)^2) = 2*(x-1)/(x+1) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have h2 : x + 1 ≠ 0 := by positivity
    norm_num
    field_simp
    ring
  have hmono : (∫ t in (1:ℝ)..x, (4:ℝ)/(t+1)^2) ≤ ∫ t in (1:ℝ)..x, t⁻¹ := by
    apply intervalIntegral.integral_mono_on hx hint hint2
    intro t ht
    have ht1 : (1:ℝ) ≤ t := ht.1
    have ht0 : (0:ℝ) < t := by linarith
    have ht20 : (0:ℝ) < (t+1)^2 := by positivity
    have hmul : (1:ℝ)/t * (t+1)^2 = (t+1)^2/t := by ring
    rw [div_le_iff₀ ht20, inv_eq_one_div, hmul, le_div_iff₀ ht0]
    nlinarith [sq_nonneg (t - 1)]
  have hlog : (∫ t in (1:ℝ)..x, t⁻¹) = Real.log x := by
    rw [integral_inv_of_pos (by norm_num) hx0]
    norm_num
  linarith

/-- The second order logarithmic bound in the ratio variable: for `0 ≤ t < 1`,
`8 t/(4 - t^2) ≤ log ((1+t)/(1-t))`. -/
private lemma log_second_pos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    8*t/(4 - t^2) ≤ Real.log ((1+t)/(1-t)) := by
  have h1 : (2:ℝ) + t ≠ 0 := by linarith
  have h2 : (2:ℝ) - t ≠ 0 := by linarith
  have h3 : (4:ℝ) - t^2 ≠ 0 := by nlinarith
  have hpos : (0:ℝ) < 1 - t := by linarith
  have hA : 2*t/(2+t) ≤ Real.log (1+t) := by
    have h := log_first (x := 1+t) (by linarith)
    have e1 : 1 + t - 1 = t := by ring
    have e2 : 1 + t + 1 = 2 + t := by ring
    rw [e1, e2] at h
    exact h
  have hB : 2*t/(2-t) ≤ Real.log ((1-t)⁻¹) := by
    have h1' : (1:ℝ) ≤ (1-t)⁻¹ := (one_le_inv₀ hpos).mpr (by linarith)
    have h := log_first (x := (1-t)⁻¹) h1'
    have hs : ((1-t)⁻¹ + 1) ≠ 0 := by
      have hp : (0:ℝ) < (1-t)⁻¹ := by positivity
      linarith
    have e : ((1-t)⁻¹ - 1)/((1-t)⁻¹ + 1) = t/(2-t) := by
      field_simp
      ring
    have h' : 2*((1-t)⁻¹ - 1)/((1-t)⁻¹ + 1) = 2*t/(2-t) := by
      rw [mul_div_assoc, e, ← mul_div_assoc]
    linarith [h, h']
  have hlog : Real.log ((1+t)/(1-t)) = Real.log (1+t) + Real.log ((1-t)⁻¹) := by
    rw [Real.log_div (by linarith) (by linarith), Real.log_inv]
    ring
  have halg : 2*t/(2+t) + 2*t/(2-t) = 8*t/(4 - t^2) := by
    field_simp <;> ring
  linarith

/-- The second order logarithmic bound, in the ratio variable: for `x ≥ 1` with
`t = (x-1)/(x+1)` one has `8 t/(4 - t^2) ≤ log x`. (For `x < 1` this is false; there one uses
`Real.one_sub_inv_le_log_of_pos`.) -/
private lemma log_second {x : ℝ} (hx : 1 ≤ x) :
    8*((x-1)/(x+1))/(4 - ((x-1)/(x+1))^2) ≤ Real.log x := by
  set t := (x-1)/(x+1) with ht
  have hx1 : (0:ℝ) < x + 1 := by linarith
  have ht0 : 0 ≤ t := by
    rw [ht]
    exact div_nonneg (by linarith) (by linarith)
  have ht1 : t < 1 := by
    rw [ht, div_lt_one hx1]
    linarith
  have hxe : x = (1+t)/(1-t) := by
    rw [ht]
    have h1 : (1:ℝ) - t ≠ 0 := by linarith
    field_simp
    ring
  rw [hxe]
  exact log_second_pos ht0 ht1

/-- The quadrature reduction for one trapezoid piece `{(a,b) : A1 ≤ a ≤ A2, c + e a ≤ b ≤ f + g a}`
inside the region `C`: its integral of `1/(a b²)` is at most the integral of the region's
integrand. Uses the two-fold monotonicity `slope_two_mono`, so no Fubini and no parametric
integrability is needed; the inner integral is exact. -/
private lemma piece_lower (C : ℝ → ℝ → Prop)
    (hCb : ∀ a b, C a b → (1/8:ℝ) ≤ b) (hCa : ∀ a b, C a b → b ≤ a)
    (hFm : Measurable (fun p : ℝ × ℝ => if C p.1 p.2 then (1:ℝ)/(p.1*p.2^2) else 0))
    (hFb : ∀ a b, |(if C a b then (1:ℝ)/(a*b^2) else 0)| ≤ 1000)
    {A1 A2 c e f g : ℝ} (hA1 : (1/10:ℝ) ≤ A1) (hA2 : A2 ≤ 1/2) (hAA : A1 ≤ A2)
    (hpos1 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < c + e*a)
    (hpos2 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < f + g*a)
    (hord : ∀ a, A1 ≤ a → a ≤ A2 → c + e*a ≤ f + g*a)
    (hlow : ∀ a, A1 ≤ a → a ≤ A2 → (1/10:ℝ) ≤ c + e*a)
    (hhigh : ∀ a, A1 ≤ a → a ≤ A2 → f + g*a ≤ 1/2)
    (hinc : ∀ a b, A1 ≤ a → a ≤ A2 → c + e*a ≤ b → b ≤ f + g*a → C a b) :
    (∫ a in A1..A2, (1/a)*(1/(c+e*a) - 1/(f+g*a)))
      ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
          (if C a b then (1:ℝ)/(a*b^2) else 0) := by
  set G : ℝ → ℝ → ℝ := fun a b =>
    if (A1 ≤ a ∧ a ≤ A2 ∧ c + e*a ≤ b ∧ b ≤ f + g*a) then (1:ℝ)/(a*b^2) else 0 with hG
  have hGset : MeasurableSet {p : ℝ × ℝ |
      A1 ≤ p.1 ∧ p.1 ≤ A2 ∧ c + e*p.1 ≤ p.2 ∧ p.2 ≤ f + g*p.1} := by
    have hle : ∀ F₁ F₂ : ℝ × ℝ → ℝ, Continuous F₁ → Continuous F₂ →
        MeasurableSet {p | F₁ p ≤ F₂ p} := fun F₁ F₂ h1 h2 => (isClosed_le h1 h2).measurableSet
    simp only [Set.ofPred_and]
    repeat' first
      | apply MeasurableSet.inter
      | (apply hle <;> fun_prop)
  have hGm : Measurable (fun p : ℝ × ℝ => G p.1 p.2) := by
    have : (fun p : ℝ × ℝ => G p.1 p.2) = fun p : ℝ × ℝ =>
        if (A1 ≤ p.1 ∧ p.1 ≤ A2 ∧ c + e*p.1 ≤ p.2 ∧ p.2 ≤ f + g*p.1) then (1:ℝ)/(p.1*p.2^2) else 0 := by
      funext p
      simp only [hG]
    rw [this]
    exact Measurable.ite hGset (by fun_prop) measurable_const
  have hGb : ∀ a b, |G a b| ≤ 1000 := by
    intro a b
    by_cases h : (A1 ≤ a ∧ a ≤ A2 ∧ c + e*a ≤ b ∧ b ≤ f + g*a)
    · have hC : C a b := hinc a b h.1 h.2.1 h.2.2.1 h.2.2.2
      have hb8 : (1/8:ℝ) ≤ b := hCb a b hC
      have hba : b ≤ a := hCa a b hC
      have hb2 : (1/64:ℝ) ≤ b^2 := by nlinarith
      have hmul : (1/8:ℝ)*(1/64) ≤ a*b^2 :=
        mul_le_mul (le_trans hb8 hba) hb2 (by norm_num) (by linarith)
      have hpos : 0 < a*b^2 := by linarith
      have hnn : 0 ≤ (1:ℝ)/(a*b^2) := by positivity
      simp only [hG, if_pos h, abs_of_nonneg hnn]
      rw [div_le_iff₀ hpos]
      linarith
    · simp only [hG, if_neg h, abs_zero]
      norm_num
  have hGle : ∀ a b, G a b ≤ (if C a b then (1:ℝ)/(a*b^2) else 0) := by
    intro a b
    by_cases h : (A1 ≤ a ∧ a ≤ A2 ∧ c + e*a ≤ b ∧ b ≤ f + g*a)
    · have hC : C a b := hinc a b h.1 h.2.1 h.2.2.1 h.2.2.2
      simp only [hG, if_pos h, if_pos hC]
      exact le_rfl
    · simp only [hG, if_neg h]
      split_ifs with hC
      · have hb8 : (1/8:ℝ) ≤ b := hCb a b hC
        have hba : b ≤ a := hCa a b hC
        have hpos : 0 < a*b^2 := by nlinarith
        exact le_of_lt (one_div_pos.2 hpos)
      · exact le_rfl
  have hmono := slope_two_mono G (fun a b => if C a b then (1:ℝ)/(a*b^2) else 0)
    hGm hFm (M := 1000) hGb hFb hGle (lo := 1/10) (hi := 1/2) (by norm_num)
  have hinner : ∀ a ∈ Set.Icc (1/10:ℝ) (1/2),
      (∫ b in (1/10:ℝ)..(1/2:ℝ), G a b)
        = (if A1 ≤ a ∧ a ≤ A2 then (1/a)*(1/(c+e*a) - 1/(f+g*a)) else 0) := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := ha
    by_cases hin : A1 ≤ a ∧ a ≤ A2
    · rw [if_pos hin]
      obtain ⟨hin1, hin2⟩ := hin
      have hga : 0 < c + e*a := hpos1 a hin1 hin2
      have hfa : 0 < f + g*a := hpos2 a hin1 hin2
      have hord' : c + e*a ≤ f + g*a := hord a hin1 hin2
      have hga1 : (1/10:ℝ) ≤ c + e*a := hlow a hin1 hin2
      have hfa1 : f + g*a ≤ 1/2 := hhigh a hin1 hin2
      have htrim : (∫ b in (1/10:ℝ)..(1/2:ℝ), G a b)
          = ∫ b in (c + e*a)..(f + g*a), G a b := by
        apply interval_trim (c := 1/10) (d := 1/2) (l := c + e*a) (h := f + g*a) hga1 hord' hfa1
        intro x hx1 hx2 hx3 hxne
        simp only [hG]
        have hfail : ¬ (A1 ≤ a ∧ a ≤ A2 ∧ c + e*a ≤ x ∧ x ≤ f + g*a) := by
          rintro ⟨-, -, h1, h2⟩
          exact hx3 ⟨lt_of_le_of_ne h1 (Ne.symm hxne), h2⟩
        rw [if_neg hfail]
      rw [htrim]
      have hcongr : (∫ b in (c + e*a)..(f + g*a), G a b)
          = ∫ b in (c + e*a)..(f + g*a), (1:ℝ)/(a*b^2) := by
        apply intervalIntegral.integral_congr
        intro b hb
        have hb' := hb
        rw [Set.uIcc_of_le hord'] at hb'
        simp only [hG]
        rw [if_pos (show A1 ≤ a ∧ a ≤ A2 ∧ c + e*a ≤ b ∧ b ≤ f + g*a from
          ⟨hin1, hin2, hb'.1, hb'.2⟩)]
      rw [hcongr, integral_inv_sq_box a (c + e*a) (f + g*a) (by linarith) hga hord']
    · rw [if_neg hin]
      have hz : ∀ b, G a b = 0 := by
        intro b
        simp only [hG]
        have hfail : ¬ (A1 ≤ a ∧ a ≤ A2 ∧ c + e*a ≤ b ∧ b ≤ f + g*a) := by
          rintro ⟨h1, h2, -⟩
          exact hin ⟨h1, h2⟩
        rw [if_neg hfail]
      simp only [hz]
      simp
  have hval : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G a b)
      = ∫ a in A1..A2, (1/a)*(1/(c+e*a) - 1/(f+g*a)) := by
    have h1 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G a b)
        = ∫ a in (1/10:ℝ)..(1/2:ℝ),
            (if A1 ≤ a ∧ a ≤ A2 then (1/a)*(1/(c+e*a) - 1/(f+g*a)) else 0) := by
      apply intervalIntegral.integral_congr
      intro a ha
      have ha' := ha
      rw [Set.uIcc_of_le (by norm_num : (1/10:ℝ) ≤ 1/2)] at ha'
      exact hinner a ha'
    rw [h1]
    have htrim : (∫ a in (1/10:ℝ)..(1/2:ℝ),
          (if A1 ≤ a ∧ a ≤ A2 then (1/a)*(1/(c+e*a) - 1/(f+g*a)) else 0))
        = ∫ a in A1..A2, (if A1 ≤ a ∧ a ≤ A2 then (1/a)*(1/(c+e*a) - 1/(f+g*a)) else 0) := by
      apply interval_trim hA1 hAA hA2
      intro x hx1 hx2 hx3 hxne
      have hfail : ¬ (A1 ≤ x ∧ x ≤ A2) := by
        rintro ⟨h1, h2⟩
        exact hx3 ⟨lt_of_le_of_ne h1 (Ne.symm hxne), h2⟩
      rw [if_neg hfail]
    rw [htrim]
    apply intervalIntegral.integral_congr
    intro a ha
    have ha' := ha
    rw [Set.uIcc_of_le hAA] at ha'
    simp only []
    exact if_pos ha'
  linarith

/-- Splitting the piece's outer integral into its two logarithmic halves. -/
private lemma outer_split {A1 A2 c e f g : ℝ} (hc : c ≠ 0) (hf : f ≠ 0) (hA1 : 0 < A1)
    (hAA : A1 ≤ A2)
    (hpos1 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < c + e*a)
    (hpos2 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < f + g*a) :
    (∫ a in A1..A2, (1/a)*(1/(c+e*a) - 1/(f+g*a)))
      = (1/c)*(Real.log (A2/A1) - Real.log ((c+e*A2)/(c+e*A1)))
        - (1/f)*(Real.log (A2/A1) - Real.log ((f+g*A2)/(f+g*A1))) := by
  have hle : ∀ a ∈ Set.uIcc A1 A2, A1 ≤ a ∧ a ≤ A2 := by
    intro a ha
    rw [Set.uIcc_of_le hAA] at ha
    exact ha
  have hi1 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(c+e*a))) MeasureTheory.volume A1 A2 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul
    · apply ContinuousOn.div continuousOn_const continuousOn_id
      intro a ha
      have h1 : A1 ≤ a := (hle a ha).1
      have h2 : (0:ℝ) < a := by linarith
      simpa using h2.ne'
    · apply ContinuousOn.div continuousOn_const
        (continuousOn_const.add (continuousOn_id.const_mul e))
      intro a ha
      exact ne_of_gt (hpos1 a (hle a ha).1 (hle a ha).2)
  have hi2 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(f+g*a))) MeasureTheory.volume A1 A2 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul
    · apply ContinuousOn.div continuousOn_const continuousOn_id
      intro a ha
      have h1 : A1 ≤ a := (hle a ha).1
      have h2 : (0:ℝ) < a := by linarith
      simpa using h2.ne'
    · apply ContinuousOn.div continuousOn_const
        (continuousOn_const.add (continuousOn_id.const_mul g))
      intro a ha
      exact ne_of_gt (hpos2 a (hle a ha).1 (hle a ha).2)
  have hcongr : (∫ a in A1..A2, (1/a)*(1/(c+e*a) - 1/(f+g*a)))
      = ∫ a in A1..A2, ((1/a)*(1/(c+e*a)) - (1/a)*(1/(f+g*a))) := by
    apply intervalIntegral.integral_congr
    intro a ha
    ring
  have hsub : (∫ a in A1..A2, ((1/a)*(1/(c+e*a)) - (1/a)*(1/(f+g*a))))
      = (∫ a in A1..A2, (1/a)*(1/(c+e*a))) - ∫ a in A1..A2, (1/a)*(1/(f+g*a)) :=
    intervalIntegral.integral_sub hi1 hi2
  have e1 : (∫ a in A1..A2, (1/a)*(1/(c+e*a)))
      = (1/c)*(Real.log (A2/A1) - Real.log ((c+e*A2)/(c+e*A1))) := by
    rw [← integral_inv_mul_inv (c := c) (e := e) hc hA1 hAA hpos1]
    apply intervalIntegral.integral_congr
    intro a ha
    have h1 : A1 ≤ a ∧ a ≤ A2 := hle a ha
    have ha0 : a ≠ 0 := by linarith [h1.1]
    have h2 : c + e*a ≠ 0 := ne_of_gt (hpos1 a h1.1 h1.2)
    field_simp
  have e2 : (∫ a in A1..A2, (1/a)*(1/(f+g*a)))
      = (1/f)*(Real.log (A2/A1) - Real.log ((f+g*A2)/(f+g*A1))) := by
    rw [← integral_inv_mul_inv (c := f) (e := g) hf hA1 hAA hpos2]
    apply intervalIntegral.integral_congr
    intro a ha
    have h1 : A1 ≤ a ∧ a ≤ A2 := hle a ha
    have ha0 : a ≠ 0 := by linarith [h1.1]
    have h2 : f + g*a ≠ 0 := ne_of_gt (hpos2 a h1.1 h1.2)
    field_simp
  rw [hcongr, hsub, e1, e2]

/-- The piece integrand is interval integrable where its two denominators stay positive. -/
private lemma piece_integrand_integrable {c e f g A1 A2 : ℝ} (hA1 : 0 < A1) (hAA : A1 ≤ A2)
    (hpos1 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < c + e*a)
    (hpos2 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < f + g*a) :
    IntervalIntegrable (fun a : ℝ => (1/a)*(1/(c+e*a) - 1/(f+g*a))) MeasureTheory.volume A1 A2 := by
  have hle : ∀ a ∈ Set.uIcc A1 A2, A1 ≤ a ∧ a ≤ A2 := by
    intro a ha
    rw [Set.uIcc_of_le hAA] at ha
    exact ha
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.mul
  · apply ContinuousOn.div continuousOn_const continuousOn_id
    intro a ha
    have h1 : A1 ≤ a := (hle a ha).1
    have h2 : (0:ℝ) < a := by linarith
    simpa using h2.ne'
  · apply ContinuousOn.sub
    · apply ContinuousOn.div continuousOn_const
        (continuousOn_const.add (continuousOn_id.const_mul e))
      intro a ha
      exact ne_of_gt (hpos1 a (hle a ha).1 (hle a ha).2)
    · apply ContinuousOn.div continuousOn_const
        (continuousOn_const.add (continuousOn_id.const_mul g))
      intro a ha
      exact ne_of_gt (hpos2 a (hle a ha).1 (hle a ha).2)

/-- `outer_split` for a right end point `δ(a) = a`: the second half is `∫ 1/a²`. -/
private lemma outer_split_zero {A1 A2 c e : ℝ} (hc : c ≠ 0) (hA1 : 0 < A1) (hAA : A1 ≤ A2)
    (hpos1 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < c + e*a) :
    (∫ a in A1..A2, (1/a)*(1/(c+e*a) - 1/(0 + 1*a)))
      = (1/c)*(Real.log (A2/A1) - Real.log ((c+e*A2)/(c+e*A1))) - (1/A1 - 1/A2) := by
  have hle : ∀ a ∈ Set.uIcc A1 A2, A1 ≤ a ∧ a ≤ A2 := by
    intro a ha
    rw [Set.uIcc_of_le hAA] at ha
    exact ha
  have hinv : ∀ a ∈ Set.uIcc A1 A2, (0:ℝ) < a := by
    intro a ha
    have h1 : A1 ≤ a := (hle a ha).1
    linarith
  have hi1 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(c+e*a))) MeasureTheory.volume A1 A2 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul
    · apply ContinuousOn.div continuousOn_const continuousOn_id
      intro a ha
      exact ne_of_gt (hinv a ha)
    · apply ContinuousOn.div continuousOn_const
        (continuousOn_const.add (continuousOn_id.const_mul e))
      intro a ha
      exact ne_of_gt (hpos1 a (hle a ha).1 (hle a ha).2)
  have hi2 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/a)) MeasureTheory.volume A1 A2 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul
    · apply ContinuousOn.div continuousOn_const continuousOn_id
      intro a ha
      exact ne_of_gt (hinv a ha)
    · apply ContinuousOn.div continuousOn_const continuousOn_id
      intro a ha
      exact ne_of_gt (hinv a ha)
  have hcongr : (∫ a in A1..A2, (1/a)*(1/(c+e*a) - 1/(0 + 1*a)))
      = ∫ a in A1..A2, ((1/a)*(1/(c+e*a)) - (1/a)*(1/a)) := by
    apply intervalIntegral.integral_congr
    intro a ha
    simp only []
    rw [show (0:ℝ) + 1*a = a from by ring]
    ring
  have hsub : (∫ a in A1..A2, ((1/a)*(1/(c+e*a)) - (1/a)*(1/a)))
      = (∫ a in A1..A2, (1/a)*(1/(c+e*a))) - ∫ a in A1..A2, (1/a)*(1/a) :=
    intervalIntegral.integral_sub hi1 hi2
  have e1 : (∫ a in A1..A2, (1/a)*(1/(c+e*a)))
      = (1/c)*(Real.log (A2/A1) - Real.log ((c+e*A2)/(c+e*A1))) := by
    rw [← integral_inv_mul_inv (c := c) (e := e) hc hA1 hAA hpos1]
    apply intervalIntegral.integral_congr
    intro a ha
    have h1 : A1 ≤ a ∧ a ≤ A2 := hle a ha
    have ha0 : a ≠ 0 := by linarith [h1.1]
    have h2 : c + e*a ≠ 0 := ne_of_gt (hpos1 a h1.1 h1.2)
    field_simp
  have e2 : (∫ a in A1..A2, (1/a)*(1/a)) = 1/A1 - 1/A2 := by
    rw [← integral_inv_sq_alone hA1 hAA]
    apply intervalIntegral.integral_congr
    intro a ha
    ring
  rw [hcongr, hsub, e1, e2]

/-- One `a`-slice of a trapezoid piece, case `1/f ≤ 1/c`: both logarithms enter with a positive
coefficient, so only lower bounds of the two composite logarithms are needed. -/
private lemma slice_le_A {A1 A2 c e f g lb1 lb2 : ℝ} (hc : 0 < c) (hf : 0 < f)
    (hA1 : (1/10:ℝ) ≤ A1) (hAA : A1 ≤ A2)
    (hpos1 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < c + e*a)
    (hpos2 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < f + g*a)
    (hle : 1/f ≤ 1/c)
    (h1 : lb1 ≤ Real.log ((A2/A1)/((c+e*A2)/(c+e*A1))))
    (h2 : lb2 ≤ Real.log (((f+g*A2)/(f+g*A1))/((c+e*A2)/(c+e*A1))))
    : (1/c - 1/f)*lb1 + (1/f)*lb2
      ≤ ∫ a in A1..A2, (1/a)*(1/(c+e*a) - 1/(f+g*a)) := by
  have hA10 : (0:ℝ) < A1 := by linarith
  have hA20 : (0:ℝ) < A2 := by linarith
  have hq0 : (0:ℝ) < A2/A1 := div_pos hA20 hA10
  have hr10 : (0:ℝ) < (c+e*A2)/(c+e*A1) :=
    div_pos (hpos1 A2 hAA le_rfl) (hpos1 A1 le_rfl hAA)
  have hr20 : (0:ℝ) < (f+g*A2)/(f+g*A1) :=
    div_pos (hpos2 A2 hAA le_rfl) (hpos2 A1 le_rfl hAA)
  rw [outer_split (A1 := A1) (A2 := A2) (c := c) (e := e) (f := f) (g := g)
    (ne_of_gt hc) (ne_of_gt hf) hA10 hAA hpos1 hpos2]
  have hp1 : Real.log (A2/A1) - Real.log ((c+e*A2)/(c+e*A1))
      = Real.log ((A2/A1)/((c+e*A2)/(c+e*A1))) := by
    rw [← Real.log_div (ne_of_gt hq0) (ne_of_gt hr10)]
  have hp2 : Real.log ((f+g*A2)/(f+g*A1)) - Real.log ((c+e*A2)/(c+e*A1))
      = Real.log (((f+g*A2)/(f+g*A1))/((c+e*A2)/(c+e*A1))) := by
    rw [← Real.log_div (ne_of_gt hr20) (ne_of_gt hr10)]
  have key : (1/c)*(Real.log (A2/A1) - Real.log ((c+e*A2)/(c+e*A1)))
      - (1/f)*(Real.log (A2/A1) - Real.log ((f+g*A2)/(f+g*A1)))
      = (1/c - 1/f)*(Real.log (A2/A1) - Real.log ((c+e*A2)/(c+e*A1)))
        + (1/f)*(Real.log ((f+g*A2)/(f+g*A1)) - Real.log ((c+e*A2)/(c+e*A1))) := by
    field_simp
    ring
  rw [key, hp1, hp2]
  have hcoef : (0:ℝ) ≤ 1/c - 1/f := sub_nonneg.mpr hle
  have h3 : (1/c - 1/f)*lb1 ≤ (1/c - 1/f)*Real.log ((A2/A1)/((c+e*A2)/(c+e*A1))) :=
    mul_le_mul_of_nonneg_left h1 hcoef
  have h4 : (1/f)*lb2 ≤ (1/f)*Real.log (((f+g*A2)/(f+g*A1))/((c+e*A2)/(c+e*A1))) :=
    mul_le_mul_of_nonneg_left h2 (le_of_lt (one_div_pos.mpr hf))
  linarith

/-- One `a`-slice of a trapezoid piece, case `1/c ≤ 1/f`. -/
private lemma slice_le_B {A1 A2 c e f g lb1 lb2 : ℝ} (hc : 0 < c) (hf : 0 < f)
    (hA1 : (1/10:ℝ) ≤ A1) (hAA : A1 ≤ A2)
    (hpos1 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < c + e*a)
    (hpos2 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < f + g*a)
    (hle : 1/c ≤ 1/f)
    (h1 : lb1 ≤ Real.log (((f+g*A2)/(f+g*A1))/((c+e*A2)/(c+e*A1))))
    (h2 : lb2 ≤ Real.log (((f+g*A2)/(f+g*A1))/(A2/A1)))
    : (1/c)*lb1 + (1/f - 1/c)*lb2
      ≤ ∫ a in A1..A2, (1/a)*(1/(c+e*a) - 1/(f+g*a)) := by
  have hA10 : (0:ℝ) < A1 := by linarith
  have hA20 : (0:ℝ) < A2 := by linarith
  have hq0 : (0:ℝ) < A2/A1 := div_pos hA20 hA10
  have hr10 : (0:ℝ) < (c+e*A2)/(c+e*A1) :=
    div_pos (hpos1 A2 hAA le_rfl) (hpos1 A1 le_rfl hAA)
  have hr20 : (0:ℝ) < (f+g*A2)/(f+g*A1) :=
    div_pos (hpos2 A2 hAA le_rfl) (hpos2 A1 le_rfl hAA)
  rw [outer_split (A1 := A1) (A2 := A2) (c := c) (e := e) (f := f) (g := g)
    (ne_of_gt hc) (ne_of_gt hf) hA10 hAA hpos1 hpos2]
  have hp1 : Real.log ((f+g*A2)/(f+g*A1)) - Real.log ((c+e*A2)/(c+e*A1))
      = Real.log (((f+g*A2)/(f+g*A1))/((c+e*A2)/(c+e*A1))) := by
    rw [← Real.log_div (ne_of_gt hr20) (ne_of_gt hr10)]
  have hp2 : Real.log ((f+g*A2)/(f+g*A1)) - Real.log (A2/A1)
      = Real.log (((f+g*A2)/(f+g*A1))/(A2/A1)) := by
    rw [← Real.log_div (ne_of_gt hr20) (ne_of_gt hq0)]
  have key : (1/c)*(Real.log (A2/A1) - Real.log ((c+e*A2)/(c+e*A1)))
      - (1/f)*(Real.log (A2/A1) - Real.log ((f+g*A2)/(f+g*A1)))
      = (1/c)*(Real.log ((f+g*A2)/(f+g*A1)) - Real.log ((c+e*A2)/(c+e*A1)))
        + (1/f - 1/c)*(Real.log ((f+g*A2)/(f+g*A1)) - Real.log (A2/A1)) := by
    field_simp
    ring
  rw [key, hp1, hp2]
  have hcoef : (0:ℝ) ≤ 1/f - 1/c := sub_nonneg.mpr hle
  have h3 : (1/c)*lb1 ≤ (1/c)*Real.log (((f+g*A2)/(f+g*A1))/((c+e*A2)/(c+e*A1))) :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt (one_div_pos.mpr hc))
  have h4 : (1/f - 1/c)*lb2 ≤ (1/f - 1/c)*Real.log (((f+g*A2)/(f+g*A1))/(A2/A1)) :=
    mul_le_mul_of_nonneg_left h2 hcoef
  linarith

/-- One `a`-slice of a piece with `δ(a) = a`: the second half is exactly `1/A1 - 1/A2`. -/
private lemma slice_le_Z {A1 A2 c e lb1 : ℝ} (hc : 0 < c)
    (hA1 : (1/10:ℝ) ≤ A1) (hAA : A1 ≤ A2)
    (hpos1 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < c + e*a)
    (h1 : lb1 ≤ Real.log ((A2/A1)/((c+e*A2)/(c+e*A1))))
    : (1/c)*lb1 - (1/A1 - 1/A2)
      ≤ ∫ a in A1..A2, (1/a)*(1/(c+e*a) - 1/(0 + 1*a)) := by
  have hA10 : (0:ℝ) < A1 := by linarith
  have hA20 : (0:ℝ) < A2 := by linarith
  have hq0 : (0:ℝ) < A2/A1 := div_pos hA20 hA10
  have hr10 : (0:ℝ) < (c+e*A2)/(c+e*A1) :=
    div_pos (hpos1 A2 hAA le_rfl) (hpos1 A1 le_rfl hAA)
  rw [outer_split_zero (A1 := A1) (A2 := A2) (c := c) (e := e) (ne_of_gt hc) hA10 hAA hpos1]
  have hp1 : Real.log (A2/A1) - Real.log ((c+e*A2)/(c+e*A1))
      = Real.log ((A2/A1)/((c+e*A2)/(c+e*A1))) := by
    rw [← Real.log_div (ne_of_gt hq0) (ne_of_gt hr10)]
  rw [hp1]
  have h3 : (1/c)*lb1 ≤ (1/c)*Real.log ((A2/A1)/((c+e*A2)/(c+e*A1))) :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt (one_div_pos.mpr hc))
  linarith

/-- Piece `Q1a1` of the quadrature, in three `a`-slices. -/

private lemma piece_G_eval {A1 A2 c e f g : ℝ} (hA1 : (1/10:ℝ) ≤ A1) (hA2 : A2 ≤ 1/2)
    (hAA : A1 ≤ A2)
    (hpos1 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < c + e*a)
    (hpos2 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < f + g*a)
    (hord : ∀ a, A1 ≤ a → a ≤ A2 → c + e*a ≤ f + g*a)
    (hlow : ∀ a, A1 ≤ a → a ≤ A2 → (1/10:ℝ) ≤ c + e*a)
    (hhigh : ∀ a, A1 ≤ a → a ≤ A2 → f + g*a ≤ 1/2) :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
        (if (A1 ≤ a ∧ a ≤ A2 ∧ c + e*a ≤ b ∧ b ≤ f + g*a) then (1:ℝ)/(a*b^2) else 0))
      = ∫ a in A1..A2, (1/a)*(1/(c+e*a) - 1/(f+g*a)) := by
  have hinner : ∀ a ∈ Set.Icc (1/10:ℝ) (1/2),
      (∫ b in (1/10:ℝ)..(1/2:ℝ),
        (if (A1 ≤ a ∧ a ≤ A2 ∧ c + e*a ≤ b ∧ b ≤ f + g*a) then (1:ℝ)/(a*b^2) else 0))
        = (if A1 ≤ a ∧ a ≤ A2 then (1/a)*(1/(c+e*a) - 1/(f+g*a)) else 0) := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := ha
    by_cases hin : A1 ≤ a ∧ a ≤ A2
    · rw [if_pos hin]
      obtain ⟨hin1, hin2⟩ := hin
      have hga : 0 < c + e*a := hpos1 a hin1 hin2
      have hord' : c + e*a ≤ f + g*a := hord a hin1 hin2
      have hga1 : (1/10:ℝ) ≤ c + e*a := hlow a hin1 hin2
      have hfa1 : f + g*a ≤ 1/2 := hhigh a hin1 hin2
      have htrim : (∫ b in (1/10:ℝ)..(1/2:ℝ),
          (if (A1 ≤ a ∧ a ≤ A2 ∧ c + e*a ≤ b ∧ b ≤ f + g*a) then (1:ℝ)/(a*b^2) else 0))
          = ∫ b in (c + e*a)..(f + g*a),
          (if (A1 ≤ a ∧ a ≤ A2 ∧ c + e*a ≤ b ∧ b ≤ f + g*a) then (1:ℝ)/(a*b^2) else 0) := by
        apply interval_trim (c := 1/10) (d := 1/2) (l := c + e*a) (h := f + g*a) hga1 hord' hfa1
        intro x hx1 hx2 hx3 hxne
        have hfail : ¬ (A1 ≤ a ∧ a ≤ A2 ∧ c + e*a ≤ x ∧ x ≤ f + g*a) := by
          rintro ⟨-, -, h1, h2⟩
          exact hx3 ⟨lt_of_le_of_ne h1 (Ne.symm hxne), h2⟩
        rw [if_neg hfail]
      rw [htrim]
      have hcongr : (∫ b in (c + e*a)..(f + g*a),
          (if (A1 ≤ a ∧ a ≤ A2 ∧ c + e*a ≤ b ∧ b ≤ f + g*a) then (1:ℝ)/(a*b^2) else 0))
          = ∫ b in (c + e*a)..(f + g*a), (1:ℝ)/(a*b^2) := by
        apply intervalIntegral.integral_congr
        intro b hb
        have hb' := hb
        rw [Set.uIcc_of_le hord'] at hb'
        simp only []
        rw [if_pos (show A1 ≤ a ∧ a ≤ A2 ∧ c + e*a ≤ b ∧ b ≤ f + g*a from
          ⟨hin1, hin2, hb'.1, hb'.2⟩)]
      rw [hcongr, integral_inv_sq_box a (c + e*a) (f + g*a) (by linarith) hga hord']
    · rw [if_neg hin]
      have hz : ∀ b, (if (A1 ≤ a ∧ a ≤ A2 ∧ c + e*a ≤ b ∧ b ≤ f + g*a)
          then (1:ℝ)/(a*b^2) else 0) = 0 := by
        intro b
        have hfail : ¬ (A1 ≤ a ∧ a ≤ A2 ∧ c + e*a ≤ b ∧ b ≤ f + g*a) := by
          rintro ⟨h1, h2, -⟩
          exact hin ⟨h1, h2⟩
        rw [if_neg hfail]
      simp only [hz]
      simp
  have h1 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
        (if (A1 ≤ a ∧ a ≤ A2 ∧ c + e*a ≤ b ∧ b ≤ f + g*a) then (1:ℝ)/(a*b^2) else 0))
      = ∫ a in (1/10:ℝ)..(1/2:ℝ),
          (if A1 ≤ a ∧ a ≤ A2 then (1/a)*(1/(c+e*a) - 1/(f+g*a)) else 0) := by
    apply intervalIntegral.integral_congr
    intro a ha
    have ha' := ha
    rw [Set.uIcc_of_le (by norm_num : (1/10:ℝ) ≤ 1/2)] at ha'
    exact hinner a ha'
  rw [h1]
  have htrim : (∫ a in (1/10:ℝ)..(1/2:ℝ),
        (if A1 ≤ a ∧ a ≤ A2 then (1/a)*(1/(c+e*a) - 1/(f+g*a)) else 0))
      = ∫ a in A1..A2, (if A1 ≤ a ∧ a ≤ A2 then (1/a)*(1/(c+e*a) - 1/(f+g*a)) else 0) := by
    apply interval_trim hA1 hAA hA2
    intro x hx1 hx2 hx3 hxne
    have hfail : ¬ (A1 ≤ x ∧ x ≤ A2) := by
      rintro ⟨h1, h2⟩
      exact hx3 ⟨lt_of_le_of_ne h1 (Ne.symm hxne), h2⟩
    rw [if_neg hfail]
  rw [htrim]
  apply intervalIntegral.integral_congr
  intro a ha
  have ha' := ha
  rw [Set.uIcc_of_le hAA] at ha'
  simp only []
  exact if_pos ha'

/-- `piece_G_eval` with strict lower bounds in both variables. The strictness makes the fourteen
pieces pairwise disjoint; the integral is unchanged, because the difference sits on the two lines
`a = A1` and `b = c + e a`. -/
private lemma piece_G_eval_strict {A1 A2 c e f g : ℝ} (hA1 : (1/10:ℝ) ≤ A1) (hA2 : A2 ≤ 1/2)
    (hAA : A1 ≤ A2)
    (hpos1 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < c + e*a)
    (hpos2 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < f + g*a)
    (hord : ∀ a, A1 ≤ a → a ≤ A2 → c + e*a ≤ f + g*a)
    (hlow : ∀ a, A1 ≤ a → a ≤ A2 → (1/10:ℝ) ≤ c + e*a)
    (hhigh : ∀ a, A1 ≤ a → a ≤ A2 → f + g*a ≤ 1/2) :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
        (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a) then (1:ℝ)/(a*b^2) else 0))
      = ∫ a in A1..A2, (1/a)*(1/(c+e*a) - 1/(f+g*a)) := by
  have hinner : ∀ a ∈ Set.Icc (1/10:ℝ) (1/2),
      (∫ b in (1/10:ℝ)..(1/2:ℝ),
        (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a) then (1:ℝ)/(a*b^2) else 0))
        = (if A1 < a ∧ a ≤ A2 then (1/a)*(1/(c+e*a) - 1/(f+g*a)) else 0) := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := ha
    by_cases hin : A1 < a ∧ a ≤ A2
    · rw [if_pos hin]
      obtain ⟨hin1, hin2⟩ := hin
      have hga : 0 < c + e*a := hpos1 a hin1.le hin2
      have hord' : c + e*a ≤ f + g*a := hord a hin1.le hin2
      have hga1 : (1/10:ℝ) ≤ c + e*a := hlow a hin1.le hin2
      have hfa1 : f + g*a ≤ 1/2 := hhigh a hin1.le hin2
      have htrim : (∫ b in (1/10:ℝ)..(1/2:ℝ),
          (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a) then (1:ℝ)/(a*b^2) else 0))
          = ∫ b in (c + e*a)..(f + g*a),
          (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a) then (1:ℝ)/(a*b^2) else 0) := by
        apply interval_trim (c := 1/10) (d := 1/2) (l := c + e*a) (h := f + g*a) hga1 hord' hfa1
        intro x hx1 hx2 hx3 hxne
        have hfail : ¬ (A1 < a ∧ a ≤ A2 ∧ c + e*a < x ∧ x ≤ f + g*a) := by
          rintro ⟨-, -, h1, h2⟩
          exact absurd h1 (not_lt.mpr (le_of_not_gt (fun hc => hx3 ⟨hc, h2⟩)))
        rw [if_neg hfail]
      rw [htrim]
      have hcongr : (∫ b in (c + e*a)..(f + g*a),
          (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a) then (1:ℝ)/(a*b^2) else 0))
          = ∫ b in (c + e*a)..(f + g*a), (1:ℝ)/(a*b^2) := by
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ b ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), b ≠ c + e*a := by
          simpa using (Set.countable_singleton (c + e*a)).ae_notMem
            (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        filter_upwards [hne] with b hbne hb
        have hb' := hb
        rw [Set.uIoc_of_le hord'] at hb'
        rw [if_pos (show A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a from
          ⟨hin1, hin2, hb'.1, hb'.2⟩)]
      rw [hcongr, integral_inv_sq_box a (c + e*a) (f + g*a) (by linarith) hga hord']
    · rw [if_neg hin]
      have hz : ∀ b, (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a)
          then (1:ℝ)/(a*b^2) else 0) = 0 := by
        intro b
        have hfail : ¬ (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a) := by
          rintro ⟨h1, h2, -⟩
          exact hin ⟨h1, h2⟩
        rw [if_neg hfail]
      simp only [hz]
      simp
  have h1 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
        (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a) then (1:ℝ)/(a*b^2) else 0))
      = ∫ a in (1/10:ℝ)..(1/2:ℝ),
          (if A1 < a ∧ a ≤ A2 then (1/a)*(1/(c+e*a) - 1/(f+g*a)) else 0) := by
    apply intervalIntegral.integral_congr
    intro a ha
    have ha' := ha
    rw [Set.uIcc_of_le (by norm_num : (1/10:ℝ) ≤ 1/2)] at ha'
    exact hinner a ha'
  rw [h1]
  have htrim2 : (∫ a in (1/10:ℝ)..(1/2:ℝ),
        (if A1 < a ∧ a ≤ A2 then (1/a)*(1/(c+e*a) - 1/(f+g*a)) else 0))
      = ∫ a in A1..A2, (if A1 < a ∧ a ≤ A2 then (1/a)*(1/(c+e*a) - 1/(f+g*a)) else 0) := by
    apply interval_trim hA1 hAA hA2
    intro x hx1 hx2 hx3 hxne
    have hfail : ¬ (A1 < x ∧ x ≤ A2) := by
      rintro ⟨h1, h2⟩
      exact hx3 ⟨h1, h2⟩
    rw [if_neg hfail]
  rw [htrim2]
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ a ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), a ≠ A1 := by
    simpa using (Set.countable_singleton A1).ae_notMem (MeasureTheory.volume : MeasureTheory.Measure ℝ)
  filter_upwards [hne] with a hane ha
  have ha' := ha
  rw [Set.uIoc_of_le hAA] at ha'
  change (if A1 < a ∧ a ≤ A2 then (1/a)*(1/(c+e*a) - 1/(f+g*a)) else 0)
    = (1/a)*(1/(c+e*a) - 1/(f+g*a))
  rw [if_pos (show A1 < a ∧ a ≤ A2 from ⟨ha'.1, ha'.2⟩)]

/-- Piece `1a1` excludes every other piece (pairwise disjointness of the thirteen regions). -/

private lemma trap_measurable {A1 A2 c e f g : ℝ} :
    Measurable (fun p : ℝ × ℝ =>
      if (A1 < p.1 ∧ p.1 ≤ A2 ∧ c + e*p.1 < p.2 ∧ p.2 ≤ f + g*p.1)
        then (1:ℝ)/(p.1*p.2^2) else 0) := by
  have hset : MeasurableSet {p : ℝ × ℝ |
      A1 < p.1 ∧ p.1 ≤ A2 ∧ c + e*p.1 < p.2 ∧ p.2 ≤ f + g*p.1} := by
    have hlt : ∀ F₁ F₂ : ℝ × ℝ → ℝ, Continuous F₁ → Continuous F₂ →
        MeasurableSet {p | F₁ p < F₂ p} := fun F₁ F₂ h1 h2 => (isOpen_lt h1 h2).measurableSet
    have hle : ∀ F₁ F₂ : ℝ × ℝ → ℝ, Continuous F₁ → Continuous F₂ →
        MeasurableSet {p | F₁ p ≤ F₂ p} := fun F₁ F₂ h1 h2 => (isClosed_le h1 h2).measurableSet
    simp only [Set.ofPred_and]
    repeat' first
      | apply MeasurableSet.inter
      | (apply hlt <;> fun_prop)
      | (apply hle <;> fun_prop)
  exact Measurable.ite hset (by fun_prop) measurable_const

/-- The trapezoid indicator integrand is bounded by `1000` on the box `a ≥ 1/10`, `b > 1/10`. -/
private lemma trap_bound {A1 A2 c e f g a b : ℝ} (ha : (1/10:ℝ) ≤ a) (hb : (1/10:ℝ) < b) :
    |(if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a) then (1:ℝ)/(a*b^2) else 0)| ≤ 1000 := by
  by_cases h : (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a)
  · rw [if_pos h]
    have ha0 : 0 < a := by linarith
    have hb0 : 0 < b := by linarith
    have hb2 : (1/100:ℝ) < b^2 := by nlinarith
    have hb2' : (0:ℝ) < b^2 := by linarith
    have h1 : (1/10:ℝ)*b^2 ≤ a*b^2 := mul_le_mul_of_nonneg_right ha (le_of_lt hb2')
    have h2 : (1/10:ℝ)*(1/100:ℝ) < (1/10:ℝ)*b^2 :=
      mul_lt_mul_of_pos_left hb2 (by norm_num)
    have hpos : 0 < a*b^2 := by linarith
    have hnn : 0 ≤ (1:ℝ)/(a*b^2) := by positivity
    rw [abs_of_nonneg hnn, div_le_iff₀ hpos]
    linarith
  · rw [if_neg h]
    norm_num

/-- A measurable function uniformly bounded on the whole line is interval integrable on a bounded
interval. -/
private lemma intervalIntegrable_of_bound {φ : ℝ → ℝ} {M : ℝ}
    (hm : Measurable φ) (hb : ∀ b, |φ b| ≤ M) (lo hi : ℝ) :
    IntervalIntegrable φ MeasureTheory.volume lo hi := by
  refine ⟨MeasureTheory.Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
      hm.aestronglyMeasurable ?_,
    MeasureTheory.Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
      hm.aestronglyMeasurable ?_⟩ <;>
    exact Filter.Eventually.of_forall fun y => by
      simpa only [Real.norm_eq_abs] using hb y

/-- Everything one trapezoid piece of the three band region needs: the function is measurable, is
bounded by `1000`, is nonnegative, its slice is interval integrable in `b` at every `a`, its `b`
integral is measurable and bounded, that integral is interval integrable in `a`, and the double
integral is the elementary one of `piece_G_eval_strict`. -/
private lemma piece_G_all {A1 A2 c e f g : ℝ} (hA1 : (1/10:ℝ) ≤ A1) (hA2 : A2 ≤ 1/2)
    (hAA : A1 ≤ A2)
    (hpos1 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < c + e*a)
    (hpos2 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < f + g*a)
    (hord : ∀ a, A1 ≤ a → a ≤ A2 → c + e*a ≤ f + g*a)
    (hlow : ∀ a, A1 ≤ a → a ≤ A2 → (1/10:ℝ) ≤ c + e*a)
    (hhigh : ∀ a, A1 ≤ a → a ≤ A2 → f + g*a ≤ 1/2) :
    Measurable (fun p : ℝ × ℝ =>
        (if (A1 < p.1 ∧ p.1 ≤ A2 ∧ c + e*p.1 < p.2 ∧ p.2 ≤ f + g*p.1)
          then (1:ℝ)/(p.1*p.2^2) else 0))
    ∧ (∀ a b : ℝ,
        |(if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a)
          then (1:ℝ)/(a*b^2) else 0)| ≤ 1000)
    ∧ (∀ a b : ℝ,
        0 ≤ (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a)
          then (1:ℝ)/(a*b^2) else 0))
    ∧ (∀ a : ℝ, IntervalIntegrable (fun b : ℝ =>
        (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a)
          then (1:ℝ)/(a*b^2) else 0)) MeasureTheory.volume (1/10) (1/2))
    ∧ Measurable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ),
        (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a)
          then (1:ℝ)/(a*b^2) else 0))
    ∧ (∀ a : ℝ, |∫ b in (1/10:ℝ)..(1/2:ℝ),
        (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a)
          then (1:ℝ)/(a*b^2) else 0)| ≤ 1000)
    ∧ IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ),
        (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a)
          then (1:ℝ)/(a*b^2) else 0)) MeasureTheory.volume (1/10) (1/2)
    ∧ ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
        (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a)
          then (1:ℝ)/(a*b^2) else 0))
      = ∫ a in A1..A2, (1/a)*(1/(c+e*a) - 1/(f+g*a))) := by
  have hset : MeasurableSet {p : ℝ × ℝ |
      A1 < p.1 ∧ p.1 ≤ A2 ∧ c + e*p.1 < p.2 ∧ p.2 ≤ f + g*p.1} := by
    have hlt : ∀ F₁ F₂ : ℝ × ℝ → ℝ, Continuous F₁ → Continuous F₂ →
        MeasurableSet {p | F₁ p < F₂ p} := fun F₁ F₂ h1 h2 => (isOpen_lt h1 h2).measurableSet
    have hle : ∀ F₁ F₂ : ℝ × ℝ → ℝ, Continuous F₁ → Continuous F₂ →
        MeasurableSet {p | F₁ p ≤ F₂ p} := fun F₁ F₂ h1 h2 => (isClosed_le h1 h2).measurableSet
    simp only [Set.ofPred_and]
    repeat' first
      | apply MeasurableSet.inter
      | (apply hlt <;> fun_prop)
      | (apply hle <;> fun_prop)
  have hm : Measurable (fun p : ℝ × ℝ =>
      (if (A1 < p.1 ∧ p.1 ≤ A2 ∧ c + e*p.1 < p.2 ∧ p.2 ≤ f + g*p.1)
        then (1:ℝ)/(p.1*p.2^2) else 0)) :=
    Measurable.ite hset (by fun_prop) measurable_const
  have hbnd : ∀ a b : ℝ,
      |(if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a)
        then (1:ℝ)/(a*b^2) else 0)| ≤ 1000 := by
    intro a b
    by_cases h : (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a)
    · have ha : (1/10:ℝ) ≤ a := by linarith [h.1]
      have hb : (1/10:ℝ) < b := by linarith [hlow a h.1.le h.2.1, h.2.2.1]
      exact trap_bound (A1 := A1) (A2 := A2) (c := c) (e := e) (f := f) (g := g) ha hb
    · rw [if_neg h]; norm_num
  have hnn : ∀ a b : ℝ,
      0 ≤ (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a)
        then (1:ℝ)/(a*b^2) else 0) := by
    intro a b
    by_cases h : (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a)
    · rw [if_pos h]
      have ha : (0:ℝ) < a := by linarith [h.1]
      have hb : (0:ℝ) < b := by linarith [hlow a h.1.le h.2.1, h.2.2.1]
      exact le_of_lt (one_div_pos.mpr (mul_pos ha (pow_pos hb 2)))
    · rw [if_neg h]
  have hi : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ =>
      (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a)
        then (1:ℝ)/(a*b^2) else 0)) MeasureTheory.volume (1/10) (1/2) := by
    intro a
    have hmc : Measurable (fun b : ℝ =>
        (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a)
          then (1:ℝ)/(a*b^2) else 0)) :=
      hm.comp (measurable_const.prodMk measurable_id)
    exact intervalIntegrable_of_bound (M := 1000) hmc (fun b => hbnd a b) _ _
  have hlev := four_density_level (fun a b : ℝ =>
      (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a)
        then (1:ℝ)/(a*b^2) else 0)) hm hbnd (1/10) (1/2)
  have hbI : ∀ a : ℝ, |∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a)
        then (1:ℝ)/(a*b^2) else 0)| ≤ 1000 := by
    intro a
    have h := hlev.2 a
    rw [show (1000:ℝ) * |(1/2:ℝ) - (1/10:ℝ)| = 400 by norm_num] at h
    linarith
  have ho : IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if (A1 < a ∧ a ≤ A2 ∧ c + e*a < b ∧ b ≤ f + g*a)
        then (1:ℝ)/(a*b^2) else 0)) MeasureTheory.volume (1/10) (1/2) :=
    intervalIntegrable_of_bound hlev.1 hbI _ _
  exact ⟨hm, hbnd, hnn, hi, hlev.1, hbI, ho,
    piece_G_eval_strict hA1 hA2 hAA hpos1 hpos2 hord hlow hhigh⟩

private lemma log_series_lb {y : ℝ} (hy : 1 ≤ y) :
    2*((y-1)/(y+1) + ((y-1)/(y+1))^3/3 + ((y-1)/(y+1))^5/5) ≤ Real.log y := by
  set t := (y-1)/(y+1) with ht
  have hy1 : (0:ℝ) < y + 1 := by linarith
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (by linarith) (by linarith)
  have ht1 : t < 1 := by rw [ht, div_lt_one hy1]; linarith
  have h1 : (1:ℝ) - (y-1)/(y+1) ≠ 0 := by
    have h' : (y-1)/(y+1) < 1 := by rw [← ht]; exact ht1
    linarith
  have h2 : y + 1 ≠ 0 := by linarith
  have hye : y = (1+t)/(1-t) := by
    rw [ht]
    field_simp
    ring
  have h := Real.sum_range_le_log_div ht0 ht1 3
  rw [hye]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero] at h
  linarith

private lemma log_series_ub {y : ℝ} (hy : 1 ≤ y) :
    Real.log y ≤ 2*((y-1)/(y+1) + ((y-1)/(y+1))^3/3 + ((y-1)/(y+1))^5/5 +
      ((y-1)/(y+1))^7/(1 - ((y-1)/(y+1))^2)) := by
  set t := (y-1)/(y+1) with ht
  have hy1 : (0:ℝ) < y + 1 := by linarith
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (by linarith) (by linarith)
  have ht1 : t < 1 := by rw [ht, div_lt_one hy1]; linarith
  have h1 : (1:ℝ) - (y-1)/(y+1) ≠ 0 := by
    have h' : (y-1)/(y+1) < 1 := by rw [← ht]; exact ht1
    linarith
  have h2 : y + 1 ≠ 0 := by linarith
  have hye : y = (1+t)/(1-t) := by
    rw [ht]
    field_simp
    ring
  have h := Real.log_div_le_sum_range_add ht0 ht1 3
  rw [hye]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero] at h
  linarith

/-- The `a`-integral of one trapezoid piece, bounded below through the two logarithm series
bounds: with `X = (A2/A1)/((c+e*A2)/(c+e*A1)) ≥ 1` and `Y = (A2/A1)/((f+g*A2)/(f+g*A1)) ≥ 1` the
integral equals `(1/c) log X - (1/f) log Y`. -/
private lemma trap_lower {A1 A2 c e f g lbX ubY : ℝ} (hc : 0 < c) (hf : 0 < f)
    (hA1 : (1/10:ℝ) ≤ A1) (hAA : A1 ≤ A2)
    (hpos1 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < c + e*a)
    (hpos2 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < f + g*a)
    (hXb : lbX ≤ Real.log ((A2/A1)/((c+e*A2)/(c+e*A1))))
    (hYb : Real.log ((A2/A1)/((f+g*A2)/(f+g*A1))) ≤ ubY) :
    (1/c)*lbX - (1/f)*ubY ≤ ∫ a in A1..A2, (1/a)*(1/(c+e*a) - 1/(f+g*a)) := by
  have hA10 : (0:ℝ) < A1 := by linarith
  have hA20 : (0:ℝ) < A2 := by linarith
  have hq0 : (0:ℝ) < A2/A1 := div_pos hA20 hA10
  have hr10 : (0:ℝ) < (c+e*A2)/(c+e*A1) :=
    div_pos (hpos1 A2 hAA le_rfl) (hpos1 A1 le_rfl hAA)
  have hr20 : (0:ℝ) < (f+g*A2)/(f+g*A1) :=
    div_pos (hpos2 A2 hAA le_rfl) (hpos2 A1 le_rfl hAA)
  rw [outer_split (A1 := A1) (A2 := A2) (c := c) (e := e) (f := f) (g := g)
    (ne_of_gt hc) (ne_of_gt hf) hA10 hAA hpos1 hpos2]
  have hp1 : Real.log (A2/A1) - Real.log ((c+e*A2)/(c+e*A1))
      = Real.log ((A2/A1)/((c+e*A2)/(c+e*A1))) := by
    rw [← Real.log_div (ne_of_gt hq0) (ne_of_gt hr10)]
  have hp2 : Real.log (A2/A1) - Real.log ((f+g*A2)/(f+g*A1))
      = Real.log ((A2/A1)/((f+g*A2)/(f+g*A1))) := by
    rw [← Real.log_div (ne_of_gt hq0) (ne_of_gt hr20)]
  rw [hp1, hp2]
  have h3 := mul_le_mul_of_nonneg_left hXb (le_of_lt (one_div_pos.mpr hc))
  have h4 := mul_le_mul_of_nonneg_left hYb (le_of_lt (one_div_pos.mpr hf))
  linarith

/-- The same for a piece whose upper `b`-bound is `a` itself: the second half is exact. -/
private lemma trap_lower_Z {A1 A2 c e lbX : ℝ} (hc : 0 < c)
    (hA1 : (1/10:ℝ) ≤ A1) (hAA : A1 ≤ A2)
    (hpos1 : ∀ a, A1 ≤ a → a ≤ A2 → 0 < c + e*a)
    (hXb : lbX ≤ Real.log ((A2/A1)/((c+e*A2)/(c+e*A1)))) :
    (1/c)*lbX - (1/A1 - 1/A2) ≤ ∫ a in A1..A2, (1/a)*(1/(c+e*a) - 1/(0 + 1*a)) := by
  have hA10 : (0:ℝ) < A1 := by linarith
  have hA20 : (0:ℝ) < A2 := by linarith
  have hq0 : (0:ℝ) < A2/A1 := div_pos hA20 hA10
  have hr10 : (0:ℝ) < (c+e*A2)/(c+e*A1) :=
    div_pos (hpos1 A2 hAA le_rfl) (hpos1 A1 le_rfl hAA)
  rw [outer_split_zero (A1 := A1) (A2 := A2) (c := c) (e := e) (ne_of_gt hc) hA10 hAA hpos1]
  have hp1 : Real.log (A2/A1) - Real.log ((c+e*A2)/(c+e*A1))
      = Real.log ((A2/A1)/((c+e*A2)/(c+e*A1))) := by
    rw [← Real.log_div (ne_of_gt hq0) (ne_of_gt hr10)]
  rw [hp1]
  have h3 := mul_le_mul_of_nonneg_left hXb (le_of_lt (one_div_pos.mpr hc))
  linarith

-- piece `Q1a2b`: `a ∈ [2273/10000, 43/176]`, `b ∈ [17/56+(-4/7)a, 17/88+(0)a]`
private lemma Q1a2b_lower :
    (((673691)/(12500000)):ℝ) ≤ ∫ a in (((2273)/(10000)):ℝ)..(((43)/(176)):ℝ), (1/a)*(1/(((((17)/(56))):ℝ) + (((-4)/(7)))*a) - 1/(((((17)/(88))):ℝ) + ((0))*a)) := by
  have hXe : (((((43)/(176)))/(((2273)/(10000))))/(((((17)/(56))) + (((-4)/(7)))*(((43)/(176))))/((((17)/(56))) + (((-4)/(7)))*(((2273)/(10000)))))) = (((261397)/(229573)):ℝ) := by norm_num
  have hX1 : (1:ℝ) ≤ (((261397)/(229573)):ℝ) := by norm_num
  have hXb0 : (((578673960086563706977067664)/(4457535453349796737269640625)):ℝ) ≤ Real.log (((261397)/(229573)):ℝ) := by
    have hh := log_series_lb hX1
    norm_num at hh
    linarith
  have hXb : (((578673960086563706977067664)/(4457535453349796737269640625)):ℝ) ≤ Real.log (((((43)/(176)))/(((2273)/(10000))))/(((((17)/(56))) + (((-4)/(7)))*(((43)/(176))))/((((17)/(56))) + (((-4)/(7)))*(((2273)/(10000)))))) := by rw [hXe]; exact hXb0
  have hYe : (((((43)/(176)))/(((2273)/(10000))))/(((((17)/(88))) + ((0))*(((43)/(176))))/((((17)/(88))) + ((0))*(((2273)/(10000)))))) = (((26875)/(25003)):ℝ) := by norm_num
  have hY1 : (1:ℝ) ≤ (((26875)/(25003)):ℝ) := by norm_num
  have hYb0 : Real.log (((26875)/(25003)):ℝ) ≤ (((569702284229116536626468547792)/(7890540250998174220804420106875)):ℝ) := by
    have hh := log_series_ub hY1
    norm_num at hh
    linarith
  have hYb : Real.log (((((43)/(176)))/(((2273)/(10000))))/(((((17)/(88))) + ((0))*(((43)/(176))))/((((17)/(88))) + ((0))*(((2273)/(10000)))))) ≤ (((569702284229116536626468547792)/(7890540250998174220804420106875)):ℝ) := by rw [hYe]; exact hYb0
  have hmain := trap_lower (A1 := (((2273)/(10000)):ℝ)) (A2 := (((43)/(176)):ℝ)) (c := (((17)/(56)):ℝ)) (e := (((-4)/(7)):ℝ)) (f := (((17)/(88)):ℝ)) (g := ((0):ℝ)) (lbX := (((578673960086563706977067664)/(4457535453349796737269640625)):ℝ)) (ubY := (((569702284229116536626468547792)/(7890540250998174220804420106875)):ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith) hXb hYb
  have heq : (1/((((17)/(56))):ℝ))*(((578673960086563706977067664)/(4457535453349796737269640625)):ℝ) - (1/((((17)/(88))):ℝ))*(((569702284229116536626468547792)/(7890540250998174220804420106875)):ℝ) ≥ (((673691)/(12500000)):ℝ) := by norm_num
  linarith

-- piece `Q1b`: `a ∈ [43/176, 5/16]`, `b ∈ [17/56+(-4/7)a, 7/16+(-1)a]`
private lemma Q1b_lower :
    (((906629)/(6250000)):ℝ) ≤ ∫ a in (((43)/(176)):ℝ)..(((5)/(16)):ℝ), (1/a)*(1/(((((17)/(56))):ℝ) + (((-4)/(7)))*a) - 1/(((((7)/(16))):ℝ) + ((-1))*a)) := by
  have hXe : (((((5)/(16)))/(((43)/(176))))/(((((17)/(56))) + (((-4)/(7)))*(((5)/(16))))/((((17)/(56))) + (((-4)/(7)))*(((43)/(176)))))) = (((505)/(301)):ℝ) := by norm_num
  have hX1 : (1:ℝ) ≤ (((505)/(301)):ℝ) := by norm_num
  have hXb0 : (((27500797662924)/(53149016811215)):ℝ) ≤ Real.log (((505)/(301)):ℝ) := by
    have hh := log_series_lb hX1
    norm_num at hh
    linarith
  have hXb : (((27500797662924)/(53149016811215)):ℝ) ≤ Real.log (((((5)/(16)))/(((43)/(176))))/(((((17)/(56))) + (((-4)/(7)))*(((5)/(16))))/((((17)/(56))) + (((-4)/(7)))*(((43)/(176)))))) := by rw [hXe]; exact hXb0
  have hYe : (((((5)/(16)))/(((43)/(176))))/(((((7)/(16))) + ((-1))*(((5)/(16))))/((((7)/(16))) + ((-1))*(((43)/(176)))))) = (((85)/(43)):ℝ) := by norm_num
  have hY1 : (1:ℝ) ≤ (((85)/(43)):ℝ) := by norm_num
  have hYb0 : Real.log (((85)/(43)):ℝ) ≤ (((334684221753)/(490565795840)):ℝ) := by
    have hh := log_series_ub hY1
    norm_num at hh
    linarith
  have hYb : Real.log (((((5)/(16)))/(((43)/(176))))/(((((7)/(16))) + ((-1))*(((5)/(16))))/((((7)/(16))) + ((-1))*(((43)/(176)))))) ≤ (((334684221753)/(490565795840)):ℝ) := by rw [hYe]; exact hYb0
  have hmain := trap_lower (A1 := (((43)/(176)):ℝ)) (A2 := (((5)/(16)):ℝ)) (c := (((17)/(56)):ℝ)) (e := (((-4)/(7)):ℝ)) (f := (((7)/(16)):ℝ)) (g := ((-1):ℝ)) (lbX := (((27500797662924)/(53149016811215)):ℝ)) (ubY := (((334684221753)/(490565795840)):ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith) hXb hYb
  have heq : (1/((((17)/(56))):ℝ))*(((27500797662924)/(53149016811215)):ℝ) - (1/((((7)/(16))):ℝ))*(((334684221753)/(490565795840)):ℝ) ≥ (((906629)/(6250000)):ℝ) := by norm_num
  linarith

-- piece `Q3a`: `a ∈ [1977/8000, 11931/40000]`, `b ∈ [17/40+(-4/5)a, 2273/10000+(0)a]`
private lemma Q3a_lower :
    (((4100779)/(50000000)):ℝ) ≤ ∫ a in (((1977)/(8000)):ℝ)..(((11931)/(40000)):ℝ), (1/a)*(1/(((((17)/(40))):ℝ) + (((-4)/(5)))*a) - 1/(((((2273)/(10000))):ℝ) + ((0))*a)) := by
  have hXe : (((((11931)/(40000)))/(((1977)/(8000))))/(((((17)/(40))) + (((-4)/(5)))*(((11931)/(40000))))/((((17)/(40))) + (((-4)/(5)))*(((1977)/(8000)))))) = (((9039721)/(6141221)):ℝ) := by norm_num
  have hX1 : (1:ℝ) ≤ (((9039721)/(6141221)):ℝ) := by norm_num
  have hXb0 : (((9741093973450663672303640424728500)/(25196697771281949525454811739141351)):ℝ) ≤ Real.log (((9039721)/(6141221)):ℝ) := by
    have hh := log_series_lb hX1
    norm_num at hh
    linarith
  have hXb : (((9741093973450663672303640424728500)/(25196697771281949525454811739141351)):ℝ) ≤ Real.log (((((11931)/(40000)))/(((1977)/(8000))))/(((((17)/(40))) + (((-4)/(5)))*(((11931)/(40000))))/((((17)/(40))) + (((-4)/(5)))*(((1977)/(8000)))))) := by rw [hXe]; exact hXb0
  have hYe : (((((11931)/(40000)))/(((1977)/(8000))))/(((((2273)/(10000))) + ((0))*(((11931)/(40000))))/((((2273)/(10000))) + ((0))*(((1977)/(8000)))))) = (((3977)/(3295)):ℝ) := by norm_num
  have hY1 : (1:ℝ) ≤ (((3977)/(3295)):ℝ) := by norm_num
  have hYb0 : Real.log (((3977)/(3295)):ℝ) ≤ (((195830038987494377739361)/(1040975230179992327556480)):ℝ) := by
    have hh := log_series_ub hY1
    norm_num at hh
    linarith
  have hYb : Real.log (((((11931)/(40000)))/(((1977)/(8000))))/(((((2273)/(10000))) + ((0))*(((11931)/(40000))))/((((2273)/(10000))) + ((0))*(((1977)/(8000)))))) ≤ (((195830038987494377739361)/(1040975230179992327556480)):ℝ) := by rw [hYe]; exact hYb0
  have hmain := trap_lower (A1 := (((1977)/(8000)):ℝ)) (A2 := (((11931)/(40000)):ℝ)) (c := (((17)/(40)):ℝ)) (e := (((-4)/(5)):ℝ)) (f := (((2273)/(10000)):ℝ)) (g := ((0):ℝ)) (lbX := (((9741093973450663672303640424728500)/(25196697771281949525454811739141351)):ℝ)) (ubY := (((195830038987494377739361)/(1040975230179992327556480)):ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith) hXb hYb
  have heq : (1/((((17)/(40))):ℝ))*(((9741093973450663672303640424728500)/(25196697771281949525454811739141351)):ℝ) - (1/((((2273)/(10000))):ℝ))*(((195830038987494377739361)/(1040975230179992327556480)):ℝ) ≥ (((4100779)/(50000000)):ℝ) := by norm_num
  linarith

-- piece `Q3b`: `a ∈ [11931/40000, 3/8]`, `b ∈ [17/40+(-4/5)a, 5/8+(-4/3)a]`
private lemma Q3b_lower :
    (((1508031)/(10000000)):ℝ) ≤ ∫ a in (((11931)/(40000)):ℝ)..(((3)/(8)):ℝ), (1/a)*(1/(((((17)/(40))):ℝ) + (((-4)/(5)))*a) - 1/(((((5)/(8))):ℝ) + (((-4)/(3)))*a)) := by
  have hXe : (((((3)/(8)))/(((11931)/(40000))))/(((((17)/(40))) + (((-4)/(5)))*(((3)/(8))))/((((17)/(40))) + (((-4)/(5)))*(((11931)/(40000)))))) = (((37276)/(19885)):ℝ) := by norm_num
  have hX1 : (1:ℝ) ≤ (((37276)/(19885)):ℝ) := by norm_num
  have hXb0 : (((1917091550606765226634182)/(3051188887320144321509005)):ℝ) ≤ Real.log (((37276)/(19885)):ℝ) := by
    have hh := log_series_lb hX1
    norm_num at hh
    linarith
  have hXb : (((1917091550606765226634182)/(3051188887320144321509005)):ℝ) ≤ Real.log (((((3)/(8)))/(((11931)/(40000))))/(((((17)/(40))) + (((-4)/(5)))*(((3)/(8))))/((((17)/(40))) + (((-4)/(5)))*(((11931)/(40000)))))) := by rw [hXe]; exact hXb0
  have hYe : (((((3)/(8)))/(((11931)/(40000))))/(((((5)/(8))) + (((-4)/(3)))*(((3)/(8))))/((((5)/(8))) + (((-4)/(3)))*(((11931)/(40000)))))) = (((9092)/(3977)):ℝ) := by norm_num
  have hY1 : (1:ℝ) ≤ (((9092)/(3977)):ℝ) := by norm_num
  have hYb0 : Real.log (((9092)/(3977)):ℝ) ≤ (((22876791564916213511523933315)/(27571272049877658638407029032)):ℝ) := by
    have hh := log_series_ub hY1
    norm_num at hh
    linarith
  have hYb : Real.log (((((3)/(8)))/(((11931)/(40000))))/(((((5)/(8))) + (((-4)/(3)))*(((3)/(8))))/((((5)/(8))) + (((-4)/(3)))*(((11931)/(40000)))))) ≤ (((22876791564916213511523933315)/(27571272049877658638407029032)):ℝ) := by rw [hYe]; exact hYb0
  have hmain := trap_lower (A1 := (((11931)/(40000)):ℝ)) (A2 := (((3)/(8)):ℝ)) (c := (((17)/(40)):ℝ)) (e := (((-4)/(5)):ℝ)) (f := (((5)/(8)):ℝ)) (g := (((-4)/(3)):ℝ)) (lbX := (((1917091550606765226634182)/(3051188887320144321509005)):ℝ)) (ubY := (((22876791564916213511523933315)/(27571272049877658638407029032)):ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith) hXb hYb
  have heq : (1/((((17)/(40))):ℝ))*(((1917091550606765226634182)/(3051188887320144321509005)):ℝ) - (1/((((5)/(8))):ℝ))*(((22876791564916213511523933315)/(27571272049877658638407029032)):ℝ) ≥ (((1508031)/(10000000)):ℝ) := by norm_num
  linarith

-- piece `Q4a`: `a ∈ [14431/40000, 16477/40000]`, `b ∈ [17/24+(-4/3)a, 2273/10000+(0)a]`
private lemma Q4a_lower :
    (((1343499)/(12500000)):ℝ) ≤ ∫ a in (((14431)/(40000)):ℝ)..(((16477)/(40000)):ℝ), (1/a)*(1/(((((17)/(24))):ℝ) + (((-4)/(3)))*a) - 1/(((((2273)/(10000))):ℝ) + ((0))*a)) := by
  have hXe : (((((16477)/(40000)))/(((14431)/(40000))))/(((((17)/(24))) + (((-4)/(3)))*(((16477)/(40000))))/((((17)/(24))) + (((-4)/(3)))*(((14431)/(40000)))))) = (((37452221)/(22959721)):ℝ) := by norm_num
  have hX1 : (1:ℝ) ≤ (((37452221)/(22959721)):ℝ) := by norm_num
  have hXb0 : (((12304073320262365753104311362758642500)/(25145715957729105000133429264588918851)):ℝ) ≤ Real.log (((37452221)/(22959721)):ℝ) := by
    have hh := log_series_lb hX1
    norm_num at hh
    linarith
  have hXb : (((12304073320262365753104311362758642500)/(25145715957729105000133429264588918851)):ℝ) ≤ Real.log (((((16477)/(40000)))/(((14431)/(40000))))/(((((17)/(24))) + (((-4)/(3)))*(((16477)/(40000))))/((((17)/(24))) + (((-4)/(3)))*(((14431)/(40000)))))) := by rw [hXe]; exact hXb0
  have hYe : (((((16477)/(40000)))/(((14431)/(40000))))/(((((2273)/(10000))) + ((0))*(((16477)/(40000))))/((((2273)/(10000))) + ((0))*(((14431)/(40000)))))) = (((16477)/(14431)):ℝ) := by norm_num
  have hY1 : (1:ℝ) ≤ (((16477)/(14431)):ℝ) := by norm_num
  have hYb0 : Real.log (((16477)/(14431)):ℝ) ≤ (((17368385149213999619583725949)/(130996328995866639077672818180)):ℝ) := by
    have hh := log_series_ub hY1
    norm_num at hh
    linarith
  have hYb : Real.log (((((16477)/(40000)))/(((14431)/(40000))))/(((((2273)/(10000))) + ((0))*(((16477)/(40000))))/((((2273)/(10000))) + ((0))*(((14431)/(40000)))))) ≤ (((17368385149213999619583725949)/(130996328995866639077672818180)):ℝ) := by rw [hYe]; exact hYb0
  have hmain := trap_lower (A1 := (((14431)/(40000)):ℝ)) (A2 := (((16477)/(40000)):ℝ)) (c := (((17)/(24)):ℝ)) (e := (((-4)/(3)):ℝ)) (f := (((2273)/(10000)):ℝ)) (g := ((0):ℝ)) (lbX := (((12304073320262365753104311362758642500)/(25145715957729105000133429264588918851)):ℝ)) (ubY := (((17368385149213999619583725949)/(130996328995866639077672818180)):ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith) hXb hYb
  have heq : (1/((((17)/(24))):ℝ))*(((12304073320262365753104311362758642500)/(25145715957729105000133429264588918851)):ℝ) - (1/((((2273)/(10000))):ℝ))*(((17368385149213999619583725949)/(130996328995866639077672818180)):ℝ) ≥ (((1343499)/(12500000)):ℝ) := by norm_num
  linarith

-- piece `Q4b`: `a ∈ [16477/40000, 7/16]`, `b ∈ [17/24+(-4/3)a, 15/8+(-4)a]`
private lemma Q4b_lower :
    (((3710637)/(50000000)):ℝ) ≤ ∫ a in (((16477)/(40000)):ℝ)..(((7)/(16)):ℝ), (1/a)*(1/(((((17)/(24))):ℝ) + (((-4)/(3)))*a) - 1/(((((15)/(8))):ℝ) + ((-4))*a)) := by
  have hXe : (((((7)/(16)))/(((16477)/(40000))))/(((((17)/(24))) + (((-4)/(3)))*(((7)/(16))))/((((17)/(24))) + (((-4)/(3)))*(((16477)/(40000)))))) = (((22274)/(16477)):ℝ) := by norm_num
  have hX1 : (1:ℝ) ≤ (((22274)/(16477)):ℝ) := by norm_num
  have hXb0 : (((131706073652735104477394)/(436902546305348516593755)):ℝ) ≤ Real.log (((22274)/(16477)):ℝ) := by
    have hh := log_series_lb hX1
    norm_num at hh
    linarith
  have hXb : (((131706073652735104477394)/(436902546305348516593755)):ℝ) ≤ Real.log (((((7)/(16)))/(((16477)/(40000))))/(((((17)/(24))) + (((-4)/(3)))*(((7)/(16))))/((((17)/(24))) + (((-4)/(3)))*(((16477)/(40000)))))) := by rw [hXe]; exact hXb0
  have hYe : (((((7)/(16)))/(((16477)/(40000))))/(((((15)/(8))) + ((-4))*(((7)/(16))))/((((15)/(8))) + ((-4))*(((16477)/(40000)))))) = (((31822)/(16477)):ℝ) := by norm_num
  have hY1 : (1:ℝ) ≤ (((31822)/(16477)):ℝ) := by norm_num
  have hYb0 : Real.log (((31822)/(16477)):ℝ) ≤ (((181589903619348069263260623642345)/(275629885090043211330482796539812)):ℝ) := by
    have hh := log_series_ub hY1
    norm_num at hh
    linarith
  have hYb : Real.log (((((7)/(16)))/(((16477)/(40000))))/(((((15)/(8))) + ((-4))*(((7)/(16))))/((((15)/(8))) + ((-4))*(((16477)/(40000)))))) ≤ (((181589903619348069263260623642345)/(275629885090043211330482796539812)):ℝ) := by rw [hYe]; exact hYb0
  have hmain := trap_lower (A1 := (((16477)/(40000)):ℝ)) (A2 := (((7)/(16)):ℝ)) (c := (((17)/(24)):ℝ)) (e := (((-4)/(3)):ℝ)) (f := (((15)/(8)):ℝ)) (g := ((-4):ℝ)) (lbX := (((131706073652735104477394)/(436902546305348516593755)):ℝ)) (ubY := (((181589903619348069263260623642345)/(275629885090043211330482796539812)):ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith) hXb hYb
  have heq : (1/((((17)/(24))):ℝ))*(((131706073652735104477394)/(436902546305348516593755)):ℝ) - (1/((((15)/(8))):ℝ))*(((181589903619348069263260623642345)/(275629885090043211330482796539812)):ℝ) ≥ (((3710637)/(50000000)):ℝ) := by norm_num
  linarith

-- piece `Q5`: `a ∈ [18977/40000, 1/2]`, `b ∈ [17/8+(-4)a, 2273/10000+(0)a]`
private lemma Q5_lower :
    (((1876579)/(25000000)):ℝ) ≤ ∫ a in (((18977)/(40000)):ℝ)..(((1)/(2)):ℝ), (1/a)*(1/(((((17)/(8))):ℝ) + ((-4))*a) - 1/(((((2273)/(10000))):ℝ) + ((0))*a)) := by
  have hXe : (((((1)/(2)))/(((18977)/(40000))))/(((((17)/(8))) + ((-4))*(((1)/(2))))/((((17)/(8))) + ((-4))*(((18977)/(40000)))))) = (((36368)/(18977)):ℝ) := by norm_num
  have hX1 : (1:ℝ) ≤ (((36368)/(18977)):ℝ) := by norm_num
  have hXb0 : (((1688577736221076659508902)/(2596342385221026349203125)):ℝ) ≤ Real.log (((36368)/(18977)):ℝ) := by
    have hh := log_series_lb hX1
    norm_num at hh
    linarith
  have hXb : (((1688577736221076659508902)/(2596342385221026349203125)):ℝ) ≤ Real.log (((((1)/(2)))/(((18977)/(40000))))/(((((17)/(8))) + ((-4))*(((1)/(2))))/((((17)/(8))) + ((-4))*(((18977)/(40000)))))) := by rw [hXe]; exact hXb0
  have hYe : (((((1)/(2)))/(((18977)/(40000))))/(((((2273)/(10000))) + ((0))*(((1)/(2))))/((((2273)/(10000))) + ((0))*(((18977)/(40000)))))) = (((20000)/(18977)):ℝ) := by norm_num
  have hY1 : (1:ℝ) ≤ (((20000)/(18977)):ℝ) := by norm_num
  have hYb0 : Real.log (((20000)/(18977)):ℝ) ≤ (((3585308808000472274373968664447)/(68285673052557710211425355560000)):ℝ) := by
    have hh := log_series_ub hY1
    norm_num at hh
    linarith
  have hYb : Real.log (((((1)/(2)))/(((18977)/(40000))))/(((((2273)/(10000))) + ((0))*(((1)/(2))))/((((2273)/(10000))) + ((0))*(((18977)/(40000)))))) ≤ (((3585308808000472274373968664447)/(68285673052557710211425355560000)):ℝ) := by rw [hYe]; exact hYb0
  have hmain := trap_lower (A1 := (((18977)/(40000)):ℝ)) (A2 := (((1)/(2)):ℝ)) (c := (((17)/(8)):ℝ)) (e := ((-4):ℝ)) (f := (((2273)/(10000)):ℝ)) (g := ((0):ℝ)) (lbX := (((1688577736221076659508902)/(2596342385221026349203125)):ℝ)) (ubY := (((3585308808000472274373968664447)/(68285673052557710211425355560000)):ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith) hXb hYb
  have heq : (1/((((17)/(8))):ℝ))*(((1688577736221076659508902)/(2596342385221026349203125)):ℝ) - (1/((((2273)/(10000))):ℝ))*(((3585308808000472274373968664447)/(68285673052557710211425355560000)):ℝ) ≥ (((1876579)/(25000000)):ℝ) := by norm_num
  linarith

-- piece `Q6a`: `a ∈ [2273/10000, 1/4]`, `b ∈ [2273/10000+(0)a, 0+(1)a]`
private lemma Q6a_lower :
    (((38629)/(2000000)):ℝ) ≤ ∫ a in (((2273)/(10000)):ℝ)..(((1)/(4)):ℝ), (1/a)*(1/(((((2273)/(10000))):ℝ) + ((0))*a) - 1/((0:ℝ) + (1)*a)) := by
  have hXe : (((((1)/(4)))/(((2273)/(10000))))/(((((2273)/(10000))) + ((0))*(((1)/(4))))/((((2273)/(10000))) + ((0))*(((2273)/(10000)))))) = (((2500)/(2273)):ℝ) := by norm_num
  have hX1 : (1:ℝ) ≤ (((2500)/(2273)):ℝ) := by norm_num
  have hXb0 : (((1179015067918278574)/(12385888787285175465)):ℝ) ≤ Real.log (((2500)/(2273)):ℝ) := by
    have hh := log_series_lb hX1
    norm_num at hh
    linarith
  have hXb : (((1179015067918278574)/(12385888787285175465)):ℝ) ≤ Real.log (((((1)/(4)))/(((2273)/(10000))))/(((((2273)/(10000))) + ((0))*(((1)/(4))))/((((2273)/(10000))) + ((0))*(((2273)/(10000)))))) := by rw [hXe]; exact hXb0
  have hmain := trap_lower_Z (A1 := (((2273)/(10000)):ℝ)) (A2 := (((1)/(4)):ℝ)) (c := (((2273)/(10000)):ℝ)) (e := ((0):ℝ)) (lbX := (((1179015067918278574)/(12385888787285175465)):ℝ))
    (by norm_num) (by norm_num) (by norm_num) (fun a _ _ => by linarith) hXb
  have heq : (1/((((2273)/(10000))):ℝ))*(((1179015067918278574)/(12385888787285175465)):ℝ) - (1/(((2273)/(10000)):ℝ) - 1/(((1)/(4)):ℝ)) ≥ (((38629)/(2000000)):ℝ) := by norm_num
  linarith

-- piece `Q6b`: `a ∈ [1/4, 1/2]`, `b ∈ [2273/10000+(0)a, 1/4+(0)a]`
private lemma Q6b_lower :
    (((5454411)/(20000000)):ℝ) ≤ ∫ a in (((1)/(4)):ℝ)..(((1)/(2)):ℝ), (1/a)*(1/(((((2273)/(10000))):ℝ) + ((0))*a) - 1/(((((1)/(4))):ℝ) + ((0))*a)) := by
  have hXe : (((((1)/(2)))/(((1)/(4))))/(((((2273)/(10000))) + ((0))*(((1)/(2))))/((((2273)/(10000))) + ((0))*(((1)/(4)))))) = ((2):ℝ) := by norm_num
  have hX1 : (1:ℝ) ≤ ((2):ℝ) := by norm_num
  have hXb0 : (((842)/(1215)):ℝ) ≤ Real.log ((2):ℝ) := by
    have hh := log_series_lb hX1
    norm_num at hh
    linarith
  have hXb : (((842)/(1215)):ℝ) ≤ Real.log (((((1)/(2)))/(((1)/(4))))/(((((2273)/(10000))) + ((0))*(((1)/(2))))/((((2273)/(10000))) + ((0))*(((1)/(4)))))) := by rw [hXe]; exact hXb0
  have hYe : (((((1)/(2)))/(((1)/(4))))/(((((1)/(4))) + ((0))*(((1)/(2))))/((((1)/(4))) + ((0))*(((1)/(4)))))) = ((2):ℝ) := by norm_num
  have hY1 : (1:ℝ) ≤ ((2):ℝ) := by norm_num
  have hYb0 : Real.log ((2):ℝ) ≤ (((3373)/(4860)):ℝ) := by
    have hh := log_series_ub hY1
    norm_num at hh
    linarith
  have hYb : Real.log (((((1)/(2)))/(((1)/(4))))/(((((1)/(4))) + ((0))*(((1)/(2))))/((((1)/(4))) + ((0))*(((1)/(4)))))) ≤ (((3373)/(4860)):ℝ) := by rw [hYe]; exact hYb0
  have hmain := trap_lower (A1 := (((1)/(4)):ℝ)) (A2 := (((1)/(2)):ℝ)) (c := (((2273)/(10000)):ℝ)) (e := ((0):ℝ)) (f := (((1)/(4)):ℝ)) (g := ((0):ℝ)) (lbX := (((842)/(1215)):ℝ)) (ubY := (((3373)/(4860)):ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith) hXb hYb
  have heq : (1/((((2273)/(10000))):ℝ))*(((842)/(1215)):ℝ) - (1/((((1)/(4))):ℝ))*(((3373)/(4860)):ℝ) ≥ (((5454411)/(20000000)):ℝ) := by norm_num
  linarith

-- piece `Q7a`: `a ∈ [1/4, 1/3]`, `b ∈ [1/4+(0)a, 0+(1)a]`
private lemma Q7a_lower :
    (((15072687)/(100000000)):ℝ) ≤ ∫ a in (((1)/(4)):ℝ)..(((1)/(3)):ℝ), (1/a)*(1/(((((1)/(4))):ℝ) + ((0))*a) - 1/((0:ℝ) + (1)*a)) := by
  have hXe : (((((1)/(3)))/(((1)/(4))))/(((((1)/(4))) + ((0))*(((1)/(3))))/((((1)/(4))) + ((0))*(((1)/(4)))))) = (((4)/(3)):ℝ) := by norm_num
  have hX1 : (1:ℝ) ≤ (((4)/(3)):ℝ) := by norm_num
  have hXb0 : (((72526)/(252105)):ℝ) ≤ Real.log (((4)/(3)):ℝ) := by
    have hh := log_series_lb hX1
    norm_num at hh
    linarith
  have hXb : (((72526)/(252105)):ℝ) ≤ Real.log (((((1)/(3)))/(((1)/(4))))/(((((1)/(4))) + ((0))*(((1)/(3))))/((((1)/(4))) + ((0))*(((1)/(4)))))) := by rw [hXe]; exact hXb0
  have hmain := trap_lower_Z (A1 := (((1)/(4)):ℝ)) (A2 := (((1)/(3)):ℝ)) (c := (((1)/(4)):ℝ)) (e := ((0):ℝ)) (lbX := (((72526)/(252105)):ℝ))
    (by norm_num) (by norm_num) (by norm_num) (fun a _ _ => by linarith) hXb
  have heq : (1/((((1)/(4))):ℝ))*(((72526)/(252105)):ℝ) - (1/(((1)/(4)):ℝ) - 1/(((1)/(3)):ℝ)) ≥ (((15072687)/(100000000)):ℝ) := by norm_num
  linarith

-- piece `Q7b`: `a ∈ [1/3, 1/2]`, `b ∈ [1/4+(0)a, 1/2+(-1/2)a]`
private lemma Q7b_lower :
    (((5844487)/(25000000)):ℝ) ≤ ∫ a in (((1)/(3)):ℝ)..(((1)/(2)):ℝ), (1/a)*(1/(((((1)/(4))):ℝ) + ((0))*a) - 1/(((((1)/(2))):ℝ) + (((-1)/(2)))*a)) := by
  have hXe : (((((1)/(2)))/(((1)/(3))))/(((((1)/(4))) + ((0))*(((1)/(2))))/((((1)/(4))) + ((0))*(((1)/(3)))))) = (((3)/(2)):ℝ) := by norm_num
  have hX1 : (1:ℝ) ≤ (((3)/(2)):ℝ) := by norm_num
  have hXb0 : (((19006)/(46875)):ℝ) ≤ Real.log (((3)/(2)):ℝ) := by
    have hh := log_series_lb hX1
    norm_num at hh
    linarith
  have hXb : (((19006)/(46875)):ℝ) ≤ Real.log (((((1)/(2)))/(((1)/(3))))/(((((1)/(4))) + ((0))*(((1)/(2))))/((((1)/(4))) + ((0))*(((1)/(3)))))) := by rw [hXe]; exact hXb0
  have hYe : (((((1)/(2)))/(((1)/(3))))/(((((1)/(2))) + (((-1)/(2)))*(((1)/(2))))/((((1)/(2))) + (((-1)/(2)))*(((1)/(3)))))) = ((2):ℝ) := by norm_num
  have hY1 : (1:ℝ) ≤ ((2):ℝ) := by norm_num
  have hYb0 : Real.log ((2):ℝ) ≤ (((3373)/(4860)):ℝ) := by
    have hh := log_series_ub hY1
    norm_num at hh
    linarith
  have hYb : Real.log (((((1)/(2)))/(((1)/(3))))/(((((1)/(2))) + (((-1)/(2)))*(((1)/(2))))/((((1)/(2))) + (((-1)/(2)))*(((1)/(3)))))) ≤ (((3373)/(4860)):ℝ) := by rw [hYe]; exact hYb0
  have hmain := trap_lower (A1 := (((1)/(3)):ℝ)) (A2 := (((1)/(2)):ℝ)) (c := (((1)/(4)):ℝ)) (e := ((0):ℝ)) (f := (((1)/(2)):ℝ)) (g := (((-1)/(2)):ℝ)) (lbX := (((19006)/(46875)):ℝ)) (ubY := (((3373)/(4860)):ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith) hXb hYb
  have heq : (1/((((1)/(4))):ℝ))*(((19006)/(46875)):ℝ) - (1/((((1)/(2))):ℝ))*(((3373)/(4860)):ℝ) ≥ (((5844487)/(25000000)):ℝ) := by norm_num
  linarith

/-- LEAF: the geometric step of the split. The first piece is the whole first band; the second and
third pieces are the two branches of the second band, distinguished by `a + b ≤ 7/16` against
`17/8 ≤ 4*a + 5*b`; the fourth and fifth pieces are the two branches of the third band,
distinguished by `4*a + b ≤ 15/8` against `17/8 ≤ 4*a + b`. Each piece repeats the branch
conditions of the band it comes from, so a point of any of them is a point of the target region,
with no use of the slack `ε` at all. -/
theorem leaf_band_union_membership (a b : ℝ) :
    (((((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧ a + b ≤ 7/16 ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 5*b ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 4*a + b ≤ 15/8)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 17/8 ≤ 4*a + b)) →
    ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) := by
  intro h
  rcases h with (((h | h) | h) | h) | h
  · obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact Or.inl ⟨h1, h2, h3, h4, h5⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
    exact Or.inr (Or.inl ⟨h1, h2, h3, h4, h5, h6, h7, h8, Or.inl h9, Or.inl h10⟩)
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    exact Or.inr (Or.inl ⟨h1, h2, h3, h4, h5, h6, h7, by linarith, Or.inr h8, Or.inl h9⟩)
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    exact Or.inr (Or.inr ⟨h1, h2, h3, h4, h5, h6, h7, Or.inl h8⟩)
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    exact Or.inr (Or.inr ⟨h1, h2, h3, h4, h5, h6, h7, Or.inr h8⟩)

/-- The pointwise bound of the five-piece union, used by the quadrature below and by
`leaf_band_union_integrand_bound`. -/
private lemma leaf_band_union_bound_aux (a b : ℝ) :
    |(if ((((((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧ a + b ≤ 7/16 ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 5*b ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 4*a + b ≤ 15/8)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)| ≤ 1000 := by
  split_ifs with h
  · have hb : (1/8 : ℝ) ≤ b := by
      rcases h with (((h | h) | h) | h) | h
      · obtain ⟨h1, -⟩ := h; linarith
      · obtain ⟨h1, -⟩ := h; exact h1
      · obtain ⟨h1, -⟩ := h; exact h1
      · obtain ⟨h1, -⟩ := h; exact h1
      · obtain ⟨h1, -⟩ := h; exact h1
    have hba : b ≤ a := by
      rcases h with (((h | h) | h) | h) | h
      · obtain ⟨-, h2, -⟩ := h; exact h2
      · obtain ⟨-, -, h2, -⟩ := h; exact h2
      · obtain ⟨-, -, h2, -⟩ := h; exact h2
      · obtain ⟨-, -, h2, -⟩ := h; exact h2
      · obtain ⟨-, -, h2, -⟩ := h; exact h2
    have ha : (1/8 : ℝ) ≤ a := le_trans hb hba
    have hb0 : (0:ℝ) < b := by linarith
    have ha0 : (0:ℝ) < a := by linarith
    have hsq : (1/64 : ℝ) ≤ b^2 := by nlinarith
    have h512 : (1/512 : ℝ) ≤ a*b^2 := by
      have := mul_le_mul ha hsq (by norm_num : (0:ℝ) ≤ 1/64) (by linarith : (0:ℝ) ≤ a)
      linarith
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(a*b^2))]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < a*b^2)]
    nlinarith
  · simp

set_option maxHeartbeats 8000000 in
/-- LEAF: the computation of the split. The integral of `1 / (a b^2)` over the union of the five
convex pieces is at least `13/10`; a floating point quadrature gives about `1.3941`, so there is a
margin of about `0.094` to spend on the rounding of any grid used for it. -/
theorem leaf_band_union_quadrature :
    13/10 ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if ((((((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧ a + b ≤ 7/16 ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 5*b ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 4*a + b ≤ 15/8)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0) := by
  set C : ℝ → ℝ → Prop := fun a b => ((((((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧ a + b ≤ 7/16 ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 5*b ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 4*a + b ≤ 15/8)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 17/8 ≤ 4*a + b))) with hC
  have hCb : ∀ a b, C a b → (1/8:ℝ) ≤ b := by
    intro a b h
    simp only [hC] at h
    rcases h with (((h | h) | h) | h) | h
    · obtain ⟨h1, -⟩ := h; linarith
    · obtain ⟨h1, -⟩ := h; exact h1
    · obtain ⟨h1, -⟩ := h; exact h1
    · obtain ⟨h1, -⟩ := h; exact h1
    · obtain ⟨h1, -⟩ := h; exact h1
  have hCa : ∀ a b, C a b → b ≤ a := by
    intro a b h
    simp only [hC] at h
    rcases h with (((h | h) | h) | h) | h
    · obtain ⟨-, h2, -⟩ := h; exact h2
    · obtain ⟨-, -, h2, -⟩ := h; exact h2
    · obtain ⟨-, -, h2, -⟩ := h; exact h2
    · obtain ⟨-, -, h2, -⟩ := h; exact h2
    · obtain ⟨-, -, h2, -⟩ := h; exact h2
  have hCmeas : MeasurableSet {p : ℝ × ℝ | C p.1 p.2} := by
    rw [hC]
    have hle : ∀ f g : ℝ × ℝ → ℝ, Continuous f → Continuous g →
        MeasurableSet {p | f p ≤ g p} := fun f g hf hg => (isClosed_le hf hg).measurableSet
    simp only [Set.ofPred_and, Set.ofPred_or]
    repeat' first
      | apply MeasurableSet.inter
      | apply MeasurableSet.union
      | (apply hle <;> fun_prop)
  have hFmeas : Measurable (fun p : ℝ × ℝ => if C p.1 p.2 then (1:ℝ)/(p.1*p.2^2) else 0) :=
    Measurable.ite hCmeas (by fun_prop) measurable_const
  have hFb : ∀ a b, |(if C a b then (1:ℝ)/(a*b^2) else 0)| ≤ 1000 := by
    intro a b
    have h := leaf_band_union_bound_aux a b
    simpa only [hC] using h
  have hinc1 : ∀ a b, (((2273)/(10000)):ℝ) ≤ a → a ≤ (((43)/(176)):ℝ) →
      ((((17)/(56))) + (((-4)/(7)))*a) ≤ b → b ≤ ((((17)/(88))) + ((0))*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨by linarith, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith, by linarith⟩)))
  have hinc2 : ∀ a b, (((43)/(176)):ℝ) ≤ a → a ≤ (((5)/(16)):ℝ) →
      ((((17)/(56))) + (((-4)/(7)))*a) ≤ b → b ≤ ((((7)/(16))) + ((-1))*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨by linarith, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith, by linarith⟩)))
  have hinc3 : ∀ a b, (((1977)/(8000)):ℝ) ≤ a → a ≤ (((11931)/(40000)):ℝ) →
      ((((17)/(40))) + (((-4)/(5)))*a) ≤ b → b ≤ ((((2273)/(10000))) + ((0))*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    exact Or.inl (Or.inl (Or.inr ⟨by linarith, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith⟩))
  have hinc4 : ∀ a b, (((11931)/(40000)):ℝ) ≤ a → a ≤ (((3)/(8)):ℝ) →
      ((((17)/(40))) + (((-4)/(5)))*a) ≤ b → b ≤ ((((5)/(8))) + (((-4)/(3)))*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    exact Or.inl (Or.inl (Or.inr ⟨by linarith, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith⟩))
  have hinc5 : ∀ a b, (((14431)/(40000)):ℝ) ≤ a → a ≤ (((16477)/(40000)):ℝ) →
      ((((17)/(24))) + (((-4)/(3)))*a) ≤ b → b ≤ ((((2273)/(10000))) + ((0))*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    exact Or.inl (Or.inr ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith⟩)
  have hinc6 : ∀ a b, (((16477)/(40000)):ℝ) ≤ a → a ≤ (((7)/(16)):ℝ) →
      ((((17)/(24))) + (((-4)/(3)))*a) ≤ b → b ≤ ((((15)/(8))) + ((-4))*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    exact Or.inl (Or.inr ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith⟩)
  have hinc7 : ∀ a b, (((18977)/(40000)):ℝ) ≤ a → a ≤ (((1)/(2)):ℝ) →
      ((((17)/(8))) + ((-4))*a) ≤ b → b ≤ ((((2273)/(10000))) + ((0))*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    exact Or.inr ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith⟩
  have hinc8 : ∀ a b, (((2273)/(10000)):ℝ) ≤ a → a ≤ (((1)/(4)):ℝ) →
      ((((2273)/(10000))) + ((0))*a) ≤ b → b ≤ (((0)) + ((1))*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    exact Or.inl (Or.inl (Or.inl (Or.inl ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩)))
  have hinc9 : ∀ a b, (((1)/(4)):ℝ) ≤ a → a ≤ (((1)/(2)):ℝ) →
      ((((2273)/(10000))) + ((0))*a) ≤ b → b ≤ ((((1)/(4))) + ((0))*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    exact Or.inl (Or.inl (Or.inl (Or.inl ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩)))
  have hinc10 : ∀ a b, (((1)/(4)):ℝ) ≤ a → a ≤ (((1)/(3)):ℝ) →
      ((((1)/(4))) + ((0))*a) ≤ b → b ≤ (((0)) + ((1))*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    exact Or.inl (Or.inl (Or.inl (Or.inl ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩)))
  have hinc11 : ∀ a b, (((1)/(3)):ℝ) ≤ a → a ≤ (((1)/(2)):ℝ) →
      ((((1)/(4))) + ((0))*a) ≤ b → b ≤ ((((1)/(2))) + (((-1)/(2)))*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    exact Or.inl (Or.inl (Or.inl (Or.inl ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩)))
  -- the eleven trapezoid pieces
  let G1 : ℝ → ℝ → ℝ := fun a b =>
    (if ((((2273)/(10000)):ℝ) < a ∧ a ≤ (((43)/(176)):ℝ) ∧ ((((17)/(56)):ℝ) + (((-4)/(7)))*a) < b ∧ b ≤ ((((17)/(88)):ℝ) + ((0))*a)) then (1:ℝ)/(a*b^2) else 0)
  let G2 : ℝ → ℝ → ℝ := fun a b =>
    (if ((((43)/(176)):ℝ) < a ∧ a ≤ (((5)/(16)):ℝ) ∧ ((((17)/(56)):ℝ) + (((-4)/(7)))*a) < b ∧ b ≤ ((((7)/(16)):ℝ) + ((-1))*a)) then (1:ℝ)/(a*b^2) else 0)
  let G3 : ℝ → ℝ → ℝ := fun a b =>
    (if ((((1977)/(8000)):ℝ) < a ∧ a ≤ (((11931)/(40000)):ℝ) ∧ ((((17)/(40)):ℝ) + (((-4)/(5)))*a) < b ∧ b ≤ ((((2273)/(10000)):ℝ) + ((0))*a)) then (1:ℝ)/(a*b^2) else 0)
  let G4 : ℝ → ℝ → ℝ := fun a b =>
    (if ((((11931)/(40000)):ℝ) < a ∧ a ≤ (((3)/(8)):ℝ) ∧ ((((17)/(40)):ℝ) + (((-4)/(5)))*a) < b ∧ b ≤ ((((5)/(8)):ℝ) + (((-4)/(3)))*a)) then (1:ℝ)/(a*b^2) else 0)
  let G5 : ℝ → ℝ → ℝ := fun a b =>
    (if ((((14431)/(40000)):ℝ) < a ∧ a ≤ (((16477)/(40000)):ℝ) ∧ ((((17)/(24)):ℝ) + (((-4)/(3)))*a) < b ∧ b ≤ ((((2273)/(10000)):ℝ) + ((0))*a)) then (1:ℝ)/(a*b^2) else 0)
  let G6 : ℝ → ℝ → ℝ := fun a b =>
    (if ((((16477)/(40000)):ℝ) < a ∧ a ≤ (((7)/(16)):ℝ) ∧ ((((17)/(24)):ℝ) + (((-4)/(3)))*a) < b ∧ b ≤ ((((15)/(8)):ℝ) + ((-4))*a)) then (1:ℝ)/(a*b^2) else 0)
  let G7 : ℝ → ℝ → ℝ := fun a b =>
    (if ((((18977)/(40000)):ℝ) < a ∧ a ≤ (((1)/(2)):ℝ) ∧ ((((17)/(8)):ℝ) + ((-4))*a) < b ∧ b ≤ ((((2273)/(10000)):ℝ) + ((0))*a)) then (1:ℝ)/(a*b^2) else 0)
  let G8 : ℝ → ℝ → ℝ := fun a b =>
    (if ((((2273)/(10000)):ℝ) < a ∧ a ≤ (((1)/(4)):ℝ) ∧ ((((2273)/(10000)):ℝ) + ((0))*a) < b ∧ b ≤ (((0):ℝ) + ((1))*a)) then (1:ℝ)/(a*b^2) else 0)
  let G9 : ℝ → ℝ → ℝ := fun a b =>
    (if ((((1)/(4)):ℝ) < a ∧ a ≤ (((1)/(2)):ℝ) ∧ ((((2273)/(10000)):ℝ) + ((0))*a) < b ∧ b ≤ ((((1)/(4)):ℝ) + ((0))*a)) then (1:ℝ)/(a*b^2) else 0)
  let G10 : ℝ → ℝ → ℝ := fun a b =>
    (if ((((1)/(4)):ℝ) < a ∧ a ≤ (((1)/(3)):ℝ) ∧ ((((1)/(4)):ℝ) + ((0))*a) < b ∧ b ≤ (((0):ℝ) + ((1))*a)) then (1:ℝ)/(a*b^2) else 0)
  let G11 : ℝ → ℝ → ℝ := fun a b =>
    (if ((((1)/(3)):ℝ) < a ∧ a ≤ (((1)/(2)):ℝ) ∧ ((((1)/(4)):ℝ) + ((0))*a) < b ∧ b ≤ ((((1)/(2)):ℝ) + (((-1)/(2)))*a)) then (1:ℝ)/(a*b^2) else 0)
  obtain ⟨nm1, nb1, nn1, ni1, nI1, nJ1, no1, ne1⟩ := piece_G_all
      (A1 := (((2273)/(10000)):ℝ)) (A2 := (((43)/(176)):ℝ)) (c := (((17)/(56)):ℝ)) (e := (((-4)/(7)))) (f := (((17)/(88)):ℝ)) (g := ((0)))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have mb1 : Measurable (fun p : ℝ × ℝ => G1 p.1 p.2) := nm1
  have mB1 : ∀ a b : ℝ, |G1 a b| ≤ 1000 := nb1
  have mN1 : ∀ a b : ℝ, 0 ≤ G1 a b := nn1
  have mI1 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => G1 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := ni1
  have lv1 : Measurable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G1 a b) := nI1
  have lb1 : ∀ a : ℝ, |∫ b in (1/10:ℝ)..(1/2:ℝ), G1 a b| ≤ 1000 := nJ1
  have li1 : IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G1 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := no1
  have ev1 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G1 a b)
      = ∫ a in (((2273)/(10000)):ℝ)..(((43)/(176)):ℝ), (1/a)*(1/((((17)/(56)):ℝ) + (((-4)/(7)))*a) - 1/((((17)/(88)):ℝ) + ((0))*a)) := ne1
  have zZ1 : ∀ a b : ℝ, ¬((((2273)/(10000)):ℝ) < a ∧ a ≤ (((43)/(176)):ℝ) ∧ ((((17)/(56)):ℝ) + (((-4)/(7)))*a) < b ∧ b ≤ ((((17)/(88)):ℝ) + ((0))*a)) → G1 a b = 0 := fun a b h => if_neg h
  have vV1 : ∀ a b : ℝ, ((((2273)/(10000)):ℝ) < a ∧ a ≤ (((43)/(176)):ℝ) ∧ ((((17)/(56)):ℝ) + (((-4)/(7)))*a) < b ∧ b ≤ ((((17)/(88)):ℝ) + ((0))*a)) → G1 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P1 : (673691/12500000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G1 a b := by
    rw [ev1]
    linarith [Q1a2b_lower]
  obtain ⟨nm2, nb2, nn2, ni2, nI2, nJ2, no2, ne2⟩ := piece_G_all
      (A1 := (((43)/(176)):ℝ)) (A2 := (((5)/(16)):ℝ)) (c := (((17)/(56)):ℝ)) (e := (((-4)/(7)))) (f := (((7)/(16)):ℝ)) (g := ((-1)))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have mb2 : Measurable (fun p : ℝ × ℝ => G2 p.1 p.2) := nm2
  have mB2 : ∀ a b : ℝ, |G2 a b| ≤ 1000 := nb2
  have mN2 : ∀ a b : ℝ, 0 ≤ G2 a b := nn2
  have mI2 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => G2 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := ni2
  have lv2 : Measurable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b) := nI2
  have lb2 : ∀ a : ℝ, |∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b| ≤ 1000 := nJ2
  have li2 : IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := no2
  have ev2 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b)
      = ∫ a in (((43)/(176)):ℝ)..(((5)/(16)):ℝ), (1/a)*(1/((((17)/(56)):ℝ) + (((-4)/(7)))*a) - 1/((((7)/(16)):ℝ) + ((-1))*a)) := ne2
  have zZ2 : ∀ a b : ℝ, ¬((((43)/(176)):ℝ) < a ∧ a ≤ (((5)/(16)):ℝ) ∧ ((((17)/(56)):ℝ) + (((-4)/(7)))*a) < b ∧ b ≤ ((((7)/(16)):ℝ) + ((-1))*a)) → G2 a b = 0 := fun a b h => if_neg h
  have vV2 : ∀ a b : ℝ, ((((43)/(176)):ℝ) < a ∧ a ≤ (((5)/(16)):ℝ) ∧ ((((17)/(56)):ℝ) + (((-4)/(7)))*a) < b ∧ b ≤ ((((7)/(16)):ℝ) + ((-1))*a)) → G2 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P2 : (906629/6250000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b := by
    rw [ev2]
    linarith [Q1b_lower]
  obtain ⟨nm3, nb3, nn3, ni3, nI3, nJ3, no3, ne3⟩ := piece_G_all
      (A1 := (((1977)/(8000)):ℝ)) (A2 := (((11931)/(40000)):ℝ)) (c := (((17)/(40)):ℝ)) (e := (((-4)/(5)))) (f := (((2273)/(10000)):ℝ)) (g := ((0)))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have mb3 : Measurable (fun p : ℝ × ℝ => G3 p.1 p.2) := nm3
  have mB3 : ∀ a b : ℝ, |G3 a b| ≤ 1000 := nb3
  have mN3 : ∀ a b : ℝ, 0 ≤ G3 a b := nn3
  have mI3 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => G3 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := ni3
  have lv3 : Measurable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b) := nI3
  have lb3 : ∀ a : ℝ, |∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b| ≤ 1000 := nJ3
  have li3 : IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := no3
  have ev3 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b)
      = ∫ a in (((1977)/(8000)):ℝ)..(((11931)/(40000)):ℝ), (1/a)*(1/((((17)/(40)):ℝ) + (((-4)/(5)))*a) - 1/((((2273)/(10000)):ℝ) + ((0))*a)) := ne3
  have zZ3 : ∀ a b : ℝ, ¬((((1977)/(8000)):ℝ) < a ∧ a ≤ (((11931)/(40000)):ℝ) ∧ ((((17)/(40)):ℝ) + (((-4)/(5)))*a) < b ∧ b ≤ ((((2273)/(10000)):ℝ) + ((0))*a)) → G3 a b = 0 := fun a b h => if_neg h
  have vV3 : ∀ a b : ℝ, ((((1977)/(8000)):ℝ) < a ∧ a ≤ (((11931)/(40000)):ℝ) ∧ ((((17)/(40)):ℝ) + (((-4)/(5)))*a) < b ∧ b ≤ ((((2273)/(10000)):ℝ) + ((0))*a)) → G3 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P3 : (4100779/50000000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b := by
    rw [ev3]
    linarith [Q3a_lower]
  obtain ⟨nm4, nb4, nn4, ni4, nI4, nJ4, no4, ne4⟩ := piece_G_all
      (A1 := (((11931)/(40000)):ℝ)) (A2 := (((3)/(8)):ℝ)) (c := (((17)/(40)):ℝ)) (e := (((-4)/(5)))) (f := (((5)/(8)):ℝ)) (g := (((-4)/(3))))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have mb4 : Measurable (fun p : ℝ × ℝ => G4 p.1 p.2) := nm4
  have mB4 : ∀ a b : ℝ, |G4 a b| ≤ 1000 := nb4
  have mN4 : ∀ a b : ℝ, 0 ≤ G4 a b := nn4
  have mI4 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => G4 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := ni4
  have lv4 : Measurable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) := nI4
  have lb4 : ∀ a : ℝ, |∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b| ≤ 1000 := nJ4
  have li4 : IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := no4
  have ev4 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b)
      = ∫ a in (((11931)/(40000)):ℝ)..(((3)/(8)):ℝ), (1/a)*(1/((((17)/(40)):ℝ) + (((-4)/(5)))*a) - 1/((((5)/(8)):ℝ) + (((-4)/(3)))*a)) := ne4
  have zZ4 : ∀ a b : ℝ, ¬((((11931)/(40000)):ℝ) < a ∧ a ≤ (((3)/(8)):ℝ) ∧ ((((17)/(40)):ℝ) + (((-4)/(5)))*a) < b ∧ b ≤ ((((5)/(8)):ℝ) + (((-4)/(3)))*a)) → G4 a b = 0 := fun a b h => if_neg h
  have vV4 : ∀ a b : ℝ, ((((11931)/(40000)):ℝ) < a ∧ a ≤ (((3)/(8)):ℝ) ∧ ((((17)/(40)):ℝ) + (((-4)/(5)))*a) < b ∧ b ≤ ((((5)/(8)):ℝ) + (((-4)/(3)))*a)) → G4 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P4 : (1508031/10000000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b := by
    rw [ev4]
    linarith [Q3b_lower]
  obtain ⟨nm5, nb5, nn5, ni5, nI5, nJ5, no5, ne5⟩ := piece_G_all
      (A1 := (((14431)/(40000)):ℝ)) (A2 := (((16477)/(40000)):ℝ)) (c := (((17)/(24)):ℝ)) (e := (((-4)/(3)))) (f := (((2273)/(10000)):ℝ)) (g := ((0)))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have mb5 : Measurable (fun p : ℝ × ℝ => G5 p.1 p.2) := nm5
  have mB5 : ∀ a b : ℝ, |G5 a b| ≤ 1000 := nb5
  have mN5 : ∀ a b : ℝ, 0 ≤ G5 a b := nn5
  have mI5 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => G5 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := ni5
  have lv5 : Measurable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) := nI5
  have lb5 : ∀ a : ℝ, |∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b| ≤ 1000 := nJ5
  have li5 : IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := no5
  have ev5 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b)
      = ∫ a in (((14431)/(40000)):ℝ)..(((16477)/(40000)):ℝ), (1/a)*(1/((((17)/(24)):ℝ) + (((-4)/(3)))*a) - 1/((((2273)/(10000)):ℝ) + ((0))*a)) := ne5
  have zZ5 : ∀ a b : ℝ, ¬((((14431)/(40000)):ℝ) < a ∧ a ≤ (((16477)/(40000)):ℝ) ∧ ((((17)/(24)):ℝ) + (((-4)/(3)))*a) < b ∧ b ≤ ((((2273)/(10000)):ℝ) + ((0))*a)) → G5 a b = 0 := fun a b h => if_neg h
  have vV5 : ∀ a b : ℝ, ((((14431)/(40000)):ℝ) < a ∧ a ≤ (((16477)/(40000)):ℝ) ∧ ((((17)/(24)):ℝ) + (((-4)/(3)))*a) < b ∧ b ≤ ((((2273)/(10000)):ℝ) + ((0))*a)) → G5 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P5 : (1343499/12500000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b := by
    rw [ev5]
    linarith [Q4a_lower]
  obtain ⟨nm6, nb6, nn6, ni6, nI6, nJ6, no6, ne6⟩ := piece_G_all
      (A1 := (((16477)/(40000)):ℝ)) (A2 := (((7)/(16)):ℝ)) (c := (((17)/(24)):ℝ)) (e := (((-4)/(3)))) (f := (((15)/(8)):ℝ)) (g := ((-4)))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have mb6 : Measurable (fun p : ℝ × ℝ => G6 p.1 p.2) := nm6
  have mB6 : ∀ a b : ℝ, |G6 a b| ≤ 1000 := nb6
  have mN6 : ∀ a b : ℝ, 0 ≤ G6 a b := nn6
  have mI6 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => G6 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := ni6
  have lv6 : Measurable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) := nI6
  have lb6 : ∀ a : ℝ, |∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b| ≤ 1000 := nJ6
  have li6 : IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := no6
  have ev6 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b)
      = ∫ a in (((16477)/(40000)):ℝ)..(((7)/(16)):ℝ), (1/a)*(1/((((17)/(24)):ℝ) + (((-4)/(3)))*a) - 1/((((15)/(8)):ℝ) + ((-4))*a)) := ne6
  have zZ6 : ∀ a b : ℝ, ¬((((16477)/(40000)):ℝ) < a ∧ a ≤ (((7)/(16)):ℝ) ∧ ((((17)/(24)):ℝ) + (((-4)/(3)))*a) < b ∧ b ≤ ((((15)/(8)):ℝ) + ((-4))*a)) → G6 a b = 0 := fun a b h => if_neg h
  have vV6 : ∀ a b : ℝ, ((((16477)/(40000)):ℝ) < a ∧ a ≤ (((7)/(16)):ℝ) ∧ ((((17)/(24)):ℝ) + (((-4)/(3)))*a) < b ∧ b ≤ ((((15)/(8)):ℝ) + ((-4))*a)) → G6 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P6 : (3710637/50000000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b := by
    rw [ev6]
    linarith [Q4b_lower]
  obtain ⟨nm7, nb7, nn7, ni7, nI7, nJ7, no7, ne7⟩ := piece_G_all
      (A1 := (((18977)/(40000)):ℝ)) (A2 := (((1)/(2)):ℝ)) (c := (((17)/(8)):ℝ)) (e := ((-4))) (f := (((2273)/(10000)):ℝ)) (g := ((0)))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have mb7 : Measurable (fun p : ℝ × ℝ => G7 p.1 p.2) := nm7
  have mB7 : ∀ a b : ℝ, |G7 a b| ≤ 1000 := nb7
  have mN7 : ∀ a b : ℝ, 0 ≤ G7 a b := nn7
  have mI7 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => G7 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := ni7
  have lv7 : Measurable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) := nI7
  have lb7 : ∀ a : ℝ, |∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b| ≤ 1000 := nJ7
  have li7 : IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := no7
  have ev7 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b)
      = ∫ a in (((18977)/(40000)):ℝ)..(((1)/(2)):ℝ), (1/a)*(1/((((17)/(8)):ℝ) + ((-4))*a) - 1/((((2273)/(10000)):ℝ) + ((0))*a)) := ne7
  have zZ7 : ∀ a b : ℝ, ¬((((18977)/(40000)):ℝ) < a ∧ a ≤ (((1)/(2)):ℝ) ∧ ((((17)/(8)):ℝ) + ((-4))*a) < b ∧ b ≤ ((((2273)/(10000)):ℝ) + ((0))*a)) → G7 a b = 0 := fun a b h => if_neg h
  have vV7 : ∀ a b : ℝ, ((((18977)/(40000)):ℝ) < a ∧ a ≤ (((1)/(2)):ℝ) ∧ ((((17)/(8)):ℝ) + ((-4))*a) < b ∧ b ≤ ((((2273)/(10000)):ℝ) + ((0))*a)) → G7 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P7 : (1876579/25000000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b := by
    rw [ev7]
    linarith [Q5_lower]
  obtain ⟨nm8, nb8, nn8, ni8, nI8, nJ8, no8, ne8⟩ := piece_G_all
      (A1 := (((2273)/(10000)):ℝ)) (A2 := (((1)/(4)):ℝ)) (c := (((2273)/(10000)):ℝ)) (e := ((0))) (f := ((0):ℝ)) (g := ((1)))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have mb8 : Measurable (fun p : ℝ × ℝ => G8 p.1 p.2) := nm8
  have mB8 : ∀ a b : ℝ, |G8 a b| ≤ 1000 := nb8
  have mN8 : ∀ a b : ℝ, 0 ≤ G8 a b := nn8
  have mI8 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => G8 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := ni8
  have lv8 : Measurable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) := nI8
  have lb8 : ∀ a : ℝ, |∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b| ≤ 1000 := nJ8
  have li8 : IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := no8
  have ev8 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b)
      = ∫ a in (((2273)/(10000)):ℝ)..(((1)/(4)):ℝ), (1/a)*(1/((((2273)/(10000)):ℝ) + ((0))*a) - 1/(((0):ℝ) + ((1))*a)) := ne8
  have zZ8 : ∀ a b : ℝ, ¬((((2273)/(10000)):ℝ) < a ∧ a ≤ (((1)/(4)):ℝ) ∧ ((((2273)/(10000)):ℝ) + ((0))*a) < b ∧ b ≤ (((0):ℝ) + ((1))*a)) → G8 a b = 0 := fun a b h => if_neg h
  have vV8 : ∀ a b : ℝ, ((((2273)/(10000)):ℝ) < a ∧ a ≤ (((1)/(4)):ℝ) ∧ ((((2273)/(10000)):ℝ) + ((0))*a) < b ∧ b ≤ (((0):ℝ) + ((1))*a)) → G8 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P8 : (38629/2000000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b := by
    rw [ev8]
    linarith [Q6a_lower]
  obtain ⟨nm9, nb9, nn9, ni9, nI9, nJ9, no9, ne9⟩ := piece_G_all
      (A1 := (((1)/(4)):ℝ)) (A2 := (((1)/(2)):ℝ)) (c := (((2273)/(10000)):ℝ)) (e := ((0))) (f := (((1)/(4)):ℝ)) (g := ((0)))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have mb9 : Measurable (fun p : ℝ × ℝ => G9 p.1 p.2) := nm9
  have mB9 : ∀ a b : ℝ, |G9 a b| ≤ 1000 := nb9
  have mN9 : ∀ a b : ℝ, 0 ≤ G9 a b := nn9
  have mI9 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => G9 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := ni9
  have lv9 : Measurable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) := nI9
  have lb9 : ∀ a : ℝ, |∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b| ≤ 1000 := nJ9
  have li9 : IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := no9
  have ev9 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b)
      = ∫ a in (((1)/(4)):ℝ)..(((1)/(2)):ℝ), (1/a)*(1/((((2273)/(10000)):ℝ) + ((0))*a) - 1/((((1)/(4)):ℝ) + ((0))*a)) := ne9
  have zZ9 : ∀ a b : ℝ, ¬((((1)/(4)):ℝ) < a ∧ a ≤ (((1)/(2)):ℝ) ∧ ((((2273)/(10000)):ℝ) + ((0))*a) < b ∧ b ≤ ((((1)/(4)):ℝ) + ((0))*a)) → G9 a b = 0 := fun a b h => if_neg h
  have vV9 : ∀ a b : ℝ, ((((1)/(4)):ℝ) < a ∧ a ≤ (((1)/(2)):ℝ) ∧ ((((2273)/(10000)):ℝ) + ((0))*a) < b ∧ b ≤ ((((1)/(4)):ℝ) + ((0))*a)) → G9 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P9 : (5454411/20000000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b := by
    rw [ev9]
    linarith [Q6b_lower]
  obtain ⟨nm10, nb10, nn10, ni10, nI10, nJ10, no10, ne10⟩ := piece_G_all
      (A1 := (((1)/(4)):ℝ)) (A2 := (((1)/(3)):ℝ)) (c := (((1)/(4)):ℝ)) (e := ((0))) (f := ((0):ℝ)) (g := ((1)))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have mb10 : Measurable (fun p : ℝ × ℝ => G10 p.1 p.2) := nm10
  have mB10 : ∀ a b : ℝ, |G10 a b| ≤ 1000 := nb10
  have mN10 : ∀ a b : ℝ, 0 ≤ G10 a b := nn10
  have mI10 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => G10 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := ni10
  have lv10 : Measurable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) := nI10
  have lb10 : ∀ a : ℝ, |∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b| ≤ 1000 := nJ10
  have li10 : IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := no10
  have ev10 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b)
      = ∫ a in (((1)/(4)):ℝ)..(((1)/(3)):ℝ), (1/a)*(1/((((1)/(4)):ℝ) + ((0))*a) - 1/(((0):ℝ) + ((1))*a)) := ne10
  have zZ10 : ∀ a b : ℝ, ¬((((1)/(4)):ℝ) < a ∧ a ≤ (((1)/(3)):ℝ) ∧ ((((1)/(4)):ℝ) + ((0))*a) < b ∧ b ≤ (((0):ℝ) + ((1))*a)) → G10 a b = 0 := fun a b h => if_neg h
  have vV10 : ∀ a b : ℝ, ((((1)/(4)):ℝ) < a ∧ a ≤ (((1)/(3)):ℝ) ∧ ((((1)/(4)):ℝ) + ((0))*a) < b ∧ b ≤ (((0):ℝ) + ((1))*a)) → G10 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P10 : (15072687/100000000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b := by
    rw [ev10]
    linarith [Q7a_lower]
  obtain ⟨nm11, nb11, nn11, ni11, nI11, nJ11, no11, ne11⟩ := piece_G_all
      (A1 := (((1)/(3)):ℝ)) (A2 := (((1)/(2)):ℝ)) (c := (((1)/(4)):ℝ)) (e := ((0))) (f := (((1)/(2)):ℝ)) (g := (((-1)/(2))))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have mb11 : Measurable (fun p : ℝ × ℝ => G11 p.1 p.2) := nm11
  have mB11 : ∀ a b : ℝ, |G11 a b| ≤ 1000 := nb11
  have mN11 : ∀ a b : ℝ, 0 ≤ G11 a b := nn11
  have mI11 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => G11 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := ni11
  have lv11 : Measurable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b) := nI11
  have lb11 : ∀ a : ℝ, |∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b| ≤ 1000 := nJ11
  have li11 : IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := no11
  have ev11 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b)
      = ∫ a in (((1)/(3)):ℝ)..(((1)/(2)):ℝ), (1/a)*(1/((((1)/(4)):ℝ) + ((0))*a) - 1/((((1)/(2)):ℝ) + (((-1)/(2)))*a)) := ne11
  have zZ11 : ∀ a b : ℝ, ¬((((1)/(3)):ℝ) < a ∧ a ≤ (((1)/(2)):ℝ) ∧ ((((1)/(4)):ℝ) + ((0))*a) < b ∧ b ≤ ((((1)/(2)):ℝ) + (((-1)/(2)))*a)) → G11 a b = 0 := fun a b h => if_neg h
  have vV11 : ∀ a b : ℝ, ((((1)/(3)):ℝ) < a ∧ a ≤ (((1)/(2)):ℝ) ∧ ((((1)/(4)):ℝ) + ((0))*a) < b ∧ b ≤ ((((1)/(2)):ℝ) + (((-1)/(2)))*a)) → G11 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P11 : (5844487/25000000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b := by
    rw [ev11]
    linarith [Q7b_lower]
  have hSle : ∀ a b : ℝ, (G1 a b + (G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + G11 a b)))))))))) ≤ (if C a b then (1:ℝ)/(a*b^2) else 0) := by
    intro a b
    by_cases h1 : ((((2273)/(10000)):ℝ) < a ∧ a ≤ (((43)/(176)):ℝ) ∧ ((((17)/(56)):ℝ) + (((-4)/(7)))*a) < b ∧ b ≤ ((((17)/(88)):ℝ) + ((0))*a))
    · rw [vV1 a b h1,
      zZ2 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ3 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ4 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ5 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ6 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ7 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ8 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ9 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ10 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      if_pos (hinc1 a b (le_of_lt h1.1) h1.2.1 (le_of_lt h1.2.2.1) h1.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h2 : ((((43)/(176)):ℝ) < a ∧ a ≤ (((5)/(16)):ℝ) ∧ ((((17)/(56)):ℝ) + (((-4)/(7)))*a) < b ∧ b ≤ ((((7)/(16)):ℝ) + ((-1))*a))
    · rw [vV2 a b h2,
      zZ1 a b h1,
      zZ3 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ4 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ5 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ6 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ7 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ8 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ9 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ10 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      if_pos (hinc2 a b (le_of_lt h2.1) h2.2.1 (le_of_lt h2.2.2.1) h2.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h3 : ((((1977)/(8000)):ℝ) < a ∧ a ≤ (((11931)/(40000)):ℝ) ∧ ((((17)/(40)):ℝ) + (((-4)/(5)))*a) < b ∧ b ≤ ((((2273)/(10000)):ℝ) + ((0))*a))
    · rw [vV3 a b h3,
      zZ1 a b h1,
      zZ2 a b h2,
      zZ4 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ5 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ6 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ7 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ8 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ9 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ10 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      if_pos (hinc3 a b (le_of_lt h3.1) h3.2.1 (le_of_lt h3.2.2.1) h3.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h4 : ((((11931)/(40000)):ℝ) < a ∧ a ≤ (((3)/(8)):ℝ) ∧ ((((17)/(40)):ℝ) + (((-4)/(5)))*a) < b ∧ b ≤ ((((5)/(8)):ℝ) + (((-4)/(3)))*a))
    · rw [vV4 a b h4,
      zZ1 a b h1,
      zZ2 a b h2,
      zZ3 a b h3,
      zZ5 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ6 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ7 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ8 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ9 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ10 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      if_pos (hinc4 a b (le_of_lt h4.1) h4.2.1 (le_of_lt h4.2.2.1) h4.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h5 : ((((14431)/(40000)):ℝ) < a ∧ a ≤ (((16477)/(40000)):ℝ) ∧ ((((17)/(24)):ℝ) + (((-4)/(3)))*a) < b ∧ b ≤ ((((2273)/(10000)):ℝ) + ((0))*a))
    · rw [vV5 a b h5,
      zZ1 a b h1,
      zZ2 a b h2,
      zZ3 a b h3,
      zZ4 a b h4,
      zZ6 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ7 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ8 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ9 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ10 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      if_pos (hinc5 a b (le_of_lt h5.1) h5.2.1 (le_of_lt h5.2.2.1) h5.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h6 : ((((16477)/(40000)):ℝ) < a ∧ a ≤ (((7)/(16)):ℝ) ∧ ((((17)/(24)):ℝ) + (((-4)/(3)))*a) < b ∧ b ≤ ((((15)/(8)):ℝ) + ((-4))*a))
    · rw [vV6 a b h6,
      zZ1 a b h1,
      zZ2 a b h2,
      zZ3 a b h3,
      zZ4 a b h4,
      zZ5 a b h5,
      zZ7 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ8 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ9 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ10 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      if_pos (hinc6 a b (le_of_lt h6.1) h6.2.1 (le_of_lt h6.2.2.1) h6.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h7 : ((((18977)/(40000)):ℝ) < a ∧ a ≤ (((1)/(2)):ℝ) ∧ ((((17)/(8)):ℝ) + ((-4))*a) < b ∧ b ≤ ((((2273)/(10000)):ℝ) + ((0))*a))
    · rw [vV7 a b h7,
      zZ1 a b h1,
      zZ2 a b h2,
      zZ3 a b h3,
      zZ4 a b h4,
      zZ5 a b h5,
      zZ6 a b h6,
      zZ8 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ9 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ10 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      if_pos (hinc7 a b (le_of_lt h7.1) h7.2.1 (le_of_lt h7.2.2.1) h7.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h8 : ((((2273)/(10000)):ℝ) < a ∧ a ≤ (((1)/(4)):ℝ) ∧ ((((2273)/(10000)):ℝ) + ((0))*a) < b ∧ b ≤ (((0):ℝ) + ((1))*a))
    · rw [vV8 a b h8,
      zZ1 a b h1,
      zZ2 a b h2,
      zZ3 a b h3,
      zZ4 a b h4,
      zZ5 a b h5,
      zZ6 a b h6,
      zZ7 a b h7,
      zZ9 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ10 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      if_pos (hinc8 a b (le_of_lt h8.1) h8.2.1 (le_of_lt h8.2.2.1) h8.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h9 : ((((1)/(4)):ℝ) < a ∧ a ≤ (((1)/(2)):ℝ) ∧ ((((2273)/(10000)):ℝ) + ((0))*a) < b ∧ b ≤ ((((1)/(4)):ℝ) + ((0))*a))
    · rw [vV9 a b h9,
      zZ1 a b h1,
      zZ2 a b h2,
      zZ3 a b h3,
      zZ4 a b h4,
      zZ5 a b h5,
      zZ6 a b h6,
      zZ7 a b h7,
      zZ8 a b h8,
      zZ10 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      if_pos (hinc9 a b (le_of_lt h9.1) h9.2.1 (le_of_lt h9.2.2.1) h9.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h10 : ((((1)/(4)):ℝ) < a ∧ a ≤ (((1)/(3)):ℝ) ∧ ((((1)/(4)):ℝ) + ((0))*a) < b ∧ b ≤ (((0):ℝ) + ((1))*a))
    · rw [vV10 a b h10,
      zZ1 a b h1,
      zZ2 a b h2,
      zZ3 a b h3,
      zZ4 a b h4,
      zZ5 a b h5,
      zZ6 a b h6,
      zZ7 a b h7,
      zZ8 a b h8,
      zZ9 a b h9,
      zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith),
      if_pos (hinc10 a b (le_of_lt h10.1) h10.2.1 (le_of_lt h10.2.2.1) h10.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h11 : ((((1)/(3)):ℝ) < a ∧ a ≤ (((1)/(2)):ℝ) ∧ ((((1)/(4)):ℝ) + ((0))*a) < b ∧ b ≤ ((((1)/(2)):ℝ) + (((-1)/(2)))*a))
    · rw [vV11 a b h11,
      zZ1 a b h1,
      zZ2 a b h2,
      zZ3 a b h3,
      zZ4 a b h4,
      zZ5 a b h5,
      zZ6 a b h6,
      zZ7 a b h7,
      zZ8 a b h8,
      zZ9 a b h9,
      zZ10 a b h10,
      if_pos (hinc11 a b (le_of_lt h11.1) h11.2.1 (le_of_lt h11.2.2.1) h11.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    rw [zZ1 a b h1, zZ2 a b h2, zZ3 a b h3, zZ4 a b h4, zZ5 a b h5, zZ6 a b h6, zZ7 a b h7, zZ8 a b h8, zZ9 a b h9, zZ10 a b h10, zZ11 a b h11]
    by_cases hC2 : C a b
    · rw [if_pos hC2]
      simp only [zero_add, add_zero]
      exact le_of_lt (one_div_pos.mpr (by nlinarith [hCa a b hC2, hCb a b hC2]))
    · rw [if_neg hC2]
      simp only [zero_add, add_zero, le_refl]
  have hSb : ∀ a b : ℝ, |(G1 a b + (G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + G11 a b))))))))))| ≤ 11000 := by
    intro a b
    have h0 : 0 ≤ (G1 a b + (G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + G11 a b)))))))))) := by linarith [mN1 a b, mN2 a b, mN3 a b, mN4 a b, mN5 a b, mN6 a b, mN7 a b, mN8 a b, mN9 a b, mN10 a b, mN11 a b]
    rw [abs_of_nonneg h0]
    have hF := abs_le.mp (hFb a b)
    have hS := hSle a b
    linarith
  have hSmeas : Measurable (fun p : ℝ × ℝ => (G1 p.1 p.2 + (G2 p.1 p.2 + (G3 p.1 p.2 + (G4 p.1 p.2 + (G5 p.1 p.2 + (G6 p.1 p.2 + (G7 p.1 p.2 + (G8 p.1 p.2 + (G9 p.1 p.2 + (G10 p.1 p.2 + G11 p.1 p.2))))))))))) :=
    (mb1.add (mb2.add (mb3.add (mb4.add (mb5.add (mb6.add (mb7.add (mb8.add (mb9.add (mb10.add mb11))))))))))
  -- additivity of the iterated integral over the eleven pieces
  have sfb11 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => G11 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := mI11
  have sfb10 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => ((G10 a b + G11 a b))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI10 a).add (sfb11 a)
  have sfb9 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => ((G9 a b + (G10 a b + G11 a b)))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI9 a).add (sfb10 a)
  have sfb8 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => ((G8 a b + (G9 a b + (G10 a b + G11 a b))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI8 a).add (sfb9 a)
  have sfb7 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => ((G7 a b + (G8 a b + (G9 a b + (G10 a b + G11 a b)))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI7 a).add (sfb8 a)
  have sfb6 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => ((G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + G11 a b))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI6 a).add (sfb7 a)
  have sfb5 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => ((G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + G11 a b)))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI5 a).add (sfb6 a)
  have sfb4 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => ((G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + G11 a b))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI4 a).add (sfb5 a)
  have sfb3 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => ((G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + G11 a b)))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI3 a).add (sfb4 a)
  have sfb2 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => ((G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + G11 a b))))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI2 a).add (sfb3 a)
  have sfb1 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => ((G1 a b + (G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + G11 a b)))))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI1 a).add (sfb2 a)
  have hinner : ∀ a : ℝ, (∫ b in (1/10:ℝ)..(1/2:ℝ), (G1 a b + (G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + G11 a b))))))))))) =
      ((∫ b in (1/10:ℝ)..(1/2:ℝ), G1 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + (∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b))))))))))) := by
    intro a
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add] <;>
      first
        | simpa only [] using mI1 a
        | simpa only [] using mI2 a
        | simpa only [] using mI3 a
        | simpa only [] using mI4 a
        | simpa only [] using mI5 a
        | simpa only [] using mI6 a
        | simpa only [] using mI7 a
        | simpa only [] using mI8 a
        | simpa only [] using mI9 a
        | simpa only [] using mI10 a
        | simpa only [] using mI11 a
        | simpa only [] using sfb2 a
        | simpa only [] using sfb3 a
        | simpa only [] using sfb4 a
        | simpa only [] using sfb5 a
        | simpa only [] using sfb6 a
        | simpa only [] using sfb7 a
        | simpa only [] using sfb8 a
        | simpa only [] using sfb9 a
        | simpa only [] using sfb10 a
        | simpa only [] using sfb11 a

  have sfa11 : IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := li11
  have sfa10 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + (∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li10).add (sfa11)
  have sfa9 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + (∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b)))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li9).add (sfa10)
  have sfa8 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + (∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li8).add (sfa9)
  have sfa7 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + (∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b)))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li7).add (sfa8)
  have sfa6 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + (∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li6).add (sfa7)
  have sfa5 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + (∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b)))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li5).add (sfa6)
  have sfa4 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + (∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li4).add (sfa5)
  have sfa3 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + (∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b)))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li3).add (sfa4)
  have sfa2 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + (∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b))))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li2).add (sfa3)
  have sfa1 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G1 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + (∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b)))))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li1).add (sfa2)

  have hEq : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), (G1 a b + (G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + G11 a b))))))))))) = ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G1 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b))))))))))) := by
    have hstep : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), (G1 a b + (G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + G11 a b))))))))))) =
        (∫ a in (1/10:ℝ)..(1/2:ℝ), ((∫ b in (1/10:ℝ)..(1/2:ℝ), G1 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + (∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b)))))))))))) := by
      simp only [hinner]
    rw [hstep]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add] <;>
      first
        | simpa only [] using li1
        | simpa only [] using li2
        | simpa only [] using li3
        | simpa only [] using li4
        | simpa only [] using li5
        | simpa only [] using li6
        | simpa only [] using li7
        | simpa only [] using li8
        | simpa only [] using li9
        | simpa only [] using li10
        | simpa only [] using li11
        | simpa only [] using sfa2
        | simpa only [] using sfa3
        | simpa only [] using sfa4
        | simpa only [] using sfa5
        | simpa only [] using sfa6
        | simpa only [] using sfa7
        | simpa only [] using sfa8
        | simpa only [] using sfa9
        | simpa only [] using sfa10
        | simpa only [] using sfa11

  -- ---- the monotonicity step and the final comparison ----
  have hFb11 : ∀ a b : ℝ, |(if C a b then (1:ℝ)/(a*b^2) else 0)| ≤ 11000 := fun a b => le_trans (hFb a b) (by norm_num)
  have hmono := slope_two_mono (fun a b : ℝ => (G1 a b + (G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + G11 a b))))))))))) (fun a b : ℝ => (if C a b then (1:ℝ)/(a*b^2) else 0))
    hSmeas hFmeas (M := 11000) hSb hFb11 hSle (lo := (1/10:ℝ)) (hi := (1/2:ℝ)) (by norm_num)
  have hsum : (13/10:ℝ) ≤ ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G1 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b))))))))))) := by
    linarith [P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11]
  have hmain : (13/10:ℝ) ≤ (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), (if C a b then (1:ℝ)/(a*b^2) else 0)) := by
    calc (13/10:ℝ) ≤ ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G1 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b))))))))))) := hsum
      _ = (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), (G1 a b + (G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + G11 a b))))))))))) := hEq.symm
      _ ≤ (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), (if C a b then (1:ℝ)/(a*b^2) else 0)) := hmono
  simpa only [hC] using hmain

/-- LEAF: the pointwise bound. Each of the five pieces has `1/8 ≤ b ≤ a`, so `a b^2 ≥ 1/512` there
and its integrand is at most `512`; off the union the integrand is zero. Hence `1000` bounds it
everywhere. -/
theorem leaf_band_union_integrand_bound (a b : ℝ) :
    |(if ((((((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧ a + b ≤ 7/16 ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 5*b ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 4*a + b ≤ 15/8)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)| ≤ 1000 := by
  split_ifs with h
  · have hb : (1/8 : ℝ) ≤ b := by
      rcases h with (((h | h) | h) | h) | h
      · obtain ⟨h1, -⟩ := h; linarith
      · obtain ⟨h1, -⟩ := h; exact h1
      · obtain ⟨h1, -⟩ := h; exact h1
      · obtain ⟨h1, -⟩ := h; exact h1
      · obtain ⟨h1, -⟩ := h; exact h1
    have hba : b ≤ a := by
      rcases h with (((h | h) | h) | h) | h
      · obtain ⟨-, h2, -⟩ := h; exact h2
      · obtain ⟨-, -, h2, -⟩ := h; exact h2
      · obtain ⟨-, -, h2, -⟩ := h; exact h2
      · obtain ⟨-, -, h2, -⟩ := h; exact h2
      · obtain ⟨-, -, h2, -⟩ := h; exact h2
    have ha : (1/8 : ℝ) ≤ a := le_trans hb hba
    have hb0 : (0:ℝ) < b := by linarith
    have ha0 : (0:ℝ) < a := by linarith
    have hsq : (1/64 : ℝ) ≤ b^2 := by nlinarith
    have h512 : (1/512 : ℝ) ≤ a*b^2 := by
      have := mul_le_mul ha hsq (by norm_num : (0:ℝ) ≤ 1/64) (by linarith : (0:ℝ) ≤ a)
      linarith
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(a*b^2))]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < a*b^2)]
    nlinarith
  · simp

/-- The quadrature of the target, assembled from the geometric step, the computation over the five
convex pieces and the pointwise bound: the union of the five pieces lies in the target region and
`1 / (a b^2) ≥ 0` there, so the two integrands are pointwise ordered, both are bounded by `1000`,
and `slope_two_mono` carries that order to the twofold iterated interval integrals. -/
theorem leaf_three_band_quadrature_split {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    13/10 ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0 := by
  have hS : MeasurableSet {p : ℝ × ℝ | ((((((2273/10000 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1) ∨ (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1 ∧ 4*p.1 + 3*p.2 ≤ 15/8 ∧ 17/8 ≤ 4*p.1 + 7*p.2 ∧ p.1 + p.2 ≤ 7/16 ∧ 2273/10000 ≤ p.1)) ∨ (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1 ∧ 4*p.1 + 3*p.2 ≤ 15/8 ∧ 17/8 ≤ 4*p.1 + 5*p.2 ∧ 2273/10000 ≤ p.1)) ∨ (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1 ∧ 17/8 ≤ 4*p.1 + 3*p.2 ∧ 4*p.1 + p.2 ≤ 15/8)) ∨ (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1 ∧ 17/8 ≤ 4*p.1 + 3*p.2 ∧ 17/8 ≤ 4*p.1 + p.2)))} := by
    have hle : ∀ f g : ℝ × ℝ → ℝ, Continuous f → Continuous g →
        MeasurableSet {p | f p ≤ g p} := fun f g hf hg => (isClosed_le hf hg).measurableSet
    simp only [Set.ofPred_and, Set.ofPred_or]
    repeat' first
      | apply MeasurableSet.inter
      | apply MeasurableSet.union
      | (apply hle <;> fun_prop)
  have hf : Measurable (fun p : ℝ × ℝ =>
      if ((((((2273/10000 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1) ∨ (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1 ∧ 4*p.1 + 3*p.2 ≤ 15/8 ∧ 17/8 ≤ 4*p.1 + 7*p.2 ∧ p.1 + p.2 ≤ 7/16 ∧ 2273/10000 ≤ p.1)) ∨ (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1 ∧ 4*p.1 + 3*p.2 ≤ 15/8 ∧ 17/8 ≤ 4*p.1 + 5*p.2 ∧ 2273/10000 ≤ p.1)) ∨ (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1 ∧ 17/8 ≤ 4*p.1 + 3*p.2 ∧ 4*p.1 + p.2 ≤ 15/8)) ∨ (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1 ∧ 17/8 ≤ 4*p.1 + 3*p.2 ∧ 17/8 ≤ 4*p.1 + p.2))) then 1/(p.1*p.2^2) else 0) :=
    Measurable.ite hS (by fun_prop) measurable_const
  have hR : MeasurableSet {p : ℝ × ℝ | ((2273/10000 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1) ∨
        (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧
            p.1 + 2*p.2 ≤ 1 ∧ 4*p.1 + 3*p.2 ≤ 15/8 ∧ 17/8 ≤ 4*p.1 + 7*p.2 ∧
            (p.1 + p.2 ≤ 7/16 ∨ 17/8 ≤ 4*p.1 + 5*p.2) ∧
            (2273/10000 ≤ p.1 ∨ p.1 + 1/8 ≤ 2*p.2)) ∨
        (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧
            p.1 + 2*p.2 ≤ 1 ∧ 17/8 ≤ 4*p.1 + 3*p.2 ∧
            (4*p.1 + p.2 ≤ 15/8 ∨ 17/8 ≤ 4*p.1 + p.2)))} := by
    have hle : ∀ f g : ℝ × ℝ → ℝ, Continuous f → Continuous g →
        MeasurableSet {p | f p ≤ g p} := fun f g hf hg => (isClosed_le hf hg).measurableSet
    simp only [Set.ofPred_and, Set.ofPred_or]
    repeat' first
      | apply MeasurableSet.inter
      | apply MeasurableSet.union
      | (apply hle <;> fun_prop)
  have hg : Measurable (fun p : ℝ × ℝ =>
      if ((2273/10000 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1) ∨
        (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧
            p.1 + 2*p.2 ≤ 1 ∧ 4*p.1 + 3*p.2 ≤ 15/8 ∧ 17/8 ≤ 4*p.1 + 7*p.2 ∧
            (p.1 + p.2 ≤ 7/16 ∨ 17/8 ≤ 4*p.1 + 5*p.2) ∧
            (2273/10000 ≤ p.1 ∨ p.1 + 1/8 ≤ 2*p.2)) ∨
        (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧
            p.1 + 2*p.2 ≤ 1 ∧ 17/8 ≤ 4*p.1 + 3*p.2 ∧
            (4*p.1 + p.2 ≤ 15/8 ∨ 17/8 ≤ 4*p.1 + p.2))) then 1/(p.1*p.2^2) else 0) :=
    Measurable.ite hR (by fun_prop) measurable_const
  have hfM : ∀ a b : ℝ, |(if ((((((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧ a + b ≤ 7/16 ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 5*b ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 4*a + b ≤ 15/8)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)| ≤ 1000 :=
    fun a b => leaf_band_union_integrand_bound a b
  have hgM : ∀ a b : ℝ, |(if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)| ≤ 1000 :=
    fun a b => leaf_three_band_bound a b
  have hle' : ∀ a b : ℝ, (if ((((((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧ a + b ≤ 7/16 ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 5*b ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 4*a + b ≤ 15/8)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)
      ≤ (if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0) := by
    intro a b
    by_cases h : ((((((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧ a + b ≤ 7/16 ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 5*b ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 4*a + b ≤ 15/8)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 17/8 ≤ 4*a + b)))
    · rw [if_pos h, if_pos (leaf_band_union_membership a b h)]
    · rw [if_neg h]
      by_cases hR : ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b)))
      · rw [if_pos hR]
        have hb1 : (1/8:ℝ) ≤ b := by
          rcases hR with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
          · linarith
          · exact h1
          · exact h1
        have hba : b ≤ a := by
          rcases hR with ⟨-, h2, -⟩ | ⟨-, -, h2, -⟩ | ⟨-, -, h2, -⟩
          · exact h2
          · exact h2
          · exact h2
        have hb0 : (0:ℝ) < b := by linarith
        have ha0 : (0:ℝ) < a := by linarith
        positivity
      · rw [if_neg hR]
  have hm := slope_two_mono
    (fun a b => if ((((((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧ a + b ≤ 7/16 ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 5*b ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 4*a + b ≤ 15/8)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)
    (fun a b => if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)
    hf hg (M := 1000) hfM hgM hle' (lo := 1/10) (hi := 1/2) (by norm_num)
  have hq := leaf_band_union_quadrature
  linarith


end LeanLab.BHP1997.LowerShortC165
