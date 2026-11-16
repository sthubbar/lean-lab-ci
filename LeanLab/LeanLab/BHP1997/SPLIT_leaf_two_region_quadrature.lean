/-
The E2 band of the section 5 lower density computation: the split of
`leaf_two_region_quadrature` of `DensitySlope517`, the quadrature of `1 / (a b^2)` over E2.

The target leaf asks for `13/10 ≤ ∫∫ 1 / (a b^2)` over E2. This file cuts it into

* three band inclusions, each a completely explicit set of rational linear inequalities and each
  contained in E2 with a margin of at least `2 * 10^-5`, far more than the allowed `ε ≤ 10^-8`:
  `leaf_high_band_membership` (the band `b ≥ 2273/10000`, where no case exclusion bites),
  `leaf_middle_band_membership` (the band below the line `4 a + 3 b = 15/8`) and
  `leaf_notch_band_membership` (the band above the line `4 a + 3 b = 17/8`, which straddles the
  excluded strip `15/8 < 4 a + 3 b < 17/8` by a disjunction);
* one quadrature, `leaf_three_band_quadrature`, of `1 / (a b^2)` over the union of the three
  bands: a rational function over an explicit polygon, with no `ε` and no case split of E2 in it
  (a floating point quadrature gives about 1.4963 there, and 1.4975 over E2 itself);
* one bound, `leaf_three_band_bound`, which is what the two fold monotonicity lemma needs.

The assembly `leaf_two_region_quadrature_split` only compares the two integrands pointwise, using
the three inclusions and the nonnegativity of `1 / (a b^2)` on E2.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DensitySlope517

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d Decomp514a
open scoped BigOperators

set_option maxHeartbeats 400000

/-- The union of the three bands is a measurable subset of the plane: a boolean combination of
closed half planes. -/
private lemma three_band_region_measurable :
    MeasurableSet {p : ℝ × ℝ | ((2273/10000 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1) ∨
        (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧
            p.1 + 2*p.2 ≤ 1 ∧ 4*p.1 + 3*p.2 ≤ 15/8 ∧ 17/8 ≤ 4*p.1 + 7*p.2 ∧
            (p.1 + p.2 ≤ 7/16 ∨ 17/8 ≤ 4*p.1 + 5*p.2) ∧
            (2273/10000 ≤ p.1 ∨ p.1 + 1/8 ≤ 2*p.2)) ∨
        (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧
            p.1 + 2*p.2 ≤ 1 ∧ 17/8 ≤ 4*p.1 + 3*p.2 ∧
            (4*p.1 + p.2 ≤ 15/8 ∨ 17/8 ≤ 4*p.1 + p.2))) } := by
  have hle : ∀ f g : ℝ × ℝ → ℝ, Continuous f → Continuous g →
      MeasurableSet {p | f p ≤ g p} := fun f g hf hg => (isClosed_le hf hg).measurableSet
  simp only [Set.ofPred_and, Set.ofPred_or]
  repeat' first
    | apply MeasurableSet.inter
    | apply MeasurableSet.union
    | (apply hle <;> fun_prop)

/-- LEAF: first band inclusion. Every point with `b ≥ 2273/10000`, `b ≤ a ≤ 1/2` and
`9/16 ≤ a + 2 b ≤ 1` is in E2: the square `b ≤ a` already gives `4 a + 7 b ≥ 11 b ≥ 25003/10000`,
so the small `b` cut of the second alternative is killed, and `b ≥ 2273/10000 > 2272072/10^7`
kills both the third alternative and the last conjunct of the pair region. Only the strip cut
`a + 2 b ≥ 9/16 > 562492666/10^9` is used. -/
theorem leaf_high_band_membership {ε a b : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hb : 2273/10000 ≤ b) (hba : b ≤ a) (ha : a ≤ 1/2)
    (hs1 : 9/16 ≤ a + 2*b) (hs2 : a + 2*b ≤ 1) :
    lowerTwoDiscarded ε a b := by
  unfold lowerTwoDiscarded upperPairRegion
  refine ⟨by linarith, hba, ha, hs2, ?_⟩
  rintro (hA | hB | hC | hD)
  · linarith
  · linarith
  · linarith
  · obtain ⟨-, -, -, hbD, -⟩ := hD
    linarith

/-- LEAF: second band inclusion, the part of E2 below the strip `4 a + 3 b = 2`. Here
`4 a + 3 b ≤ 15/8` makes both `|4 a + 3 b - 2|` and `|4 a + b - 2|` at least `1/8`, which kills
the pair region, the strip cut `a + 2 b ≥ 9/16` kills the wide band, `17/8 ≤ 4 a + 7 b` kills the
first alternative and `a + b ≤ 7/16` or `17/8 ≤ 4 a + 5 b` kills the second; the last disjunct
keeps the point clear of the first alternative of the pair region. -/
theorem leaf_middle_band_membership {ε a b : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hb1 : 1/8 ≤ b) (hb2 : b ≤ 2273/10000) (hba : b ≤ a) (ha : a ≤ 1/2)
    (hs1 : 9/16 ≤ a + 2*b) (hs2 : a + 2*b ≤ 1)
    (hcut : 4*a + 3*b ≤ 15/8) (h7 : 17/8 ≤ 4*a + 7*b)
    (h5 : a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b)
    (hclear : 2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b) :
    lowerTwoDiscarded ε a b := by
  unfold lowerTwoDiscarded upperPairRegion
  refine ⟨by linarith, hba, ha, hs2, ?_⟩
  rintro (hA | hB | hC | hD)
  · linarith
  · linarith
  · rcases h5 with h5 | h5 <;> linarith
  · obtain ⟨-, -, -, -, hrest⟩ := hD
    rcases hrest with ⟨h1, h2⟩ | h3 | h4
    · rcases hclear with hcl | hcl
      · linarith
      · linarith
    · rw [abs_le] at h3
      linarith
    · rw [abs_le] at h4
      linarith

/-- LEAF: third band inclusion, the part of E2 above the strip `4 a + 3 b = 2`. Here
`17/8 ≤ 4 a + 3 b` kills the first and second alternatives at once, and forces
`a ≥ 3608/10000 > 2272072/10^7`, so the first alternative of the pair region fails; the
disjunction `4 a + b ≤ 15/8 ∨ 17/8 ≤ 4 a + b` is exactly the choice of the side of the other
excluded strip `4 a + b = 2`. -/
theorem leaf_notch_band_membership {ε a b : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hb1 : 1/8 ≤ b) (hb2 : b ≤ 2273/10000) (hba : b ≤ a) (ha : a ≤ 1/2)
    (hs1 : 9/16 ≤ a + 2*b) (hs2 : a + 2*b ≤ 1)
    (h3 : 17/8 ≤ 4*a + 3*b) (h4 : 4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b) :
    lowerTwoDiscarded ε a b := by
  unfold lowerTwoDiscarded upperPairRegion
  refine ⟨by linarith, hba, ha, hs2, ?_⟩
  rintro (hA | hB | hC | hD)
  · linarith
  · linarith
  · linarith
  · obtain ⟨-, -, -, -, hrest⟩ := hD
    rcases hrest with ⟨h1, h2⟩ | h5 | h5
    · linarith
    · rw [abs_le] at h5
      linarith
    · rcases h4 with h4 | h4 <;> rw [abs_le] at h5 <;> linarith

/-- `1 - x⁻¹ ≤ log x` for `x > 0`, the weak form of concavity used below. -/
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
private lemma Q1a1_lower :
    ((50176/30343555) + (404608/38573255) + (5055232/265668231) : ℝ)
      ≤ ∫ a in ((17/88):ℝ)..((9/40):ℝ), (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((17/88):ℝ) + (0)*a)) := by
  have hs1 : ((50176/30343555) : ℝ) ≤ ∫ a in ((17/88):ℝ)..((269/1320)), (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((17/88):ℝ) + (0)*a)) := by
    have key := slice_le_B (A1 := ((17/88):ℝ)) (A2 := ((269/1320):ℝ)) (c := ((17/56):ℝ)) (e := (-4/7)) (f := ((17/88):ℝ)) (g := 0) (lb1 := ((2008/62997):ℝ)) (lb2 := ((-14/255):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : ((((17/88):ℝ)+(0)*((269/1320)))/(((17/88):ℝ)+(0)*((17/88))))/((((17/56):ℝ)+((-4/7))*((269/1320)))/(((17/56):ℝ)+((-4/7))*((17/88)))) = ((255/247):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((255/247):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((17/88):ℝ)+(0)*((269/1320)))/(((17/88):ℝ)+(0)*((17/88))))/(((269/1320):ℝ)/((17/88))) = ((255/269):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((255/269):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/56):ℝ))*((2008/62997):ℝ) + (1/((17/88):ℝ) - 1/((17/56):ℝ))*((-14/255):ℝ) = ((50176/30343555):ℝ) := by norm_num
    linarith [key, heq]
  have hs2 : ((404608/38573255) : ℝ) ≤ ∫ a in ((269/1320):ℝ)..((283/1320)), (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((17/88):ℝ) + (0)*a)) := by
    have key := slice_le_B (A1 := ((269/1320):ℝ)) (A2 := ((283/1320):ℝ)) (c := ((17/56):ℝ)) (e := (-4/7)) (f := ((17/88):ℝ)) (g := 0) (lb1 := ((1944/59045):ℝ)) (lb2 := ((-14/269):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : ((((17/88):ℝ)+(0)*((283/1320)))/(((17/88):ℝ)+(0)*((269/1320))))/((((17/56):ℝ)+((-4/7))*((283/1320)))/(((17/56):ℝ)+((-4/7))*((269/1320)))) = ((247/239):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((247/239):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((17/88):ℝ)+(0)*((283/1320)))/(((17/88):ℝ)+(0)*((269/1320))))/(((283/1320):ℝ)/((269/1320))) = ((269/283):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((269/283):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/56):ℝ))*((1944/59045):ℝ) + (1/((17/88):ℝ) - 1/((17/56):ℝ))*((-14/269):ℝ) = ((404608/38573255):ℝ) := by norm_num
    linarith [key, heq]
  have hs3 : ((5055232/265668231) : ℝ) ≤ ∫ a in ((283/1320):ℝ)..((9/40)), (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((17/88):ℝ) + (0)*a)) := by
    have key := slice_le_B (A1 := ((283/1320):ℝ)) (A2 := ((9/40):ℝ)) (c := ((17/56):ℝ)) (e := (-4/7)) (f := ((17/88):ℝ)) (g := 0) (lb1 := ((1880/55221):ℝ)) (lb2 := ((-14/283):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : ((((17/88):ℝ)+(0)*((9/40)))/(((17/88):ℝ)+(0)*((283/1320))))/((((17/56):ℝ)+((-4/7))*((9/40)))/(((17/56):ℝ)+((-4/7))*((283/1320)))) = ((239/231):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((239/231):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((17/88):ℝ)+(0)*((9/40)))/(((17/88):ℝ)+(0)*((283/1320))))/(((9/40):ℝ)/((283/1320))) = ((283/297):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((283/297):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/56):ℝ))*((1880/55221):ℝ) + (1/((17/88):ℝ) - 1/((17/56):ℝ))*((-14/283):ℝ) = ((5055232/265668231):ℝ) := by norm_num
    linarith [key, heq]
  have hi1 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((17/88):ℝ) + (0)*a))) MeasureTheory.volume ((17/88):ℝ) ((269/1320):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi2 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((17/88):ℝ) + (0)*a))) MeasureTheory.volume ((269/1320):ℝ) ((283/1320):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi3 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((17/88):ℝ) + (0)*a))) MeasureTheory.volume ((283/1320):ℝ) ((9/40):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi13 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((17/88):ℝ) + (0)*a))) MeasureTheory.volume ((17/88):ℝ) ((283/1320):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hs : ((50176/30343555) + (404608/38573255) + (5055232/265668231) : ℝ)
      ≤ ∫ a in ((17/88):ℝ)..((9/40):ℝ), (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((17/88):ℝ) + (0)*a)) := by
    have hA := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hB := intervalIntegral.integral_add_adjacent_intervals hi13 hi3
    linarith
  exact hs

/-- Piece `Q1a2` of the quadrature, in three `a`-slices. -/
private lemma Q1a2a_lower :
    ((3838173215222/2137313692817625) + (6387336391712762056/3655193602209274804921) + (349768432925397028/205787986266743240171) : ℝ)
      ≤ ∫ a in ((9/40):ℝ)..((2273/10000):ℝ), (1/a)*(1/(((1/16):ℝ) + ((1/2))*a) - 1/(((17/88):ℝ) + (0)*a)) := by
  have hs1 : ((3838173215222/2137313692817625) : ℝ) ≤ ∫ a in ((9/40):ℝ)..((6773/30000)), (1/a)*(1/(((1/16):ℝ) + ((1/2))*a) - 1/(((17/88):ℝ) + (0)*a)) := by
    have key := slice_le_A (A1 := ((9/40):ℝ)) (A2 := ((6773/30000):ℝ)) (c := ((1/16):ℝ)) (e := (1/2)) (f := ((17/88):ℝ)) (g := 0) (lb1 := ((174366680/143684954139):ℝ)) (lb2 := ((-23/10500):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : (((6773/30000):ℝ)/((9/40)))/((((1/16):ℝ)+((1/2))*((6773/30000)))/(((1/16):ℝ)+((1/2))*((9/40)))) = ((94822/94707):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((94822/94707):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((17/88):ℝ)+(0)*((6773/30000)))/(((17/88):ℝ)+(0)*((9/40))))/((((1/16):ℝ)+((1/2))*((6773/30000)))/(((1/16):ℝ)+((1/2))*((9/40)))) = ((10500/10523):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((10500/10523):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((1/16):ℝ) - 1/((17/88):ℝ))*((174366680/143684954139):ℝ) + (1/((17/88):ℝ))*((-23/10500):ℝ) = ((3838173215222/2137313692817625):ℝ) := by norm_num
    linarith [key, heq]
  have hs2 : ((6387336391712762056/3655193602209274804921) : ℝ) ≤ ∫ a in ((6773/30000):ℝ)..((1699/7500)), (1/a)*(1/(((1/16):ℝ) + ((1/2))*a) - 1/(((17/88):ℝ) + (0)*a)) := by
    have key := slice_le_A (A1 := ((6773/30000):ℝ)) (A2 := ((1699/7500):ℝ)) (c := ((1/16):ℝ)) (e := (1/2)) (f := ((17/88):ℝ)) (g := 0) (lb1 := ((24657558135000/20432518137912331):ℝ)) (lb2 := ((-23/10523):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : (((1699/7500):ℝ)/((6773/30000)))/((((1/16):ℝ)+((1/2))*((1699/7500)))/(((1/16):ℝ)+((1/2))*((6773/30000)))) = ((35757154/35714029):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((35757154/35714029):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((17/88):ℝ)+(0)*((1699/7500)))/(((17/88):ℝ)+(0)*((6773/30000))))/((((1/16):ℝ)+((1/2))*((1699/7500)))/(((1/16):ℝ)+((1/2))*((6773/30000)))) = ((10523/10546):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((10523/10546):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((1/16):ℝ) - 1/((17/88):ℝ))*((24657558135000/20432518137912331):ℝ) + (1/((17/88):ℝ))*((-23/10523):ℝ) = ((6387336391712762056/3655193602209274804921):ℝ) := by norm_num
    linarith [key, heq]
  have hs3 : ((349768432925397028/205787986266743240171) : ℝ) ≤ ∫ a in ((1699/7500):ℝ)..((2273/10000)), (1/a)*(1/(((1/16):ℝ) + ((1/2))*a) - 1/(((17/88):ℝ) + (0)*a)) := by
    have key := slice_le_A (A1 := ((1699/7500):ℝ)) (A2 := ((2273/10000):ℝ)) (c := ((1/16):ℝ)) (e := (1/2)) (f := ((17/88):ℝ)) (g := 0) (lb1 := ((2755018545000/2295690434809331):ℝ)) (lb2 := ((-23/10546):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : (((2273/10000):ℝ)/((1699/7500)))/((((1/16):ℝ)+((1/2))*((2273/10000)))/(((1/16):ℝ)+((1/2))*((1699/7500)))) = ((11985529/11971154):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((11985529/11971154):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((17/88):ℝ)+(0)*((2273/10000)))/(((17/88):ℝ)+(0)*((1699/7500))))/((((1/16):ℝ)+((1/2))*((2273/10000)))/(((1/16):ℝ)+((1/2))*((1699/7500)))) = ((10546/10569):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((10546/10569):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((1/16):ℝ) - 1/((17/88):ℝ))*((2755018545000/2295690434809331):ℝ) + (1/((17/88):ℝ))*((-23/10546):ℝ) = ((349768432925397028/205787986266743240171):ℝ) := by norm_num
    linarith [key, heq]
  have hi1 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((1/16):ℝ) + ((1/2))*a) - 1/(((17/88):ℝ) + (0)*a))) MeasureTheory.volume ((9/40):ℝ) ((6773/30000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi2 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((1/16):ℝ) + ((1/2))*a) - 1/(((17/88):ℝ) + (0)*a))) MeasureTheory.volume ((6773/30000):ℝ) ((1699/7500):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi3 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((1/16):ℝ) + ((1/2))*a) - 1/(((17/88):ℝ) + (0)*a))) MeasureTheory.volume ((1699/7500):ℝ) ((2273/10000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi13 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((1/16):ℝ) + ((1/2))*a) - 1/(((17/88):ℝ) + (0)*a))) MeasureTheory.volume ((9/40):ℝ) ((1699/7500):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hs : ((3838173215222/2137313692817625) + (6387336391712762056/3655193602209274804921) + (349768432925397028/205787986266743240171) : ℝ)
      ≤ ∫ a in ((9/40):ℝ)..((2273/10000):ℝ), (1/a)*(1/(((1/16):ℝ) + ((1/2))*a) - 1/(((17/88):ℝ) + (0)*a)) := by
    have hA := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hB := intervalIntegral.integral_add_adjacent_intervals hi13 hi3
    linarith
  exact hs

private lemma Q1a2b_lower :
    ((4018789322496/266464634694533) + (32055843485952/1840446963121235) + (35809110395136/1813556639676419) : ℝ)
      ≤ ∫ a in ((2273/10000):ℝ)..((43/176):ℝ), (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((17/88):ℝ) + (0)*a)) := by
  have hs1 : ((4018789322496/266464634694533) : ℝ) ≤ ∫ a in ((2273/10000):ℝ)..((25627/110000)), (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((17/88):ℝ) + (0)*a)) := by
    have key := slice_le_B (A1 := ((2273/10000):ℝ)) (A2 := ((25627/110000):ℝ)) (c := ((17/56):ℝ)) (e := (-4/7)) (f := ((17/88):ℝ)) (g := 0) (lb1 := ((82673760/4388302681):ℝ)) (lb2 := ((-624/25003):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : ((((17/88):ℝ)+(0)*((25627/110000)))/(((17/88):ℝ)+(0)*((2273/10000))))/((((17/56):ℝ)+((-4/7))*((25627/110000)))/(((17/56):ℝ)+((-4/7))*((2273/10000)))) = ((66869/65621):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((66869/65621):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((17/88):ℝ)+(0)*((25627/110000)))/(((17/88):ℝ)+(0)*((2273/10000))))/(((25627/110000):ℝ)/((2273/10000))) = ((25003/25627):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((25003/25627):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/56):ℝ))*((82673760/4388302681):ℝ) + (1/((17/88):ℝ) - 1/((17/56):ℝ))*((-624/25003):ℝ) = ((4018789322496/266464634694533):ℝ) := by norm_num
    linarith [key, heq]
  have hs2 : ((32055843485952/1840446963121235) : ℝ) ≤ ∫ a in ((25627/110000):ℝ)..((26251/110000)), (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((17/88):ℝ) + (0)*a)) := by
    have key := slice_le_B (A1 := ((25627/110000):ℝ)) (A2 := ((26251/110000):ℝ)) (c := ((17/56):ℝ)) (e := (-4/7)) (f := ((17/88):ℝ)) (g := 0) (lb1 := ((81116256/4224512665):ℝ)) (lb2 := ((-624/25627):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : ((((17/88):ℝ)+(0)*((26251/110000)))/(((17/88):ℝ)+(0)*((25627/110000))))/((((17/56):ℝ)+((-4/7))*((26251/110000)))/(((17/56):ℝ)+((-4/7))*((25627/110000)))) = ((65621/64373):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((65621/64373):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((17/88):ℝ)+(0)*((26251/110000)))/(((17/88):ℝ)+(0)*((25627/110000))))/(((26251/110000):ℝ)/((25627/110000))) = ((25627/26251):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((25627/26251):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/56):ℝ))*((81116256/4224512665):ℝ) + (1/((17/88):ℝ) - 1/((17/56):ℝ))*((-624/25627):ℝ) = ((32055843485952/1840446963121235):ℝ) := by norm_num
    linarith [key, heq]
  have hs3 : ((35809110395136/1813556639676419) : ℝ) ≤ ∫ a in ((26251/110000):ℝ)..((43/176)), (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((17/88):ℝ) + (0)*a)) := by
    have key := slice_le_B (A1 := ((26251/110000):ℝ)) (A2 := ((43/176):ℝ)) (c := ((17/56):ℝ)) (e := (-4/7)) (f := ((17/88):ℝ)) (g := 0) (lb1 := ((79558752/4063837657):ℝ)) (lb2 := ((-624/26251):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : ((((17/88):ℝ)+(0)*((43/176)))/(((17/88):ℝ)+(0)*((26251/110000))))/((((17/56):ℝ)+((-4/7))*((43/176)))/(((17/56):ℝ)+((-4/7))*((26251/110000)))) = ((64373/63125):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((64373/63125):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((17/88):ℝ)+(0)*((43/176)))/(((17/88):ℝ)+(0)*((26251/110000))))/(((43/176):ℝ)/((26251/110000))) = ((26251/26875):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((26251/26875):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/56):ℝ))*((79558752/4063837657):ℝ) + (1/((17/88):ℝ) - 1/((17/56):ℝ))*((-624/26251):ℝ) = ((35809110395136/1813556639676419):ℝ) := by norm_num
    linarith [key, heq]
  have hi1 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((17/88):ℝ) + (0)*a))) MeasureTheory.volume ((2273/10000):ℝ) ((25627/110000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi2 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((17/88):ℝ) + (0)*a))) MeasureTheory.volume ((25627/110000):ℝ) ((26251/110000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi3 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((17/88):ℝ) + (0)*a))) MeasureTheory.volume ((26251/110000):ℝ) ((43/176):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi13 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((17/88):ℝ) + (0)*a))) MeasureTheory.volume ((2273/10000):ℝ) ((26251/110000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hs : ((4018789322496/266464634694533) + (32055843485952/1840446963121235) + (35809110395136/1813556639676419) : ℝ)
      ≤ ∫ a in ((2273/10000):ℝ)..((43/176):ℝ), (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((17/88):ℝ) + (0)*a)) := by
    have hA := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hB := intervalIntegral.integral_add_adjacent_intervals hi13 hi3
    linarith
  exact hs

/-- Piece `Q1b` of the quadrature, in three `a`-slices. -/
private lemma Q1b_lower :
    ((10294031/140576345) + (906796/18819697) + (94/6545) : ℝ)
      ≤ ∫ a in ((43/176):ℝ)..((5/16):ℝ), (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((7/16):ℝ) + (-1)*a)) := by
  have hs1 : ((10294031/140576345) : ℝ) ≤ ∫ a in ((43/176):ℝ)..((47/176)), (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((7/16):ℝ) + (-1)*a)) := by
    have key := slice_le_A (A1 := ((43/176):ℝ)) (A2 := ((47/176):ℝ)) (c := ((17/56):ℝ)) (e := (-4/7)) (f := ((7/16):ℝ)) (g := -1) (lb1 := ((817751/4772040):ℝ)) (lb2 := ((-22/505):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : (((47/176):ℝ)/((43/176)))/((((17/56):ℝ)+((-4/7))*((47/176)))/(((17/56):ℝ)+((-4/7))*((43/176)))) = ((4747/3999):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((4747/3999):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((7/16):ℝ)+(-1)*((47/176)))/(((7/16):ℝ)+(-1)*((43/176))))/((((17/56):ℝ)+((-4/7))*((47/176)))/(((17/56):ℝ)+((-4/7))*((43/176)))) = ((505/527):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((505/527):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/56):ℝ) - 1/((7/16):ℝ))*((817751/4772040):ℝ) + (1/((7/16):ℝ))*((-22/505):ℝ) = ((10294031/140576345):ℝ) := by norm_num
    linarith [key, heq]
  have hs2 : ((906796/18819697) : ℝ) ≤ ∫ a in ((47/176):ℝ)..((51/176)), (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((7/16):ℝ) + (-1)*a)) := by
    have key := slice_le_A (A1 := ((47/176):ℝ)) (A2 := ((51/176):ℝ)) (c := ((17/56):ℝ)) (e := (-4/7)) (f := ((7/16):ℝ)) (g := -1) (lb1 := ((2827/16482):ℝ)) (lb2 := ((-22/403):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : (((51/176):ℝ)/((47/176)))/((((17/56):ℝ)+((-4/7))*((51/176)))/(((17/56):ℝ)+((-4/7))*((47/176)))) = ((279/235):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((279/235):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((7/16):ℝ)+(-1)*((51/176)))/(((7/16):ℝ)+(-1)*((47/176))))/((((17/56):ℝ)+((-4/7))*((51/176)))/(((17/56):ℝ)+((-4/7))*((47/176)))) = ((403/425):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((403/425):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/56):ℝ) - 1/((7/16):ℝ))*((2827/16482):ℝ) + (1/((7/16):ℝ))*((-22/403):ℝ) = ((906796/18819697):ℝ) := by norm_num
    linarith [key, heq]
  have hs3 : ((94/6545) : ℝ) ≤ ∫ a in ((51/176):ℝ)..((5/16)), (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((7/16):ℝ) + (-1)*a)) := by
    have key := slice_le_A (A1 := ((51/176):ℝ)) (A2 := ((5/16):ℝ)) (c := ((17/56):ℝ)) (e := (-4/7)) (f := ((7/16):ℝ)) (g := -1) (lb1 := ((23/132):ℝ)) (lb2 := ((-6/85):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : (((5/16):ℝ)/((51/176)))/((((17/56):ℝ)+((-4/7))*((5/16)))/(((17/56):ℝ)+((-4/7))*((51/176)))) = ((25/21):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((25/21):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((7/16):ℝ)+(-1)*((5/16)))/(((7/16):ℝ)+(-1)*((51/176))))/((((17/56):ℝ)+((-4/7))*((5/16)))/(((17/56):ℝ)+((-4/7))*((51/176)))) = ((85/91):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((85/91):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/56):ℝ) - 1/((7/16):ℝ))*((23/132):ℝ) + (1/((7/16):ℝ))*((-6/85):ℝ) = ((94/6545):ℝ) := by norm_num
    linarith [key, heq]
  have hi1 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((7/16):ℝ) + (-1)*a))) MeasureTheory.volume ((43/176):ℝ) ((47/176):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi2 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((7/16):ℝ) + (-1)*a))) MeasureTheory.volume ((47/176):ℝ) ((51/176):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi3 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((7/16):ℝ) + (-1)*a))) MeasureTheory.volume ((51/176):ℝ) ((5/16):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi13 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((7/16):ℝ) + (-1)*a))) MeasureTheory.volume ((43/176):ℝ) ((51/176):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hs : ((10294031/140576345) + (906796/18819697) + (94/6545) : ℝ)
      ≤ ∫ a in ((43/176):ℝ)..((5/16):ℝ), (1/a)*(1/(((17/56):ℝ) + ((-4/7))*a) - 1/(((7/16):ℝ) + (-1)*a)) := by
    have hA := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hB := intervalIntegral.integral_add_adjacent_intervals hi13 hi3
    linarith
  exact hs

/-- Piece `Q2` of the quadrature, in three `a`-slices. -/
private lemma Q2_lower :
    ((40248/8479175) + (49691664/3755419969) + (8183088/401531585) : ℝ)
      ≤ ∫ a in ((17/88):ℝ)..((7/32):ℝ), (1/a)*(1/(((17/88):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a)) := by
  have hs1 : ((40248/8479175) : ℝ) ≤ ∫ a in ((17/88):ℝ)..((71/352)), (1/a)*(1/(((17/88):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a)) := by
    have key := slice_le_Z (A1 := ((17/88):ℝ)) (A2 := ((71/352):ℝ)) (c := ((17/88):ℝ)) (e := 0) (lb1 := ((3336/77275):ℝ))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (by
        have hr : (((71/352):ℝ)/((17/88)))/((((17/88):ℝ)+(0)*((71/352)))/(((17/88):ℝ)+(0)*((17/88)))) = ((71/68):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((71/68):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
    have heq : (1/((17/88):ℝ))*((3336/77275):ℝ) - (1/((17/88):ℝ) - 1/((71/352):ℝ)) = ((40248/8479175):ℝ) := by norm_num
    linarith [key, heq]
  have hs2 : ((49691664/3755419969) : ℝ) ≤ ∫ a in ((71/352):ℝ)..((37/176)), (1/a)*(1/(((17/88):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a)) := by
    have key := slice_le_Z (A1 := ((71/352):ℝ)) (A2 := ((37/176):ℝ)) (c := ((17/88):ℝ)) (e := 0) (lb1 := ((3480/84091):ℝ))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (by
        have hr : (((37/176):ℝ)/((71/352)))/((((17/88):ℝ)+(0)*((37/176)))/(((17/88):ℝ)+(0)*((71/352)))) = ((74/71):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((74/71):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
    have heq : (1/((17/88):ℝ))*((3480/84091):ℝ) - (1/((71/352):ℝ) - 1/((37/176):ℝ)) = ((49691664/3755419969):ℝ) := by norm_num
    linarith [key, heq]
  have hs3 : ((8183088/401531585) : ℝ) ≤ ∫ a in ((37/176):ℝ)..((7/32)), (1/a)*(1/(((17/88):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a)) := by
    have key := slice_le_Z (A1 := ((37/176):ℝ)) (A2 := ((7/32):ℝ)) (c := ((17/88):ℝ)) (e := 0) (lb1 := ((3624/91195):ℝ))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (by
        have hr : (((7/32):ℝ)/((37/176)))/((((17/88):ℝ)+(0)*((7/32)))/(((17/88):ℝ)+(0)*((37/176)))) = ((77/74):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((77/74):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
    have heq : (1/((17/88):ℝ))*((3624/91195):ℝ) - (1/((37/176):ℝ) - 1/((7/32):ℝ)) = ((8183088/401531585):ℝ) := by norm_num
    linarith [key, heq]
  have hi1 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/88):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a))) MeasureTheory.volume ((17/88):ℝ) ((71/352):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi2 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/88):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a))) MeasureTheory.volume ((71/352):ℝ) ((37/176):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi3 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/88):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a))) MeasureTheory.volume ((37/176):ℝ) ((7/32):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi13 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/88):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a))) MeasureTheory.volume ((17/88):ℝ) ((37/176):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hs : ((40248/8479175) + (49691664/3755419969) + (8183088/401531585) : ℝ)
      ≤ ∫ a in ((17/88):ℝ)..((7/32):ℝ), (1/a)*(1/(((17/88):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a)) := by
    have hA := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hB := intervalIntegral.integral_add_adjacent_intervals hi13 hi3
    linarith
  exact hs

/-- Piece `Q3a` of the quadrature, in three `a`-slices. -/
private lemma Q3a_lower :
    ((82674860752/18779449606743) + (807616555979728/34928590755899805) + (401618396987280/9540964534350263) : ℝ)
      ≤ ∫ a in ((1977/8000):ℝ)..((11931/40000):ℝ), (1/a)*(1/(((17/40):ℝ) + ((-4/5))*a) - 1/(((2273/10000):ℝ) + (0)*a)) := by
  have hs1 : ((82674860752/18779449606743) : ℝ) ≤ ∫ a in ((1977/8000):ℝ)..((10567/40000)), (1/a)*(1/(((17/40):ℝ) + ((-4/5))*a) - 1/(((2273/10000):ℝ) + (0)*a)) := by
    have key := slice_le_B (A1 := ((1977/8000):ℝ)) (A2 := ((10567/40000):ℝ)) (c := ((17/40):ℝ)) (e := (-4/5)) (f := ((2273/10000):ℝ)) (g := 0) (lb1 := ((30073472/485998023):ℝ)) (lb2 := ((-682/9885):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : ((((2273/10000):ℝ)+(0)*((10567/40000)))/(((2273/10000):ℝ)+(0)*((1977/8000))))/((((17/40):ℝ)+((-4/5))*((10567/40000)))/(((17/40):ℝ)+((-4/5))*((1977/8000)))) = ((11365/10683):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((11365/10683):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((2273/10000):ℝ)+(0)*((10567/40000)))/(((2273/10000):ℝ)+(0)*((1977/8000))))/(((10567/40000):ℝ)/((1977/8000))) = ((9885/10567):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((9885/10567):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/40):ℝ))*((30073472/485998023):ℝ) + (1/((2273/10000):ℝ) - 1/((17/40):ℝ))*((-682/9885):ℝ) = ((82674860752/18779449606743):ℝ) := by norm_num
    linarith [key, heq]
  have hs2 : ((807616555979728/34928590755899805) : ℝ) ≤ ∫ a in ((10567/40000):ℝ)..((11249/40000)), (1/a)*(1/(((17/40):ℝ) + ((-4/5))*a) - 1/(((2273/10000):ℝ) + (0)*a)) := by
    have key := slice_le_B (A1 := ((10567/40000):ℝ)) (A2 := ((11249/40000):ℝ)) (c := ((17/40):ℝ)) (e := (-4/5)) (f := ((2273/10000):ℝ)) (g := 0) (lb1 := ((28212976/427711575):ℝ)) (lb2 := ((-682/10567):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : ((((2273/10000):ℝ)+(0)*((11249/40000)))/(((2273/10000):ℝ)+(0)*((10567/40000))))/((((17/40):ℝ)+((-4/5))*((11249/40000)))/(((17/40):ℝ)+((-4/5))*((10567/40000)))) = ((10683/10001):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((10683/10001):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((2273/10000):ℝ)+(0)*((11249/40000)))/(((2273/10000):ℝ)+(0)*((10567/40000))))/(((11249/40000):ℝ)/((10567/40000))) = ((10567/11249):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((10567/11249):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/40):ℝ))*((28212976/427711575):ℝ) + (1/((2273/10000):ℝ) - 1/((17/40):ℝ))*((-682/10567):ℝ) = ((807616555979728/34928590755899805):ℝ) := by norm_num
    linarith [key, heq]
  have hs3 : ((401618396987280/9540964534350263) : ℝ) ≤ ∫ a in ((11249/40000):ℝ)..((11931/40000)), (1/a)*(1/(((17/40):ℝ) + ((-4/5))*a) - 1/(((2273/10000):ℝ) + (0)*a)) := by
    have key := slice_le_B (A1 := ((11249/40000):ℝ)) (A2 := ((11931/40000):ℝ)) (c := ((17/40):ℝ)) (e := (-4/5)) (f := ((2273/10000):ℝ)) (g := 0) (lb1 := ((26352480/373146119):ℝ)) (lb2 := ((-682/11249):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : ((((2273/10000):ℝ)+(0)*((11931/40000)))/(((2273/10000):ℝ)+(0)*((11249/40000))))/((((17/40):ℝ)+((-4/5))*((11931/40000)))/(((17/40):ℝ)+((-4/5))*((11249/40000)))) = ((10001/9319):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((10001/9319):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((2273/10000):ℝ)+(0)*((11931/40000)))/(((2273/10000):ℝ)+(0)*((11249/40000))))/(((11931/40000):ℝ)/((11249/40000))) = ((11249/11931):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((11249/11931):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/40):ℝ))*((26352480/373146119):ℝ) + (1/((2273/10000):ℝ) - 1/((17/40):ℝ))*((-682/11249):ℝ) = ((401618396987280/9540964534350263):ℝ) := by norm_num
    linarith [key, heq]
  have hi1 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/40):ℝ) + ((-4/5))*a) - 1/(((2273/10000):ℝ) + (0)*a))) MeasureTheory.volume ((1977/8000):ℝ) ((10567/40000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi2 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/40):ℝ) + ((-4/5))*a) - 1/(((2273/10000):ℝ) + (0)*a))) MeasureTheory.volume ((10567/40000):ℝ) ((11249/40000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi3 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/40):ℝ) + ((-4/5))*a) - 1/(((2273/10000):ℝ) + (0)*a))) MeasureTheory.volume ((11249/40000):ℝ) ((11931/40000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi13 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/40):ℝ) + ((-4/5))*a) - 1/(((2273/10000):ℝ) + (0)*a))) MeasureTheory.volume ((1977/8000):ℝ) ((11249/40000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hs : ((82674860752/18779449606743) + (807616555979728/34928590755899805) + (401618396987280/9540964534350263) : ℝ)
      ≤ ∫ a in ((1977/8000):ℝ)..((11931/40000):ℝ), (1/a)*(1/(((17/40):ℝ) + ((-4/5))*a) - 1/(((2273/10000):ℝ) + (0)*a)) := by
    have hA := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hB := intervalIntegral.integral_add_adjacent_intervals hi13 hi3
    linarith
  exact hs

/-- Piece `Q3b` of the quadrature, in three `a`-slices. -/
private lemma Q3b_lower :
    ((104268403197110185000/1416486720497657845911) + (1476450586870572500/27943260787362174777) + (1362204937808/79595609210691) : ℝ)
      ≤ ∫ a in ((11931/40000):ℝ)..((3/8):ℝ), (1/a)*(1/(((17/40):ℝ) + ((-4/5))*a) - 1/(((5/8):ℝ) + ((-4/3))*a)) := by
  have hs1 : ((104268403197110185000/1416486720497657845911) : ℝ) ≤ ∫ a in ((11931/40000):ℝ)..((6477/20000)), (1/a)*(1/(((17/40):ℝ) + ((-4/5))*a) - 1/(((5/8):ℝ) + ((-4/3))*a)) := by
    have key := slice_le_A (A1 := ((11931/40000):ℝ)) (A2 := ((6477/20000):ℝ)) (c := ((17/40):ℝ)) (e := (-4/5)) (f := ((5/8):ℝ)) (g := (-4/3)) (lb1 := ((3672401205000/18511735805579):ℝ)) (lb2 := ((-213125/4501077):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : (((6477/20000):ℝ)/((11931/40000)))/((((17/40):ℝ)+((-4/5))*((6477/20000)))/(((17/40):ℝ)+((-4/5))*((11931/40000)))) = ((1183513/970388):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((1183513/970388):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((5/8):ℝ)+((-4/3))*((6477/20000)))/(((5/8):ℝ)+((-4/3))*((11931/40000))))/((((17/40):ℝ)+((-4/5))*((6477/20000)))/(((17/40):ℝ)+((-4/5))*((11931/40000)))) = ((4501077/4714202):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((4501077/4714202):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/40):ℝ) - 1/((5/8):ℝ))*((3672401205000/18511735805579):ℝ) + (1/((5/8):ℝ))*((-213125/4501077):ℝ) = ((104268403197110185000/1416486720497657845911):ℝ) := by norm_num
    linarith [key, heq]
  have hs2 : ((1476450586870572500/27943260787362174777) : ℝ) ≤ ∫ a in ((6477/20000):ℝ)..((13977/40000)), (1/a)*(1/(((17/40):ℝ) + ((-4/5))*a) - 1/(((5/8):ℝ) + ((-4/3))*a)) := by
    have key := slice_le_A (A1 := ((6477/20000):ℝ)) (A2 := ((13977/40000):ℝ)) (c := ((17/40):ℝ)) (e := (-4/5)) (f := ((5/8):ℝ)) (g := (-4/3)) (lb1 := ((3513096235000/16936674766731):ℝ)) (lb2 := ((-213125/3299734):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : (((13977/40000):ℝ)/((6477/20000)))/((((17/40):ℝ)+((-4/5))*((13977/40000)))/(((17/40):ℝ)+((-4/5))*((6477/20000)))) = ((1136796/923671):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((1136796/923671):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((5/8):ℝ)+((-4/3))*((13977/40000)))/(((5/8):ℝ)+((-4/3))*((6477/20000))))/((((17/40):ℝ)+((-4/5))*((13977/40000)))/(((17/40):ℝ)+((-4/5))*((6477/20000)))) = ((3299734/3512859):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((3299734/3512859):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/40):ℝ) - 1/((5/8):ℝ))*((3513096235000/16936674766731):ℝ) + (1/((5/8):ℝ))*((-213125/3299734):ℝ) = ((1476450586870572500/27943260787362174777):ℝ) := by norm_num
    linarith [key, heq]
  have hs3 : ((1362204937808/79595609210691) : ℝ) ≤ ∫ a in ((13977/40000):ℝ)..((3/8)), (1/a)*(1/(((17/40):ℝ) + ((-4/5))*a) - 1/(((5/8):ℝ) + ((-4/3))*a)) := by
    have key := slice_le_A (A1 := ((13977/40000):ℝ)) (A2 := ((3/8):ℝ)) (c := ((17/40):ℝ)) (e := (-4/5)) (f := ((5/8):ℝ)) (g := (-4/3)) (lb1 := ((2429499512/10943985867):ℝ)) (lb2 := ((-682/7273):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : (((3/8):ℝ)/((13977/40000)))/((((17/40):ℝ)+((-4/5))*((3/8)))/(((17/40):ℝ)+((-4/5))*((13977/40000)))) = ((29092/23295):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((29092/23295):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((5/8):ℝ)+((-4/3))*((3/8)))/(((5/8):ℝ)+((-4/3))*((13977/40000))))/((((17/40):ℝ)+((-4/5))*((3/8)))/(((17/40):ℝ)+((-4/5))*((13977/40000)))) = ((7273/7955):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((7273/7955):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/40):ℝ) - 1/((5/8):ℝ))*((2429499512/10943985867):ℝ) + (1/((5/8):ℝ))*((-682/7273):ℝ) = ((1362204937808/79595609210691):ℝ) := by norm_num
    linarith [key, heq]
  have hi1 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/40):ℝ) + ((-4/5))*a) - 1/(((5/8):ℝ) + ((-4/3))*a))) MeasureTheory.volume ((11931/40000):ℝ) ((6477/20000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi2 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/40):ℝ) + ((-4/5))*a) - 1/(((5/8):ℝ) + ((-4/3))*a))) MeasureTheory.volume ((6477/20000):ℝ) ((13977/40000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi3 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/40):ℝ) + ((-4/5))*a) - 1/(((5/8):ℝ) + ((-4/3))*a))) MeasureTheory.volume ((13977/40000):ℝ) ((3/8):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi13 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/40):ℝ) + ((-4/5))*a) - 1/(((5/8):ℝ) + ((-4/3))*a))) MeasureTheory.volume ((11931/40000):ℝ) ((13977/40000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hs : ((104268403197110185000/1416486720497657845911) + (1476450586870572500/27943260787362174777) + (1362204937808/79595609210691) : ℝ)
      ≤ ∫ a in ((11931/40000):ℝ)..((3/8):ℝ), (1/a)*(1/(((17/40):ℝ) + ((-4/5))*a) - 1/(((5/8):ℝ) + ((-4/3))*a)) := by
    have hA := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hB := intervalIntegral.integral_add_adjacent_intervals hi13 hi3
    linarith
  exact hs

/-- Piece `Q4a` of the quadrature, in three `a`-slices. -/
private lemma Q4a_lower :
    ((16281200496/2160568430285) + (2464802356900400/78404286100316239) + (97264894570448/1635316476147315) : ℝ)
      ≤ ∫ a in ((14431/40000):ℝ)..((16477/40000):ℝ), (1/a)*(1/(((17/24):ℝ) + ((-4/3))*a) - 1/(((2273/10000):ℝ) + (0)*a)) := by
  have hs1 : ((16281200496/2160568430285) : ℝ) ≤ ∫ a in ((14431/40000):ℝ)..((15113/40000)), (1/a)*(1/(((17/24):ℝ) + ((-4/3))*a) - 1/(((2273/10000):ℝ) + (0)*a)) := by
    have key := slice_le_B (A1 := ((14431/40000):ℝ)) (A2 := ((15113/40000):ℝ)) (c := ((17/24):ℝ)) (e := (-4/3)) (f := ((2273/10000):ℝ)) (g := 0) (lb1 := ((17671984/167741655):ℝ)) (lb2 := ((-682/14431):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : ((((2273/10000):ℝ)+(0)*((15113/40000)))/(((2273/10000):ℝ)+(0)*((14431/40000))))/((((17/24):ℝ)+((-4/3))*((15113/40000)))/(((17/24):ℝ)+((-4/3))*((14431/40000)))) = ((6819/6137):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((6819/6137):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((2273/10000):ℝ)+(0)*((15113/40000)))/(((2273/10000):ℝ)+(0)*((14431/40000))))/(((15113/40000):ℝ)/((14431/40000))) = ((14431/15113):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((14431/15113):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/24):ℝ))*((17671984/167741655):ℝ) + (1/((2273/10000):ℝ) - 1/((17/24):ℝ))*((-682/14431):ℝ) = ((16281200496/2160568430285):ℝ) := by norm_num
    linarith [key, heq]
  have hs2 : ((2464802356900400/78404286100316239) : ℝ) ≤ ∫ a in ((15113/40000):ℝ)..((3159/8000)), (1/a)*(1/(((17/24):ℝ) + ((-4/3))*a) - 1/(((2273/10000):ℝ) + (0)*a)) := by
    have key := slice_le_B (A1 := ((15113/40000):ℝ)) (A2 := ((3159/8000):ℝ)) (c := ((17/24):ℝ)) (e := (-4/3)) (f := ((2273/10000):ℝ)) (g := 0) (lb1 := ((15811488/134258183):ℝ)) (lb2 := ((-682/15113):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : ((((2273/10000):ℝ)+(0)*((3159/8000)))/(((2273/10000):ℝ)+(0)*((15113/40000))))/((((17/24):ℝ)+((-4/3))*((3159/8000)))/(((17/24):ℝ)+((-4/3))*((15113/40000)))) = ((6137/5455):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((6137/5455):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((2273/10000):ℝ)+(0)*((3159/8000)))/(((2273/10000):ℝ)+(0)*((15113/40000))))/(((3159/8000):ℝ)/((15113/40000))) = ((15113/15795):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((15113/15795):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/24):ℝ))*((15811488/134258183):ℝ) + (1/((2273/10000):ℝ) - 1/((17/24):ℝ))*((-682/15113):ℝ) = ((2464802356900400/78404286100316239):ℝ) := by norm_num
    linarith [key, heq]
  have hs3 : ((97264894570448/1635316476147315) : ℝ) ≤ ∫ a in ((3159/8000):ℝ)..((16477/40000)), (1/a)*(1/(((17/24):ℝ) + ((-4/3))*a) - 1/(((2273/10000):ℝ) + (0)*a)) := by
    have key := slice_le_B (A1 := ((3159/8000):ℝ)) (A2 := ((16477/40000):ℝ)) (c := ((17/24):ℝ)) (e := (-4/3)) (f := ((2273/10000):ℝ)) (g := 0) (lb1 := ((13950992/104495703):ℝ)) (lb2 := ((-682/15795):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : ((((2273/10000):ℝ)+(0)*((16477/40000)))/(((2273/10000):ℝ)+(0)*((3159/8000))))/((((17/24):ℝ)+((-4/3))*((16477/40000)))/(((17/24):ℝ)+((-4/3))*((3159/8000)))) = ((5455/4773):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((5455/4773):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((2273/10000):ℝ)+(0)*((16477/40000)))/(((2273/10000):ℝ)+(0)*((3159/8000))))/(((16477/40000):ℝ)/((3159/8000))) = ((15795/16477):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((15795/16477):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/24):ℝ))*((13950992/104495703):ℝ) + (1/((2273/10000):ℝ) - 1/((17/24):ℝ))*((-682/15795):ℝ) = ((97264894570448/1635316476147315):ℝ) := by norm_num
    linarith [key, heq]
  have hi1 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/24):ℝ) + ((-4/3))*a) - 1/(((2273/10000):ℝ) + (0)*a))) MeasureTheory.volume ((14431/40000):ℝ) ((15113/40000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi2 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/24):ℝ) + ((-4/3))*a) - 1/(((2273/10000):ℝ) + (0)*a))) MeasureTheory.volume ((15113/40000):ℝ) ((3159/8000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi3 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/24):ℝ) + ((-4/3))*a) - 1/(((2273/10000):ℝ) + (0)*a))) MeasureTheory.volume ((3159/8000):ℝ) ((16477/40000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi13 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/24):ℝ) + ((-4/3))*a) - 1/(((2273/10000):ℝ) + (0)*a))) MeasureTheory.volume ((14431/40000):ℝ) ((3159/8000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hs : ((16281200496/2160568430285) + (2464802356900400/78404286100316239) + (97264894570448/1635316476147315) : ℝ)
      ≤ ∫ a in ((14431/40000):ℝ)..((16477/40000):ℝ), (1/a)*(1/(((17/24):ℝ) + ((-4/3))*a) - 1/(((2273/10000):ℝ) + (0)*a)) := by
    have hA := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hB := intervalIntegral.integral_add_adjacent_intervals hi13 hi3
    linarith
  exact hs

/-- Piece `Q4b` of the quadrature, in three `a`-slices. -/
private lemma Q4b_lower :
    ((37334645790762595000/1105032230220741200469) + (17580420557026401250/749275331387737534983) + (13941844454032/2900939235395175) : ℝ)
      ≤ ∫ a in ((16477/40000):ℝ)..((7/16):ℝ), (1/a)*(1/(((17/24):ℝ) + ((-4/3))*a) - 1/(((15/8):ℝ) + (-4)*a)) := by
  have hs1 : ((37334645790762595000/1105032230220741200469) : ℝ) ≤ ∫ a in ((16477/40000):ℝ)..((8409/20000)), (1/a)*(1/(((17/24):ℝ) + ((-4/3))*a) - 1/(((15/8):ℝ) + (-4)*a)) := by
    have key := slice_le_A (A1 := ((16477/40000):ℝ)) (A2 := ((8409/20000):ℝ)) (c := ((17/24):ℝ)) (e := (-4/3)) (f := ((15/8):ℝ)) (g := -4) (lb1 := ((2221676743165000/23487265662665259):ℝ)) (lb2 := ((-213125/2305359):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : (((8409/20000):ℝ)/((16477/40000)))/((((17/24):ℝ)+((-4/3))*((8409/20000)))/(((17/24):ℝ)+((-4/3))*((16477/40000)))) = ((40136157/36513032):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((40136157/36513032):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((15/8):ℝ)+(-4)*((8409/20000)))/(((15/8):ℝ)+(-4)*((16477/40000))))/((((17/24):ℝ)+((-4/3))*((8409/20000)))/(((17/24):ℝ)+((-4/3))*((16477/40000)))) = ((2305359/2518484):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((2305359/2518484):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/24):ℝ) - 1/((15/8):ℝ))*((2221676743165000/23487265662665259):ℝ) + (1/((15/8):ℝ))*((-213125/2305359):ℝ) = ((37334645790762595000/1105032230220741200469):ℝ) := by norm_num
    linarith [key, heq]
  have hs2 : ((17580420557026401250/749275331387737534983) : ℝ) ≤ ∫ a in ((8409/20000):ℝ)..((17159/40000)), (1/a)*(1/(((17/24):ℝ) + ((-4/3))*a) - 1/(((15/8):ℝ) + (-4)*a)) := by
    have key := slice_le_A (A1 := ((8409/20000):ℝ)) (A2 := ((17159/40000):ℝ)) (c := ((17/24):ℝ)) (e := (-4/3)) (f := ((15/8):ℝ)) (g := -4) (lb1 := ((2099254943555000/20968721668702251):ℝ)) (lb2 := ((-213125/1762828):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : (((17159/40000):ℝ)/((8409/20000)))/((((17/24):ℝ)+((-4/3))*((17159/40000)))/(((17/24):ℝ)+((-4/3))*((8409/20000)))) = ((38024344/34401219):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((38024344/34401219):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((15/8):ℝ)+(-4)*((17159/40000)))/(((15/8):ℝ)+(-4)*((8409/20000))))/((((17/24):ℝ)+((-4/3))*((17159/40000)))/(((17/24):ℝ)+((-4/3))*((8409/20000)))) = ((1762828/1975953):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((1762828/1975953):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/24):ℝ) - 1/((15/8):ℝ))*((2099254943555000/20968721668702251):ℝ) + (1/((15/8):ℝ))*((-213125/1762828):ℝ) = ((17580420557026401250/749275331387737534983):ℝ) := by norm_num
    linarith [key, heq]
  have hs3 : ((13941844454032/2900939235395175) : ℝ) ≤ ∫ a in ((17159/40000):ℝ)..((7/16)), (1/a)*(1/(((17/24):ℝ) + ((-4/3))*a) - 1/(((15/8):ℝ) + (-4)*a)) := by
    have key := slice_le_A (A1 := ((17159/40000):ℝ)) (A2 := ((7/16):ℝ)) (c := ((17/24):ℝ)) (e := (-4/3)) (f := ((15/8):ℝ)) (g := -4) (lb1 := ((5043436376/47273514795):ℝ)) (lb2 := ((-682/4091):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : (((7/16):ℝ)/((17159/40000)))/((((17/24):ℝ)+((-4/3))*((7/16)))/(((17/24):ℝ)+((-4/3))*((17159/40000)))) = ((57274/51477):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((57274/51477):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((15/8):ℝ)+(-4)*((7/16)))/(((15/8):ℝ)+(-4)*((17159/40000))))/((((17/24):ℝ)+((-4/3))*((7/16)))/(((17/24):ℝ)+((-4/3))*((17159/40000)))) = ((4091/4773):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((4091/4773):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/24):ℝ) - 1/((15/8):ℝ))*((5043436376/47273514795):ℝ) + (1/((15/8):ℝ))*((-682/4091):ℝ) = ((13941844454032/2900939235395175):ℝ) := by norm_num
    linarith [key, heq]
  have hi1 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/24):ℝ) + ((-4/3))*a) - 1/(((15/8):ℝ) + (-4)*a))) MeasureTheory.volume ((16477/40000):ℝ) ((8409/20000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi2 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/24):ℝ) + ((-4/3))*a) - 1/(((15/8):ℝ) + (-4)*a))) MeasureTheory.volume ((8409/20000):ℝ) ((17159/40000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi3 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/24):ℝ) + ((-4/3))*a) - 1/(((15/8):ℝ) + (-4)*a))) MeasureTheory.volume ((17159/40000):ℝ) ((7/16):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi13 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/24):ℝ) + ((-4/3))*a) - 1/(((15/8):ℝ) + (-4)*a))) MeasureTheory.volume ((16477/40000):ℝ) ((17159/40000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hs : ((37334645790762595000/1105032230220741200469) + (17580420557026401250/749275331387737534983) + (13941844454032/2900939235395175) : ℝ)
      ≤ ∫ a in ((16477/40000):ℝ)..((7/16):ℝ), (1/a)*(1/(((17/24):ℝ) + ((-4/3))*a) - 1/(((15/8):ℝ) + (-4)*a)) := by
    have hA := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hB := intervalIntegral.integral_add_adjacent_intervals hi13 hi3
    linarith
  exact hs

/-- Piece `Q5` of the quadrature, in three `a`-slices. -/
private lemma Q5_lower :
    ((15963985928/2728511297979) + (23880151287652/1087422921150345) + (1105195820364680/24436849881794217) : ℝ)
      ≤ ∫ a in ((18977/40000):ℝ)..((1/2):ℝ), (1/a)*(1/(((17/8):ℝ) + (-4)*a) - 1/(((2273/10000):ℝ) + (0)*a)) := by
  have hs1 : ((15963985928/2728511297979) : ℝ) ≤ ∫ a in ((18977/40000):ℝ)..((9659/20000)), (1/a)*(1/(((17/8):ℝ) + (-4)*a) - 1/(((2273/10000):ℝ) + (0)*a)) := by
    have key := slice_le_B (A1 := ((18977/40000):ℝ)) (A2 := ((9659/20000):ℝ)) (c := ((17/8):ℝ)) (e := -4) (f := ((2273/10000):ℝ)) (g := 0) (lb1 := ((11471240/70611819):ℝ)) (lb2 := ((-341/18977):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : ((((2273/10000):ℝ)+(0)*((9659/20000)))/(((2273/10000):ℝ)+(0)*((18977/40000))))/((((17/8):ℝ)+(-4)*((9659/20000)))/(((17/8):ℝ)+(-4)*((18977/40000)))) = ((2273/1932):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((2273/1932):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((2273/10000):ℝ)+(0)*((9659/20000)))/(((2273/10000):ℝ)+(0)*((18977/40000))))/(((9659/20000):ℝ)/((18977/40000))) = ((18977/19318):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((18977/19318):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/8):ℝ))*((11471240/70611819):ℝ) + (1/((2273/10000):ℝ) - 1/((17/8):ℝ))*((-341/18977):ℝ) = ((15963985928/2728511297979):ℝ) := by norm_num
    linarith [key, heq]
  have hs2 : ((23880151287652/1087422921150345) : ℝ) ≤ ∫ a in ((9659/20000):ℝ)..((19659/40000)), (1/a)*(1/(((17/8):ℝ) + (-4)*a) - 1/(((2273/10000):ℝ) + (0)*a)) := by
    have key := slice_le_B (A1 := ((9659/20000):ℝ)) (A2 := ((19659/40000):ℝ)) (c := ((17/8):ℝ)) (e := -4) (f := ((2273/10000):ℝ)) (g := 0) (lb1 := ((9610744/49529835):ℝ)) (lb2 := ((-341/19318):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : ((((2273/10000):ℝ)+(0)*((19659/40000)))/(((2273/10000):ℝ)+(0)*((9659/20000))))/((((17/8):ℝ)+(-4)*((19659/40000)))/(((17/8):ℝ)+(-4)*((9659/20000)))) = ((1932/1591):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((1932/1591):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((2273/10000):ℝ)+(0)*((19659/40000)))/(((2273/10000):ℝ)+(0)*((9659/20000))))/(((19659/40000):ℝ)/((9659/20000))) = ((19318/19659):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((19318/19659):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/8):ℝ))*((9610744/49529835):ℝ) + (1/((2273/10000):ℝ) - 1/((17/8):ℝ))*((-341/19318):ℝ) = ((23880151287652/1087422921150345):ℝ) := by norm_num
    linarith [key, heq]
  have hs3 : ((1105195820364680/24436849881794217) : ℝ) ≤ ∫ a in ((19659/40000):ℝ)..((1/2)), (1/a)*(1/(((17/8):ℝ) + (-4)*a) - 1/(((2273/10000):ℝ) + (0)*a)) := by
    have key := slice_le_B (A1 := ((19659/40000):ℝ)) (A2 := ((1/2):ℝ)) (c := ((17/8):ℝ)) (e := -4) (f := ((2273/10000):ℝ)) (g := 0) (lb1 := ((7750248/32168843):ℝ)) (lb2 := ((-341/19659):ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : ((((2273/10000):ℝ)+(0)*((1/2)))/(((2273/10000):ℝ)+(0)*((19659/40000))))/((((17/8):ℝ)+(-4)*((1/2)))/(((17/8):ℝ)+(-4)*((19659/40000)))) = ((1591/1250):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((1591/1250):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((2273/10000):ℝ)+(0)*((1/2)))/(((2273/10000):ℝ)+(0)*((19659/40000))))/(((1/2):ℝ)/((19659/40000))) = ((19659/20000):ℝ) := by norm_num
        rw [hr]
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < ((19659/20000):ℝ))
        norm_num at hh
        linarith
        )
    have heq : (1/((17/8):ℝ))*((7750248/32168843):ℝ) + (1/((2273/10000):ℝ) - 1/((17/8):ℝ))*((-341/19659):ℝ) = ((1105195820364680/24436849881794217):ℝ) := by norm_num
    linarith [key, heq]
  have hi1 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/8):ℝ) + (-4)*a) - 1/(((2273/10000):ℝ) + (0)*a))) MeasureTheory.volume ((18977/40000):ℝ) ((9659/20000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi2 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/8):ℝ) + (-4)*a) - 1/(((2273/10000):ℝ) + (0)*a))) MeasureTheory.volume ((9659/20000):ℝ) ((19659/40000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi3 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/8):ℝ) + (-4)*a) - 1/(((2273/10000):ℝ) + (0)*a))) MeasureTheory.volume ((19659/40000):ℝ) ((1/2):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi13 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((17/8):ℝ) + (-4)*a) - 1/(((2273/10000):ℝ) + (0)*a))) MeasureTheory.volume ((18977/40000):ℝ) ((19659/40000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hs : ((15963985928/2728511297979) + (23880151287652/1087422921150345) + (1105195820364680/24436849881794217) : ℝ)
      ≤ ∫ a in ((18977/40000):ℝ)..((1/2):ℝ), (1/a)*(1/(((17/8):ℝ) + (-4)*a) - 1/(((2273/10000):ℝ) + (0)*a)) := by
    have hA := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hB := intervalIntegral.integral_add_adjacent_intervals hi13 hi3
    linarith
  exact hs

/-- Piece `Q6a` of the quadrature, in three `a`-slices. -/
private lemma Q6a_lower :
    ((14347477115000/6157192251765009) + (63135889369437000/9552427365740068901) + (149589117164092/14430612809513523) : ℝ)
      ≤ ∫ a in ((2273/10000):ℝ)..((1/4):ℝ), (1/a)*(1/(((2273/10000):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a)) := by
  have hs1 : ((14347477115000/6157192251765009) : ℝ) ≤ ∫ a in ((2273/10000):ℝ)..((3523/15000)), (1/a)*(1/(((2273/10000):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a)) := by
    have key := slice_le_Z (A1 := ((2273/10000):ℝ)) (A2 := ((3523/15000):ℝ)) (c := ((2273/10000):ℝ)) (e := 0) (lb1 := ((25178840/768901371):ℝ))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (by
        have hr : (((3523/15000):ℝ)/((2273/10000)))/((((2273/10000):ℝ)+(0)*((3523/15000)))/(((2273/10000):ℝ)+(0)*((2273/10000)))) = ((7046/6819):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((7046/6819):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
    have heq : (1/((2273/10000):ℝ))*((25178840/768901371):ℝ) - (1/((2273/10000):ℝ) - 1/((3523/15000):ℝ)) = ((14347477115000/6157192251765009):ℝ) := by norm_num
    linarith [key, heq]
  have hs2 : ((63135889369437000/9552427365740068901) : ℝ) ≤ ∫ a in ((3523/15000):ℝ)..((7273/30000)), (1/a)*(1/(((2273/10000):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a)) := by
    have key := slice_le_Z (A1 := ((3523/15000):ℝ)) (A2 := ((7273/30000):ℝ)) (c := ((2273/10000):ℝ)) (e := 0) (lb1 := ((26003304/820083515):ℝ))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (by
        have hr : (((7273/30000):ℝ)/((3523/15000)))/((((2273/10000):ℝ)+(0)*((7273/30000)))/(((2273/10000):ℝ)+(0)*((3523/15000)))) = ((7273/7046):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((7273/7046):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
    have heq : (1/((2273/10000):ℝ))*((26003304/820083515):ℝ) - (1/((3523/15000):ℝ) - 1/((7273/30000):ℝ)) = ((63135889369437000/9552427365740068901):ℝ) := by norm_num
    linarith [key, heq]
  have hs3 : ((149589117164092/14430612809513523) : ℝ) ≤ ∫ a in ((7273/30000):ℝ)..((1/4)), (1/a)*(1/(((2273/10000):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a)) := by
    have key := slice_le_Z (A1 := ((7273/30000):ℝ)) (A2 := ((1/4):ℝ)) (c := ((2273/10000):ℝ)) (e := 0) (lb1 := ((26827768/872914587):ℝ))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (by
        have hr : (((1/4):ℝ)/((7273/30000)))/((((2273/10000):ℝ)+(0)*((1/4)))/(((2273/10000):ℝ)+(0)*((7273/30000)))) = ((7500/7273):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((7500/7273):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
    have heq : (1/((2273/10000):ℝ))*((26827768/872914587):ℝ) - (1/((7273/30000):ℝ) - 1/((1/4):ℝ)) = ((149589117164092/14430612809513523):ℝ) := by norm_num
    linarith [key, heq]
  have hi1 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((2273/10000):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a))) MeasureTheory.volume ((2273/10000):ℝ) ((3523/15000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi2 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((2273/10000):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a))) MeasureTheory.volume ((3523/15000):ℝ) ((7273/30000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi3 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((2273/10000):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a))) MeasureTheory.volume ((7273/30000):ℝ) ((1/4):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi13 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((2273/10000):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a))) MeasureTheory.volume ((2273/10000):ℝ) ((7273/30000):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hs : ((14347477115000/6157192251765009) + (63135889369437000/9552427365740068901) + (149589117164092/14430612809513523) : ℝ)
      ≤ ∫ a in ((2273/10000):ℝ)..((1/4):ℝ), (1/a)*(1/(((2273/10000):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a)) := by
    have hA := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hB := intervalIntegral.integral_add_adjacent_intervals hi13 hi3
    linarith
  exact hs

/-- Piece `Q6b` of the quadrature, in three `a`-slices. -/
private lemma Q6b_lower :
    ((50848/443235) + (65376/734179) + (79904/1097859) : ℝ)
      ≤ ∫ a in ((1/4):ℝ)..((1/2):ℝ), (1/a)*(1/(((2273/10000):ℝ) + (0)*a) - 1/(((1/4):ℝ) + (0)*a)) := by
  have hs1 : ((50848/443235) : ℝ) ≤ ∫ a in ((1/4):ℝ)..((1/3)), (1/a)*(1/(((2273/10000):ℝ) + (0)*a) - 1/(((1/4):ℝ) + (0)*a)) := by
    have key := slice_le_A (A1 := ((1/4):ℝ)) (A2 := ((1/3):ℝ)) (c := ((2273/10000):ℝ)) (e := 0) (f := ((1/4):ℝ)) (g := 0) (lb1 := ((56/195):ℝ)) (lb2 := (0:ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : (((1/3):ℝ)/((1/4)))/((((2273/10000):ℝ)+(0)*((1/3)))/(((2273/10000):ℝ)+(0)*((1/4)))) = ((4/3):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((4/3):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((1/4):ℝ)+(0)*((1/3)))/(((1/4):ℝ)+(0)*((1/4))))/((((2273/10000):ℝ)+(0)*((1/3)))/(((2273/10000):ℝ)+(0)*((1/4)))) = (1:ℝ) := by norm_num
        rw [hr]
        simp
        )
    have heq : (1/((2273/10000):ℝ) - 1/((1/4):ℝ))*((56/195):ℝ) + (1/((1/4):ℝ))*(0:ℝ) = ((50848/443235):ℝ) := by norm_num
    linarith [key, heq]
  have hs2 : ((65376/734179) : ℝ) ≤ ∫ a in ((1/3):ℝ)..((5/12)), (1/a)*(1/(((2273/10000):ℝ) + (0)*a) - 1/(((1/4):ℝ) + (0)*a)) := by
    have key := slice_le_A (A1 := ((1/3):ℝ)) (A2 := ((5/12):ℝ)) (c := ((2273/10000):ℝ)) (e := 0) (f := ((1/4):ℝ)) (g := 0) (lb1 := ((72/323):ℝ)) (lb2 := (0:ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : (((5/12):ℝ)/((1/3)))/((((2273/10000):ℝ)+(0)*((5/12)))/(((2273/10000):ℝ)+(0)*((1/3)))) = ((5/4):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((5/4):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((1/4):ℝ)+(0)*((5/12)))/(((1/4):ℝ)+(0)*((1/3))))/((((2273/10000):ℝ)+(0)*((5/12)))/(((2273/10000):ℝ)+(0)*((1/3)))) = (1:ℝ) := by norm_num
        rw [hr]
        simp
        )
    have heq : (1/((2273/10000):ℝ) - 1/((1/4):ℝ))*((72/323):ℝ) + (1/((1/4):ℝ))*(0:ℝ) = ((65376/734179):ℝ) := by norm_num
    linarith [key, heq]
  have hs3 : ((79904/1097859) : ℝ) ≤ ∫ a in ((5/12):ℝ)..((1/2)), (1/a)*(1/(((2273/10000):ℝ) + (0)*a) - 1/(((1/4):ℝ) + (0)*a)) := by
    have key := slice_le_A (A1 := ((5/12):ℝ)) (A2 := ((1/2):ℝ)) (c := ((2273/10000):ℝ)) (e := 0) (f := ((1/4):ℝ)) (g := 0) (lb1 := ((88/483):ℝ)) (lb2 := (0:ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (by norm_num)
      (by
        have hr : (((1/2):ℝ)/((5/12)))/((((2273/10000):ℝ)+(0)*((1/2)))/(((2273/10000):ℝ)+(0)*((5/12)))) = ((6/5):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((6/5):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
      (by
        have hr : ((((1/4):ℝ)+(0)*((1/2)))/(((1/4):ℝ)+(0)*((5/12))))/((((2273/10000):ℝ)+(0)*((1/2)))/(((2273/10000):ℝ)+(0)*((5/12)))) = (1:ℝ) := by norm_num
        rw [hr]
        simp
        )
    have heq : (1/((2273/10000):ℝ) - 1/((1/4):ℝ))*((88/483):ℝ) + (1/((1/4):ℝ))*(0:ℝ) = ((79904/1097859):ℝ) := by norm_num
    linarith [key, heq]
  have hi1 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((2273/10000):ℝ) + (0)*a) - 1/(((1/4):ℝ) + (0)*a))) MeasureTheory.volume ((1/4):ℝ) ((1/3):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi2 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((2273/10000):ℝ) + (0)*a) - 1/(((1/4):ℝ) + (0)*a))) MeasureTheory.volume ((1/3):ℝ) ((5/12):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi3 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((2273/10000):ℝ) + (0)*a) - 1/(((1/4):ℝ) + (0)*a))) MeasureTheory.volume ((5/12):ℝ) ((1/2):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi13 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((2273/10000):ℝ) + (0)*a) - 1/(((1/4):ℝ) + (0)*a))) MeasureTheory.volume ((1/4):ℝ) ((5/12):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hs : ((50848/443235) + (65376/734179) + (79904/1097859) : ℝ)
      ≤ ∫ a in ((1/4):ℝ)..((1/2):ℝ), (1/a)*(1/(((2273/10000):ℝ) + (0)*a) - 1/(((1/4):ℝ) + (0)*a)) := by
    have hA := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hB := intervalIntegral.integral_add_adjacent_intervals hi13 hi3
    linarith
  exact hs

/-- Piece `Q7a` of the quadrature, in three `a`-slices. -/
private lemma Q7a_lower :
    ((154/7215) + (5226/96965) + (1751/23265) : ℝ)
      ≤ ∫ a in ((1/4):ℝ)..((1/3):ℝ), (1/a)*(1/(((1/4):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a)) := by
  have hs1 : ((154/7215) : ℝ) ≤ ∫ a in ((1/4):ℝ)..((5/18)), (1/a)*(1/(((1/4):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a)) := by
    have key := slice_le_Z (A1 := ((1/4):ℝ)) (A2 := ((5/18):ℝ)) (c := ((1/4):ℝ)) (e := 0) (lb1 := ((152/1443):ℝ))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (by
        have hr : (((5/18):ℝ)/((1/4)))/((((1/4):ℝ)+(0)*((5/18)))/(((1/4):ℝ)+(0)*((1/4)))) = ((10/9):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((10/9):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
    have heq : (1/((1/4):ℝ))*((152/1443):ℝ) - (1/((1/4):ℝ) - 1/((5/18):ℝ)) = ((154/7215):ℝ) := by norm_num
    linarith [key, heq]
  have hs2 : ((5226/96965) : ℝ) ≤ ∫ a in ((5/18):ℝ)..((11/36)), (1/a)*(1/(((1/4):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a)) := by
    have key := slice_le_Z (A1 := ((5/18):ℝ)) (A2 := ((11/36):ℝ)) (c := ((1/4):ℝ)) (e := 0) (lb1 := ((168/1763):ℝ))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (by
        have hr : (((11/36):ℝ)/((5/18)))/((((1/4):ℝ)+(0)*((11/36)))/(((1/4):ℝ)+(0)*((5/18)))) = ((11/10):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((11/10):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
    have heq : (1/((1/4):ℝ))*((168/1763):ℝ) - (1/((5/18):ℝ) - 1/((11/36):ℝ)) = ((5226/96965):ℝ) := by norm_num
    linarith [key, heq]
  have hs3 : ((1751/23265) : ℝ) ≤ ∫ a in ((11/36):ℝ)..((1/3)), (1/a)*(1/(((1/4):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a)) := by
    have key := slice_le_Z (A1 := ((11/36):ℝ)) (A2 := ((1/3):ℝ)) (c := ((1/4):ℝ)) (e := 0) (lb1 := ((184/2115):ℝ))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith)
      (by
        have hr : (((1/3):ℝ)/((11/36)))/((((1/4):ℝ)+(0)*((1/3)))/(((1/4):ℝ)+(0)*((11/36)))) = ((12/11):ℝ) := by norm_num
        rw [hr]
        have hh := log_second (x := ((12/11):ℝ)) (by norm_num)
        norm_num at hh
        linarith
        )
    have heq : (1/((1/4):ℝ))*((184/2115):ℝ) - (1/((11/36):ℝ) - 1/((1/3):ℝ)) = ((1751/23265):ℝ) := by norm_num
    linarith [key, heq]
  have hi1 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((1/4):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a))) MeasureTheory.volume ((1/4):ℝ) ((5/18):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi2 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((1/4):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a))) MeasureTheory.volume ((5/18):ℝ) ((11/36):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi3 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((1/4):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a))) MeasureTheory.volume ((11/36):ℝ) ((1/3):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hi13 : IntervalIntegrable (fun a : ℝ => (1/a)*(1/(((1/4):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a))) MeasureTheory.volume ((1/4):ℝ) ((11/36):ℝ) := by
    apply piece_integrand_integrable (by norm_num) (by norm_num) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have hs : ((154/7215) + (5226/96965) + (1751/23265) : ℝ)
      ≤ ∫ a in ((1/4):ℝ)..((1/3):ℝ), (1/a)*(1/(((1/4):ℝ) + (0)*a) - 1/((0:ℝ) + (1)*a)) := by
    have hA := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hB := intervalIntegral.integral_add_adjacent_intervals hi13 hi3
    linarith
  exact hs

/-- One piece of the quadrature, in two halves: the part of the region with `b ≥ 1/4`,
`a ∈ [1/3, 1/2]`, `b ≤ (1 - a)/2`. Each half contributes its second-order log bound. -/
private lemma Q7b_lower :
    (362:ℝ)/2261 + 45/1449
      ≤ ∫ a in (1/3:ℝ)..(1/2:ℝ),
          (1/a)*(1/((1/4:ℝ) + 0*a) - 1/((1/2:ℝ) + (-1/2)*a)) := by
  have hs1 : (362:ℝ)/2261
      ≤ ∫ a in (1/3:ℝ)..(5/12:ℝ),
          (1/a)*(1/((1/4:ℝ) + 0*a) - 1/((1/2:ℝ) + (-1/2)*a)) := by
    rw [outer_split (A1 := (1/3:ℝ)) (A2 := (5/12:ℝ)) (c := (1/4:ℝ)) (e := 0) (f := (1/2:ℝ))
      (g := -1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by positivity) (fun a ha1 ha2 => by linarith)]
    have e1 : ((5/12:ℝ)/(1/3)) = 5/4 := by norm_num
    have e2 : (((1/4:ℝ) + 0*(5/12))/((1/4:ℝ) + 0*(1/3))) = 1 := by norm_num
    have e3 : (((1/2:ℝ) + (-1/2)*(5/12))/((1/2:ℝ) + (-1/2)*(1/3))) = 7/8 := by norm_num
    rw [e1, e2, e3, Real.log_one]
    norm_num
    have h1 : (72:ℝ)/323 ≤ Real.log (5/4) := by
      have h2 := log_second (x := (5/4:ℝ)) (by norm_num)
      norm_num at h2
      exact h2
    have h3 : (-1:ℝ)/7 ≤ Real.log (7/8) := by
      have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 7/8)
      norm_num at h2
      linarith
    linarith
  have hs2 : (45:ℝ)/1449
      ≤ ∫ a in (5/12:ℝ)..(1/2:ℝ),
          (1/a)*(1/((1/4:ℝ) + 0*a) - 1/((1/2:ℝ) + (-1/2)*a)) := by
    rw [outer_split (A1 := (5/12:ℝ)) (A2 := (1/2:ℝ)) (c := (1/4:ℝ)) (e := 0) (f := (1/2:ℝ))
      (g := -1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by positivity) (fun a ha1 ha2 => by linarith)]
    have e1 : ((1/2:ℝ)/(5/12)) = 6/5 := by norm_num
    have e2 : (((1/4:ℝ) + 0*(1/2))/((1/4:ℝ) + 0*(5/12))) = 1 := by norm_num
    have e3 : (((1/2:ℝ) + (-1/2)*(1/2))/((1/2:ℝ) + (-1/2)*(5/12))) = 6/7 := by norm_num
    rw [e1, e2, e3, Real.log_one]
    norm_num
    have h1 : (88:ℝ)/483 ≤ Real.log (6/5) := by
      have h2 := log_second (x := (6/5:ℝ)) (by norm_num)
      norm_num at h2
      exact h2
    have h3 : (-1:ℝ)/6 ≤ Real.log (6/7) := by
      have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 6/7)
      norm_num at h2
      linarith
    linarith
  have hi1 : IntervalIntegrable
      (fun a : ℝ => (1/a)*(1/((1/4:ℝ) + 0*a) - 1/((1/2:ℝ) + (-1/2)*a)))
      MeasureTheory.volume (1/3:ℝ) (5/12:ℝ) :=
    piece_integrand_integrable (by norm_num) (by norm_num)
      (fun a _ _ => by positivity) (fun a ha1 ha2 => by linarith)
  have hi2 : IntervalIntegrable
      (fun a : ℝ => (1/a)*(1/((1/4:ℝ) + 0*a) - 1/((1/2:ℝ) + (-1/2)*a)))
      MeasureTheory.volume (5/12:ℝ) (1/2:ℝ) :=
    piece_integrand_integrable (by norm_num) (by norm_num)
      (fun a _ _ => by positivity) (fun a ha1 ha2 => by linarith)
  have hs : (362:ℝ)/2261 + 45/1449
      ≤ ∫ a in (1/3:ℝ)..(1/2:ℝ),
          (1/a)*(1/((1/4:ℝ) + 0*a) - 1/((1/2:ℝ) + (-1/2)*a)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    linarith
  exact hs

/-- The double integral of one piece's indicator function: it equals the piece's outer integral.
This is the equality behind `piece_lower`, stated on the explicit indicator so that the pieces can be
summed. -/
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
private lemma excl_1a1 {a b : ℝ}
    (h : ((17/88) < a ∧ a ≤ (9/40) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a))) :
    ¬((9/40) < a ∧ a ≤ (2273/10000) ∧ ((1/16) + ((1/2))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (43/176) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((43/176) < a ∧ a ≤ (5/16) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((7/16) + (-1)*a)) ∧ ¬((17/88) < a ∧ a ≤ (7/32) ∧ ((17/88) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1977/8000) < a ∧ a ≤ (11931/40000) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((11931/40000) < a ∧ a ≤ (3/8) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((5/8) + ((-4/3))*a)) ∧ ¬((14431/40000) < a ∧ a ≤ (16477/40000) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((16477/40000) < a ∧ a ≤ (7/16) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((15/8) + (-4)*a)) ∧ ¬((18977/40000) < a ∧ a ≤ (1/2) ∧ ((17/8) + (-4)*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (1/4) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/2) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ ((1/4) + (0)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/3) ∧ ((1/4) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/3) < a ∧ a ≤ (1/2) ∧ ((1/4) + (0)*a) < b ∧ b ≤ ((1/2) + ((-1/2))*a)) := by
  obtain ⟨i1, i2, i3, i4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rintro ⟨j1, j2, j3, j4⟩
  all_goals linarith

/-- Piece `1a2a` excludes every other piece (pairwise disjointness of the thirteen regions). -/
private lemma excl_1a2a {a b : ℝ}
    (h : ((9/40) < a ∧ a ≤ (2273/10000) ∧ ((1/16) + ((1/2))*a) < b ∧ b ≤ ((17/88) + (0)*a))) :
    ¬((17/88) < a ∧ a ≤ (9/40) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (43/176) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((43/176) < a ∧ a ≤ (5/16) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((7/16) + (-1)*a)) ∧ ¬((17/88) < a ∧ a ≤ (7/32) ∧ ((17/88) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1977/8000) < a ∧ a ≤ (11931/40000) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((11931/40000) < a ∧ a ≤ (3/8) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((5/8) + ((-4/3))*a)) ∧ ¬((14431/40000) < a ∧ a ≤ (16477/40000) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((16477/40000) < a ∧ a ≤ (7/16) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((15/8) + (-4)*a)) ∧ ¬((18977/40000) < a ∧ a ≤ (1/2) ∧ ((17/8) + (-4)*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (1/4) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/2) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ ((1/4) + (0)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/3) ∧ ((1/4) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/3) < a ∧ a ≤ (1/2) ∧ ((1/4) + (0)*a) < b ∧ b ≤ ((1/2) + ((-1/2))*a)) := by
  obtain ⟨i1, i2, i3, i4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rintro ⟨j1, j2, j3, j4⟩
  all_goals linarith

/-- Piece `1a2b` excludes every other piece (pairwise disjointness of the thirteen regions). -/
private lemma excl_1a2b {a b : ℝ}
    (h : ((2273/10000) < a ∧ a ≤ (43/176) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a))) :
    ¬((17/88) < a ∧ a ≤ (9/40) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((9/40) < a ∧ a ≤ (2273/10000) ∧ ((1/16) + ((1/2))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((43/176) < a ∧ a ≤ (5/16) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((7/16) + (-1)*a)) ∧ ¬((17/88) < a ∧ a ≤ (7/32) ∧ ((17/88) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1977/8000) < a ∧ a ≤ (11931/40000) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((11931/40000) < a ∧ a ≤ (3/8) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((5/8) + ((-4/3))*a)) ∧ ¬((14431/40000) < a ∧ a ≤ (16477/40000) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((16477/40000) < a ∧ a ≤ (7/16) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((15/8) + (-4)*a)) ∧ ¬((18977/40000) < a ∧ a ≤ (1/2) ∧ ((17/8) + (-4)*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (1/4) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/2) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ ((1/4) + (0)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/3) ∧ ((1/4) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/3) < a ∧ a ≤ (1/2) ∧ ((1/4) + (0)*a) < b ∧ b ≤ ((1/2) + ((-1/2))*a)) := by
  obtain ⟨i1, i2, i3, i4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rintro ⟨j1, j2, j3, j4⟩
  all_goals linarith

/-- Piece `1b` excludes every other piece (pairwise disjointness of the thirteen regions). -/
private lemma excl_1b {a b : ℝ}
    (h : ((43/176) < a ∧ a ≤ (5/16) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((7/16) + (-1)*a))) :
    ¬((17/88) < a ∧ a ≤ (9/40) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((9/40) < a ∧ a ≤ (2273/10000) ∧ ((1/16) + ((1/2))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (43/176) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((17/88) < a ∧ a ≤ (7/32) ∧ ((17/88) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1977/8000) < a ∧ a ≤ (11931/40000) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((11931/40000) < a ∧ a ≤ (3/8) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((5/8) + ((-4/3))*a)) ∧ ¬((14431/40000) < a ∧ a ≤ (16477/40000) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((16477/40000) < a ∧ a ≤ (7/16) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((15/8) + (-4)*a)) ∧ ¬((18977/40000) < a ∧ a ≤ (1/2) ∧ ((17/8) + (-4)*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (1/4) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/2) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ ((1/4) + (0)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/3) ∧ ((1/4) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/3) < a ∧ a ≤ (1/2) ∧ ((1/4) + (0)*a) < b ∧ b ≤ ((1/2) + ((-1/2))*a)) := by
  obtain ⟨i1, i2, i3, i4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rintro ⟨j1, j2, j3, j4⟩
  all_goals linarith

/-- Piece `2` excludes every other piece (pairwise disjointness of the thirteen regions). -/
private lemma excl_2 {a b : ℝ}
    (h : ((17/88) < a ∧ a ≤ (7/32) ∧ ((17/88) + (0)*a) < b ∧ b ≤ (0 + (1)*a))) :
    ¬((17/88) < a ∧ a ≤ (9/40) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((9/40) < a ∧ a ≤ (2273/10000) ∧ ((1/16) + ((1/2))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (43/176) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((43/176) < a ∧ a ≤ (5/16) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((7/16) + (-1)*a)) ∧ ¬((1977/8000) < a ∧ a ≤ (11931/40000) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((11931/40000) < a ∧ a ≤ (3/8) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((5/8) + ((-4/3))*a)) ∧ ¬((14431/40000) < a ∧ a ≤ (16477/40000) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((16477/40000) < a ∧ a ≤ (7/16) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((15/8) + (-4)*a)) ∧ ¬((18977/40000) < a ∧ a ≤ (1/2) ∧ ((17/8) + (-4)*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (1/4) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/2) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ ((1/4) + (0)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/3) ∧ ((1/4) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/3) < a ∧ a ≤ (1/2) ∧ ((1/4) + (0)*a) < b ∧ b ≤ ((1/2) + ((-1/2))*a)) := by
  obtain ⟨i1, i2, i3, i4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rintro ⟨j1, j2, j3, j4⟩
  all_goals linarith

/-- Piece `3a` excludes every other piece (pairwise disjointness of the thirteen regions). -/
private lemma excl_3a {a b : ℝ}
    (h : ((1977/8000) < a ∧ a ≤ (11931/40000) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((2273/10000) + (0)*a))) :
    ¬((17/88) < a ∧ a ≤ (9/40) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((9/40) < a ∧ a ≤ (2273/10000) ∧ ((1/16) + ((1/2))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (43/176) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((43/176) < a ∧ a ≤ (5/16) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((7/16) + (-1)*a)) ∧ ¬((17/88) < a ∧ a ≤ (7/32) ∧ ((17/88) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((11931/40000) < a ∧ a ≤ (3/8) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((5/8) + ((-4/3))*a)) ∧ ¬((14431/40000) < a ∧ a ≤ (16477/40000) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((16477/40000) < a ∧ a ≤ (7/16) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((15/8) + (-4)*a)) ∧ ¬((18977/40000) < a ∧ a ≤ (1/2) ∧ ((17/8) + (-4)*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (1/4) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/2) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ ((1/4) + (0)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/3) ∧ ((1/4) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/3) < a ∧ a ≤ (1/2) ∧ ((1/4) + (0)*a) < b ∧ b ≤ ((1/2) + ((-1/2))*a)) := by
  obtain ⟨i1, i2, i3, i4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rintro ⟨j1, j2, j3, j4⟩
  all_goals linarith

/-- Piece `3b` excludes every other piece (pairwise disjointness of the thirteen regions). -/
private lemma excl_3b {a b : ℝ}
    (h : ((11931/40000) < a ∧ a ≤ (3/8) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((5/8) + ((-4/3))*a))) :
    ¬((17/88) < a ∧ a ≤ (9/40) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((9/40) < a ∧ a ≤ (2273/10000) ∧ ((1/16) + ((1/2))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (43/176) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((43/176) < a ∧ a ≤ (5/16) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((7/16) + (-1)*a)) ∧ ¬((17/88) < a ∧ a ≤ (7/32) ∧ ((17/88) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1977/8000) < a ∧ a ≤ (11931/40000) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((14431/40000) < a ∧ a ≤ (16477/40000) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((16477/40000) < a ∧ a ≤ (7/16) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((15/8) + (-4)*a)) ∧ ¬((18977/40000) < a ∧ a ≤ (1/2) ∧ ((17/8) + (-4)*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (1/4) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/2) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ ((1/4) + (0)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/3) ∧ ((1/4) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/3) < a ∧ a ≤ (1/2) ∧ ((1/4) + (0)*a) < b ∧ b ≤ ((1/2) + ((-1/2))*a)) := by
  obtain ⟨i1, i2, i3, i4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rintro ⟨j1, j2, j3, j4⟩
  all_goals linarith

/-- Piece `4a` excludes every other piece (pairwise disjointness of the thirteen regions). -/
private lemma excl_4a {a b : ℝ}
    (h : ((14431/40000) < a ∧ a ≤ (16477/40000) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((2273/10000) + (0)*a))) :
    ¬((17/88) < a ∧ a ≤ (9/40) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((9/40) < a ∧ a ≤ (2273/10000) ∧ ((1/16) + ((1/2))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (43/176) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((43/176) < a ∧ a ≤ (5/16) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((7/16) + (-1)*a)) ∧ ¬((17/88) < a ∧ a ≤ (7/32) ∧ ((17/88) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1977/8000) < a ∧ a ≤ (11931/40000) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((11931/40000) < a ∧ a ≤ (3/8) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((5/8) + ((-4/3))*a)) ∧ ¬((16477/40000) < a ∧ a ≤ (7/16) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((15/8) + (-4)*a)) ∧ ¬((18977/40000) < a ∧ a ≤ (1/2) ∧ ((17/8) + (-4)*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (1/4) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/2) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ ((1/4) + (0)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/3) ∧ ((1/4) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/3) < a ∧ a ≤ (1/2) ∧ ((1/4) + (0)*a) < b ∧ b ≤ ((1/2) + ((-1/2))*a)) := by
  obtain ⟨i1, i2, i3, i4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rintro ⟨j1, j2, j3, j4⟩
  all_goals linarith

/-- Piece `4b` excludes every other piece (pairwise disjointness of the thirteen regions). -/
private lemma excl_4b {a b : ℝ}
    (h : ((16477/40000) < a ∧ a ≤ (7/16) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((15/8) + (-4)*a))) :
    ¬((17/88) < a ∧ a ≤ (9/40) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((9/40) < a ∧ a ≤ (2273/10000) ∧ ((1/16) + ((1/2))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (43/176) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((43/176) < a ∧ a ≤ (5/16) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((7/16) + (-1)*a)) ∧ ¬((17/88) < a ∧ a ≤ (7/32) ∧ ((17/88) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1977/8000) < a ∧ a ≤ (11931/40000) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((11931/40000) < a ∧ a ≤ (3/8) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((5/8) + ((-4/3))*a)) ∧ ¬((14431/40000) < a ∧ a ≤ (16477/40000) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((18977/40000) < a ∧ a ≤ (1/2) ∧ ((17/8) + (-4)*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (1/4) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/2) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ ((1/4) + (0)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/3) ∧ ((1/4) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/3) < a ∧ a ≤ (1/2) ∧ ((1/4) + (0)*a) < b ∧ b ≤ ((1/2) + ((-1/2))*a)) := by
  obtain ⟨i1, i2, i3, i4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rintro ⟨j1, j2, j3, j4⟩
  all_goals linarith

/-- Piece `5` excludes every other piece (pairwise disjointness of the thirteen regions). -/
private lemma excl_5 {a b : ℝ}
    (h : ((18977/40000) < a ∧ a ≤ (1/2) ∧ ((17/8) + (-4)*a) < b ∧ b ≤ ((2273/10000) + (0)*a))) :
    ¬((17/88) < a ∧ a ≤ (9/40) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((9/40) < a ∧ a ≤ (2273/10000) ∧ ((1/16) + ((1/2))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (43/176) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((43/176) < a ∧ a ≤ (5/16) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((7/16) + (-1)*a)) ∧ ¬((17/88) < a ∧ a ≤ (7/32) ∧ ((17/88) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1977/8000) < a ∧ a ≤ (11931/40000) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((11931/40000) < a ∧ a ≤ (3/8) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((5/8) + ((-4/3))*a)) ∧ ¬((14431/40000) < a ∧ a ≤ (16477/40000) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((16477/40000) < a ∧ a ≤ (7/16) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((15/8) + (-4)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (1/4) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/2) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ ((1/4) + (0)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/3) ∧ ((1/4) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/3) < a ∧ a ≤ (1/2) ∧ ((1/4) + (0)*a) < b ∧ b ≤ ((1/2) + ((-1/2))*a)) := by
  obtain ⟨i1, i2, i3, i4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rintro ⟨j1, j2, j3, j4⟩
  all_goals linarith

/-- Piece `6a` excludes every other piece (pairwise disjointness of the thirteen regions). -/
private lemma excl_6a {a b : ℝ}
    (h : ((2273/10000) < a ∧ a ≤ (1/4) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ (0 + (1)*a))) :
    ¬((17/88) < a ∧ a ≤ (9/40) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((9/40) < a ∧ a ≤ (2273/10000) ∧ ((1/16) + ((1/2))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (43/176) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((43/176) < a ∧ a ≤ (5/16) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((7/16) + (-1)*a)) ∧ ¬((17/88) < a ∧ a ≤ (7/32) ∧ ((17/88) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1977/8000) < a ∧ a ≤ (11931/40000) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((11931/40000) < a ∧ a ≤ (3/8) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((5/8) + ((-4/3))*a)) ∧ ¬((14431/40000) < a ∧ a ≤ (16477/40000) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((16477/40000) < a ∧ a ≤ (7/16) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((15/8) + (-4)*a)) ∧ ¬((18977/40000) < a ∧ a ≤ (1/2) ∧ ((17/8) + (-4)*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/2) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ ((1/4) + (0)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/3) ∧ ((1/4) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/3) < a ∧ a ≤ (1/2) ∧ ((1/4) + (0)*a) < b ∧ b ≤ ((1/2) + ((-1/2))*a)) := by
  obtain ⟨i1, i2, i3, i4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rintro ⟨j1, j2, j3, j4⟩
  all_goals linarith

/-- Piece `6b` excludes every other piece (pairwise disjointness of the thirteen regions). -/
private lemma excl_6b {a b : ℝ}
    (h : ((1/4) < a ∧ a ≤ (1/2) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ ((1/4) + (0)*a))) :
    ¬((17/88) < a ∧ a ≤ (9/40) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((9/40) < a ∧ a ≤ (2273/10000) ∧ ((1/16) + ((1/2))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (43/176) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((43/176) < a ∧ a ≤ (5/16) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((7/16) + (-1)*a)) ∧ ¬((17/88) < a ∧ a ≤ (7/32) ∧ ((17/88) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1977/8000) < a ∧ a ≤ (11931/40000) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((11931/40000) < a ∧ a ≤ (3/8) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((5/8) + ((-4/3))*a)) ∧ ¬((14431/40000) < a ∧ a ≤ (16477/40000) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((16477/40000) < a ∧ a ≤ (7/16) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((15/8) + (-4)*a)) ∧ ¬((18977/40000) < a ∧ a ≤ (1/2) ∧ ((17/8) + (-4)*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (1/4) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/3) ∧ ((1/4) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/3) < a ∧ a ≤ (1/2) ∧ ((1/4) + (0)*a) < b ∧ b ≤ ((1/2) + ((-1/2))*a)) := by
  obtain ⟨i1, i2, i3, i4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rintro ⟨j1, j2, j3, j4⟩
  all_goals linarith

/-- Piece `7a` excludes every other piece (pairwise disjointness of the thirteen regions). -/
private lemma excl_7a {a b : ℝ}
    (h : ((1/4) < a ∧ a ≤ (1/3) ∧ ((1/4) + (0)*a) < b ∧ b ≤ (0 + (1)*a))) :
    ¬((17/88) < a ∧ a ≤ (9/40) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((9/40) < a ∧ a ≤ (2273/10000) ∧ ((1/16) + ((1/2))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (43/176) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((43/176) < a ∧ a ≤ (5/16) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((7/16) + (-1)*a)) ∧ ¬((17/88) < a ∧ a ≤ (7/32) ∧ ((17/88) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1977/8000) < a ∧ a ≤ (11931/40000) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((11931/40000) < a ∧ a ≤ (3/8) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((5/8) + ((-4/3))*a)) ∧ ¬((14431/40000) < a ∧ a ≤ (16477/40000) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((16477/40000) < a ∧ a ≤ (7/16) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((15/8) + (-4)*a)) ∧ ¬((18977/40000) < a ∧ a ≤ (1/2) ∧ ((17/8) + (-4)*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (1/4) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/2) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ ((1/4) + (0)*a)) ∧ ¬((1/3) < a ∧ a ≤ (1/2) ∧ ((1/4) + (0)*a) < b ∧ b ≤ ((1/2) + ((-1/2))*a)) := by
  obtain ⟨i1, i2, i3, i4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rintro ⟨j1, j2, j3, j4⟩
  all_goals linarith

/-- Piece `7b` excludes every other piece (pairwise disjointness of the thirteen regions). -/
private lemma excl_7b {a b : ℝ}
    (h : ((1/3) < a ∧ a ≤ (1/2) ∧ ((1/4) + (0)*a) < b ∧ b ≤ ((1/2) + ((-1/2))*a))) :
    ¬((17/88) < a ∧ a ≤ (9/40) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((9/40) < a ∧ a ≤ (2273/10000) ∧ ((1/16) + ((1/2))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (43/176) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((17/88) + (0)*a)) ∧ ¬((43/176) < a ∧ a ≤ (5/16) ∧ ((17/56) + ((-4/7))*a) < b ∧ b ≤ ((7/16) + (-1)*a)) ∧ ¬((17/88) < a ∧ a ≤ (7/32) ∧ ((17/88) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1977/8000) < a ∧ a ≤ (11931/40000) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((11931/40000) < a ∧ a ≤ (3/8) ∧ ((17/40) + ((-4/5))*a) < b ∧ b ≤ ((5/8) + ((-4/3))*a)) ∧ ¬((14431/40000) < a ∧ a ≤ (16477/40000) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((16477/40000) < a ∧ a ≤ (7/16) ∧ ((17/24) + ((-4/3))*a) < b ∧ b ≤ ((15/8) + (-4)*a)) ∧ ¬((18977/40000) < a ∧ a ≤ (1/2) ∧ ((17/8) + (-4)*a) < b ∧ b ≤ ((2273/10000) + (0)*a)) ∧ ¬((2273/10000) < a ∧ a ≤ (1/4) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/2) ∧ ((2273/10000) + (0)*a) < b ∧ b ≤ ((1/4) + (0)*a)) ∧ ¬((1/4) < a ∧ a ≤ (1/3) ∧ ((1/4) + (0)*a) < b ∧ b ≤ (0 + (1)*a)) := by
  obtain ⟨i1, i2, i3, i4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rintro ⟨j1, j2, j3, j4⟩
  all_goals linarith

/-- The trapezoid indicator integrand is measurable. -/
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

set_option maxHeartbeats 8000000 in
/-- LEAF: the quadrature. The integral of `1 / (a b^2)` over the union of the three bands, as a
function of the plane, is at least `13/10`. The region is a fixed finite union of polygons cut out
by rational linear inequalities, so this is a computation about an explicit rational function; a
floating point quadrature gives about 1.4963, and an inner grid sum over cells inside the region
would prove it, in the same way as the certificate for the E2 sum. -/
theorem leaf_three_band_quadrature {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    13/10 ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0 := by
  set C : ℝ → ℝ → Prop := fun a b =>
      (2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b)) with hC
  have hCb : ∀ a b, C a b → (1/8:ℝ) ≤ b := by
    intro a b h
    simp only [hC] at h
    rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · linarith
    · exact h1
    · exact h1
  have hCa : ∀ a b, C a b → b ≤ a := by
    intro a b h
    simp only [hC] at h
    rcases h with ⟨-, h2, -⟩ | ⟨-, -, h2, -⟩ | ⟨-, -, h2, -⟩
    · exact h2
    · exact h2
    · exact h2
  have hCmeas : MeasurableSet {p : ℝ × ℝ | C p.1 p.2} := by
    rw [hC]
    simp only []
    exact three_band_region_measurable
  have hFmeas : Measurable (fun p : ℝ × ℝ => if C p.1 p.2 then (1:ℝ)/(p.1*p.2^2) else 0) :=
    Measurable.ite hCmeas (by fun_prop) measurable_const
  have hFb : ∀ a b, |(if C a b then (1:ℝ)/(a*b^2) else 0)| ≤ 1000 := by
    intro a b
    by_cases h : C a b
    · rw [if_pos h]
      have hb8 : (1/8:ℝ) ≤ b := hCb a b h
      have hba : b ≤ a := hCa a b h
      have hb2 : (1/64:ℝ) ≤ b^2 := by nlinarith
      have hmul : (1/8:ℝ)*(1/64) ≤ a*b^2 :=
        mul_le_mul (le_trans hb8 hba) hb2 (by norm_num) (by linarith)
      have hpos : 0 < a*b^2 := by linarith
      have hnn : 0 ≤ (1:ℝ)/(a*b^2) := by positivity
      rw [abs_of_nonneg hnn, div_le_iff₀ hpos]
      linarith
    · rw [if_neg h]
      norm_num
  have hinc_Q1a1 : ∀ a b, ((17/88):ℝ) ≤ a → a ≤ ((9/40):ℝ) →
      ((17/56) + ((-4/7))*a) ≤ b → b ≤ ((17/88) + (0)*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    refine Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩)
    · left
      linarith
    · right
      linarith
  have hinc_Q1a2a : ∀ a b, ((9/40):ℝ) ≤ a → a ≤ ((2273/10000):ℝ) →
      ((1/16) + ((1/2))*a) ≤ b → b ≤ ((17/88) + (0)*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    refine Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩)
    · left
      linarith
    · right
      linarith
  have hinc_Q1a2b : ∀ a b, ((2273/10000):ℝ) ≤ a → a ≤ ((43/176):ℝ) →
      ((17/56) + ((-4/7))*a) ≤ b → b ≤ ((17/88) + (0)*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    refine Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩)
    · left
      linarith
    · left
      linarith
  have hinc_Q1b : ∀ a b, ((43/176):ℝ) ≤ a → a ≤ ((5/16):ℝ) →
      ((17/56) + ((-4/7))*a) ≤ b → b ≤ ((7/16) + (-1)*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    refine Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩)
    · left
      linarith
    · left
      linarith
  have hinc_Q2 : ∀ a b, ((17/88):ℝ) ≤ a → a ≤ ((7/32):ℝ) →
      ((17/88) + (0)*a) ≤ b → b ≤ (0 + (1)*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    refine Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩)
    · left
      linarith
    · right
      linarith
  have hinc_Q3a : ∀ a b, ((1977/8000):ℝ) ≤ a → a ≤ ((11931/40000):ℝ) →
      ((17/40) + ((-4/5))*a) ≤ b → b ≤ ((2273/10000) + (0)*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    refine Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩)
    · right
      linarith
    · left
      linarith
  have hinc_Q3b : ∀ a b, ((11931/40000):ℝ) ≤ a → a ≤ ((3/8):ℝ) →
      ((17/40) + ((-4/5))*a) ≤ b → b ≤ ((5/8) + ((-4/3))*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    refine Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩)
    · right
      linarith
    · left
      linarith
  have hinc_Q4a : ∀ a b, ((14431/40000):ℝ) ≤ a → a ≤ ((16477/40000):ℝ) →
      ((17/24) + ((-4/3))*a) ≤ b → b ≤ ((2273/10000) + (0)*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    refine Or.inr (Or.inr ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, ?_⟩)
    left
    linarith
  have hinc_Q4b : ∀ a b, ((16477/40000):ℝ) ≤ a → a ≤ ((7/16):ℝ) →
      ((17/24) + ((-4/3))*a) ≤ b → b ≤ ((15/8) + (-4)*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    refine Or.inr (Or.inr ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, ?_⟩)
    left
    linarith
  have hinc_Q5 : ∀ a b, ((18977/40000):ℝ) ≤ a → a ≤ ((1/2):ℝ) →
      ((17/8) + (-4)*a) ≤ b → b ≤ ((2273/10000) + (0)*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    refine Or.inr (Or.inr ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, ?_⟩)
    right
    linarith
  have hinc_Q6a : ∀ a b, ((2273/10000):ℝ) ≤ a → a ≤ ((1/4):ℝ) →
      ((2273/10000) + (0)*a) ≤ b → b ≤ (0 + (1)*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    exact Or.inl ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hinc_Q6b : ∀ a b, ((1/4):ℝ) ≤ a → a ≤ ((1/2):ℝ) →
      ((2273/10000) + (0)*a) ≤ b → b ≤ ((1/4) + (0)*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    exact Or.inl ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hinc_Q7a : ∀ a b, ((1/4):ℝ) ≤ a → a ≤ ((1/3):ℝ) →
      ((1/4) + (0)*a) ≤ b → b ≤ (0 + (1)*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    exact Or.inl ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hinc_Q7b : ∀ a b, ((1/3):ℝ) ≤ a → a ≤ ((1/2):ℝ) →
      ((1/4) + (0)*a) ≤ b → b ≤ ((1/2) + ((-1/2))*a) → C a b := by
    intro a b ha1 ha2 hb1 hb2
    simp only [hC]
    exact Or.inl ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  -- ================= the fourteen trapezoid pieces of C =================
  let G1 : ℝ → ℝ → ℝ := fun a b =>
    (if ((17/88:ℝ) < a ∧ a ≤ (9/40:ℝ) ∧ ((17/56:ℝ) + (-4/7)*a) < b ∧ b ≤ ((17/88:ℝ) + (0:ℝ)*a)) then (1:ℝ)/(a*b^2) else 0)
  let G2 : ℝ → ℝ → ℝ := fun a b =>
    (if ((9/40:ℝ) < a ∧ a ≤ (2273/10000:ℝ) ∧ ((1/16:ℝ) + (1/2)*a) < b ∧ b ≤ ((17/88:ℝ) + (0:ℝ)*a)) then (1:ℝ)/(a*b^2) else 0)
  let G3 : ℝ → ℝ → ℝ := fun a b =>
    (if ((2273/10000:ℝ) < a ∧ a ≤ (43/176:ℝ) ∧ ((17/56:ℝ) + (-4/7)*a) < b ∧ b ≤ ((17/88:ℝ) + (0:ℝ)*a)) then (1:ℝ)/(a*b^2) else 0)
  let G4 : ℝ → ℝ → ℝ := fun a b =>
    (if ((43/176:ℝ) < a ∧ a ≤ (5/16:ℝ) ∧ ((17/56:ℝ) + (-4/7)*a) < b ∧ b ≤ ((7/16:ℝ) + (-1)*a)) then (1:ℝ)/(a*b^2) else 0)
  let G5 : ℝ → ℝ → ℝ := fun a b =>
    (if ((17/88:ℝ) < a ∧ a ≤ (7/32:ℝ) ∧ ((17/88:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((0:ℝ) + (1)*a)) then (1:ℝ)/(a*b^2) else 0)
  let G6 : ℝ → ℝ → ℝ := fun a b =>
    (if ((1977/8000:ℝ) < a ∧ a ≤ (11931/40000:ℝ) ∧ ((17/40:ℝ) + (-4/5)*a) < b ∧ b ≤ ((2273/10000:ℝ) + (0:ℝ)*a)) then (1:ℝ)/(a*b^2) else 0)
  let G7 : ℝ → ℝ → ℝ := fun a b =>
    (if ((11931/40000:ℝ) < a ∧ a ≤ (3/8:ℝ) ∧ ((17/40:ℝ) + (-4/5)*a) < b ∧ b ≤ ((5/8:ℝ) + (-4/3)*a)) then (1:ℝ)/(a*b^2) else 0)
  let G8 : ℝ → ℝ → ℝ := fun a b =>
    (if ((14431/40000:ℝ) < a ∧ a ≤ (16477/40000:ℝ) ∧ ((17/24:ℝ) + (-4/3)*a) < b ∧ b ≤ ((2273/10000:ℝ) + (0:ℝ)*a)) then (1:ℝ)/(a*b^2) else 0)
  let G9 : ℝ → ℝ → ℝ := fun a b =>
    (if ((16477/40000:ℝ) < a ∧ a ≤ (7/16:ℝ) ∧ ((17/24:ℝ) + (-4/3)*a) < b ∧ b ≤ ((15/8:ℝ) + (-4)*a)) then (1:ℝ)/(a*b^2) else 0)
  let G10 : ℝ → ℝ → ℝ := fun a b =>
    (if ((18977/40000:ℝ) < a ∧ a ≤ (1/2:ℝ) ∧ ((17/8:ℝ) + (-4)*a) < b ∧ b ≤ ((2273/10000:ℝ) + (0:ℝ)*a)) then (1:ℝ)/(a*b^2) else 0)
  let G11 : ℝ → ℝ → ℝ := fun a b =>
    (if ((2273/10000:ℝ) < a ∧ a ≤ (1/4:ℝ) ∧ ((2273/10000:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((0:ℝ) + (1)*a)) then (1:ℝ)/(a*b^2) else 0)
  let G12 : ℝ → ℝ → ℝ := fun a b =>
    (if ((1/4:ℝ) < a ∧ a ≤ (1/2:ℝ) ∧ ((2273/10000:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((1/4:ℝ) + (0:ℝ)*a)) then (1:ℝ)/(a*b^2) else 0)
  let G13 : ℝ → ℝ → ℝ := fun a b =>
    (if ((1/4:ℝ) < a ∧ a ≤ (1/3:ℝ) ∧ ((1/4:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((0:ℝ) + (1)*a)) then (1:ℝ)/(a*b^2) else 0)
  let G14 : ℝ → ℝ → ℝ := fun a b =>
    (if ((1/3:ℝ) < a ∧ a ≤ (1/2:ℝ) ∧ ((1/4:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((1/2:ℝ) + (-1/2)*a)) then (1:ℝ)/(a*b^2) else 0)

  obtain ⟨nm1, nb1, nn1, ni1, nI1, nJ1, no1, ne1⟩ := piece_G_all
      (A1 := (17/88:ℝ)) (A2 := (9/40:ℝ)) (c := (17/56:ℝ)) (e := (-4/7)) (f := (17/88:ℝ)) (g := (0:ℝ))
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
      = ∫ a in (17/88:ℝ)..(9/40:ℝ), (1/a)*(1/((17/56:ℝ) + (-4/7)*a) - 1/((17/88:ℝ) + (0:ℝ)*a)) := ne1
  have zZ1 : ∀ a b : ℝ, ¬((17/88:ℝ) < a ∧ a ≤ (9/40:ℝ) ∧ ((17/56:ℝ) + (-4/7)*a) < b ∧ b ≤ ((17/88:ℝ) + (0:ℝ)*a)) → G1 a b = 0 := fun a b h => if_neg h
  have vV1 : ∀ a b : ℝ, ((17/88:ℝ) < a ∧ a ≤ (9/40:ℝ) ∧ ((17/56:ℝ) + (-4/7)*a) < b ∧ b ≤ ((17/88:ℝ) + (0:ℝ)*a)) → G1 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P1 : (311/10000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G1 a b := by
    rw [ev1]
    linarith [Q1a1_lower,
      (show (311/10000:ℝ) ≤ ((50176/30343555) + (404608/38573255) + (5055232/265668231) : ℝ) by norm_num)]
  obtain ⟨nm2, nb2, nn2, ni2, nI2, nJ2, no2, ne2⟩ := piece_G_all
      (A1 := (9/40:ℝ)) (A2 := (2273/10000:ℝ)) (c := (1/16:ℝ)) (e := (1/2)) (f := (17/88:ℝ)) (g := (0:ℝ))
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
      = ∫ a in (9/40:ℝ)..(2273/10000:ℝ), (1/a)*(1/((1/16:ℝ) + (1/2)*a) - 1/((17/88:ℝ) + (0:ℝ)*a)) := ne2
  have zZ2 : ∀ a b : ℝ, ¬((9/40:ℝ) < a ∧ a ≤ (2273/10000:ℝ) ∧ ((1/16:ℝ) + (1/2)*a) < b ∧ b ≤ ((17/88:ℝ) + (0:ℝ)*a)) → G2 a b = 0 := fun a b h => if_neg h
  have vV2 : ∀ a b : ℝ, ((9/40:ℝ) < a ∧ a ≤ (2273/10000:ℝ) ∧ ((1/16:ℝ) + (1/2)*a) < b ∧ b ≤ ((17/88:ℝ) + (0:ℝ)*a)) → G2 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P2 : (52/10000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b := by
    rw [ev2]
    linarith [Q1a2a_lower,
      (show (52/10000:ℝ) ≤ ((3838173215222/2137313692817625) + (6387336391712762056/3655193602209274804921) + (349768432925397028/205787986266743240171) : ℝ) by norm_num)]
  obtain ⟨nm3, nb3, nn3, ni3, nI3, nJ3, no3, ne3⟩ := piece_G_all
      (A1 := (2273/10000:ℝ)) (A2 := (43/176:ℝ)) (c := (17/56:ℝ)) (e := (-4/7)) (f := (17/88:ℝ)) (g := (0:ℝ))
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
      = ∫ a in (2273/10000:ℝ)..(43/176:ℝ), (1/a)*(1/((17/56:ℝ) + (-4/7)*a) - 1/((17/88:ℝ) + (0:ℝ)*a)) := ne3
  have zZ3 : ∀ a b : ℝ, ¬((2273/10000:ℝ) < a ∧ a ≤ (43/176:ℝ) ∧ ((17/56:ℝ) + (-4/7)*a) < b ∧ b ≤ ((17/88:ℝ) + (0:ℝ)*a)) → G3 a b = 0 := fun a b h => if_neg h
  have vV3 : ∀ a b : ℝ, ((2273/10000:ℝ) < a ∧ a ≤ (43/176:ℝ) ∧ ((17/56:ℝ) + (-4/7)*a) < b ∧ b ≤ ((17/88:ℝ) + (0:ℝ)*a)) → G3 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P3 : (522/10000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b := by
    rw [ev3]
    linarith [Q1a2b_lower,
      (show (522/10000:ℝ) ≤ ((4018789322496/266464634694533) + (32055843485952/1840446963121235) + (35809110395136/1813556639676419) : ℝ) by norm_num)]
  obtain ⟨nm4, nb4, nn4, ni4, nI4, nJ4, no4, ne4⟩ := piece_G_all
      (A1 := (43/176:ℝ)) (A2 := (5/16:ℝ)) (c := (17/56:ℝ)) (e := (-4/7)) (f := (7/16:ℝ)) (g := (-1))
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
      = ∫ a in (43/176:ℝ)..(5/16:ℝ), (1/a)*(1/((17/56:ℝ) + (-4/7)*a) - 1/((7/16:ℝ) + (-1)*a)) := ne4
  have zZ4 : ∀ a b : ℝ, ¬((43/176:ℝ) < a ∧ a ≤ (5/16:ℝ) ∧ ((17/56:ℝ) + (-4/7)*a) < b ∧ b ≤ ((7/16:ℝ) + (-1)*a)) → G4 a b = 0 := fun a b h => if_neg h
  have vV4 : ∀ a b : ℝ, ((43/176:ℝ) < a ∧ a ≤ (5/16:ℝ) ∧ ((17/56:ℝ) + (-4/7)*a) < b ∧ b ≤ ((7/16:ℝ) + (-1)*a)) → G4 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P4 : (1357/10000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b := by
    rw [ev4]
    linarith [Q1b_lower,
      (show (1357/10000:ℝ) ≤ ((10294031/140576345) + (906796/18819697) + (94/6545) : ℝ) by norm_num)]
  obtain ⟨nm5, nb5, nn5, ni5, nI5, nJ5, no5, ne5⟩ := piece_G_all
      (A1 := (17/88:ℝ)) (A2 := (7/32:ℝ)) (c := (17/88:ℝ)) (e := (0:ℝ)) (f := (0:ℝ)) (g := (1))
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
      = ∫ a in (17/88:ℝ)..(7/32:ℝ), (1/a)*(1/((17/88:ℝ) + (0:ℝ)*a) - 1/((0:ℝ) + (1)*a)) := ne5
  have zZ5 : ∀ a b : ℝ, ¬((17/88:ℝ) < a ∧ a ≤ (7/32:ℝ) ∧ ((17/88:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((0:ℝ) + (1)*a)) → G5 a b = 0 := fun a b h => if_neg h
  have vV5 : ∀ a b : ℝ, ((17/88:ℝ) < a ∧ a ≤ (7/32:ℝ) ∧ ((17/88:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((0:ℝ) + (1)*a)) → G5 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P5 : (383/10000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b := by
    rw [ev5]
    linarith [Q2_lower,
      (show (383/10000:ℝ) ≤ ((40248/8479175) + (49691664/3755419969) + (8183088/401531585) : ℝ) by norm_num)]
  obtain ⟨nm6, nb6, nn6, ni6, nI6, nJ6, no6, ne6⟩ := piece_G_all
      (A1 := (1977/8000:ℝ)) (A2 := (11931/40000:ℝ)) (c := (17/40:ℝ)) (e := (-4/5)) (f := (2273/10000:ℝ)) (g := (0:ℝ))
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
      = ∫ a in (1977/8000:ℝ)..(11931/40000:ℝ), (1/a)*(1/((17/40:ℝ) + (-4/5)*a) - 1/((2273/10000:ℝ) + (0:ℝ)*a)) := ne6
  have zZ6 : ∀ a b : ℝ, ¬((1977/8000:ℝ) < a ∧ a ≤ (11931/40000:ℝ) ∧ ((17/40:ℝ) + (-4/5)*a) < b ∧ b ≤ ((2273/10000:ℝ) + (0:ℝ)*a)) → G6 a b = 0 := fun a b h => if_neg h
  have vV6 : ∀ a b : ℝ, ((1977/8000:ℝ) < a ∧ a ≤ (11931/40000:ℝ) ∧ ((17/40:ℝ) + (-4/5)*a) < b ∧ b ≤ ((2273/10000:ℝ) + (0:ℝ)*a)) → G6 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P6 : (696/10000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b := by
    rw [ev6]
    linarith [Q3a_lower,
      (show (696/10000:ℝ) ≤ ((82674860752/18779449606743) + (807616555979728/34928590755899805) + (401618396987280/9540964534350263) : ℝ) by norm_num)]
  obtain ⟨nm7, nb7, nn7, ni7, nI7, nJ7, no7, ne7⟩ := piece_G_all
      (A1 := (11931/40000:ℝ)) (A2 := (3/8:ℝ)) (c := (17/40:ℝ)) (e := (-4/5)) (f := (5/8:ℝ)) (g := (-4/3))
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
      = ∫ a in (11931/40000:ℝ)..(3/8:ℝ), (1/a)*(1/((17/40:ℝ) + (-4/5)*a) - 1/((5/8:ℝ) + (-4/3)*a)) := ne7
  have zZ7 : ∀ a b : ℝ, ¬((11931/40000:ℝ) < a ∧ a ≤ (3/8:ℝ) ∧ ((17/40:ℝ) + (-4/5)*a) < b ∧ b ≤ ((5/8:ℝ) + (-4/3)*a)) → G7 a b = 0 := fun a b h => if_neg h
  have vV7 : ∀ a b : ℝ, ((11931/40000:ℝ) < a ∧ a ≤ (3/8:ℝ) ∧ ((17/40:ℝ) + (-4/5)*a) < b ∧ b ≤ ((5/8:ℝ) + (-4/3)*a)) → G7 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P7 : (1435/10000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b := by
    rw [ev7]
    linarith [Q3b_lower,
      (show (1435/10000:ℝ) ≤ ((104268403197110185000/1416486720497657845911) + (1476450586870572500/27943260787362174777) + (1362204937808/79595609210691) : ℝ) by norm_num)]
  obtain ⟨nm8, nb8, nn8, ni8, nI8, nJ8, no8, ne8⟩ := piece_G_all
      (A1 := (14431/40000:ℝ)) (A2 := (16477/40000:ℝ)) (c := (17/24:ℝ)) (e := (-4/3)) (f := (2273/10000:ℝ)) (g := (0:ℝ))
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
      = ∫ a in (14431/40000:ℝ)..(16477/40000:ℝ), (1/a)*(1/((17/24:ℝ) + (-4/3)*a) - 1/((2273/10000:ℝ) + (0:ℝ)*a)) := ne8
  have zZ8 : ∀ a b : ℝ, ¬((14431/40000:ℝ) < a ∧ a ≤ (16477/40000:ℝ) ∧ ((17/24:ℝ) + (-4/3)*a) < b ∧ b ≤ ((2273/10000:ℝ) + (0:ℝ)*a)) → G8 a b = 0 := fun a b h => if_neg h
  have vV8 : ∀ a b : ℝ, ((14431/40000:ℝ) < a ∧ a ≤ (16477/40000:ℝ) ∧ ((17/24:ℝ) + (-4/3)*a) < b ∧ b ≤ ((2273/10000:ℝ) + (0:ℝ)*a)) → G8 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P8 : (984/10000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b := by
    rw [ev8]
    linarith [Q4a_lower,
      (show (984/10000:ℝ) ≤ ((16281200496/2160568430285) + (2464802356900400/78404286100316239) + (97264894570448/1635316476147315) : ℝ) by norm_num)]
  obtain ⟨nm9, nb9, nn9, ni9, nI9, nJ9, no9, ne9⟩ := piece_G_all
      (A1 := (16477/40000:ℝ)) (A2 := (7/16:ℝ)) (c := (17/24:ℝ)) (e := (-4/3)) (f := (15/8:ℝ)) (g := (-4))
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
      = ∫ a in (16477/40000:ℝ)..(7/16:ℝ), (1/a)*(1/((17/24:ℝ) + (-4/3)*a) - 1/((15/8:ℝ) + (-4)*a)) := ne9
  have zZ9 : ∀ a b : ℝ, ¬((16477/40000:ℝ) < a ∧ a ≤ (7/16:ℝ) ∧ ((17/24:ℝ) + (-4/3)*a) < b ∧ b ≤ ((15/8:ℝ) + (-4)*a)) → G9 a b = 0 := fun a b h => if_neg h
  have vV9 : ∀ a b : ℝ, ((16477/40000:ℝ) < a ∧ a ≤ (7/16:ℝ) ∧ ((17/24:ℝ) + (-4/3)*a) < b ∧ b ≤ ((15/8:ℝ) + (-4)*a)) → G9 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P9 : (620/10000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b := by
    rw [ev9]
    linarith [Q4b_lower,
      (show (620/10000:ℝ) ≤ ((37334645790762595000/1105032230220741200469) + (17580420557026401250/749275331387737534983) + (13941844454032/2900939235395175) : ℝ) by norm_num)]
  obtain ⟨nm10, nb10, nn10, ni10, nI10, nJ10, no10, ne10⟩ := piece_G_all
      (A1 := (18977/40000:ℝ)) (A2 := (1/2:ℝ)) (c := (17/8:ℝ)) (e := (-4)) (f := (2273/10000:ℝ)) (g := (0:ℝ))
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
      = ∫ a in (18977/40000:ℝ)..(1/2:ℝ), (1/a)*(1/((17/8:ℝ) + (-4)*a) - 1/((2273/10000:ℝ) + (0:ℝ)*a)) := ne10
  have zZ10 : ∀ a b : ℝ, ¬((18977/40000:ℝ) < a ∧ a ≤ (1/2:ℝ) ∧ ((17/8:ℝ) + (-4)*a) < b ∧ b ≤ ((2273/10000:ℝ) + (0:ℝ)*a)) → G10 a b = 0 := fun a b h => if_neg h
  have vV10 : ∀ a b : ℝ, ((18977/40000:ℝ) < a ∧ a ≤ (1/2:ℝ) ∧ ((17/8:ℝ) + (-4)*a) < b ∧ b ≤ ((2273/10000:ℝ) + (0:ℝ)*a)) → G10 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P10 : (730/10000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b := by
    rw [ev10]
    linarith [Q5_lower,
      (show (730/10000:ℝ) ≤ ((15963985928/2728511297979) + (23880151287652/1087422921150345) + (1105195820364680/24436849881794217) : ℝ) by norm_num)]
  obtain ⟨nm11, nb11, nn11, ni11, nI11, nJ11, no11, ne11⟩ := piece_G_all
      (A1 := (2273/10000:ℝ)) (A2 := (1/4:ℝ)) (c := (2273/10000:ℝ)) (e := (0:ℝ)) (f := (0:ℝ)) (g := (1))
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
      = ∫ a in (2273/10000:ℝ)..(1/4:ℝ), (1/a)*(1/((2273/10000:ℝ) + (0:ℝ)*a) - 1/((0:ℝ) + (1)*a)) := ne11
  have zZ11 : ∀ a b : ℝ, ¬((2273/10000:ℝ) < a ∧ a ≤ (1/4:ℝ) ∧ ((2273/10000:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((0:ℝ) + (1)*a)) → G11 a b = 0 := fun a b h => if_neg h
  have vV11 : ∀ a b : ℝ, ((2273/10000:ℝ) < a ∧ a ≤ (1/4:ℝ) ∧ ((2273/10000:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((0:ℝ) + (1)*a)) → G11 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P11 : (193/10000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b := by
    rw [ev11]
    linarith [Q6a_lower,
      (show (193/10000:ℝ) ≤ ((14347477115000/6157192251765009) + (63135889369437000/9552427365740068901) + (149589117164092/14430612809513523) : ℝ) by norm_num)]
  obtain ⟨nm12, nb12, nn12, ni12, nI12, nJ12, no12, ne12⟩ := piece_G_all
      (A1 := (1/4:ℝ)) (A2 := (1/2:ℝ)) (c := (2273/10000:ℝ)) (e := (0:ℝ)) (f := (1/4:ℝ)) (g := (0:ℝ))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have mb12 : Measurable (fun p : ℝ × ℝ => G12 p.1 p.2) := nm12
  have mB12 : ∀ a b : ℝ, |G12 a b| ≤ 1000 := nb12
  have mN12 : ∀ a b : ℝ, 0 ≤ G12 a b := nn12
  have mI12 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => G12 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := ni12
  have lv12 : Measurable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b) := nI12
  have lb12 : ∀ a : ℝ, |∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b| ≤ 1000 := nJ12
  have li12 : IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := no12
  have ev12 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b)
      = ∫ a in (1/4:ℝ)..(1/2:ℝ), (1/a)*(1/((2273/10000:ℝ) + (0:ℝ)*a) - 1/((1/4:ℝ) + (0:ℝ)*a)) := ne12
  have zZ12 : ∀ a b : ℝ, ¬((1/4:ℝ) < a ∧ a ≤ (1/2:ℝ) ∧ ((2273/10000:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((1/4:ℝ) + (0:ℝ)*a)) → G12 a b = 0 := fun a b h => if_neg h
  have vV12 : ∀ a b : ℝ, ((1/4:ℝ) < a ∧ a ≤ (1/2:ℝ) ∧ ((2273/10000:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((1/4:ℝ) + (0:ℝ)*a)) → G12 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P12 : (2765/10000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b := by
    rw [ev12]
    linarith [Q6b_lower,
      (show (2765/10000:ℝ) ≤ ((50848/443235) + (65376/734179) + (79904/1097859) : ℝ) by norm_num)]
  obtain ⟨nm13, nb13, nn13, ni13, nI13, nJ13, no13, ne13⟩ := piece_G_all
      (A1 := (1/4:ℝ)) (A2 := (1/3:ℝ)) (c := (1/4:ℝ)) (e := (0:ℝ)) (f := (0:ℝ)) (g := (1))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have mb13 : Measurable (fun p : ℝ × ℝ => G13 p.1 p.2) := nm13
  have mB13 : ∀ a b : ℝ, |G13 a b| ≤ 1000 := nb13
  have mN13 : ∀ a b : ℝ, 0 ≤ G13 a b := nn13
  have mI13 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => G13 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := ni13
  have lv13 : Measurable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) := nI13
  have lb13 : ∀ a : ℝ, |∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b| ≤ 1000 := nJ13
  have li13 : IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := no13
  have ev13 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b)
      = ∫ a in (1/4:ℝ)..(1/3:ℝ), (1/a)*(1/((1/4:ℝ) + (0:ℝ)*a) - 1/((0:ℝ) + (1)*a)) := ne13
  have zZ13 : ∀ a b : ℝ, ¬((1/4:ℝ) < a ∧ a ≤ (1/3:ℝ) ∧ ((1/4:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((0:ℝ) + (1)*a)) → G13 a b = 0 := fun a b h => if_neg h
  have vV13 : ∀ a b : ℝ, ((1/4:ℝ) < a ∧ a ≤ (1/3:ℝ) ∧ ((1/4:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((0:ℝ) + (1)*a)) → G13 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P13 : (1505/10000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b := by
    rw [ev13]
    linarith [Q7a_lower,
      (show (1505/10000:ℝ) ≤ ((154/7215) + (5226/96965) + (1751/23265) : ℝ) by norm_num)]
  obtain ⟨nm14, nb14, nn14, ni14, nI14, nJ14, no14, ne14⟩ := piece_G_all
      (A1 := (1/3:ℝ)) (A2 := (1/2:ℝ)) (c := (1/4:ℝ)) (e := (0:ℝ)) (f := (1/2:ℝ)) (g := (-1/2))
      (by norm_num) (by norm_num) (by norm_num)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith) (fun a _ _ => by linarith)
      (fun a _ _ => by linarith) (fun a _ _ => by linarith)
  have mb14 : Measurable (fun p : ℝ × ℝ => G14 p.1 p.2) := nm14
  have mB14 : ∀ a b : ℝ, |G14 a b| ≤ 1000 := nb14
  have mN14 : ∀ a b : ℝ, 0 ≤ G14 a b := nn14
  have mI14 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => G14 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := ni14
  have lv14 : Measurable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b) := nI14
  have lb14 : ∀ a : ℝ, |∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b| ≤ 1000 := nJ14
  have li14 : IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := no14
  have ev14 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b)
      = ∫ a in (1/3:ℝ)..(1/2:ℝ), (1/a)*(1/((1/4:ℝ) + (0:ℝ)*a) - 1/((1/2:ℝ) + (-1/2)*a)) := ne14
  have zZ14 : ∀ a b : ℝ, ¬((1/3:ℝ) < a ∧ a ≤ (1/2:ℝ) ∧ ((1/4:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((1/2:ℝ) + (-1/2)*a)) → G14 a b = 0 := fun a b h => if_neg h
  have vV14 : ∀ a b : ℝ, ((1/3:ℝ) < a ∧ a ≤ (1/2:ℝ) ∧ ((1/4:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((1/2:ℝ) + (-1/2)*a)) → G14 a b = (1:ℝ)/(a*b^2) := fun a b h => if_pos h
  have P14 : (1911/10000:ℝ) ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b := by
    rw [ev14]
    linarith [Q7b_lower,
      (show (1911/10000:ℝ) ≤ (362:ℝ)/2261 + 45/1449 by norm_num)]

  -- ---- at most one piece is active, and each active piece lies in C ----
  have hSle : ∀ a b : ℝ, (G1 a b + (G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + (G11 a b + (G12 a b + (G13 a b + (G14 a b)))))))))))))) ≤ (if C a b then (1:ℝ)/(a*b^2) else 0) := by
    intro a b
    by_cases h1 : ((17/88:ℝ) < a ∧ a ≤ (9/40:ℝ) ∧ ((17/56:ℝ) + (-4/7)*a) < b ∧ b ≤ ((17/88:ℝ) + (0:ℝ)*a))
    · rw [vV1 a b h1, zZ2 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ3 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ4 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ5 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ6 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ7 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ8 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ9 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ10 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ12 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ13 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ14 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), if_pos (hinc_Q1a1 a b (le_of_lt h1.1) h1.2.1 (le_of_lt h1.2.2.1) h1.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h2 : ((9/40:ℝ) < a ∧ a ≤ (2273/10000:ℝ) ∧ ((1/16:ℝ) + (1/2)*a) < b ∧ b ≤ ((17/88:ℝ) + (0:ℝ)*a))
    · rw [zZ1 a b h1, vV2 a b h2, zZ3 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ4 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ5 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ6 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ7 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ8 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ9 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ10 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ12 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ13 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ14 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), if_pos (hinc_Q1a2a a b (le_of_lt h2.1) h2.2.1 (le_of_lt h2.2.2.1) h2.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h3 : ((2273/10000:ℝ) < a ∧ a ≤ (43/176:ℝ) ∧ ((17/56:ℝ) + (-4/7)*a) < b ∧ b ≤ ((17/88:ℝ) + (0:ℝ)*a))
    · rw [zZ1 a b h1, zZ2 a b h2, vV3 a b h3, zZ4 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ5 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ6 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ7 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ8 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ9 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ10 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ12 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ13 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ14 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), if_pos (hinc_Q1a2b a b (le_of_lt h3.1) h3.2.1 (le_of_lt h3.2.2.1) h3.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h4 : ((43/176:ℝ) < a ∧ a ≤ (5/16:ℝ) ∧ ((17/56:ℝ) + (-4/7)*a) < b ∧ b ≤ ((7/16:ℝ) + (-1)*a))
    · rw [zZ1 a b h1, zZ2 a b h2, zZ3 a b h3, vV4 a b h4, zZ5 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ6 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ7 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ8 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ9 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ10 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ12 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ13 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ14 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), if_pos (hinc_Q1b a b (le_of_lt h4.1) h4.2.1 (le_of_lt h4.2.2.1) h4.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h5 : ((17/88:ℝ) < a ∧ a ≤ (7/32:ℝ) ∧ ((17/88:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((0:ℝ) + (1)*a))
    · rw [zZ1 a b h1, zZ2 a b h2, zZ3 a b h3, zZ4 a b h4, vV5 a b h5, zZ6 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ7 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ8 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ9 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ10 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ12 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ13 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ14 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), if_pos (hinc_Q2 a b (le_of_lt h5.1) h5.2.1 (le_of_lt h5.2.2.1) h5.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h6 : ((1977/8000:ℝ) < a ∧ a ≤ (11931/40000:ℝ) ∧ ((17/40:ℝ) + (-4/5)*a) < b ∧ b ≤ ((2273/10000:ℝ) + (0:ℝ)*a))
    · rw [zZ1 a b h1, zZ2 a b h2, zZ3 a b h3, zZ4 a b h4, zZ5 a b h5, vV6 a b h6, zZ7 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ8 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ9 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ10 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ12 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ13 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ14 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), if_pos (hinc_Q3a a b (le_of_lt h6.1) h6.2.1 (le_of_lt h6.2.2.1) h6.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h7 : ((11931/40000:ℝ) < a ∧ a ≤ (3/8:ℝ) ∧ ((17/40:ℝ) + (-4/5)*a) < b ∧ b ≤ ((5/8:ℝ) + (-4/3)*a))
    · rw [zZ1 a b h1, zZ2 a b h2, zZ3 a b h3, zZ4 a b h4, zZ5 a b h5, zZ6 a b h6, vV7 a b h7, zZ8 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ9 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ10 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ12 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ13 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ14 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), if_pos (hinc_Q3b a b (le_of_lt h7.1) h7.2.1 (le_of_lt h7.2.2.1) h7.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h8 : ((14431/40000:ℝ) < a ∧ a ≤ (16477/40000:ℝ) ∧ ((17/24:ℝ) + (-4/3)*a) < b ∧ b ≤ ((2273/10000:ℝ) + (0:ℝ)*a))
    · rw [zZ1 a b h1, zZ2 a b h2, zZ3 a b h3, zZ4 a b h4, zZ5 a b h5, zZ6 a b h6, zZ7 a b h7, vV8 a b h8, zZ9 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ10 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ12 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ13 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ14 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), if_pos (hinc_Q4a a b (le_of_lt h8.1) h8.2.1 (le_of_lt h8.2.2.1) h8.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h9 : ((16477/40000:ℝ) < a ∧ a ≤ (7/16:ℝ) ∧ ((17/24:ℝ) + (-4/3)*a) < b ∧ b ≤ ((15/8:ℝ) + (-4)*a))
    · rw [zZ1 a b h1, zZ2 a b h2, zZ3 a b h3, zZ4 a b h4, zZ5 a b h5, zZ6 a b h6, zZ7 a b h7, zZ8 a b h8, vV9 a b h9, zZ10 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ12 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ13 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ14 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), if_pos (hinc_Q4b a b (le_of_lt h9.1) h9.2.1 (le_of_lt h9.2.2.1) h9.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h10 : ((18977/40000:ℝ) < a ∧ a ≤ (1/2:ℝ) ∧ ((17/8:ℝ) + (-4)*a) < b ∧ b ≤ ((2273/10000:ℝ) + (0:ℝ)*a))
    · rw [zZ1 a b h1, zZ2 a b h2, zZ3 a b h3, zZ4 a b h4, zZ5 a b h5, zZ6 a b h6, zZ7 a b h7, zZ8 a b h8, zZ9 a b h9, vV10 a b h10, zZ11 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ12 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ13 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ14 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), if_pos (hinc_Q5 a b (le_of_lt h10.1) h10.2.1 (le_of_lt h10.2.2.1) h10.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h11 : ((2273/10000:ℝ) < a ∧ a ≤ (1/4:ℝ) ∧ ((2273/10000:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((0:ℝ) + (1)*a))
    · rw [zZ1 a b h1, zZ2 a b h2, zZ3 a b h3, zZ4 a b h4, zZ5 a b h5, zZ6 a b h6, zZ7 a b h7, zZ8 a b h8, zZ9 a b h9, zZ10 a b h10, vV11 a b h11, zZ12 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ13 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ14 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), if_pos (hinc_Q6a a b (le_of_lt h11.1) h11.2.1 (le_of_lt h11.2.2.1) h11.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h12 : ((1/4:ℝ) < a ∧ a ≤ (1/2:ℝ) ∧ ((2273/10000:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((1/4:ℝ) + (0:ℝ)*a))
    · rw [zZ1 a b h1, zZ2 a b h2, zZ3 a b h3, zZ4 a b h4, zZ5 a b h5, zZ6 a b h6, zZ7 a b h7, zZ8 a b h8, zZ9 a b h9, zZ10 a b h10, zZ11 a b h11, vV12 a b h12, zZ13 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), zZ14 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), if_pos (hinc_Q6b a b (le_of_lt h12.1) h12.2.1 (le_of_lt h12.2.2.1) h12.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h13 : ((1/4:ℝ) < a ∧ a ≤ (1/3:ℝ) ∧ ((1/4:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((0:ℝ) + (1)*a))
    · rw [zZ1 a b h1, zZ2 a b h2, zZ3 a b h3, zZ4 a b h4, zZ5 a b h5, zZ6 a b h6, zZ7 a b h7, zZ8 a b h8, zZ9 a b h9, zZ10 a b h10, zZ11 a b h11, zZ12 a b h12, vV13 a b h13, zZ14 a b (by rintro ⟨j1, j2, j3, j4⟩; linarith), if_pos (hinc_Q7a a b (le_of_lt h13.1) h13.2.1 (le_of_lt h13.2.2.1) h13.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    by_cases h14 : ((1/3:ℝ) < a ∧ a ≤ (1/2:ℝ) ∧ ((1/4:ℝ) + (0:ℝ)*a) < b ∧ b ≤ ((1/2:ℝ) + (-1/2)*a))
    · rw [zZ1 a b h1, zZ2 a b h2, zZ3 a b h3, zZ4 a b h4, zZ5 a b h5, zZ6 a b h6, zZ7 a b h7, zZ8 a b h8, zZ9 a b h9, zZ10 a b h10, zZ11 a b h11, zZ12 a b h12, zZ13 a b h13, vV14 a b h14, if_pos (hinc_Q7b a b (le_of_lt h14.1) h14.2.1 (le_of_lt h14.2.2.1) h14.2.2.2)]
      simp only [zero_add, add_zero, le_refl]
    · rw [zZ1 a b h1, zZ2 a b h2, zZ3 a b h3, zZ4 a b h4, zZ5 a b h5, zZ6 a b h6, zZ7 a b h7, zZ8 a b h8, zZ9 a b h9, zZ10 a b h10, zZ11 a b h11, zZ12 a b h12, zZ13 a b h13, zZ14 a b h14]
      simp only [zero_add, add_zero]
      by_cases hC2 : C a b
      · rw [if_pos hC2]
        exact le_of_lt (one_div_pos.mpr (by nlinarith [hCa a b hC2, hCb a b hC2]))
      · rw [if_neg hC2]

  have hSb : ∀ a b : ℝ, |(G1 a b + (G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + (G11 a b + (G12 a b + (G13 a b + (G14 a b))))))))))))))| ≤ 14000 := by
    intro a b
    have h0 : 0 ≤ (G1 a b + (G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + (G11 a b + (G12 a b + (G13 a b + (G14 a b)))))))))))))) := by linarith [mN1 a b, mN2 a b, mN3 a b, mN4 a b, mN5 a b, mN6 a b, mN7 a b, mN8 a b, mN9 a b, mN10 a b, mN11 a b, mN12 a b, mN13 a b, mN14 a b]
    rw [abs_of_nonneg h0]
    have hF := abs_le.mp (hFb a b)
    have hS := hSle a b
    linarith

  have hSmeas : Measurable (fun p : ℝ × ℝ => (G1 p.1 p.2 + (G2 p.1 p.2 + (G3 p.1 p.2 + (G4 p.1 p.2 + (G5 p.1 p.2 + (G6 p.1 p.2 + (G7 p.1 p.2 + (G8 p.1 p.2 + (G9 p.1 p.2 + (G10 p.1 p.2 + (G11 p.1 p.2 + (G12 p.1 p.2 + (G13 p.1 p.2 + (G14 p.1 p.2))))))))))))))) :=
    mb1.add (mb2.add (mb3.add (mb4.add (mb5.add (mb6.add (mb7.add (mb8.add (mb9.add (mb10.add (mb11.add (mb12.add (mb13.add (mb14)))))))))))))

  -- ---- additivity of the iterated integral over the fourteen pieces ----
  have sfb14 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => G14 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := mI14
  have sfb13 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => (G13 a b + (G14 a b))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI13 a).add (sfb14 a)
  have sfb12 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => (G12 a b + (G13 a b + (G14 a b)))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI12 a).add (sfb13 a)
  have sfb11 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => (G11 a b + (G12 a b + (G13 a b + (G14 a b))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI11 a).add (sfb12 a)
  have sfb10 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => (G10 a b + (G11 a b + (G12 a b + (G13 a b + (G14 a b)))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI10 a).add (sfb11 a)
  have sfb9 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => (G9 a b + (G10 a b + (G11 a b + (G12 a b + (G13 a b + (G14 a b))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI9 a).add (sfb10 a)
  have sfb8 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => (G8 a b + (G9 a b + (G10 a b + (G11 a b + (G12 a b + (G13 a b + (G14 a b)))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI8 a).add (sfb9 a)
  have sfb7 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => (G7 a b + (G8 a b + (G9 a b + (G10 a b + (G11 a b + (G12 a b + (G13 a b + (G14 a b))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI7 a).add (sfb8 a)
  have sfb6 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + (G11 a b + (G12 a b + (G13 a b + (G14 a b)))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI6 a).add (sfb7 a)
  have sfb5 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + (G11 a b + (G12 a b + (G13 a b + (G14 a b))))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI5 a).add (sfb6 a)
  have sfb4 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + (G11 a b + (G12 a b + (G13 a b + (G14 a b)))))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI4 a).add (sfb5 a)
  have sfb3 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + (G11 a b + (G12 a b + (G13 a b + (G14 a b))))))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI3 a).add (sfb4 a)
  have sfb2 : ∀ a : ℝ, IntervalIntegrable (fun b : ℝ => (G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + (G11 a b + (G12 a b + (G13 a b + (G14 a b)))))))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    fun a => (mI2 a).add (sfb3 a)

  have hinner : ∀ a : ℝ, (∫ b in (1/10:ℝ)..(1/2:ℝ), (G1 a b + (G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + (G11 a b + (G12 a b + (G13 a b + (G14 a b))))))))))))))) = 
      ((∫ b in (1/10:ℝ)..(1/2:ℝ), G1 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b))))))))))))))) := by
    intro a
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add] <;>
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
        | simpa only [] using mI12 a
        | simpa only [] using mI13 a
        | simpa only [] using mI14 a
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
        | simpa only [] using sfb12 a
        | simpa only [] using sfb13 a
        | simpa only [] using sfb14 a

  have sfa14 : IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) := li14
  have sfa13 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b)))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li13).add (sfa14)
  have sfa12 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li12).add (sfa13)
  have sfa11 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b)))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li11).add (sfa12)
  have sfa10 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li10).add (sfa11)
  have sfa9 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b)))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li9).add (sfa10)
  have sfa8 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li8).add (sfa9)
  have sfa7 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b)))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li7).add (sfa8)
  have sfa6 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b))))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li6).add (sfa7)
  have sfa5 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b)))))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li5).add (sfa6)
  have sfa4 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b))))))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li4).add (sfa5)
  have sfa3 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b)))))))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li3).add (sfa4)
  have sfa2 : IntervalIntegrable (fun a : ℝ => ((∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b))))))))))))))) MeasureTheory.volume (1/10:ℝ) (1/2:ℝ) :=
    (li2).add (sfa3)

  have hEq : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), (G1 a b + (G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + (G11 a b + (G12 a b + (G13 a b + (G14 a b))))))))))))))) = ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G1 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b))))))))))))))) := by
    have hstep : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), (G1 a b + (G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + (G11 a b + (G12 a b + (G13 a b + (G14 a b))))))))))))))) =
        (∫ a in (1/10:ℝ)..(1/2:ℝ), ((∫ b in (1/10:ℝ)..(1/2:ℝ), G1 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) + ((∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b)))))))))))))))) := by
      simp only [hinner]
    rw [hstep]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add] <;>
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
        | simpa only [] using li12
        | simpa only [] using li13
        | simpa only [] using li14
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
        | simpa only [] using sfa12
        | simpa only [] using sfa13
        | simpa only [] using sfa14

  -- ---- the monotonicity step and the final comparison ----
  have hFb14 : ∀ a b : ℝ, |(if C a b then (1:ℝ)/(a*b^2) else 0)| ≤ 14000 := fun a b => le_trans (hFb a b) (by norm_num)
  have hmono := slope_two_mono (fun a b : ℝ => (G1 a b + (G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + (G11 a b + (G12 a b + (G13 a b + (G14 a b))))))))))))))) (fun a b : ℝ => (if C a b then (1:ℝ)/(a*b^2) else 0))
    hSmeas hFmeas (M := 14000) hSb hFb14 hSle (lo := (1/10:ℝ)) (hi := (1/2:ℝ)) (by norm_num)
  have hsum : (13/10:ℝ) ≤ ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G1 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b))))))))))))))) := by
    linarith [P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14]
  have hmain : (13/10:ℝ) ≤ (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), (if C a b then (1:ℝ)/(a*b^2) else 0)) := by
    calc (13/10:ℝ) ≤ ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G1 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G2 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G3 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G4 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G5 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G6 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G7 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G8 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G9 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G10 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G11 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G12 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G13 a b) + ((∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), G14 a b))))))))))))))) := hsum
      _ = (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), (G1 a b + (G2 a b + (G3 a b + (G4 a b + (G5 a b + (G6 a b + (G7 a b + (G8 a b + (G9 a b + (G10 a b + (G11 a b + (G12 a b + (G13 a b + (G14 a b))))))))))))))) := hEq.symm
      _ ≤ (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), (if C a b then (1:ℝ)/(a*b^2) else 0)) := hmono
  simpa only [hC] using hmain


/-- LEAF: the pointwise bound the two fold monotonicity lemma needs. On the three bands
`1/8 ≤ b ≤ a` gives `a b^2 ≥ 1/512`, so the integrand is at most `512` there and zero elsewhere;
hence `10^3` bounds its absolute value everywhere. -/
theorem leaf_three_band_bound (a b : ℝ) :
    |(if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)| ≤ 1000 := by
  split_ifs with h
  · have hb1 : (1/8:ℝ) ≤ b := by
      rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · linarith
      · exact h1
      · exact h1
    have hba : b ≤ a := by
      rcases h with ⟨-, h2, -⟩ | ⟨-, -, h2, -⟩ | ⟨-, -, h2, -⟩
      · exact h2
      · exact h2
      · exact h2
    have hb2 : (1/64:ℝ) ≤ b^2 := by nlinarith
    have hmul : (1/8:ℝ)*(1/64) ≤ a*b^2 :=
      mul_le_mul (le_trans hb1 hba) hb2 (by norm_num) (by linarith)
    have hpos : 0 < a*b^2 := by linarith
    have hnn : 0 ≤ (1:ℝ)/(a*b^2) := by positivity
    rw [abs_of_nonneg hnn]
    rw [div_le_iff₀ hpos]
    linarith
  · norm_num

/-- The E2 quadrature, assembled from the three band inclusions, the quadrature over their union
and the pointwise bound. Since every band is contained in E2 and `1 / (a b^2) ≥ 0` on E2, the
integrand of the union is pointwise at most the E2 integrand, and the two fold monotonicity lemma
`slope_two_mono` carries that to the integrals. -/
theorem leaf_two_region_quadrature_split {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    13/10 ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      if lowerTwoDiscarded ε a b then 1/(a*b^2) else 0 := by
  have hle : ∀ a b : ℝ,
      (if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0) ≤
      (if lowerTwoDiscarded ε a b then 1/(a*b^2) else 0) := by
    intro a b
    by_cases hR : (((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))))
    · rw [if_pos hR]
      rw [if_pos (by
        rcases hR with h | h | h
        · obtain ⟨hb, hba, ha, hs1, hs2⟩ := h
          exact leaf_high_band_membership hε hε8 hb hba ha hs1 hs2
        · obtain ⟨hb1, hb2, hba, ha, hs1, hs2, hcut, h7, h5, hclear⟩ := h
          exact leaf_middle_band_membership hε hε8 hb1 hb2 hba ha hs1 hs2 hcut h7 h5 hclear
        · obtain ⟨hb1, hb2, hba, ha, hs1, hs2, h3, h4⟩ := h
          exact leaf_notch_band_membership hε hε8 hb1 hb2 hba ha hs1 hs2 h3 h4)]
    · rw [if_neg hR]
      by_cases hD : lowerTwoDiscarded ε a b
      · rw [if_pos hD]
        obtain ⟨hb, hba, ha, hs⟩ := lower_two_domain_box hε8 hD
        have hb2 : (1/100:ℝ) ≤ b^2 := by nlinarith
        have hab : (1/10:ℝ)*(1/100) ≤ a*b^2 :=
          mul_le_mul (by linarith) hb2 (by norm_num) (by linarith)
        have hpos : 0 < a*b^2 := by linarith
        exact le_of_lt (one_div_pos.2 hpos)
      · rw [if_neg hD]
  have hf : Measurable (fun p : ℝ × ℝ =>
      if ((2273/10000 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1) ∨
        (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧
            p.1 + 2*p.2 ≤ 1 ∧ 4*p.1 + 3*p.2 ≤ 15/8 ∧ 17/8 ≤ 4*p.1 + 7*p.2 ∧
            (p.1 + p.2 ≤ 7/16 ∨ 17/8 ≤ 4*p.1 + 5*p.2) ∧
            (2273/10000 ≤ p.1 ∨ p.1 + 1/8 ≤ 2*p.2)) ∨
        (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧
            p.1 + 2*p.2 ≤ 1 ∧ 17/8 ≤ 4*p.1 + 3*p.2 ∧
            (4*p.1 + p.2 ≤ 15/8 ∨ 17/8 ≤ 4*p.1 + p.2))) then 1/(p.1*p.2^2) else 0) :=
    Measurable.ite three_band_region_measurable (by fun_prop) measurable_const
  have hg : Measurable (fun p : ℝ × ℝ =>
      if lowerTwoDiscarded ε p.1 p.2 then 1/(p.1*p.2^2) else 0) :=
    Measurable.ite (two_density_region_measurable ε) (by fun_prop) measurable_const
  have hfb : ∀ a b : ℝ, |(if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)| ≤ 1000 :=
    fun a b => leaf_three_band_bound a b
  have hgb : ∀ a b : ℝ,
      |(if lowerTwoDiscarded ε a b then 1/(a*b^2) else 0)| ≤ 1000 := fun a b => by
    by_cases hD : lowerTwoDiscarded ε a b
    · simp only [hD, ↓reduceIte]
      obtain ⟨hb, hba, ha, hs⟩ := lower_two_domain_box hε8 hD
      have hb2 : (1/100:ℝ) ≤ b^2 := by nlinarith
      have hab : (1/10:ℝ)*(1/100) ≤ a*b^2 :=
        mul_le_mul (by linarith) hb2 (by norm_num) (by linarith)
      have hpos : 0 < a*b^2 := by linarith
      have h1 : 1/(a*b^2) ≤ 1000 := by rw [div_le_iff₀ hpos]; linarith
      have h0 : 0 ≤ 1/(a*b^2) := by positivity
      rw [abs_of_nonneg (by linarith)]
      linarith
    · simp only [hD, ↓reduceIte]
      norm_num
  have hmono := slope_two_mono
    (fun a b => if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)
    (fun a b => if lowerTwoDiscarded ε a b then 1/(a*b^2) else 0)
    hf hg (M := 1000) hfb hgb hle (lo := 1/10) (hi := 1/2) (by norm_num)
  have hq := leaf_three_band_quadrature hε hε8
  linarith

end LeanLab.BHP1997.LowerShortC165
