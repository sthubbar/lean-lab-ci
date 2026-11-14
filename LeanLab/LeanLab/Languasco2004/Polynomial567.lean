/-
Jia 1996 pages 275 to 277, numerical integrals in Lemma 25.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Numeric548
import LeanLab.Languasco2004.MovingIntegral548

namespace LeanLab.Languasco2004.Polynomial567
open Real Finset Set intervalIntegral Numeric548 MovingIntegral548
noncomputable section

/-- Pages 275 to 277 numerical support: eight centered geometric terms. -/
def invPoly7 (x c : ℝ) : ℝ :=
  (1 + (1-x/c) + (1-x/c)^2 + (1-x/c)^3 +
    (1-x/c)^4 + (1-x/c)^5 + (1-x/c)^6 + (1-x/c)^7) / c

/-- Pages 275 to 277: the existing six term minorant also works with a center.
The input lies between zero and twice the positive center. -/
theorem invPoly5_centered (x c : ℝ) (hx : 0 < x) (hc : 0 < c)
    (hxc : x ≤ 2*c) : 0 ≤ invPoly5 x c ∧ invPoly5 x c ≤ 1/x := by
  have hz : 0 ≤ 2 - x/c := by
    have := (div_le_iff₀ hc).mpr hxc
    linarith
  have he : invPoly5 x c * x = 1 - (1-x/c)^6 := by
    unfold invPoly5
    field_simp
    ring
  constructor
  · have hf : invPoly5 x c = (2-x/c) * (1+(1-x/c)^2+(1-x/c)^4) / c := by
      unfold invPoly5
      ring
    rw [hf]
    positivity
  · apply (le_div_iff₀ hx).mpr
    have hp : 0 ≤ (1-x/c)^6 := by positivity
    linarith

/-- Pages 275 to 277: the centered eight term reciprocal has a positive remainder. -/
theorem invPoly7_centered (x c : ℝ) (hx : 0 < x) (hc : 0 < c)
    (hxc : x ≤ 2*c) : 0 ≤ invPoly7 x c ∧ invPoly7 x c ≤ 1/x := by
  have hz : 0 ≤ 2 - x/c := by
    have := (div_le_iff₀ hc).mpr hxc
    linarith
  have he : invPoly7 x c * x = 1 - (1-x/c)^8 := by
    unfold invPoly7
    field_simp
    ring
  constructor
  · have hf : invPoly7 x c =
        (2-x/c) * (1+(1-x/c)^2+(1-x/c)^4+(1-x/c)^6) / c := by
      unfold invPoly7
      ring
    rw [hf]
    positivity
  · apply (le_div_iff₀ hx).mpr
    have hp : 0 ≤ (1-x/c)^8 := by positivity
    linarith

/-- Pages 275 to 277: one polynomial covers each of the three printed kernels. -/
def minorant (k : ℕ) (ct cu cv t u : ℝ) : ℝ :=
  let pt := invPoly5 t ct
  let pu := invPoly7 u cu
  let pv := invPoly5 (1-t-u) cv
  if k = 0 then pt*pu*pv
  else if k = 1 then pt*pu*pv *
    (1 + 2*((1-t-3*u)*pv + ((1-t-3*u)*pv)^3/3 +
      ((1-t-3*u)*pv)^5/5 + ((1-t-3*u)*pv)^7/7))
  else 0.5607*pt*pu^2

/-- Pages 275 to 277: the rational, logarithmic and constant Buchstab kernels. -/
def kernel (k : ℕ) (t u : ℝ) : ℝ :=
  if k = 0 then 1/(t*u*(1-t-u))
  else if k = 1 then (1+Real.log ((1-t)/u-2))/(t*u*(1-t-u))
  else 0.5607/(t*u^2)

/-- Pages 275 to 277: the polynomial for a rational kernel is a minorant. -/
theorem minorant_rational_le (ct cu cv t u : ℝ)
    (ht : 0 < t) (hu : 0 < u) (hv : 0 < 1-t-u)
    (hct : 0 < ct) (hcu : 0 < cu) (hcv : 0 < cv)
    (hT : t ≤ 2*ct) (hU : u ≤ 2*cu) (hV : 1-t-u ≤ 2*cv) :
    minorant 0 ct cu cv t u ≤ kernel 0 t u := by
  obtain ⟨ht0, ht1⟩ := invPoly5_centered t ct ht hct hT
  obtain ⟨hu0, hu1⟩ := invPoly7_centered u cu hu hcu hU
  obtain ⟨hv0, hv1⟩ := invPoly5_centered (1-t-u) cv hv hcv hV
  have h1 := mul_le_mul ht1 hu1 hu0 (by positivity : (0 : ℝ) ≤ 1/t)
  have h2 := mul_le_mul h1 hv1 hv0 (by positivity : (0 : ℝ) ≤ 1/t*(1/u))
  simpa [minorant, kernel, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h2

/-- Pages 275 to 277: the constant Buchstab kernel has the same polynomial enclosure. -/
theorem minorant_constant_le (ct cu cv t u : ℝ)
    (ht : 0 < t) (hu : 0 < u) (hct : 0 < ct) (hcu : 0 < cu)
    (hT : t ≤ 2*ct) (hU : u ≤ 2*cu) :
    minorant 2 ct cu cv t u ≤ kernel 2 t u := by
  obtain ⟨ht0, ht1⟩ := invPoly5_centered t ct ht hct hT
  obtain ⟨hu0, hu1⟩ := invPoly7_centered u cu hu hcu hU
  have hsq : invPoly7 u cu ^ 2 ≤ (1/u)^2 := by nlinarith
  have h1 := mul_le_mul ht1 hsq (sq_nonneg _) (by positivity : (0 : ℝ) ≤ 1/t)
  have h2 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 0.5607)
  convert h2 using 1 <;> simp [minorant, kernel] <;> field_simp

/-- Pages 275 to 277: four existing logarithm series terms give a lower bound. -/
theorem log_four_lower (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1) :
    2*(z+z^3/3+z^5/5+z^7/7) ≤ Real.log ((1+z)/(1-z)) := by
  have h := Real.sum_range_le_log_div hz hz1 4
  norm_num [sum_range_succ] at h
  linarith

/-- Pages 275 to 277: the logarithmic polynomial uses the same reciprocal bounds. -/
theorem minorant_log_le (ct cu cv t u : ℝ)
    (ht : 0 < t) (hu : 0 < u) (hv : 0 < 1-t-u) (hw : 0 ≤ 1-t-3*u)
    (hct : 0 < ct) (hcu : 0 < cu) (hcv : 0 < cv)
    (hT : t ≤ 2*ct) (hU : u ≤ 2*cu) (hV : 1-t-u ≤ 2*cv) :
    minorant 1 ct cu cv t u ≤ kernel 1 t u := by
  obtain ⟨ht0, ht1⟩ := invPoly5_centered t ct ht hct hT
  obtain ⟨hu0, hu1⟩ := invPoly7_centered u cu hu hcu hU
  obtain ⟨hv0, hv1⟩ := invPoly5_centered (1-t-u) cv hv hcv hV
  let z := (1-t-3*u)/(1-t-u)
  have hz : 0 ≤ z := div_nonneg hw hv.le
  have hz1 : z < 1 := (div_lt_one hv).mpr (by linarith)
  have hlog := log_four_lower z hz hz1
  have he : (1+z)/(1-z) = (1-t)/u-2 := by
    apply (div_eq_iff (sub_pos.mpr hz1).ne').mpr
    dsimp [z]
    field_simp [hu.ne', hv.ne']
    <;> ring
  rw [he] at hlog
  have hwp : (1-t-3*u)*invPoly5 (1-t-u) cv ≤ z := by
    simpa only [z, div_eq_mul_inv, one_div, one_mul] using mul_le_mul_of_nonneg_left hv1 hw
  have hwp0 : 0 ≤ (1-t-3*u)*invPoly5 (1-t-u) cv := mul_nonneg hw hv0
  have hp3 := pow_le_pow_left₀ hwp0 hwp 3
  have hp5 := pow_le_pow_left₀ hwp0 hwp 5
  have hp7 := pow_le_pow_left₀ hwp0 hwp 7
  have hnum : 1+2*((1-t-3*u)*invPoly5 (1-t-u) cv +
      ((1-t-3*u)*invPoly5 (1-t-u) cv)^3/3 +
      ((1-t-3*u)*invPoly5 (1-t-u) cv)^5/5 +
      ((1-t-3*u)*invPoly5 (1-t-u) cv)^7/7) ≤ 1+Real.log ((1-t)/u-2) := by
    linarith
  have hnum0 : 0 ≤ 1+2*((1-t-3*u)*invPoly5 (1-t-u) cv +
      ((1-t-3*u)*invPoly5 (1-t-u) cv)^3/3 +
      ((1-t-3*u)*invPoly5 (1-t-u) cv)^5/5 +
      ((1-t-3*u)*invPoly5 (1-t-u) cv)^7/7) := by positivity
  have h1 := mul_le_mul ht1 hu1 hu0 (by positivity : (0 : ℝ) ≤ 1/t)
  have h2 := mul_le_mul h1 hv1 hv0 (by positivity : (0 : ℝ) ≤ 1/t*(1/u))
  have h3 := mul_le_mul h2 hnum hnum0 (by positivity : (0 : ℝ) ≤ 1/t*(1/u)*(1/(1-t-u)))
  convert h3 using 1 <;> simp [minorant, kernel]
  field_simp

/-- Pages 275 to 277: comparison of two iterated integrals on a moving strip.
Compact rectangle continuity supplies every integrability premise. -/
theorem strip_integral_mono (F P : ℝ → ℝ → ℝ) (a b c d : ℝ)
    (L U : ℝ → ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Icc c d))
    (hP : Continuous (Function.uncurry P)) (hL : Continuous L) (hU : Continuous U)
    (hBounds : ∀ t ∈ Icc a b, c ≤ L t ∧ L t ≤ U t ∧ U t ≤ d)
    (hle : ∀ t ∈ Icc a b, ∀ u ∈ Icc (L t) (U t), P t u ≤ F t u) :
    (∫ t in a..b, ∫ u in L t..U t, P t u) ≤
      ∫ t in a..b, ∫ u in L t..U t, F t u := by
  have hBounds' : ∀ t ∈ Icc a b, c ≤ L t ∧ L t ≤ d ∧ c ≤ U t ∧ U t ≤ d := by
    intro t ht
    obtain ⟨h1,h2,h3⟩ := hBounds t ht
    exact ⟨h1,h2.trans h3,h1.trans h2,h3⟩
  have hiF := moving_integral_continuousOn F a b c d L U hab hcd hF hL hU hBounds'
  have hiP := moving_integral_continuousOn P a b c d L U hab hcd hP.continuousOn hL hU hBounds'
  apply integral_mono_on hab
    (hiP.intervalIntegrable_of_Icc hab) (hiF.intervalIntegrable_of_Icc hab)
  intro t ht
  obtain ⟨h1,h2,h3⟩ := hBounds t ht
  have hf : ContinuousOn (F t) (Icc (L t) (U t)) := by
    apply hF.comp (continuousOn_const.prodMk continuousOn_id)
    intro u hu
    exact ⟨ht, h1.trans hu.1, hu.2.trans h3⟩
  exact integral_mono_on h2 ((hP.uncurry_left t).intervalIntegrable _ _)
    (hf.intervalIntegrable_of_Icc h2) (hle t ht)

#print axioms invPoly5_centered
#print axioms invPoly7_centered
#print axioms minorant_rational_le
#print axioms minorant_constant_le
#print axioms log_four_lower
#print axioms minorant_log_le
#print axioms strip_integral_mono
end
end LeanLab.Languasco2004.Polynomial567
