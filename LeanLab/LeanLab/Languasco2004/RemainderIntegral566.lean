/-
Jia 1996 pages 271 to 273, integral comparison for all 25 remainder components.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.RemainderKernel566
import LeanLab.Languasco2004.Endpoint566
import LeanLab.Languasco2004.Numeric11_566

namespace LeanLab.Languasco2004.RemainderIntegral566
open Real Set intervalIntegral RemainderData566 RemainderKernel566 MovingIntegral548
noncomputable section
set_option maxHeartbeats 0

/-- LEAF. Pages 271 to 273 support: a compact rectangle avoids every denominator and logarithm pole. -/
theorem rectangle_positive (i : Fin 25) (t u : ℝ)
    (htl : (data i 0 : ℝ) ≤ t) (htu : t ≤ (data i 1 : ℝ))
    (hul : (uMin i : ℝ) ≤ u) (huu : u ≤ (uMax i : ℝ)) :
    0 < t ∧ 0 < u ∧ 0 < 1 - t - u ∧ 0 < 1 - t - 2 * u := by
  obtain ⟨ha, _, hu, _, hv, hw⟩ := Affine566.rectangle_certificate i
  have har : 0 < (data i 0 : ℝ) := by exact_mod_cast ha
  have hur : 0 < (uMin i : ℝ) := by exact_mod_cast hu
  have hvr : (data i 1 : ℝ) + (uMax i : ℝ) < 1 := by exact_mod_cast hv
  have hwr : (data i 1 : ℝ) + 2 * (uMax i : ℝ) < 1 := by exact_mod_cast hw
  exact ⟨har.trans_le htl, hur.trans_le hul, by linarith, by linarith⟩

/-- LEAF. Pages 271 to 273 support: each exact kernel is continuous on a containing rectangle. -/
theorem kernel_continuousOn (i : Fin 25) :
    ContinuousOn (Function.uncurry (kernel i))
      (Icc (data i 0 : ℝ) (data i 1 : ℝ) ×ˢ Icc (uMin i : ℝ) (uMax i : ℝ)) := by
  let R := Icc (data i 0 : ℝ) (data i 1 : ℝ) ×ˢ Icc (uMin i : ℝ) (uMax i : ℝ)
  have ht (z : ℝ × ℝ) (hz : z ∈ R) : 0 < z.1 :=
    (rectangle_positive i z.1 z.2 hz.1.1 hz.1.2 hz.2.1 hz.2.2).1
  have hu (z : ℝ × ℝ) (hz : z ∈ R) : 0 < z.2 :=
    (rectangle_positive i z.1 z.2 hz.1.1 hz.1.2 hz.2.1 hz.2.2).2.1
  have hv (z : ℝ × ℝ) (hz : z ∈ R) : 0 < 1 - z.1 - z.2 :=
    (rectangle_positive i z.1 z.2 hz.1.1 hz.1.2 hz.2.1 hz.2.2).2.2.1
  have harg (z : ℝ × ℝ) (hz : z ∈ R) : 0 < (1 - z.1) / z.2 - 2 := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ (hu z hz)).mpr
    have h := (rectangle_positive i z.1 z.2 hz.1.1 hz.1.2 hz.2.1 hz.2.2).2.2.2
    linarith
  have hden : ContinuousOn (fun z : ℝ × ℝ => z.1 * z.2 * (1 - z.1 - z.2)) R := by fun_prop
  have hnz (z : ℝ × ℝ) (hz : z ∈ R) : z.1 * z.2 * (1 - z.1 - z.2) ≠ 0 :=
    (mul_pos (mul_pos (ht z hz) (hu z hz)) (hv z hz)).ne'
  unfold kernel Function.uncurry
  split_ifs
  · exact continuousOn_const.div (by fun_prop)
      (fun z hz => (mul_pos (ht z hz) (sq_pos_of_pos (hu z hz))).ne')
  · have hrat : ContinuousOn (fun z : ℝ × ℝ => (1 - z.1) / z.2 - 2) R :=
      ((continuousOn_const.sub continuous_fst.continuousOn).div continuous_snd.continuousOn
        (fun z hz => (hu z hz).ne')).sub continuousOn_const
    exact (continuousOn_const.add (hrat.log (fun z hz => (harg z hz).ne'))).div hden hnz
  · exact continuousOn_const.div hden hnz

/-- LEAF. Pages 271 to 273 support: each source inner integral is continuous on its outer interval. -/
theorem inner_continuousOn (i : Fin 25) :
    ContinuousOn (fun t : ℝ =>
      ∫ u in ((data i 2 : ℝ) * t + data i 3)..((data i 4 : ℝ) * t + data i 5), kernel i t u)
      (Icc (data i 0 : ℝ) (data i 1 : ℝ)) := by
  have ha : (data i 0 : ℝ) ≤ (data i 1 : ℝ) := by
    exact_mod_cast (Affine566.rectangle_certificate i).2.1
  have hu : (uMin i : ℝ) ≤ (uMax i : ℝ) := by
    exact_mod_cast (Affine566.rectangle_certificate i).2.2.2.1
  apply moving_integral_continuousOn (kernel i)
    (data i 0 : ℝ) (data i 1 : ℝ) (uMin i : ℝ) (uMax i : ℝ)
    (fun t => (data i 2 : ℝ) * t + data i 3)
    (fun t => (data i 4 : ℝ) * t + data i 5)
    ha hu (kernel_continuousOn i) (by fun_prop) (by fun_prop)
  intro t ht
  obtain ⟨h1, h2, h3, h4, h5⟩ := endpoint_bounds i t ht.1 ht.2
  exact ⟨h1, h2, h3, h4⟩

/-- LEAF. Pages 271 to 273 support: the polynomial comparison passes through both definite integrals. -/
theorem polynomialTerm_le (i : Fin 25) : polynomialTerm i ≤ term i := by
  have hP : Continuous (Function.uncurry (polynomial i)) := by
    unfold polynomial
    dsimp only
    split_ifs <;> simp only [Numeric548.invPoly5, Numeric30_548.invPoly3, Midpoint566.invPoly1] <;> fun_prop
  have hi := Numeric11_566.polynomial_inner_continuous (polynomial i) hP
    (fun t => (data i 2 : ℝ) * t + data i 3)
    (fun t => (data i 4 : ℝ) * t + data i 5) (by fun_prop) (by fun_prop)
  have ha : (data i 0 : ℝ) ≤ (data i 1 : ℝ) := by
    exact_mod_cast (Affine566.rectangle_certificate i).2.1
  apply integral_mono_on ha (hi.intervalIntegrable _ _)
    ((inner_continuousOn i).intervalIntegrable_of_Icc ha)
  intro t ht
  obtain ⟨h1, h2, h3, h4, hab⟩ := endpoint_bounds i t ht.1 ht.2
  have hc : ContinuousOn (kernel i t)
      (Icc ((data i 2 : ℝ) * t + data i 3) ((data i 4 : ℝ) * t + data i 5)) := by
    apply (kernel_continuousOn i).comp (continuous_const.prodMk continuous_id).continuousOn
    intro u hu
    exact ⟨ht, ⟨h1.trans hu.1, hu.2.trans h4⟩⟩
  exact integral_mono_on hab ((hP.uncurry_left t).intervalIntegrable _ _)
    (hc.intervalIntegrable_of_Icc hab)
    (fun u hu => polynomial_le i t u ht.1 ht.2 hu.1 hu.2)

#print axioms rectangle_positive
#print axioms endpoint_bounds
#print axioms kernel_continuousOn
#print axioms inner_continuousOn
#print axioms polynomialTerm_le
end
end LeanLab.Languasco2004.RemainderIntegral566
