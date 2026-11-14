/-
Jia 1996 Lemma 27, pages 281 and 282, a shorter polynomial enclosure.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The source integral and final subtotals stay unchanged.
-/
import LeanLab.Languasco2004.Integral564

namespace LeanLab.Languasco2004.Short564
open Real Set Finset intervalIntegral RemainderData564 Integral564
noncomputable section
set_option maxHeartbeats 0

/-- Pages 281 and 282 numerical support: the two term logarithm polynomial.
The already certified constant kernel polynomials are retained exactly. -/
def shortPolynomial (i : Fin 16) (t u : ℝ) : ℝ :=
  let r := numericData i
  let it := logReciprocal t (r 6)
  let iu := logReciprocal u (r 7)
  let iv := logReciprocal (1-t-u) (r 8)
  let s := 1-t-3*u
  if isLog i then it*iu*iv*(1+2*s*iv+(2/3:ℝ)*s^3*iv^3)
  else polynomial i t u

/-- Supporting row enclosures. They certify the required family subtotals directly.
They are not assertions of each separately printed decimal coefficient. -/
def rowTarget (i : Fin 16) : ℚ :=
  if isLog i then
    match i.val with
    | 0 => 0.0002443
    | 2 => 0.0002762
    | 5 => 0.0018420
    | 7 => 0.0003574
    | 9 => 0.0015451
    | 11 => 0.0006341
    | 13 => 0.0029103
    | _ => 0.0009746
  else numericData i 9

/-- Pages 281 and 282: dropping the positive fifth power term preserves the minorant. -/
theorem shortPolynomial_le (i : Fin 16) (t u : ℝ)
    (htl : (numericData i 0 : ℝ) ≤ t) (htu : t ≤ (numericData i 1 : ℝ))
    (hul : (numericData i 2 : ℝ)+numericData i 3*t ≤ u)
    (huu : u ≤ (numericData i 4 : ℝ)+numericData i 5*t) :
    shortPolynomial i t u ≤ kernel i t u := by
  have hp : shortPolynomial i t u ≤ polynomial i t u := by
    by_cases hk : isLog i = true
    · obtain ⟨ht, hu, hv, hct, htc, hcu, huc, hcv, hvc, hs⟩ :=
        row_kernel_bounds i t u htl htu hul huu
      have hs := hs hk
      have hit := (logReciprocal_bounds t (numericData i 6) ht hct htc).1
      have hiu := (logReciprocal_bounds u (numericData i 7) hu hcu huc).1
      have hiv := (logReciprocal_bounds (1-t-u) (numericData i 8) hv hcv hvc).1
      dsimp [shortPolynomial, polynomial]
      simp only [hk, ↓reduceIte]
      apply mul_le_mul_of_nonneg_left
      · exact le_add_of_nonneg_right (by positivity)
      · positivity
    · simp [shortPolynomial, polynomial, hk]
  exact hp.trans (polynomial_le i t u htl htu hul huu)

/-- Supporting regularity: the shorter polynomial inner integral is continuous. -/
theorem short_inner_continuous (i : Fin 16) :
    let r := numericData i
    Continuous (fun t : ℝ =>
      ∫ u in ((r 2 : ℝ)+r 3*t)..((r 4 : ℝ)+r 5*t), shortPolynomial i t u) := by
  dsimp
  have hc : Continuous (Function.uncurry (shortPolynomial i)) := by
    unfold shortPolynomial polynomial reciprocal logReciprocal
    split_ifs <;> fun_prop
  have hU := continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume) (a₀ := 0) hc
    (show Continuous (fun t : ℝ => (numericData i 4 : ℝ)+numericData i 5*t) by fun_prop)
  have hL := continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume) (a₀ := 0) hc
    (show Continuous (fun t : ℝ => (numericData i 2 : ℝ)+numericData i 3*t) by fun_prop)
  have hp (t : ℝ) : Continuous (shortPolynomial i t) := by
    unfold shortPolynomial polynomial reciprocal logReciprocal
    split_ifs <;> fun_prop
  have he : (fun t : ℝ => ∫ u in ((numericData i 2 : ℝ)+numericData i 3*t)..
      ((numericData i 4 : ℝ)+numericData i 5*t), shortPolynomial i t u) =
      fun t : ℝ => (∫ u in (0:ℝ)..((numericData i 4 : ℝ)+numericData i 5*t), shortPolynomial i t u) -
        (∫ u in (0:ℝ)..((numericData i 2 : ℝ)+numericData i 3*t), shortPolynomial i t u) := by
    funext t
    exact (integral_interval_sub_left ((hp t).intervalIntegrable _ _)
      ((hp t).intervalIntegrable _ _)).symm
  rw [he]
  exact hU.sub hL

/-- Pages 281 and 282: the complete shorter polynomial integral is below the source integral. -/
theorem short_integral_le (i : Fin 16) :
    let r := numericData i
    (∫ t in (r 0 : ℝ)..(r 1),
      ∫ u in ((r 2 : ℝ)+r 3*t)..((r 4 : ℝ)+r 5*t), shortPolynomial i t u) ≤ sourceIntegral i := by
  dsimp [sourceIntegral]
  have hab : (numericData i 0 : ℝ) ≤ numericData i 1 := by
    fin_cases i <;> norm_num [numericData]
  apply integral_mono_on hab ((short_inner_continuous i).intervalIntegrable _ _)
    ((source_inner_continuousOn i).intervalIntegrable_of_Icc hab)
  intro t ht
  obtain ⟨ht1, ht2, hl, hlu, hu⟩ := row_endpoints i t ht.1 ht.2
  have hp : Continuous (shortPolynomial i t) := by
    unfold shortPolynomial polynomial reciprocal logReciprocal
    split_ifs <;> fun_prop
  have hk : ContinuousOn (kernel i t) (Icc ((numericData i 2 : ℝ)+numericData i 3*t)
      ((numericData i 4 : ℝ)+numericData i 5*t)) :=
    (kernel_continuousOn i).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu' => ⟨⟨ht1,ht2⟩,⟨hl.trans hu'.1,hu'.2.trans hu⟩⟩)
  apply integral_mono_on hlu (hp.intervalIntegrable _ _) (hk.intervalIntegrable_of_Icc hlu)
  intro u hu'
  exact shortPolynomial_le i t u ht.1 ht.2 hu'.1 hu'.2

#print axioms shortPolynomial_le
#print axioms short_inner_continuous
#print axioms short_integral_le
end
end LeanLab.Languasco2004.Short564
