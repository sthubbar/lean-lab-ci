/-
Jia 1996 Lemma 27, pages 281 and 282, sixteen remainder integrals.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
All entries are arithmetic data, with no new Prop input.
-/
import LeanLab.Languasco2004.Numeric30_548

namespace LeanLab.Languasco2004.RemainderData564
open Real Set Finset intervalIntegral
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Pages 281 and 282: a, b, lower intercept and slope, upper intercept and slope,
three reciprocal centers and a rational polynomial integral lower bound.
The row order is the printed integrals two through seventeen. -/
def numericData (i : Fin 16) : Fin 10 → ℚ :=
  match i.val with
  | 0 => ![1649/4752,77/221,34/59,-70/59,85/147,-58/49,730333/2100384,8500543/51459408,1856719/3811808,489/2000000]
  | 1 => ![77/221,193/549,34/59,-70/59,1/4,-1/4,42463/121329,1152776/7158411,31601/64782,141/500000]
  | 2 => ![77/221,193/549,1/4,-1/4,85/147,-58/49,42463/121329,974801/5945121,31657/64974,553/2000000]
  | 3 => ![193/549,1823/4725,34/59,-70/59,85/147,-58/49,106264/288225,2311/16470,283037/576450,80367/10000000]
  | 4 => ![1823/4725,3041/7830,16/135,0,85/147,-58/49,70723/182700,18527/154350,45763/92610,393/1000000]
  | 5 => ![11/27,121/291,89/114,-29/19,18/23,-35/23,1078/2619,37189/240948,34861/80316,1843/1000000]
  | 6 => ![121/291,49/117,89/114,-29/19,1/4,-1/4,4736/11349,61999/431262,3893/8892,3693/10000000]
  | 7 => ![121/291,49/117,1/4,-1/4,18/23,-35/23,4736/11349,38522/261027,3893/8924,3577/10000000]
  | 8 => ![49/117,49/114,89/114,-29/19,18/23,-35/23,3773/8892,5701/42237,8273/18772,30879/10000000]
  | 9 => ![3397/7830,7/16,17/12,-35/12,17/12,-29/10,54581/125280,12923/86400,1039213/2505600,15459/10000000]
  | 10 => ![7/16,70/159,17/12,-35/12,1/4,-1/4,2233/5088,8341/61056,202/477,1699/2500000]
  | 11 => ![7/16,70/159,1/4,-1/4,17/12,-29/10,2233/5088,2441/16960,803/1920,3173/5000000]
  | 12 => ![70/159,4/9,17/12,-35/12,17/12,-29/10,211/477,745/5724,2447/5724,23193/10000000]
  | 13 => ![211/432,329/669,89/27,-58/9,36/11,-70/11,94429/192672,154513/1059696,771647/2119392,7277/2500000]
  | 14 => ![329/669,281/570,89/27,-58/9,1/4,-1/4,125173/254220,5219/42370,1751/4560,413/1250000]
  | _ => ![329/669,281/570,1/4,-1/4,36/11,-70/11,125173/254220,503319/3728560,5491/14718,9751/10000000]

/-- Pages 281 and 282: these eight rows use the exact logarithmic kernel.
The other eight use the source lower bound 0.5607 divided by t times u squared. -/
def isLog (i : Fin 16) : Bool := decide (i.val ∈ ({0, 2, 5, 7, 9, 11, 13, 15} : Finset ℕ))

/-- Pages 281 and 282 numerical support: a sixth order reciprocal minorant. -/
def reciprocal (x c : ℝ) : ℝ :=
  (2 - x / c) * (1 + (1 - x / c)^2 + (1 - x / c)^4) / c

/-- Pages 281 and 282 numerical support: a fourth order centered reciprocal minorant
suffices on the narrow logarithmic subdomains. -/
def logReciprocal (x c : ℝ) : ℝ := (2-x/c) * (1+(1-x/c)^2) / c

/-- Pages 281 and 282: the source lower kernel on each printed subdomain. -/
def kernel (i : Fin 16) (t u : ℝ) : ℝ :=
  if isLog i then (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u))
  else 0.5607 / (t * u^2)

/-- Pages 281 and 282 numerical support: a polynomial using three logarithm series terms. -/
def polynomial (i : Fin 16) (t u : ℝ) : ℝ :=
  let r := numericData i
  let it := reciprocal t (r 6)
  let iu := reciprocal u (r 7)
  let s := 1 - t - 3 * u
  if isLog i then
    let jt := logReciprocal t (r 6)
    let ju := logReciprocal u (r 7)
    let jv := logReciprocal (1-t-u) (r 8)
    jt * ju * jv * (1 + 2*s*jv + (2/3:ℝ)*s^3*jv^3 + (2/5:ℝ)*s^5*jv^5)
  else 0.5607 * it * iu^2

/-- Pages 281 and 282: the exact source lower integral on a printed subdomain. -/
def sourceIntegral (i : Fin 16) : ℝ :=
  let r := numericData i
  ∫ t in (r 0 : ℝ)..(r 1), ∫ u in ((r 2 : ℝ) + r 3*t)..((r 4 : ℝ) + r 5*t), kernel i t u

/-- Pages 281 and 282: the combined lower integral for the nine remainder regions. -/
def remainderIntegral : ℝ := ∑ i : Fin 16, sourceIntegral i

/-- Pages 280 and 281: the lower integral for the seven Lemma 11 remainder regions. -/
def integral11 : ℝ := ∑ i ∈ (Finset.univ.filter (fun i : Fin 16 => i.val < 9)), sourceIntegral i

/-- Pages 281 and 282: the lower integral for the two Lemma 12 regions. -/
def integral12 : ℝ := ∑ i ∈ (Finset.univ.filter (fun i : Fin 16 => ¬ i.val < 9)), sourceIntegral i

/-- Numerical support: the exact sixth power remainder has the correct sign. -/
theorem reciprocal_bounds (x c : ℝ) (hx : 0 < x) (hc : 0 < c) (hxc : x ≤ 2*c) :
    0 ≤ reciprocal x c ∧ reciprocal x c ≤ 1 / x := by
  have hz : 0 ≤ 2 - x / c := sub_nonneg.mpr ((div_le_iff₀ hc).mpr hxc)
  have he : reciprocal x c * x = 1 - (1 - x / c)^6 := by
    unfold reciprocal
    field_simp
    ring
  constructor
  · unfold reciprocal
    positivity
  · apply (le_div_iff₀ hx).mpr
    nlinarith [sq_nonneg ((1 - x / c)^3)]

/-- Numerical support: the centered logarithmic reciprocal has a fourth power remainder. -/
theorem logReciprocal_bounds (x c : ℝ) (hx : 0 < x) (hc : 0 < c) (hxc : x ≤ 2*c) :
    0 ≤ logReciprocal x c ∧ logReciprocal x c ≤ 1/x := by
  have hz : 0 ≤ 2-x/c := sub_nonneg.mpr ((div_le_iff₀ hc).mpr hxc)
  have he : logReciprocal x c * x = 1-(1-x/c)^4 := by
    unfold logReciprocal
    field_simp
    ring
  constructor
  · unfold logReciprocal
    positivity
  · apply (le_div_iff₀ hx).mpr
    nlinarith [sq_nonneg ((1-x/c)^2)]

/-- Numerical support: Mathlib's logarithm series gives a rational three term minorant. -/
theorem log_three_terms (t u : ℝ) (hu : 0 < u) (hv : 0 < 1-t-u)
    (hs : 0 ≤ 1-t-3*u) :
    2*((1-t-3*u)/(1-t-u) + ((1-t-3*u)/(1-t-u))^3/3 +
      ((1-t-3*u)/(1-t-u))^5/5) ≤ Real.log ((1-t)/u-2) := by
  let z := (1-t-3*u)/(1-t-u)
  have hz0 : 0 ≤ z := div_nonneg hs hv.le
  have hz1 : z < 1 := (div_lt_one hv).mpr (by linarith)
  have h := Real.sum_range_le_log_div hz0 hz1 3
  have he : (1+z)/(1-z) = (1-t)/u-2 := by
    apply (div_eq_iff (sub_pos.mpr hz1).ne').mpr
    dsimp [z]
    field_simp [hu.ne', hv.ne']
    ring
  rw [he] at h
  norm_num [sum_range_succ] at h
  dsimp [z] at h
  nlinarith

/-- Pages 281 and 282: every printed row has ordered endpoints inside a fixed rectangle. -/
theorem row_endpoints (i : Fin 16) (t : ℝ)
    (htl : (numericData i 0 : ℝ) ≤ t) (htu : t ≤ (numericData i 1 : ℝ)) :
    (1/3:ℝ) ≤ t ∧ t ≤ 1/2 ∧
    (1/10:ℝ) ≤ (numericData i 2 : ℝ) + numericData i 3*t ∧
    (numericData i 2 : ℝ) + numericData i 3*t ≤
      (numericData i 4 : ℝ) + numericData i 5*t ∧
    (numericData i 4 : ℝ) + numericData i 5*t ≤ 1/5 := by
  fin_cases i <;> norm_num [numericData] at * <;> (repeat' constructor) <;> linarith

/-- Pages 281 and 282: the reciprocal centers and logarithm series are valid on every row. -/
theorem row_kernel_bounds (i : Fin 16) (t u : ℝ)
    (htl : (numericData i 0 : ℝ) ≤ t) (htu : t ≤ (numericData i 1 : ℝ))
    (hul : (numericData i 2 : ℝ) + numericData i 3*t ≤ u)
    (huu : u ≤ (numericData i 4 : ℝ) + numericData i 5*t) :
    0 < t ∧ 0 < u ∧ 0 < 1-t-u ∧
    0 < (numericData i 6 : ℝ) ∧ t ≤ 2*(numericData i 6 : ℝ) ∧
    0 < (numericData i 7 : ℝ) ∧ u ≤ 2*(numericData i 7 : ℝ) ∧
    0 < (numericData i 8 : ℝ) ∧ 1-t-u ≤ 2*(numericData i 8 : ℝ) ∧
    (isLog i = true → 0 ≤ 1-t-3*u) := by
  fin_cases i <;> norm_num [numericData, isLog] at * <;> (repeat' constructor) <;> linarith

/-- Pages 281 and 282: the literal split uses the logarithmic formula through three
and the global lower bound only at arguments at least three. -/
theorem row_buchstab_range (i : Fin 16) (t u : ℝ)
    (htl : (numericData i 0 : ℝ) ≤ t) (htu : t ≤ (numericData i 1 : ℝ))
    (hul : (numericData i 2 : ℝ) + numericData i 3*t ≤ u)
    (huu : u ≤ (numericData i 4 : ℝ) + numericData i 5*t) :
    if isLog i then 2 ≤ (1-t-u)/u ∧ (1-t-u)/u ≤ 3
      else 3 ≤ (1-t-u)/u := by
  have hu : 0 < u := (row_kernel_bounds i t u htl htu hul huu).2.1
  fin_cases i <;> norm_num [numericData, isLog] at *
  all_goals first
    | constructor
      · apply (le_div_iff₀ hu).mpr
        linarith
      · apply (div_le_iff₀ hu).mpr
        linarith
    | apply (le_div_iff₀ hu).mpr
      linarith

/-- Pages 281 and 282: every proposed polynomial lies below its full source kernel. -/
theorem polynomial_le (i : Fin 16) (t u : ℝ)
    (htl : (numericData i 0 : ℝ) ≤ t) (htu : t ≤ (numericData i 1 : ℝ))
    (hul : (numericData i 2 : ℝ) + numericData i 3*t ≤ u)
    (huu : u ≤ (numericData i 4 : ℝ) + numericData i 5*t) :
    polynomial i t u ≤ kernel i t u := by
  obtain ⟨ht, hu, hv, hct, htc, hcu, huc, hcv, hvc, hs⟩ :=
    row_kernel_bounds i t u htl htu hul huu
  obtain ⟨hit0, hit⟩ := reciprocal_bounds t (numericData i 6) ht hct htc
  obtain ⟨hiu0, hiu⟩ := reciprocal_bounds u (numericData i 7) hu hcu huc
  obtain ⟨hiv0, hiv⟩ := reciprocal_bounds (1-t-u) (numericData i 8) hv hcv hvc
  by_cases hk : isLog i = true
  · obtain ⟨hit0, hit⟩ := logReciprocal_bounds t (numericData i 6) ht hct htc
    obtain ⟨hiu0, hiu⟩ := logReciprocal_bounds u (numericData i 7) hu hcu huc
    obtain ⟨hiv0, hiv⟩ := logReciprocal_bounds (1-t-u) (numericData i 8) hv hcv hvc
    have hs := hs hk
    have hlog := log_three_terms t u hu hv hs
    have hp : polynomial i t u ≤
        (1/t)*(1/u)*(1/(1-t-u)) *
          (1 + 2*(1-t-3*u)/(1-t-u) + (2/3:ℝ)*((1-t-3*u)/(1-t-u))^3 +
            (2/5:ℝ)*((1-t-3*u)/(1-t-u))^5) := by
      dsimp [polynomial]
      simp only [hk, ↓reduceIte]
      calc
        _ ≤ (1/t)*(1/u)*(1/(1-t-u)) *
            (1 + 2*(1-t-3*u)*(1/(1-t-u)) +
              (2/3:ℝ)*(1-t-3*u)^3*(1/(1-t-u))^3 +
              (2/5:ℝ)*(1-t-3*u)^5*(1/(1-t-u))^5) := by
                gcongr
        _ = _ := by ring
    have hnum : 1 + 2*(1-t-3*u)/(1-t-u) + (2/3:ℝ)*((1-t-3*u)/(1-t-u))^3 +
        (2/5:ℝ)*((1-t-3*u)/(1-t-u))^5 ≤ 1 + Real.log ((1-t)/u-2) := by
      convert (add_le_add_left hlog 1) using 1 <;> ring
    have hm := mul_le_mul_of_nonneg_left hnum
      (by positivity : 0 ≤ (1/t)*(1/u)*(1/(1-t-u)))
    unfold kernel
    simp only [hk, ↓reduceIte]
    convert hp.trans hm using 1
    field_simp [ht.ne', hu.ne', hv.ne']
  · simp only [polynomial, kernel, hk, Bool.false_eq_true, ↓reduceIte]
    calc
      _ ≤ 0.5607 * (1/t) * (1/u)^2 := by gcongr
      _ = _ := by ring

#print axioms reciprocal_bounds
#print axioms logReciprocal_bounds
#print axioms log_three_terms
#print axioms row_endpoints
#print axioms row_kernel_bounds
#print axioms row_buchstab_range
#print axioms polynomial_le
end
end LeanLab.Languasco2004.RemainderData564
