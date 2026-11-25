import LeanLab.ChenDoubleSieve.Feed1122_Decomp275b_explicit
import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.Feed1122_Decomp275b_explicit4
import LeanLab.ChenDoubleSieve.Feed1122_Decomp275b_explicit3
import LeanLab.ChenDoubleSieve.Feed1122_Decomp275b_explicit2
import LeanLab.ChenDoubleSieve.Feed1122_Decomp275b_explicit1
import LeanLab.ChenDoubleSieve.Feed1122_Decomp275b_explicit0

/-!
Elementary forms of the six values F0 to F5 of the final display of Wu 2004 Section 10,
https://arxiv.org/pdf/0705.1652, page 42, indices 0 to 5 of `integralTerms`.
The explicit formulas of page 6 equation 2.6 for F and f, proved in
Feed1122_Decomp275b_explicit.lean, are substituted; the factor exp γ cancels exactly.
Each LEAF below is a purely elementary numerical inequality with no F, f, ω or exp γ.
Each `value_i_of_explicit` theorem derives the original leaf statement form of
Feed1122_Decomp275b_integral_evaluation.lean from `IsLinearSieve` and that LEAF;
the congruence steps are fully proved. That file is not edited.
Numerical values by adaptive quadrature: F0 13.4736135364, F1 3.8918539726,
F2 20.4320972999, F3 17.3272403125, F4 0.6973756066, F5 2.1181194840.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set MeasureTheory

namespace LeanLab.ChenDoubleSieve.Task275.Feed1122ValuesExplicit
open Wu04Functional (IsLinearSieve IsBuchstab)
open Feed1122Explicit

/-- Wu 2004 page 6 equation 2.6 made explicit for 3 ≤ t ≤ 5:
F t = exp γ times the quantity 2 plus twice the integral from 3 to t of log of s minus 2
over s minus 1, all over t. -/
theorem F_on_3_5 {F f : ℝ → ℝ} (h : IsLinearSieve F f) (t : ℝ) (h3 : 3 ≤ t) (h5 : t ≤ 5) :
    F t = exp eulerMascheroniConstant *
      ((2 + 2 * ∫ s in (3:ℝ)..t, Real.log (s - 2) / (s - 1)) / t) := by
  have hm := F_mid h t h3 h5
  have hc : (∫ s in (3:ℝ)..t, f (s - 1)) =
      2 * exp eulerMascheroniConstant * ∫ s in (3:ℝ)..t, Real.log (s - 2) / (s - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [uIcc_of_le h3] at hs
    rw [f_eq h (s - 1) (by linarith [hs.1]) (by linarith [hs.2])]
    have : s - 1 - 1 = s - 2 := by ring
    rw [this]
    ring
  rw [hc] at hm
  have ht : t ≠ 0 := by linarith
  field_simp
  linear_combination hm

/-- The same formula on 2 ≤ t ≤ 5, with the upper limit max t 3, so the integral
vanishes for t ≤ 3. -/
theorem F_on_2_5 {F f : ℝ → ℝ} (h : IsLinearSieve F f) (t : ℝ) (h2 : 2 ≤ t) (h5 : t ≤ 5) :
    F t = exp eulerMascheroniConstant *
      ((2 + 2 * ∫ s in (3:ℝ)..max t 3, Real.log (s - 2) / (s - 1)) / t) := by
  rcases le_total t 3 with h3 | h3
  · rw [max_eq_right h3, intervalIntegral.integral_same, F_eq h t (by linarith) h3]
    ring
  · rw [max_eq_left h3]
    exact F_on_3_5 h t h3 h5

/-! ### F4, index 4 -/

/-- PROVED in Feed1122_Decomp275b_explicit4: Wu 2004 page 42 final display value of F4 with f from equation 2.6 made explicit, certified numerical integration. -/
theorem leaf_explicit4 :
    (0.697375 : ℝ) ≤ 48 * ∫ t in (1/12 : ℝ)..(29/250),
      (∫ u in t..(29/250 : ℝ),
        Real.log (5 - 12 * t - 12 * u) / (6 - 12 * t - 12 * u) / u) / t := by
  exact LeanLab.ChenDoubleSieve.Feed1122Explicit4.explicit4

/-- Wu 2004 page 42, equation 10.5: index 4 of `integralTerms` equals the elementary
double integral of `leaf_explicit4`. -/
theorem integralTerms4_eq {F f ω : ℝ → ℝ} (h : IsLinearSieve F f) :
    integralTerms F f ω 4 = 48 * ∫ t in (1/12 : ℝ)..(29/250),
      (∫ u in t..(29/250 : ℝ),
        Real.log (5 - 12 * t - 12 * u) / (6 - 12 * t - 12 * u) / u) / t := by
  simp only [integralTerms, Matrix.cons_val]
  rw [show kappa1 = 1 / 12 from rfl, show kappa2 = 29 / 250 from rfl]
  set eg := exp eulerMascheroniConstant with heg
  have hpos : 0 < eg := exp_pos _
  have hout : (∫ t in (1/12 : ℝ)..(29/250),
      (∫ u in t..(29/250 : ℝ), f ((1 / 2 - t - u) / (1 / 12)) / u) / t) =
      2 * eg * ∫ t in (1/12 : ℝ)..(29/250),
        (∫ u in t..(29/250 : ℝ),
          Real.log (5 - 12 * t - 12 * u) / (6 - 12 * t - 12 * u) / u) / t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le (by norm_num)] at ht
    have hin : (∫ u in t..(29/250 : ℝ), f ((1 / 2 - t - u) / (1 / 12)) / u) =
        2 * eg * ∫ u in t..(29/250 : ℝ),
          Real.log (5 - 12 * t - 12 * u) / (6 - 12 * t - 12 * u) / u := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [uIcc_of_le ht.2] at hu
      have ha : (1 / 2 - t - u) / (1 / 12) = 6 - 12 * t - 12 * u := by ring
      rw [ha, f_eq h _ (by linarith [hu.2, ht.2]) (by linarith [hu.1, ht.1])]
      have hb : 6 - 12 * t - 12 * u - 1 = 5 - 12 * t - 12 * u := by ring
      rw [hb]
      ring
    rw [hin]
    ring
  rw [hout, ← mul_assoc]
  congr 1
  field_simp
  ring

/-- Wu 2004 page 42 final display, F4: the leaf_value4 statement form, from
`IsLinearSieve` and `leaf_explicit4`. -/
theorem value4_of_explicit (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (_hω : IsBuchstab ω) :
    (0.697375 : ℝ) ≤ integralTerms F f ω 4 := by
  rw [integralTerms4_eq h]
  exact leaf_explicit4

/-! ### F5, index 5 -/

/-- LEAF: Wu 2004 page 42 final display value of F5 with f from equation 2.6 made explicit, certified numerical integration. Class HARD. -/
theorem leaf_explicit5 :
    (2.118119 : ℝ) ≤ 48 * ∫ t in (1/12 : ℝ)..(29/250),
      (∫ u in (29/250 : ℝ)..(1/3 - t),
        Real.log (5 - 12 * t - 12 * u) / (6 - 12 * t - 12 * u) / u) / t := by
  sorry

/-- Wu 2004 page 42, equation 10.5: index 5 of `integralTerms` equals the elementary
double integral of `leaf_explicit5`. -/
theorem integralTerms5_eq {F f ω : ℝ → ℝ} (h : IsLinearSieve F f) :
    integralTerms F f ω 5 = 48 * ∫ t in (1/12 : ℝ)..(29/250),
      (∫ u in (29/250 : ℝ)..(1/3 - t),
        Real.log (5 - 12 * t - 12 * u) / (6 - 12 * t - 12 * u) / u) / t := by
  simp only [integralTerms, Matrix.cons_val]
  rw [show kappa1 = 1 / 12 from rfl, show kappa2 = 29 / 250 from rfl]
  set eg := exp eulerMascheroniConstant with heg
  have hpos : 0 < eg := exp_pos _
  have hout : (∫ t in (1/12 : ℝ)..(29/250),
      (∫ u in (29/250 : ℝ)..(1 / 2 - 2 * (1 / 12) - t),
        f ((1 / 2 - t - u) / (1 / 12)) / u) / t) =
      2 * eg * ∫ t in (1/12 : ℝ)..(29/250),
        (∫ u in (29/250 : ℝ)..(1/3 - t),
          Real.log (5 - 12 * t - 12 * u) / (6 - 12 * t - 12 * u) / u) / t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le (by norm_num)] at ht
    have hup : (1 / 2 - 2 * (1 / 12) - t : ℝ) = 1 / 3 - t := by ring
    have hin : (∫ u in (29/250 : ℝ)..(1/3 - t), f ((1 / 2 - t - u) / (1 / 12)) / u) =
        2 * eg * ∫ u in (29/250 : ℝ)..(1/3 - t),
          Real.log (5 - 12 * t - 12 * u) / (6 - 12 * t - 12 * u) / u := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [uIcc_of_le (by linarith [ht.2])] at hu
      have ha : (1 / 2 - t - u) / (1 / 12) = 6 - 12 * t - 12 * u := by ring
      rw [ha, f_eq h _ (by linarith [hu.2]) (by linarith [hu.1, ht.1])]
      have hb : 6 - 12 * t - 12 * u - 1 = 5 - 12 * t - 12 * u := by ring
      rw [hb]
      ring
    rw [hup, hin]
    ring
  rw [hout, ← mul_assoc]
  congr 1
  field_simp
  ring

/-- Wu 2004 page 42 final display, F5: the leaf_value5 statement form, from
`IsLinearSieve` and `leaf_explicit5`. -/
theorem value5_of_explicit (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (_hω : IsBuchstab ω) :
    (2.118119 : ℝ) ≤ integralTerms F f ω 5 := by
  rw [integralTerms5_eq h]
  exact leaf_explicit5

/-! ### F1, index 1 -/

/-- PROVED in Feed1122_Decomp275b_explicit1: Wu 2004 page 42 final display value of F1 with F from equation 2.6 made explicit, certified numerical integration. -/
theorem leaf_explicit1 :
    4 * (∫ t in (96/29 : ℝ)..5,
      (2 + 2 * ∫ s in (3:ℝ)..t, Real.log (s - 2) / (s - 1)) / t) ≤ (3.891854 : ℝ) := by
  exact LeanLab.ChenDoubleSieve.Feed1122Explicit1.explicit1

/-- Wu 2004 page 42, equation 10.3: index 1 of `integralTerms` equals the elementary
integral of `leaf_explicit1`. -/
theorem integralTerms1_eq {F f ω : ℝ → ℝ} (h : IsLinearSieve F f) :
    integralTerms F f ω 1 = 4 * (∫ t in (96/29 : ℝ)..5,
      (2 + 2 * ∫ s in (3:ℝ)..t, Real.log (s - 2) / (s - 1)) / t) := by
  simp only [integralTerms, Matrix.cons_val]
  have e1 : (1 / (2 * kappa2) - 1 : ℝ) = 96 / 29 := by norm_num [kappa2]
  have e2 : (1 / (2 * kappa1) - 1 : ℝ) = 5 := by norm_num [kappa1]
  rw [e1, e2]
  set eg := exp eulerMascheroniConstant with heg
  have hpos : 0 < eg := exp_pos _
  have hc : (∫ t in (96/29 : ℝ)..5, F t) = eg * ∫ t in (96/29 : ℝ)..5,
      (2 + 2 * ∫ s in (3:ℝ)..t, Real.log (s - 2) / (s - 1)) / t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le (by norm_num)] at ht
    exact F_on_3_5 h t (by linarith [ht.1]) ht.2
  rw [hc, ← mul_assoc]
  congr 1
  field_simp

/-- Wu 2004 page 42 final display, F1: the leaf_value1 statement form, from
`IsLinearSieve` and `leaf_explicit1`. -/
theorem value1_of_explicit (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (_hω : IsBuchstab ω) :
    integralTerms F f ω 1 ≤ (3.891854 : ℝ) := by
  rw [integralTerms1_eq h]
  exact leaf_explicit1

/-! ### F0, index 0 -/

/-- PROVED in Feed1122_Decomp275b_explicit0: Wu 2004 page 42 final display value of F0 with f and F from equation 2.6 made explicit, certified numerical integration. -/
theorem leaf_explicit0 :
    (13.473613 : ℝ) ≤ 4 * (2 * Real.log 3 + ∫ t in (3 : ℝ)..5,
      (2 + 2 * ∫ s in (3:ℝ)..t, Real.log (s - 2) / (s - 1)) / t) := by
  exact LeanLab.ChenDoubleSieve.Feed1122Explicit0.explicit0

/-- Wu 2004 page 42, equation 10.2: index 0 of `integralTerms` equals the elementary
expression of `leaf_explicit0`. -/
theorem integralTerms0_eq {F f ω : ℝ → ℝ} (h : IsLinearSieve F f) :
    integralTerms F f ω 0 = 4 * (2 * Real.log 3 + ∫ t in (3 : ℝ)..5,
      (2 + 2 * ∫ s in (3:ℝ)..t, Real.log (s - 2) / (s - 1)) / t) := by
  simp only [integralTerms, Matrix.cons_val]
  have e1 : (1 / (2 * kappa1) : ℝ) = 6 := by norm_num [kappa1]
  rw [e1, show kappa1 = 1 / 12 from rfl]
  set eg := exp eulerMascheroniConstant with heg
  have hpos : 0 < eg := exp_pos _
  have h6 := f_mid h 6 (by norm_num) le_rfl
  have h4 : f 4 = 2 * eg * Real.log (4 - 1) / 4 := f_eq h 4 (by norm_num) le_rfl
  have hs : (∫ t in (4:ℝ)..6, F (t - 1)) = ∫ t in (3:ℝ)..5, F t := by
    rw [intervalIntegral.integral_comp_sub_right (fun t => F t)]
    norm_num
  have hc : (∫ t in (3 : ℝ)..5, F t) = eg * ∫ t in (3 : ℝ)..5,
      (2 + 2 * ∫ s in (3:ℝ)..t, Real.log (s - 2) / (s - 1)) / t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le (by norm_num)] at ht
    exact F_on_3_5 h t ht.1 ht.2
  rw [hs, hc, h4] at h6
  have e3 : (4 - 1 : ℝ) = 3 := by norm_num
  rw [e3] at h6
  have hf6 : f 6 = (2 * eg * Real.log 3 + eg * ∫ t in (3 : ℝ)..5,
      (2 + 2 * ∫ s in (3:ℝ)..t, Real.log (s - 2) / (s - 1)) / t) / 6 := by
    rw [eq_div_iff (by norm_num)]
    linear_combination h6
  rw [hf6]
  field_simp
  ring

/-- Wu 2004 page 42 final display, F0: the leaf_value0 statement form, from
`IsLinearSieve` and `leaf_explicit0`. -/
theorem value0_of_explicit (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (_hω : IsBuchstab ω) :
    (13.473613 : ℝ) ≤ integralTerms F f ω 0 := by
  rw [integralTerms0_eq h]
  exact leaf_explicit0

/-! ### F2 and F3, indices 2 and 3 -/

/-- Index 2 and 3 share one shape: 4 over exp γ times the integral of F t over
1 minus t over 6 from a to 5, for 2 ≤ a ≤ 5. -/
theorem shape23_eq {F f : ℝ → ℝ} (h : IsLinearSieve F f) (a : ℝ) (ha2 : 2 ≤ a) (ha5 : a ≤ 5) :
    4 / exp eulerMascheroniConstant * (∫ t in a..5, F t / (1 - 2 * kappa1 * t)) =
      4 * ∫ t in a..5,
        (2 + 2 * ∫ s in (3:ℝ)..max t 3, Real.log (s - 2) / (s - 1)) / t / (1 - t / 6) := by
  set eg := exp eulerMascheroniConstant with heg
  have hpos : 0 < eg := exp_pos _
  have hc : (∫ t in a..5, F t / (1 - 2 * kappa1 * t)) = eg * ∫ t in a..5,
      (2 + 2 * ∫ s in (3:ℝ)..max t 3, Real.log (s - 2) / (s - 1)) / t / (1 - t / 6) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le ha5] at ht
    have hd : (1 - 2 * kappa1 * t) = 1 - t / 6 := by
      rw [show kappa1 = 1 / 12 from rfl]
      ring
    show F t / (1 - 2 * kappa1 * t) = eg * _
    rw [hd, F_on_2_5 h t (by linarith [ht.1]) ht.2]
    ring
  rw [hc, ← mul_assoc]
  congr 1
  field_simp

/-- PROVED in Feed1122_Decomp275b_explicit2: Wu 2004 page 42 final display value of F2 with F from equation 2.6 made explicit, certified numerical integration. -/
theorem leaf_explicit2 :
    4 * (∫ t in (258/125 : ℝ)..5,
      (2 + 2 * ∫ s in (3:ℝ)..max t 3, Real.log (s - 2) / (s - 1)) / t / (1 - t / 6))
      ≤ (20.432098 : ℝ) := by
  exact LeanLab.ChenDoubleSieve.Feed1122Explicit2.explicit2

/-- Wu 2004 page 42 final display, F2: the leaf_value2 statement form, from
`IsLinearSieve` and `leaf_explicit2`. -/
theorem value2_of_explicit (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (_hω : IsBuchstab ω) :
    integralTerms F f ω 2 ≤ (20.432098 : ℝ) := by
  simp only [integralTerms, Matrix.cons_val]
  have e1 : ((1 / 2 - sigma1) / kappa1 : ℝ) = 258 / 125 := by norm_num [sigma1, kappa1]
  have e2 : ((1 / 2 - kappa1) / kappa1 : ℝ) = 5 := by norm_num [kappa1]
  rw [e1, e2, shape23_eq h _ (by norm_num) (by norm_num)]
  exact leaf_explicit2

/-- PROVED in Feed1122_Decomp275b_explicit3: Wu 2004 page 42 final display value of F3 with F from equation 2.6 made explicit, certified numerical integration. -/
theorem leaf_explicit3 :
    4 * (∫ t in (327/125 : ℝ)..5,
      (2 + 2 * ∫ s in (3:ℝ)..max t 3, Real.log (s - 2) / (s - 1)) / t / (1 - t / 6))
      ≤ (17.327241 : ℝ) := by
  exact LeanLab.ChenDoubleSieve.Feed1122Explicit3.explicit3

/-- Wu 2004 page 42 final display, F3: the leaf_value3 statement form, from
`IsLinearSieve` and `leaf_explicit3`. -/
theorem value3_of_explicit (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (_hω : IsBuchstab ω) :
    integralTerms F f ω 3 ≤ (17.327241 : ℝ) := by
  simp only [integralTerms, Matrix.cons_val]
  have e1 : ((1 / 2 - sigma2) / kappa1 : ℝ) = 327 / 125 := by norm_num [sigma2, kappa1]
  have e2 : ((1 / 2 - kappa1) / kappa1 : ℝ) = 5 := by norm_num [kappa1]
  rw [e1, e2, shape23_eq h _ (by norm_num) (by norm_num)]
  exact leaf_explicit3

end LeanLab.ChenDoubleSieve.Task275.Feed1122ValuesExplicit
#print axioms LeanLab.ChenDoubleSieve.Task275.Feed1122ValuesExplicit.F_on_3_5
#print axioms LeanLab.ChenDoubleSieve.Task275.Feed1122ValuesExplicit.F_on_2_5
#print axioms LeanLab.ChenDoubleSieve.Task275.Feed1122ValuesExplicit.integralTerms0_eq
#print axioms LeanLab.ChenDoubleSieve.Task275.Feed1122ValuesExplicit.integralTerms1_eq
#print axioms LeanLab.ChenDoubleSieve.Task275.Feed1122ValuesExplicit.shape23_eq
#print axioms LeanLab.ChenDoubleSieve.Task275.Feed1122ValuesExplicit.integralTerms4_eq
#print axioms LeanLab.ChenDoubleSieve.Task275.Feed1122ValuesExplicit.integralTerms5_eq
#print axioms LeanLab.ChenDoubleSieve.Task275.Feed1122ValuesExplicit.value0_of_explicit
#print axioms LeanLab.ChenDoubleSieve.Task275.Feed1122ValuesExplicit.value1_of_explicit
#print axioms LeanLab.ChenDoubleSieve.Task275.Feed1122ValuesExplicit.value2_of_explicit
#print axioms LeanLab.ChenDoubleSieve.Task275.Feed1122ValuesExplicit.value3_of_explicit
#print axioms LeanLab.ChenDoubleSieve.Task275.Feed1122ValuesExplicit.value4_of_explicit
#print axioms LeanLab.ChenDoubleSieve.Task275.Feed1122ValuesExplicit.value5_of_explicit
