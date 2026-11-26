/-
Faithful split of the MEDIUM leaf caseB_ratio_high of Decomp119LeavesIIS124CaseBRatio,
P0013 page 72, case b, on x ≥ 1e25. The display caseBDisplay is the sum of four terms,
caseBT1 to caseBT4 below, equal to it by rfl. The range is cut at 1e26, 3e27 and 1e30;
on each piece each term divided by x^{5/6} (log x)^{3/2} gets one constant, one leaf per term
and piece. mpmath at 30 digits on grids of 4001 points in log x per bounded piece and
20001 points on [1e30, 1e5000] for the last, plus spot values up to 1e100000 where every
ratio tends to 0, checks each leaf TRUE with the margin in its doc comment.
The sums of the constants are 0.2485, 0.2483, 0.2477 and 0.24955, each at most 0.24956.
These are float grid checks, not proofs. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseB
import LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseBT4Helpers
import LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseBT4Seg1Helpers

namespace LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseBRatioHigh
open LeanLab.HelfgottArcs.Decomp119 LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseB
  LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseBT4Helpers
  LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseBT4Seg1Helpers

/-- P0013 page 72, case b display, the first term, the large sieve contribution from 5.36 with ̥(y); caseBDisplay is caseBT1 + caseBT2 + caseBT3 + caseBT4. -/
noncomputable def caseBT1 (x : ℝ) : ℝ :=
  let y := x ^ ((1 : ℝ) / 3) / 6
  let Q := x / U x
  let κ2 : ℝ := 1.93768
  let κ6 : ℝ := 0.60428
  let κ7 : ℝ := 0.1281
  let κ9 : ℝ := 3.9086
  2 * x * Real.sqrt (frakF y) / Real.sqrt (8 * y) *
      Real.sqrt ((Real.log (x / (U x * Real.exp 2 * (8 * y))) +
          Real.log (3 * y) * Real.log (Real.log (x / (3 * U x * y)) /
            Real.log (8 * Real.exp 2 / 3))) *
        (κ6 * Real.log (x / (U x * Real.exp 2 * (2 * y))) + 2 * κ7))

/-- P0013 page 72, case b display, the second term, the two differences of (log)^{3/2} with factor 2κ2/3; caseBDisplay is caseBT1 + caseBT2 + caseBT3 + caseBT4. -/
noncomputable def caseBT2 (x : ℝ) : ℝ :=
  let y := x ^ ((1 : ℝ) / 3) / 6
  let Q := x / U x
  let κ2 : ℝ := 1.93768
  let κ6 : ℝ := 0.60428
  let κ7 : ℝ := 0.1281
  let κ9 : ℝ := 3.9086
  2 * κ2 / 3 * (x / Real.sqrt (16 * y) *
        (Real.log (8 * Real.exp 2 * y) ^ ((3 : ℝ) / 2) - Real.log y ^ ((3 : ℝ) / 2)) +
      x / 4 / Real.sqrt (Q - y) *
        (Real.log (Real.exp 2 * U x) ^ ((3 : ℝ) / 2) - Real.log y ^ ((3 : ℝ) / 2)))

/-- P0013 page 72, case b display, the third term, the κ2 and κ9 contribution times x/√V; caseBDisplay is caseBT1 + caseBT2 + caseBT3 + caseBT4. -/
noncomputable def caseBT3 (x : ℝ) : ℝ :=
  let y := x ^ ((1 : ℝ) / 3) / 6
  let Q := x / U x
  let κ2 : ℝ := 1.93768
  let κ6 : ℝ := 0.60428
  let κ7 : ℝ := 0.1281
  let κ9 : ℝ := 3.9086
  (κ2 / Real.sqrt (2 * (1 - y / Q)) *
        (Real.sqrt (Real.log (V x)) + Real.sqrt (1 / Real.log (V x))) + κ9) *
      (x / Real.sqrt (V x))

/-- P0013 page 72, case b display, the fourth term, the κ2 √(2̥(y)) contribution times x/√U; caseBDisplay is caseBT1 + caseBT2 + caseBT3 + caseBT4. -/
noncomputable def caseBT4 (x : ℝ) : ℝ :=
  let y := x ^ ((1 : ℝ) / 3) / 6
  let Q := x / U x
  let κ2 : ℝ := 1.93768
  let κ6 : ℝ := 0.60428
  let κ7 : ℝ := 0.1281
  let κ9 : ℝ := 3.9086
  κ2 * Real.sqrt (2 * frakF y) *
      Real.sqrt (Real.log (Real.exp 2 * U x) / Real.log (8 * Real.exp 2 / 3)) *
      (x / Real.sqrt (U x))

/-- The case b display is the sum of its four terms, by definition. -/
theorem caseBDisplay_eq (x : ℝ) :
    caseBDisplay x = caseBT1 x + caseBT2 x + caseBT3 x + caseBT4 x := rfl

/-- LEAF: P0013 page 72, case b, maximum of the ratio of term 1 to x^{5/6} (log x)^{3/2} on 1e25 ≤ x ≤ 1e26.
Class MEDIUM, a numerical bound; mpmath 30 digit grid check TRUE, margin 4.3e-5. -/
theorem caseBT1_seg1 (x : ℝ) (ha : 1e25 ≤ x) (hb : x ≤ 1e26) :
    caseBT1 x ≤ 0.1582 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- LEAF: P0013 page 72, case b, maximum of the ratio of term 2 to x^{5/6} (log x)^{3/2} on 1e25 ≤ x ≤ 1e26.
Class MEDIUM, a numerical bound; mpmath 30 digit grid check TRUE, margin 2.3e-5. -/
theorem caseBT2_seg1 (x : ℝ) (ha : 1e25 ≤ x) (hb : x ≤ 1e26) :
    caseBT2 x ≤ 0.0490 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- LEAF: P0013 page 72, case b, maximum of the ratio of term 3 to x^{5/6} (log x)^{3/2} on 1e25 ≤ x ≤ 1e26.
Class MEDIUM, a numerical bound; mpmath 30 digit grid check TRUE, margin 1.1e-5. -/
theorem caseBT3_seg1 (x : ℝ) (ha : 1e25 ≤ x) (hb : x ≤ 1e26) :
    caseBT3 x ≤ 0.0399 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- LEAF: P0013 page 72, case b, maximum of the ratio of term 4 to x^{5/6} (log x)^{3/2} on 1e25 ≤ x ≤ 1e26.
Class MEDIUM, a numerical bound; mpmath 30 digit grid check TRUE, margin 5.1e-5. -/
theorem caseBT4_seg1 (x : ℝ) (ha : 1e25 ≤ x) (hb : x ≤ 1e26) :
    caseBT4 x ≤ 0.0014 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) ha
  set c : ℝ := 500 * Real.sqrt 6 with hc
  set t : ℝ := x ^ ((1 : ℝ) / 3) with ht
  set L : ℝ := Real.log x with hL
  have ht0 : 0 < t := Real.rpow_pos_of_pos hx0 _
  have hc0 : 0 < c := by positivity
  have hcge : 1224.5 ≤ c := by
    have : 2.449 ≤ Real.sqrt 6 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    rw [hc]; linarith
  have hL1 := logx_ge1 x ha
  have hL2 := logx_le1 x hx0 hb
  have hdef : caseBT4 x = 1.93768 * Real.sqrt (2 * frakF (t / 6)) *
      Real.sqrt (Real.log (Real.exp 2 * (c * t)) / Real.log (8 * Real.exp 2 / 3)) *
      (x / Real.sqrt (c * t)) := rfl
  have hlogt : Real.log t = L / 3 := by
    rw [ht, Real.log_rpow hx0]; ring
  have hA : Real.log (Real.exp 2 * (c * t)) = 2 + Real.log c + L / 3 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp,
      Real.log_mul hc0.ne' ht0.ne', hlogt]; ring
  have hB : Real.log (8 * Real.exp 2 / 3) = Real.log (8 / 3) + 2 := by
    rw [show 8 * Real.exp 2 / 3 = 8 / 3 * Real.exp 2 by ring,
      Real.log_mul (by norm_num) (by positivity), Real.log_exp]
  have hz : Real.log (t / 6) = L / 3 - Real.log 6 := by
    rw [Real.log_div ht0.ne' (by norm_num), hlogt]
  have h6 := log6_le
  have h6g := log6_ge
  have h60 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  set z := Real.log (t / 6) with hzdef
  have hz0 : 0 < z := by rw [hz]; linarith
  set u := Real.log z with hu
  have hulo : 2.8 ≤ u := by
    rw [hu, Real.le_log_iff_exp_le hz0]; have := exp_28_lt; rw [hz]; linarith
  have huhi : u ≤ 3.05 + (L / 3 - 1.69 - 21) / 21 := by
    have h1 : u = Real.log 21 + Real.log (z / 21) := by
      rw [hu, Real.log_div hz0.ne' (by norm_num)]; ring
    have h2 := Real.log_le_sub_one_of_pos (show 0 < z / 21 by positivity)
    have h3 := log21_le
    rw [h1]
    have : z / 21 - 1 ≤ (L / 3 - 1.69 - 21) / 21 := by rw [hz]; linarith
    linarith
  have hu0 : 0 < u := by linarith
  have hF : frakF (t / 6) = Real.exp Real.eulerMascheroniConstant * u + 2.50637 / u := rfl
  have heg := exp_gamma_lt
  have hFle : frakF (t / 6) ≤ 1.8222 * (3.05 + (L / 3 - 1.69 - 21) / 21) + 2.50637 / 2.8 := by
    rw [hF]
    have e1 : Real.exp Real.eulerMascheroniConstant * u ≤ 1.8222 * (3.05 + (L / 3 - 1.69 - 21) / 21) := by
      have := Real.exp_pos Real.eulerMascheroniConstant
      nlinarith
    have e2 : 2.50637 / u ≤ 2.50637 / 2.8 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hulo
    linarith
  have hF0 : 0 ≤ frakF (t / 6) := by
    rw [hF]; have := Real.exp_pos Real.eulerMascheroniConstant; positivity
  set A := Real.log (Real.exp 2 * (c * t)) with hAdef
  set B := Real.log (8 * Real.exp 2 / 3) with hBdef
  have hlc := logc_le
  have hlc0 : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  have hAle : A ≤ 2 + 7.12 + L / 3 := by rw [hA]; linarith
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hBge : 2.95 ≤ B := by rw [hB]; linarith [log_83_ge]
  have hB0 : 0 < B := by linarith
  have hP := poly1 L hL1 (frakF (t / 6)) A B c hF0 hFle hA0 hAle hBge hcge
  -- x / sqrt(c t) = x^(5/6) / sqrt c
  have hsx : x / Real.sqrt (c * t) = x ^ ((5 : ℝ) / 6) / Real.sqrt c := by
    have hst : Real.sqrt t = x ^ ((1 : ℝ) / 6) := by
      rw [Real.sqrt_eq_rpow, ht, ← Real.rpow_mul hx0.le]; norm_num
    have hxx : x = x ^ ((5 : ℝ) / 6) * x ^ ((1 : ℝ) / 6) := by
      rw [← Real.rpow_add hx0]; norm_num
    rw [Real.sqrt_mul hc0.le, hst]
    have : 0 < x ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hx0 _
    have : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
    field_simp
    nth_rewrite 1 [hxx]; ring
  rw [hdef, hsx]
  have hx56 : 0 < x ^ ((5 : ℝ) / 6) := Real.rpow_pos_of_pos hx0 _
  have hL0 : 0 ≤ L := by linarith
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
  have key : 1.93768 * Real.sqrt (2 * frakF (t / 6)) * Real.sqrt (A / B) / Real.sqrt c
      ≤ 0.0014 * L ^ ((3 : ℝ) / 2) := by
    have hl0 : 0 ≤ 1.93768 * Real.sqrt (2 * frakF (t / 6)) * Real.sqrt (A / B) / Real.sqrt c := by
      positivity
    have hr0 : 0 ≤ 0.0014 * L ^ ((3 : ℝ) / 2) := by positivity
    rw [← pow_le_pow_iff_left₀ hl0 hr0 (two_ne_zero)]
    have e1 : (1.93768 * Real.sqrt (2 * frakF (t / 6)) * Real.sqrt (A / B) / Real.sqrt c) ^ 2
        = (1.93768 : ℝ) ^ 2 * (2 * frakF (t / 6)) * (A / B) / c := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
        Real.sq_sqrt hc0.le]
    have e2 : (0.0014 * L ^ ((3 : ℝ) / 2)) ^ 2 = 0.0014 ^ 2 * L ^ 3 := by
      rw [mul_pow, ← Real.rpow_natCast (L ^ ((3 : ℝ) / 2)), ← Real.rpow_mul hL0]
      norm_num
    rw [e1, e2]; exact hP
  have := mul_le_mul_of_nonneg_left key hx56.le
  calc 1.93768 * Real.sqrt (2 * frakF (t / 6)) * Real.sqrt (A / B) * (x ^ ((5 : ℝ) / 6) / Real.sqrt c)
      = x ^ ((5 : ℝ) / 6) * (1.93768 * Real.sqrt (2 * frakF (t / 6)) * Real.sqrt (A / B) / Real.sqrt c) := by
        ring
    _ ≤ x ^ ((5 : ℝ) / 6) * (0.0014 * L ^ ((3 : ℝ) / 2)) := this
    _ = 0.0014 * x ^ ((5 : ℝ) / 6) * L ^ ((3 : ℝ) / 2) := by ring

/-- LEAF: P0013 page 72, case b, maximum of the ratio of term 1 to x^{5/6} (log x)^{3/2} on 1e26 ≤ x ≤ 3e27.
Class MEDIUM, a numerical bound; mpmath 30 digit grid check TRUE, margin 1.3e-4. -/
theorem caseBT1_seg2 (x : ℝ) (ha : 1e26 ≤ x) (hb : x ≤ 3e27) :
    caseBT1 x ≤ 0.1618 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- LEAF: P0013 page 72, case b, maximum of the ratio of term 2 to x^{5/6} (log x)^{3/2} on 1e26 ≤ x ≤ 3e27.
Class MEDIUM, a numerical bound; mpmath 30 digit grid check TRUE, margin 5.9e-5. -/
theorem caseBT2_seg2 (x : ℝ) (ha : 1e26 ≤ x) (hb : x ≤ 3e27) :
    caseBT2 x ≤ 0.0471 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- LEAF: P0013 page 72, case b, maximum of the ratio of term 3 to x^{5/6} (log x)^{3/2} on 1e26 ≤ x ≤ 3e27.
Class MEDIUM, a numerical bound; mpmath 30 digit grid check TRUE, margin 5.8e-5. -/
theorem caseBT3_seg2 (x : ℝ) (ha : 1e26 ≤ x) (hb : x ≤ 3e27) :
    caseBT3 x ≤ 0.0381 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- LEAF: P0013 page 72, case b, maximum of the ratio of term 4 to x^{5/6} (log x)^{3/2} on 1e26 ≤ x ≤ 3e27.
Class MEDIUM, a numerical bound; mpmath 30 digit grid check TRUE, margin 3.9e-6. -/
theorem caseBT4_seg2 (x : ℝ) (ha : 1e26 ≤ x) (hb : x ≤ 3e27) :
    caseBT4 x ≤ 0.0013 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- LEAF: P0013 page 72, case b, maximum of the ratio of term 1 to x^{5/6} (log x)^{3/2} on 3e27 ≤ x ≤ 1e30.
Class MEDIUM, a numerical bound; mpmath 30 digit grid check TRUE, margin 3.6e-5. -/
theorem caseBT1_seg3 (x : ℝ) (ha : 3e27 ≤ x) (hb : x ≤ 1e30) :
    caseBT1 x ≤ 0.1663 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- LEAF: P0013 page 72, case b, maximum of the ratio of term 2 to x^{5/6} (log x)^{3/2} on 3e27 ≤ x ≤ 1e30.
Class MEDIUM, a numerical bound; mpmath 30 digit grid check TRUE, margin 3.8e-5. -/
theorem caseBT2_seg3 (x : ℝ) (ha : 3e27 ≤ x) (hb : x ≤ 1e30) :
    caseBT2 x ≤ 0.0445 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- LEAF: P0013 page 72, case b, maximum of the ratio of term 3 to x^{5/6} (log x)^{3/2} on 3e27 ≤ x ≤ 1e30.
Class MEDIUM, a numerical bound; mpmath 30 digit grid check TRUE, margin 8.4e-6. -/
theorem caseBT3_seg3 (x : ℝ) (ha : 3e27 ≤ x) (hb : x ≤ 1e30) :
    caseBT3 x ≤ 0.0356 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- LEAF: P0013 page 72, case b, maximum of the ratio of term 4 to x^{5/6} (log x)^{3/2} on 3e27 ≤ x ≤ 1e30.
Class MEDIUM, a numerical bound; mpmath 30 digit grid check TRUE, margin 7.5e-5. -/
theorem caseBT4_seg3 (x : ℝ) (ha : 3e27 ≤ x) (hb : x ≤ 1e30) :
    caseBT4 x ≤ 0.0013 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) ha
  set c : ℝ := 500 * Real.sqrt 6 with hc
  set t : ℝ := x ^ ((1 : ℝ) / 3) with ht
  set L : ℝ := Real.log x with hL
  have ht0 : 0 < t := Real.rpow_pos_of_pos hx0 _
  have hc0 : 0 < c := by positivity
  have hcge : 1224.5 ≤ c := by
    have : 2.449 ≤ Real.sqrt 6 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    rw [hc]; linarith
  have hL1 := logx_ge x ha
  have hL2 := logx_le x hx0 hb
  have hdef : caseBT4 x = 1.93768 * Real.sqrt (2 * frakF (t / 6)) *
      Real.sqrt (Real.log (Real.exp 2 * (c * t)) / Real.log (8 * Real.exp 2 / 3)) *
      (x / Real.sqrt (c * t)) := rfl
  have hlogt : Real.log t = L / 3 := by
    rw [ht, Real.log_rpow hx0]; ring
  have hA : Real.log (Real.exp 2 * (c * t)) = 2 + Real.log c + L / 3 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp,
      Real.log_mul hc0.ne' ht0.ne', hlogt]; ring
  have hB : Real.log (8 * Real.exp 2 / 3) = Real.log (8 / 3) + 2 := by
    rw [show 8 * Real.exp 2 / 3 = 8 / 3 * Real.exp 2 by ring,
      Real.log_mul (by norm_num) (by positivity), Real.log_exp]
  have hz : Real.log (t / 6) = L / 3 - Real.log 6 := by
    rw [Real.log_div ht0.ne' (by norm_num), hlogt]
  have h6 := log6_le
  have h60 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  set z := Real.log (t / 6) with hzdef
  have hz0 : 0 < z := by rw [hz]; linarith
  set u := Real.log z with hu
  have hulo : 2.5 ≤ u := by
    rw [hu, Real.le_log_iff_exp_le hz0]; have := exp_25_lt; rw [hz]; linarith
  have huhi : u ≤ 3.05 + (L / 3 - 21) / 21 := by
    have h1 : u = Real.log 21 + Real.log (z / 21) := by
      rw [hu, Real.log_div hz0.ne' (by norm_num)]; ring
    have h2 := Real.log_le_sub_one_of_pos (show 0 < z / 21 by positivity)
    have h3 := log21_le
    rw [h1]
    have : z / 21 - 1 ≤ (L / 3 - 21) / 21 := by rw [hz]; linarith
    linarith
  have hu0 : 0 < u := by linarith
  have hF : frakF (t / 6) = Real.exp Real.eulerMascheroniConstant * u + 2.50637 / u := rfl
  have heg := exp_gamma_lt
  have hFle : frakF (t / 6) ≤ 1.8222 * (3.05 + (L / 3 - 21) / 21) + 2.50637 / 2.5 := by
    rw [hF]
    have e1 : Real.exp Real.eulerMascheroniConstant * u ≤ 1.8222 * (3.05 + (L / 3 - 21) / 21) := by
      have := Real.exp_pos Real.eulerMascheroniConstant
      nlinarith
    have e2 : 2.50637 / u ≤ 2.50637 / 2.5 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hulo
    linarith
  have hF0 : 0 ≤ frakF (t / 6) := by
    rw [hF]; have := Real.exp_pos Real.eulerMascheroniConstant; positivity
  set A := Real.log (Real.exp 2 * (c * t)) with hAdef
  set B := Real.log (8 * Real.exp 2 / 3) with hBdef
  have hlc := logc_le
  have hlc0 : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  have hAle : A ≤ 2 + 7.12 + L / 3 := by rw [hA]; linarith
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hBge : 2.95 ≤ B := by rw [hB]; linarith [log_83_ge]
  have hB0 : 0 < B := by linarith
  have hP := poly L hL1 hL2 (frakF (t / 6)) A B c hF0 hFle hA0 hAle hBge hcge
  -- x / sqrt(c t) = x^(5/6) / sqrt c
  have hsx : x / Real.sqrt (c * t) = x ^ ((5 : ℝ) / 6) / Real.sqrt c := by
    have hst : Real.sqrt t = x ^ ((1 : ℝ) / 6) := by
      rw [Real.sqrt_eq_rpow, ht, ← Real.rpow_mul hx0.le]; norm_num
    have hxx : x = x ^ ((5 : ℝ) / 6) * x ^ ((1 : ℝ) / 6) := by
      rw [← Real.rpow_add hx0]; norm_num
    rw [Real.sqrt_mul hc0.le, hst]
    have : 0 < x ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hx0 _
    have : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
    field_simp
    nth_rewrite 1 [hxx]; ring
  rw [hdef, hsx]
  have hx56 : 0 < x ^ ((5 : ℝ) / 6) := Real.rpow_pos_of_pos hx0 _
  have hL0 : 0 ≤ L := by linarith
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
  have key : 1.93768 * Real.sqrt (2 * frakF (t / 6)) * Real.sqrt (A / B) / Real.sqrt c
      ≤ 0.0013 * L ^ ((3 : ℝ) / 2) := by
    have hl0 : 0 ≤ 1.93768 * Real.sqrt (2 * frakF (t / 6)) * Real.sqrt (A / B) / Real.sqrt c := by
      positivity
    have hr0 : 0 ≤ 0.0013 * L ^ ((3 : ℝ) / 2) := by positivity
    rw [← pow_le_pow_iff_left₀ hl0 hr0 (two_ne_zero)]
    have e1 : (1.93768 * Real.sqrt (2 * frakF (t / 6)) * Real.sqrt (A / B) / Real.sqrt c) ^ 2
        = (1.93768 : ℝ) ^ 2 * (2 * frakF (t / 6)) * (A / B) / c := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
        Real.sq_sqrt hc0.le]
    have e2 : (0.0013 * L ^ ((3 : ℝ) / 2)) ^ 2 = 0.0013 ^ 2 * L ^ 3 := by
      rw [mul_pow, ← Real.rpow_natCast (L ^ ((3 : ℝ) / 2)), ← Real.rpow_mul hL0]
      norm_num
    rw [e1, e2]; exact hP
  have := mul_le_mul_of_nonneg_left key hx56.le
  calc 1.93768 * Real.sqrt (2 * frakF (t / 6)) * Real.sqrt (A / B) * (x ^ ((5 : ℝ) / 6) / Real.sqrt c)
      = x ^ ((5 : ℝ) / 6) * (1.93768 * Real.sqrt (2 * frakF (t / 6)) * Real.sqrt (A / B) / Real.sqrt c) := by
        ring
    _ ≤ x ^ ((5 : ℝ) / 6) * (0.0013 * L ^ ((3 : ℝ) / 2)) := this
    _ = 0.0013 * x ^ ((5 : ℝ) / 6) * L ^ ((3 : ℝ) / 2) := by ring

/-- LEAF: P0013 page 72, case b, maximum of the ratio of term 1 to x^{5/6} (log x)^{3/2} on x ≥ 1e30.
Class MEDIUM, a numerical bound; mpmath 30 digit grid check TRUE, margin 7.0e-5; the ratio tends to 0 as x grows. -/
theorem caseBT1_seg4 (x : ℝ) (ha : 1e30 ≤ x) :
    caseBT1 x ≤ 0.1756 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- LEAF: P0013 page 72, case b, maximum of the ratio of term 2 to x^{5/6} (log x)^{3/2} on x ≥ 1e30.
Class MEDIUM, a numerical bound; mpmath 30 digit grid check TRUE, margin 2.2e-5; the ratio tends to 0 as x grows. -/
theorem caseBT2_seg4 (x : ℝ) (ha : 1e30 ≤ x) :
    caseBT2 x ≤ 0.0407 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- LEAF: P0013 page 72, case b, maximum of the ratio of term 3 to x^{5/6} (log x)^{3/2} on x ≥ 1e30.
Class MEDIUM, a numerical bound; mpmath 30 digit grid check TRUE, margin 7.0e-5; the ratio tends to 0 as x grows. -/
theorem caseBT3_seg4 (x : ℝ) (ha : 1e30 ≤ x) :
    caseBT3 x ≤ 0.0321 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- LEAF: P0013 page 72, case b, maximum of the ratio of term 4 to x^{5/6} (log x)^{3/2} on x ≥ 1e30.
Class MEDIUM, a numerical bound; mpmath 30 digit grid check TRUE, margin 2.9e-5; the ratio tends to 0 as x grows. -/
theorem caseBT4_seg4 (x : ℝ) (ha : 1e30 ≤ x) :
    caseBT4 x ≤ 0.00115 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- Sum of four term bounds against the target constant. -/
theorem sum_bound (x c1 c2 c3 c4 : ℝ) (hx : 1 ≤ x) (hc : c1 + c2 + c3 + c4 ≤ 0.24956)
    (h1 : caseBT1 x ≤ c1 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2))
    (h2 : caseBT2 x ≤ c2 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2))
    (h3 : caseBT3 x ≤ c3 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2))
    (h4 : caseBT4 x ≤ c4 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2)) :
    caseBDisplay x ≤ 0.24956 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  have hD : 0 ≤ x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg (Real.log_nonneg hx) _)
  rw [caseBDisplay_eq]
  simp only [mul_assoc] at h1 h2 h3 h4 ⊢
  nlinarith

/-- Assembly of caseB_ratio_high from the sixteen leaves, exact parent statement. -/
theorem caseB_ratio_high_of_leaves (x : ℝ) (hx1 : 1e25 ≤ x) :
    caseBDisplay x ≤ 0.24956 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  have hx : (1 : ℝ) ≤ x := le_trans (by norm_num) hx1
  rcases le_or_gt x 1e26 with h1 | h1
  · exact sum_bound x _ _ _ _ hx (by norm_num) (caseBT1_seg1 x hx1 h1) (caseBT2_seg1 x hx1 h1)
      (caseBT3_seg1 x hx1 h1) (caseBT4_seg1 x hx1 h1)
  rcases le_or_gt x 3e27 with h2 | h2
  · exact sum_bound x _ _ _ _ hx (by norm_num) (caseBT1_seg2 x h1.le h2)
      (caseBT2_seg2 x h1.le h2) (caseBT3_seg2 x h1.le h2) (caseBT4_seg2 x h1.le h2)
  rcases le_or_gt x 1e30 with h3 | h3
  · exact sum_bound x _ _ _ _ hx (by norm_num) (caseBT1_seg3 x h2.le h3)
      (caseBT2_seg3 x h2.le h3) (caseBT3_seg3 x h2.le h3) (caseBT4_seg3 x h2.le h3)
  · exact sum_bound x _ _ _ _ hx (by norm_num) (caseBT1_seg4 x h3.le)
      (caseBT2_seg4 x h3.le) (caseBT3_seg4 x h3.le) (caseBT4_seg4 x h3.le)

end LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseBRatioHigh
