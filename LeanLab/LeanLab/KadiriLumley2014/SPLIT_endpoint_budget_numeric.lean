/-
P0059, Kadiri and Lumley 2014, arXiv 1407.7902v1, page 2 display 2.3, page 3 display 2.7,
page 9 display 2.64 and page 13 Table 2. SPLIT of Task92.endpoint_budget_numeric from
SPLIT_table_endpoint_budget_low.lean, ROUTE BURST S1 burst-20261124.
After dividing display 2.64 at the row endpoint by the positive factor (e^u - 1) X, its
left side is the sum of three pieces: the enlarged Brun Titchmarsh term
2 (1 + delta) times the logarithm quotient of display 2.7 times the endpoint mass ratio
nu over the weight mass of display 2.3, the omega square root term, and u over 2 X.
Each piece gets its own per row bound, and the final comparison of rationals is proved.
The bounds were computed in exact rational arithmetic for the mass ratio, by expanding
the weight polynomial, and in double precision for the logarithm quotient, then rounded
up at the fourth decimal for the quotient and the fifth for the mass ratio, each raised
by one more unit. Per row, log index, quotient bound, mass ratio bound, computed values:
  log 4e18 1.7791 0.03185 from 1.77890 0.031830,  43 1.7786 0.03319 from 1.77840 0.033170,
  44 1.7863 0.03274 from 1.78620 0.032730,  45 1.7915 0.03420 from 1.79130 0.034180,
  46 1.7952 0.03672 from 1.79510 0.036700,  47 1.7962 0.04436 from 1.79600 0.044340,
  48 1.7999 0.04903 from 1.79970 0.049010,  49 1.8074 0.04584 from 1.80730 0.045820,
  50 1.8092 0.05515 from 1.80900 0.055140,  51 1.8066 0.07710 from 1.80640 0.077080,
  52 1.7964 0.11712 from 1.79630 0.117100,  53 1.7779 0.16599 from 1.77770 0.165980,
  54 1.7563 0.20682 from 1.75620 0.206810,  55 1.7335 0.23640 from 1.73340 0.236380,
  56 1.7124 0.25615 from 1.71230 0.256130,  57 1.6913 0.27025 from 1.69120 0.270230.
The square root and u over 2 X terms together are at most 1.5e-4 of (e^u - 1) X on
every row, against the budget 2e-4 used here. The smallest rational margin is 0.01037,
at row 57, matching the falsifier margin 0.01069 of the parent note.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.SPLIT_table_endpoint_budget_low

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-- Per row upper bound for the logarithm quotient of page 3 display 2.7 at the row
endpoint, by log index; data only, values in the file header. -/
noncomputable def logRatioBound : ℕ → ℝ
  | 0 => 1.7791 | 43 => 1.7786 | 44 => 1.7863 | 45 => 1.7915
  | 46 => 1.7952 | 47 => 1.7962 | 48 => 1.7999 | 49 => 1.8074
  | 50 => 1.8092 | 51 => 1.8066 | 52 => 1.7964 | 53 => 1.7779
  | 54 => 1.7563 | 55 => 1.7335 | 56 => 1.7124 | 57 => 1.6913
  | _ => 0

/-- Per row upper bound for the endpoint mass ratio nu over the weight mass of page 2
display 2.3 at the cut aQ + 1/10000, by log index; data only, values in the file header. -/
noncomputable def nuRatioBound : ℕ → ℝ
  | 0 => 0.03185 | 43 => 0.03319 | 44 => 0.03274 | 45 => 0.03420
  | 46 => 0.03672 | 47 => 0.04436 | 48 => 0.04903 | 49 => 0.04584
  | 50 => 0.05515 | 51 => 0.07710 | 52 => 0.11712 | 53 => 0.16599
  | 54 => 0.20682 | 55 => 0.23640 | 56 => 0.25615 | 57 => 0.27025
  | _ => 0

/-- LEAF: page 2 display 2.3 and page 9, the endpoint mass nu of the polynomial weight
(4 t (1 - t))^m at the cut aQ + 1/10000 of Table 2 on page 13, divided by the full weight
mass 2^(2m) (m!)^2 / (2m+1)! of WeightMass.weight_mass, for the sixteen rows with log
index at most 57. Both integrals are integrals of explicit polynomials with rational
endpoints, so this is a finite rational evaluation. Exact rational values in the header.
Class MEDIUM. -/
theorem endpoint_nu_ratio_le {r : PrintedRow} (hr : r ∈ tableTwo)
    (hlow : r.logIndex ≤ 57) :
    tailMass r.m ((r.aQ : ℝ) + 1 / 10000) / (∫ t in (0 : ℝ)..1, weight r.m t) ≤
      nuRatioBound r.logIndex := by
  sorry

/-- Lower bound for exp on [0, 1] from the degree 11 Taylor polynomial and Mathlib exp_bound.
AI wrote this Lean code, burst-20261124. -/
theorem exp_poly_lower (f : ℝ) (h0 : 0 ≤ f) (h1 : f ≤ 1) :
    (∑ i ∈ Finset.range 12, f ^ i / (i.factorial : ℝ)) - f ^ 12 * (13 / (12 * (Nat.factorial 12) : ℝ)) ≤
      Real.exp f := by
  have h := Real.exp_bound (x := f) (by rw [abs_of_nonneg h0]; exact h1) (n := 12) (by norm_num)
  rw [abs_of_nonneg h0] at h
  have := (abs_le.mp h).1
  have e : ((Nat.succ 12 : ℕ) : ℝ) / (((Nat.factorial 12) : ℕ) * (12 : ℕ)) = 13 / (12 * (Nat.factorial 12) : ℝ) := by
    push_cast; ring
  rw [e] at this
  linarith

/-- Upper bound for exp on [0, 1] from the degree 11 Taylor polynomial, Mathlib exp_bound'.
AI wrote this Lean code, burst-20261124. -/
theorem exp_poly_upper (f : ℝ) (h0 : 0 ≤ f) (h1 : f ≤ 1) :
    Real.exp f ≤
      (∑ i ∈ Finset.range 12, f ^ i / (i.factorial : ℝ)) + f ^ 12 * (13 / (12 * (Nat.factorial 12) : ℝ)) := by
  have h := Real.exp_bound' h0 h1 (n := 12) (by norm_num)
  have e : f ^ 12 * ((12 : ℕ) + 1) / (((Nat.factorial 12) : ℕ) * (12 : ℕ)) = f ^ 12 * (13 / (12 * (Nat.factorial 12) : ℝ)) := by
    push_cast; ring
  push_cast at h e ⊢
  linarith

/-- Page 3 display 2.7 at the row endpoint X = T / (e^u (1 + delta)): the numerator is log T,
and the denominator is at least log T - c once log (1/u) + u + delta is at most c.
AI wrote this Lean code, burst-20261124. -/
theorem log_ratio_generic {T u δ lo c : ℝ} (hT : 0 < T) (hu : 0 < u) (hδ : 0 ≤ δ)
    (hlo : lo ≤ Real.log T) (hL : Real.log (1 / u) + u + δ ≤ c) (hc : c < lo) (hc0 : 0 ≤ c) :
    Real.log (Real.exp u * (T / (Real.exp u * (1 + δ))) * (1 + δ)) /
        Real.log (T / (Real.exp u * (1 + δ)) * (Real.exp u - 1)) ≤ lo / (lo - c) := by
  have he : 0 < Real.exp u := Real.exp_pos u
  have hd : 0 < 1 + δ := by linarith
  have hnum : Real.exp u * (T / (Real.exp u * (1 + δ))) * (1 + δ) = T := by
    field_simp
  have hE : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  have hE0 : 0 < Real.exp u - 1 := by linarith
  have hden : Real.log T - c ≤ Real.log (T / (Real.exp u * (1 + δ)) * (Real.exp u - 1)) := by
    rw [Real.log_mul (by positivity) hE0.ne', Real.log_div hT.ne' (by positivity),
      Real.log_mul he.ne' hd.ne', Real.log_exp]
    have h1 : Real.log (1 + δ) ≤ δ := by linarith [Real.log_le_sub_one_of_pos hd]
    have h2 : Real.log u ≤ Real.log (Real.exp u - 1) := Real.log_le_log hu hE
    have h3 : Real.log (1 / u) = - Real.log u := by rw [one_div, Real.log_inv]
    linarith
  rw [hnum]
  have hlogT : 0 < Real.log T - c := by linarith
  calc Real.log T / Real.log (T / (Real.exp u * (1 + δ)) * (Real.exp u - 1))
      ≤ Real.log T / (Real.log T - c) :=
        div_le_div_of_nonneg_left (by linarith) hlogT hden
    _ ≤ lo / (lo - c) := by
        rw [div_le_div_iff₀ hlogT (by linarith)]
        nlinarith


/-- Integer part of the per row upper bound for log of 1/u, page 13 Table 2. Data only. -/
def logIntPart : ℕ → ℕ
  | 0 => 18
  | 43 => 18
  | 44 => 19
  | 45 => 19
  | 46 => 20
  | 47 => 20
  | 48 => 21
  | 49 => 21
  | 50 => 22
  | 51 => 22
  | 52 => 23
  | 53 => 23
  | 54 => 23
  | 55 => 23
  | 56 => 23
  | 57 => 23
  | _ => 0

/-- Fractional part, rounded up, of the per row upper bound for log of 1/u. Data only. -/
noncomputable def logFracUp : ℕ → ℝ
  | 0 => 189/250
  | 43 => 823/1000
  | 44 => 46/125
  | 45 => 881/1000
  | 46 => 47/125
  | 47 => 833/1000
  | 48 => 331/1000
  | 49 => 889/1000
  | 50 => 181/500
  | 51 => 769/1000
  | 52 => 53/1000
  | 53 => 47/250
  | 54 => 253/1000
  | 55 => 34/125
  | 56 => 37/125
  | 57 => 297/1000
  | _ => 0

/-- Lower bound for log of the row threshold: 42.832 for 4e18, else the log index. -/
noncomputable def logLower (k : ℕ) : ℝ := if k = 0 then 42.832 else k

/-- Page 13 Table 2, a comparison of rationals on the sixteen rows with log index at most 57:
the Taylor lower bound certifies log (1/u) below logIntPart plus logFracUp, and the resulting
quotient bound is below logRatioBound. Smallest margin 5.7e-6, at row 44.
AI wrote this Lean code, burst-20261124. -/
theorem log_ratio_rational_check {r : PrintedRow} (hr : r ∈ tableTwo)
    (hlow : r.logIndex ≤ 57) :
    0 ≤ logFracUp r.logIndex ∧ logFracUp r.logIndex ≤ 1 ∧
    1 / (r.uQ : ℝ) ≤ (2.7182818283 : ℝ) ^ (logIntPart r.logIndex) *
      ((∑ i ∈ Finset.range 12, logFracUp r.logIndex ^ i / (i.factorial : ℝ)) -
        logFracUp r.logIndex ^ 12 * (13 / (12 * (Nat.factorial 12) : ℝ))) ∧
    (logIntPart r.logIndex : ℝ) + logFracUp r.logIndex + (r.uQ : ℝ) + (r.deltaQ : ℝ) <
      logLower r.logIndex ∧
    0 ≤ (logIntPart r.logIndex : ℝ) + logFracUp r.logIndex + (r.uQ : ℝ) + (r.deltaQ : ℝ) ∧
    logLower r.logIndex / (logLower r.logIndex - ((logIntPart r.logIndex : ℝ) +
      logFracUp r.logIndex + (r.uQ : ℝ) + (r.deltaQ : ℝ))) ≤ logRatioBound r.logIndex := by
  simp only [tableTwo, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    subst h
    first
      | (exfalso; norm_num at hlow; done)
      | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          norm_num [PrintedRow.deltaQ, PrintedRow.uQ, logIntPart, logFracUp, logLower,
            logRatioBound, Finset.sum_range_succ, Nat.factorial])

/-- log of the row threshold is at least logLower; for 4e18 by the Taylor upper bound for exp.
AI wrote this Lean code, burst-20261124. -/
theorem logLower_le (r : PrintedRow) : logLower r.logIndex ≤ Real.log r.threshold := by
  unfold logLower PrintedRow.threshold
  split_ifs with h
  · rw [Real.le_log_iff_exp_le (by norm_num [evenBase])]
    have hs : (42.832 : ℝ) = (42 : ℕ) + 0.832 := by norm_num
    rw [hs, Real.exp_add, ← Real.exp_one_pow]
    have h1 : Real.exp 1 ^ 42 ≤ (2.7182818286 : ℝ) ^ 42 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le _
    have h2 := exp_poly_upper 0.832 (by norm_num) (by norm_num)
    have h3 : (2.7182818286 : ℝ) ^ 42 * ((∑ i ∈ Finset.range 12, (0.832 : ℝ) ^ i / (i.factorial : ℝ)) +
        (0.832 : ℝ) ^ 12 * (13 / (12 * (Nat.factorial 12) : ℝ))) ≤ ((evenBase : ℕ) : ℝ) := by
      norm_num [evenBase, Finset.sum_range_succ, Nat.factorial]
    calc Real.exp 1 ^ 42 * Real.exp 0.832 ≤ (2.7182818286 : ℝ) ^ 42 * ((∑ i ∈ Finset.range 12,
          (0.832 : ℝ) ^ i / (i.factorial : ℝ)) + (0.832 : ℝ) ^ 12 * (13 / (12 * (Nat.factorial 12) : ℝ))) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ ≤ _ := h3
  · rw [Real.log_exp]



/-- LEAF: page 3 display 2.7, the logarithm quotient log (e^u X (1 + delta)) over
log (X (e^u - 1)) in the enlarged Brun Titchmarsh coefficient, at the row endpoint
X = threshold / (e^u (1 + delta)) for the sixteen Table 2 rows on page 13 with log index
at most 57. Needs only interval bounds for exp and log at the printed parameters.
Double precision values in the header. Class MEDIUM. PROVED burst-20261124 from log_ratio_generic and the rational check. -/
theorem endpoint_log_ratio_le {r : PrintedRow} (hr : r ∈ tableTwo)
    (hlow : r.logIndex ≤ 57) :
    Real.log (Real.exp r.uQ * rowEndpointX r * (1 + (r.deltaQ : ℝ))) /
        Real.log (rowEndpointX r * (Real.exp r.uQ - 1)) ≤
      logRatioBound r.logIndex := by
  have hs := table_small_steps r hr
  have hδ : (0 : ℝ) ≤ r.deltaQ := by exact_mod_cast hs.1.le
  have hu : (0 : ℝ) < r.uQ := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    have h2 : (0 : ℝ) < ((1 / 10 ^ 12 : ℚ) : ℝ) := by norm_num
    linarith
  have hth : 0 < r.threshold := by
    unfold PrintedRow.threshold
    split_ifs
    · norm_num [evenBase]
    · exact Real.exp_pos _
  obtain ⟨hf0, hf1, hexp, hc, hc0, hq⟩ := log_ratio_rational_check hr hlow
  have hlog : Real.log (1 / (r.uQ : ℝ)) ≤ (logIntPart r.logIndex : ℝ) + logFracUp r.logIndex := by
    rw [Real.log_le_iff_le_exp (by positivity), Real.exp_add, ← Real.exp_one_pow]
    refine hexp.trans (mul_le_mul ?_ (exp_poly_lower _ hf0 hf1) ?_ (by positivity))
    · exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le _
    · have h := Real.add_one_le_exp (logFracUp r.logIndex)
      have h' := exp_poly_lower _ hf0 hf1
      nlinarith [Real.exp_pos (logFracUp r.logIndex), hexp, one_div_pos.mpr hu,
        pow_pos (show (0:ℝ) < 2.7182818283 by norm_num) (logIntPart r.logIndex)]
  have hL : Real.log (1 / (r.uQ : ℝ)) + r.uQ + r.deltaQ ≤
      (logIntPart r.logIndex : ℝ) + logFracUp r.logIndex + (r.uQ : ℝ) + (r.deltaQ : ℝ) := by
    linarith
  unfold rowEndpointX
  exact (log_ratio_generic hth hu hδ (logLower_le r) hL hc hc0).trans hq

/-- Page 9 display 2.64, the two small terms against the main factor: once u squared X is
at least 117 and X is at least 1000, the omega square root term and u over 2 X are together at
most 2e-4 of (e^u - 1) X. Uses only e^u - 1 at least u. AI wrote this Lean code, burst-20261124. -/
theorem small_terms_generic {u X : ℝ} (hu : 0 < u) (hX : 1000 ≤ X) (hK : 117 ≤ u ^ 2 * X) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X + u / (2 * X) ≤
      2 / 10000 * ((Real.exp u - 1) * X) := by
  have hX0 : 0 < X := by linarith
  set s := Real.sqrt X with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hX0
  have hss : s * s = X := Real.mul_self_sqrt hX0.le
  have hexp : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  have hus : 10.8 ≤ u * s := by
    have h1 : (u * s) ^ 2 = u ^ 2 * X := by rw [← hss]; ring
    nlinarith [mul_pos hu hs0]
  have h1 : (2.05022 * 10 ^ (-3 : ℤ)) * s ≤ 19 / 100000 * (u * X) := by
    rw [← hss]
    have : (2.05022 * 10 ^ (-3 : ℤ) : ℝ) = 0.00205022 := by norm_num
    rw [this]
    nlinarith
  have h2 : u / (2 * X) ≤ 1 / 100000 * (u * X) := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ X * X / 50000 := by
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    nlinarith [mul_pos hu hX0]
  have h3 : u * X ≤ (Real.exp u - 1) * X := mul_le_mul_of_nonneg_right hexp hX0.le
  nlinarith

/-- Lower bound for the row threshold of Table 2 on page 13: 4e18 for the first row, and
2.718 to the log index otherwise, below e to the log index. Data only. -/
noncomputable def thresholdLower (k : ℕ) : ℝ := if k = 0 then 4 * 10 ^ 18 else (2.718 : ℝ) ^ k

/-- The row threshold is at least thresholdLower. AI wrote this Lean code, burst-20261124. -/
theorem thresholdLower_le (r : PrintedRow) : thresholdLower r.logIndex ≤ r.threshold := by
  unfold thresholdLower PrintedRow.threshold
  split_ifs
  · norm_num [evenBase]
  · rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _

/-- The row endpoint X of Table 2 is at least thresholdLower over (1 + u + u^2)(1 + delta),
from e^u at most 1 + u + u^2 for u at most 1. AI wrote this Lean code, burst-20261124. -/
theorem rowEndpointX_lower (r : PrintedRow) (hu0 : 0 ≤ (r.uQ : ℝ)) (hu1 : (r.uQ : ℝ) ≤ 1)
    (hδ : 0 ≤ (r.deltaQ : ℝ)) :
    thresholdLower r.logIndex / ((1 + (r.uQ : ℝ) + (r.uQ : ℝ) ^ 2) * (1 + (r.deltaQ : ℝ))) ≤
      rowEndpointX r := by
  unfold rowEndpointX
  have hT := thresholdLower_le r
  have hT0 : 0 ≤ thresholdLower r.logIndex := by
    unfold thresholdLower; split_ifs <;> positivity
  have he := Real.abs_exp_sub_one_sub_id_le (x := (r.uQ : ℝ)) (by rw [abs_of_nonneg hu0]; exact hu1)
  have he' : Real.exp r.uQ ≤ 1 + (r.uQ : ℝ) + (r.uQ : ℝ) ^ 2 := by
    have := (abs_le.mp he).2; linarith
  apply div_le_div₀ (hT0.trans hT) hT (by positivity)
  exact mul_le_mul_of_nonneg_right he' (by linarith)

/-- Page 13 Table 2, a comparison of rationals: on the sixteen rows with log index at most 57
the lower bound for X is at least 1000 and u squared times it is at least 117.
AI wrote this Lean code, burst-20261124. -/
theorem small_terms_rational_check {r : PrintedRow} (hr : r ∈ tableTwo)
    (hlow : r.logIndex ≤ 57) :
    1000 ≤ thresholdLower r.logIndex /
        ((1 + (r.uQ : ℝ) + (r.uQ : ℝ) ^ 2) * (1 + (r.deltaQ : ℝ))) ∧
      117 ≤ (r.uQ : ℝ) ^ 2 * (thresholdLower r.logIndex /
        ((1 + (r.uQ : ℝ) + (r.uQ : ℝ) ^ 2) * (1 + (r.deltaQ : ℝ)))) := by
  simp only [tableTwo, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    subst h
    first
      | (exfalso; norm_num at hlow; done)
      | (constructor <;> norm_num [PrintedRow.deltaQ, PrintedRow.uQ, thresholdLower])

/-- LEAF: page 9 display 2.64, the omega term 2.05022e-3 sqrt X and the term u over 2 X at
the row endpoint are together at most 2e-4 of (e^u - 1) X, for the sixteen Table 2 rows
on page 13 with log index at most 57. Uses only u sqrt X at least 13.6 on these rows.
Class EASY. PROVED burst-20261124 from small_terms_generic and the rational check. -/
theorem endpoint_small_terms_le {r : PrintedRow} (hr : r ∈ tableTwo)
    (hlow : r.logIndex ≤ 57) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) + (r.uQ : ℝ) / (2 * rowEndpointX r) ≤
      2 / 10000 * ((Real.exp r.uQ - 1) * rowEndpointX r) := by
  have hs := table_small_steps r hr
  have hδ : (0 : ℝ) ≤ r.deltaQ := by exact_mod_cast hs.1.le
  have hu : (0 : ℝ) < r.uQ := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    have h2 : (0 : ℝ) < ((1 / 10 ^ 12 : ℚ) : ℝ) := by norm_num
    linarith
  have hu1 : (r.uQ : ℝ) ≤ 1 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.2
    have h2 : ((0.0001 : ℚ) : ℝ) ≤ 1 := by norm_num
    linarith
  have hX := rowEndpointX_lower r hu.le hu1 hδ
  obtain ⟨h1, h2⟩ := small_terms_rational_check hr hlow
  apply small_terms_generic hu (h1.trans hX)
  exact h2.trans (mul_le_mul_of_nonneg_left hX (by positivity))

/-- Page 9 display 2.64 with every piece replaced by its per row bound: a comparison of
rationals over the sixteen Table 2 rows on page 13 with log index at most 57.
AI wrote this Lean code, burst-20261124. -/
theorem endpoint_budget_rational_check {r : PrintedRow} (hr : r ∈ tableTwo)
    (hlow : r.logIndex ≤ 57) :
    2 * (1 + (r.deltaQ : ℝ)) * logRatioBound r.logIndex * nuRatioBound r.logIndex +
        2 / 10000 <
      1 + (r.deltaQ : ℝ) / 2 - (lowZeroBudget r.logIndex + highZeroBudget r.logIndex) := by
  simp only [tableTwo, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    subst h
    first
      | (exfalso; norm_num at hlow; done)
      | norm_num [PrintedRow.deltaQ, logRatioBound, nuRatioBound, lowZeroBudget,
          highZeroBudget]

/-- The bound quotient is nonnegative on every row. -/
theorem logRatioBound_nonneg (k : ℕ) : 0 ≤ logRatioBound k := by
  unfold logRatioBound
  split <;> norm_num

/-- Task92.endpoint_budget_numeric from the three leaves above and the rational check.
CONDITIONAL ON endpoint_nu_ratio_le, endpoint_log_ratio_le and endpoint_small_terms_le.
AI wrote this Lean code, burst-20261124. -/
theorem endpoint_budget_numeric_split {r : PrintedRow} (hr : r ∈ tableTwo)
    (hlow : r.logIndex ≤ 57) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  have hs := table_small_steps r hr
  have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hs.1
  have hu : (0 : ℝ) < r.uQ := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    have h2 : (0 : ℝ) < ((1 / 10 ^ 12 : ℚ) : ℝ) := by norm_num
    linarith
  have hth : 0 < r.threshold := by
    unfold PrintedRow.threshold
    split_ifs
    · norm_num [evenBase]
    · exact Real.exp_pos _
  have hX : 0 < rowEndpointX r := by
    unfold rowEndpointX
    have := Real.exp_pos (r.uQ : ℝ)
    positivity
  have hE : 0 < Real.exp (r.uQ : ℝ) - 1 := by
    have := Real.add_one_lt_exp hu.ne'
    linarith
  have hP : 0 < (Real.exp r.uQ - 1) * rowEndpointX r := mul_pos hE hX
  have hrpar := (tableTwo_rounding_arithmetic r hr).1
  have haQ : (0 : ℝ) ≤ r.aQ := by exact_mod_cast hrpar.2.2.2.1
  have hbQ : (r.aQ : ℝ) + 1 / 10000 ≤ 1 / 2 := by
    have hb := (Rat.cast_le (K := ℝ)).mpr hrpar.2.2.2.2.1
    push_cast at hb
    norm_num at hb ⊢
    exact hb
  have hnu0 := (tailMass_ratio_bounds r.m (by linarith : (0 : ℝ) ≤ (r.aQ : ℝ) + 1 / 10000)
    hbQ).1
  have hnu := endpoint_nu_ratio_le hr hlow
  have hlr := endpoint_log_ratio_le hr hlow
  have hsm := endpoint_small_terms_le hr hlow
  have hchk := endpoint_budget_rational_check hr hlow
  set P := (Real.exp (r.uQ : ℝ) - 1) * rowEndpointX r with hPdef
  set lr := Real.log (Real.exp r.uQ * rowEndpointX r * (1 + (r.deltaQ : ℝ))) /
      Real.log (rowEndpointX r * (Real.exp r.uQ - 1)) with hlrdef
  set q := tailMass r.m ((r.aQ : ℝ) + 1 / 10000) / (∫ t in (0 : ℝ)..1, weight r.m t)
    with hqdef
  have htail : tailCoefficient r.deltaQ r.uQ (rowEndpointX r) *
      tailMass r.m ((r.aQ : ℝ) + 1 / 10000) / (∫ t in (0 : ℝ)..1, weight r.m t) =
      2 * (1 + (r.deltaQ : ℝ)) * P * (lr * q) := by
    rw [hqdef, hPdef, hlrdef]
    unfold tailCoefficient
    ring
  have hprod : lr * q ≤ logRatioBound r.logIndex * nuRatioBound r.logIndex :=
    mul_le_mul hlr hnu hnu0 (logRatioBound_nonneg _)
  have hc : 0 ≤ 2 * (1 + (r.deltaQ : ℝ)) * P := by positivity
  have h1 := mul_le_mul_of_nonneg_left hprod hc
  have h2 := mul_lt_mul_of_pos_left hchk hP
  rw [htail]
  nlinarith
end LeanLab.KadiriLumley2014.Task92
