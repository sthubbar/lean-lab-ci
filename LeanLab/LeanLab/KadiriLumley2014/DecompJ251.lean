import Mathlib
import LeanLab.KadiriLumley2014.Decomp92

namespace LeanLab.KadiriLumley2014.Task251

open Real
open Set
open LeanLab.KadiriLumley2014.Task64
open LeanLab.KadiriLumley2014.Task92

-- We decompose table_zero_budget

/-- A rational lower bound for the exponential threshold, used to bound
`Real.sqrt (Real.exp 38)` from below. -/
private theorem exp38_ge_quarter : (2.89 * 10 ^ 16 : ℝ) ≤ Real.exp 38 := by
  have h : Real.exp 38 = Real.exp 1 ^ 38 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have h1 : (2.715 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.715) h1 38
  have h2 : (2.89 * 10 ^ 16 : ℝ) ≤ (2.715:ℝ)^38 := by norm_num
  linarith

/-- The square root of the exponential threshold dominates `1.7 · 10^8`. -/
private theorem sqrt_exp38_ge : (1.7 * 10 ^ 8 : ℝ) ≤ Real.sqrt (Real.exp 38) := by
  rw [Real.le_sqrt (by norm_num) (Real.exp_pos 38).le]
  have h : (1.7 * 10 ^ 8 : ℝ) ^ 2 = 2.89 * 10 ^ 16 := by norm_num
  rw [h]
  exact exp38_ge_quarter

/-- Every printed smoothing step `u = delta / m` is at least `73 · 10^{-12}`. -/
private theorem tableTwo_uQ_lower : ∀ r ∈ tableTwo, (73 / 10 ^ 12 : ℚ) ≤ r.uQ := by
  decide +kernel

/-- LEAF. Page 10 Lemma 2.5. Unproved estimate. -/
theorem lemma2_5 {r : PrintedRow} (hr : r ∈ tableTwo) {X : ℝ}
  (hX : Real.exp 38 ≤ X) :
  (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X + (r.uQ : ℝ) / (2 * X) <
  (Real.exp (r.uQ : ℝ) - 1) * X * (1 + (r.deltaQ : ℝ) / 2) := by
  have hs := table_small_steps r hr
  have hδ : (0 : ℝ) < (r.deltaQ : ℝ) := by exact_mod_cast hs.1
  have huQ : (73 / 10 ^ 12 : ℝ) ≤ (r.uQ : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr (tableTwo_uQ_lower r hr)
    norm_num at h ⊢
    exact h
  have huQ0 : (0 : ℝ) ≤ (r.uQ : ℝ) := by linarith
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 38) hX
  have hbase : (1 : ℝ) < X := by
    have h := exp38_ge_quarter
    linarith
  have hexp : (r.uQ : ℝ) ≤ Real.exp (r.uQ : ℝ) - 1 := by
    linarith [Real.add_one_le_exp (r.uQ : ℝ)]
  -- the square root term
  have hY : (1.7 * 10 ^ 8 : ℝ) ≤ Real.sqrt X :=
    sqrt_exp38_ge.trans (Real.sqrt_le_sqrt hX)
  have hYpos : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hXpos
  have hYX : Real.sqrt X * (1.7 * 10 ^ 8) ≤ X := by
    have hsq : Real.sqrt X ^ 2 = X := Real.sq_sqrt hXpos.le
    nlinarith [hY, hYpos, hsq]
  have h1 : (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X ≤
      ((2.05022 * 10 ^ (-3 : ℤ)) / (1.7 * 10 ^ 8)) * X := by
    have hc : (0 : ℝ) < 1.7 * 10 ^ 8 := by norm_num
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith [hYX]
  -- the linear error term
  have h2 : (r.uQ : ℝ) / (2 * X) ≤ (r.uQ : ℝ) / 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * X)]
    nlinarith [huQ0, hbase]
  have h3 : (r.uQ : ℝ) / 2 ≤ (r.uQ : ℝ) * X / 2 := by nlinarith [huQ0, hbase]
  -- the numerical margin
  have hc : ((2.05022 * 10 ^ (-3 : ℤ)) / (1.7 * 10 ^ 8) : ℝ) < (r.uQ : ℝ) / 2 := by
    have hnum : ((2.05022 * 10 ^ (-3 : ℤ)) / (1.7 * 10 ^ 8) : ℝ) < (73 / 10 ^ 12) / 2 := by
      norm_num
    linarith
  have h4 : ((2.05022 * 10 ^ (-3 : ℤ)) / (1.7 * 10 ^ 8)) * X + (r.uQ : ℝ) * X / 2 <
      (r.uQ : ℝ) * X := by
    have := mul_lt_mul_of_pos_right hc hXpos
    nlinarith [this]
  -- the right-hand side
  have hmid : (r.uQ : ℝ) * X ≤ (Real.exp (r.uQ : ℝ) - 1) * X :=
    mul_le_mul_of_nonneg_right hexp hXpos.le
  have hB : (1 : ℝ) ≤ 1 + (r.deltaQ : ℝ) / 2 := by linarith
  have hnonneg : (0 : ℝ) ≤ (Real.exp (r.uQ : ℝ) - 1) * X := by linarith
  have h5 : (Real.exp (r.uQ : ℝ) - 1) * X ≤
      (Real.exp (r.uQ : ℝ) - 1) * X * (1 + (r.deltaQ : ℝ) / 2) :=
    le_mul_of_one_le_right hnonneg hB
  linarith [h1, h2, h3, h4, hmid, h5]

-- NOT PROVABLE AS STATED: `zeroError` is the `tsum` of the nonnegative family
-- `zeroSummand`, so it can only be `≤ 0` if that family is not summable; the
-- paper's Lemma 2.6 bounds the zero sum by a positive quantity, not by zero.
-- The sibling unit KadiriLumley2014/DecompJ336 asserts summability
-- (`lemma2_2_summable`, itself a leaf), and under summability this is false.
/-- REFUTED given summability and one zero, `Audit1614.old_lemma2_6_false_of_summable`: a nonnegative sum
is not `≤ 0`; the paper bounds it by a positive quantity. Do not prove this.
LEAF. Page 10 Lemma 2.6. Unproved estimate. -/
theorem lemma2_6 {r : PrintedRow} (hr : r ∈ tableTwo) {X : ℝ}
  (hX : Real.exp 38 ≤ X) :
  zeroError r.m r.deltaQ r.uQ X ≤ 0 := by sorry

-- FALSE as stated: the quotient is strictly positive, not ≤ 0.  Take the first
-- table row `r = ⟨0, 5, 35800, 272519712, 92, 2129, 36082898⟩`, `a = 2129/10000`
-- and `X = Real.exp 38`: the hypotheses hold and `tailCoefficient * tailMass /
-- ∫ weight` is `> 0`.  (Checked in Lean against this very statement; the paper's
-- tail term is a positive correction that must fit inside the numeric budget.)
/-- REFUTED, `Audit1614.old_theorem3_2_false`, first row of Table 2. Do not prove this. A repair needs the
per row budget of Table 2, see the open `Decomp92.table_zero_budget`, which this split does not reach.
LEAF. Page 12 Theorem 3.2. Unproved estimate. -/
theorem theorem3_2 {r : PrintedRow} (hr : r ∈ tableTwo) {a X : ℝ}
  (ha : a ∈ Icc (r.aQ : ℝ) ((r.aQ : ℝ) + 1 / 10000))
  (hX : Real.exp 38 ≤ X) :
  tailCoefficient r.deltaQ r.uQ X * tailMass r.m a /
    (∫ t in (0 : ℝ)..1, weight r.m t) ≤ 0 := by sorry

/-- Assembly of table_zero_budget from the above leaves. -/
theorem table_zero_budget_assembly {r : PrintedRow} (hr : r ∈ tableTwo) {a X : ℝ}
    (ha : a ∈ Icc (r.aQ : ℝ) ((r.aQ : ℝ) + 1 / 10000))
    (hD : (r.gapDenom : ℝ) = 1 / intervalFraction r.deltaQ r.uQ a)
    (hX : Real.exp 38 ≤ X)
    (hx : r.threshold < Real.exp r.uQ * (X * (1 + (r.deltaQ : ℝ) * (1 - a)))) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X +
      tailCoefficient r.deltaQ r.uQ X * tailMass r.m a /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * X) <
      (Real.exp r.uQ - 1) * X *
        (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ X) := by
  have h1 := lemma2_5 hr hX
  have h2 := lemma2_6 hr hX
  have h3 := theorem3_2 hr ha hX
  have h4 : (Real.exp (r.uQ : ℝ) - 1) * X * zeroError r.m (r.deltaQ : ℝ) (r.uQ : ℝ) X ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · have hs := table_small_steps r hr
      have hu : 0 ≤ (r.uQ : ℝ) := by
        have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
        norm_num at h ⊢
        linarith
      have : 0 ≤ Real.exp (r.uQ : ℝ) - 1 := by
        rw [sub_nonneg]
        exact Real.one_le_exp hu
      have hX_pos : 0 ≤ X := by linarith [Real.exp_pos 38]
      exact mul_nonneg this hX_pos
    · exact h2
  calc
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X + tailCoefficient (r.deltaQ : ℝ) (r.uQ : ℝ) X * tailMass r.m a / (∫ (t : ℝ) in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * X)
      = ((2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X + (r.uQ : ℝ) / (2 * X)) + tailCoefficient (r.deltaQ : ℝ) (r.uQ : ℝ) X * tailMass r.m a / (∫ (t : ℝ) in (0 : ℝ)..1, weight r.m t) := by ring
    _ ≤ ((2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X + (r.uQ : ℝ) / (2 * X)) + 0 := add_le_add le_rfl h3
    _ = (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X + (r.uQ : ℝ) / (2 * X) := add_zero _
    _ < (Real.exp (r.uQ : ℝ) - 1) * X * (1 + (r.deltaQ : ℝ) / 2) := h1
    _ = (Real.exp (r.uQ : ℝ) - 1) * X * (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m (r.deltaQ : ℝ) (r.uQ : ℝ) X) + (Real.exp (r.uQ : ℝ) - 1) * X * zeroError r.m (r.deltaQ : ℝ) (r.uQ : ℝ) X := by ring
    _ ≤ (Real.exp (r.uQ : ℝ) - 1) * X * (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m (r.deltaQ : ℝ) (r.uQ : ℝ) X) + 0 := add_le_add le_rfl h4
    _ = (Real.exp (r.uQ : ℝ) - 1) * X * (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m (r.deltaQ : ℝ) (r.uQ : ℝ) X) := add_zero _

end LeanLab.KadiriLumley2014.Task251
