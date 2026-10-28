import Mathlib
import LeanLab.KadiriLumley2014.Decomp92

namespace LeanLab.KadiriLumley2014.Task251

open Real
open Set
open LeanLab.KadiriLumley2014.Task64
open LeanLab.KadiriLumley2014.Task92

-- We decompose table_zero_budget

/-- LEAF. Page 10 Lemma 2.5. Unproved estimate. -/
theorem lemma2_5 {r : PrintedRow} (hr : r ∈ tableTwo) {X : ℝ}
  (hX : Real.exp 38 ≤ X) :
  (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X + (r.uQ : ℝ) / (2 * X) <
  (Real.exp (r.uQ : ℝ) - 1) * X * (1 + (r.deltaQ : ℝ) / 2) := by sorry

/-- LEAF. Page 10 Lemma 2.6. Unproved estimate. -/
theorem lemma2_6 {r : PrintedRow} (hr : r ∈ tableTwo) {X : ℝ}
  (hX : Real.exp 38 ≤ X) :
  zeroError r.m r.deltaQ r.uQ X ≤ 0 := by sorry

/-- LEAF. Page 12 Theorem 3.2. Unproved estimate. -/
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
