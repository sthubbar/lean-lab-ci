/-
Proof of the LEAF leafB8_adjQK_pairing of Split1122bAdjQK8.lean, CONDITIONAL ON the LEAF
leafB8_adjQ_deriv of Split1122bAdjoint8.lean, the delay relation s q'(s) = - q(s + 1) of the
adjoint function of Nathanson Theorem 9.4, as quoted by Bordignon, Johnston and Starichkova,
arXiv 2207.09452v6, papers/P0009.pdf, page 6.
adjQK_pairing_of_deriv1122c proves K(q) = q(1) for every q with the delay relation, no LEAF.
With adjQB8_one_1122c of Prove1122cEin8.lean, leafB8_adjQ_K_1122c gives the old LEAF
leafB8_adjQ_K, statement verbatim, from leafB8_adjQ_deriv alone.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Prove1122cEin8

namespace LeanLab.Cai2002

open Real

/-- Nathanson Theorem 9.4, adjoint pairing, as quoted by BJS arXiv 2207.09452 page 6: for any
q with s q'(s) = - q(s + 1) on s > 0, K(q) = q(1). By parts on [2, 3] with
q(t + 1) = - t q'(t), then t = u + 1 and the delay relation again on [1, 2]. -/
theorem adjQK_pairing_of_deriv1122c (q : ℝ → ℝ) (hq : ∀ s : ℝ, 0 < s → HasDerivAt q (-q (s + 1) / s) s) : kConstB8 q = q 1 := by
  have hqc : ∀ s : ℝ, 0 < s → ContinuousAt q s := fun s hs => (hq s hs).continuousAt
  -- continuity on positive reals
  have hqcon : ContinuousOn q (Set.Ioi 0) := fun s hs => (hqc s hs).continuousWithinAt
  -- Step A: FTC on f t = (1 + log (t-1)) * q t over [2,3]
  have hA : ∫ t in (2:ℝ)..3, (1 / (t - 1) * q t + (1 + log (t - 1)) * (-q (t + 1) / t))
      = (1 + log (3 - 1)) * q 3 - (1 + log (2 - 1)) * q 2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => (1 + log (t - 1)) * q t)
    · intro t ht
      rw [Set.uIcc_of_le (by norm_num)] at ht
      have ht1 : 0 < t - 1 := by linarith [ht.1]
      have hl : HasDerivAt (fun t => 1 + log (t - 1)) (1 / (t - 1)) t := by
        have := ((hasDerivAt_id t).sub_const 1).log ht1.ne'
        simpa using this.const_add 1
      exact hl.mul (hq t (by linarith [ht.1]))
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by norm_num)]
      intro t ht
      have ht1 : 0 < t - 1 := by linarith [ht.1]
      have ht0 : 0 < t := by linarith [ht.1]
      apply ContinuousAt.continuousWithinAt
      have c1 : ContinuousAt (fun t : ℝ => t - 1) t := continuousAt_id.sub continuousAt_const
      have cq1 : ContinuousAt (fun t => q (t + 1)) t :=
        ContinuousAt.comp (f := fun x : ℝ => x + 1) (g := q) (hqc (t + 1) (by linarith)) (continuousAt_id.add continuousAt_const)
      exact ((continuousAt_const.div c1 ht1.ne').mul (hqc t ht0)).add
        ((continuousAt_const.add (c1.log ht1.ne')).mul (cq1.neg.div continuousAt_id ht0.ne'))
  -- Step B: ∫_1^2 -q(u+1)/u = q 2 - q 1
  have hB : ∫ u in (1:ℝ)..2, -q (u + 1) / u = q 2 - q 1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le (by norm_num)] at ht
      exact hq t (by linarith [ht.1])
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by norm_num)]
      intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      apply ContinuousAt.continuousWithinAt
      have cq1 : ContinuousAt (fun t => q (t + 1)) t :=
        ContinuousAt.comp (f := fun x : ℝ => x + 1) (g := q) (hqc (t + 1) (by linarith)) (continuousAt_id.add continuousAt_const)
      exact cq1.neg.div continuousAt_id ht0.ne'
  -- Step C: substitution
  have hC : ∫ t in (2:ℝ)..3, 1 / (t - 1) * q t = ∫ u in (1:ℝ)..2, q (u + 1) / u := by
    have := intervalIntegral.integral_comp_add_right (fun x : ℝ => 1 / (x - 1) * q x) (1:ℝ)
      (a := 1) (b := 2)
    have e : ∫ x in (1:ℝ)..2, 1 / (x + 1 - 1) * q (x + 1) = ∫ u in (1:ℝ)..2, q (u + 1) / u := by
      apply intervalIntegral.integral_congr
      intro u _
      simp only
      rw [add_sub_cancel_right]; ring
    rw [← e, this]; norm_num
  have hneg : ∫ u in (1:ℝ)..2, q (u + 1) / u = -(q 2 - q 1) := by
    rw [← hB, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u _
    simp only
    ring
  -- integrability of the two pieces on [2,3]
  have hI1 : IntervalIntegrable (fun t => 1 / (t - 1) * q t) MeasureTheory.volume 2 3 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    intro t ht
    have ht1 : 0 < t - 1 := by linarith [ht.1]
    apply ContinuousAt.continuousWithinAt
    have c1 : ContinuousAt (fun t : ℝ => t - 1) t := continuousAt_id.sub continuousAt_const
    exact (continuousAt_const.div c1 ht1.ne').mul (hqc t (by linarith))
  have hI2 : IntervalIntegrable (fun t => (1 + log (t - 1)) * (-q (t + 1) / t)) MeasureTheory.volume 2 3 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    intro t ht
    have ht1 : 0 < t - 1 := by linarith [ht.1]
    have ht0 : 0 < t := by linarith [ht.1]
    apply ContinuousAt.continuousWithinAt
    have c1 : ContinuousAt (fun t : ℝ => t - 1) t := continuousAt_id.sub continuousAt_const
    have cq1 : ContinuousAt (fun t => q (t + 1)) t :=
      ContinuousAt.comp (f := fun x : ℝ => x + 1) (g := q) (hqc (t + 1) (by linarith)) (continuousAt_id.add continuousAt_const)
    exact (continuousAt_const.add (c1.log ht1.ne')).mul (cq1.neg.div continuousAt_id ht0.ne')
  rw [intervalIntegral.integral_add hI1 hI2] at hA
  have hD : ∫ t in (2:ℝ)..3, (1 + log (t - 1)) * q (t + 1) / t
      = -∫ t in (2:ℝ)..3, (1 + log (t - 1)) * (-q (t + 1) / t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u _
    simp only
    ring
  unfold kConstB8
  rw [hD]
  rw [hC, hneg] at hA
  norm_num at hA
  linarith

/-- Twin of leafB8_adjQK_pairing of Split1122bAdjQK8.lean, statement verbatim,
CONDITIONAL ON the LEAF leafB8_adjQ_deriv. -/
theorem leafB8_adjQK_pairing_1122c : kConstB8 adjQB8 = adjQB8 1 :=
  adjQK_pairing_of_deriv1122c adjQB8 leafB8_adjQ_deriv

/-- Twin of leafB8_adjQ_K of Split1122bAdjoint8.lean, statement verbatim, CONDITIONAL ON the
LEAF leafB8_adjQ_deriv only. -/
theorem leafB8_adjQ_K_1122c : kConstB8 adjQB8 = exp (-eulerMascheroniConstant) := by
  rw [leafB8_adjQK_pairing_1122c, adjQB8_one_1122c]

/-- Twin of leafB8_adjoint of Split1122bBoundary8.lean, statement verbatim, CONDITIONAL ON the
LEAFs leafB8_adjQ_deriv and leafB8_adjQ_tendsto of Split1122bAdjoint8.lean. -/
theorem leafB8_adjoint_1122c :
    ∃ q : ℝ → ℝ, IsAdjB8 q ∧ kConstB8 q = exp (-eulerMascheroniConstant) :=
  ⟨adjQB8, ⟨fun s hs => leafB8_adjQ_deriv s hs, leafB8_adjQ_tendsto⟩, leafB8_adjQ_K_1122c⟩

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.adjQK_pairing_of_deriv1122c
#print axioms LeanLab.Cai2002.leafB8_adjQK_pairing_1122c
#print axioms LeanLab.Cai2002.leafB8_adjQ_K_1122c
#print axioms LeanLab.Cai2002.leafB8_adjoint_1122c
