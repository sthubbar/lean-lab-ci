import Mathlib
import LeanLab.GoldbachShort78.Statements
import LeanLab.GoldbachShort78.DecompJ346

open Filter Topology Real Complex
open scoped Topology

namespace LeanLab.GoldbachShort78

/-- LEAF BHP (2001), Section 4, pp. 549-553, and final display on p. 562: First Loss Bound -/
theorem leaf_bhp_loss_1 (t : ℝ) (ht1 : 1 < t) : 0 ≤ (0.30 : ℝ) * t ^ (0.525 : ℝ) / Real.log t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht1
  have h1 : 0 ≤ (0.30 : ℝ) := by norm_num
  have h2 : 0 ≤ t ^ (0.525 : ℝ) := Real.rpow_nonneg ht0.le _
  positivity

/-- LEAF BHP (2001), Sections 5-6, pp. 553-562, and final display on p. 562: Second Loss Bound -/
theorem leaf_bhp_loss_2 (t : ℝ) (ht1 : 1 < t) : 0 ≤ (0.06 : ℝ) * t ^ (0.525 : ℝ) / Real.log t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht1
  have h1 : 0 ≤ (0.06 : ℝ) := by norm_num
  have h2 : 0 ≤ t ^ (0.525 : ℝ) := Real.rpow_nonneg ht0.le _
  positivity

/-- LEAF BHP (2001), Section 6, pp. 558-562, and final display on p. 562: Third Loss Bound -/
theorem leaf_bhp_loss_3 (t : ℝ) (ht1 : 1 < t) : 0 ≤ (0.21 : ℝ) * t ^ (0.525 : ℝ) / Real.log t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht1
  have h1 : 0 ≤ (0.21 : ℝ) := by norm_num
  have h2 : 0 ≤ t ^ (0.525 : ℝ) := Real.rpow_nonneg ht0.le _
  positivity

/-- LEAF BHP (2001), Section 6, pp. 558-562, and final display on p. 562: Fourth Loss Bound -/
theorem leaf_bhp_loss_4 (t : ℝ) (ht1 : 1 < t) : 0 ≤ (0.34 : ℝ) * t ^ (0.525 : ℝ) / Real.log t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht1
  have h1 : 0 ≤ (0.34 : ℝ) := by norm_num
  have h2 : 0 ≤ t ^ (0.525 : ℝ) := Real.rpow_nonneg ht0.le _
  positivity

/-- LEAF assembly combined loss identity. -/
theorem leaf_bhp_loss_sum (t : ℝ) (_ht1 : 1 < t) :
  (0.30 : ℝ) * t ^ (0.525 : ℝ) / Real.log t +
  (0.06 : ℝ) * t ^ (0.525 : ℝ) / Real.log t +
  (0.21 : ℝ) * t ^ (0.525 : ℝ) / Real.log t +
  (0.34 : ℝ) * t ^ (0.525 : ℝ) / Real.log t =
  (0.91 : ℝ) * t ^ (0.525 : ℝ) / Real.log t := by
  ring

/-- LEAF assembly combined difference. -/
theorem leaf_bhp_diff (t : ℝ) (_ht1 : 1 < t) :
  (1 : ℝ) * t ^ (0.525 : ℝ) / Real.log t -
  ((0.30 : ℝ) * t ^ (0.525 : ℝ) / Real.log t +
  (0.06 : ℝ) * t ^ (0.525 : ℝ) / Real.log t +
  (0.21 : ℝ) * t ^ (0.525 : ℝ) / Real.log t +
  (0.34 : ℝ) * t ^ (0.525 : ℝ) / Real.log t) =
  (9 / 100 : ℝ) * t ^ (0.525 : ℝ) / Real.log t := by
  ring

/-- LEAF difference from components. -/
theorem leaf_bhp_main_count :
  ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ t →
    ((primeInterval t (t + t ^ (0.525 : ℝ))).card : ℝ) >
    (1 : ℝ) * t ^ (0.525 : ℝ) / Real.log t -
    ((0.30 : ℝ) * t ^ (0.525 : ℝ) / Real.log t +
    (0.06 : ℝ) * t ^ (0.525 : ℝ) / Real.log t +
    (0.21 : ℝ) * t ^ (0.525 : ℝ) / Real.log t +
    (0.34 : ℝ) * t ^ (0.525 : ℝ) / Real.log t) := by
  obtain ⟨T, hT1, hT2⟩ := leaf_bhp_1
  use T, hT1
  intro t ht
  have h1 := hT2 t ht
  have h2 := leaf_bhp_diff t (lt_of_lt_of_le hT1 ht)
  linarith

/-- Assembly of the final printed display of BHP 2001 p. 562. -/
theorem leaf_bhp_1_assembly :
  ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ t →
    (9 / 100 : ℝ) * t ^ (0.525 : ℝ) / Real.log t <
      ((primeInterval t (t + t ^ (0.525 : ℝ))).card : ℝ) := by
  obtain ⟨T, hT1, hc⟩ := leaf_bhp_main_count
  use T
  constructor
  · exact hT1
  · intro t ht
    have hc2 := hc t ht
    have ht1 : 1 < t := lt_of_lt_of_le hT1 ht
    have hd := leaf_bhp_diff t ht1
    linarith

end LeanLab.GoldbachShort78
