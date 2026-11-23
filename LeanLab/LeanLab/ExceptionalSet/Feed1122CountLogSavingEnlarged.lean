/-
`count_log_saving_enlarged` of `LeanLab.ExceptionalSet.SPLIT_major_arc_count_power` reduced to the
one LEAF `goldbach_count_window_power` of `Feed1122MajorArcCountPower`, burst-20261122, session
S91. A power saving `C x^θ`, `θ < 1`, is below `C x / (log x)^A` once `(log x)^A ≤ x^{1-θ}`,
which holds for all large `x`. No new sorry here.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.Feed1122MajorArcCountPower

namespace LeanLab.ExceptionalSet.BG2026
open Real Finset ArithmeticFunction
open ZMod
open LeanLab.ExceptionalSet.MV

noncomputable section

/-- `count_log_saving_enlarged` from `major_arc_count_power_of_leaves`: the power saving implies
the log saving for every `A > 0`, since `(log x)^A = o(x^{1-θ})`. Statement identical to the
parent. -/
theorem count_log_saving_enlarged_of_leaves :
    ∀ A : ℝ, 0 < A → ∃ (C : ℝ) (X0 : ℕ), 0 ≤ C ∧ 1 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
        ((((Finset.Icc (x / 2 + 1) x).filter (fun n : ℕ => Even n ∧
              ‖majorPart (logPrimes x) (minorArcs x ((x : ℝ) ^ ((1 : ℝ) / 10)))
                (n : ZMod (Mx x))‖ ≤ (Mx x : ℝ) * x / 4)).card : ℕ) : ℝ)
          ≤ C * (x : ℝ) / Real.log x ^ A := by
  intro A _hA
  obtain ⟨θ, C, X1, _hθ0, hθ1, hC, hX1, h⟩ := major_arc_count_power_of_leaves
  have hs : 0 < 1 - θ := by linarith
  have hlit := isLittleO_log_rpow_rpow_atTop A hs
  have hev : ∀ᶠ t : ℝ in Filter.atTop, Real.log t ^ A ≤ t ^ (1 - θ) := by
    filter_upwards [hlit.eventuallyLE, Filter.eventually_gt_atTop (1 : ℝ)] with t ht ht1
    have hl : 0 < Real.log t := Real.log_pos ht1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hl.le _),
      abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)] at ht
    exact ht
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hev
  refine ⟨C, max (max X1 (Nat.ceil a)) 2, hC, le_trans hX1
    (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro x hx
  have hx1 : X1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxa : Nat.ceil a ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hx2r : (2 : ℝ) ≤ x := by exact_mod_cast hx2
  have hxpos : (0 : ℝ) < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hLA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlog _
  have hbound : Real.log x ^ A ≤ (x : ℝ) ^ (1 - θ) := by
    apply ha
    have h1 : a ≤ (Nat.ceil a : ℝ) := Nat.le_ceil a
    have h2 : ((Nat.ceil a : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxa
    linarith
  have hsplit : (x : ℝ) ^ θ * (x : ℝ) ^ (1 - θ) = x := by
    rw [← Real.rpow_add hxpos, add_sub_cancel, Real.rpow_one]
  have hθpos : 0 ≤ (x : ℝ) ^ θ := Real.rpow_nonneg hxpos.le _
  refine le_trans (h x hx1) ?_
  rw [le_div_iff₀ hLA]
  calc C * (x : ℝ) ^ θ * Real.log x ^ A ≤ C * (x : ℝ) ^ θ * (x : ℝ) ^ (1 - θ) := by
        gcongr
    _ = C * x := by rw [mul_assoc, hsplit]

end

#print axioms count_log_saving_enlarged_of_leaves

end LeanLab.ExceptionalSet.BG2026
