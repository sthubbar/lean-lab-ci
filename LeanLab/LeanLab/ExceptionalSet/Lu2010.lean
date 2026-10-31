/-
P0095 W. C. Lu, Exceptional set of Goldbach number, J. Number Theory 130 (2010), no. 10,
2359-2392, DOI 10.1016/j.jnt.2010.03.017. Unit U-6808, CLOUD 20261021T0117Z-cloud55, track T1.

No copy of the paper was reached: ScienceDirect returns 403 to the cloud and there is no arXiv
version. Every statement here is fixed by secondary sources only:
* Pintz 2018, P0016, papers/P0016.pdf page 2, eq (1.8), read on the rendered page:
  "Finally in 2010 Lu [14] succeeded to show E(X) < X^0.879 for X > X_2 ineffective constant."
* Zhao 2025, P0040, arXiv 2511.05631v2, introduction: "δ = 0.121 by W. C. Lu [8]".

The lab's cited `ExceptionalSet.lu : PowerBound 0.879` is the `≪` form. Pintz reports Lu in the
stronger eventual form `E X < X^0.879` for all large `X`, with no constant. This file states that
form, `lu_eventually_stmt`, and proves its links to the rest of the chain with zero sorry.
Nothing here proves Lu's theorem; the analytic content, zero density estimates and the
Deuring-Heilbronn treatment of an exceptional zero per Pintz pp. 5 and 6, stays cited.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach itself is OPEN.
-/
import Mathlib
import LeanLab.ExceptionalSet.Statements

namespace LeanLab.ExceptionalSet.Lu2010
open LeanLab.ExceptionalSet

/-- P0095 Lu 2010 as Pintz 2018 eq (1.8) reports it: `E X < X^{0.879}` for all large `X`. -/
def lu_eventually_stmt : Prop := EventuallyBelow 0.879

/-- Lu's exponent is `1 - δ` with Zhao's `δ = 0.121`, and it beats Li's `0.914` by `0.035`. -/
theorem lu_exponent_arith :
    (1 : ℝ) - 0.121 = 0.879 ∧ (0.879 : ℝ) < 0.914 ∧ (0.914 : ℝ) - 0.879 = 0.035 ∧
      (1 : ℝ) - 0.914 = 0.086 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The eventual bound is monotone in the exponent. Not in `Statements.lean`, which has only
the `PowerBound` monotonicity. -/
theorem eventuallyBelow_mono {θ θ' : ℝ} (hθ : θ ≤ θ') (h : EventuallyBelow θ) :
    EventuallyBelow θ' := by
  obtain ⟨X0, hX0⟩ := h
  refine ⟨max X0 1, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast le_of_max_le_right hX
  calc (E X : ℝ) < (X : ℝ) ^ θ := hX0 X (le_of_max_le_left hX)
    _ ≤ (X : ℝ) ^ θ' := Real.rpow_le_rpow_of_exponent_le hX1 hθ

/-- Lu's eventual form gives the lab's cited `≪` form. -/
theorem lu_of_lu_eventually (h : lu_eventually_stmt) : PowerBound 0.879 :=
  powerBound_of_eventuallyBelow (by norm_num) h

/-- Lu's eventual form gives `δ = 0.121` in the Montgomery-Vaughan shape. -/
theorem powerSaving_of_lu_eventually (h : lu_eventually_stmt) : PowerSaving :=
  montgomeryVaughan_of_lu (lu_of_lu_eventually h)

/-- Lu's eventual form gives Li's bound (1.7) of Pintz 2018 in its own eventual form. -/
theorem li_eventually_of_lu_eventually (h : lu_eventually_stmt) : EventuallyBelow 0.914 :=
  eventuallyBelow_mono (by norm_num) h

/-- Pintz 2018 Theorem 1 implies Lu's eventual form. -/
theorem lu_eventually_of_pintz (h : EventuallyBelow 0.72) : lu_eventually_stmt :=
  eventuallyBelow_mono (by norm_num) h

/-- Zhao 2025 Theorem 1.1 implies Lu's eventual form. -/
theorem lu_eventually_of_zhao (h : PowerBound (7 / 10)) : lu_eventually_stmt :=
  eventuallyBelow_of_powerBound (by norm_num) h

/-- Vacuity test: the statement is not contradictory, since binary Goldbach implies it. -/
theorem lu_eventually_of_binaryGoldbach (h : BinaryGoldbach) : lu_eventually_stmt :=
  lu_eventually_of_zhao (zhao_of_binaryGoldbach h)

/-- Vacuity test, other side: the statement is not the trivial bound. It already forces
`E X < X` for every large `X`, which `E_le` alone does not give. -/
theorem lu_eventually_forces_lt (h : lu_eventually_stmt) :
    ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X → (E X : ℝ) < X := by
  obtain ⟨X0, hX0⟩ := eventuallyBelow_mono (θ' := 1) (by norm_num) h
  exact ⟨X0, fun X hX => by simpa using hX0 X hX⟩

end LeanLab.ExceptionalSet.Lu2010
