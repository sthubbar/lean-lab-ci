/-
# The cited `Dudek2014.Section22.Schoenfeld` reduced by `Bound.lean`

Unit U-1290, PC run 20261020T2203Z-17931. AI-written Lean code, Claude, 2026-10-20. Checked only
by the Lean kernel.

`Dudek2014.Section22.Schoenfeld` cites Schoenfeld 1976 Theorem 14 and (5.5), Dudek 2014 page 6:
`0.98 √y < ψ(y) - θ(y) < 1.11 √y + 3 y^{1/3}` for `y ≥ 121`. `Bound.psi_sub_theta_lt_schoenfeld`
proves the upper half for `y ≥ 10^8` with no cited input. Here:
* `psiF_eq_psi`, `thetaF_eq_theta`: the Dudek file's `psiF`, `thetaF` are Mathlib's `ψ`, `θ`;
* `schoenfeld_upper_large`: the upper half in the Dudek file's notation for `y ≥ 10^8`;
* `schoenfeld_of_lower_small`: the cited `Schoenfeld` follows from its lower half
  `SchoenfeldLower` and the upper half on the finite range `[121, 10^8)`, `SchoenfeldUpperSmall`.
So the cited input shrinks to `SchoenfeldLower ∧ SchoenfeldUpperSmall`. No theorem is relabeled
here: every lab consumer of `Schoenfeld` already has a PrimePowerWindow version without it.
Goldbach is open.
-/
import LeanLab.Common.PsiTheta.Bound
import LeanLab.Dudek2014.Display

namespace LeanLab.Common.PsiTheta

open Real Chebyshev
open LeanLab.Dudek2014.Section22

lemma psiF_eq_psi (x : ℝ) : psiF x = ψ x := by
  rw [psi_eq_sum_Icc]; unfold psiF; rfl

lemma thetaF_eq_theta (x : ℝ) : thetaF x = θ x := by
  rw [theta_eq_sum_Icc]; unfold thetaF; rfl

/-- The lower half of the cited bound, `0.98 √y < ψ(y) - θ(y)` for `y ≥ 121`. Cited. -/
def SchoenfeldLower : Prop :=
  ∀ y : ℝ, 121 ≤ y → 0.98 * √y < psiF y - thetaF y

/-- The upper half of the cited bound on the finite range `121 ≤ y < 10^8`. Cited, or a
finite check. -/
def SchoenfeldUpperSmall : Prop :=
  ∀ y : ℝ, 121 ≤ y → y < 10 ^ 8 → psiF y - thetaF y < 1.11 * √y + 3 * y ^ (1 / 3 : ℝ)

/-- **The upper half for `y ≥ 10^8`, in Dudek's notation, unconditional.** -/
theorem schoenfeld_upper_large {y : ℝ} (hy : 10 ^ 8 ≤ y) :
    psiF y - thetaF y < 1.11 * √y + 3 * y ^ (1 / 3 : ℝ) := by
  rw [psiF_eq_psi, thetaF_eq_theta]; exact psi_sub_theta_lt_schoenfeld hy

/-- **`Schoenfeld` from its lower half and the upper half below `10^8`.** CONDITIONAL ON
`SchoenfeldLower` and `SchoenfeldUpperSmall`. -/
theorem schoenfeld_of_lower_small (hL : SchoenfeldLower) (hU : SchoenfeldUpperSmall) :
    Schoenfeld := by
  intro y hy
  refine ⟨hL y hy, ?_⟩
  rcases lt_or_ge y (10 ^ 8) with h | h
  · exact hU y hy h
  · exact schoenfeld_upper_large h

/-- The converse, so the two Props together are exactly as strong as `Schoenfeld`, no stronger. -/
theorem lower_small_of_schoenfeld (h : Schoenfeld) : SchoenfeldLower ∧ SchoenfeldUpperSmall :=
  ⟨fun y hy => (h y hy).1, fun y hy _ => (h y hy).2⟩

end LeanLab.Common.PsiTheta
