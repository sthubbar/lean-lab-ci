/-
The bump `h(t) = t²(2-t)³ e^{t-1/2}` on `[0, 2]` behind Helfgott's `η₊`:
`0 ≤ h ≤ e^{1/2}`, with the maximum at `t = 1`.
From the definition `hfun` in Statements.lean alone; the paper text was not re-read.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.HelfgottArcs.Statements

namespace LeanLab.HelfgottArcs
open Real

theorem hfun_nonneg (t : ℝ) : 0 ≤ hfun t := by
  unfold hfun
  split_ifs with h
  · have : 0 ≤ 2 - t := by linarith [h.2]
    positivity
  · rfl

theorem hfun_one : hfun 1 = Real.exp (1 / 2) := by
  unfold hfun
  rw [if_pos ⟨by norm_num, by norm_num⟩]
  norm_num

/-- `h ≤ e^{1/2}`: with `u = t - 1`, `t²(2-t)³ = (1-u²)²(1-u) ≤ 1 - u ≤ e^{-u}`. -/
theorem hfun_le (t : ℝ) : hfun t ≤ Real.exp (1 / 2) := by
  unfold hfun
  split_ifs with h
  · obtain ⟨h0, h2⟩ := h
    set u := t - 1 with hu
    have ht : t = 1 + u := by ring
    have hu1 : -1 ≤ u := by linarith
    have hu2 : u ≤ 1 := by linarith
    have hpoly : t ^ 2 * (2 - t) ^ 3 = (1 - u ^ 2) ^ 2 * (1 - u) := by rw [ht]; ring
    have hsq : (1 - u ^ 2) ^ 2 ≤ 1 := by
      have a : 0 ≤ 1 - u ^ 2 := by nlinarith
      have b : 1 - u ^ 2 ≤ 1 := by nlinarith
      nlinarith
    have hlin : 1 - u ≤ Real.exp (-u) := by
      have := Real.add_one_le_exp (-u); linarith
    have hexp : Real.exp (t - 1 / 2) = Real.exp u * Real.exp (1 / 2) := by
      rw [← Real.exp_add]; congr 1; rw [hu]; ring
    have hpos : 0 ≤ 1 - u := by linarith
    have hE : Real.exp (-u) * Real.exp u = 1 := by
      rw [← Real.exp_add]; simp
    rw [hpoly, hexp]
    calc (1 - u ^ 2) ^ 2 * (1 - u) * (Real.exp u * Real.exp (1 / 2))
        ≤ 1 * (1 - u) * (Real.exp u * Real.exp (1 / 2)) := by
          gcongr
      _ ≤ 1 * Real.exp (-u) * (Real.exp u * Real.exp (1 / 2)) := by
          gcongr
      _ = Real.exp (1 / 2) := by rw [one_mul, ← mul_assoc, hE, one_mul]
  · exact (Real.exp_pos _).le

end LeanLab.HelfgottArcs
