/-
P0028, arXiv 1610.02017, Lemma 4.3 proof, page 10.
Elementary density bookkeeping for a shifted progression.
The printed equality is recorded as a question. The lower bound survives for ε ≤ 1/6.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSTransference

namespace LeanLab.Ternary.MMS

/-- The exact density loss identity, with L the progression length and D the lost length. -/
theorem lemma43_loss_identity (ε L D : ℝ) :
    (1 / 3 + ε) * (L - D) =
      L * (1 / 3 + ε) - D / 2 + (1 / 6 - ε) * D := by
  ring

/-- The printed equality on page 10 fails at ε = 1/12, L = 24 and D = 1. -/
theorem lemma43_printed_equality_false :
    (1 / 3 + (1 / 12 : ℝ)) * (24 - 1) ≠
      24 * (1 / 3 + (1 / 12 : ℝ) - 1 / (2 * 24)) := by
  norm_num

/-- For small ε the inequality needed by Lemma 4.3 follows from the exact identity. -/
theorem lemma43_density_loss {ε L D : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 6)
    (hD : 0 ≤ D) (hDL : D ≤ ε * L) :
    (1 / 3 + ε / 2) * L ≤ (1 / 3 + ε) * (L - D) := by
  have hrem : 0 ≤ (1 / 6 - ε) * D := mul_nonneg (sub_nonneg.mpr hε1) hD
  rw [lemma43_loss_identity]
  nlinarith

end LeanLab.Ternary.MMS
