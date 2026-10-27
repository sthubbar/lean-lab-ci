/-
I-0065 block 28: every even n in [93274, 98272] has minGB n ≤ 293.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.RecBase

namespace LeanLab.Verifications.Top50.Fast

theorem recBlock_28 : allGBb 293 2500 93274 = true := by decide +kernel

end LeanLab.Verifications.Top50.Fast
