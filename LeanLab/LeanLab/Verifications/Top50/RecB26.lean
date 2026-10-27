/-
I-0065 block 26: every even n in [83274, 88272] has minGB n ≤ 293.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.RecBase

namespace LeanLab.Verifications.Top50.Fast

theorem recBlock_26 : allGBb 293 2500 83274 = true := by decide +kernel

end LeanLab.Verifications.Top50.Fast
