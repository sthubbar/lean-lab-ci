/-
I-0065 block 1: every even n in [4, 4] has minGB n ≤ 2.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.RecBase

namespace LeanLab.Verifications.Top50.Fast

theorem recBlock_1 : allGBb 2 1 4 = true := by decide +kernel

end LeanLab.Verifications.Top50.Fast
