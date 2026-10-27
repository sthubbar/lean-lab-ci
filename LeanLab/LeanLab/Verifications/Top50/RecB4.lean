/-
I-0065 block 4: every even n in [30, 96] has minGB n ≤ 7.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.RecBase

namespace LeanLab.Verifications.Top50.Fast

theorem recBlock_4 : allGBb 7 34 30 = true := by decide +kernel

end LeanLab.Verifications.Top50.Fast
