/-
I-0065 block 17: every even n in [43532, 48530] has minGB n ≤ 211.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.RecBase

namespace LeanLab.Verifications.Top50.Fast

theorem recBlock_17 : allGBb 211 2500 43532 = true := by decide +kernel

end LeanLab.Verifications.Top50.Fast
