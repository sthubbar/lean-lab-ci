/-
I-0065 block 2: every even n in [6, 10] has minGB n ≤ 3.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.RecBase

namespace LeanLab.Verifications.Top50.Fast

theorem recBlock_2 : allGBb 3 3 6 = true := by decide +kernel

end LeanLab.Verifications.Top50.Fast
