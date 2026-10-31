/-
I-0065 block 6: every even n in [220, 306] has minGB n ≤ 23.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.RecBase

namespace LeanLab.Verifications.Top50.Fast

theorem recBlock_6 : allGBb 23 44 220 = true := by decide +kernel

end LeanLab.Verifications.Top50.Fast
