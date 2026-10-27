/-
I-0065 block 9: every even n in [992, 2640] has minGB n ≤ 73.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.RecBase

namespace LeanLab.Verifications.Top50.Fast

theorem recBlock_9 : allGBb 73 825 992 = true := by decide +kernel

end LeanLab.Verifications.Top50.Fast
