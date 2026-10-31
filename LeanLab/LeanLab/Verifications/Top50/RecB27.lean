/-
I-0065 block 27: every even n in [88274, 93272] has minGB n ≤ 293.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.RecBase

namespace LeanLab.Verifications.Top50.Fast

theorem recBlock_27 : allGBb 293 2500 88274 = true := by decide +kernel

end LeanLab.Verifications.Top50.Fast
