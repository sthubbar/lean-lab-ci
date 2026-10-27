/-
I-0065 block 12: every even n in [7426, 17424] has minGB n ≤ 173.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.RecBase

namespace LeanLab.Verifications.Top50.Fast

theorem recBlock_12 : allGBb 173 5000 7426 = true := by decide +kernel

end LeanLab.Verifications.Top50.Fast
