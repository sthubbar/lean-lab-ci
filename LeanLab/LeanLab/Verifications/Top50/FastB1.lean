/-
Kernel Goldbach check, block 1: every even n in [1402, 11400] is a sum of two primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.FastCheck

namespace LeanLab.Verifications.Top50.Fast

theorem fastBlock_1 : allGB 5000 1402 = true := by decide +kernel

end LeanLab.Verifications.Top50.Fast
