/-
SEAL TEST, lean-merge 2026-11-02. Deliberate planted cheat to prove CI rejects it. Never merged anywhere.
-/
import Mathlib

namespace LeanLab.SealTestCheat

axiom sealtest_ax : (1 : ℕ) = 2

theorem sealtest_false : (1 : ℕ) = 2 := sealtest_ax

theorem sealtest_native : (2 : ℕ) ^ 10 = 1024 := by native_decide

end LeanLab.SealTestCheat
