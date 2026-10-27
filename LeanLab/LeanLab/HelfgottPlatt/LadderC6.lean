/-
Primality of ladder part 6 by norm_num, U-0341. AI-written Lean code, Claude, 2026-10-17.
-/
import Mathlib
import LeanLab.HelfgottPlatt.LadderData

namespace LeanLab.HelfgottPlatt

theorem t6_prime : ∀ p ∈ t6, p.Prime := by
  intro p hp
  simp only [t6, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

end LeanLab.HelfgottPlatt
