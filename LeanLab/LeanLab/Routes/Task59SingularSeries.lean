/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
The positivity assertion for the defined singular series is elementary.
It gives no lower bound for an actual prime count.
Source: Matomaki and Merikoski, printed page 1, singular series display.
-/
import LeanLab.Routes.Task59TwinPositive

namespace LeanLab.Routes.Task59

open Finset LeanLab.Routes.U1451

/-- The defined singular series is positive exactly at even natural shifts. -/
theorem singSeries_pos_iff_even (h : ℕ) : 0 < singSeries h ↔ 2 ∣ h := by
  constructor
  · intro hp
    by_contra ho
    simp [singSeries, ho] at hp
  · intro he
    rw [singSeries, if_pos he]
    apply mul_pos (mul_pos (by norm_num) twinProd_pos)
    apply prod_pos
    intro p hp
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
    have hd : 0 < (p : ℝ) - 2 := by linarith
    positivity

example : 0 < singSeries 10 := (singSeries_pos_iff_even 10).mpr (by decide)

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.singSeries_pos_iff_even
