/-
P0069 Baker-Harman-Pintz 1997, page 2: "the singular series 𝔖(2n), which is always positive".
Unit U-5075, CLOUD 20261019T0213Z-cloud14.
PROVED: `C2_eq`, the lab's `Thm2.C2` is `ChenExplicit.twinC`; `C2_multipliable`, the product
converges, so the `tprod` is the true constant and not Lean's junk value; `sing_pos`, the corrected
𝔖(2n) of `Thm2.sing` is positive for every n, as the paper says, while the printed form is 0,
`Thm2.sing_printed_zero`, F-5014. Reuses ChenExplicit/Reductions.lean twinC_pos and
twinC_multipliable. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib
import LeanLab.BHP1997.Thm2Statement
import LeanLab.ChenExplicit.Reductions

namespace LeanLab.BHP1997.Thm2

theorem C2_eq : C2 = ChenExplicit.twinC := rfl

theorem C2_multipliable :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => 1 - 1 / ((p : ℝ) - 1) ^ 2) :=
  ChenExplicit.twinC_multipliable

theorem C2_pos : 0 < C2 := ChenExplicit.twinC_pos

theorem sing_pos (n : ℕ) : 0 < sing n := by
  unfold sing
  have h1 := ChenExplicit.one_le_oddFactor n
  have := C2_pos
  positivity

end LeanLab.BHP1997.Thm2
