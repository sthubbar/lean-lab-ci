-- Repo encoding of P0070 from cloud runs, copied under namespace B by PC run 20261020T0603Z-352, unit U-1182, unchanged otherwise.
/-
P0070 Perelli-Pintz 1992, the singular series of page 355. Unit U-5075,
CLOUD 20261019T0213Z-cloud14, the PROGRESS.md next action "prove Sing is Multipliable".
PROVED: `sing_multipliable`, the product over p > 2 converges, so the `tprod` in `Sing` is the true
twin prime constant; `sing_eq`, `Sing k` is `2 twinC` times the odd local factor; `sing_pos`,
`𝔖(2k) > 0`; `sing_ge`, `𝔖(2k) ≥ 2 twinC`. Reuses ChenExplicit/Reductions.lean.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib
import LeanLab.PerelliPintz1992.B.Statements
import LeanLab.ChenExplicit.Reductions

namespace LeanLab.PerelliPintz1992.B

theorem sing_multipliable :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => 1 - 1 / ((p.1 : ℝ) - 1) ^ 2) :=
  ChenExplicit.twinC_multipliable

theorem sing_eq (k : ℕ) : Sing k = 2 * ChenExplicit.twinC *
    ∏ p ∈ k.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2)) := rfl

theorem sing_ge (k : ℕ) : 2 * ChenExplicit.twinC ≤ Sing k := by
  rw [sing_eq]
  have h1 := ChenExplicit.one_le_oddFactor k
  have h0 := ChenExplicit.twinC_pos
  nlinarith

theorem sing_pos (k : ℕ) : 0 < Sing k :=
  lt_of_lt_of_le (by have := ChenExplicit.twinC_pos; linarith) (sing_ge k)

end LeanLab.PerelliPintz1992.B

