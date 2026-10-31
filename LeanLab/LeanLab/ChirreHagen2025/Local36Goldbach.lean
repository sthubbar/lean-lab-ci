/-
P0075, unit U-6351, track T2. The lab's best short interval result under RH, `goldbach_995`
of Bilinear128.lean, took Chirre-Hagen's Theorem 2 as a hypothesis; Local36.lean derives
Theorem 2 from the local bound (3.6), so here the hypothesis is (3.6) under RH instead.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1125Z-cloud41.
Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.ChirreHagen2025.Bilinear128
import LeanLab.ChirreHagen2025.Local36

namespace LeanLab.ChirreHagen2025

/-- Under RH, through Chirre-Hagen's local bound (3.6), Schoenfeld's θ bound and the
4·10^18 even check, a Goldbach number lies in `(x, x + 9.95 log² x)` for every `x ≥ 2`. -/
theorem goldbach_995_of_local36 (h36 : RiemannHypothesis → Local36.Local36)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hS : RiemannHypothesis → SchoenfeldTheta) :
    RiemannHypothesis → ∀ x : ℝ, 2 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 9.95 * Real.log x ^ 2 :=
  goldbach_995 (Local36.theorem2_of_RH_local36 h36) hE hS

end LeanLab.ChirreHagen2025
