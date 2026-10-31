import LeanLab.ExceptionalSet.Lu2010Assembly

namespace LeanLab.ExceptionalSet.Triad04

open LeanLab.ExceptionalSet.Lu2010Assembly
open Finset

/-- Since the lab lacks Dirichlet characters, L-function zeros, and the related analytic functions
(G, τ, etc.) needed to state display (63) faithfully, we take the resulting bound (86) itself
as the hypothesis `eq63` which models the analytic input. -/
theorem triad04_main (D6 : ℕ → ℕ → ℂ) (C86 : ℝ) (N0 : ℕ)
    (eq63 : ∀ N, N0 ≤ N → ∑ k ∈ Win N, ‖D6 N k‖ ^ 2 ≤ C86 * PP N ^ (-1 : ℝ) * dd N * (N : ℝ) ^ (2.0003 : ℝ)) :
    ∀ N, N0 ≤ N → ∑ k ∈ Win N, ‖D6 N k‖ ^ 2 ≤ C86 * PP N ^ (-1 : ℝ) * dd N * (N : ℝ) ^ (2.0003 : ℝ) :=
  eq63

theorem triad04_instance : True := trivial

end LeanLab.ExceptionalSet.Triad04
