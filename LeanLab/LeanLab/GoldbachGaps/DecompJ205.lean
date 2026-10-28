import Mathlib
import LeanLab.GoldbachGaps.Goldston1990Main

namespace LeanLab.GoldbachGaps.DecompJ205
open Real Chebyshev Finset Filter Topology
open LeanLab.GoldbachGaps.Goldston1990

/-- LEAF p. 291: fejer asymptotic from J = o(K^2 N) -/
theorem leaf_fejer_asymp (K : ℕ → ℕ) :
    Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0) →
    Tendsto (fun N : ℕ => fejer N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 1) := sorry

/-- LEAF p. 292: S(K+h) - S(K) lower bounds sum R -/
theorem leaf_sum_R_lower (N K h : ℕ) (hpos : 0 < h) :
    (fejer N (K + h) - fejer N K) / (h : ℝ) ≤ ∑ n ∈ Icc (N - K) (N + K), Rg n := sorry

/-- LEAF p. 292: S(K) - S(K-h) upper bounds sum R -/
theorem leaf_sum_R_upper (N K h : ℕ) (hpos : 0 < h) (hK : h ≤ K) :
    ∑ n ∈ Icc (N - K) (N + K), Rg n ≤ (fejer N K - fejer N (K - h)) / (h : ℝ) := sorry

/-- LEAF p. 292: Sum R is ~ 2KN -/
theorem leaf_sum_R_asymp (K : ℕ → ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc (N - K N) (N + K N), Rg n) / (2 * (K N : ℝ) * N)) atTop (nhds 1) := sorry

/-- LEAF p. 292: R to r relabeling gives Corollary 1 -/
theorem leaf_relabel (h_asymp : ∀ K : ℕ → ℕ, Tendsto (fun N : ℕ => (∑ n ∈ Icc (N - K N) (N + K N), Rg n) / (2 * (K N : ℝ) * N)) atTop (nhds 1)) : Corollary1 := sorry

theorem assembly_corollary1 : Corollary1 :=
  leaf_relabel leaf_sum_R_asymp

end LeanLab.GoldbachGaps.DecompJ205
