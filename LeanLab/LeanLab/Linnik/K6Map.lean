/-
T2 map, unit U-5052, CLOUD 20261019T0114Z-cloud13: the Pintz-Ruzsa 2020 scheme, K = 2k powers of 2 when
A(k) + C₂₀ c₁^{2k-2} < 1. With their constants it gives K = 8 and cannot give K = 6.
PROVED: `k6_fails`, `A(3) + 4.0826 · 0.789401⁴ > 1` for `A(3) ≥ 0`; `k6_needs`, with `c₁ = 0.789401` and
`A(3) ≤ 0.0127`, `C₂₀ < 2.54` suffices for K = 6. numerics/K6_frontier.py: with C₂₀ = 4.0826 the threshold
c₁ < 0.70126 corresponds to minor arcs S ≪ N^θ with θ ≤ 0.7403, below N^{3/4}; or C₂₀ < 2.5425, i.e.
Chen's constant C* below about 2.71, against the best known 3.3996 of Wu 2004 and the parity limit 2.
Johnston-Trudgian 2026 already reach K = 7 unconditionally and K = 6 under GRH by another route, P0025.
Binary Goldbach is OPEN; K = 0 is binary Goldbach. AI-written Lean code, Claude, 2026-10-19.
-/
import Mathlib

namespace LeanLab.Linnik.K6Map

theorem k6_fails {A : ℝ} (hA : 0 ≤ A) : 1 < A + 4.0826 * (0.789401 : ℝ) ^ 4 := by
  norm_num; linarith

theorem k6_needs {A C : ℝ} (hA : A ≤ 0.0127) (hC0 : 0 ≤ C) (hC : C < 2.54) :
    A + C * (0.789401 : ℝ) ^ 4 < 1 := by
  have : C * (0.789401 : ℝ) ^ 4 < 2.54 * (0.789401 : ℝ) ^ 4 :=
    mul_lt_mul_of_pos_right hC (by norm_num)
  norm_num at this ⊢; linarith

end LeanLab.Linnik.K6Map
