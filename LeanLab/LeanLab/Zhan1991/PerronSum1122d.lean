/-
P0068 Zhan 1991, page 263 display (3.3): the summation of the single term Perron errors over
the tuples of display (3.4), split into three LEAFs: the coefficient bound
`|a₁(n₁)⋯a₂₀(n₂₀)| ≤ log (2^20 N) ≪ N^ε`, the divisor bound `d₂₀(m) ≪ N^ε` for the number of
tuples with a given product `m`, and the harmonic sum over the products `m ≤ 2^20 N`.
Source: papers/P0068.pdf. AI-written Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.SPLIT_theorem2_1122

namespace LeanLab.Zhan1991
open Finset Real

noncomputable section

/-- LEAF: page 263 display (3.3), the coefficient bound for the tuples of display (3.4): under
condition (3.5) each `n₁ ≤ 2N₁ ≤ 2^20 N`, so `|a₁(n₁)χ(n₁)⋯a₂₀(n₂₀)χ(n₂₀)| ≤ log n₁ ≤
log (2^20 N) ≪ N^ε`, since `|a_j| ≤ 1` for `j ≥ 2` and `|χ| ≤ 1`. Class EASY. -/
theorem perron_coef_leaf_ps2 : ∀ ε : ℝ, 0 < ε → ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (Nv : Fin 20 → ℝ) (n : Fin 20 → ℕ), N₀ ≤ N → Cond35 N Nv →
    n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)) →
    ‖∏ j : Fin 20, aj (j.val + 1) (n j) * χ (n j)‖ ≤ K * (N : ℝ) ^ ε := by
  sorry

/-- LEAF: page 263 display (3.3), the divisor bound: the number of tuples of display (3.4)
with product `n₁⋯n₂₀ = m` is at most `d₂₀(m) ≪ m^ε ≪ N^ε` for `m ≤ 2^20 N`, Hardy and Wright,
Theorem 315, iterated. Class MEDIUM. -/
theorem perron_fiber_leaf_ps2 : ∀ ε : ℝ, 0 < ε → ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ)
    (Nv : Fin 20 → ℝ) (m : ℕ), N₀ ≤ N → m ≤ 2 ^ 20 * N →
    ((Fintype.piFinset (fun j : Fin 20 => dyad (Nv j))).filter
      (fun n => ∏ j, n j = m)).card ≤ K * (N : ℝ) ^ ε := by
  sorry

/-- LEAF: page 263 display (3.3), the harmonic sum: with `c = 1 + 1/log N`, `2 ≤ T ≤ N`,
`0 < v ≤ N`, the single term errors `1/2 + c/T` at `m = v` and `2 (v/m)^c min(1, 1/(T|log(v/m)|))`
otherwise, summed over `1 ≤ m ≤ 2^20 N`, are `≪ N^{1+ε}/T`: `(v/m)^c ≤ e v/m`,
`|log(v/m)| ≫ |v - m|/N` near `v`, `≥ log 2` away from it, and the `O(1)` terms with
`|m - v| < 1` are `≤ N/T`. Class MEDIUM. -/
theorem perron_harmonic_leaf_ps2 : ∀ ε : ℝ, 0 < ε → ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (T v : ℝ),
    N₀ ≤ N → 2 ≤ T → T ≤ N → 0 < v → v ≤ N →
    ∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ 20 * N),
      (if v / (m : ℝ) = 1 then 1 / 2 + (1 + 1 / Real.log N) / T
        else 2 * (v / (m : ℝ)) ^ (1 + 1 / Real.log N) *
          min 1 (1 / (T * |Real.log (v / (m : ℝ))|)))
      ≤ K * (N : ℝ) ^ (1 + ε) / T := by
  sorry

end

end LeanLab.Zhan1991
