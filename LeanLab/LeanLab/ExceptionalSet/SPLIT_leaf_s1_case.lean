/-
Split of the sealed statement `leaf_s1_case` of `LeanLab.ExceptionalSet.KaracubaSplit`, the
case `S = {1}` of the lab class in the source's Theorem 1, stated there as `LeafS1Case`.

The step is cut into three leaves:
* `leaf_s1_deriv_sign`: the two sided bound `N ^ (-θ) ≤ |f'| ≤ N ^ (-Θ)` makes `f'`
  continuous and nowhere zero on `[N, 2N]`, so it keeps one sign there and the phase is
  monotone.
* `leaf_s1_monotone_saving`: for `N ≥ N₀` the sum over `(N, 2N]` saves a fixed power
  `N ^ (c / k ^ 2)`: `k - 1` Weyl differences convert `|f^(k) / k!| ≤ N ^ (-Θ₀ k)` into
  cancellation, and the part of the sum where the linear term dominates is handled by the
  first derivative test against `|f'| ≥ N ^ (-θ)`, which is the weaker bound since `θ > Θ₀`.
  This carries the analytic content of the step.
* `leaf_s1_small_N_boundary`: below `N₀` the trivial bound `‖Σ‖ ≤ N` and
  `N ^ (c / k ^ 2) ≤ N₀ ^ (1 / 9)` for `c ≤ 1`, `k ≥ 3` and `N < N₀` give the same shape,
  with only the constant `B` depending on `N₀`.

AI wrote the Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.KaracubaSplit

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-- LEAF. Step 2 of the split, the analytic saving for large `N`: for `f` of class `C^k` on a
neighbourhood of `[N, 2N]`, `k ≥ 3`, `δ k ≤ 1`, the bound `|f^(k) / k!| ≤ N ^ (-Θ₀ k)`, the
two sided bound on `f'`, and one sign for `f'` on the interval, the sum over `(N, 2N]` is
`O(N ^ (1 - c / k ^ 2))` with `B, c` depending on `θ, Θ, Θ₀, δ` only, not on `N`, `f` or
`k`. -/
theorem leaf_s1_monotone_saving :
    ∀ θ Θ Θ₀ δ : ℝ, 0 < δ → δ < 1 → 0 < Θ → Θ < θ → θ < Θ₀ → Θ₀ < 1 →
      ∃ B c N₀ : ℝ, 0 < B ∧ 0 < c ∧ 0 < N₀ ∧
        ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ (f : ℝ → ℝ) (k : ℕ),
        3 ≤ k → (∃ U : Set ℝ, IsOpen U ∧ Set.Icc (N : ℝ) (2 * N) ⊆ U ∧ ContDiffOn ℝ k f U) →
        (∀ x ∈ Set.Icc (N : ℝ) (2 * N),
          |iteratedDeriv k f x / k.factorial| ≤ (N : ℝ) ^ (-(Θ₀ * k))) →
        δ * k ≤ 1 →
        (∀ x ∈ Set.Icc (N : ℝ) (2 * N),
          (N : ℝ) ^ (-(θ * (1 : ℕ))) ≤ |iteratedDeriv 1 f x / (1 : ℕ).factorial| ∧
          |iteratedDeriv 1 f x / (1 : ℕ).factorial| ≤ (N : ℝ) ^ (-(Θ * (1 : ℕ)))) →
        ((∀ x ∈ Set.Icc (N : ℝ) (2 * N), 0 < iteratedDeriv 1 f x) ∨
          (∀ x ∈ Set.Icc (N : ℝ) (2 * N), iteratedDeriv 1 f x < 0)) →
        ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  sorry

/-- LEAF. Step 3 of the split, the range below `N₀`: for `0 < c ≤ 1` the trivial bound
`‖Σ_{n ∈ (N, 2N]} e(f n)‖ ≤ N` and `N ^ (c / k ^ 2) ≤ N₀ ^ (1 / 9)`, valid for `1 ≤ N < N₀`
and `3 ≤ k`, give the same inequality with a constant `B` that absorbs `N₀`. No cancellation
is used here. -/
theorem leaf_s1_small_N_boundary :
    ∀ θ Θ Θ₀ δ : ℝ, 0 < δ → δ < 1 → 0 < Θ → Θ < θ → θ < Θ₀ → Θ₀ < 1 →
      ∀ c N₀ : ℝ, 0 < c → c ≤ 1 → 0 < N₀ →
        ∃ B : ℝ, 0 < B ∧
          ∀ N : ℕ, 1 ≤ N → (N : ℝ) < N₀ → ∀ (f : ℝ → ℝ) (k : ℕ),
          3 ≤ k → (∃ U : Set ℝ, IsOpen U ∧ Set.Icc (N : ℝ) (2 * N) ⊆ U ∧ ContDiffOn ℝ k f U) →
          (∀ x ∈ Set.Icc (N : ℝ) (2 * N),
            |iteratedDeriv k f x / k.factorial| ≤ (N : ℝ) ^ (-(Θ₀ * k))) →
          δ * k ≤ 1 →
          (∀ x ∈ Set.Icc (N : ℝ) (2 * N),
            (N : ℝ) ^ (-(θ * (1 : ℕ))) ≤ |iteratedDeriv 1 f x / (1 : ℕ).factorial| ∧
            |iteratedDeriv 1 f x / (1 : ℕ).factorial| ≤ (N : ℝ) ^ (-(Θ * (1 : ℕ)))) →
          ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  sorry

/-- LEAF. Step 1 of the split, one sign for `f'`: from `N ≥ 1`, `k ≥ 3`, `C^k` on a
neighbourhood of `[N, 2N]` and the two sided bound on `f'`, the derivative is continuous on
`[N, 2N]` and never `0` there, so it has one sign on the whole interval and the phase carries
no stationary point. -/
theorem leaf_s1_deriv_sign :
    ∀ N : ℕ, 1 ≤ N → ∀ (f : ℝ → ℝ) (k : ℕ) (θ Θ : ℝ), 3 ≤ k → 0 < Θ → Θ < θ →
      (∃ U : Set ℝ, IsOpen U ∧ Set.Icc (N : ℝ) (2 * N) ⊆ U ∧ ContDiffOn ℝ k f U) →
      (∀ x ∈ Set.Icc (N : ℝ) (2 * N),
        (N : ℝ) ^ (-(θ * (1 : ℕ))) ≤ |iteratedDeriv 1 f x / (1 : ℕ).factorial| ∧
        |iteratedDeriv 1 f x / (1 : ℕ).factorial| ≤ (N : ℝ) ^ (-(Θ * (1 : ℕ)))) →
      ((∀ x ∈ Set.Icc (N : ℝ) (2 * N), 0 < iteratedDeriv 1 f x) ∨
        (∀ x ∈ Set.Icc (N : ℝ) (2 * N), iteratedDeriv 1 f x < 0)) := by
  sorry

/-- The step `LeafS1Case` from the three leaves: the sign of `f'` from `leaf_s1_deriv_sign`,
the saving for `N ≥ N₀` from `leaf_s1_monotone_saving` with the exponent `c₁` weakened to
`min c₁ 1`, and the range `N < N₀` from `leaf_s1_small_N_boundary`. No `sorry`. -/
theorem leaf_s1_case_split : LeafS1Case := by
  intro θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  obtain ⟨B₁, c₁, N₀, hB₁, hc₁, hN₀, hbig⟩ :=
    leaf_s1_monotone_saving θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  obtain ⟨B₂, _, hsmall⟩ :=
    leaf_s1_small_N_boundary θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1 (min c₁ 1) N₀
      (lt_min hc₁ one_pos) (min_le_right _ _) hN₀
  refine ⟨max B₁ B₂, min c₁ 1, lt_of_lt_of_le hB₁ (le_max_left _ _), lt_min hc₁ one_pos, ?_⟩
  intro N hN f k hk3 hsm hder hδk hf'
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have : (0 : ℕ) < k := by omega
    exact_mod_cast this
  rcases lt_or_ge (N : ℝ) N₀ with hlt | hge
  · refine (hsmall N hN hlt f k hk3 hsm hder hδk hf').trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right B₁ B₂)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  · have hsgn := leaf_s1_deriv_sign N hN f k θ Θ hk3 hΘ0 hΘθ hsm hf'
    refine (hbig N hge f k hk3 hsm hder hδk hf' hsgn).trans ?_
    refine mul_le_mul (le_max_left B₁ B₂) ?_ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      (le_trans hB₁.le (le_max_left _ _))
    apply Real.rpow_le_rpow_of_exponent_le hNr
    have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    have hmin : min c₁ 1 / (k : ℝ) ^ 2 ≤ c₁ / (k : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (min_le_left _ _) hk2.le
    linarith

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
