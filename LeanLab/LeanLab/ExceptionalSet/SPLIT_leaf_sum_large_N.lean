/-
Split of the sealed statement `leaf_sum_large_N` of `LeanLab.ExceptionalSet.SPLIT_lemma10`.

That statement is the estimate of the class `KClass`: for `0 < δ < 1` and
`0 < Θ < θ < Θ₀ < 1` there are `B, c > 0` and a threshold `N₁` with
`‖Σ_{N < n ≤ 2N} e(f n)‖ ≤ B N^(1 - c/k²)` for every `f` in the class and every order `k`,
for all `N ≥ N₁`.

This file cuts it by the order `k`.  The class already forces `k ≥ 3`, so the two ranges
`k ≤ 3` (that is `k = 3`) and `4 ≤ k` exhaust the possibilities.  Leaves 1 and 2 are the
estimate on those two ranges, with constants allowed to depend on the range; leaf 3 is the
comparison of two powers of `N` that lets one pair `(B, c)` serve both ranges.  The
assembly `leaf_sum_large_N_split` below has the same type as the target and is proved from
the three leaves with no `sorry` of its own.

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_lemma10

namespace LeanLab.ExceptionalSet.U1539

/-! ### Leaves -/

/-- LEAF 1 of the split of `leaf_sum_large_N`: the estimate on the lowest order `k = 3`,
that is on the range `k ≤ 3` of the order, which the class forces to be a single value.
The constants of this leaf may depend on the range of `k`; that is what makes the leaf
strictly weaker than the statement that is split.  The hypotheses on `θ Θ Θ₀ δ` are the
ones of the class and are untouched, so the leaf is a sub-case and not a restatement. -/
theorem leaf_bound_k3 :
    ∀ θ Θ Θ₀ δ : ℝ, 0 < δ → δ < 1 → 0 < Θ → Θ < θ → θ < Θ₀ → Θ₀ < 1 →
      ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ (f : ℝ → ℝ) (k : ℕ),
        k ≤ 3 → KClass N θ Θ Θ₀ δ f k →
        ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  sorry

/-- LEAF 2 of the split of `leaf_sum_large_N`: the estimate on the orders `k ≥ 4`.  As in
LEAF 1 the constants may depend on the range of `k`, here the higher orders, and the
parameter hypotheses of the class are unchanged, so the leaf is a sub-case and not a
restatement of the statement that is split. -/
theorem leaf_bound_k_large :
    ∀ θ Θ Θ₀ δ : ℝ, 0 < δ → δ < 1 → 0 < Θ → Θ < θ → θ < Θ₀ → Θ₀ < 1 →
      ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ (f : ℝ → ℝ) (k : ℕ),
        4 ≤ k → KClass N θ Θ Θ₀ δ f k →
        ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  sorry

/-- LEAF 3 of the split of `leaf_sum_large_N`: the comparison of the two powers that lets
the two ranges share one pair `(B, c)`.  Since `N ≥ 1`, `N^x` is nondecreasing in `x`, and
a smaller `c` makes the exponent larger: `N^(1 - c_A/k²) ≤ N^(1 - c/k²)` whenever
`0 < c ≤ c_A` and `k ≥ 1`.  This is the only step of the assembly that touches `Real.rpow`.
Small cases: at `N = 1` both sides are `1`; at `k = 1` the exponents are `1 - c_A` and
`1 - c`; at `c = c_A` the two sides coincide, so the estimate holds with equality and the
hypothesis is not vacuous. -/
theorem leaf_exponent_mono (cA c : ℝ) (hc : 0 < c) (hcA : c ≤ cA) (N : ℕ) (hN : 1 ≤ N)
    (k : ℕ) (hk : 0 < k) :
    (N : ℝ) ^ (1 - cA / (k : ℝ) ^ 2) ≤ (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  have hN_real : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk2_pos : (0 : ℝ) < (k : ℝ) ^ 2 := sq_pos_of_pos hk_pos
  apply Real.rpow_le_rpow_of_exponent_le hN_real
  have h1 : c / (k : ℝ) ^ 2 ≤ cA / (k : ℝ) ^ 2 := div_le_div_of_nonneg_right hcA (le_of_lt hk2_pos)
  linarith

/-! ### Assembly -/

/-- The target from the three leaves above.  LEAF 1 covers `k = 3` and LEAF 2 covers
`k ≥ 4`; the class supplies `3 ≤ k`, so the two ranges exhaust the orders.  The constants
are `max B₁ B₂` and `min c₁ c₂`: the larger base dominates both leaves, and the smaller gain
gives the larger exponent by LEAF 3, applied with `N ≥ 1` coming from the threshold
`max (max N₁ N₂) 1`. -/
theorem leaf_sum_large_N_split :
    ∀ θ Θ Θ₀ δ : ℝ, 0 < δ → δ < 1 → 0 < Θ → Θ < θ → θ < Θ₀ → Θ₀ < 1 →
      ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ (f : ℝ → ℝ) (k : ℕ),
        KClass N θ Θ Θ₀ δ f k →
        ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  intro θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  obtain ⟨B₁, c₁, hB₁, hc₁, N₁, hN₁⟩ :=
    leaf_bound_k3 θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  obtain ⟨B₂, c₂, hB₂, hc₂, N₂, hN₂⟩ :=
    leaf_bound_k_large θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  refine ⟨max B₁ B₂, min c₁ c₂, lt_of_lt_of_le hB₁ (le_max_left B₁ B₂), lt_min hc₁ hc₂,
    max (max N₁ N₂) 1, ?_⟩
  intro N hN f k hK
  have hN1 : 1 ≤ N := le_trans (le_max_right (max N₁ N₂) 1) hN
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNle₁ : N₁ ≤ N :=
    le_trans (le_trans (le_max_left N₁ N₂) (le_max_left (max N₁ N₂) 1)) hN
  have hNle₂ : N₂ ≤ N :=
    le_trans (le_trans (le_max_right N₁ N₂) (le_max_left (max N₁ N₂) 1)) hN
  have hbase : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
  have hk3 : 3 ≤ k := hK.1
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hksq : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos hkpos 2
  have step : ∀ (Bi ci : ℝ), 0 < Bi → 0 < ci → Bi ≤ max B₁ B₂ → min c₁ c₂ ≤ ci →
      Bi * (N : ℝ) ^ (1 - ci / (k : ℝ) ^ 2) ≤
        max B₁ B₂ * (N : ℝ) ^ (1 - min c₁ c₂ / (k : ℝ) ^ 2) := by
    intro Bi ci hBi hci hBle hcle
    have hX : (0 : ℝ) ≤ (N : ℝ) ^ (1 - min c₁ c₂ / (k : ℝ) ^ 2) := Real.rpow_nonneg hbase _
    have hexp : (N : ℝ) ^ (1 - ci / (k : ℝ) ^ 2) ≤
        (N : ℝ) ^ (1 - min c₁ c₂ / (k : ℝ) ^ 2) := by
      refine Real.rpow_le_rpow_of_exponent_le hN1R ?_
      have hdiv : min c₁ c₂ / (k : ℝ) ^ 2 ≤ ci / (k : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hcle hksq.le
      linarith
    calc Bi * (N : ℝ) ^ (1 - ci / (k : ℝ) ^ 2)
        ≤ Bi * (N : ℝ) ^ (1 - min c₁ c₂ / (k : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hexp hBi.le
      _ ≤ max B₁ B₂ * (N : ℝ) ^ (1 - min c₁ c₂ / (k : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hBle hX
  rcases le_or_gt k 3 with hk | hk
  · exact le_trans (hN₁ N hNle₁ f k hk hK)
      (step B₁ c₁ hB₁ hc₁ (le_max_left B₁ B₂) (min_le_left c₁ c₂))
  · exact le_trans (hN₂ N hNle₂ f k (by omega) hK)
      (step B₂ c₂ hB₂ hc₂ (le_max_right B₁ B₂) (min_le_right c₁ c₂))

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.leaf_sum_large_N_split
