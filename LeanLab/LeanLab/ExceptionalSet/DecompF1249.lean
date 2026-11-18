/-
Unit U-1539, run 20261026T0403Z-9802, SPLIT job for P0082, track T1, task FREE-nv-glm6/task1249.
J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378, §8, p. 370-371: Karacuba's Lemma 10,
sealed as CITED `LeanLab.ExceptionalSet.State1539.lemma10`.

AI wrote this Lean code, checked only by the Lean kernel. Binary Goldbach is OPEN.

This file is a SPLIT of the sealed statement `lemma10`. It creates no existing declaration:
it only adds LEAF lemmas (each ending in `sorry`) and one assembly theorem
`lemma10_F1249 : Lemma10` proved from the leaves with no `sorry` of its own.

The argument is split into three steps:
  * LEAF 1: the Karacuba sum estimate on the tail range `N ≥ N₁`.  This is the analytic
    step in which the derivative bounds of `KClass` are used; it leaves the bounded
    range `1 ≤ N < N₁` to the next two leaves, so it is weaker than the sealed target
    and does not assume it.
  * LEAF 2: every term `eC (f n)` has modulus one, so the sum over `(N, 2N]` has modulus
    at most its number of terms, `N`.  No hypothesis on `f` enters.
  * LEAF 3: for `0 < c`, `1 ≤ N ≤ M` and `3 ≤ k`, `N ≤ M^(c/9) * N^(1 - c/k²)`,
    carrying the bounded-range bound into the shape of the estimate.
-/
import LeanLab.ExceptionalSet.State1539

namespace LeanLab.ExceptionalSet.U1539

open Real

/-! ### Leaves -/

/-- LEAF 1 of the split of `lemma10`: the sum estimate on the tail range `N ≥ N₁`.
For `0 < δ < 1` and `0 < Θ < θ < Θ₀ < 1` there are `B, c > 0` and a threshold `N₁` such
that every `f` satisfying the derivative conditions of `KClass` at `N`, and every `k ≥ 3`,
obey `‖Σ_{N < n ≤ 2N} e(f n)‖ ≤ B N^(1 - c/k²)` for all `N ≥ N₁`.  This is the step in
which the derivative bounds of the class are used.  It covers only the tail range
(`1 ≤ N < N₁` is restored by LEAF 2 and LEAF 3 below), so it is strictly weaker than the
sealed target and does not assume it. -/
theorem leaf_tail_estimate :
    ∀ θ Θ Θ₀ δ : ℝ, 0 < δ → δ < 1 → 0 < Θ → Θ < θ → θ < Θ₀ → Θ₀ < 1 →
      ∃ (B c : ℝ) (N₁ : ℕ), 0 < B ∧ 0 < c ∧
        ∀ (N : ℕ), N₁ ≤ N → ∀ (f : ℝ → ℝ) (k : ℕ),
          KClass N θ Θ Θ₀ δ f k →
          ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by sorry

/-- LEAF 2 of the split of `lemma10`: the cardinality bound.  Every term `eC (f n)` has
modulus one, so the sum over `(N, 2N]` has modulus at most its number of terms, `N`.
No hypothesis on `f` enters.  At `N = 0` the index set is empty and both sides are `0`;
at `N = 1` the sum is the single term `eC (f 2)`. -/
theorem leaf_card_bound (N : ℕ) (f : ℝ → ℝ) :
    ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ (N : ℝ) := by
  calc
    ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ ∑ n ∈ Finset.Ioc N (2 * N), ‖eC (f n)‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.Ioc N (2 * N), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [norm_eC (f n)]
    _ = ((Finset.Ioc N (2 * N)).card : ℝ) := by simp [Finset.sum_const]
    _ = (N : ℝ) := by
      have hcard : 2 * N - N = N := by omega
      rw [Nat.card_Ioc, hcard]

/-- LEAF 3 of the split of `lemma10`: the power comparison that disposes of the bounded
range.  For `0 < c`, `1 ≤ N ≤ M` and `3 ≤ k`, the factor `N^(c/k²)` that the estimate of
LEAF 1 must pay for is at most `M^(c/9)`, hence `N ≤ M^(c/9) * N^(1 - c/k²)`.
At `N = 1` and `M = 1` both sides are `1`, and at `k = 3` the two exponents coincide, so
the bounds are attained and no hypothesis is vacuous. -/
theorem leaf_pow_small_N (c : ℝ) (hc : 0 < c) (M : ℕ) (N : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M)
    (k : ℕ) (hk : 3 ≤ k) :
    (N : ℝ) ≤ (M : ℝ) ^ (c / 9) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  have hX : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hXpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hX
  have hXY : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
  have hk9 : (9 : ℝ) ≤ (k : ℝ) ^ 2 := by
    have h3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  have hexp : c / (k : ℝ) ^ 2 ≤ c / 9 := by
    apply div_le_div_of_nonneg_left hc.le
    norm_num
    <;> nlinarith
  have hc9 : (0 : ℝ) ≤ c / 9 := by positivity
  calc
    (N : ℝ) = (N : ℝ) ^ (c / (k : ℝ) ^ 2) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
      rw [← Real.rpow_add hXpos]
      have hsum : c / (k : ℝ) ^ 2 + (1 - c / (k : ℝ) ^ 2) = 1 := by ring
      rw [hsum]
      <;> simp [Real.rpow_one]
    _ ≤ (M : ℝ) ^ (c / 9) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
      refine' mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXpos.le _)
      exact le_trans (Real.rpow_le_rpow_of_exponent_le hX hexp)
        (Real.rpow_le_rpow hXpos.le hXY hc9)

#eval (decide ((4 : ℝ) ≤ (16 : ℝ) ^ ((1 : ℝ) / 9) * (4 : ℝ) ^ (1 - (1 : ℝ) / (3 : ℝ) ^ 2)))

/-! ### Assembly -/

/-- Assembly of the sealed `lemma10` from the three leaves above, with no `sorry` of its
own.  LEAF 1 gives the estimate on the tail `N ≥ N₁`; on the bounded range `N < N₁` the
sum is bounded by its number of terms (LEAF 2) and the power comparison with
`M = max N₁ 1` carries that bound into the shape of the estimate (LEAF 3).  The constant
`B + M^(c/9) + 1` dominates both `B` and `M^(c/9)`, so no case analysis beyond the range
of `N` is needed. -/
theorem lemma10_F1249 : Lemma10 := by
  intro θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  obtain ⟨B, c, N₁, hB, hc, hN₁⟩ :=
    leaf_tail_estimate θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  let M : ℕ := max N₁ 1
  have hM_nonneg : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.zero_le M
  refine ⟨B + (M : ℝ) ^ (c / 9) + 1, c, by positivity, hc, fun N hN f k hK => _⟩
  have hk : 3 ≤ k := hK.1
  have hNpos : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpow_nonneg : (0 : ℝ) ≤ (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
    apply Real.rpow_nonneg
    exact_mod_cast Nat.zero_le N
  have hpowM_nonneg : (0 : ℝ) ≤ (M : ℝ) ^ (c / 9) := by
    apply Real.rpow_nonneg
    exact_mod_cast Nat.zero_le M
  by_cases hNge : N₁ ≤ N
  · -- tail range: LEAF 1 applies
    have htail : ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) :=
      hN₁ N hNge f k hK
    have hle : B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) ≤
        (B + (M : ℝ) ^ (c / 9) + 1) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
      have h₁ : 0 ≤ (M : ℝ) ^ (c / 9) := hpowM_nonneg
      have h₂ : 0 ≤ (1 : ℝ) := by norm_num
      have h₃ : 0 ≤ (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := hpow_nonneg
      have h₄ : 0 ≤ B := by linarith
      nlinarith
    calc
      ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := htail
      _ ≤ (B + (M : ℝ) ^ (c / 9) + 1) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := hle
  · -- bounded range: N < N₁ ≤ M, so LEAF 2 and LEAF 3 apply
    have hNleM : (N : ℝ) ≤ (M : ℝ) := by
      have h₁ : N < N₁ := by linarith
      have h₂ : N ≤ N₁ := by omega
      have h₃ : (N₁ : ℕ) ≤ max N₁ 1 := by apply le_max_left
      have h₄ : N ≤ max N₁ 1 := by omega
      exact_mod_cast h₄
    have hcard : ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ (N : ℝ) := leaf_card_bound N f
    have hpow : (N : ℝ) ≤ (M : ℝ) ^ (c / 9) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
      have h₁ : 1 ≤ N := by exact_mod_cast hN
      have h₂ : N ≤ M := by exact_mod_cast hNleM
      exact leaf_pow_small_N c hc M N h₁ h₂ k hk
    calc
      ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ (N : ℝ) := hcard
      _ ≤ (M : ℝ) ^ (c / 9) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := hpow
      _ ≤ (B + (M : ℝ) ^ (c / 9) + 1) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
        have h₁ : 0 ≤ (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := hpow_nonneg
        have h₂ : 0 ≤ B := by linarith
        nlinarith [hpowM_nonneg]

end LeanLab.ExceptionalSet.U1539
