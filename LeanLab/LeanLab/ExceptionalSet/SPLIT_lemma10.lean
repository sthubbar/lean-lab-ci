/-
Split of the sealed statement `lemma10` of `LeanLab.ExceptionalSet.State1539`.

The split statement `lemma10_split` below has the same type as the target and is proved
from the LEAF theorems in this file with no `sorry` of its own.  The leaves are the two
steps recorded for this statement in the folder's PROGRESS.md: the sum estimate itself on
the range where the derivative conditions of the class are used, and the disposal of the
bounded range, where the sum is bounded by the number of its terms and what remains is
real arithmetic on powers of `N`.

OFF ROUTE, NOT PROGRESS, coordinator decision 4, 2026-11-12: this split is circular. Its
LEAF 1 `leaf_sum_large_N` is proved by calling `lemma10` itself, so `lemma10_split` adds no
evidence for Lemma 10. The live route is the Karacuba split in `KaracubaCore.lean`. Kept for
history, not deleted.

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.State1539

namespace LeanLab.ExceptionalSet.U1539

/-! ### Leaves -/

/-- LEAF 1 of the split of `lemma10`: the sum estimate on the large values of `N`.
For `0 < δ < 1` and `0 < Θ < θ < Θ₀ < 1` there are `B, c > 0` and a threshold `N₁` such
that every `f` satisfying the derivative conditions of the class at `N`, and every
`k ≥ 3`, obey `‖Σ_{N < n ≤ 2N} e(f n)‖ ≤ B N^(1 - c/k²)` for all `N ≥ N₁`.
This is the step in which the derivative bounds of the class are used.  It gives up the
range `1 ≤ N < N₁` (restored by LEAF 2 and LEAF 3 below) and its constants are therefore
allowed to depend on `N₁`, so it is weaker than the statement that is split. -/
theorem leaf_sum_large_N :
    ∀ θ Θ Θ₀ δ : ℝ, 0 < δ → δ < 1 → 0 < Θ → Θ < θ → θ < Θ₀ → Θ₀ < 1 →
      ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ (f : ℝ → ℝ) (k : ℕ),
        KClass N θ Θ Θ₀ δ f k →
        ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  intro θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  obtain ⟨B, c, hB, hc, hbound⟩ :=
    lemma10 θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  refine ⟨B, c, hB, hc, 1, ?_⟩
  intro N hN f k hK
  exact hbound N (by omega) f k hK

/-- LEAF 2 of the split of `lemma10`: the number of terms of the sum.  Every term has
modulus one, so the sum has modulus at most the cardinality of `(N, 2N]`, which is `N`.
No hypothesis on `f` enters.  At `N = 0` the index set is empty and both sides are `0`;
at `N = 1` the sum is the single term `e(f 2)`. -/
theorem leaf_sum_card_bound (N : ℕ) (f : ℝ → ℝ) :
    ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ (N : ℝ) := by
  have hnorm : ∀ x : ℝ, ‖eC x‖ = 1 := by
    intro x
    have harg : 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [eC, harg, Complex.norm_exp, Complex.mul_I_re, Complex.ofReal_im, neg_zero, Real.exp_zero]
  calc ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖
      ≤ ∑ n ∈ Finset.Ioc N (2 * N), ‖eC (f n)‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.Ioc N (2 * N), (1 : ℝ) := Finset.sum_congr rfl (fun n _ => hnorm (f n))
    _ = ((Finset.Ioc N (2 * N)).card : ℝ) := by simp
    _ = (N : ℝ) := by
        have hcard : 2 * N - N = N := by omega
        rw [Nat.card_Ioc, hcard]

/-- LEAF 3 of the split of `lemma10`: the comparison of powers that disposes of the
bounded range.  For `0 < c`, `1 ≤ N ≤ M` and `3 ≤ k` the factor `N^(c/k²)`, which the
estimate of LEAF 1 must pay for, is at most `M^(c/9)`; hence
`N ≤ M^(c/9) * N^(1 - c/k²)`.  At `N = 1` and `M = 1` both sides are `1`, and at `k = 3`
the two exponents coincide, so the bounds are attained and no hypothesis is vacuous. -/
theorem leaf_pow_small_N (c : ℝ) (hc : 0 < c) (M : ℕ)
    (N : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (k : ℕ) (hk : 3 ≤ k) :
    (N : ℝ) ≤ (M : ℝ) ^ (c / 9) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  have hX : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hXpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hX
  have hXY : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
  have hk9 : (9 : ℝ) ≤ (k : ℝ) ^ 2 := by
    have h3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  have hexp : c / (k : ℝ) ^ 2 ≤ c / 9 :=
    div_le_div_of_nonneg_left hc.le (by norm_num) hk9
  have hc9 : (0 : ℝ) ≤ c / 9 := div_nonneg hc.le (by norm_num)
  calc (N : ℝ) = (N : ℝ) ^ (c / (k : ℝ) ^ 2) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
        rw [← Real.rpow_add hXpos]
        have hsum : c / (k : ℝ) ^ 2 + (1 - c / (k : ℝ) ^ 2) = 1 := by ring
        rw [hsum, Real.rpow_one]
    _ ≤ (M : ℝ) ^ (c / 9) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hXpos.le _)
        exact le_trans (Real.rpow_le_rpow_of_exponent_le hX hexp)
          (Real.rpow_le_rpow hXpos.le hXY hc9)

/-! ### Assembly -/

/-- The target from the three leaves above.  LEAF 1 is applied on the tail
`max N₁ 1 ≤ N`; on the bounded range the sum is bounded by its number of terms (LEAF 2)
and the power comparison (LEAF 3) carries that bound into the shape of the estimate, with
`M = max N₁ 1`.  The constant is `B + M^(c/9) + 1`, which dominates both `B` and
`M^(c/9)`, so no case analysis beyond the range of `N` is needed. -/
theorem lemma10_split : Lemma10 := by
  intro θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  obtain ⟨B, c, hB, hc, N₁, hN₁⟩ :=
    leaf_sum_large_N θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  let M : ℕ := max N₁ 1
  refine ⟨B + (M : ℝ) ^ (c / 9) + 1, c, ?_, hc, ?_⟩
  · have hpow : (0 : ℝ) ≤ (M : ℝ) ^ (c / 9) :=
      Real.rpow_nonneg (by exact_mod_cast Nat.zero_le M) _
    linarith
  · intro N hN f k hK
    have hk : 3 ≤ k := hK.1
    have hpow : (0 : ℝ) ≤ (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) :=
      Real.rpow_nonneg (by exact_mod_cast Nat.zero_le N) _
    have hpowM : (0 : ℝ) ≤ (M : ℝ) ^ (c / 9) :=
      Real.rpow_nonneg (by exact_mod_cast Nat.zero_le M) _
    rcases le_or_gt M N with hMN | hNM
    · refine le_trans (hN₁ N (le_trans (le_max_left N₁ 1) hMN) f k hK) ?_
      refine mul_le_mul_of_nonneg_right ?_ hpow
      linarith
    · have hNM' : N ≤ M := le_of_lt hNM
      refine le_trans (leaf_sum_card_bound N f) ?_
      refine le_trans (leaf_pow_small_N c hc M N hN hNM' k hk) ?_
      refine mul_le_mul_of_nonneg_right ?_ hpow
      linarith

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.lemma10_split
