/-
Split of the sealed statement `leaf_s1_monotone_saving` of
`LeanLab.ExceptionalSet.SPLIT_leaf_s1_case` (the step `LeafS1Case` of the lab class for the
case `S = {1}`, source Theorem 1).

The statement being split, verbatim after its name:

:
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
        ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) 

`leaf_s1_monotone_saving_split` below proves it from the leaves, with no `sorry` of its own
and without using the target theorem.

The cut is by the sign that the target assumes for the derivative.  The target ends with the
disjunction "`f' > 0` on the whole interval or `f' < 0` on the whole interval"; each leaf
takes one of the two disjuncts as an extra hypothesis and is otherwise the target word for
word, so each is strictly weaker than the target and neither disjunct implies the other.
The phase in the two cases has opposite orientation, so the two analyses are genuinely
different, and there is no conjugation symmetry in this file that would let one case be
derived from the other:

1. `leaf_s1_saving_sign_pos` - the increasing case, `0 < f'` on `[N, 2N]`.
2. `leaf_s1_saving_sign_neg` - the decreasing case, `f' < 0` on `[N, 2N]`.
3. `leaf_s1_exponent_merge` - the comparison that lets one pair `(B, c)` serve both cases:
   for `N ≥ 1`, `k ≥ 1` and `0 < c ≤ c'` a smaller gain `c` gives the larger exponent
   `1 - c / k ^ 2 ≥ 1 - c' / k ^ 2`, and `N ^ x` is nondecreasing in `x` there.

The assembly splits on the disjunction, takes `B = max B₁ B₂`, `c = min c₁ c₂` and the
threshold `max (max N₀₁ N₀₂) 1`; the last `1` is what supplies `N ≥ 1` for step 3 when both
thresholds happen to be below `1`.  `k ≥ 3` gives `0 < (k : ℝ)` for the division by `k ^ 2`.

Degenerate values were checked on each leaf: at `N = 1` the index set `(1, 2]` is the single
point `2`, so the sum has norm `1` and the right side is `B`; the linear phase
`f x = x * N ^ (-θ)` satisfies every hypothesis with `k = 3` and `δ = 1 / 3`, so no leaf has
hypotheses that cannot hold.

AI wrote the Lean code.  Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.SPLIT_leaf_s1_case

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-! ### Leaves -/

/-- LEAF. The increasing case: the target with the disjunction on the sign of `f'` replaced
by its first disjunct, `0 < f'` on the whole of `[N, 2N]`.  Every other hypothesis is the
target's, unchanged, and the conclusion is the same, so this is a strict sub-case of the
target and not a restatement of it.  Non-vacuous: the linear phase `f x = x * N ^ (-θ)` has
`f' = N ^ (-θ) ∈ [N ^ (-θ), N ^ (-Θ)]` because `Θ < θ`, so all hypotheses hold with
`k = 3`, `δ = 1 / 3`. -/
theorem leaf_s1_saving_sign_pos :
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
        (∀ x ∈ Set.Icc (N : ℝ) (2 * N), 0 < iteratedDeriv 1 f x) →
        ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  sorry

/-- LEAF. The decreasing case: the target with the disjunction on the sign of `f'` replaced
by its second disjunct, `f' < 0` on the whole of `[N, 2N]`.  As in the increasing case every
other hypothesis and the conclusion are the target's, so this is a strict sub-case and not a
restatement.  Non-vacuous: the phase `f x = -x * N ^ (-θ)` has `f' = -N ^ (-θ)`, of absolute
value in `[N ^ (-θ), N ^ (-Θ)]`, and satisfies the higher derivative bound with `k = 3`,
`δ = 1 / 3`. -/
theorem leaf_s1_saving_sign_neg :
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
        (∀ x ∈ Set.Icc (N : ℝ) (2 * N), iteratedDeriv 1 f x < 0) →
        ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  sorry

/-- LEAF. The comparison that lets the two cases share one pair of constants: for `N ≥ 1`,
`k ≥ 1` and `0 < c ≤ c'` the smaller gain gives the larger exponent, so that
`N ^ (1 - c' / k ^ 2) ≤ N ^ (1 - c / k ^ 2)`.  Small cases: at `N = 1` both powers are `1`;
at `c = c'` the two exponents coincide and the inequality is an equality, so the hypothesis
`0 < c ≤ c'` is satisfiable and this step is not vacuous. -/
theorem leaf_s1_exponent_merge (N : ℝ) (hN : 1 ≤ N) (k : ℕ) (hk : 0 < k) (c c' : ℝ)
    (hc : 0 < c) (hcc' : c ≤ c') :
    1 - c' / (k : ℝ) ^ 2 ≤ 1 - c / (k : ℝ) ^ 2 := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have h1 : c / (k : ℝ) ^ 2 ≤ c' / (k : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right hcc' hk2.le
  linarith

/-! ### Assembly -/

/-- The target from the three leaves above.  The derivative has one sign on `[N, 2N]` by the
last hypothesis of the target, which is a disjunction; its two cases are the first two
leaves.  The constants are `max B₁ B₂` and `min c₁ c₂`, the larger base dominating both
leaves and the smaller gain giving the larger exponent by the third leaf, and the threshold
is `max (max N₀₁ N₀₂) 1`, so that `N ≥ 1` is available for that comparison. -/
theorem leaf_s1_monotone_saving_split :
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
  intro θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  obtain ⟨B₁, c₁, N₁, hB₁, hc₁, hN₁, hb₁⟩ :=
    leaf_s1_saving_sign_pos θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  obtain ⟨B₂, c₂, N₂, hB₂, hc₂, hN₂, hb₂⟩ :=
    leaf_s1_saving_sign_neg θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  refine ⟨max B₁ B₂, min c₁ c₂, max (max N₁ N₂) 1,
    lt_of_lt_of_le hB₁ (le_max_left B₁ B₂), lt_min hc₁ hc₂,
    lt_of_lt_of_le zero_lt_one (le_max_right (max N₁ N₂) 1), ?_⟩
  intro N hN f k hk3 hsm hder hδk hf' hsgn
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := le_trans (le_max_right (max N₁ N₂) 1) hN
  have hNA : N₁ ≤ (N : ℝ) :=
    le_trans (le_trans (le_max_left N₁ N₂) (le_max_left (max N₁ N₂) 1)) hN
  have hNB : N₂ ≤ (N : ℝ) :=
    le_trans (le_trans (le_max_right N₁ N₂) (le_max_left (max N₁ N₂) 1)) hN
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hbase : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have step : ∀ (Bi ci : ℝ), 0 < Bi → 0 < ci → Bi ≤ max B₁ B₂ → min c₁ c₂ ≤ ci →
      Bi * (N : ℝ) ^ (1 - ci / (k : ℝ) ^ 2) ≤
        max B₁ B₂ * (N : ℝ) ^ (1 - min c₁ c₂ / (k : ℝ) ^ 2) := by
    intro Bi ci hBi hci hBle hcle
    have hcmin : 0 < min c₁ c₂ := lt_min hc₁ hc₂
    have hexp : 1 - ci / (k : ℝ) ^ 2 ≤ 1 - min c₁ c₂ / (k : ℝ) ^ 2 :=
      leaf_s1_exponent_merge (N : ℝ) hN1 k (by omega) (min c₁ c₂) ci hcmin hcle
    have hpow : (N : ℝ) ^ (1 - ci / (k : ℝ) ^ 2) ≤
        (N : ℝ) ^ (1 - min c₁ c₂ / (k : ℝ) ^ 2) :=
      Real.rpow_le_rpow_of_exponent_le hN1 hexp
    calc Bi * (N : ℝ) ^ (1 - ci / (k : ℝ) ^ 2)
        ≤ Bi * (N : ℝ) ^ (1 - min c₁ c₂ / (k : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hpow hBi.le
      _ ≤ max B₁ B₂ * (N : ℝ) ^ (1 - min c₁ c₂ / (k : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hBle (Real.rpow_nonneg hbase _)
  rcases hsgn with hpos | hneg
  · exact (hb₁ N hNA f k hk3 hsm hder hδk hf' hpos).trans
      (step B₁ c₁ hB₁ hc₁ (le_max_left B₁ B₂) (min_le_left c₁ c₂))
  · exact (hb₂ N hNB f k hk3 hsm hder hδk hf' hneg).trans
      (step B₂ c₂ hB₂ hc₂ (le_max_right B₁ B₂) (min_le_right c₁ c₂))

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
