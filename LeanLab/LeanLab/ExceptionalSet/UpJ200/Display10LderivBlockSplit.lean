import Mathlib

/-!
# Split of `Display10LderivSplit.leaf_Lderiv_block`

Burst burst-20261122, Claude cloud session S150. AI wrote the Lean code. Binary Goldbach is open.

`leaf_Lderiv_block_of_leaves` is the exact type twin of `Display10LderivSplit.leaf_Lderiv_block`,
assembled from three leaves of the partial summation in Davenport chapter 14: the bound `r` for
character sums over intervals, Abel summation by parts, and the variation bound for the weight
`log t t^{-σ}` on `[r, ∞)`.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Display10LderivBlockSplit

open Real

/-- LEAF: Davenport, Multiplicative Number Theory, chapter 4, the trivial Polya bound: for a
nonprincipal character `χ` mod `r` the sum of `χ n` over a full period vanishes, so any sum over
an interval `r ≤ n < k` has norm at most `r`, class MEDIUM. -/
theorem leaf_char_interval_sum : ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
    χ ≠ 1 → ∀ k : ℕ, r ≤ k → ‖∑ n ∈ Finset.Ico r k, χ n‖ ≤ r := by
  sorry

/-- Summation by parts identity behind `leaf_abel_block`, Davenport chapter 14: for `r ≤ m`,
`∑_{r ≤ n ≤ m} a n w n = S_{m+1} w m - ∑_{r ≤ n < m} S_{n+1} (w (n+1) - w n)` with `S_k = ∑_{r ≤ j < k} a j`. -/
theorem abel_block_identity (a w : ℕ → ℂ) (r : ℕ) : ∀ m : ℕ, r ≤ m →
    ∑ n ∈ Finset.Ico r (m + 1), a n * w n =
      (∑ n ∈ Finset.Ico r (m + 1), a n) * w m -
        ∑ n ∈ Finset.Ico r m, (∑ j ∈ Finset.Ico r (n + 1), a j) * (w (n + 1) - w n) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have e1 : ∑ n ∈ Finset.Ico r (m + 1 + 1), a n * w n =
        ∑ n ∈ Finset.Ico r (m + 1), a n * w n + a (m + 1) * w (m + 1) :=
      Finset.sum_Ico_succ_top (by omega) _
    have e2 : ∑ n ∈ Finset.Ico r (m + 1 + 1), a n =
        ∑ n ∈ Finset.Ico r (m + 1), a n + a (m + 1) :=
      Finset.sum_Ico_succ_top (by omega) _
    have e3 : ∑ n ∈ Finset.Ico r (m + 1), (∑ j ∈ Finset.Ico r (n + 1), a j) * (w (n + 1) - w n) =
        ∑ n ∈ Finset.Ico r m, (∑ j ∈ Finset.Ico r (n + 1), a j) * (w (n + 1) - w n) +
          (∑ j ∈ Finset.Ico r (m + 1), a j) * (w (m + 1) - w m) :=
      Finset.sum_Ico_succ_top hm _
    rw [e1, e2, e3, ih]
    ring

/-- PROVED in S150, formerly LEAF: Davenport, Multiplicative Number Theory, chapter 14, Abel summation by parts on the
block `r ≤ n < M`: if all partial sums `∑_{r ≤ n < k} a n` with `r ≤ k ≤ M` have norm at most
`B`, then `‖∑_{r ≤ n < M} a n w n‖ ≤ B (‖w (M-1)‖ + ∑_{r ≤ n < M} ‖w (n+1) - w n‖)`, class EASY. -/
theorem leaf_abel_block : ∀ (a w : ℕ → ℂ) (r M : ℕ) (B : ℝ), r ≤ M →
    (∀ k : ℕ, r ≤ k → k ≤ M → ‖∑ n ∈ Finset.Ico r k, a n‖ ≤ B) →
      ‖∑ n ∈ Finset.Ico r M, a n * w n‖ ≤
        B * (‖w (M - 1)‖ + ∑ n ∈ Finset.Ico r M, ‖w (n + 1) - w n‖) := by
  intro a w r M B hrM hS
  have hB : 0 ≤ B := by simpa using hS r le_rfl hrM
  have hvar : 0 ≤ ∑ n ∈ Finset.Ico r M, ‖w (n + 1) - w n‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  rcases Nat.eq_or_lt_of_le hrM with h | h
  · subst h; simp; positivity
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hrm : r ≤ m := by omega
  simp only [Nat.add_sub_cancel]
  rw [abel_block_identity a w r m hrm]
  have h1 : ‖(∑ n ∈ Finset.Ico r (m + 1), a n) * w m‖ ≤ B * ‖w m‖ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hS _ (by omega) le_rfl) (norm_nonneg _)
  have h2 : ‖∑ n ∈ Finset.Ico r m, (∑ j ∈ Finset.Ico r (n + 1), a j) * (w (n + 1) - w n)‖
      ≤ B * ∑ n ∈ Finset.Ico r (m + 1), ‖w (n + 1) - w n‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum (fun n hn => ?_)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (by omega))
        (fun _ _ _ => mul_nonneg hB (norm_nonneg _)))
    rw [norm_mul]
    have hn := Finset.mem_Ico.mp hn
    exact mul_le_mul_of_nonneg_right (hS _ (by omega) (by omega)) (norm_nonneg _)
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ B * ‖w m‖ + B * ∑ n ∈ Finset.Ico r (m + 1), ‖w (n + 1) - w n‖ := add_le_add h1 h2
    _ = _ := by ring

/-- LEAF: Davenport, Multiplicative Number Theory, chapter 14, the weight `log t t^{-σ}` for
`1 - 1/log r ≤ σ ≤ 1`: for `r ≥ 8` it is decreasing on `[r, ∞)` since `e^{1/σ} ≤ r`, with value
at most `e log r / r` there because `r^{1-σ} ≤ e`; for `3 ≤ r < 8` it is bounded by `1/(eσ)`
with `σ` bounded below. Hence its endpoint value plus total variation over `r - 1 ≤ n ≤ M` is
`≤ K log r / r`, class MEDIUM. -/
theorem leaf_weight_variation : ∃ K : ℝ, 0 < K ∧ ∀ r : ℕ, 3 ≤ r →
    ∀ σ : ℝ, 1 - 1 / Real.log r ≤ σ → σ ≤ 1 → ∀ M : ℕ, r ≤ M →
      ‖(Real.log ((M - 1 : ℕ) : ℝ) : ℂ) * (((M - 1 : ℕ) : ℕ) : ℂ) ^ (-(σ : ℂ))‖ +
        ∑ n ∈ Finset.Ico r M,
          ‖(Real.log ((n + 1 : ℕ) : ℝ) : ℂ) * (((n + 1 : ℕ) : ℕ) : ℂ) ^ (-(σ : ℂ)) -
            (Real.log (n : ℝ) : ℂ) * ((n : ℕ) : ℂ) ^ (-(σ : ℂ))‖ ≤
        K * Real.log r / r := by
  sorry

/-- Exact type twin of `Display10LderivSplit.leaf_Lderiv_block`, assembled from the leaves.
The file imports only Mathlib so it builds without the parent chain. -/
theorem leaf_Lderiv_block_of_leaves : ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (_ : NeZero r)
    (χ : DirichletCharacter ℂ r), χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
    ∀ σ : ℝ, 1 - 1 / Real.log r ≤ σ → σ ≤ 1 → ∀ M : ℕ, r ≤ M →
      ‖∑ n ∈ Finset.Ico r M, χ n * ((Real.log n : ℂ) * (n : ℂ) ^ (-(σ : ℂ)))‖ ≤
        C * Real.log r := by
  obtain ⟨K, hK, hW⟩ := leaf_weight_variation
  refine ⟨K, hK, ?_⟩
  intro r hr χ hprim hsq hχ σ hσ1 hσ2 M hM
  have hr2 : 2 ≤ r := by
    have hr0 : r ≠ 0 := NeZero.ne r
    have hr1 : r ≠ 1 := by
      intro heq
      subst r
      exact hχ (DirichletCharacter.level_one χ)
    omega
  have hr3 : 3 ≤ r := by
    by_contra hlt
    have hr : r = 2 := by omega
    subst hr
    apply hχ
    ext a
    have hcard : Fintype.card (ZMod 2)ˣ = 1 := by
      rw [ZMod.card_units_eq_totient]; rfl
    have : a = 1 := by
      have := Fintype.card_le_one_iff_subsingleton.mp hcard.le
      exact Subsingleton.elim _ _
    subst this
    simp
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  set w : ℕ → ℂ := fun n => (Real.log (n : ℝ) : ℂ) * ((n : ℕ) : ℂ) ^ (-(σ : ℂ)) with hw
  have hab := leaf_abel_block (fun n => χ n) w r M r hM
    (fun k hk _ => leaf_char_interval_sum r hr χ hχ k hk)
  have hv := hW r hr3 σ hσ1 hσ2 M hM
  calc ‖∑ n ∈ Finset.Ico r M, χ n * ((Real.log n : ℂ) * (n : ℂ) ^ (-(σ : ℂ)))‖
      = ‖∑ n ∈ Finset.Ico r M, χ n * w n‖ := rfl
    _ ≤ r * (‖w (M - 1)‖ + ∑ n ∈ Finset.Ico r M, ‖w (n + 1) - w n‖) := hab
    _ ≤ r * (K * Real.log r / r) := by
        apply mul_le_mul_of_nonneg_left _ hrpos.le
        exact hv
    _ = K * Real.log r := by field_simp

#print axioms leaf_char_interval_sum
#print axioms leaf_abel_block
#print axioms leaf_weight_variation
#print axioms leaf_Lderiv_block_of_leaves

end LeanLab.ExceptionalSet.UpJ200.Display10LderivBlockSplit
