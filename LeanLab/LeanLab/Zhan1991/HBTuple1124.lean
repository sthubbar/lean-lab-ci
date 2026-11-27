/-
P0068 Zhan 1991, the LEAF `hb_tuple_leaf` of DyadicSplit1122d.lean, page 263, split into one
finer cited LEAF, the pointwise ordered convolution identity, plus a PROVED assembly: the sum
over `n` regrouped as a sum over tuples by fibres of the product, with `χ` completely
multiplicative. Source: papers/P0068.pdf, pdf page 5.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.DyadicSplit1122d

namespace LeanLab.Zhan1991
open Finset Real
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

noncomputable section

open Classical in
/-- LEAF: page 263, the `j`-th Heath-Brown term at one integer `n`, `1 ≤ n ≤ N`, as an ordered
convolution sum: `(log * ζ^{j-1} * M_X^j)(n) = Σ_{n₁⋯n₂₀ = n} Π a_k(n_k)`, the variables at the
20 positions of `aj`, unused positions fixed at `1`, the `μ` variables cut at `X = N^{1/10}`,
and every variable cut at `N`, harmless since `n_k ∣ n ≤ N`. Class MEDIUM. -/
theorem hb_conv_tuple_leaf (N : ℕ) (j : ℕ) (hj : j ∈ Finset.Icc 1 10) (n : ℕ) (hn1 : 1 ≤ n)
    (hnN : n ≤ N) :
    (((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) *
      muTrunc ((N : ℝ) ^ (1 / 10 : ℝ)) ^ j) n : ℝ) : ℂ) =
      ∑ t ∈ (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter
        (fun t => ∏ k, t k = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧
          (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))),
        ∏ k : Fin 20, aj (k.val + 1) (t k) := by
  sorry

/-- PROVED from `hb_conv_tuple_leaf`: the statement of `hb_tuple_leaf`, page 263. -/
theorem hb_tuple_split (N : ℕ) (A : ℝ) (j : ℕ) (hj : j ∈ Finset.Icc 1 10) (hN : 2 ≤ N)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (u : ℝ) (hu : u ≤ N) :
    HBsum_dy j χ N A u = Tsum_dy j χ N A u := by
  classical
  have hfloor : ⌊u⌋₊ ≤ N := by
    have := Nat.floor_le_floor (R := ℝ) hu
    simpa using this
  -- left side, rewritten pointwise by the LEAF
  have hL : HBsum_dy j χ N A u = ∑ n ∈ ((Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n)), ∑ t ∈ (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter (fun t => ∏ k, t k = n ∧ ((∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)))),
      ∏ k : Fin 20, aj (k.val + 1) (t k) * χ (t k) := by
    unfold HBsum_dy
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn' := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    rw [hb_conv_tuple_leaf N j hj n hn'.1 (hn'.2.trans hfloor), Finset.sum_mul]
    refine Finset.sum_congr (by rfl) (fun t ht => ?_)
    have htn : ∏ k, t k = n := (Finset.mem_filter.mp ht).2.1
    rw [Finset.prod_mul_distrib, ← htn, Nat.cast_prod, map_prod]
  rw [hL]
  -- regroup by fibres of the product
  have hR : Tsum_dy j χ N A u = ∑ t ∈ (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter (fun t => (∏ k, t k) ∈ ((Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n)) ∧ ((∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)))),
      ∏ k : Fin 20, aj (k.val + 1) (t k) * χ (t k) := by
    unfold Tsum_dy
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hT', h1, h2, h3, h4⟩
      have hpos : ∀ k, 1 ≤ t k := fun k =>
        (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hT' k)).1
      have hp1 : 1 ≤ ∏ k, t k := by
        calc 1 = ∏ _k : Fin 20, (1 : ℕ) := by simp
          _ ≤ ∏ k, t k := Finset.prod_le_prod (fun k _ => hpos k)
      refine ⟨hT', ⟨⟨hp1, ?_⟩, by push_cast; exact h1⟩, h3, h4⟩
      apply Nat.le_floor
      push_cast; exact h2
    · rintro ⟨hT', ⟨⟨hp1, hp2⟩, h1⟩, h3, h4⟩
      refine ⟨hT', by push_cast at h1; exact h1, ?_, h3, h4⟩
      have hu0 : 0 ≤ u := by
        by_contra hneg
        replace hneg := lt_of_not_ge hneg
        have : ⌊u⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
        omega
      have := (Nat.le_floor_iff hu0).mp hp2
      push_cast at this; exact this
  rw [hR]
  have hmap : ∀ t ∈ (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter (fun t => (∏ k, t k) ∈ ((Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n)) ∧ ((∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)))), (∏ k, t k) ∈ ((Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n)) :=
    fun t ht => (Finset.mem_filter.mp ht).2.1
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext t
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hT', h1, h2⟩
    exact ⟨⟨hT', h1 ▸ Finset.mem_filter.mp hn, h2⟩, h1⟩
  · rintro ⟨⟨hT', _, h2⟩, h1⟩
    exact ⟨hT', h1, h2⟩

end

end LeanLab.Zhan1991
