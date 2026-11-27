/-
P0068 Zhan 1991, the LEAF `tuple_dyadic_leaf` of DyadicSplit1122d.lean, page 264 top, split
into two finer cited LEAF steps, the dyadic partition over the full grid and the vanishing of
boxes failing condition (3.5), plus a PROVED assembly. Source: papers/P0068.pdf, pdf page 6.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.DyadicSplit1122d

namespace LeanLab.Zhan1991
open Finset Real

noncomputable section

/-- LEAF: page 264 top, "splitting the range of each variable into intervals `N_k < n_k ≤ 2N_k`":
every tuple of `Tsum_dy` lies in exactly one box `Π (N_k, 2N_k]` with `N_k` on the grid, and
every tuple of a grid box with `N - A < Π n_k ≤ u ≤ N` is a tuple of `Tsum_dy`, so the tuple sum
is the sum of the dyadic sums over all grid vectors. Class MEDIUM. -/
theorem tuple_grid_partition_leaf (N : ℕ) (hN : 1 ≤ N) (A : ℝ) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 10) (q : ℕ) (χ : DirichletCharacter ℂ q) (u : ℝ) (hu : u ≤ N) :
    haveI := Classical.decEq ℝ
    Tsum_dy j χ N A u = ∑ Nv ∈ Fintype.piFinset (grid_dy N j), Dsum_dy Nv χ N A u := by
  sorry

/-! ### PROVED helpers for the empty boxes -/

theorem rpow23_le_half_td (N : ℕ) (hN : (8 : ℝ) ≤ N) : (N : ℝ) ^ (2 / 3 : ℝ) ≤ (N : ℝ) / 2 := by
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have h3 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
    have h8 : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← h8]
    exact Real.rpow_le_rpow (by norm_num) hN (by norm_num)
  have hsplit : (N : ℝ) = (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add' hN0 (by norm_num)]; norm_num
  have hp : 0 ≤ (N : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hN0 _
  nlinarith

theorem dyad_bounds_td (x : ℝ) (n : ℕ) (h : n ∈ dyad x) :
    1 ≤ n ∧ x < n ∧ (n : ℝ) ≤ 2 * x := by
  unfold dyad at h
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
  obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp h1
  refine ⟨ha, h2, ?_⟩
  have hx : 0 ≤ 2 * x := by
    by_contra hneg
    have : ⌊2 * x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    omega
  exact (Nat.le_floor_iff hx).mp hb

theorem grid_le_X_td (N j : ℕ) (hN : 1 ≤ N) (k : Fin 20) (x : ℝ) (hx : x ∈ grid_dy N j k)
    (hk : 10 ≤ k.val) : x ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
  classical
  have hX : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  unfold grid_dy at hx
  by_cases h1 : usedPos_dy j k
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true hk)] at hx
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hx
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ 2 ^ (m + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)] at hx
    rw [Finset.mem_singleton.mp hx]; linarith

/-- PROVED, page 264 top, condition (3.5) is automatic for every box that carries a tuple: a grid
box with `N - A < Π n_k ≤ u ≤ N`, `n_k ∈ (N_k, 2N_k]`, has `Π N_k < Π n_k ≤ N` and
`Π N_k ≥ 2^{-20} Π n_k > 2^{-20} (N - A) ≥ N / 2^{21}` once `A ≤ N^{2/3} ≤ N/2`, and
`N_k ≤ X` at the `μ` positions by the grid, so a grid box failing `Cond35` has empty sum.
Proved here; no LEAF. -/
theorem box_not_cond35_leaf : ∃ N₀ : ℝ, ∀ (N : ℕ) (A : ℝ), N₀ ≤ N → 0 ≤ A →
    A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → ∀ j ∈ Finset.Icc 1 10,
    ∀ Nv ∈ Fintype.piFinset (grid_dy N j), ¬ Cond35 N Nv →
    ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (u : ℝ), (N : ℝ) - A ≤ u → u ≤ N →
      Dsum_dy Nv χ N A u = 0 := by
  refine ⟨8, ?_⟩
  intro N A hN hA hA' j _ Nv hNv hC q χ u _ hu2
  by_contra hne
  obtain ⟨n, hn, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hnmem, hlo, hhi⟩ := Finset.mem_filter.mp hn
  have hb : ∀ k, 1 ≤ n k ∧ Nv k < n k ∧ (n k : ℝ) ≤ 2 * Nv k := fun k =>
    dyad_bounds_td (Nv k) (n k) (Fintype.mem_piFinset.mp hnmem k)
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  apply hC
  have hhalf : ∀ k, (1 / 2 : ℝ) ≤ Nv k := by
    intro k
    have h1 : (1 : ℝ) ≤ n k := by exact_mod_cast (hb k).1
    linarith [(hb k).2.2]
  have hNv0 : ∀ k, 0 ≤ Nv k := fun k => by linarith [hhalf k]
  have hle : ∏ k, Nv k ≤ ∏ k, (n k : ℝ) :=
    Finset.prod_le_prod₀ (fun k _ => hNv0 k) (fun k _ => (hb k).2.1.le)
  have hge : ∏ k, (n k : ℝ) ≤ 2 ^ 20 * ∏ k, Nv k := by
    calc ∏ k, (n k : ℝ) ≤ ∏ k, (2 * Nv k) :=
          Finset.prod_le_prod₀ (fun k _ => by positivity) (fun k _ => (hb k).2.2)
      _ = 2 ^ 20 * ∏ k, Nv k := by rw [Finset.prod_mul_distrib]; simp
  have hAh := rpow23_le_half_td N hN
  refine ⟨hhalf, ?_, ?_, ?_⟩
  · have : (N : ℝ) / 2 < ∏ k, (n k : ℝ) := by linarith
    have h2 : (0 : ℝ) < 2 ^ 21 := by positivity
    rw [div_le_iff₀ h2]
    nlinarith
  · linarith
  · intro k hk
    exact grid_le_X_td N j hN1 k (Nv k) (Fintype.mem_piFinset.mp hNv k) hk

/-- PROVED from the two LEAF steps: the statement of `tuple_dyadic_leaf`, page 264 top. -/
theorem tuple_dyadic_split : ∃ N₀ : ℝ, ∀ (N : ℕ) (A : ℝ), N₀ ≤ N → 0 ≤ A →
    A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → ∀ j ∈ Finset.Icc 1 10,
    ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (u : ℝ), (N : ℝ) - A ≤ u → u ≤ N →
      Tsum_dy j χ N A u = ∑ Nv ∈ boxes_dy N j, Dsum_dy Nv χ N A u := by
  classical
  obtain ⟨N₁, h1⟩ := box_not_cond35_leaf
  refine ⟨max N₁ 1, ?_⟩
  intro N A hN hA hA' j hj q χ u hu1 hu2
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : (1 : ℝ) ≤ N := le_trans (le_max_right _ _) hN
  have hN2' : 1 ≤ N := by exact_mod_cast hN2
  rw [tuple_grid_partition_leaf N hN2' A j hj q χ u hu2]
  unfold boxes_dy
  rw [← Finset.sum_filter_add_sum_filter_not (Fintype.piFinset (grid_dy N j))
    (fun Nv => Cond35 N Nv)]
  have h0 : ∑ Nv ∈ (Fintype.piFinset (grid_dy N j)).filter (fun Nv => ¬ Cond35 N Nv),
      Dsum_dy Nv χ N A u = 0 := by
    refine Finset.sum_eq_zero (fun Nv hNv => ?_)
    have hm := Finset.mem_filter.mp hNv
    exact h1 N A hN1 hA hA' j hj Nv hm.1 hm.2 q χ u hu1 hu2
  rw [h0, add_zero]

end

end LeanLab.Zhan1991
