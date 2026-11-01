import Mathlib
import LeanLab.GoldbachGaps.Goldston1990Main
import LeanLab.GoldbachGaps.Goldston1990Cor2
import LeanLab.SchnirelmannGoldbach.Discharged

namespace LeanLab.GoldbachGaps.DecompJ610
open Real Finset Filter Topology
open LeanLab.GoldbachGaps.Goldston1990
open LeanLab.SchnirelmannGoldbach

/-- LEAF p. 292: Corollary 1, display 7 -/
theorem leaf_corollary1 : Corollary1 := sorry

/-- LEAF p. 292: Cauchy's inequality for rg on [N, N+K] -/
theorem leaf_cauchy_rg (N K : ℕ) :
    (∑ n ∈ Icc N (N + K), (rg n : ℝ)) ^ 2 ≤
    (((Icc N (N + K)).filter (fun n => 1 ≤ rg n)).card : ℝ) *
    ∑ n ∈ Icc N (N + K), (rg n : ℝ) ^ 2 := by
  let S := (Icc N (N + K)).filter (fun n => 1 ≤ rg n)
  have h_eq : ∑ n ∈ Icc N (N + K), (rg n : ℝ) = ∑ n ∈ S, (rg n : ℝ) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro x hx
    split_ifs with h
    · rfl
    · have : rg x = 0 := by omega
      rw [this, Nat.cast_zero]
  rw [h_eq]
  have := sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun n => (rg n : ℝ))
  simp only [one_mul, sum_const, nsmul_eq_mul] at this
  have hs_eq : (S.card : ℝ) * 1 ^ 2 = (S.card : ℝ) := by ring
  rw [hs_eq] at this
  refine le_trans this ?_
  have h_le : ∑ i ∈ S, (rg i : ℝ) ^ 2 ≤ ∑ n ∈ Icc N (N + K), (rg n : ℝ) ^ 2 := by
    refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) ?_
    intro n _ _
    exact sq_nonneg _
  exact mul_le_mul_of_nonneg_left h_le (Nat.cast_nonneg _)

/-- LEAF p. 292: Lower bound for sum of rg from Corollary 1 -/
theorem leaf_sum_rg_lower_bound (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3)
    (hj : Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0)) :
    ∀ᶠ N : ℕ in atTop, 1 / 2 * K N * N / Real.log N ^ 2 ≤ ∑ n ∈ Icc N (N + K N), (rg n : ℝ) := sorry

/-- LEAF p. 293: Sieve bound pointwise on [N, N+K] -/
theorem leaf_rg_le_singProd (C : ℝ) (_hC : 0 < C) (N K : ℕ) (n : ℕ) (_hn : n ∈ Icc N (N + K))
    (_hN : 3 ≤ N) (_hKN : K ≤ N) :
    (rg n : ℝ) ≤ C * n / Real.log n ^ 2 * singProd n →
    (rg n : ℝ) ≤ 2 * C * N / Real.log N ^ 2 * singProd n := by
  intro h
  have : (n : ℝ) / Real.log n ^ 2 ≤ 2 * N / Real.log N ^ 2 := sorry
  sorry

/-- LEAF p. 293: Sieve bound pointwise square on [N, N+K] -/
theorem leaf_rg_sq_le_singProd (C : ℝ) (_hC : 0 < C) (N K : ℕ) (n : ℕ) (_hn : n ∈ Icc N (N + K))
    (_hN : 3 ≤ N) (_hKN : K ≤ N) :
    (rg n : ℝ) ≤ 2 * C * N / Real.log N ^ 2 * singProd n →
    (rg n : ℝ) ^ 2 ≤ 4 * C ^ 2 * (N : ℝ) ^ 2 / Real.log N ^ 4 * singProd n ^ 2 := by
  intro h
  have h1 : 0 ≤ (rg n : ℝ) := Nat.cast_nonneg _
  have h4 := mul_self_le_mul_self h1 h
  have e : (2 * C * N / Real.log N ^ 2 * singProd n) * (2 * C * N / Real.log N ^ 2 * singProd n) = 4 * C ^ 2 * (N : ℝ) ^ 2 / Real.log N ^ 4 * singProd n ^ 2 := by ring
  have e2 : (rg n : ℝ) * (rg n : ℝ) = (rg n : ℝ) ^ 2 := by ring
  rw [e2] at h4
  rwa [e] at h4

/-- LEAF p. 293: Sieve bound sum on [N, N+K] -/
theorem leaf_sum_rg_sq_le (C : ℝ) (_hC : 0 < C) (N K : ℕ) (_hN : 3 ≤ N) (_hKN : K ≤ N)
    (h_pointwise : ∀ n ∈ Icc N (N + K), (rg n : ℝ) ^ 2 ≤ 4 * C ^ 2 * (N : ℝ) ^ 2 / Real.log N ^ 4 * singProd n ^ 2) :
    ∑ n ∈ Icc N (N + K), (rg n : ℝ) ^ 2 ≤
    4 * C ^ 2 * (N : ℝ) ^ 2 / Real.log N ^ 4 * ∑ n ∈ Icc N (N + K), singProd n ^ 2 := by
  have := sum_le_sum h_pointwise
  rw [← Finset.mul_sum] at this
  exact this

/-- LEAF p. 293: Mean square of singProd bounded by K -/
theorem leaf_singProd_sq_bound (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, Real.log N ^ 2 ≤ K N) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
    ∑ n ∈ Icc N (N + K N), singProd n ^ 2 ≤ C * K N := sorry

/-- LEAF p. 293: Sum of rg^2 bounded by K * N^2 / log^4 N -/
theorem leaf_sum_rg_sq_bound_K (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, Real.log N ^ 2 ≤ K N ∧ K N ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
    ∑ n ∈ Icc N (N + K N), (rg n : ℝ) ^ 2 ≤ C * K N * (N : ℝ) ^ 2 / Real.log N ^ 4 := sorry

/-- LEAF p. 293: Assembly of Corollary 2 -/
theorem leaf_assembly_corollary2 : Corollary2 := sorry

theorem assembly_corollary2 : Corollary2 := leaf_assembly_corollary2

end LeanLab.GoldbachGaps.DecompJ610
