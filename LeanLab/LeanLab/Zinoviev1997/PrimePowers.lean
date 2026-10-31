/-
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261019T2314Z-cloud29, unit U-5793, paper P0097.

# Zinoviev 1997, (0.4): the prime powers in the triple sum

`T3_le`: if `N ≥ 2` is not a sum of three primes, then every triple sum
`T3 N M = Σ_{x + y + z = N} Λ(x)Λ(y)Λ(z) e^{-(x+y+z)/N}` is at most
`3 e^{-1} (ψ(N) - θ(N)) ψ(N) ln N`, since each nonzero term then has a coordinate that is a prime
power `p^k`, `k ≥ 2`, and those carry `ψ(N) - θ(N)` in total. This is the `θ N^{1.5} ln³ N` term of
(0.4) in a usable form. Binary Goldbach is OPEN.
-/
import LeanLab.Zinoviev1997.Series
import LeanLab.Common.Goldbach

namespace LeanLab.Zinoviev1997
open Real Finset ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-- `np n = 1` if `n` is not prime, else `0`. -/
noncomputable def np (n : ℕ) : ℝ := if n.Prime then 0 else 1

theorem np_nonneg (n : ℕ) : 0 ≤ np n := by unfold np; split_ifs <;> norm_num

/-- On a triple with sum `N`, `a(x)a(y)a(z) = e^{-1} Λ(x)Λ(y)Λ(z)`. -/
theorem aZ_triple {N x y z : ℕ} (hN : 0 < N) (h : x + y + z = N) :
    aZ N x * aZ N y * aZ N z = Real.exp (-1) * (Λ x * Λ y * Λ z) := by
  unfold aZ
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have : Real.exp (-x / N) * Real.exp (-y / N) * Real.exp (-z / N) = Real.exp (-1) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1
    have hs : (x : ℝ) + y + z = N := by exact_mod_cast h
    field_simp; linarith
  calc Λ x * Real.exp (-x / N) * (Λ y * Real.exp (-y / N)) * (Λ z * Real.exp (-z / N))
      = (Real.exp (-x / N) * Real.exp (-y / N) * Real.exp (-z / N)) * (Λ x * Λ y * Λ z) := by ring
    _ = _ := by rw [this]

/-- The pointwise step: with no prime triple, `ΛΛΛ ≤ (np x + np y + np z) ΛΛΛ`. -/
theorem triple_le {N x y z : ℕ} (hT : ¬ IsTernarySum N) (h : x + y + z = N) :
    Λ x * Λ y * Λ z ≤ (np x + np y + np z) * (Λ x * Λ y * Λ z) := by
  have h0 : 0 ≤ Λ x * Λ y * Λ z :=
    mul_nonneg (mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg) vonMangoldt_nonneg
  by_cases hx : x.Prime
  · by_cases hy : y.Prime
    · by_cases hz : z.Prime
      · exact absurd ⟨x, y, z, hx, hy, hz, h⟩ hT
      · have : np z = 1 := by simp [np, hz]
        have := np_nonneg x; have := np_nonneg y; nlinarith
    · have : np y = 1 := by simp [np, hy]
      have := np_nonneg x; have := np_nonneg z; nlinarith
  · have : np x = 1 := by simp [np, hx]
    have := np_nonneg y; have := np_nonneg z; nlinarith

/-- The inner sum over `z`: at most `ln N`, and `0` unless `x, y ≤ N`. -/
theorem inner_le (N M x y : ℕ) :
    ∑ z ∈ Icc 1 M, (if x + y + z = N then Λ z else 0) ≤
      if x ≤ N ∧ y ≤ N then Real.log N else 0 := by
  have hL0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hterm : ∀ z ∈ Icc 1 M, (if x + y + z = N then Λ z else 0) ≤
      if z = N - x - y then (if x ≤ N ∧ y ≤ N then Real.log N else 0) else 0 := by
    intro z hz
    rw [Finset.mem_Icc] at hz
    by_cases h1 : x + y + z = N
    · have h2 : z = N - x - y := by omega
      have h3 : x ≤ N ∧ y ≤ N := ⟨by omega, by omega⟩
      rw [if_pos h1, if_pos h2, if_pos h3]
      exact vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast hz.1)
        (by exact_mod_cast (by omega : z ≤ N)))
    · rw [if_neg h1]
      split_ifs <;> first | exact hL0 | exact le_rfl
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_ite_eq']
  split_ifs <;> first | exact le_rfl | (positivity) | (split_ifs <;> simp [Real.log_natCast_nonneg])

theorem sum_np_le (N M : ℕ) :
    ∑ x ∈ Icc 1 M, (if x ≤ N then np x * Λ x else 0) ≤ Chebyshev.psi N - Chebyshev.theta N := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, Finset.sum_filter]
  set g : ℕ → ℝ := fun x => if ¬ x.Prime then Λ x else 0 with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => by simp only [hg]; split_ifs <;> simp [vonMangoldt_nonneg]
  have h1 : ∑ x ∈ Icc 1 M, (if x ≤ N then np x * Λ x else 0) =
      ∑ x ∈ (Icc 1 M).filter (· ≤ N), g x := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h h' h' <;> simp_all [np, hg]
  rw [h1]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => hg0 x)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hx ⊢
  omega

theorem sum_L_le (N M : ℕ) : ∑ y ∈ Icc 1 M, (if y ≤ N then Λ y else 0) ≤ Chebyshev.psi N := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, ← Finset.sum_filter]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => vonMangoldt_nonneg)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢
  omega

/-- The sum with the distinguished non-prime coordinate first. -/
theorem Ax_le (N M : ℕ) :
    ∑ x ∈ Icc 1 M, ∑ y ∈ Icc 1 M, ∑ z ∈ Icc 1 M,
      (if x + y + z = N then np x * (Λ x * Λ y * Λ z) else 0) ≤
      (Chebyshev.psi N - Chebyshev.theta N) * Chebyshev.psi N * Real.log N := by
  have hL0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have step : ∀ x y : ℕ, ∑ z ∈ Icc 1 M, (if x + y + z = N then np x * (Λ x * Λ y * Λ z) else 0) ≤
      (if x ≤ N then np x * Λ x else 0) * (if y ≤ N then Λ y else 0) * Real.log N := by
    intro x y
    have e : ∑ z ∈ Icc 1 M, (if x + y + z = N then np x * (Λ x * Λ y * Λ z) else 0) =
        (np x * Λ x * Λ y) * ∑ z ∈ Icc 1 M, (if x + y + z = N then Λ z else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      split_ifs <;> ring
    rw [e]
    have hc : 0 ≤ np x * Λ x * Λ y :=
      mul_nonneg (mul_nonneg (np_nonneg x) vonMangoldt_nonneg) vonMangoldt_nonneg
    refine (mul_le_mul_of_nonneg_left (inner_le N M x y) hc).trans ?_
    split_ifs with h1 h2 h3 h2 h3 <;> first | (simp_all) | (nlinarith [h1]) | skip
    all_goals first | (exfalso; tauto) | (simp)
  calc ∑ x ∈ Icc 1 M, ∑ y ∈ Icc 1 M, ∑ z ∈ Icc 1 M,
        (if x + y + z = N then np x * (Λ x * Λ y * Λ z) else 0)
      ≤ ∑ x ∈ Icc 1 M, ∑ y ∈ Icc 1 M,
        (if x ≤ N then np x * Λ x else 0) * (if y ≤ N then Λ y else 0) * Real.log N :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => step x y
    _ = (∑ x ∈ Icc 1 M, (if x ≤ N then np x * Λ x else 0)) *
        (∑ y ∈ Icc 1 M, (if y ≤ N then Λ y else 0)) * Real.log N := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul]
    _ ≤ (Chebyshev.psi N - Chebyshev.theta N) * Chebyshev.psi N * Real.log N := by
        have h1 := sum_np_le N M
        have h2 := sum_L_le N M
        have hA0 : 0 ≤ ∑ x ∈ Icc 1 M, (if x ≤ N then np x * Λ x else 0) :=
          Finset.sum_nonneg fun x _ => by
            split_ifs <;> first | exact mul_nonneg (np_nonneg x) vonMangoldt_nonneg | exact le_rfl
        have hB0 : 0 ≤ ∑ y ∈ Icc 1 M, (if y ≤ N then Λ y else 0) :=
          Finset.sum_nonneg fun y _ => by split_ifs <;> first | exact vonMangoldt_nonneg | exact le_rfl
        have := mul_le_mul h1 h2 hB0 (hA0.trans h1)
        exact mul_le_mul_of_nonneg_right this hL0

/-- **Prime powers**: with no prime triple, `T3 N M ≤ 3 e^{-1} (ψ(N) - θ(N)) ψ(N) ln N`. -/
theorem T3_le {N : ℕ} (hN : 0 < N) (hT : ¬ IsTernarySum N) (M : ℕ) :
    T3 N M ≤ 3 * Real.exp (-1) *
      ((Chebyshev.psi N - Chebyshev.theta N) * Chebyshev.psi N * Real.log N) := by
  set F : ℕ → ℕ → ℕ → ℝ := fun x y z => if x + y + z = N then Λ x * Λ y * Λ z else 0
  have h1 : T3 N M = Real.exp (-1) * ∑ x ∈ Icc 1 M, ∑ y ∈ Icc 1 M, ∑ z ∈ Icc 1 M, F x y z := by
    unfold T3
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun z _ => ?_
    simp only [F]
    split_ifs with h
    · exact aZ_triple hN h
    · simp
  have h2 : ∑ x ∈ Icc 1 M, ∑ y ∈ Icc 1 M, ∑ z ∈ Icc 1 M, F x y z ≤
      ∑ x ∈ Icc 1 M, ∑ y ∈ Icc 1 M, ∑ z ∈ Icc 1 M,
        ((if x + y + z = N then np x * (Λ x * Λ y * Λ z) else 0) +
         (if x + y + z = N then np y * (Λ x * Λ y * Λ z) else 0) +
         (if x + y + z = N then np z * (Λ x * Λ y * Λ z) else 0)) := by
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
      Finset.sum_le_sum fun z _ => ?_
    simp only [F]
    split_ifs with h
    · have := triple_le hT h; linarith
    · simp
  have A := Ax_le N M
  have Ay : ∑ x ∈ Icc 1 M, ∑ y ∈ Icc 1 M, ∑ z ∈ Icc 1 M,
      (if x + y + z = N then np y * (Λ x * Λ y * Λ z) else 0) ≤
      (Chebyshev.psi N - Chebyshev.theta N) * Chebyshev.psi N * Real.log N := by
    rw [Finset.sum_comm]
    refine le_of_eq_of_le ?_ A
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun z _ => ?_
    by_cases h : x + y + z = N
    · rw [if_pos h, if_pos (by omega)]; ring
    · rw [if_neg h, if_neg (by omega)]
  have Az : ∑ x ∈ Icc 1 M, ∑ y ∈ Icc 1 M, ∑ z ∈ Icc 1 M,
      (if x + y + z = N then np z * (Λ x * Λ y * Λ z) else 0) ≤
      (Chebyshev.psi N - Chebyshev.theta N) * Chebyshev.psi N * Real.log N := by
    have e1 : ∑ x ∈ Icc 1 M, ∑ y ∈ Icc 1 M, ∑ z ∈ Icc 1 M,
        (if x + y + z = N then np z * (Λ x * Λ y * Λ z) else 0) =
        ∑ x ∈ Icc 1 M, ∑ z ∈ Icc 1 M, ∑ y ∈ Icc 1 M,
        (if x + y + z = N then np z * (Λ x * Λ y * Λ z) else 0) :=
      Finset.sum_congr rfl fun x _ => Finset.sum_comm
    rw [e1, Finset.sum_comm]
    refine le_of_eq_of_le ?_ A
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun y _ => ?_
    by_cases h : x + y + z = N
    · rw [if_pos h, if_pos (by omega)]; ring
    · rw [if_neg h, if_neg (by omega)]
  rw [h1]
  have he := Real.exp_pos (-1)
  simp only [Finset.sum_add_distrib] at h2
  nlinarith

end LeanLab.Zinoviev1997
