/-
Pintz-Althöfer arXiv 2610.15559v1, Section 4.4, the elementary half of the L² input.
Unit U-1104, PC run 20261019T2003Z-20508, T2 FRONTIER, idea I-0080.

* (4.19), PROVED unconditional with an explicit constant: if `n` is not a sum of two primes,
  every nonzero term of `R_Λ(n) = Σ_{u+v=n} Λ(u)Λ(v)` has a proper prime power, so
  `R_Λ(n) ≤ 2 (√n + 1) log₂ n (log n)²`. The HTML render of the paper lost the square roots:
  the count of proper prime powers up to `X` is `O(√X log X)`, and the bound `O(√X (log X)³)`.
* `coef_gap`: (4.18) and (4.19) give the coefficient of `F_X² − V_X²` at least `c x / 2`.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.PintzAlthofer2026

namespace LeanLab.ExceptionalSet.PintzAlthofer2026

open Finset ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-- `R_Λ(n) = Σ_{u+v=n} Λ(u)Λ(v)`. -/
noncomputable def RΛ (n : ℕ) : ℝ := ∑ u ∈ range (n + 1), Λ u * Λ (n - u)

/-- A proper prime power: `p^k` with `k ≥ 2`, that is a prime power that is not prime. -/
def ProperPP (m : ℕ) : Prop := IsPrimePow m ∧ ¬ m.Prime

/-- The proper prime powers up to `n`. -/
noncomputable def ppSet (n : ℕ) : Finset ℕ := (range (n + 1)).filter ProperPP

/-- Every proper prime power `m ≤ n` is `p^k` with `p ≤ √n` and `2 ≤ k ≤ log₂ n`. -/
theorem ppSet_subset (n : ℕ) :
    ppSet n ⊆ ((range (Nat.sqrt n + 1)) ×ˢ (Icc 2 (Nat.log 2 n))).image (fun pk => pk.1 ^ pk.2) := by
  intro m hm
  simp only [ppSet, mem_filter, mem_range] at hm
  obtain ⟨hmn, hpp, hnp⟩ := hm
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).mp hpp
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · have : k = 1 := by omega
      subst this; simp at hnp; exact absurd hp hnp
    · exact h
  have hle : p ^ k ≤ n := by omega
  have hp2 : 2 ≤ p := hp.two_le
  simp only [mem_image, mem_product, mem_range, mem_Icc]
  refine ⟨(p, k), ⟨?_, hk2, ?_⟩, rfl⟩
  · have : p * p ≤ n := by
      calc p * p = p ^ 2 := by ring
        _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk2
        _ ≤ n := hle
    have := Nat.le_sqrt.mpr this
    omega
  · have h2k : 2 ^ k ≤ n := le_trans (Nat.pow_le_pow_left hp2 k) hle
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr h2k

/-- The count of proper prime powers up to `n`: at most `(√n + 1) log₂ n`. -/
theorem card_ppSet_le (n : ℕ) : (ppSet n).card ≤ (Nat.sqrt n + 1) * Nat.log 2 n := by
  calc (ppSet n).card
      ≤ (((range (Nat.sqrt n + 1)) ×ˢ (Icc 2 (Nat.log 2 n))).image (fun pk => pk.1 ^ pk.2)).card :=
        card_le_card (ppSet_subset n)
    _ ≤ ((range (Nat.sqrt n + 1)) ×ˢ (Icc 2 (Nat.log 2 n))).card := card_image_le
    _ = (Nat.sqrt n + 1) * (Nat.log 2 n + 1 - 2) := by simp [card_product]
    _ ≤ (Nat.sqrt n + 1) * Nat.log 2 n := Nat.mul_le_mul_left _ (by omega)

/-- In a non-Goldbach `n`, a nonzero term has a proper prime power. -/
theorem term_pp {n u : ℕ} (hu : u ≤ n) (hng : ¬ IsGoldbachSum n)
    (h : Λ u * Λ (n - u) ≠ 0) : ProperPP u ∨ ProperPP (n - u) := by
  have hu0 : Λ u ≠ 0 := left_ne_zero_of_mul h
  have hv0 : Λ (n - u) ≠ 0 := right_ne_zero_of_mul h
  rw [vonMangoldt_ne_zero_iff] at hu0 hv0
  by_contra hc
  push_neg at hc
  have hpu : u.Prime := by
    by_contra hnp; exact hc.1 ⟨hu0, hnp⟩
  have hpv : (n - u).Prime := by
    by_contra hnp; exact hc.2 ⟨hv0, hnp⟩
  exact hng ⟨u, n - u, hpu, hpv, by omega⟩

/-- (4.19), explicit: a non-Goldbach `n` has `R_Λ(n) ≤ 2 (√n + 1) log₂ n (log n)²`. -/
theorem RΛ_le_of_not_goldbach {n : ℕ} (hng : ¬ IsGoldbachSum n) :
    RΛ n ≤ 2 * ((Nat.sqrt n + 1) * Nat.log 2 n : ℕ) * Real.log n ^ 2 := by
  have hL : ∀ m ≤ n, Λ m ≤ Real.log n := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp; exact Real.log_natCast_nonneg n
    · exact vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hm))
  have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  -- each term is bounded by the indicator of a proper prime power at u or at n - u
  have hterm : ∀ u ∈ range (n + 1), Λ u * Λ (n - u) ≤
      (if ProperPP u then Real.log n ^ 2 else 0) + (if ProperPP (n - u) then Real.log n ^ 2 else 0) := by
    intro u hu
    have hun : u ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hu)
    by_cases h : Λ u * Λ (n - u) = 0
    · rw [h]; positivity
    · have hb : Λ u * Λ (n - u) ≤ Real.log n ^ 2 := by
        rw [sq]
        exact mul_le_mul (hL u hun) (hL (n - u) (Nat.sub_le n u)) vonMangoldt_nonneg hlog0
      rcases term_pp hun hng h with h1 | h1
      · rw [if_pos h1]; split_ifs <;> linarith [sq_nonneg (Real.log n)]
      · rw [if_pos h1]; split_ifs <;> linarith [sq_nonneg (Real.log n)]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite] at hsum
  simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul] at hsum
  -- the second count is the reflected first count
  have hrefl : ((range (n + 1)).filter (fun u => ProperPP (n - u))).card = (ppSet n).card := by
    apply Finset.card_bij (fun u _ => n - u)
    · intro u hu
      simp only [mem_filter, mem_range] at hu
      simp only [ppSet, mem_filter, mem_range]; exact ⟨by omega, hu.2⟩
    · intro a ha b hb hab
      simp only [mem_filter, mem_range] at ha hb; omega
    · intro m hm
      simp only [ppSet, mem_filter, mem_range] at hm
      refine ⟨n - m, ?_, by omega⟩
      simp only [mem_filter, mem_range]
      exact ⟨by omega, by rw [show n - (n - m) = m by omega]; exact hm.2⟩
  have hc : ((ppSet n).card : ℝ) ≤ ((Nat.sqrt n + 1) * Nat.log 2 n : ℕ) := by
    exact_mod_cast card_ppSet_le n
  unfold RΛ
  have hfirst : ((range (n + 1)).filter ProperPP).card = (ppSet n).card := rfl
  rw [hrefl, hfirst] at hsum
  nlinarith [sq_nonneg (Real.log n)]

/-- (4.18) with (4.19): the coefficient of `F_X² − V_X²` at a bad `n` is at least `c x / 2`, as
soon as `e^{-n/X} R_Λ(n) ≤ c x / 2`. -/
theorem coef_gap {v r c x : ℝ} (hv : c * x ≤ |v|) (hr : |r| ≤ c * x / 2) :
    c * x / 2 ≤ |v - r| := by
  have := abs_sub_abs_le_abs_sub v r
  linarith

/-- The (4.19) bound is `o(x)`: for `n ≤ x`, `x ≥ 2`, it is at most `8 x^{1/2} (log x)³/log 2`,
here in the plain form `R_Λ(n) ≤ 2 (√x + 1) (log x / log 2) (log x)²`. -/
theorem RΛ_le_real {n : ℕ} (hng : ¬ IsGoldbachSum n) (hn : 1 ≤ n) :
    RΛ n ≤ 2 * (Real.sqrt n + 1) * (Real.log n / Real.log 2) * Real.log n ^ 2 := by
  have h := RΛ_le_of_not_goldbach hng
  have hs : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have hl : ((Nat.log 2 n : ℕ) : ℝ) ≤ Real.log n / Real.log 2 := by
    rw [le_div_iff₀ (Real.log_pos (by norm_num))]
    have h2 : (2 : ℝ) ^ (Nat.log 2 n) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have := Real.log_le_log (by positivity) h2
    rwa [Real.log_pow] at this
  have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  push_cast at h
  calc RΛ n ≤ 2 * (((Nat.sqrt n : ℕ) : ℝ) + 1) * ((Nat.log 2 n : ℕ) : ℝ) * Real.log n ^ 2 := by
        linarith
    _ ≤ 2 * (Real.sqrt n + 1) * (Real.log n / Real.log 2) * Real.log n ^ 2 := by
        gcongr

/-- Vacuity: the hypothesis of (4.19) is not empty; `n = 3` is not a sum of two primes. -/
theorem not_goldbach_three : ¬ IsGoldbachSum 3 := by
  rintro ⟨p, q, hp, hq, h⟩
  have h2 := hp.two_le; have h2' := hq.two_le; omega

end LeanLab.ExceptionalSet.PintzAlthofer2026
