/-
Split of Decomp564aRoughLeaves.leaf_reciprocal_sum_region30, Jia 1996, Lemma 27, page 281.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The reciprocal double sum over region 30 is at most the product of two prime reciprocal sums
over windows Y^a < p <= Y^b with 0 < a <= b. Each such sum is bounded here in full,
by dyadic blocks and Mathlib's Chebyshev bound theta of x at most x log 4.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Chebyshev

namespace LeanLab.Languasco2004.Decomp564aRoughMertens
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Chebyshev block bound: the sum of 1/p over primes y < p <= 2y is at most 2 log 4 / log y,
from theta of 2y at most 2 y log 4, Mathlib Chebyshev.theta_le_log4_mul_x. -/
lemma block_bound (y : ℝ) (hy : 1 < y) (M : ℕ) :
    (∑ p ∈ range M, if p.Prime ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ 2 * y then 1 / (p : ℝ) else 0)
      ≤ 2 * Real.log 4 / Real.log y := by
  have hy0 : 0 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos hy
  have h1 : ∀ p ∈ range M, (if p.Prime ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ 2 * y then 1 / (p : ℝ) else 0)
      ≤ (if p.Prime ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ 2 * y then Real.log p else 0) / (y * Real.log y) := by
    intro p _
    split_ifs with hc
    · have hp : y < (p : ℝ) := hc.2.1
      have hlp : Real.log y < Real.log p := Real.log_lt_log hy0 hp
      rw [div_le_div_iff₀ (by linarith) (by positivity)]
      nlinarith
    · simp
  have h2 : (∑ p ∈ range M, if p.Prime ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ 2 * y then Real.log p else 0)
      ≤ Chebyshev.theta (2 * y) := by
    rw [← sum_filter, Chebyshev.theta]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [mem_filter, mem_range] at hp
      simp only [mem_filter, mem_Ioc]
      refine ⟨⟨hp.2.1.pos, ?_⟩, hp.2.1⟩
      exact Nat.le_floor hp.2.2.2
    · intro p hp _
      exact Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_lt.le)
  have h3 := Chebyshev.theta_le_log4_mul_x (x := 2 * y) (by linarith)
  calc _ ≤ ∑ p ∈ range M,
        (if p.Prime ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ 2 * y then Real.log p else 0) / (y * Real.log y) :=
        sum_le_sum h1
    _ = (∑ p ∈ range M,
        (if p.Prime ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ 2 * y then Real.log p else 0)) / (y * Real.log y) := by
        rw [sum_div]
    _ ≤ Real.log 4 * (2 * y) / (y * Real.log y) := by
        gcongr; exact h2.trans h3
    _ = 2 * Real.log 4 / Real.log y := by field_simp

/-- Dyadic cover: the window x < p <= x 2^J is the union of the blocks x 2^j < p <= x 2^(j+1). -/
lemma cover (x : ℝ) (_hx : 0 < x) (M J : ℕ) :
    (∑ p ∈ range M, if p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x * 2 ^ J then 1 / (p : ℝ) else 0)
      ≤ ∑ j ∈ range J, ∑ p ∈ range M,
        if p.Prime ∧ x * 2 ^ j < (p : ℝ) ∧ (p : ℝ) ≤ 2 * (x * 2 ^ j) then 1 / (p : ℝ) else 0 := by
  induction J with
  | zero =>
    simp only [pow_zero, mul_one, range_zero, sum_empty]
    apply le_of_eq
    apply sum_eq_zero
    intro p _
    rw [if_neg]
    rintro ⟨_, h1, h2⟩
    linarith
  | succ J ih =>
    rw [sum_range_succ]
    refine le_trans ?_ (add_le_add ih le_rfl)
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro p _
    have hp0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    by_cases hc : p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x * 2 ^ (J + 1)
    · rw [if_pos hc]
      by_cases hd : (p : ℝ) ≤ x * 2 ^ J
      · rw [if_pos ⟨hc.1, hc.2.1, hd⟩]
        split_ifs <;> linarith
      · rw [if_neg (fun h => hd h.2.2)]
        rw [if_pos ⟨hc.1, lt_of_not_ge hd, by rw [pow_succ] at hc; linarith [hc.2.2]⟩]
        simp
    · rw [if_neg hc]
      split_ifs <;> positivity

/-- Mertens type bound used on Jia page 281, Lemma 27, for the error term of the Buchstab step:
the sum of 1/p over primes Y^a < p <= Y^b is bounded for 0 < a <= b. PROVED S154 by dyadic
blocks and the Chebyshev bound. -/
theorem prime_reciprocal_window (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ K Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ M : ℕ,
      (∑ p ∈ range M,
          if p.Prime ∧ Y ^ a < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ b then 1 / (p : ℝ) else 0) ≤ K := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 * Real.log 4 * ((b - a) / (a * Real.log 2) + 1 / Real.log 2),
    Real.exp (Real.log 2 / a), ?_⟩
  intro Y hY M
  have hY0 : 0 < Y := (Real.exp_pos _).trans_le hY
  have hLY : Real.log 2 / a ≤ Real.log Y := by
    rw [← Real.log_exp (Real.log 2 / a)]; exact Real.log_le_log (Real.exp_pos _) hY
  set L := Real.log Y with hL
  have haL : Real.log 2 ≤ a * L := by
    have := mul_le_mul_of_nonneg_left hLY ha.le
    rwa [mul_div_cancel₀ _ ha.ne'] at this
  set x := Y ^ a with hx
  have hlx : Real.log x = a * L := by rw [hx, Real.log_rpow hY0]
  have hx0 : 0 < x := by positivity
  have hx1 : 1 < x := by
    rw [← Real.log_pos_iff hx0.le, hlx]; linarith
  set J := ⌈(b - a) * L / Real.log 2⌉₊ with hJ
  have hJle : (J : ℝ) < (b - a) * L / Real.log 2 + 1 := by
    apply Nat.ceil_lt_add_one
    have : 0 ≤ L := le_trans (div_nonneg hl2.le ha.le) hLY
    have : 0 ≤ b - a := by linarith
    positivity
  have hJge : (b - a) * L / Real.log 2 ≤ J := Nat.le_ceil _
  have hYb : Y ^ b ≤ x * 2 ^ J := by
    have e : Y ^ b = x * Y ^ (b - a) := by
      rw [hx, ← Real.rpow_add hY0]; congr 1; ring
    rw [e]
    gcongr
    rw [Real.rpow_def_of_pos hY0, ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    rw [← hL]
    have := (div_le_iff₀ hl2).mp hJge
    linarith
  have hstep : (∑ p ∈ range M,
      if p.Prime ∧ Y ^ a < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ b then 1 / (p : ℝ) else 0) ≤
      ∑ p ∈ range M, if p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x * 2 ^ J then 1 / (p : ℝ) else 0 := by
    apply sum_le_sum
    intro p _
    by_cases hc : p.Prime ∧ Y ^ a < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ b
    · rw [if_pos hc, if_pos ⟨hc.1, hc.2.1, hc.2.2.trans hYb⟩]
    · rw [if_neg hc]; split_ifs <;> positivity
  have hblk : ∀ j ∈ range J, (∑ p ∈ range M,
      if p.Prime ∧ x * 2 ^ j < (p : ℝ) ∧ (p : ℝ) ≤ 2 * (x * 2 ^ j) then 1 / (p : ℝ) else 0)
      ≤ 2 * Real.log 4 / (a * L) := by
    intro j _
    have hyj : x ≤ x * 2 ^ j := le_mul_of_one_le_right hx0.le (one_le_pow₀ (by norm_num))
    refine (block_bound (x * 2 ^ j) (by linarith) M).trans ?_
    rw [← hlx]
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hlx0 : 0 < Real.log x := Real.log_pos hx1
    gcongr
  have haL0 : 0 < a * L := hl2.trans_le haL
  calc _ ≤ _ := hstep
    _ ≤ _ := cover x hx0 M J
    _ ≤ ∑ j ∈ range J, 2 * Real.log 4 / (a * L) := sum_le_sum hblk
    _ = J * (2 * Real.log 4 / (a * L)) := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ ((b - a) * L / Real.log 2 + 1) * (2 * Real.log 4 / (a * L)) := by
        have : 0 ≤ 2 * Real.log 4 / (a * L) := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); positivity
        nlinarith
    _ = 2 * Real.log 4 * ((b - a) / (a * Real.log 2) + 1 / (a * L)) := by
        have hL0 : L ≠ 0 := by
          intro h0; rw [h0, mul_zero] at haL0; exact lt_irrefl _ haL0
        field_simp
    _ ≤ 2 * Real.log 4 * ((b - a) / (a * Real.log 2) + 1 / Real.log 2) := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
        gcongr

#print axioms block_bound
#print axioms cover
#print axioms prime_reciprocal_window
end
end LeanLab.Languasco2004.Decomp564aRoughMertens
