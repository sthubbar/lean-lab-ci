/-
P0079 page 9, the elementary integer versus continuous approximation.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Quadrature396
import LeanLab.LZPowersOfTwo.DiscreteModel396

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 9, the partial-summation estimate before J3.
The inclusive integer sum differs from T by at most two plus pi absolute
frequency times the interval length. The extra endpoint costs at most one. -/
theorem discretePrime_sub_continuous396 (ε X α : ℝ)
    (ha : 0 ≤ ε * X) (hab : ε * X ≤ X) :
    ‖discretePrime396 ε X α - continuousPrime353 ε X α‖ ≤
      2 + Real.pi * |α| * (X - ε * X) := by
  classical
  let P := (range (⌊X⌋₊ + 1)).filter (fun n : ℕ => ε * X ≤ (n : ℝ))
  let Q := Ioc ⌊ε * X⌋₊ ⌊X⌋₊
  have hsub : Q ⊆ P := by
    intro n hn
    have hn' := mem_Ioc.mp hn
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hn'.2),
      ((Nat.floor_lt ha).mp hn'.1).le⟩
  have hone : P \ Q ⊆ {⌊ε * X⌋₊} := by
    intro n hn
    have hnP := mem_filter.mp (mem_sdiff.mp hn).1
    have hnX := Nat.le_of_lt_succ (mem_range.mp hnP.1)
    have hna : ⌊ε * X⌋₊ ≤ n := by simpa only [Nat.floor_natCast] using Nat.floor_le_floor hnP.2
    have hnQ := (mem_sdiff.mp hn).2
    have he : n = ⌊ε * X⌋₊ := by
      by_contra H
      exact hnQ (mem_Ioc.mpr ⟨by omega, hnX⟩)
    simpa only [mem_singleton] using he
  have hdiff : ‖discretePrime396 ε X α - ∑ n ∈ Q, character293 ((n : ℝ) * α)‖ ≤ 1 := by
    change ‖(∑ n ∈ P, character293 ((n : ℝ) * α)) - ∑ n ∈ Q, character293 ((n : ℝ) * α)‖ ≤ 1
    rw [← sum_sdiff hsub, add_sub_cancel_right]
    calc
      _ ≤ ∑ n ∈ P \ Q, ‖character293 ((n : ℝ) * α)‖ := norm_sum_le _ _
      _ = ((P \ Q).card : ℝ) := by simp only [character_norm293, sum_const, nsmul_eq_mul, mul_one]
      _ ≤ 1 := by exact_mod_cast (card_le_card hone).trans_eq (card_singleton _)
  have hquad := character_riemann396 (ε * X) X α ha hab
  have H := norm_sub_le_norm_sub_add_norm_sub (discretePrime396 ε X α)
    (∑ n ∈ Q, character293 ((n : ℝ) * α)) (continuousPrime353 ε X α)
  have hquad' : ‖(∑ n ∈ Q, character293 ((n : ℝ) * α)) - continuousPrime353 ε X α‖ ≤
      1 + Real.pi * |α| * (X - ε * X) := hquad
  exact H.trans (by linarith only [hdiff, hquad'])

/-- P0079 page 9, the prime bound in the J3 quadrature error.
Mathlib Chebyshev gives the stronger uniform bound log 4 times X. -/
theorem primeSum_norm_chebyshev396 (ε X α : ℝ) (hX : 0 ≤ X) :
    ‖primeSum293 ε X α‖ ≤ log 4 * X := by
  let P := (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ))
  let Q := (Ioc 0 ⌊X⌋₊).filter (fun p : ℕ => p.Prime)
  have hsub : P ⊆ Q := by
    intro p hp
    have H := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨H.2.1.pos, Nat.le_of_lt_succ (mem_range.mp H.1)⟩, H.2.1⟩
  calc
    _ ≤ ∑ p ∈ P, |log p| := primeSum_norm_le293 ε X α
    _ = ∑ p ∈ P, log p := by
      apply sum_congr rfl
      intro p hp
      exact abs_of_nonneg (log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.1.one_lt.le))
    _ ≤ ∑ p ∈ Q, log p := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro p hp hp'
      exact log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_lt.le)
    _ = Chebyshev.theta X := rfl
    _ ≤ _ := Chebyshev.theta_le_log4_mul_x hX

end LeanLab.LZPowersOfTwo
