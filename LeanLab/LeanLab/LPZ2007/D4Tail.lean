/-
P0045, journal pages 777 to 779, displays 20, 28 and 30.
Single exponent counts isolate the remainder in the actual divisor tail.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LPZ2007.D4Asymptotic

namespace LeanLab.LPZ2007.D4Tail

open Finset Real Filter Topology
open LeanLab.LPZ2007 LeanLab.LPZ2007.D4Count

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The number of single exponents with the required divisor. -/
def oneCount (d M m : ℕ) : ℕ := #{a ∈ Icc 1 M | d ∣ m - 2 ^ a}

/-- Exact subtraction identifies the single exponent count with the periodic count. -/
theorem oneCount_eq_cnt (d M m : ℕ) (hpow : ∀ a ∈ Icc 1 M, 2 ^ a < m) :
    oneCount d M m = cnt d 1 M (m : ZMod d) := by
  unfold oneCount
  rw [card_filter, cnt_succ]
  apply sum_congr rfl
  intro a ha
  rw [cnt_zero']
  congr 1
  apply propext
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (hpow a ha).le]
  push_cast
  exact eq_comm

/-- The additive error is paid only by moduli that actually occur. -/
theorem oneCount_bound {d : ℕ} (hd : Odd d) (M m : ℕ)
    (hpow : ∀ a ∈ Icc 1 M, 2 ^ a < m) :
    (oneCount d M m : ℝ) ≤ (M : ℝ) / xi d + if 0 < oneCount d M m then 1 else 0 := by
  by_cases hc : oneCount d M m = 0
  · simpa [hc] using (div_nonneg (Nat.cast_nonneg M) (Nat.cast_nonneg (xi d)) :
      (0 : ℝ) ≤ (M : ℝ) / xi d)
  have hc0 : 0 < oneCount d M m := by omega
  rw [ite_eq_left hc0]
  have hj : jd d 1 m ≤ 1 := by simpa using eq19 hd 0 m
  have hn : oneCount d M m ≤ M / xi d + 1 := by
    rw [oneCount_eq_cnt d M m hpow]
    have h := (count_jd_bounds hd M 1 m).2
    simp only [pow_one] at h
    exact h.trans (by simpa only [mul_one] using Nat.mul_le_mul_left (M / xi d + 1) hj)
  calc (oneCount d M m : ℝ) ≤ ((M / xi d + 1 : ℕ) : ℝ) := by exact_mod_cast hn
    _ ≤ (M : ℝ) / xi d + 1 := by
      push_cast
      linarith [Nat.cast_div_le (m := M) (n := xi d) (α := ℝ)]

end
end LeanLab.LPZ2007.D4Tail

#print axioms LeanLab.LPZ2007.D4Tail.oneCount_eq_cnt

#print axioms LeanLab.LPZ2007.D4Tail.oneCount_bound
