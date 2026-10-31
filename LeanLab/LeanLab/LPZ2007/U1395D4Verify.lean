/-
U-1395, PC run 20261021T1003Z-20044, independent VERIFY of CLOUD cloud56 U-6835 D4Count,
P0045 Languasco Pintz Zaccagnini 2007 p.8 displays (17) to (20).
AI-written Lean code, Claude, 2026-10-21. Binary Goldbach is OPEN.
-/
import LeanLab.LPZ2007.D4Count

namespace LeanLab.LPZ2007.U1395

open Finset LeanLab.LPZ2007 LeanLab.LPZ2007.D4Count

/-- Vacuity and sanity: d = 3, ξ(3) = 2, k = 2, M = 4, N = 1. Both bounds of `count_jd_bounds`
are checked by evaluation: j(3,2,1) and the count on [1,4]^2. A first hand count, 2 and 8,
was wrong and was refuted by decide; the values below are the kernel's. -/
theorem xi_three : xi 3 = 2 := by
  unfold xi
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hm0
  interval_cases m
  decide

theorem jd_3_2_1 : jd 3 2 1 = 1 := by
  unfold jd; rw [xi_three]; decide

theorem cnt_3_2_4 : cnt 3 2 4 (1 : ZMod 3) = 4 := by
  unfold cnt; decide

/-- The instance: q = ⌊4/2⌋ = 2, j(3,2,1) = 1 from 2^1 + 2^1 = 4, the count on [1,4]^2 is 4,
both exponents odd, so 2^2 · 1 ≤ 4 ≤ 3^2 · 1, the lower bound tight. -/
theorem instance_3_2_4 :
    (4 / xi 3) ^ 2 * jd 3 2 1 ≤ cnt 3 2 4 ((1 : ℕ) : ZMod 3) ∧
      cnt 3 2 4 ((1 : ℕ) : ZMod 3) ≤ (4 / xi 3 + 1) ^ 2 * jd 3 2 1 :=
  count_jd_bounds (by decide) 4 2 1

theorem instance_values : (4 / xi 3) ^ 2 * jd 3 2 1 = 4 ∧ (4 / xi 3 + 1) ^ 2 * jd 3 2 1 = 9 := by
  rw [xi_three, jd_3_2_1]; norm_num

end LeanLab.LPZ2007.U1395

#print axioms LeanLab.LPZ2007.D4Count.sum_Icc_mul
#print axioms LeanLab.LPZ2007.D4Count.sum_Icc_periodic
#print axioms LeanLab.LPZ2007.D4Count.cnt_succ
#print axioms LeanLab.LPZ2007.D4Count.cnt_bounds
#print axioms LeanLab.LPZ2007.D4Count.xi_spec
#print axioms LeanLab.LPZ2007.D4Count.jd_eq_cnt
#print axioms LeanLab.LPZ2007.D4Count.count_jd_bounds
#print axioms LeanLab.LPZ2007.D4Count.D4count_eq_cnt
#print axioms LeanLab.LPZ2007.D4Count.D4count_bounds
#print axioms LeanLab.LPZ2007.U1395.instance_3_2_4
#print axioms LeanLab.LPZ2007.U1395.instance_values
#print axioms LeanLab.LPZ2007.U1395.cnt_3_2_4
