/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1404.5669v2 pages 2 and 3, the C3 sum and H definition.
-/
import LeanLab.PlattTrudgian2014.LiuLu

namespace LeanLab.PlattTrudgian2014.Section2

open Finset

/-- A uniform normalized lower bound for H propagates to every larger K. -/
theorem H_lower_extend (d e k A B n : ℕ)
    (hbase : ∀ a : ZMod d, A * e ^ k ≤ B * H d e k a) (a : ZMod d) :
    A * e ^ (k + n) ≤ B * H d e (k + n) a := by
  induction n generalizing a with
  | zero => simpa using hbase a
  | succ n ih =>
    rw [show k + (n + 1) = (k + n) + 1 by omega, H_succ, Finset.mul_sum]
    calc
      A * e ^ (k + n + 1) = ∑ j : Fin e, A * e ^ (k + n) := by
        simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]
      _ ≤ ∑ j : Fin e, B * H d e (k + n) (a - 2 ^ ((j : ℕ) + 1)) :=
        sum_le_sum fun j _ => ih _

theorem eps_7 : orderOf (2 : ZMod 7) = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem H7_K6_lower (a : ZMod 7) : 101 ≤ H 7 3 6 a := by
  fin_cases a <;> decide

theorem H7_ratio_lower (K : ℕ) (hK : 6 ≤ K) (a : ZMod 7) :
    (101 / 729 : ℝ) ≤ (H 7 3 K a : ℝ) / 3 ^ K := by
  have hb : ∀ a : ZMod 7, 101 * 3 ^ 6 ≤ 729 * H 7 3 6 a := by
    intro a
    have h := H7_K6_lower a
    omega
  have h := H_lower_extend 7 3 6 101 729 (K - 6) hb a
  rw [Nat.add_sub_of_le hK] at h
  have hr : (101 : ℝ) * 3 ^ K ≤ 729 * H 7 3 K a := by exact_mod_cast h
  rw [le_div_iff₀ (by positivity)]
  linarith

noncomputable def C3sum11Full (K : ℕ) (a : ZMod 3) (b : ZMod 5) (u : ZMod 7)
    (c : ZMod 11) : ℝ :=
  C3sum11 K a b c + 2 / 5 * ((H 7 3 K u : ℝ) / 3 ^ K)

theorem C3_D11_full_lower (K : ℕ) (hK : 6 ≤ K) (a : ZMod 3) (b : ZMod 5)
    (u : ZMod 7) (c : ZMod 11) : 2.8650 ≤ C3sum11Full K a b u c := by
  have h11 := liuLu_C3_D11 K hK a b c
  have h7 := H7_ratio_lower K hK u
  unfold C3sum11Full
  linarith

#print axioms H_lower_extend

#print axioms eps_7

#print axioms H7_K6_lower

#print axioms H7_ratio_lower

#print axioms C3_D11_full_lower

end LeanLab.PlattTrudgian2014.Section2
