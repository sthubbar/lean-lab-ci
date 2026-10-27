/-
Aristotle trial 6, lean-aristotle 2026-10-27. Target from MOUNTAIN.md, folder Tao2012, file
Decomp1555b.lean, OPEN leaf `count_multiples`, Tao 2012 eq. 4.17: the count of h in [1, H]
with 2n | h - h' is at most H/(2n) + 1.
Statement copied character for character from Decomp1555b.lean on main, unchanged; own
namespace only. Proof written by Aristotle, Harmonic, project
51075858-dd16-46d5-9cca-5ab7eac6ae4b, on Lean 4.28; checked by lean-aristotle on Lean and
Mathlib 4.35 standalone: builds, axioms propext, Classical.choice, Quot.sound only, no banned
token. This repo file itself is NOT yet built in the lane: the lean-refresh merge rebuild is
the trusted check. AI wrote the Lean code.
-/
import Mathlib

open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

namespace LeanLab.Tao2012.AristotleTrial06

theorem count_multiples (H h' : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (((Icc 1 H).filter fun h : ℕ => (2 * (n : ℤ)) ∣ (h : ℤ) - h').card : ℝ) ≤
      H / (2 * n) + 1 := by
  set m := 2 * n with hm
  have hm0 : 0 < m := by omega
  have hcard : ((Icc 1 H).filter fun h : ℕ => (2 * (n : ℤ)) ∣ (h : ℤ) - h').card ≤
      (range ((H - 1) / m + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun h => (h - 1) / m)
    · intro x hx
      simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hx
      simp only [coe_range, Set.mem_Iio]
      have : (x - 1) / m ≤ (H - 1) / m := Nat.div_le_div_right (by omega)
      omega
    · intro x hx y hy hxy
      simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hx hy
      simp only at hxy
      have hd : (m : ℤ) ∣ ((y - 1 : ℕ) : ℤ) - ((x - 1 : ℕ) : ℤ) := by
        have h1 := hx.2
        have h2 := hy.2
        have e : ((y - 1 : ℕ) : ℤ) - ((x - 1 : ℕ) : ℤ) = ((y : ℤ) - h') - ((x : ℤ) - h') := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ x), Nat.cast_sub (by omega : 1 ≤ y)]
          ring
        rw [e]
        push_cast [hm]
        exact dvd_sub h2 h1
      have hmod : (x - 1) % m = (y - 1) % m := (Nat.modEq_iff_dvd).mpr hd
      have : x - 1 = y - 1 := by rw [← Nat.div_add_mod (x - 1) m, ← Nat.div_add_mod (y - 1) m, hxy, hmod]
      omega
  rw [card_range] at hcard
  have h1 : (((H - 1) / m : ℕ) : ℝ) ≤ (H : ℝ) / (2 * n) := by
    calc (((H - 1) / m : ℕ) : ℝ) ≤ ((H - 1 : ℕ) : ℝ) / (m : ℝ) := Nat.cast_div_le
      _ ≤ (H : ℝ) / (m : ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact_mod_cast Nat.sub_le H 1
      _ = (H : ℝ) / (2 * n) := by rw [hm]; push_cast; ring
  calc _ ≤ (((H - 1) / m + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ _ := by push_cast; linarith

end LeanLab.Tao2012.AristotleTrial06
