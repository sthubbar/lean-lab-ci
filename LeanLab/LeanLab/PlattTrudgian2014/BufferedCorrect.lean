/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1404.5669v2 page 4 Algorithm 1, corrected as recorded in AuthorFix.
Each step reads the vector held at its start and includes the exponent e.
-/
import LeanLab.PlattTrudgian2014.AuthorFix

namespace LeanLab.PlattTrudgian2014.Section2

open Finset

theorem sum_list_range' (f : ℕ → ℕ) (s n : ℕ) :
    ((List.range' s n).map f).sum = ∑ j : Fin n, f (s + j) := by
  rw [← List.sum_toFinset f (List.nodup_range'), List.toFinset_range'_1,
    Finset.sum_Ico_eq_sum_range]
  simpa only [Nat.add_sub_cancel_left] using
    (Fin.sum_univ_eq_sum_range (fun j => f (s + j)) n).symm

theorem cast_two_pow_sub_two (d j : ℕ) (hj : 1 ≤ j) :
    ((2 ^ j - 2 : ℕ) : ZMod d) = (2 : ZMod d) ^ j - 2 := by
  have hp : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
         _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  rw [Nat.cast_sub hp]
  simp

def bufferedStep (d e : ℕ) (W : ZMod d → ℕ) : ZMod d → ℕ := fun a =>
  W a + ((List.range' 2 (e - 1)).map fun j => W (a - ((2 ^ j - 2 : ℕ) : ZMod d))).sum

theorem bufferedStep_eq_sum (d e : ℕ) (he : 1 ≤ e) (W : ZMod d → ℕ) (a : ZMod d) :
    bufferedStep d e W a = ∑ j : Fin e, W (a - ((2 : ZMod d) ^ ((j : ℕ) + 1) - 2)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
  rw [bufferedStep, sum_list_range']
  simp only [Nat.succ_sub_one]
  rw [Fin.sum_univ_eq_sum_range (fun j => W (a - ((2 : ZMod d) ^ (j + 1) - 2))) (n + 1),
    Finset.sum_range_succ']
  simp only [Nat.zero_add, pow_one, sub_self, sub_zero]
  rw [add_comm]
  apply congrArg (fun z => z + W a)
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => W (a - ((2 ^ (2 + j) - 2 : ℕ) : ZMod d))) n]
  apply Finset.sum_congr rfl
  intro j hj
  rw [cast_two_pow_sub_two d _ (by omega)]
  rw [show 2 + j = j + 1 + 1 by omega]

theorem bufferedStep_H_shift (d e k : ℕ) (he : 1 ≤ e) (s : ZMod d) :
    bufferedStep d e (fun a => H d e k (a - s)) =
      fun a => H d e (k + 1) (a - s + 2) := by
  funext a
  rw [bufferedStep_eq_sum d e he, H_succ]
  apply sum_congr rfl
  intro j _
  congr 1
  ring

theorem bufferedStep_iterate (d e : ℕ) (he : 1 ≤ e) (n : ℕ) (s : ZMod d) :
    (bufferedStep d e)^[n] (fun a => H d e 1 (a - s)) =
      fun a => H d e (n + 1) (a - s + 2 * (n : ZMod d)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    have hf : (fun a => H d e (n + 1) (a - s + 2 * (n : ZMod d))) =
        (fun a => H d e (n + 1) (a - (s - 2 * (n : ZMod d)))) := by
      funext a
      congr 1
      ring
    rw [hf, bufferedStep_H_shift d e (n + 1) he]
    funext a
    congr 1
    push_cast
    ring

theorem buffered_initial (d e K : ℕ) :
    (fun a : ZMod d =>
      ((Icc 1 e).filter fun ν => ((2 * (K - 1) + 2 ^ ν : ℕ) : ZMod d) = a).card) =
      fun a => H d e 1 (a - ((2 * (K - 1) : ℕ) : ZMod d)) := by
  funext a
  rw [card_filter, ← List.toFinset_range'_1_1 e,
    List.sum_toFinset _ (List.nodup_range'), sum_list_range']
  rw [show (1 : ℕ) = 0 + 1 by rfl, H_succ]
  simp only [H_zero, sub_eq_zero]
  apply sum_congr rfl
  intro j _
  congr 1
  apply propext
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
    show 1 + (j : ℕ) = (j : ℕ) + 1 by omega, sub_eq_iff_eq_add]
  constructor <;> intro h
  · rw [← h]; ring
  · rw [h]; ring

theorem alg1WBuffered_correct (d e K : ℕ) (he : 1 ≤ e) (hK : 1 ≤ K) :
    alg1WBuffered d e K = H d e K := by
  change (List.range (K - 1)).foldl (fun W _ => bufferedStep d e W)
    (fun a : ZMod d =>
      ((Icc 1 e).filter fun ν => ((2 * (K - 1) + 2 ^ ν : ℕ) : ZMod d) = a).card) = _
  rw [List.foldl_const, List.length_range, buffered_initial, bufferedStep_iterate d e he]
  rw [show K - 1 + 1 = K by omega]
  funext a
  congr 1
  push_cast
  ring

theorem alg1WBuffered_min_correct (d e K : ℕ) [NeZero d] (he : 1 ≤ e) (hK : 1 ≤ K) :
    univ.inf' univ_nonempty (alg1WBuffered d e K) = univ.inf' univ_nonempty (H d e K) := by
  rw [alg1WBuffered_correct d e K he hK]

#print axioms sum_list_range'
#print axioms cast_two_pow_sub_two
#print axioms bufferedStep_eq_sum

#print axioms bufferedStep_H_shift

#print axioms bufferedStep_iterate

#print axioms buffered_initial

#print axioms alg1WBuffered_correct

#print axioms alg1WBuffered_min_correct

end LeanLab.PlattTrudgian2014.Section2
