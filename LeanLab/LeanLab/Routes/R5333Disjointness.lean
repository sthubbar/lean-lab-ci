/-
R-5333, CLOUD MANUAL-M3, unit U-7003, T3 MOONSHOT.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.

The communication complexity route.  Binary Goldbach at N is set disjointness:
Alice holds A = {i ≤ N/2 prime}, Bob holds B = {i ≤ N/2 : N - i prime}, and
N is a sum of two primes iff A ∩ B ≠ ∅.
* `goldbach_iff_half`: the reduction, with the smaller prime at most N/2.
* `ams_unbiased`: the random sign sketch is unbiased; summed over all sign vectors
  s, (Σ σ(sᵢ) aᵢ)(Σ σ(sᵢ) bᵢ) is 2ⁿ Σ aᵢ bᵢ.  So k shared random sketches decide
  any fixed N once k exceeds a constant times |A||B|/r², about log² N.
* `sample_miss`: (1 - x)^k ≤ exp(-k x), the gap promise sampling bound.
* `rep_card`: repeating each coordinate r times multiplies the intersection by r,
  the reduction that turns a disjointness lower bound into one for the gap
  problem.
* `swap_count`: replacing i by j with i ≡ j mod Q keeps every residue count mod
  every d ∣ Q, the swap decoy that fools every explicit residue sketch of level D
  with lcm(1..D) small, numerics/r5333_disjointness.py.
-/
import Mathlib

namespace LeanLab.Routes.R5333

open Finset

theorem goldbach_iff_half (N : ℕ) :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N) ↔
      ∃ i, 2 * i ≤ N ∧ i.Prime ∧ (N - i).Prime := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq⟩
    rcases le_total p q with h | h
    · exact ⟨p, by omega, hp, by rwa [show N - p = q by omega]⟩
    · exact ⟨q, by omega, hq, by rwa [show N - q = p by omega]⟩
  · rintro ⟨i, hi, hp, hq⟩
    exact ⟨i, N - i, hp, hq, by omega⟩

/-- The sign of a bit. -/
def sgn (b : Bool) : ℤ := if b then 1 else -1

lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp [sgn]

lemma sum_sgn_mul {n : ℕ} (i j : Fin n) :
    ∑ s : Fin n → Bool, sgn (s i) * sgn (s j) = if i = j then 2 ^ n else 0 := by
  split_ifs with hij
  · subst hij
    simp [sgn_mul_self, Finset.card_univ, Fintype.card_bool]
  · refine Finset.sum_involution (fun s _ => Function.update s i (!s i)) ?_ ?_ ?_ ?_
    · intro s _
      have hj : Function.update s i (!s i) j = s j := Function.update_of_ne (Ne.symm hij) _ _
      rw [Function.update_self, hj]
      cases s i <;> simp [sgn] <;> split_ifs <;> norm_num
    · intro s _ _ h
      have := congrFun h i
      rw [Function.update_self] at this
      cases hs : s i <;> simp [hs] at this
    · intro s _; exact Finset.mem_univ _
    · intro s _
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Function.update_of_ne hk]

/-- The AMS sketch is unbiased: the sum over all 2ⁿ sign vectors of the product of
the two sketches is 2ⁿ times the inner product. -/
theorem ams_unbiased {n : ℕ} (a b : Fin n → ℤ) :
    ∑ s : Fin n → Bool, (∑ i, sgn (s i) * a i) * (∑ j, sgn (s j) * b j) =
      2 ^ n * ∑ i, a i * b i := by
  calc ∑ s : Fin n → Bool, (∑ i, sgn (s i) * a i) * (∑ j, sgn (s j) * b j)
      = ∑ s : Fin n → Bool, ∑ i, ∑ j, (sgn (s i) * sgn (s j)) * (a i * b j) := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
    _ = ∑ i, ∑ j, ∑ s : Fin n → Bool, (sgn (s i) * sgn (s j)) * (a i * b j) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ i, ∑ j, (if i = j then (2 : ℤ) ^ n else 0) * (a i * b j) := by
        simp_rw [← Finset.sum_mul, sum_sgn_mul]
    _ = 2 ^ n * ∑ i, a i * b i := by
        simp [Finset.mul_sum]

/-- Gap promise sampling: k independent samples that each hit with probability x
all miss with probability at most exp(-k x). -/
theorem sample_miss {x : ℝ} (_h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    (1 - x) ^ k ≤ Real.exp (-(k * x)) := by
  have hb : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x); linarith
  calc (1 - x) ^ k ≤ Real.exp (-x) ^ k :=
        pow_le_pow_left₀ (by linarith) hb k
    _ = Real.exp (-(k * x)) := by rw [← Real.exp_nat_mul]; ring_nf

/-- Repeating each coordinate r times multiplies the size of the intersection by r. -/
theorem rep_card {m r : ℕ} (a b : Fin m → Bool) :
    (univ.filter (fun ij : Fin m × Fin r => a ij.1 && b ij.1)).card =
      (univ.filter (fun i : Fin m => a i && b i)).card * r := by
  have : univ.filter (fun ij : Fin m × Fin r => a ij.1 && b ij.1) =
      (univ.filter (fun i : Fin m => a i && b i)) ×ˢ (univ : Finset (Fin r)) := by
    ext ⟨i, j⟩; simp
  rw [this, Finset.card_product, Finset.card_univ, Fintype.card_fin]

/-- A swap within one class mod Q keeps every residue count mod every d ∣ Q. -/
theorem swap_count {S : Finset ℕ} {i j Q d c : ℕ} (hi : i ∈ S) (hj : j ∉ S)
    (hij : i % Q = j % Q) (hd : d ∣ Q) :
    ((insert j (S.erase i)).filter (· % d = c)).card = (S.filter (· % d = c)).card := by
  have hmod : i % d = j % d := by
    rw [← Nat.mod_mod_of_dvd i hd, ← Nat.mod_mod_of_dvd j hd, hij]
  have hj' : j ∉ S.erase i := fun h => hj (Finset.mem_of_mem_erase h)
  rw [Finset.filter_insert]
  by_cases hc : j % d = c
  · rw [if_pos hc, Finset.card_insert_of_notMem (fun h => hj' (Finset.mem_of_mem_filter _ h)),
      Finset.filter_erase, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hi, by omega⟩)]
    have : 0 < (S.filter (· % d = c)).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, by omega⟩⟩
    omega
  · rw [if_neg hc, Finset.filter_erase, Finset.erase_eq_of_notMem]
    simp only [Finset.mem_filter, not_and]
    intro _ h; exact hc (by omega)

end LeanLab.Routes.R5333

#print axioms LeanLab.Routes.R5333.goldbach_iff_half
#print axioms LeanLab.Routes.R5333.sum_sgn_mul
#print axioms LeanLab.Routes.R5333.ams_unbiased
#print axioms LeanLab.Routes.R5333.sample_miss
#print axioms LeanLab.Routes.R5333.rep_card
#print axioms LeanLab.Routes.R5333.swap_count
