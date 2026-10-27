/- AI-written Lean code by OpenAI Codex, task113, 2026-10-26. Binary Goldbach is open. -/
import Mathlib
namespace LeanLab.Tchudakov1938.Decomp113b
open Finset Real
/-- LEAF. P0064, page 27, finite product step in Lemma 1.
A finite set of distinct integers at least two has reciprocal Euler product at most its size plus one. -/
theorem prod_reciprocal_le_card (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p) :
    (∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1)) ≤ s.card + 1 := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have ha : 2 ≤ a := hs a (mem_insert_self a s)
    have hs' : ∀ p ∈ s, 2 ≤ p := fun p hp => hs p (mem_insert_of_mem hp)
    have hnot : a ∉ s := fun h => (hmax a h).false
    have hcard : s.card ≤ a - 2 := by
      calc s.card ≤ (Ico 2 a).card := card_le_card (fun p hp => mem_Ico.mpr ⟨hs' p hp, hmax p hp⟩)
           _ = a - 2 := by simp
    have hacard : (s.card : ℝ) + 2 ≤ a := by exact_mod_cast (by omega : s.card + 2 ≤ a)
    have haR : 0 < (a : ℝ) - 1 := by
      have : (2 : ℝ) ≤ a := by exact_mod_cast ha
      linarith
    rw [prod_insert hnot, card_insert_of_notMem hnot, Nat.cast_add, Nat.cast_one]
    calc (a : ℝ) / (a - 1) * (∏ p ∈ s, (p : ℝ) / (p - 1))
        ≤ (a : ℝ) / (a - 1) * (s.card + 1) :=
          mul_le_mul_of_nonneg_left (ih hs') (by positivity)
      _ ≤ s.card + 1 + 1 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ haR]
        nlinarith

/-- LEAF. P0064, page 27, Euler totient product in Lemma 1.
The number of distinct prime factors gives a finite bound. -/
theorem totient_card (n : ℕ) :
    (n : ℝ) ≤ n.totient * ((n.primeFactors.card : ℝ) + 1) := by
  have hp (p : ℕ) (h : p ∈ n.primeFactors) : 2 ≤ p := (Nat.prime_of_mem_primeFactors h).two_le
  have hd : (∏ p ∈ n.primeFactors, ((p : ℝ) - 1)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p h
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp p h
    linarith
  have hcast : (n.totient : ℝ) * (∏ p ∈ n.primeFactors, (p : ℝ)) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    have H := congrArg (fun x : ℕ => (x : ℝ)) (Nat.totient_mul_prod_primeFactors n)
    push_cast at H
    convert H using 1
    congr 1
    apply Finset.prod_congr rfl
    intro p h
    rw [Nat.cast_sub (by have := hp p h; omega), Nat.cast_one]
  have heq : (n.totient : ℝ) * (∏ p ∈ n.primeFactors, (p : ℝ) / (p - 1)) = n := by
    rw [Finset.prod_div_distrib, ← mul_div_assoc]
    exact (div_eq_iff hd).mpr hcast
  rw [← heq]
  exact mul_le_mul_of_nonneg_left (prod_reciprocal_le_card _ hp) (by positivity)

/-- LEAF. P0064, page 27, elementary logarithmic control of the finite product.
The product of the distinct prime factors is at least two to their count and divides n. -/
theorem card_log (n : ℕ) (hn : n ≠ 0) :
    (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log n := by
  have hp (p : ℕ) (h : p ∈ n.primeFactors) : 2 ≤ p := (Nat.prime_of_mem_primeFactors h).two_le
  have h2 : 2 ^ n.primeFactors.card ≤ n := by
    calc 2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by simp
         _ ≤ ∏ p ∈ n.primeFactors, p := Finset.prod_le_prod hp
         _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
  rw [← Real.log_pow]
  apply Real.log_le_log (by positivity)
  exact_mod_cast h2

/-- LEAF. P0064, page 27, Lemma 1 for q at least two, with an explicit constant. -/
theorem totient_log_lower (n : ℕ) (hn : 2 ≤ n) :
    (Real.log 2 / 2) * n ≤ n.totient * Real.log n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hc := card_log n (by omega)
  have hc' : ((n.primeFactors.card : ℝ) + 1) * Real.log 2 ≤ 2 * Real.log n := by
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right (totient_card n) hlog2.le
  have h2 := mul_le_mul_of_nonneg_left hc' (show (0 : ℝ) ≤ n.totient by positivity)
  nlinarith

/-- CITED. P0064, Lemma 1, page 27, with the explicit endpoint convention q at least two.
The printed display itself does not give this convention. -/
def lemma1FromTwo : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, 2 ≤ q → c * q ≤ q.totient * Real.log q

/-- P0064, Lemma 1, page 27, assembled with c equal to log 2 divided by 2.
The theorem has exactly the cited proposition as its type. -/
theorem lemma1 : lemma1FromTwo := by
  exact ⟨Real.log 2 / 2, by positivity, totient_log_lower⟩

/-- P0064, page 27, endpoint audit. The literal formula fails at q equal to one.
This does not assert a failure of the paper's asymptotic use. -/
theorem lemma1_at_one_fails (c : ℝ) (hc : 0 < c) :
    ¬ c * (1 : ℕ) ≤ ((1 : ℕ).totient : ℝ) * Real.log (1 : ℕ) := by
  simpa using hc.not_ge

end LeanLab.Tchudakov1938.Decomp113b
