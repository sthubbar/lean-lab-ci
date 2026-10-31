/-
Li and Liu, https://arxiv.org/pdf/2610.15784, page 6, Euler coefficient in Proposition 3.2.
The finite local factor cancellation, before passage to infinite products.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik.Task37Gram

namespace LeanLab.Linnik.Task37EulerFinite
open Finset
open LeanLab.Linnik.U1464Display20

noncomputable def localC (p : ℕ) : ℝ := 1 - 1 / ((p : ℝ) - 1) ^ 2
noncomputable def localF (p : ℕ) : ℝ := 1 / ((p : ℝ) * ((p : ℝ) - 2))

lemma absent_factor {p : ℕ} (hp : 3 ≤ p) : localC p * (1 + localF p) = 1 := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : (p : ℝ) ≠ 0 := by linarith
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
  unfold localC localF
  field_simp [h0, h1, h2]
  ring

lemma present_factor {p : ℕ} (hp : 3 ≤ p) : localC p * localF p = 1 / ((p : ℝ) - 1) ^ 2 := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : (p : ℝ) ≠ 0 := by linarith
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
  unfold localC localF
  field_simp [h0, h1, h2]
  ring

lemma wt_div_eq_prod {d : ℕ} (hd : Odd d) (hs : Squarefree d) :
    wt d / (d : ℝ) = ∏ p ∈ d.primeFactors, localF p := by
  have he : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    simpa only [Nat.cast_prod] using
      congrArg (fun n : ℕ => (n : ℝ)) (Nat.prod_primeFactors_of_squarefree hs).symm
  rw [wt, ite_eq_left ⟨hd, hs⟩, he, ← Finset.prod_div_distrib]
  refine prod_congr rfl fun p _ => ?_
  simp only [localF, div_div, mul_comm]

lemma totient_sqf {d : ℕ} (hd : Squarefree d) :
    (Nat.totient d : ℝ) = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors d
  rw [Nat.prod_primeFactors_of_squarefree hd] at h
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have h2 : d.totient = ∏ p ∈ d.primeFactors, (p - 1) := by
    rw [mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left hd0 h
  rw [h2, Nat.cast_prod]
  refine prod_congr rfl fun p hp => ?_
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]
  simp

/-- The factored finite divisor coefficient has exactly the totient square normalization. -/
theorem finite_coefficient (S T : Finset ℕ) (hT : T ⊆ S)
    (hS : ∀ p ∈ S, p.Prime ∧ 2 < p) :
    (∏ p ∈ S, localC p) * (∏ p ∈ T, localF p) *
      (∏ p ∈ S \ T, (1 + localF p)) = 1 / ((∏ p ∈ T, p).totient : ℝ) ^ 2 := by
  have hpr : ∀ p ∈ T, p.Prime := fun p hp => (hS p (hT hp)).1
  have he : (∏ p ∈ S \ T, localC p * (1 + localF p)) = 1 := by
    apply prod_eq_one
    intro p hp
    exact absent_factor (by have := (hS p (mem_sdiff.mp hp).1).2; omega)
  calc
    _ = (∏ p ∈ T, localC p * localF p) *
        (∏ p ∈ S \ T, localC p * (1 + localF p)) := by
      rw [prod_mul_distrib, prod_mul_distrib, ← Finset.prod_sdiff hT]
      ring
    _ = ∏ p ∈ T, 1 / ((p : ℝ) - 1) ^ 2 := by
      rw [he, mul_one]
      refine prod_congr rfl fun p hp => present_factor ?_
      have := (hS p (hT hp)).2
      omega
    _ = _ := by
      rw [totient_sqf (sq_prod hpr), Nat.primeFactors_prod hpr]
      simp only [prod_div_distrib, prod_const_one, prod_pow]

/-- The forced prime set 3,5 gives the exact finite coefficient 1/64. -/
theorem coefficient_instance :
    (∏ p ∈ ({3, 5} : Finset ℕ), localC p) *
      (∏ p ∈ ({3, 5} : Finset ℕ), localF p) = 1 / 64 := by
  norm_num [localC, localF]

end LeanLab.Linnik.Task37EulerFinite

#print axioms LeanLab.Linnik.Task37EulerFinite.absent_factor
#print axioms LeanLab.Linnik.Task37EulerFinite.present_factor
#print axioms LeanLab.Linnik.Task37EulerFinite.wt_div_eq_prod
#print axioms LeanLab.Linnik.Task37EulerFinite.totient_sqf
#print axioms LeanLab.Linnik.Task37EulerFinite.finite_coefficient
#print axioms LeanLab.Linnik.Task37EulerFinite.coefficient_instance
