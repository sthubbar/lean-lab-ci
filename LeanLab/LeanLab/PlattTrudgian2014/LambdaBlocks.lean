/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv math/0201299 pages 29 to 30, displays 42 and 43.
These identities prepare larger block certificates for the open lambda targets.
-/
import LeanLab.PlattTrudgian2014.LambdaMoment

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Complex Finset

theorem G_add_length (L h : ℕ) (x : ℝ) :
    G (L + h) x = G h x + G L ((2 : ℝ) ^ h * x) := by
  rw [Nat.add_comm L h]
  simp only [G_eq_sum_phase, sum_range_add]
  congr 1
  apply sum_congr rfl
  intro j _
  congr 1
  rw [pow_add]
  ring

theorem G_add_nat (L : ℕ) (x : ℝ) (n : ℕ) : G L (x + n) = G L x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, G_add_one, ih]

theorem G_inverse_branch (L h r : ℕ) (β : ℝ) :
    G (L + h) ((β + r) / (2 : ℝ) ^ h) =
      G h ((β + r) / (2 : ℝ) ^ h) + G L β := by
  rw [G_add_length]
  have he : (2 : ℝ) ^ h * ((β + r) / (2 : ℝ) ^ h) = β + r := by field_simp
  rw [he, G_add_nat]

theorem moment_inverse_branch (L h r : ℕ) (β t : ℝ) (ρ : ℂ) :
    momentIntegrand (L + h) t ρ ((β + r) / (2 : ℝ) ^ h) =
      momentIntegrand L t ρ β * momentIntegrand h t ρ ((β + r) / (2 : ℝ) ^ h) := by
  simp only [momentIntegrand, G_inverse_branch, mul_add, Complex.add_re, Real.exp_add]
  ring

theorem integral_branches {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..1, f x) =
      1 / (n : ℝ) * ∫ β in (0 : ℝ)..1, ∑ r ∈ range n, f ((β + r) / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := f)
    (a := fun r : ℕ => (r : ℝ) / n) (n := n)
    (fun k hk => hf.intervalIntegrable _ _)
  simp only [Nat.cast_zero, zero_div, div_self hn0] at hsum
  have hbranch (r : ℕ) : (∫ β in (0 : ℝ)..1, f ((β + r) / n)) =
      (n : ℝ) * ∫ x in (r : ℝ) / n..((r : ℝ) + 1) / n, f x := by
    simp_rw [add_div]
    rw [intervalIntegral.integral_comp_div_add f hn0]
    simp only [zero_div, zero_add, smul_eq_mul]
    congr 1
    congr 1 <;> ring
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [hbranch]
    rw [← Finset.mul_sum]
    rw [show (∑ r ∈ range n, ∫ x in (r : ℝ) / n..((r : ℝ) + 1) / n, f x) =
      ∫ x in (0 : ℝ)..1, f x by simpa only [Nat.cast_add, Nat.cast_one] using hsum]
    field_simp
  · intro r hr
    exact (hf.comp (by fun_prop)).intervalIntegrable _ _

#print axioms G_add_length
#print axioms G_add_nat
#print axioms G_inverse_branch
#print axioms moment_inverse_branch
#print axioms integral_branches

end LeanLab.PlattTrudgian2014
