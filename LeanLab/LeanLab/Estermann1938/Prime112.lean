import LeanLab.Estermann1938.Decomp112
import LeanLab.ExceptionalSet.Statements

/-!
Estermann 1938, P0091, pages 308 and 313, displays 4 and 46.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Estermann1938.Prime112
open scoped BigOperators
open Decomp112

/-- The primes at most n in display 4, page 308. -/
def primes (n : ℕ) : Finset ℕ := (Finset.Icc 2 n).filter Nat.Prime

/-- Estermann's prime exponential sum f, display 4, page 308. -/
noncomputable def f (n : ℕ) (x : ℝ) : ℂ := ∑ p ∈ primes n, phase x p

/-- The ordered representation count a in display 46, page 313. -/
def a (n m : ℕ) : ℕ :=
  (((primes n).product (primes n)).filter (fun p : ℕ × ℕ => p.1 + p.2 = m)).card

/-- The finite Fourier identity in display 46, page 313. -/
theorem display46 (n : ℕ) (x : ℝ) :
    f n x ^ 2 = ∑ m ∈ Finset.Icc 1 (2 * n), (a n m : ℂ) * phase x m := by
  classical
  have hmap : ∀ p ∈ (primes n).product (primes n),
      p.1 + p.2 ∈ Finset.Icc 1 (2 * n) := by
    intro p hp
    have hs := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).1
    have ht := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).1
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  calc
    f n x ^ 2 = ∑ p ∈ (primes n).product (primes n), phase x (p.1 + p.2) := by
      unfold f
      rw [pow_two, Finset.sum_mul_sum]
      simp only [Finset.product_eq_sprod, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      exact (phase_add x p q).symm
    _ = ∑ m ∈ Finset.Icc 1 (2 * n),
        ∑ p ∈ ((primes n).product (primes n)).filter
          (fun p : ℕ × ℕ => p.1 + p.2 = m), phase x m :=
      (Finset.sum_fiberwise_of_maps_to' hmap (phase x)).symm
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, a]

/-- The remark after display 46: a vanishes when m is not a sum of two primes. -/
theorem a_zero_of_not_goldbach (n m : ℕ) (hm : ¬ IsGoldbachSum m) : a n m = 0 := by
  classical
  unfold a
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hp, heq⟩ := Finset.mem_filter.mp hp
  have hs := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
  have ht := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2
  exact hm ⟨p.1, p.2, hs, ht, heq⟩

#print axioms display46
#print axioms a_zero_of_not_goldbach

end LeanLab.Estermann1938.Prime112
