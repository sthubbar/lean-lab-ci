/-
AI wrote this Lean code for CODEX task372.
P0037 Section 3 page 208, the product of admissible residue counts.
This is an exact Chinese remainder calculation.
It asserts no distribution of primes or probabilistic coverage model.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp372e
import Mathlib.Data.ZMod.QuotientRing

namespace LeanLab.DtRS1998.Decomp372f

open Decomp372e

/-- P0037 Section 3 page 208, the product of factors r minus two.
For pairwise coprime positive moduli and a nonzero target in each factor,
the number of admissible simultaneous residue classes is the product
of the exact local counts. The paper applies this to distinct odd primes. -/
theorem product_admissible_card {ι : Type*} [Fintype ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] [NeZero (∏ i, m i)]
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (a : ∀ i, ZMod (m i)) (ha : ∀ i, a i ≠ 0) :
    ((Finset.univ : Finset (ZMod (∏ i, m i))).filter
      (fun x => ∀ i, (ZMod.prodEquivPi m hcop x) i ≠ 0 ∧
        a i - (ZMod.prodEquivPi m hcop x) i ≠ 0)).card =
      ∏ i, (m i - 2) := by
  classical
  let e := ZMod.prodEquivPi m hcop
  calc
    _ = (Fintype.piFinset (fun i =>
        (Finset.univ : Finset (ZMod (m i))).filter
          (fun x => x ≠ 0 ∧ a i - x ≠ 0))).card := by
      apply Finset.card_bijective e e.bijective
      intro x
      simp [Fintype.mem_piFinset, e]
    _ = ∏ i, (m i - 2) := by
      rw [Fintype.card_piFinset]
      apply Finset.prod_congr rfl
      intro i _
      exact admissible_residue_card (m i) (a i) (ha i)

/-- P0037 Section 3 page 208, the product of factors r minus one.
For pairwise coprime positive moduli, the number of simultaneous
nonzero coordinate classes equals the product of the local counts.
For the paper's prime moduli these are the coprime classes. -/
theorem product_nonzero_card {ι : Type*} [Fintype ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] [NeZero (∏ i, m i)]
    (hcop : Pairwise (fun i j => (m i).Coprime (m j))) :
    ((Finset.univ : Finset (ZMod (∏ i, m i))).filter
      (fun x => ∀ i, (ZMod.prodEquivPi m hcop x) i ≠ 0)).card =
      ∏ i, (m i - 1) := by
  classical
  let e := ZMod.prodEquivPi m hcop
  calc
    _ = (Fintype.piFinset (fun i =>
        (Finset.univ : Finset (ZMod (m i))).filter (fun x => x ≠ 0))).card := by
      apply Finset.card_bijective e e.bijective
      intro x
      simp [Fintype.mem_piFinset, e]
    _ = ∏ i, (m i - 1) := by
      rw [Fintype.card_piFinset]
      apply Finset.prod_congr rfl
      intro i _
      exact nonzero_residue_card (m i)

/-- P0037 Section 3 page 208, the denominator at R equals 15.
There are eight classes nonzero modulo both 3 and 5. -/
theorem nonzero_product_instance :
    ((Finset.univ : Finset (ZMod 15)).filter
      (fun x => (x.val : ZMod 3) ≠ 0 ∧ (x.val : ZMod 5) ≠ 0)).card = 8 := by
  decide +kernel

/-- P0037 Section 3 page 208, a concrete primorial instance.
For target one and R equals 3 times 5, three classes remain. -/
theorem product_instance :
    ((Finset.univ : Finset (ZMod 15)).filter
      (fun x => (x.val : ZMod 3) ≠ 0 ∧ 1 - (x.val : ZMod 3) ≠ 0 ∧
        (x.val : ZMod 5) ≠ 0 ∧ 1 - (x.val : ZMod 5) ≠ 0)).card = 3 := by
  decide +kernel

#print axioms product_nonzero_card
#print axioms nonzero_product_instance
#print axioms product_admissible_card
#print axioms product_instance

end LeanLab.DtRS1998.Decomp372f
