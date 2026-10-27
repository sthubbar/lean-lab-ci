/-
P0076 Theorem 1.5, pages 3 to 4. Semilinear weights and the cited exponential sum input.
The analytic theorem is a predicate. The elementary weight properties are proved.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.BohrFourier

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- The support sets in Theorem 1.5, with upper = true selecting the upper weights.
D is the level N to the power rho. -/
def SemilinearSupport (upper : Bool) (D z : ℝ) (d : ℕ) : Prop :=
  (d : ℝ) ≤ D ∧ ∃ ps : List ℕ,
    ps.prod = d ∧ ps.Pairwise (fun p q => q < p) ∧
    (∀ p ∈ ps, p.Prime ∧ (p : ℝ) ≤ z) ∧
    ∀ k : ℕ, 1 ≤ k → ∀ hk : (if upper then 2 * k - 1 else 2 * k) ≤ ps.length,
      (((ps.take (if upper then 2 * k - 2 else 2 * k - 1)).prod : ℕ) : ℝ) *
        ((ps.getD (if upper then 2 * k - 2 else 2 * k - 1) 1 : ℕ) : ℝ) ^ 2 ≤ D

/-- The Moebius function restricted to the printed semilinear support. -/
noncomputable def semilinearWeight (upper : Bool) (D z : ℝ) (d : ℕ) : ℝ :=
  if SemilinearSupport upper D z d then (ArithmeticFunction.moebius d : ℝ) else 0

/-- The finite exponential sum over a residue class in a doubling interval. -/
noncomputable def primeResidueSum (N d : ℕ) (b : ℤ) (α : ℝ) : ℂ :=
  ∑ n ∈ (Ico N (2 * N)).filter (fun n : ℕ => (n : ℤ) ≡ b [ZMOD (d : ℤ)]),
    (ArithmeticFunction.vonMangoldt n : ℂ) * eC (α * n)

/-- The absolute weighted sum appearing in Theorem 1.5. -/
noncomputable def semilinearBVSum (upper : Bool) (N : ℕ) (D z : ℝ) (b : ℤ) (α : ℝ) : ℝ :=
  ∑ d ∈ (range (⌊D⌋₊ + 1)).filter (fun d : ℕ => IsCoprime (d : ℤ) b),
    |semilinearWeight upper D z d| * ‖primeResidueSum N d b α‖

/-- A fixed b reading of Theorem 1.5 for either sign.
This cited analytic predicate makes no claim of uniform constants in b. -/
def SemilinearBVFixedB (upper : Bool) : Prop :=
  ∀ ε C : ℝ, 0 < ε → 10 ≤ C → ∀ b : ℤ, b ≠ 0 → ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ,
    max 2 N₀ ≤ N → ∀ z : ℝ, 0 < z →
    z ≤ (N : ℝ) ^ (if upper then (1 : ℝ) / 2 else 1 / 3 - ε) →
    ∀ α : ℝ, ∀ a : ℤ, ∀ q : ℕ, 0 < q → IsCoprime a (q : ℤ) →
    |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 →
    (Real.log N) ^ (1000 * C) ≤ q → (q : ℝ) ≤ N * (Real.log N) ^ (-(1000 * C)) →
    semilinearBVSum upper N ((N : ℝ) ^ ((if upper then (2 : ℝ) / 5 else 3 / 7) - ε)) z b α ≤
        A * N / (Real.log N) ^ C

/-- Both choices of sign in the fixed b reading of Theorem 1.5. -/
def Theorem15FixedB : Prop := SemilinearBVFixedB true ∧ SemilinearBVFixedB false

/-- The empty prime list puts 1 in either support at every level at least 1. -/
theorem semilinearSupport_one (upper : Bool) {D z : ℝ} (hD : 1 ≤ D) :
    SemilinearSupport upper D z 1 := by
  refine ⟨by simpa using hD, [], by simp, by simp, by simp, ?_⟩
  intro k hk hlen
  cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_nil] at hlen <;> omega

/-- The weight of 1 is 1 at every level at least 1. -/
theorem semilinearWeight_one (upper : Bool) {D z : ℝ} (hD : 1 ≤ D) :
    semilinearWeight upper D z 1 = 1 := by
  simp [semilinearWeight, semilinearSupport_one upper hD]

/-- No weight occurs beyond the level. -/
theorem semilinearWeight_eq_zero_of_level (upper : Bool) {D z : ℝ} {d : ℕ} (hd : D < d) :
    semilinearWeight upper D z d = 0 := by
  rw [semilinearWeight, if_neg]
  exact fun h => (not_le.mpr hd) h.1

/-- Semilinear weights have absolute value at most 1. -/
theorem semilinearWeight_abs_le_one (upper : Bool) (D z : ℝ) (d : ℕ) :
    |semilinearWeight upper D z d| ≤ 1 := by
  unfold semilinearWeight
  split_ifs
  · exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  · norm_num

/-- Nonzero semilinear weights are supported on squarefree integers. -/
theorem semilinearWeight_squarefree (upper : Bool) {D z : ℝ} {d : ℕ}
    (h : semilinearWeight upper D z d ≠ 0) : Squarefree d := by
  unfold semilinearWeight at h
  split_ifs at h with hs
  · apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
    exact_mod_cast h
  · exact (h rfl).elim

/-- A zero value of d has weight zero. -/
theorem semilinearWeight_zero (upper : Bool) (D z : ℝ) :
    semilinearWeight upper D z 0 = 0 := by
  unfold semilinearWeight
  split_ifs <;> simp

#print axioms semilinearSupport_one
#print axioms semilinearWeight_one
#print axioms semilinearWeight_eq_zero_of_level
#print axioms semilinearWeight_abs_le_one
#print axioms semilinearWeight_squarefree
#print axioms semilinearWeight_zero

end LeanLab.Teravainen2016
