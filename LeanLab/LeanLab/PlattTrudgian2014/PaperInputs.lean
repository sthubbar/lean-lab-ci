/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1404.5669v2 page 2, definitions of C0, C2, k and the finite C3 sum.
The cited numerical input statements are Props, not asserted theorems.
-/
import LeanLab.PlattTrudgian2014.TailQuestion
import LeanLab.PlattTrudgian2014.HGeneral

namespace LeanLab.PlattTrudgian2014

open Finset

noncomputable def paperC0 : ℝ :=
  ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p : ℝ) - 1) ^ 2)

noncomputable def paperC2term (j : ℕ) : ℝ :=
  paperWeight (2 ^ (j + 1) - 1) / (orderOf (2 : ZMod (2 ^ (j + 1) - 1)) : ℝ)

noncomputable def paperC2 : ℝ := ∑' j : ℕ, paperC2term j

noncomputable def paperC3Finite (D K N : ℕ) : ℝ :=
  2 * ∑ d ∈ Icc 1 D, paperWeight d *
    ((Section2.H d (orderOf (2 : ZMod d)) K (N : ZMod d) : ℝ) /
      (orderOf (2 : ZMod d) : ℝ) ^ K)

def WrenchInput : Prop := 0.6601618158 < paperC0 ∧ paperC0 < 0.6601618159

def PintzProductInput : Prop :=
  Summable paperC2term ∧ 1.2783521041 < paperC2 * paperC0 ∧ paperC2 * paperC0 < 1.2784421041

def C3ComputationsInput : Prop :=
  ∀ N : ℕ, 3.011112 ≤ paperC3Finite 40000 6 N ∧ 3.02858417 ≤ paperC3Finite 40000 11 N

theorem paperWeight_nonneg (d : ℕ) : 0 ≤ paperWeight d := by
  unfold paperWeight
  split_ifs with h
  · apply prod_nonneg
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    exact div_nonneg (by norm_num) (sub_nonneg.mpr (by exact_mod_cast hpr.two_le))
  · exact le_rfl

theorem paperWeight_one : paperWeight 1 = 1 := by
  norm_num [paperWeight]

theorem paperWeight_even {d : ℕ} (hd : Even d) : paperWeight d = 0 := by
  have ho : ¬Odd d := Nat.not_odd_iff_even.mpr hd
  simp [paperWeight, ho]

theorem paperWeight_not_squarefree {d : ℕ} (hd : ¬Squarefree d) : paperWeight d = 0 := by
  simp [paperWeight, hd]

theorem paperWeight_odd_prime {p : ℕ} (hp : Nat.Prime p) (ho : Odd p) :
    paperWeight p = 1 / ((p : ℝ) - 2) := by
  have hs : Squarefree p := (Nat.prime_iff.mp hp).squarefree
  simp [paperWeight, ho, hs, hp.primeFactors]

theorem paperWeight_mul {m n : ℕ} (hcop : Nat.Coprime m n) :
    paperWeight (m * n) = paperWeight m * paperWeight n := by
  by_cases hm : m = 0
  · subst m
    simp [paperWeight]
  by_cases hn : n = 0
  · subst n
    simp [paperWeight]
  unfold paperWeight
  simp only [Nat.odd_mul, Nat.squarefree_mul hcop]
  by_cases hmo : Odd m <;> by_cases hno : Odd n <;>
    by_cases hms : Squarefree m <;> by_cases hns : Squarefree n <;>
      simp only [hmo, hno, hms, hns, and_self, and_false, false_and, and_true, true_and,
        ite_true, ite_false, zero_mul, mul_zero]
  rw [Nat.primeFactors_mul hm hn, Finset.prod_union hcop.disjoint_primeFactors]

theorem paperC3Finite_nonneg (D K N : ℕ) : 0 ≤ paperC3Finite D K N := by
  unfold paperC3Finite
  apply mul_nonneg (by norm_num)
  apply sum_nonneg
  intro d hd
  exact mul_nonneg (paperWeight_nonneg d) (div_nonneg (Nat.cast_nonneg _) (by positivity))

theorem paperC3Finite_mono {D D' : ℕ} (hD : D ≤ D') (K N : ℕ) :
    paperC3Finite D K N ≤ paperC3Finite D' K N := by
  unfold paperC3Finite
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    exact mem_Icc.mpr ⟨(mem_Icc.mp hd).1, (mem_Icc.mp hd).2.trans hD⟩
  · intro d hd _
    exact mul_nonneg (paperWeight_nonneg d) (div_nonneg (Nat.cast_nonneg _) (by positivity))

#print axioms paperWeight_nonneg
#print axioms paperWeight_one
#print axioms paperWeight_even
#print axioms paperWeight_not_squarefree
#print axioms paperWeight_odd_prime
#print axioms paperWeight_mul
#print axioms paperC3Finite_nonneg
#print axioms paperC3Finite_mono

end LeanLab.PlattTrudgian2014
