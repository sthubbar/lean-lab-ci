/-
Euler products and truncation errors for the indexed Goldbach pure sieve.
Source: Brun 1919, pages 103, 104 and 124 to 125.
These are lab derivations from the source method. AI wrote the Lean code.
Goldbach is open.
-/
import LeanLab.SchnirelmannGoldbach.PureSieve

open Finset
open scoped Classical

namespace LeanLab.SchnirelmannGoldbach.PureSieve

open LeanLab.SchnirelmannGoldbach.S1

/-- The finite main term differs from the Euler product by at most the factorial tail. -/
theorem main_error (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (k : ℕ) :
    |(∑ T ∈ P.powerset.filter (fun T => T.card ≤ k),
        (-1 : ℝ) ^ T.card * ∏ p ∈ T, (wt n p / p)) -
      ∏ p ∈ P, (1 - wt n p / p)| ≤
      (∑ p ∈ P, wt n p / p) ^ (k + 1) / (k + 1).factorial := by
  let x : ℕ → ℝ := fun p => if p ∈ P then wt n p / p else 0
  have hx0 : ∀ p, 0 ≤ x p := by
    intro p
    dsimp [x]
    split_ifs
    · exact div_nonneg (wt_pos n p).le (Nat.cast_nonneg _)
    · norm_num
  have hx1 : ∀ p, x p ≤ 1 := by
    intro p
    dsimp [x]
    split_ifs with hp
    · rw [div_le_one (by exact_mod_cast (hP p hp).pos)]
      exact (wt_le_two n p).trans (by exact_mod_cast (hP p hp).two_le)
    · norm_num
  have hprod : ∀ T : Finset ℕ, T ⊆ P →
      (∏ p ∈ T, x p) = ∏ p ∈ T, (wt n p / p) := by
    intro T hT
    exact prod_congr rfl (fun p hp => ite_eq_left (hT hp))
  have hsum : (∑ p ∈ P, x p) = ∑ p ∈ P, (wt n p / p) :=
    sum_congr rfl (fun p hp => ite_eq_left hp)
  have hV : (∏ p ∈ P, (1 - x p)) = ∏ p ∈ P, (1 - wt n p / p) := by
    apply prod_congr rfl
    intro p hp
    dsimp [x]
    rw [ite_eq_left hp]
  have hM : (∑ T ∈ P.powerset.filter (fun T => T.card ≤ k),
      (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p) =
      ∑ T ∈ P.powerset.filter (fun T => T.card ≤ k),
        (-1 : ℝ) ^ T.card * ∏ p ∈ T, (wt n p / p) := by
    apply sum_congr rfl
    intro T hT
    rw [hprod T (mem_powerset.mp (mem_filter.mp hT).1)]
  have h := LeanLab.PNTSieve.Bonferroni.main_dev P x hx0 hx1 k
  rw [hM, hV, hsum] at h
  exact h

/-- The pure Brun upper sieve with explicit local, factorial and endpoint constants. -/
theorem r_le_pure_brun (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k : ℕ) (hk : Even k) :
    (r n : ℝ) ≤ n * ∏ p ∈ P, (1 - wt n p / p) +
      n * ((∑ p ∈ P, wt n p / p) ^ (k + 1) / (k + 1).factorial) +
      ∑ j ∈ range (k + 1), (P.card.choose j : ℝ) * 2 ^ j + 2 * P.card := by
  have h := r_le_brun_main n P hP k hk
  have hM := (abs_le.mp (main_error n P hP k)).2
  have hscaled := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg n)
  linarith

/-- Brun bounds the Euler product by the exponential of minus the density sum. -/
theorem product_le_exp (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∏ p ∈ P, (1 - wt n p / p) ≤ Real.exp (-(∑ p ∈ P, wt n p / p)) := by
  calc ∏ p ∈ P, (1 - wt n p / p) ≤ ∏ p ∈ P, Real.exp (-(wt n p / p)) := by
        apply prod_le_prod₀
        · intro p hp
          rw [sub_nonneg, div_le_one (by exact_mod_cast (hP p hp).pos)]
          exact (wt_le_two n p).trans (by exact_mod_cast (hP p hp).two_le)
        · intro p _
          exact Real.one_sub_le_exp_neg _
    _ = Real.exp (-(∑ p ∈ P, wt n p / p)) := by
        rw [← Real.exp_sum, sum_neg_distrib]

end LeanLab.SchnirelmannGoldbach.PureSieve

#print axioms LeanLab.SchnirelmannGoldbach.PureSieve.main_error

#print axioms LeanLab.SchnirelmannGoldbach.PureSieve.r_le_pure_brun

#print axioms LeanLab.SchnirelmannGoldbach.PureSieve.product_le_exp
