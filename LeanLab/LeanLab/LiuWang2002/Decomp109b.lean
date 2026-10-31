import LeanLab.LiuWang2002.Vaughan109
import LeanLab.LiuWang2002.Numeric109

/-! Lemma 6.2, page 169. AI wrote the Lean code. Binary Goldbach is open. -/

namespace LeanLab.LiuWang2002.Decomp109b
open Real Vaughan109 ArithmeticFunction
open scoped ArithmeticFunction

/-- CITED. Lemma 6.2, page 169, in the large N regime fixed on page 168. -/
def FirstSumEstimate : Prop :=
  ∀ N c α : ℝ, exp 30.95 ≤ N → 0 < c → c < 1 → ‖S1 N c α‖ ≤ 1.02 * U N

/-- LEAF. The logarithm certificate in the first line of the proof on page 169. -/
theorem log_endpoint : log (30.95 : ℝ) ≤ 3.4325 := by
  apply (log_le_iff_le_exp (by norm_num)).mpr
  have h3 : exp (3 : ℝ) = exp 1 ^ 3 := by simpa using exp_nat_mul (1 : ℝ) 3
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.4325) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  have he : (2.7182818283 : ℝ) ≤ exp 1 := Real.exp_one_gt_d9.le
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) he 3
  rw [show (3.4325 : ℝ) = 3 + 0.4325 by norm_num, exp_add, h3]
  have hh := mul_le_mul hp hs (by positivity) (by positivity : 0 ≤ exp 1 ^ 3)
  norm_num only at hh ⊢
  linarith

/-- LEAF. The parameter U is at least exp 9.634, page 169. -/
theorem U_lower (N : ℝ) (hN : exp 30.95 ≤ N) : exp 9.634 ≤ U N := by
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hL : 30.95 ≤ log N := (le_log_iff_exp_le hNp).mpr hN
  have hLp : 0 < log N := by linarith
  have hl := log_le_sub_one_of_pos (show 0 < log N / 30.95 by positivity)
  rw [log_div hLp.ne' (by norm_num)] at hl
  have heq : U N = exp (2 / 5 * log N - 4 / 5 * log (log N)) := by
    unfold U
    rw [rpow_def_of_pos hNp, rpow_def_of_pos hLp, ← exp_add]
    congr 1
    ring
  rw [heq]
  apply exp_le_exp.mpr
  have ht := log_endpoint
  have hdiv : log N / 30.95 = (log N - 30.95) / 30.95 + 1 := by ring
  rw [hdiv] at hl
  norm_num at hl
  linarith

/-- LEAF. The finite sum triangle estimate in the proof on page 169.
It holds for the inclusive cutoff of display 3.8 as well. -/
theorem first_triangle (N c α : ℝ) (X : ℝ) (hX : 0 ≤ X) :
    ‖weightedSum (shortPart Λ X) N c α‖ ≤
      ∑ n ∈ Finset.range (Nat.floor X + 1), Λ n := by
  unfold weightedSum
  calc
    _ ≤ ∑ n ∈ Finset.range (Nat.floor N + 1),
        ‖if c * N ≤ (n : ℝ) then ((shortPart Λ X) n : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (α * n)) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (Nat.floor N + 1), if (n : ℝ) ≤ X then Λ n else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : 0 ≤ Λ n := vonMangoldt_nonneg
      have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * (α * n))‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      by_cases hc : c * N ≤ (n : ℝ)
      · rw [if_pos hc, norm_mul, hexp, mul_one]
        by_cases hu : (n : ℝ) ≤ X <;> simp [shortPart, hu, Complex.norm_real, abs_of_nonneg hn0]
      · rw [if_neg hc, norm_zero]
        split_ifs <;> positivity
    _ = ∑ n ∈ (Finset.range (Nat.floor N + 1)).filter (fun n : ℕ => (n : ℝ) ≤ X), Λ n := by
      rw [Finset.sum_filter]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have hx := (Finset.mem_filter.mp hn).2
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor hx))
      · intro n hn hnot
        exact vonMangoldt_nonneg

/-- LEAF. The psi bound in the last display of the proof on page 169.
External input: Rosser and Schoenfeld 1975, page 265, displays 5.1 and 5.3. -/
theorem psi_bound (X : ℝ) (hX : exp 9.634 ≤ X) :
    (∑ n ∈ Finset.range (Nat.floor X + 1), Λ n) ≤
      1.001102 * (X + X ^ (1 / 2 : ℝ)) + 3 * X ^ (1 / 3 : ℝ) := by
  sorry

/-- LEAF. The numerical absorption in the last display on page 169. -/
theorem root_absorb (X : ℝ) (hX : exp 9.634 ≤ X) :
    1.001102 * (X + X ^ (1 / 2 : ℝ)) + 3 * X ^ (1 / 3 : ℝ) ≤ 1.02 * X := by
  have hX0 : 0 ≤ X := (exp_pos _).le.trans hX
  have h15000 : 15000 ≤ X := Constants.exp9634_ge.trans hX
  have hs0 : 0 ≤ X ^ (1 / 2 : ℝ) := rpow_nonneg hX0 _
  have hc0 : 0 ≤ X ^ (1 / 3 : ℝ) := rpow_nonneg hX0 _
  have hs2 : (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
    rw [← rpow_natCast _ 2, ← rpow_mul hX0]
    norm_num
  have hc3 : (X ^ (1 / 3 : ℝ)) ^ 3 = X := by
    rw [← rpow_natCast _ 3, ← rpow_mul hX0]
    norm_num
  have hs : 122 ≤ X ^ (1 / 2 : ℝ) := by nlinarith
  have hc : 24 ≤ X ^ (1 / 3 : ℝ) := by
    by_contra h
    have hh := pow_lt_pow_left₀ (lt_of_not_ge h) hc0 (show (3 : ℕ) ≠ 0 by decide)
    rw [hc3] at hh
    norm_num at hh
    linarith
  have hh := Constants.lemma62_numeric _ _ hs hc (hs2.trans hc3.symm)
  rwa [hs2] at hh

/-- Lemma 6.2 assembled without sorry. CONDITIONAL ON psi_bound. -/
theorem lemma62 : FirstSumEstimate := by
  intro N c α hN hc hc1
  have hu := U_lower N hN
  have hu0 : 0 ≤ U N := (exp_pos _).le.trans hu
  exact (first_triangle N c α (U N) hu0).trans ((psi_bound _ hu).trans (root_absorb _ hu))

/-- The global triangle estimate used before display 6.3, page 168. -/
theorem full_triangle (N c α : ℝ) (hN : 0 ≤ N) :
    ‖S N c α‖ ≤ ∑ n ∈ Finset.range (Nat.floor N + 1), Λ n := by
  have heq : weightedSum (shortPart Λ N) N c α = S N c α := by
    unfold weightedSum S
    apply Finset.sum_congr rfl
    intro n hn
    have hnf : n ≤ Nat.floor N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hnN : (n : ℝ) ≤ N := (by exact_mod_cast hnf : (n : ℝ) ≤ Nat.floor N).trans (Nat.floor_le hN)
    simp [shortPart, hnN]
  rw [← heq]
  exact first_triangle N c α N hN

/-- Root arithmetic for the refined global estimate on page 168. -/
theorem refined_roots (X : ℝ) (hX : 6.36e12 ≤ X) :
    1.001102 * (X + X ^ (1 / 2 : ℝ)) + 3 * X ^ (1 / 3 : ℝ) ≤ 1.0012 * X := by
  have hX0 : 0 ≤ X := by linarith
  have hs0 : 0 ≤ X ^ (1 / 2 : ℝ) := rpow_nonneg hX0 _
  have hc0 : 0 ≤ X ^ (1 / 3 : ℝ) := rpow_nonneg hX0 _
  have hs2 : (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
    rw [← rpow_natCast _ 2, ← rpow_mul hX0]
    norm_num
  have hc3 : (X ^ (1 / 3 : ℝ)) ^ 3 = X := by
    rw [← rpow_natCast _ 3, ← rpow_mul hX0]
    norm_num
  have hs : 100000 ≤ X ^ (1 / 2 : ℝ) := by nlinarith
  have hc : 1000 ≤ X ^ (1 / 3 : ℝ) := by
    by_contra h
    have hh := pow_lt_pow_left₀ (lt_of_not_ge h) hc0 (show (3 : ℕ) ≠ 0 by decide)
    rw [hc3] at hh
    norm_num at hh
    linarith
  have hsq := mul_le_mul_of_nonneg_right hs hs0
  have hc2 : 1000000 ≤ (X ^ (1 / 3 : ℝ)) ^ 2 := by nlinarith
  have hcu := mul_le_mul_of_nonneg_right hc2 hc0
  nlinarith

end LeanLab.LiuWang2002.Decomp109b

#print axioms LeanLab.LiuWang2002.Decomp109b.log_endpoint
#print axioms LeanLab.LiuWang2002.Decomp109b.U_lower
#print axioms LeanLab.LiuWang2002.Decomp109b.first_triangle
#print axioms LeanLab.LiuWang2002.Decomp109b.root_absorb
#print axioms LeanLab.LiuWang2002.Decomp109b.lemma62

#print axioms LeanLab.LiuWang2002.Decomp109b.full_triangle
#print axioms LeanLab.LiuWang2002.Decomp109b.refined_roots
