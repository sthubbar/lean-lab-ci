import LeanLab.ChenDoubleSieve.FunctionalStatements
import LeanLab.ChenDoubleSieve.Section7Algebra

/-!
# Exact dual certificate for the Section 7 linear inequalities

Source: https://arxiv.org/pdf/0705.1652, pages 30 and 31, equations 7.1 to 7.4.
The candidate matrix comes from numerical exploration. Its comparison with the
actual integral matrix is an explicit unproved input. No quadrature is trusted here.
The rational dual calculation is checked by the Lean kernel.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Finset
namespace LeanLab.ChenDoubleSieve.Wu04Table

/-- A nonnegative dual vector gives a lower bound without matrix inversion. -/
theorem dual_lower_bound {n : Type*} [Fintype n] [DecidableEq n]
    (A : n → n → ℝ) (B H w : n → ℝ) (k : n)
    (hw : ∀ i, 0 ≤ w i) (hH : ∀ i, 0 ≤ H i)
    (hdual : ∀ j, w j - ∑ i, w i * A i j ≤ if j = k then 1 else 0)
    (hrow : ∀ i, B i + ∑ j, A i j * H j ≤ H i) :
    ∑ i, w i * B i ≤ H k := by
  calc
    ∑ i, w i * B i ≤ ∑ i, w i * (H i - ∑ j, A i j * H j) := by
      exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by linarith [hrow i]) (hw i)
    _ = ∑ j, (w j - ∑ i, w i * A i j) * H j := by
      simp_rw [mul_sub, sub_mul, mul_sum, sum_mul, sum_sub_distrib, mul_assoc]
      congr 1
      exact sum_comm
    _ ≤ ∑ j, (if j = k then 1 else 0) * H j := by
      exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hdual j) (hH j)
    _ = H k := by simp

/-- Candidate lower matrix at scale ten million.
Its integral interpretation is required by IntegralMatrixBound below. -/
def candidateMatrixQ : Fin 9 → Fin 9 → ℚ :=
  ![![1551926 / 10000000, 261910 / 10000000, 266515 / 10000000, 269346 / 10000000, 271084 / 10000000, 274861 / 10000000, 278478 / 10000000, 281663 / 10000000, 284464 / 10000000],
    ![1537386 / 10000000, 255908 / 10000000, 260352 / 10000000, 262914 / 10000000, 265826 / 10000000, 270061 / 10000000, 273794 / 10000000, 277085 / 10000000, 279985 / 10000000],
    ![1525199 / 10000000, 250515 / 10000000, 254743 / 10000000, 257327 / 10000000, 261548 / 10000000, 265892 / 10000000, 269726 / 10000000, 273110 / 10000000, 276095 / 10000000],
    ![1549103 / 10000000, 239617 / 10000000, 246126 / 10000000, 251857 / 10000000, 256913 / 10000000, 261376 / 10000000, 265319 / 10000000, 268803 / 10000000, 271881 / 10000000],
    ![1594156 / 10000000, 238776 / 10000000, 245310 / 10000000, 251066 / 10000000, 256142 / 10000000, 260625 / 10000000, 264587 / 10000000, 268087 / 10000000, 271181 / 10000000],
    ![1602317 / 10000000, 234607 / 10000000, 241272 / 10000000, 247145 / 10000000, 252328 / 10000000, 256909 / 10000000, 260960 / 10000000, 264544 / 10000000, 267713 / 10000000],
    ![1649911 / 10000000, 233852 / 10000000, 240539 / 10000000, 246434 / 10000000, 251637 / 10000000, 256236 / 10000000, 260303 / 10000000, 263901 / 10000000, 267084 / 10000000],
    ![1737478 / 10000000, 236829 / 10000000, 243424 / 10000000, 249235 / 10000000, 254362 / 10000000, 258890 / 10000000, 262893 / 10000000, 266433 / 10000000, 269562 / 10000000],
    ![1910519 / 10000000, 246475 / 10000000, 252770 / 10000000, 258308 / 10000000, 263187 / 10000000, 267489 / 10000000, 271285 / 10000000, 274633 / 10000000, 277585 / 10000000]]

/-- Exact printed Table 1 right side. -/
def printedBQ : Fin 9 → ℚ :=
  ![15826357 / 1000000000, 15247971 / 1000000000, 13898757 / 1000000000, 11776059 / 1000000000, 9405211 / 1000000000, 6558950 / 1000000000, 3536751 / 1000000000, 1056651 / 1000000000, 0 / 1000000000]

/-- A prospective dual vector. Its validity is certified below. -/
def dualQ : Fin 9 → ℚ :=
  ![1250767294 / 1000000000, 41110407 / 1000000000, 41894011 / 1000000000, 42420653 / 1000000000, 42801056 / 1000000000, 43426855 / 1000000000, 44014748 / 1000000000, 44532811 / 1000000000, 44988865 / 1000000000]

set_option maxRecDepth 100000 in
/-- Nonnegativity and all nine residual inequalities are exact. -/
theorem dual_certificate :
    (∀ i : Fin 9, 0 ≤ dualQ i) ∧
    (∀ j : Fin 9, dualQ j - ∑ i, dualQ i * candidateMatrixQ i j ≤ if j = 0 then 1 else 0) ∧
    (223938 / 10000000 : ℚ) ≤ ∑ i, dualQ i * printedBQ i := by
  decide +kernel

/-- The scalar conclusion from the nine candidate linear inequalities.
CONDITIONAL ON those inequalities for the supplied correction vector. -/
theorem correction_of_discrete (H : Fin 9 → ℝ) (hH : ∀ i, 0 ≤ H i)
    (hrow : ∀ i, (printedBQ i : ℝ) + ∑ j, (candidateMatrixQ i j : ℝ) * H j ≤ H i) :
    (223938 / 10000000 : ℝ) ≤ H 0 := by
  have hw (i : Fin 9) : (0 : ℝ) ≤ dualQ i := by exact_mod_cast dual_certificate.1 i
  have hd (j : Fin 9) : (dualQ j : ℝ) - ∑ i, (dualQ i : ℝ) * (candidateMatrixQ i j : ℝ) ≤
      if j = 0 then 1 else 0 := by
    have hh : ((dualQ j - ∑ i, dualQ i * candidateMatrixQ i j : ℚ) : ℝ) ≤
        ((if j = 0 then 1 else 0 : ℚ) : ℝ) := by exact_mod_cast dual_certificate.2.1 j
    push_cast at hh
    by_cases hj : j = 0 <;> simpa [hj] using hh
  have hb : (223938 / 10000000 : ℝ) ≤ ∑ i, (dualQ i : ℝ) * (printedBQ i : ℝ) := by
    have hh : ((223938 / 10000000 : ℚ) : ℝ) ≤ ((∑ i, dualQ i * printedBQ i : ℚ) : ℝ) := by
      exact_mod_cast dual_certificate.2.2
    push_cast at hh
    exact hh
  exact hb.trans (dual_lower_bound (fun i j => (candidateMatrixQ i j : ℝ))
    (fun i => (printedBQ i : ℝ)) H (fun i => (dualQ i : ℝ)) 0 hw hH hd hrow)

/-- Replacing an actual matrix by an entrywise smaller candidate is valid for H nonnegative. -/
theorem discrete_of_entrywise {n : Type*} [Fintype n]
    (A L : n → n → ℝ) (B H : n → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hL : ∀ i j, L i j ≤ A i j)
    (hrow : ∀ i, B i + ∑ j, A i j * H j ≤ H i) :
    ∀ i, B i + ∑ j, L i j * H j ≤ H i := by
  intro i
  exact (add_le_add (le_refl (B i)) (sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (hL i j) (hH j))).trans (hrow i)

/-- A nonzero concrete instance of the discrete hypotheses. -/
theorem discrete_instance : ∀ i : Fin 9,
    (printedBQ i : ℝ) + ∑ j, (candidateMatrixQ i j : ℝ) * 1 ≤ (1 : ℝ) := by
  intro i
  fin_cases i <;> norm_num [printedBQ, candidateMatrixQ, Fin.sum_univ_succ]

/-- The exact analytic kernel at each of the nine Table 1 coordinates. -/
def tableKernel (i : Fin 9) (t : ℝ) : ℝ :=
  if hi : i.val < 4 then Wu04Functional.Xi2 (Wu04Functional.tableParams ⟨i.val, hi⟩) t
  else Wu04Functional.Xi1 (Wu04Functional.grid ⟨i.val + 1, by omega⟩)
    (Wu04Functional.tableSp ⟨i.val - 4, by omega⟩) t

/-- The integral matrix of equations 7.1 and 7.2. -/
def integralMatrix (i j : Fin 9) : ℝ :=
  ∫ t in Wu04Functional.grid ⟨j.val, by omega⟩..Wu04Functional.grid ⟨j.val + 1, by omega⟩,
    tableKernel i t

/-- The unproved comparison needed to interpret the rational candidate matrix. -/
def IntegralMatrixBound : Prop :=
  ∀ i j : Fin 9, (candidateMatrixQ i j : ℝ) ≤ integralMatrix i j

end LeanLab.ChenDoubleSieve.Wu04Table

#print axioms LeanLab.ChenDoubleSieve.Wu04Table.dual_lower_bound
#print axioms LeanLab.ChenDoubleSieve.Wu04Table.dual_certificate
#print axioms LeanLab.ChenDoubleSieve.Wu04Table.correction_of_discrete
#print axioms LeanLab.ChenDoubleSieve.Wu04Table.discrete_of_entrywise
#print axioms LeanLab.ChenDoubleSieve.Wu04Table.discrete_instance
