import LeanLab.ChenDoubleSieve.Task587R1J17

/-!
Two obstructions to uniform shortcuts for the remaining row two D2,17 certificate.
Source: https://arxiv.org/abs/0705.1652, page 26 and Table 1 page 30.
These are obstructions to proof methods, not counterexamples to the integral bound.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task660
open Wu04Functional Task587

/-- The constant one times the existing reciprocal polynomial moment exceeds the target. -/
theorem r1j17_uniform_one_insufficient :
    (92979 / 1000000000 : ℝ) <
      ∫ x in domain (fun j => (r1j17_lo j : ℝ)) (fun j => (r1j17_hi j : ℝ)),
        cellPoly 4 (2 : Fin 4) r1j17_lo r1j17_hi x := by
  rw [r1j17_integral]
  norm_num

/-- The remaining domain contains a point where the Buchstab argument at phi two is one. -/
theorem r1j17_argument_one :
    ∃ x ∈ domain (fun j => (r1j17_lo j : ℝ)) (fun j => (r1j17_hi j : ℝ)),
      (2 - ∑ j, x j) / x (2 : Fin 4) = 1 := by
  refine ⟨![(31 / 81 : ℝ), (31 / 81), (100 / 243), (100 / 243)], ?_, ?_⟩
  · constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> norm_num at hij <;> norm_num
    · intro j
      fin_cases j <;> norm_num [r1j17_lo, r1j17_hi]
  · norm_num [Fin.sum_univ_succ]

/-- A uniform pointwise cap of seven twelfths is false on the remaining compact domain. -/
theorem r1j17_seven_twelfths_pointwise_fails {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    ∃ x ∈ domain (fun j => (r1j17_lo j : ℝ)) (fun j => (r1j17_hi j : ℝ)),
      (7 / 12 : ℝ) < ω ((2 - ∑ j, x j) / x (2 : Fin 4)) := by
  obtain ⟨x, hx, he⟩ := r1j17_argument_one
  refine ⟨x, hx, ?_⟩
  rw [he, hω.2.1 1 le_rfl (by norm_num)]
  norm_num

end LeanLab.ChenDoubleSieve.Task660
#print axioms LeanLab.ChenDoubleSieve.Task660.r1j17_uniform_one_insufficient
#print axioms LeanLab.ChenDoubleSieve.Task660.r1j17_argument_one
#print axioms LeanLab.ChenDoubleSieve.Task660.r1j17_seven_twelfths_pointwise_fails
