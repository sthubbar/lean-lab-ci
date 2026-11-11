import LeanLab.LanguascoPintzZaccagnini2007.Instances481

/-!
A nonempty zero box with an admissible major arc parameter.
This is a fixed parameter domain check, not an asymptotic density assertion.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Real

/-- P0045 pages 3 to 5, the P range and display 8.
The actual zero at minus two lies in a box with H and T at least one
and with P in the required admissible range at X equal to two. -/
theorem admissible_zeroBox_instance481 :
    AdmissibleP131 2 ((2 : ℝ) ^ ((2 : ℝ) / 5)) ∧
      1 ≤ 3 * Real.log 2 ∧
      (⟨1, (1 : DirichletCharacter ℂ 1), -2⟩ : Σ r : ℕ, DirichletCharacter ℂ r × ℂ) ∈
        zeroBox481 2 (3 * Real.log 2) 1 ((2 : ℝ) ^ ((2 : ℝ) / 5)) := by
  have hP : 1 ≤ (2 : ℝ) ^ ((2 : ℝ) / 5) := Real.one_le_rpow (by norm_num) (by norm_num)
  refine ⟨⟨le_rfl, ?_⟩, ?_, ?_⟩
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  · linarith [Real.log_two_gt_d9]
  · exact ⟨zeroBox_nonempty_instance481.1, by simpa using hP, zeroBox_nonempty_instance481.2.2⟩

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.admissible_zeroBox_instance481
