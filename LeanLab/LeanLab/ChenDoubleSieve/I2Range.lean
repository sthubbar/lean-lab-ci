import LeanLab.ChenDoubleSieve.BuchstabBounds

/-!
# Range obligations for the higher dimensional I2 integrals

Source: https://arxiv.org/pdf/0705.1652, page 26, the last I2 domain.
Zero below one is an explicit auxiliary extension convention.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set
namespace LeanLab.ChenDoubleSieve.Wu04Functional

/-- A zero extension below the domain of the defining delay equation. -/
def ZeroBelowOne (ω : ℝ → ℝ) : Prop := ∀ u : ℝ, u < 1 → ω u = 0

/-- A global upper bound after stating the extension convention explicitly.
CONDITIONAL ON IsBuchstab and ZeroBelowOne. -/
theorem extended_buchstab_le_one {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    (u : ℝ) : ω u ≤ 1 := by
  by_cases hu : u < 1
  · rw [hz u hu]
    norm_num
  · have h1 : 1 ≤ u := le_of_not_gt hu
    by_cases h2 : u ≤ 2
    · rw [hω.2.1 u h1 h2]
      exact (div_le_one (by linarith : 0 < u)).mpr h1
    · exact (Wu04Buchstab.buchstab_le_567144 hω (by linarith)).trans (by norm_num)

/-- The higher dimensional domain includes arguments outside the delay equation range. -/
theorem last_I2_range_witness :
    (fun _ : Fin 6 => (7/16 : ℝ)) ∈ domain
      (fun _ => 1/(tableParams 0).k3) (fun _ => 1/(tableParams 0).s) ∧
    (2 - ∑ j : Fin 6, (7/16 : ℝ)) / (7/16 : ℝ) = -10/7 := by
  constructor
  · constructor
    · intro a b hab
      exact le_rfl
    · intro j
      norm_num [tableParams]
  · norm_num

end LeanLab.ChenDoubleSieve.Wu04Functional

#print axioms LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one
#print axioms LeanLab.ChenDoubleSieve.Wu04Functional.last_I2_range_witness
