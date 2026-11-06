/-
Exact bridges from cited stubs to existing proofs in this folder.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DensityGoldbach.Prop14Full
import LeanLab.DensityGoldbach.AlsetriClassTwo
import LeanLab.DensityGoldbach.U1502Final

namespace LeanLab.DensityGoldbach.Bridge408

/-- Shao 1206.6139v2 page 2, Proposition 1.4. The lab already proves this
statement by the finite local argument in Prop14Full. -/
theorem prop_1_4 (m : ℕ) [NeZero m] (hodd : Odd m) (hsq : Squarefree m) : Prop14 m :=
  prop_1_4_proved m hodd hsq

/-- Alsetri 2505.09648v3 page 2, Theorem 1.2. The lab already proves the
statement by its CRT induction in AlsetriFull. -/
theorem alsetri_1_2 (m : ℕ) [NeZero m] (hodd : Odd m) (hsq : Squarefree m) (h3 : 3 ∣ m) :
    Alsetri12 m := alsetri_1_2_proved m hodd hsq h3

/-- Alsetri and Shao 2405.18576v2 page 2, Theorem 1.2. The exact original
statement follows from the existing majorant and large spectrum proof. -/
theorem alsetriShao_1_2 : AlsetriShao12 := U1502.alsetriShao_1_2

end LeanLab.DensityGoldbach.Bridge408

#print axioms LeanLab.DensityGoldbach.Bridge408.prop_1_4
#print axioms LeanLab.DensityGoldbach.Bridge408.alsetri_1_2
#print axioms LeanLab.DensityGoldbach.Bridge408.alsetriShao_1_2
