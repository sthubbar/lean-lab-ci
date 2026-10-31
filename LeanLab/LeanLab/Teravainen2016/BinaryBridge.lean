/-
P0076, Theorem 1.1, pages 10 to 12. Proposition 2.1 is discharged.
The conclusions remain CONDITIONAL ON the explicitly named analytic inputs.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.Prop21
import LeanLab.Teravainen2016.CrossScale

namespace LeanLab.Teravainen2016

/-- Theorem 1.1, CONDITIONAL ON ChiExists, Prop32, Prop32Half and Prop33. -/
theorem theorem11_after_prop21 (hχ : ChiExists) (h32 : Prop32) (h32h : Prop32Half)
    (h33 : Prop33) : Theorem11 :=
  theorem11_conditional prop21_small_proved hχ h32 h32h h33

/-- Theorem 1.1, CONDITIONAL ON ChiExists, Prop32, Prop32Half and Prop33Printed. -/
theorem theorem11_printed_after_prop21 (hχ : ChiExists) (h32 : Prop32) (h32h : Prop32Half)
    (h33 : Prop33Printed) : Theorem11 :=
  theorem11_printed prop21_small_proved hχ h32 h32h h33

#print axioms theorem11_after_prop21
#print axioms theorem11_printed_after_prop21

end LeanLab.Teravainen2016
