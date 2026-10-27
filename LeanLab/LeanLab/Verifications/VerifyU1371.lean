import LeanLab.Kaniecki1995.Lemma5Kernel9A
import LeanLab.Pintz2021.Moment510U1357
/- U-1371 verification scratch, run 20261021T0604Z-1697. AI wrote the Lean code. Binary Goldbach is OPEN. -/
#print axioms LeanLab.Kaniecki1995.L5.kernel9A
#print axioms LeanLab.Kaniecki1995.L5.kernel9A_nonvacuous
#print axioms LeanLab.Pintz2021.Moment510U1357.display510_proved
#print axioms LeanLab.Pintz2021.Moment510U1357.integral_eq_Q4
#print axioms LeanLab.Pintz2021.Moment510U1357.Q4_ge
example : LeanLab.Kaniecki1995.L5.Kernel9A = (∀ T σ A : ℝ, 0 < T → 0 < σ → 0 ≤ A →
    ∫ t in Set.Ioi (0 : ℝ), LeanLab.Kaniecki1995.kern T σ t * Real.cos (A * t) =
      LeanLab.Kaniecki1995.L5.kap T σ A) := rfl
example : LeanLab.Pintz2021.Holder511.Display510 5 2 4 := LeanLab.Pintz2021.Moment510U1357.display510_proved 4 le_rfl
