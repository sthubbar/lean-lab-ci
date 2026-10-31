/-
Task63 audit of the explicit target already proved on main.
No existing theorem is counted as a new proof by task63.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.SchnirelmannExplicit.Sharper6

example : LeanLab.SchnirelmannExplicit.C1 = (34878787345 : ℝ) := by
  norm_num [LeanLab.SchnirelmannExplicit.C1]

#print axioms LeanLab.SchnirelmannExplicit.S1u_explicit
#print axioms LeanLab.SchnirelmannExplicit.S2_explicit
#print axioms LeanLab.SchnirelmannExplicit.pi_lower_explicit
#print axioms LeanLab.SchnirelmannExplicit.S3_concrete
#print axioms LeanLab.SchnirelmannExplicit.α₀_le_density
#print axioms LeanLab.SchnirelmannExplicit.one_le_α₀_mul_K₀
#print axioms LeanLab.SchnirelmannExplicit.H₀_eq
#print axioms LeanLab.SchnirelmannExplicit.schnirelmann_bounded_primes_explicit
#print axioms LeanLab.SchnirelmannExplicit.Sharper6.H₆_eq
#print axioms LeanLab.SchnirelmannExplicit.Sharper6.schnirelmann_bounded_primes_H₆
#check LeanLab.SchnirelmannExplicit.S1u_explicit
#check LeanLab.SchnirelmannExplicit.S2_explicit
#check LeanLab.SchnirelmannExplicit.S3_concrete
#check LeanLab.SchnirelmannExplicit.α₀_le_density
#check LeanLab.SchnirelmannExplicit.H₀_eq
#check LeanLab.SchnirelmannExplicit.Sharper6.H₆_eq
