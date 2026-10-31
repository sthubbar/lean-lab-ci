/-
P0045, journal pages 777 to 778, displays 15 to 25.
The arithmetic asymptotics are proved. The major arc theorem retains Cor42W as a named input.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LPZ2007.D4TailProof

namespace LeanLab.LPZ2007.D4Final

open LeanLab.LPZ2007 LeanLab.LPZ2007.R3FromS3 LeanLab.LPZ2007.Eq14FromCor42

/-- Displays 17 to 24 give the full uniform D4 asymptotic with no cited input. -/
theorem d4Asymp_proved : D4Asymp :=
  D4Asymptotic.d4Asymp_of_uniform_tail D4TailProof.uniformD4Tail_proved

/-- The unweighted singular series sum has its full uniform asymptotic. -/
theorem s3Asymp_proved : S3Asymp := s3Asymp_of_d4Asymp d4Asymp_proved

/-- The weighted singular series sum has its full uniform asymptotic. -/
theorem r3Asymp_proved : R3Asymp := r3Asymp_of_s3Asymp s3Asymp_proved

/-- The repaired major arc estimate is conditional only on Cor42W. -/
theorem eq25_twoC0_of_cor42_only (hC : Cor42W) :
    Eq25C (fun k N => twoC0 * Ckn k N) :=
  eq25_twoC0_of_cor42_r3 hC r3Asymp_proved

/-- The repaired main theorem is conditional only on Cor42W. -/
theorem mainJ_twoC0_of_cor42_only (hC : Cor42W) : MainJ_twoC0 :=
  mainJ_twoC0_of_cor42_r3 hC r3Asymp_proved

end LeanLab.LPZ2007.D4Final

#print axioms LeanLab.LPZ2007.D4Final.d4Asymp_proved
#print axioms LeanLab.LPZ2007.D4Final.s3Asymp_proved
#print axioms LeanLab.LPZ2007.D4Final.r3Asymp_proved
#print axioms LeanLab.LPZ2007.D4Final.eq25_twoC0_of_cor42_only
#print axioms LeanLab.LPZ2007.D4Final.mainJ_twoC0_of_cor42_only
