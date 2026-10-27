/-
Axiom report and kernel falsifiers for unit U-1391, PC run 20261021T1003Z-20044.
AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
-/
import LeanLab.Common.U1391RS33
import LeanLab.ChenExplicit.U1391Relabel
import LeanLab.RieselVaughan1983.U1391Relabel
import LeanLab.SchnirelmannBounds.U1391Relabel
open LeanLab.Common.U1391
#print axioms popc_eq
#print axioms S_step
#print axioms chk_sound
#print axioms chk_ok
#print axioms rs33_small
#print axioms rs33_large
#print axioms rs33_of_rs1975
#print axioms rs33_at_67
#print axioms LeanLab.ChenExplicit.Yamada.U1391.rs62_of_rs75
#print axioms LeanLab.ChenExplicit.Yamada.U1391.thm48_of_rs75
#print axioms LeanLab.ChenExplicit.Yamada.U1391.yamada_of_sieve_rs75
#print axioms LeanLab.RieselVaughan1983.U1391.rs33_of_rs75
#print axioms LeanLab.RieselVaughan1983.U1391.lemma7_of_rs75
#print axioms LeanLab.RieselVaughan1983.U1391.theorem_U1391
#print axioms LeanLab.RieselVaughan1983.U1391.corollary19_U1391
#print axioms LeanLab.SchnirelmannBounds.U1391.vaughan1977_U1391
-- falsifier: a checkpoint list that overshoots must be rejected by the same checker
example : chk (LeanLab.Verifications.Top50.Bits.pm 3300001 >>> (67 + 1)) 67
    (popc 7 (LeanLab.Verifications.Top50.Bits.pm 3300001 % 2 ^ 68)) [(71, 1074, 2)] = false := by decide +kernel
example : chk (LeanLab.Verifications.Top50.Bits.pm 3300001 >>> (67 + 1)) 67
    (popc 7 (LeanLab.Verifications.Top50.Bits.pm 3300001 % 2 ^ 68)) [(70, 1074, 2)] = true := by decide +kernel
example : popc 7 (LeanLab.Verifications.Top50.Bits.pm 3300001 % 2 ^ 68) = 19 := by decide +kernel
example : popc 22 (LeanLab.Verifications.Top50.Bits.pm 3300001 % 2 ^ 3300000) = 236900 := by decide +kernel
