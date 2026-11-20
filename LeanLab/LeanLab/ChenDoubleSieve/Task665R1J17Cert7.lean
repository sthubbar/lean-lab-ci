import LeanLab.ChenDoubleSieve.Task665R1Core

/-!
Exact row two D2,17 certificate data for Wu 2004 page 26.
The parameters are Table 1 row two page 30.
The unchanged verifier is the Prove2Me R1J16 port, mission 87d77bf0.
The existing accepted theorem is LL_Decomp587j.r1j16_short.
Author kmehltretter82. Apache 2.0. Accepted 2026-11-19.
AI generated these independent trees and wrote the Lean assembly.
Binary Goldbach is open.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace LeanLab.ChenDoubleSieve.Task665R1
open LeanLab.Ported.Prove2Me.Decomp587jR1J16.SolBuchstabR1J16

def j17Tree56 : CTree :=
  (.S4 0 (.S4 0 (.S4 0 (.S4 0 .B .B .B .B) (.S3 1 (.S3 1 .B .B .B) .B .B) (.S3 0 .B .B .B) .B) (.S3 1 (.S3 1 (.S3 1 .B .B .B) .B .B) .B .I) (.S3 0 (.S2 1 (.S2 2 .B .I) .I) .I .I) .I) (.S3 1 (.S3 1 (.S2 0 (.S2 2 .B .I) .I) .I .I) .I .I) (.S3 0 .I .I .I) (.S4 0 .I .I .I .I))

theorem j17Check56 : checkJ17 2034396 2037312 j17Tree56 = true := by decide +kernel

#print axioms LeanLab.ChenDoubleSieve.Task665R1.j17Check56

def j17Tree57 : CTree :=
  (.S4 0 (.S4 0 .B (.S3 1 .B (.S2 3 .B .I) .I) (.S3 0 (.S3 0 .B .I .I) .I .I) .I) (.S3 1 (.S3 1 (.S3 1 .B .I .I) .I .I) .I .I) (.S3 0 .I .I .I) .I)

theorem j17Check57 : checkJ17 2037312 2083968 j17Tree57 = true := by decide +kernel

#print axioms LeanLab.ChenDoubleSieve.Task665R1.j17Check57

def j17Tree58 : CTree :=
  (.S4 0 .I .I .I .B)

theorem j17Check58 : checkJ17 2083968 2177280 j17Tree58 = true := by decide +kernel

#print axioms LeanLab.ChenDoubleSieve.Task665R1.j17Check58

def j17Tree59 : CTree :=
  (.S4 0 (.S4 0 .I .B .B .B) (.S3 1 .B .B .B) (.S2 1 .B .B) .B)

theorem j17Check59 : checkJ17 2177280 2363904 j17Tree59 = true := by decide +kernel

#print axioms LeanLab.ChenDoubleSieve.Task665R1.j17Check59

def j17Tree60 : CTree :=
  (.S4 0 .B .B .B .T)

theorem j17Check60 : checkJ17 2363904 2737152 j17Tree60 = true := by decide +kernel

#print axioms LeanLab.ChenDoubleSieve.Task665R1.j17Check60

def j17Tree61 : CTree :=
  .T

theorem j17Check61 : checkJ17 2737152 3483648 j17Tree61 = true := by decide +kernel

#print axioms LeanLab.ChenDoubleSieve.Task665R1.j17Check61

end LeanLab.ChenDoubleSieve.Task665R1
