import LeanLab.ChenDoubleSieve.Task661CellCore

/-!
Exact ordered cell certificates for Wu 2004 page 26.
The parameters are Table 1 row 1 page 30.
The verifier comes from Prove2Me mission 1e48f99d, author kmehltretter82,
Apache 2.0, accepted proof LL_Decomp587l.r0j16_short.
AI wrote the new bridges, certificate generators and interval assemblies.
Binary Goldbach is open.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task661
open Wu04Functional Task587
open LeanLab.Ported.Prove2Me.R0J16.SolBuchstabR0J16

def j19Tree0 : CTree :=
  (.S4 1 .B .B (.S3 1 .B .B .B) .B)

theorem j19Check0 : checkJ19 7245824 7415648 j19Tree0 = true := by decide +kernel

#print axioms LeanLab.ChenDoubleSieve.Task661.j19Check0

def j19Tree1 : CTree :=
  (.S4 1 (.S4 1 .B .B (.S2 0 .B (.S3 1 .B .B .B)) .B) (.S3 2 (.S3 2 .B .B (.S2 0 .B .B)) .B (.S3 2 .B .B .B)) (.S2 0 (.S3 1 .B .B .B) (.S3 1 .B (.S2 0 .B .I) .I)) (.S2 0 (.S4 1 .B .B .I .I) .I))

theorem j19Check1 : checkJ19 7415648 7500560 j19Tree1 = true := by decide +kernel

#print axioms LeanLab.ChenDoubleSieve.Task661.j19Check1

def j19Tree2 : CTree :=
  (.S4 1 (.S4 1 (.S4 1 .B .B .B (.S2 0 .Z .B)) (.S3 2 .B .B (.S2 0 .B .B)) (.S2 0 (.S3 1 .B .B (.S2 0 .B .B)) .B) .B) (.S3 2 (.S2 0 (.S3 2 .B .B (.S3 2 .B .B .B)) (.S3 2 (.S3 2 .B .B .B) .B .B)) (.S2 0 .B (.S2 0 .B (.S2 0 (.S2 1 .B .I) .I))) (.S2 0 (.S3 2 (.S3 2 .B .B .B) .B .B) (.S3 2 .B .I .I))) (.S2 0 (.S3 1 (.S2 0 .B (.S2 2 .B .I)) (.S2 0 .B .I) .I) .I) (.S4 1 (.S4 1 .B .I .I .I) .I .I .I))

theorem j19Check2 : checkJ19 7500560 7543016 j19Tree2 = true := by decide +kernel

#print axioms LeanLab.ChenDoubleSieve.Task661.j19Check2

def j19Tree3 : CTree :=
  (.S4 1 (.S4 1 (.S4 1 .B .B (.S3 1 .B .B .B) (.S2 0 .B .B)) (.S3 2 (.S3 2 .B .B .B) .B (.S2 0 .B .B)) (.S3 1 (.S2 0 .B .B) .B (.S3 1 .B .B .B)) (.S2 0 .B (.S4 1 .B .I .I .I))) (.S3 2 (.S2 0 (.S3 2 .B .B (.S2 0 .B (.S3 2 .B .B .B))) (.S2 0 (.S3 2 .B .B .B) (.S3 2 .B (.S2 0 .B .I) .I))) (.S2 0 (.S2 0 .B .B) (.S2 0 (.S2 1 (.S2 0 .B .I) .I) .I)) (.S2 0 (.S2 0 .B (.S3 2 .B .I .I)) .I)) (.S2 0 (.S2 0 (.S3 1 (.S3 1 .B .B .I) (.S2 2 (.S2 3 .B .I) .I) .I) .I) .I) .I)

theorem j19Check3 : checkJ19 7543016 7564244 j19Tree3 = true := by decide +kernel

#print axioms LeanLab.ChenDoubleSieve.Task661.j19Check3

def j19Tree4 : CTree :=
  (.S4 1 (.S4 1 (.S2 0 .B (.S4 1 (.S4 1 .B .B .B .B) (.S3 2 .B .B (.S2 0 .B .B)) (.S3 1 (.S2 0 .B .B) .B (.S3 1 .B .B .B)) .B)) (.S2 0 .B (.S3 2 (.S2 0 (.S3 2 .B .B (.S3 2 .B .B .B)) .B) (.S2 0 .B (.S2 0 .B .I)) (.S2 0 .B (.S3 2 .B .I .I)))) (.S3 1 (.S2 0 (.S3 1 (.S3 1 .B .B .B) .B (.S2 0 .B (.S3 1 .B .B .B))) (.S2 0 .B .I)) (.S2 0 .B (.S2 0 (.S2 0 .B .I) .I)) (.S2 0 (.S3 1 (.S3 1 (.S2 0 .B .B) .B .B) .B .B) .I)) (.S2 0 (.S2 0 (.S4 1 .B (.S3 2 .B .B .B) .B .B) (.S4 1 .B .B .I .I)) .I)) (.S3 2 (.S3 2 (.S2 0 (.S3 2 (.S3 2 .B .B .B) .B (.S3 2 (.S3 2 .B .B .B) .B (.S3 2 .B .B .B))) (.S3 2 (.S3 2 .B .B .B) (.S2 0 .B (.S2 0 .B .I)) (.S2 0 .B .I))) (.S2 0 .B (.S2 0 (.S2 1 .B .I) .I)) (.S3 2 (.S3 2 (.S3 2 .B .B .B) .B (.S3 2 .B .B .B)) (.S2 0 .B .I) (.S2 0 (.S3 2 (.S3 2 .B .B .B) .B .B) .I))) (.S2 0 (.S2 0 (.S2 0 (.S2 1 .B (.S2 2 .B .B)) (.S2 1 .B (.S2 2 .B (.S2 1 (.S2 2 .B .I) .I)))) (.S2 0 (.S2 1 (.S2 2 .B (.S2 1 .B .I)) (.S2 2 (.S2 1 .B .I) .I)) (.S2 1 (.S2 2 .B .I) .I))) (.S2 0 .I .I)) (.S2 0 (.S2 0 (.S3 2 (.S3 2 (.S3 2 .B .B .B) .B .B) (.S2 1 .B .I) (.S3 2 .B .I .I)) (.S3 2 (.S3 2 .B .I .I) .I .I)) .I)) (.S3 1 (.S2 0 (.S2 0 (.S2 2 (.S3 1 .B (.S2 0 (.S2 2 .B .I) .I) .I) .I) .I) .I) (.S2 0 (.S2 0 .I .I) (.S2 0 .I .I)) (.S2 0 .I .I)) (.S2 0 (.S4 1 .I .I .I .I) (.S4 1 .I .I .I .I)))

theorem j19Check4 : checkJ19 7564244 7585472 j19Tree4 = true := by decide +kernel

#print axioms LeanLab.ChenDoubleSieve.Task661.j19Check4

def j19Tree5 : CTree :=
  (.S4 1 (.S4 1 (.S2 0 .B (.S4 1 (.S4 1 .B .B .B .B) (.S2 0 .B (.S3 2 (.S2 0 .B .B) .B .B)) (.S3 1 (.S2 0 .B .B) .B .B) .B)) (.S2 0 (.S3 2 .B .B (.S3 2 .B .B (.S2 0 .B (.S3 2 .B .B .B)))) (.S3 2 (.S2 0 (.S3 2 .B .B (.S3 2 .B .B .B)) .B) (.S2 0 .B (.S2 0 (.S2 0 .B .I) .I)) (.S2 0 .B .I))) (.S3 1 (.S3 1 (.S2 0 (.S3 1 .B .B .B) (.S2 0 .B .I)) .B (.S3 1 (.S3 1 .B .B .B) (.S2 0 .B .I) (.S3 1 .B .B .B))) (.S2 0 .B .I) (.S2 0 (.S3 1 (.S3 1 .B .B .B) .B .B) .I)) (.S2 0 (.S2 0 .B (.S4 1 .B .B .I .I)) .I)) (.S2 0 (.S3 2 (.S3 2 (.S3 2 (.S3 2 .B .B .B) .B (.S3 2 (.S3 2 .B .B .B) .B (.S2 0 .B .B))) (.S2 0 .B .B) (.S3 2 (.S2 0 (.S3 2 .B .B (.S2 1 .B .B)) .B) .B (.S3 2 (.S3 2 .B .B .B) .B .B))) (.S2 0 (.S2 0 (.S2 1 .B (.S2 2 .B (.S2 1 .B .I))) (.S2 1 .B (.S2 2 .B .I))) (.S2 1 (.S2 2 (.S2 0 .B (.S2 1 .B .I)) .I) .I)) (.S2 0 (.S3 2 .B (.S2 1 (.S2 0 .B .I) .I) .I) .I)) (.S3 2 (.S3 2 (.S2 0 (.S3 2 (.S3 2 .B .B .B) (.S2 1 .B .I) .B) (.S3 2 .B .I .I)) (.S2 0 (.S2 1 (.S2 0 .B .I) .I) .I) .I) (.S2 0 .I .I) .I)) (.S3 1 (.S3 1 (.S3 1 (.S2 0 (.S2 0 .B .I) .I) .I .I) (.S2 0 .I .I) (.S2 0 .I .I)) (.S2 0 (.S2 0 .I .I) (.S2 0 .I .I)) (.S2 0 .I .I)) (.S2 0 (.S4 1 .I .I .I .I) (.S4 1 .I .I .I .I)))

theorem j19Check5 : checkJ19 7585472 7596086 j19Tree5 = true := by decide +kernel

#print axioms LeanLab.ChenDoubleSieve.Task661.j19Check5

def j19Tree6 : CTree :=
  (.S4 1 (.S2 0 (.S4 1 (.S4 1 .Z .Z .B (.S4 1 .B .B (.S3 1 .B .B .B) (.S2 0 .Z (.S2 0 .B .B)))) (.S3 2 .B .B (.S3 2 (.S3 2 (.S3 2 .B .B .B) .B (.S3 2 .B .B .B)) .B (.S2 0 .B (.S3 2 (.S3 2 .B .B .B) .B .B)))) (.S3 1 (.S2 0 (.S3 1 .B .B (.S3 1 .B .B (.S3 1 .B .B .B))) (.S3 1 (.S3 1 (.S2 0 .B .B) .B (.S3 1 .B .B .B)) .B .B)) (.S2 0 .B (.S2 0 .B (.S2 2 (.S2 3 .B .I) .I))) (.S3 1 (.S3 1 (.S3 1 .B .B .B) (.S2 0 .B .I) .B) (.S2 0 .B .I) (.S2 0 (.S2 0 .B .I) .I))) (.S4 1 .B (.S3 2 (.S3 2 (.S3 2 .B .B .B) .B .B) (.S2 0 .B .I) (.S2 0 .B .I)) (.S2 0 (.S2 0 .B .I) .I) .I)) (.S4 1 (.S4 1 (.S2 0 .B (.S4 1 (.S2 0 .B .B) (.S2 0 .B .B) (.S3 1 .B .B .B) .B)) (.S2 0 .B (.S3 2 (.S3 2 (.S2 0 .B .B) .B .B) .B .B)) (.S3 1 (.S3 1 (.S2 0 .B .B) .B (.S3 1 .B .B .B)) (.S2 0 .B (.S2 0 .B .I)) (.S2 0 (.S3 1 .B .B .B) .I)) (.S2 0 .B .I)) (.S3 2 (.S3 2 (.S2 0 (.S3 2 .B .B (.S3 2 .B .B .B)) .B) (.S2 0 .B (.S2 0 .B .I)) (.S3 2 (.S3 2 .B .B .B) (.S2 0 .B .I) .B)) (.S2 0 (.S2 0 .B (.S2 1 (.S2 2 .B .I) .I)) .I) (.S2 0 (.S2 0 (.S3 2 .B .B .I) .I) .I)) (.S3 1 (.S3 1 (.S2 0 (.S2 0 .B .I) .I) .I .I) .I .I) .I)) (.S2 0 (.S3 2 (.S3 2 (.S3 2 (.S3 2 (.S3 2 .B .B .B) .B (.S3 2 .B .B .B)) .B (.S2 0 (.S3 2 .B .B (.S3 2 .B .B .B)) (.S3 2 (.S3 2 (.S2 1 .B .B) .B .B) .B (.S3 2 .B .B .B)))) (.S2 0 (.S2 0 .B .B) (.S2 0 (.S2 1 .B .B) (.S2 1 .B .I))) (.S3 2 (.S3 2 (.S3 2 (.S2 0 .B .B) .B (.S2 0 (.S2 1 .B .B) .B)) .B (.S3 2 .B .B .B)) (.S2 0 .B (.S2 1 (.S2 0 .B .I) .I)) (.S3 2 (.S3 2 .B .B .B) (.S2 0 .B (.S2 1 .B .I)) (.S2 0 (.S3 2 .B .B .B) .I)))) (.S2 0 (.S2 0 (.S2 1 (.S2 2 .B (.S2 0 .B .B)) (.S2 2 (.S2 1 .B (.S2 2 (.S2 3 .B .I) .I)) .I)) (.S2 1 (.S2 2 (.S2 0 .B .B) (.S2 1 (.S2 2 (.S2 3 .B .I) .I) .I)) (.S2 2 (.S2 1 (.S2 2 (.S2 3 .B .I) .I) .I) .I))) (.S2 1 (.S2 2 (.S2 0 (.S2 0 .B (.S2 1 (.S2 2 .B .I) .I)) .I) .I) .I)) (.S3 2 (.S2 0 (.S2 1 (.S2 0 .B (.S3 2 .B .I .I)) .I) .I) (.S2 0 .I .I) .I)) (.S3 2 (.S2 0 (.S3 2 (.S2 0 (.S3 2 (.S3 2 (.S3 2 .B .B .B) .B .B) (.S2 1 .B .I) (.S2 1 .B .I)) (.S3 2 (.S2 1 .B .I) .I .I)) (.S2 1 (.S2 0 (.S2 1 (.S2 0 .B .I) .I) .I) .I) .I) .I) (.S2 0 .I .I) (.S2 0 .I .I))) (.S2 0 (.S2 0 (.S3 1 .I .I .I) (.S3 1 .I .I .I)) (.S2 0 (.S3 1 .I .I .I) (.S3 1 .I .I .I))) (.S2 0 (.S4 1 .I (.S2 0 .I .I) (.S2 0 .I .I) .I) (.S4 1 .I (.S2 0 .I .I) (.S2 0 .I .I) .I)))

theorem j19Check6 : checkJ19 7596086 7606700 j19Tree6 = true := by decide +kernel

#print axioms LeanLab.ChenDoubleSieve.Task661.j19Check6

def j19Tree7 : CTree :=
  (.S4 1 (.S2 0 (.S4 1 (.S4 1 .Z .Z .B (.S4 1 .B .B (.S3 1 .B .B .B) (.S2 0 .Z .B))) (.S3 2 .B .B (.S2 0 .B (.S3 2 (.S2 0 .B (.S3 2 .B .B .B)) .B (.S3 2 .B .B .B)))) (.S3 1 (.S2 0 (.S3 1 .B .B (.S3 1 .B .B (.S2 0 .B .B))) (.S3 1 (.S3 1 (.S3 1 .B .B .B) .B .B) .B .B)) (.S2 0 .B (.S2 0 .B (.S2 2 (.S2 0 .B .I) .I))) (.S2 0 (.S3 1 (.S3 1 (.S3 1 .B .B .B) .B .B) .B .B) .I)) (.S4 1 .B (.S2 0 (.S3 2 (.S3 2 (.S2 0 .B .B) .B .B) .B .B) .I) (.S3 1 (.S2 0 .B .I) .I .I) .I)) (.S4 1 (.S2 0 (.S4 1 .B (.S3 2 .B .B (.S2 0 .B (.S3 2 .B .B .B))) (.S3 1 (.S2 0 .B .B) .B .B) .B) (.S4 1 .B .B (.S3 1 .B .I .I) .I)) (.S2 0 (.S3 2 (.S3 2 (.S3 2 .B .B (.S2 0 .B .B)) .B (.S3 2 .B .B .B)) (.S2 0 .B (.S2 0 (.S2 1 .B .I) .I)) (.S3 2 .B .I .I)) (.S3 2 (.S2 0 .B .I) .I .I)) .I .I)) (.S2 0 (.S3 2 (.S3 2 (.S3 2 (.S3 2 (.S3 2 .B .B .B) .B (.S3 2 .B .B .B)) .B (.S2 0 (.S3 2 .B .B (.S3 2 .B .B .B)) (.S3 2 (.S3 2 .B .B .B) .B .B))) (.S2 0 (.S2 0 .B .B) (.S2 0 (.S2 1 .B (.S2 1 (.S2 2 .B .I) .I)) (.S2 1 .B .I))) (.S3 2 (.S3 2 (.S3 2 (.S2 0 .B .B) .B .B) .B (.S3 2 .B .B .B)) (.S2 0 .B (.S2 1 (.S2 0 .B .I) .I)) (.S3 2 (.S3 2 .B .B .B) (.S2 0 .B .I) (.S2 0 .B .I)))) (.S2 0 (.S2 0 (.S2 1 (.S2 2 .B .B) (.S2 2 .B .I)) (.S2 1 (.S2 2 .B .I) .I)) (.S2 1 (.S2 2 (.S2 0 (.S2 1 (.S2 2 (.S2 3 .B .I) .I) .I) .I) .I) .I)) (.S3 2 (.S2 0 (.S2 1 (.S2 0 .B .I) .I) .I) .I .I)) (.S3 2 (.S3 2 (.S2 0 (.S2 1 (.S2 0 .B (.S3 2 .B .I .I)) .I) .I) .I .I) (.S2 0 .I .I) (.S2 0 .I .I))) (.S2 0 (.S2 0 (.S3 1 .I .I .I) (.S3 1 .I .I .I)) (.S2 0 (.S3 1 .I .I .I) (.S3 1 .I .I .I))) (.S2 0 (.S4 1 .I .I .I .I) (.S4 1 .I .I (.S2 0 .I .I) .I)))

theorem j19Check7 : checkJ19 7606700 7612007 j19Tree7 = true := by decide +kernel

#print axioms LeanLab.ChenDoubleSieve.Task661.j19Check7

end LeanLab.ChenDoubleSieve.Task661
