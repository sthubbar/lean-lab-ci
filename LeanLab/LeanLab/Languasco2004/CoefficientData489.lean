/-
Coefficient data for PP1993 page 44 display 3.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.MinorData489

namespace LeanLab.Languasco2004.Decomp489d
open Finset Real MeasureTheory Decomp279b Decomp413a
open scoped ArithmeticFunction.vonMangoldt
noncomputable section

/-- Page 44 display 3, Parseval data: the squared weights of S1. -/
def firstWeight (N Y : ℝ) : ℝ := ∑ n ∈ Ioc ⌊N - Y⌋₊ ⌊N⌋₊, (Λ n) ^ 2

/-- Page 44 display 3, Parseval data: the squared weights of S2. -/
def secondWeight (Y : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊Y⌋₊, (Λ n) ^ 2


end
end LeanLab.Languasco2004.Decomp489d
