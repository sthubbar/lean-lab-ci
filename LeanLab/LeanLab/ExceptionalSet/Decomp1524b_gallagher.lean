import Mathlib

open Complex Finset Real MeasureTheory

noncomputable def e (x : ℝ) : ℂ := cexp (2 * π * I * x)

noncomputable def trig (s : Finset ℤ) (a : ℤ → ℂ) (α : ℝ) : ℂ := ∑ n ∈ s, a n * e (n * α)
