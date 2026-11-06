/-
Principal and remainder data for PP1993 pages 43 and 45 display 7.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp279b

namespace LeanLab.Languasco2004.Decomp413b
open Finset Real MeasureTheory Decomp279b
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 43: the unweighted geometric sum T1. -/
def firstModel (N Y t : ℝ) : ℂ :=
  ∑ h ∈ Ioc ⌊N - Y⌋₊ ⌊N⌋₊, phase ((h : ℝ) * t)

/-- Page 43: the unweighted geometric sum T2. -/
def secondModel (Y t : ℝ) : ℂ :=
  ∑ k ∈ Icc 1 ⌊Y⌋₊, phase ((k : ℝ) * t)

/-- Page 45 display 7: the principal rational coefficient mu over phi. -/
def rationalWeight (q : ℕ) : ℂ :=
  (ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)

/-- Page 45 display 7: the S1 remainder at a rational centre. -/
def firstRemainder (N Y : ℝ) (q a : ℕ) (t : ℝ) : ℂ :=
  firstSum N Y ((a : ℝ) / q + t) - rationalWeight q * firstModel N Y t

/-- Page 45 display 7: the S2 remainder at a rational centre. -/
def secondRemainder (Y : ℝ) (q a : ℕ) (t : ℝ) : ℂ :=
  secondSum Y ((a : ℝ) / q + t) - rationalWeight q * secondModel Y t

/-- Pages 43 and 45: sum the rational arc integrals over the sealed period.
The explicit intersection records all finite endpoint conventions. -/
def rationalIntegral (N Y H B : ℝ) (m : ℕ) (F : ℕ → ℕ → ℝ → ℂ) : ℂ :=
  ∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊,
    ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
      ∫ t in {t : ℝ | |t| < Real.log N ^ (2 * B) / ((q : ℝ) * Y) ∧
          (a : ℝ) / q + t ∈ period H},
        F q a t * phase (-(m : ℝ) * ((a : ℝ) / q + t))

/-- Page 45 display 7: the term containing both principal factors. -/
def principalCoefficient (N Y H B : ℝ) (m : ℕ) : ℂ :=
  rationalIntegral N Y H B m (fun q _ t =>
    rationalWeight q ^ 2 * firstModel N Y t * secondModel Y t)

/-- Page 45 display 7: the sum of the other three product terms. -/
def remainderCoefficient (N Y H B : ℝ) (m : ℕ) : ℂ :=
  rationalIntegral N Y H B m (fun q a t =>
    rationalWeight q * firstModel N Y t * secondRemainder Y q a t +
    rationalWeight q * secondModel Y t * firstRemainder N Y q a t +
    firstRemainder N Y q a t * secondRemainder Y q a t)

/-- Page 45 display 7: the four product terms give the original integrand. -/
theorem product_decomposition (N Y : ℝ) (q a : ℕ) (t : ℝ) :
    firstSum N Y ((a : ℝ) / q + t) * secondSum Y ((a : ℝ) / q + t) =
      rationalWeight q ^ 2 * firstModel N Y t * secondModel Y t +
      (rationalWeight q * firstModel N Y t * secondRemainder Y q a t +
      rationalWeight q * secondModel Y t * firstRemainder N Y q a t +
      firstRemainder N Y q a t * secondRemainder Y q a t) := by
  unfold firstRemainder secondRemainder
  ring

#print axioms product_decomposition
end
end LeanLab.Languasco2004.Decomp413b
