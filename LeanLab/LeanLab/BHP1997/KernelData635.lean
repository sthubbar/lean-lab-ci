/-
P0069 pages 5 to 9. Shared data for the finite kernel reduction.
Eight definitions moved unchanged from Decomp561e to remove its split import cycle.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561c
import LeanLab.BHP1997.Decomp561d

namespace LeanLab.BHP1997.Decomp561e
open Classical Complex Thm2 MeasureTheory Set Decomp561d

/-- P0069 page 5: S1 S2 e at frequency minus N. -/
noncomputable def integrand512 (ε x : ℝ) (a b : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t *
    polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t *
      @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))


/-- P0069 page 6: the even frequencies in K. -/
noncomputable def frequencies512 (ε x : ℝ) : Finset ℕ :=
  (Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
    (fun N => Even N)


/-- P0069 page 6 display 2.3: the minor arc mean square as a real quantity. -/
noncomputable def minorError512 (ε D x : ℝ) (a b : ℕ → ℂ) : ℝ :=
  ∑ N ∈ frequencies512 ε x,
    ‖∫ t in minor512 ε D x, integrand512 ε x a b N t‖ ^ 2


/-- P0069 page 6: H Y squared times the requested logarithmic saving. -/
noncomputable def scale512 (ε A x : ℝ) : ℝ :=
  x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
    length512 ε x ^ 2 * Real.log x ^ (-A - 7)


/-- P0069 page 9 before 2.11, the complete long polynomial energy. -/
noncomputable def longEnergy561 (ε x : ℝ) (a : ℕ → ℂ) : ℝ :=
  ∫ t in period512 ε x,
    ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ ^ 2

/-- P0069 page 9 before 2.11, the complete short polynomial energy. -/
noncomputable def shortEnergy561 (ε x : ℝ) (b : ℕ → ℂ) : ℝ :=
  ∫ t in period512 ε x,
    ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ ^ 2

/-- P0069 page 8 display 2.10, the periodic kernel majorant with both poles.
At resonance use H rather than the totalized reciprocal of zero. -/
noncomputable def kernelWeight561 (H t : ℝ) : ℝ :=
  if ‖((2 * t : ℝ) : AddCircle (1 : ℝ))‖ = 0 then H
  else min H (1 / ‖((2 * t : ℝ) : AddCircle (1 : ℝ))‖)

/-- P0069 page 8 display 2.10, the weighted short polynomial energy. -/
noncomputable def weightedEnergy561 (ε D x : ℝ) (b : ℕ → ℂ) (ζ : ℝ) : ℝ :=
  ∫ t in minor512 ε D x,
    ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ ^ 2 *
      kernelWeight561
        (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - ζ) ^ 2

end LeanLab.BHP1997.Decomp561e
