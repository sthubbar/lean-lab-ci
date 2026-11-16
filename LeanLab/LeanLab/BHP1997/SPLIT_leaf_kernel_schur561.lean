/-
Split of theorem leaf_kernel_schur561 in LeanLab.BHP1997.Decomp561e: the
periodic even-frequency kernel reduction of display 2.10. The finite
geometric kernel bound for one even progression is already available; what is
split here is the fibre-count comparison for the even frequency set, the
finite Fourier double integral rearrangement of the minor arc sum, the shift
read back of the weighted short energy, and the two integral Cauchy steps.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561e

set_option autoImplicit false

namespace LeanLab.BHP1997.Decomp561e
open Classical Complex Thm2 MeasureTheory Set Decomp561d

/-- LEAF. Fibre count and pointwise kernel bound. The even frequencies in the
closed integer range from the ceiling of x to the floor of x plus H form a
single even arithmetic progression of at most H terms, so the exact periodic
Dirichlet kernel of that finite progression is at most kernelWeight561 H, both
at resonance and away from it. This is a finite trigonometric inequality with
no energy, no minor arc and no constant K in it. -/
theorem leaf_even_frequency_kernel561 (ε x : ℝ)
    (hH : 2 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) :
    ∀ u : ℝ, ‖∑ N ∈ frequencies512 ε x,
        @fourier 1 (N : ℤ) (u : AddCircle (1 : ℝ))‖ ≤
      kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) u := by
  sorry

/-- LEAF. The finite Fourier double integral rearrangement. Expanding each
squared modulus of the minor arc sum and summing the characters over the even
frequency set turns the minor error into one double integral of the two
polynomial moduli against the pointwise kernel. Only the modulus of the
summed kernel is used, so this step is an integral rearrangement plus a
triangle inequality and it carries no constant and no weighted energy bound. -/
theorem leaf_minor_kernel_double_integral561 (ε D x : ℝ) (a b : ℕ → ℂ)
    (hH : 2 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))))
    (hkern : ∀ u : ℝ, ‖∑ N ∈ frequencies512 ε x,
        @fourier 1 (N : ℤ) (u : AddCircle (1 : ℝ))‖ ≤
      kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) u) :
    minorError512 ε D x a b ≤
      ∫ t in minor512 ε D x, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ * ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a s‖ * ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ * ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ *
          kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s) := by
  sorry

/-- LEAF. The shifted short energy step, one Cauchy inequality. For every
shift t the short polynomial modulus squared against the kernel at t minus s
is controlled by the square root of the complete short energy times the square
root of the uniform weighted energy bound W. The kernel is even, so the shift
may be read on either side, and the two Cauchy factors are the modulus of the
short polynomial and that modulus times the kernel. -/
theorem leaf_shifted_short_energy561 (ε D x : ℝ) (b : ℕ → ℂ)
    (hH : 2 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (W : ℝ) (hW : 0 ≤ W)
    (hWE : ∀ ζ : ℝ, weightedEnergy561 ε D x b ζ ≤ W) :
    ∀ t : ℝ, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ ^ 2 * kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s) ≤
      Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W := by
  sorry

/-- LEAF. The second Cauchy step, the Schur comparison. Splitting the product of
the four moduli as long at t with short at s against short at t with long at s,
then swapping the two integration variables in one factor, leaves a single
double integral of the long modulus squared times the shifted short energy.
Feeding in the shifted short energy bound gives the target comparison with a
universal constant. The energy bound is an explicit hypothesis, so this leaf is
strictly weaker than the target. -/
theorem leaf_schur_kernel_comparison561 :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ε D x : ℝ, ∀ a b : ℕ → ℂ,
      2 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) →
      ∀ W : ℝ, 0 ≤ W →
      (∀ t : ℝ, ∫ s in minor512 ε D x,
          ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ ^ 2 * kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s) ≤
        Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W) →
      ∫ t in minor512 ε D x, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ * ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a s‖ * ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ * ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ *
          kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s) ≤
        K * longEnergy561 ε x a * Real.sqrt (shortEnergy561 ε x b) *
          Real.sqrt W := by
  sorry

/-- Display 2.10, the exact expanded kernel reduction. CONDITIONAL ON the fibre
count, double integral rearrangement, shifted short energy and Schur comparison
leaves. No direct admission occurs in this assembly. -/
theorem leaf_kernel_schur561_split :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ε D x : ℝ, ∀ a b : ℕ → ℂ,
      2 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) →
      ∀ W : ℝ, 0 ≤ W → (∀ ζ : ℝ, weightedEnergy561 ε D x b ζ ≤ W) →
        minorError512 ε D x a b ≤
          K * longEnergy561 ε x a * Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W := by
  obtain ⟨K, hK, hQ⟩ := leaf_schur_kernel_comparison561
  refine ⟨K, hK, ?_⟩
  intro ε D x a b hH W hW hWE
  exact (leaf_minor_kernel_double_integral561 ε D x a b hH
          (leaf_even_frequency_kernel561 ε x hH)).trans
    (hQ ε D x a b hH W hW (leaf_shifted_short_energy561 ε D x b hH W hW hWE))

end LeanLab.BHP1997.Decomp561e
