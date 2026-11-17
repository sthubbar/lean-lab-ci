/-
Split of theorem leaf_schur_kernel_comparison561 in
LeanLab.BHP1997.SPLIT_leaf_kernel_schur561: display 2.10 of page 8, the
Schur comparison for the weighted minor arc kernel. What is split here is the
pointwise two term geometric mean step on the four moduli, the change of
variable that makes the two crossed terms equal, the integral comparison that
follows from them, the restriction of the complete long energy to the minor
arc, and the pass that carries the pointwise short fibre bound through the
outer integral. The constant one is exhibited, so no optimization is left.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_kernel_schur561

set_option autoImplicit false

namespace LeanLab.BHP1997.Decomp561e
open Classical Complex Thm2 MeasureTheory Set Decomp561d

/-- LEAF. The pointwise two term geometric mean step. For four nonnegative
reals the product of all four is at most the average of the two crossed
squares, which is the inequality between the geometric and the arithmetic mean
applied to the two products. No integral, no set and no constant appears. -/
theorem leaf_four_moduli_amgm561 (p q r s : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    p * q * r * s ≤ (p ^ 2 * s ^ 2 + q ^ 2 * r ^ 2) / 2 := by
  have hps : 0 ≤ p * s := mul_nonneg hp hs
  have hqr : 0 ≤ q * r := mul_nonneg hq hr
  have hsq : 0 ≤ (p * s - q * r) ^ 2 := sq_nonneg _
  nlinarith

/-- LEAF. The change of variable in the crossed term. The kernel weight is
unchanged when the sign of its argument flips, so exchanging the two names of
integration turns the term with the short power of the outer variable into the
term with the short power of the inner variable. This is an identity for the
double integral over the symmetric product of the minor arc with itself. -/
theorem leaf_kernel_double_integral_transpose561 (ε D x : ℝ) (a b : ℕ → ℂ) :
    (∫ t in minor512 ε D x, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ ^ 2 *
          ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ ^ 2 *
            kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s)) =
      (∫ t in minor512 ε D x, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ ^ 2 *
          ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ ^ 2 *
            kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s)) := by
  sorry

/-- LEAF. The integral comparison. Integrating the pointwise geometric mean
step and using the change of variable of the crossed term leaves a single
double integral of the squared long modulus against the squared short modulus
and the kernel. Only nonnegativity and monotonicity of the set integral are
used; the weighted short energy bound is not a hypothesis here. -/
theorem leaf_schur_double_integral_le561 (ε D x : ℝ) (a b : ℕ → ℂ) :
    (∫ t in minor512 ε D x, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ * ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a s‖ * ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ * ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ *
          kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s)) ≤
      (∫ t in minor512 ε D x, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ ^ 2 * ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ ^ 2 *
          kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s)) := by
  sorry

/-- LEAF. The long energy on the minor arc. The minor arc is a subset of the
period, so the long polynomial energy restricted to the minor arc is at most
the complete long energy. This is subset monotonicity for a nonnegative
integrand and carries no kernel, no short polynomial and no constant. -/
theorem leaf_long_energy_minor_le561 (ε D x : ℝ) (a : ℕ → ℂ) :
    (∫ t in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ ^ 2) ≤
      longEnergy561 ε x a := by
  sorry

/-- LEAF. The pointwise short fibre bound carried through the outer integral.
Fixing the outer variable leaves the short squared modulus against the kernel
inside the given uniform bound, and replacing the inner integral by that bound
factor by factor keeps the nonnegative long squared modulus. The result is the
same double integral dominated by the bound times the long energy on the minor
arc. The uniform bound is a hypothesis, so this step is strictly weaker than
the target. -/
theorem leaf_weighted_short_fibre_le561 (ε D x : ℝ) (a b : ℕ → ℂ) (W : ℝ)
    (hW : 0 ≤ W)
    (hE : ∀ t : ℝ, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ ^ 2 *
          kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s) ≤
      Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W) :
    (∫ t in minor512 ε D x, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ ^ 2 * ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ ^ 2 *
          kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s)) ≤
      Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W *
        (∫ t in minor512 ε D x,
          ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ ^ 2) := by
  sorry

/-- The split assembly: display 2.10 of page 8 with constant one, proved
from the four leaves above and with no direct admission. -/
theorem leaf_schur_kernel_comparison561_split :
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
  refine ⟨1, le_rfl, ?_⟩
  intro ε D x a b hH W hW hE
  have h1 := leaf_schur_double_integral_le561 ε D x a b
  have h2 := leaf_weighted_short_fibre_le561 ε D x a b W hW hE
  have hC0 : 0 ≤ Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h3 := mul_le_mul_of_nonneg_left (leaf_long_energy_minor_le561 ε D x a) hC0
  have h4 : Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W * longEnergy561 ε x a
      = 1 * longEnergy561 ε x a * Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W := by
    ring
  exact h1.trans (h2.trans (h3.trans (le_of_eq h4)))

end LeanLab.BHP1997.Decomp561e
