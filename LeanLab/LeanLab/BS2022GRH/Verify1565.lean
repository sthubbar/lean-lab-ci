/-
BS2022GRH, P0021, unit U-1565, T1 VERIFY falsifier for Q-1561a.

The journal, Ramanujan J. 64 (2024), pp. 1214 and 1227, prints
U_N = e^{-γ} ∏_{p>2}(1 − 1/(p−1)²) ∏_{p>2, p|N}(p−1)/(p−2), and Lemma 10 says
V(x) = ∏_{p<x, p∤N}(1 − 1/(p−1)) = U_N/log x · (1 + small). Since N is even, p = 2 is not in
the product. The algebraic step below, factor by factor, is
1 − 1/(p−1) = (1 − 1/p)(1 − 1/(p−1)²) for p > 2, so over the odd primes below x the product
is ∏_{2<p<x}(1 − 1/p) times a twin-prime partial product, and ∏_{2<p<x}(1 − 1/p) is
(1 − 1/2)⁻¹ = 2 times the full Mertens product ∏_{p<x}(1 − 1/p) ~ e^{-γ}/log x.
Hence V(x) log x → 2e^{-γ} C₂ Π_N, and the printed U_N lacks the factor 2.

Plain-math twins: `factor_identity` is the displayed identity for real p > 2;
`prod_identity` is its product over any finite set of naturals above 2; `drop_two` is
∏_{p∈S}(1 − 1/p) = 2 · ∏_{p∈insert 2 S}(1 − 1/p) when 2 ∉ S. Vacuity: `vacuity` instantiates
`prod_identity` at S = {3, 5, 7}.

AI-written Lean code, Claude, for the Lean Lab, run 20261027T0004Z-17012, unit U-1565.
Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.BS2022GRH.Verify1565
open Finset

theorem factor_identity (p : ℝ) (hp : 2 < p) :
    1 - 1 / (p - 1) = (1 - 1 / p) * (1 - 1 / (p - 1) ^ 2) := by
  have h1 : p - 1 ≠ 0 := by linarith
  have h0 : p ≠ 0 := by linarith
  field_simp
  ring

theorem prod_identity (S : Finset ℕ) (h : ∀ p ∈ S, 2 < p) :
    ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1)) =
      (∏ p ∈ S, (1 - 1 / (p : ℝ))) * ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun p hp => ?_
  exact factor_identity p (by exact_mod_cast h p hp)

theorem drop_two (S : Finset ℕ) (h2 : 2 ∉ S) :
    ∏ p ∈ S, (1 - 1 / (p : ℝ)) = 2 * ∏ p ∈ insert 2 S, (1 - 1 / (p : ℝ)) := by
  rw [prod_insert h2]
  norm_num
  ring

theorem vacuity :
    ∏ p ∈ ({3, 5, 7} : Finset ℕ), (1 - 1 / ((p : ℝ) - 1)) =
      (∏ p ∈ ({3, 5, 7} : Finset ℕ), (1 - 1 / (p : ℝ))) *
        ∏ p ∈ ({3, 5, 7} : Finset ℕ), (1 - 1 / ((p : ℝ) - 1) ^ 2) :=
  prod_identity _ (by decide)

end LeanLab.BS2022GRH.Verify1565

#print axioms LeanLab.BS2022GRH.Verify1565.factor_identity
#print axioms LeanLab.BS2022GRH.Verify1565.prod_identity
#print axioms LeanLab.BS2022GRH.Verify1565.drop_two
#print axioms LeanLab.BS2022GRH.Verify1565.vacuity
