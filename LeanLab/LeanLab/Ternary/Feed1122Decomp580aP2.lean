/-
Split of `prop52_finset`, burst-20261122 session S144.
Helfgott, The ternary Goldbach conjecture is true, arXiv 1312.7748v2, Proposition 5.2,
proof on pages 34 and 35. The proof has two stages:
* display (5.6) together with [Bom74, Thm. 7A] bounds the integral over the major arcs by
  the maximal quotient of `G_q` values times a sum over the Farey arcs of level `Q` and `2Q`;
* the Farey arcs of half width `δ₀Q/2qx` for odd `q ≤ Q` and `δ₀Q/qx` for even `q ≤ 2Q`
  do not overlap, so that sum is at most `∫_{R/Z} |S|² = Σ |a_n|²`.
The glue `prop52_finset_of_leaves` is sorry free.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Feed1122Decomp580a

namespace LeanLab.Ternary.Task580
open MeasureTheory

/-- LEAF: Proposition 5.2 proof, Helfgott 1312.7748v2 pages 34 and 35, display (5.6)
followed by the two bounds from [Bom74, Thm. 7A] on page 35. Class HARD.
The integral of `|S|²` over the arcs `M_{δ₀,Q₀}` is at most the maximal quotient `M` times
`Σ_{q ≤ Q odd} ∫_{|α| ≤ δ₀Q/2qx} Σ_{(b,q)=1} |S(b/q+α)|² dα
 + Σ_{q ≤ 2Q even} ∫_{|α| ≤ δ₀Q/qx} Σ_{(b,q)=1} |S(b/q+α)|² dα`, with `Q = √(x/2δ₀)`. -/
theorem prop52_majorArcs_le_farey (A : Finset ℕ) (a : ℕ → ℂ) (x δ Q₀ : ℝ)
    (hx : 0 < x) (hδ : 1 ≤ δ) (hQ₀ : 1 ≤ Q₀) (hsize : δ * Q₀ ^ 2 ≤ x / 2)
    (hsupport : ∀ n ∈ A, ¬n.Prime ∨ (n : ℝ) ≤ Real.sqrt x → a n = 0)
    (M : ℝ)
    (hM : ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ 2 * Q₀ → Even q → ∀ s : ℝ, 1 ≤ s →
      s ≤ 2 * Q₀ / q →
        sieveG q (2 * Q₀ / (s * q)) / sieveG q (2 * Real.sqrt (x / (2 * δ)) / (s * q)) ≤ M) :
    (∫ α in majorArcs x δ Q₀ ∩ Set.Ioc (0 : ℝ) 1,
      ‖∑ n ∈ A, a n * LeanLab.Ternary.MMS.e ((n : ℝ) * α)‖ ^ 2) ≤
      M * ((∑ q ∈ (Finset.Icc 1 ⌊Real.sqrt (x / (2 * δ))⌋₊).filter (fun q => Odd q),
          ∫ α in (-(δ * Real.sqrt (x / (2 * δ)) / (2 * q * x)))..
            (δ * Real.sqrt (x / (2 * δ)) / (2 * q * x)),
            ∑ b ∈ (Finset.Icc 1 q).filter (fun b => Nat.Coprime b q),
              ‖∑ n ∈ A, a n * LeanLab.Ternary.MMS.e ((n : ℝ) * ((b : ℝ) / q + α))‖ ^ 2) +
        (∑ q ∈ (Finset.Icc 1 ⌊2 * Real.sqrt (x / (2 * δ))⌋₊).filter (fun q => Even q),
          ∫ α in (-(δ * Real.sqrt (x / (2 * δ)) / (q * x)))..
            (δ * Real.sqrt (x / (2 * δ)) / (q * x)),
            ∑ b ∈ (Finset.Icc 1 q).filter (fun b => Nat.Coprime b q),
              ‖∑ n ∈ A, a n * LeanLab.Ternary.MMS.e ((n : ℝ) * ((b : ℝ) / q + α))‖ ^ 2)) := by
  sorry

/-- LEAF: Proposition 5.2 proof, Helfgott 1312.7748v2 page 35, the non overlap of the
intervals `(b/q − δ₀Q/2qx, b/q + δ₀Q/2qx)` for odd `q ≤ Q` and `(b/q − δ₀Q/qx, b/q + δ₀Q/qx)`
for even `q ≤ 2Q`, together with `∫_{R/Z} |S(α)|² dα = Σ |a_n|²`, last display of page 35.
Class MEDIUM. -/
theorem prop52_farey_le_parseval (A : Finset ℕ) (a : ℕ → ℂ) (x δ Q₀ : ℝ)
    (hx : 0 < x) (hδ : 1 ≤ δ) (hQ₀ : 1 ≤ Q₀) (hsize : δ * Q₀ ^ 2 ≤ x / 2) :
    (∑ q ∈ (Finset.Icc 1 ⌊Real.sqrt (x / (2 * δ))⌋₊).filter (fun q => Odd q),
          ∫ α in (-(δ * Real.sqrt (x / (2 * δ)) / (2 * q * x)))..
            (δ * Real.sqrt (x / (2 * δ)) / (2 * q * x)),
            ∑ b ∈ (Finset.Icc 1 q).filter (fun b => Nat.Coprime b q),
              ‖∑ n ∈ A, a n * LeanLab.Ternary.MMS.e ((n : ℝ) * ((b : ℝ) / q + α))‖ ^ 2) +
        (∑ q ∈ (Finset.Icc 1 ⌊2 * Real.sqrt (x / (2 * δ))⌋₊).filter (fun q => Even q),
          ∫ α in (-(δ * Real.sqrt (x / (2 * δ)) / (q * x)))..
            (δ * Real.sqrt (x / (2 * δ)) / (q * x)),
            ∑ b ∈ (Finset.Icc 1 q).filter (fun b => Nat.Coprime b q),
              ‖∑ n ∈ A, a n * LeanLab.Ternary.MMS.e ((n : ℝ) * ((b : ℝ) / q + α))‖ ^ 2) ≤
      ∑ n ∈ A, ‖a n‖ ^ 2 := by
  sorry

/-- `G_q(R) ≥ 0`, immediate from (5.5) since every summand `μ²(r)/φ(r)` is nonnegative. -/
theorem sieveG_nonneg (q : ℕ) (R : ℝ) : 0 ≤ sieveG q R := by
  unfold sieveG
  exact Finset.sum_nonneg fun r _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- Proposition 5.2, Helfgott 1312.7748v2 page 33, for finitely supported coefficients.
This is the statement of `prop52_finset`, copied verbatim.
CONDITIONAL ON `prop52_majorArcs_le_farey` and `prop52_farey_le_parseval`. -/
theorem prop52_finset_of_leaves (A : Finset ℕ) (a : ℕ → ℂ) (x δ Q₀ : ℝ)
    (hx : 0 < x) (hδ : 1 ≤ δ) (hQ₀ : 1 ≤ Q₀) (hsize : δ * Q₀ ^ 2 ≤ x / 2)
    (hsupport : ∀ n ∈ A, ¬n.Prime ∨ (n : ℝ) ≤ Real.sqrt x → a n = 0)
    (M : ℝ)
    (hM : ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ 2 * Q₀ → Even q → ∀ s : ℝ, 1 ≤ s →
      s ≤ 2 * Q₀ / q →
        sieveG q (2 * Q₀ / (s * q)) / sieveG q (2 * Real.sqrt (x / (2 * δ)) / (s * q)) ≤ M) :
    (∫ α in majorArcs x δ Q₀ ∩ Set.Ioc (0 : ℝ) 1,
      ‖∑ n ∈ A, a n * LeanLab.Ternary.MMS.e ((n : ℝ) * α)‖ ^ 2) ≤
      M * ∑ n ∈ A, ‖a n‖ ^ 2 := by
  have hM0 : 0 ≤ M := by
    have h := hM 2 (by norm_num) (by push_cast; linarith) even_two 1 le_rfl
      (by push_cast; rw [le_div_iff₀ (by norm_num)]; linarith)
    exact le_trans (div_nonneg (sieveG_nonneg _ _) (sieveG_nonneg _ _)) h
  refine le_trans (prop52_majorArcs_le_farey A a x δ Q₀ hx hδ hQ₀ hsize hsupport M hM) ?_
  exact mul_le_mul_of_nonneg_left
    (prop52_farey_le_parseval A a x δ Q₀ hx hδ hQ₀ hsize) hM0

end LeanLab.Ternary.Task580
