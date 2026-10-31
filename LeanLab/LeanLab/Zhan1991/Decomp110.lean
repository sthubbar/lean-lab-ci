import LeanLab.Zhan1991.Statements
import LeanLab.Zhan1991.Theorems235

/-!
Theorem 1, P0068, pages 269 to 271.
AI wrote the Lean code. Goldbach is open.
The assembly is CONDITIONAL on the two named analytic leaves.
The major arc evaluation on page 271 cites Pan and Pan, reference 2.
-/

namespace LeanLab.Zhan1991

noncomputable section
open scoped BigOperators

/-- The unweighted prime sum used on page 270, with the lab window endpoints. -/
def primeSum110 (N : ℕ) (U α : ℝ) : ℂ :=
  ∑ p ∈ Win N U, ee ((p : ℝ) * α)

/-- The periodic major arcs on page 270, with Q₁ = log N ^ d and Q = U log N ^ -4. -/
def majorArcs110 (N : ℕ) (U d : ℝ) : Set ℝ :=
  {α | ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ Real.log N ^ d ∧
    ∃ a : ℤ, Int.gcd a q = 1 ∧ |α - (a : ℝ) / q| ≤ Real.log N ^ (4 : ℝ) / U}

/-- The real part of the major arc integral on pages 270 and 271. -/
def majorTerm110 (N : ℕ) (U d : ℝ) : ℝ :=
  (∫ α in Set.Icc (0 : ℝ) 1 ∩ majorArcs110 N U d,
    primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)).re

/-- LEAF. Page 271, the major arc display after 3.21.
The logarithmic cutoff can be made sufficiently large for an error of order U² log N ^ -4.
Source for the unproved analytic evaluation: Pan and Pan, reference 2 of P0068.
The periodic interval and inclusive endpoints must be justified with this leaf. -/
theorem major_evaluation110 :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d → ∀ c : ℝ, 0 < c →
      ∃ K N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
        |majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d
          - 3 * Sing N * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-3 : ℝ)|
          ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-4 : ℝ) := by
  sorry

/-- LEAF. Pages 269 and 270, displays 3.20 and 3.21.
Choose the logarithmic window exponent and arc cutoff so the minor contribution
is bounded by U² log N ^ -4. This includes the orthogonality identity for T.
The paper uses Theorems 2 and 3, Dirichlet approximation, and the second moment.
The cutoff d can be increased to meet the major arc threshold. -/
theorem minor_reduction110 (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ d c : ℝ, d₀ ≤ d ∧ 0 < c ∧ ∃ K N₀ : ℝ,
      ∀ N : ℕ, Odd N → N₀ ≤ N →
        |(T N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) : ℝ)
          - majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d|
          ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-4 : ℝ) := by
  sorry

/-- Theorem 1 with its exact cited Prop, assembled from the leaves.
CONDITIONAL on minor_reduction110 and major_evaluation110. -/
theorem theorem1_decomp110 : Theorem1 := by
  obtain ⟨d₀, hd₀, hmajor⟩ := major_evaluation110
  obtain ⟨d, c, hd, hc, Km, Nm, hminor⟩ := minor_reduction110 d₀ hd₀
  obtain ⟨KM, NM, hM⟩ := hmajor d hd c hc
  refine ⟨c, hc, Km + KM, max Nm NM, ?_⟩
  intro N hN hlarge
  have hm := hminor N hN ((le_max_left _ _).trans hlarge)
  have hM' := hM N hN ((le_max_right _ _).trans hlarge)
  calc
    _ ≤ |(T N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) : ℝ)
          - majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d| +
        |majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d
          - 3 * Sing N * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-3 : ℝ)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hm hM'
    _ = _ := by ring

end
end LeanLab.Zhan1991
