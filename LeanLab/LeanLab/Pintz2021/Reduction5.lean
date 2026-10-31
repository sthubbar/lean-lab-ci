/-
P0054 J. Pintz 2021, Section 5: Theorem 5 with (1.6) and (1.7) proved.
Unit U-6771, session 20261020T2317Z-cloud53.

`Section5MajorInput ε` takes `R(2m²)` from the explicit `S` of (1.1) with `X = N²`, a measurable
set of minor arcs `mi`, the minor arc first moment (5.11) as an input, and the major arc output
(5.16) with Case 1 (5.14). `section5Input_of_major` derives `Section5Input ε`, so
`theorem5_of_major`: Theorem 5 is CONDITIONAL ON (5.11) and the major arc output only.
The step (5.10) to (5.11), Hölder with `∫|f|⁴ ≪ N² L^c`, is not formalized here.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-21.
-/
import Mathlib
import LeanLab.Pintz2021.Reduction3

namespace LeanLab.Pintz2021.Reduction5

open Real Finset LeanLab.ExceptionalSet
open LeanLab.Pintz2021.Applications LeanLab.Pintz2021.MinorArcs LeanLab.Pintz2021.Reduction3

/-- The inputs of Section 5 that remain, for all `N > N₀`, `X = N²`: some `X₁` and measurable
minor arcs `mi`; (5.11) `∑_{m ≤ N} ‖R₂(2m²)‖ ≤ K X N^{4/5} L^c`; and (5.16) with Theorem 2, the
Siegel case and Case 1 (5.14): `Re R₁(2m²) > X^{1-ε}` unless `R₀ ∣ C m²` for one of at most `M`
moduli `R₀ ≥ P* = X^{7/25}`. -/
def Section5MajorInput (ε : ℝ) : Prop :=
  ∃ (K : ℝ) (c C M N0 : ℕ), 0 < C ∧ ∀ N : ℕ, N0 < N → ∃ (X1 : ℝ) (mi : Set ℝ) (𝓡 : Finset ℕ),
    MeasurableSet mi ∧
    ∑ m ∈ Icc 1 N, ‖R2 (S X1 ((N : ℝ) ^ 2)) mi (2 * m ^ 2)‖ ≤
      K * (N : ℝ) ^ 2 * (N : ℝ) ^ (4 / 5 : ℝ) * Real.log ((N : ℝ) ^ 2) ^ c ∧
    (∀ m ∈ Icc 1 N, (R1 (S X1 ((N : ℝ) ^ 2)) mi (2 * m ^ 2)).re ≤ ((N : ℝ) ^ 2) ^ (1 - ε) →
      ∃ R0 ∈ 𝓡, R0 ∣ C * m ^ 2) ∧
    (∀ R0 ∈ 𝓡, ((N : ℝ) ^ 2) ^ (7 / 25 : ℝ) ≤ R0) ∧ 𝓡.card ≤ M

theorem section5Input_of_major {ε : ℝ} (h : Section5MajorInput ε) : Section5Input ε := by
  obtain ⟨K, c, C, M, N0, hC, hin⟩ := h
  refine ⟨K, c, C, M, N0, hC, fun N hN => ?_⟩
  obtain ⟨X1, mi, 𝓡, hmi, hMi, hMa, hP, hM⟩ := hin N hN
  refine ⟨fun m => R1 (S X1 ((N : ℝ) ^ 2)) mi (2 * m ^ 2),
    fun m => R2 (S X1 ((N : ℝ) ^ 2)) mi (2 * m ^ 2), 𝓡, ?_, hMi, hMa, hP, hM⟩
  intro m _ hpos
  rw [R1_add_R2 _ (continuous_S X1 _) mi hmi] at hpos
  exact goldbach_of_re_pos X1 _ _ hpos

/-- CONDITIONAL ON `Section5MajorInput ε` for every `ε > 0`: Theorem 5, `E₂(N) ≪_ε N^{4/5+ε}`. -/
theorem theorem5_of_major (h : ∀ ε : ℝ, 0 < ε → Section5MajorInput ε) :
    LeanLab.ExceptionalSet.Pintz2021.Theorem5 :=
  theorem5_of_section5Input fun ε hε => section5Input_of_major (h ε hε)

end LeanLab.Pintz2021.Reduction5

#print axioms LeanLab.Pintz2021.Reduction5.section5Input_of_major
#print axioms LeanLab.Pintz2021.Reduction5.theorem5_of_major

