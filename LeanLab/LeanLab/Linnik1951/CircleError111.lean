/-
P0093 Linnik 1951, pages 155 to 166, Sections 3 to 9. The two arc estimates left
open by the SPLIT of error_bound111 in Decomp111.
AI wrote the Lean code. Binary Goldbach is open.

The two theorems below are the major arc and the exceptional arc estimates of
P0093 Section 10, kept in their own file because Decomp111 must stay free of
new admissions: Decomp111 proves error_bound111 from them and from the proved
circle partition and minor arc bound of CircleSplit111.

The two definitions are renamed copies, suffix Split111, of singularSeries111 and
mainTerm111 of Decomp111, for the same import cycle reason as the _up111 copies
in CircleSplit111: Decomp111 imports this file, so this file cannot import
Decomp111, and a copy with the same body is definitionally equal, which lets
Decomp111 apply the two leaves below without transport lemmas. The arc sets and
the contribution are the _up111 copies of CircleSplit111, again defeq copies of
majorArcsSplit111, exceptionalArcsSplit111, arcContributionSplit111 and
scale111 of Decomp111.
-/
import LeanLab.Linnik1951.CircleSplit111
import LeanLab.Perelli1996.Sing

namespace LeanLab.Linnik1951

open LeanLab.Linnik LeanLab.DERZ1997
open Finset

/-! Ported from Decomp111. -/
section

/-- P0093 page 168, equation 10.6. Local copy of singularSeries111. -/
noncomputable def singularSeriesSplit111 (n : ℕ) : ℝ :=
  ∏' p : Nat.Primes, if (p : ℕ) ∣ n then
    1 + 1 / (((p : ℕ) : ℝ) - 1) else 1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2

/-- P0093 page 168 after equation 10.7, with multiplicity of exponent tuples.
Local copy of mainTerm111. -/
noncomputable def mainTermSplit111 (k N : ℕ) : ℝ := by
  classical
  exact ∑ ν ∈ (Finset.univ.filter fun ν : Fin k → Fin (N + 1) =>
    (∀ i, 1 ≤ (ν i).val) ∧ 2 ≤ N - ∑ i, 2 ^ (ν i).val ∧
      Even (N - ∑ i, 2 ^ (ν i).val)),
    singularSeriesSplit111 (N - ∑ i, 2 ^ (ν i).val) *
      (N - ∑ i, 2 ^ (ν i).val : ℕ) / Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ) ^ 2

end

/-- LEAF: P0093 Sections 3 to 6, pages 155 to 161, the GRH Mellin estimate 5.2
on page 159, and Section 8 equations 8.1 and 8.2 on page 165 with equations
10.5 to 10.7 on page 168. For fixed k the major arc integral equals the
singular series main term up to an error that is arbitrarily small relative to
the scale. This is the major arc estimate of the circle method under GRH. -/
theorem major_error_leaf111 (hG : GRH) (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContribution280_up111 k N (majorArcs280_up111 N) - mainTermSplit111 k N| ≤
        ε * scale111_up111 k N := by
  sorry

/-- LEAF: P0093 pages 162 to 166, Lemmas 4 to 7, equations 7.6, 9.1 and 9.2.
Under GRH one absolute eta makes the set where the damped power of two series is
large so small that its minor arc contribution is arbitrarily small relative to
the scale for each fixed k. This is the exceptional arc estimate. -/
theorem exceptional_error_leaf111 (hG : GRH) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ k : ℕ, 3 ≤ k →
      ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
        |arcContribution280_up111 k N (exceptionalArcs280_up111 N η)| ≤
          ε * scale111_up111 k N := by
  sorry

end LeanLab.Linnik1951
