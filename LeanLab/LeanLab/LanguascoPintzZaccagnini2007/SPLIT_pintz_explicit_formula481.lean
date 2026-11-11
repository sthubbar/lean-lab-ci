import LeanLab.LanguascoPintzZaccagnini2007.Decomp481a

/-!
Split of `pintz_explicit_formula481` of `Decomp481a`, the explicit formula input on page 5 of the
source preprint, Lemma 4.1. The target states that one can choose positive decay and epsilon
constants, a uniform remainder constant, thresholds in `H` and `T`, an epsilon dependent divisor
constant `Cε`, and then, at each scale `X`, an admissible major arc parameter `P`, an indexed family
of exceptional zeros with the pole at index zero and the analytic multiplicity respected, and
generalised singular series coefficients, so that the real major arc integral differs from the signed
Gamma pair sum by at most `B * (X exp (-c H) + X / sqrt T)`.

The statement is one long existential chain, and the file splits it into the three steps it is made
of. `leaf_admissible_zero_family481` provides the thresholds and, at each scale, an admissible `P`
together with the zero family: the pole at index zero, the exceptional box membership of every other
index, and the multiplicity bound. `leaf_singular_series_coefficients481` provides the coefficients
for any zero family already in hand, with the three properties the statement asks of them: the value
`S(n)` at the pole pair, the pointwise bound by `S(n)`, and the smallness off the two divisibility
conditions. `leaf_remainder_bound481` provides the constants and, for any zero family and any
coefficients satisfying those properties, the remainder estimate itself.

That last leaf is uniform in the data it is given, which is what the source asserts: the formula is
stated for the zeros in box (8) at the given `H` and `T`, whatever family those zeros form, and the
coefficients are only constrained by the properties listed below the display. So the leaves split
the choices of the statement from its estimate, and neither restates the other.

`pintz_explicit_formula481_split` below is proved from the three leaves with no `sorry`, and does not
use `pintz_explicit_formula481`.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real
open scoped Classical

noncomputable section

/-- LEAF. The data step: large enough thresholds in `H` and `T`, at least one, and at every scale an
admissible major arc parameter together with an indexed family of exceptional zeros whose index zero
is the pole, whose other indices lie in the box of primitive zeros of conductors at most `P` with real
part in the strip and imaginary part bounded by `T`, and in which no character and zero pair is
repeated beyond its analytic order. Nothing is asserted here about the major arc integral or the
coefficients. -/
theorem leaf_admissible_zero_family481 :
    ∃ H₀ T₀ : ℝ, 1 ≤ H₀ ∧ 1 ≤ T₀ ∧ ∀ H T : ℝ, H₀ ≤ H → T₀ ≤ T →
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ∃ P : ℝ, AdmissibleP131 X P ∧
        ∃ (K : ℕ) (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
          (z 0).1 = 1 ∧ (z 0).2.2 = 1 ∧
          (∀ i, i ≠ 0 → z i ∈ zeroBox481 X H T P) ∧
          (∀ w, ((univ.filter (fun i => i ≠ 0 ∧ z i = w)).card : ℕ) ≤
            analyticOrderNatAt (Lfun481 w.2.1) w.2.2) := by
  sorry

/-- LEAF. The coefficient step: for any finite indexed zero family and any epsilon clause
`0 < ε → ε < ε₀ → Cε ε > 0` there are generalised singular series coefficients with the three
properties the statement asks of them, namely the pole pair carries `S(n)`, every coefficient is
bounded by `S(n)`, and a coefficient is at most `ε` as soon as one of the two conductors fails to
divide `Cε ε * n`. The major arc integral does not appear. -/
theorem leaf_singular_series_coefficients481 (ε₀ : ℝ) (hε₀ : 0 < ε₀) (Cε : ℝ → ℕ)
    (hC : ∀ ε, 0 < Cε ε) :
    ∀ (X K : ℕ) (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
      ∃ Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ,
        (∀ n ∈ evenJ131 X, Sg 0 0 n = (Sing n : ℂ)) ∧
        (∀ i j n, n ∈ evenJ131 X → ‖Sg i j n‖ ≤ Sing n) ∧
        (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 X →
          (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε) := by
  sorry

/-- LEAF. The estimate step: the decay constant, the epsilon constant, the remainder constant and
the divisor constant, and then the remainder estimate for whatever data is given. Given thresholds in
`H` and `T`, at every large enough scale, any admissible `P`, any indexed zero family satisfying the
pole, box and multiplicity conditions, and any coefficients satisfying the three properties, the real
major arc integral is within `B * (X exp (-c H) + X / sqrt T)` of the signed Gamma pair sum. The
existence of the data is not asserted here; the leaf consumes it. -/
theorem leaf_remainder_bound481 (H₀ T₀ : ℝ) :
    ∃ c ε₀ B : ℝ, 0 < c ∧ 0 < ε₀ ∧ 0 ≤ B ∧
    ∃ Cε : ℝ → ℕ, (∀ ε, 0 < Cε ε) ∧
      ∀ H T : ℝ, H₀ ≤ H → T₀ ≤ T →
        ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
          ∀ P : ℝ, AdmissibleP131 X P →
          ∀ (K : ℕ) (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
            (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ),
            (z 0).1 = 1 → (z 0).2.2 = 1 →
            (∀ i, i ≠ 0 → z i ∈ zeroBox481 X H T P) →
            (∀ w, ((univ.filter (fun i => i ≠ 0 ∧ z i = w)).card : ℕ) ≤
              analyticOrderNatAt (Lfun481 w.2.1) w.2.2) →
            (∀ n ∈ evenJ131 X, Sg 0 0 n = (Sing n : ℂ)) →
            (∀ i j n, n ∈ evenJ131 X → ‖Sg i j n‖ ≤ Sing n) →
            (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 X →
              (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε) →
            ∀ n ∈ evenJ131 X,
              |binaryMajor131 X n P -
                (∑ i, ∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
                  gammaPair481 (z i).2.2 (z j).2.2 n).re| ≤
                B * ((X : ℝ) * Real.exp (-c * H) + X / Real.sqrt T) := by
  sorry

/-- The split target: the same statement as `pintz_explicit_formula481`, proved from the three
leaves above and not from the target. -/
theorem pintz_explicit_formula481_split : Lemma41Statement481 := by
  obtain ⟨H₀, T₀, -, -, hfam⟩ := leaf_admissible_zero_family481
  obtain ⟨c, ε₀, B, hc, hε₀, hB, Cε, hC, hrem⟩ := leaf_remainder_bound481 H₀ T₀
  refine ⟨c, ε₀, B, H₀, T₀, hc, hε₀, hB, Cε, hC, ?_⟩
  intro H T hH hT
  obtain ⟨X₀, hX₀⟩ := hfam H T hH hT
  obtain ⟨X₁, hX₁⟩ := hrem H T hH hT
  refine ⟨max X₀ X₁, ?_⟩
  intro X hX
  obtain ⟨P, hAdm, K, z, hpole1, hpole2, hbox, hmult⟩ :=
    hX₀ X (le_trans (le_max_left _ _) hX)
  obtain ⟨Sg, hSg00, hSgS, hSgε⟩ := leaf_singular_series_coefficients481 ε₀ hε₀ Cε hC X K z
  refine ⟨P, hAdm, K, z, Sg, hpole1, hpole2, hbox, hmult, hSg00, hSgS, hSgε, ?_⟩
  exact hX₁ X (le_trans (le_max_right _ _) hX) P hAdm K z Sg hpole1 hpole2 hbox hmult
    hSg00 hSgS hSgε

end
end LeanLab.LPZ2007
