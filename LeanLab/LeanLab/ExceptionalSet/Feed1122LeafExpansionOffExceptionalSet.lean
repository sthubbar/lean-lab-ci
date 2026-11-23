/-
Split of `leaf_expansion_off_exceptional_set` of `LeanLab.ExceptionalSet.SPLIT_theorem82`, P0029
Bhowmik-Grimmelt 2026, arXiv 2607.27282v2, Section 8, pages 30 to 32.

The parent asks for an exceptional set of at most `X^{3/5}` multiples, with no `ε`. The printed
Proposition 8.1 at `ϑ = 2/5` only gives `K X^{3/5+ε}`, since Vinogradov's minor arc bound `X^{4/5}`
fixes `2 · 4/5 - 1 = 3/5` up to `X^ε`. So the parent cannot follow from the paper's own `ϑ = 2/5`
argument, see the QUESTION in the burst note. It does follow from Proposition 8.1 at the level
`ϑ = 5/12` with exception exponent `7/12 < 3/5`, the lab's chain of U-1322, U-1335 and U-1343:
`prop81PrintUnif_of_parts`, `prop81_of_printUnif`, `minorL2_cont_of_sup`, all PROVED. The open inputs
of that chain are the two leaves here:

* LEAF 1, the major arc formula of the page 31 Sketch, Pintz Theorem 1, for the continuous major
  arc integral at `ϑ = 5/12`, together with the second half of display (8.1), for some choice of the
  generalised singular series `𝔖(χ̃, χ̃, N)`.
* LEAF 2, the minor arc sup bound with exponent `19/24`, a consequence of MPR arXiv 2608.14777v1
  Theorem 1.1, an unrefereed preprint, by the PROVED `minorArcSup_of_MPR`.

`leaf_expansion_off_exceptional_set_of_leaves` has the parent's statement character for character.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.BG2026MinorCont

namespace LeanLab.ExceptionalSet.BG2026
open Real Finset ArithmeticFunction

noncomputable section

/-- LEAF: page 31 Sketch of Proposition 8.1 at `ϑ = 5/12`, the major arc formula after the cutoff
(8.2), cited from Pintz [20, Thm 1], for the continuous major arc integral `rMajI (5/12)` of eq 4.4,
together with the second half of display (8.1), page 30, `𝔖(χ̃, χ̃, N) = χ̃(-1) 𝔖(N)` for `r̃ ∣ N`.
The generalised singular series of (6.4) is left as the witness `GS`. HARD: a real analytic step,
Pintz's major arc analysis at a Siegel zero. Not vacuous: `Siegel81` holds at real zeros, and
`Display81Mult` pins `GS` at every multiple of `r̃`, the only `N` used downstream. -/
theorem leaf_major_formula_five_twelfths :
    ∃ GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ,
      MajorFormula81C GS (5 / 12) (rMajI (5 / 12)) ∧ Display81Mult GS := by
  sorry

/-- LEAF: the minor arc bound feeding Lemma 4.2 with `X^{19/24}` in place of Vinogradov's
`X^{4/5}`: `|S(α)| ≪_ε N^ε (N/√R + N^{19/24})` on the minor arcs `𝔪(R)`. It follows from MPR arXiv
2608.14777v1 Theorem 1.1 by `minorArcSup_of_MPR`, PROVED; MPR is an unrefereed preprint, an
EXTERNAL input, not a step of P0029. HARD: a real analytic step, an exponential sum bound
over primes. -/
theorem leaf_minor_arc_sup_nineteen_24 : MinorArcSup (19 / 24) := by
  sorry

/-- Proposition 8.1 at `ϑ = 5/12`, `σ = 7/12`, in the U-1322 exception form, from the two leaves
through the PROVED lab chain. -/
theorem prop81_five_twelfths_of_leaves : Prop81 (5 / 12) (7 / 12) := by
  obtain ⟨GS, hM, hD⟩ := leaf_major_formula_five_twelfths
  have hm : MinorL2 (5 / 12) (19 / 24) (rMinIR (5 / 12)) :=
    minorL2_cont_of_sup (by norm_num) (by norm_num) leaf_minor_arc_sup_nineteen_24
  have hU : Prop81PrintUnif GS (5 / 12) (7 / 12) :=
    prop81PrintUnif_of_parts (split_I _) (by norm_num) (majorFormula81_of_cont hM) hm
  exact prop81_of_printUnif hU hD

/-- `Prop81 (5/12) (7/12)` gives the parent's exceptional set bound `X^{3/5}`: take `τ = 71/120`,
between `7/12` and `3/5`, and use `X = r^A ≥ 1`; every `A > 5/2` has `1/A < 5/12`. PROVED. -/
theorem expansion_of_prop81_five_twelfths (h81 : Prop81 (5 / 12) (7 / 12)) :
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 5 / 2 < A → ∃ r0 : ℕ,
      ∀ (r : ℕ) [NeZero r], r0 ≤ r → ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive →
        (∀ a, (χ a).im = 0) →
        (∃ β : ℝ, 1 - c / Real.log ((r : ℝ) ^ A) < β ∧ β < 1 ∧
          DirichletCharacter.LFunction χ β = 0) →
        ∃ B : Finset ℕ, (B.card : ℝ) ≤ ((r : ℝ) ^ A) ^ (3 / 5 : ℝ) ∧
          ∀ N ∈ evenMult r ((r : ℝ) ^ A), N ∉ B → ∃ b E : ℝ, |b - 1| < 3 * δ / 4 ∧
            |E| ≤ δ / 4 * (Sing N * N) ∧
            r2 N = (1 + (χ (-1)).re * b) * (Sing N * N) + E := by
  intro δ hδ hδ1
  obtain ⟨c, hc, hAll⟩ := h81 δ hδ hδ1
  refine ⟨c, hc, fun A hA => ?_⟩
  have hA0 : 0 < A := by linarith
  have hAinv : 1 / A < 5 / 12 := by
    rw [div_lt_iff₀ hA0]; linarith
  obtain ⟨r0, hr0⟩ := hAll A hA0 hAinv (71 / 120) (by norm_num)
  refine ⟨r0, fun r _ hr χ hp hre hz => ?_⟩
  obtain ⟨B, hB, hBN⟩ := hr0 r hr χ hp hre hz
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
    have : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)
    exact_mod_cast this
  have hX1 : (1 : ℝ) ≤ (r : ℝ) ^ A := Real.one_le_rpow hr1 hA0.le
  refine ⟨B, hB.trans (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)), hBN⟩

/-- `leaf_expansion_off_exceptional_set` of `SPLIT_theorem82`, statement identical, from the two
leaves. -/
theorem leaf_expansion_off_exceptional_set_of_leaves :
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 5 / 2 < A → ∃ r0 : ℕ,
      ∀ (r : ℕ) [NeZero r], r0 ≤ r → ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive →
        (∀ a, (χ a).im = 0) →
        (∃ β : ℝ, 1 - c / Real.log ((r : ℝ) ^ A) < β ∧ β < 1 ∧
          DirichletCharacter.LFunction χ β = 0) →
        ∃ B : Finset ℕ, (B.card : ℝ) ≤ ((r : ℝ) ^ A) ^ (3 / 5 : ℝ) ∧
          ∀ N ∈ evenMult r ((r : ℝ) ^ A), N ∉ B → ∃ b E : ℝ, |b - 1| < 3 * δ / 4 ∧
            |E| ≤ δ / 4 * (Sing N * N) ∧
            r2 N = (1 + (χ (-1)).re * b) * (Sing N * N) + E :=
  expansion_of_prop81_five_twelfths prop81_five_twelfths_of_leaves

end

end LeanLab.ExceptionalSet.BG2026

#print axioms LeanLab.ExceptionalSet.BG2026.prop81_five_twelfths_of_leaves
#print axioms LeanLab.ExceptionalSet.BG2026.expansion_of_prop81_five_twelfths
#print axioms LeanLab.ExceptionalSet.BG2026.leaf_expansion_off_exceptional_set_of_leaves
