/-
P0069, Section 5, pages 43 to 53. The two short weight constructions
are separate leaves. Their order comes from densities below and above 1.
The exact final statement is CONDITIONAL on both OPEN leaves.
AI wrote the Lean code. CODEX task165. Goldbach is open.
-/
import LeanLab.BHP1997.SieveConditionsC165
import LeanLab.BHP1997.DecompC165a
import LeanLab.BHP1997.Decomp132
import LeanLab.BHP1997.NormalizationC165

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- LEAF. Pages 43 to 52, the lower short weight b0. Lemmas 29 to 35
supply the moment estimates, the discarded E2 and E4 integrals on page 51
supply v0 above 0.05, and 5.18 to 5.23 on page 52 normalize condition iv.
The density is at most 1 because the discarded integrals are nonnegative.
Reuse the exponent lemmas and NormalizationC165. The analytic inputs and
certified discarded integrals remain OPEN. -/
theorem lower_short_weight (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
        0.05 < v0 ∧ v0 ≤ 1 ∧ RightConditions ε B v0 b0 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  sorry

/-- LEAF. Page 53, the upper short weight b1. The four-term Buchstab
identity is gm minus hm plus jm minus km. Delete only km terms where
Lemma 33 is unavailable. The printed integral formula gives v1 below 2.2.
The upper sandwich and the density asymptotic give v1 at least 1.
Repeat the page 52 normalization. The analytic estimates and certified
Buchstab integral remain OPEN. -/
theorem upper_short_weight (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v1 : ℝ) (b1 : ℝ → ℕ → ℝ),
        1 ≤ v1 ∧ v1 < 2.2 ∧ RightConditions ε B v1 b1 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x, primeWeight m ≤ b1 x m := by
  sorry

/-- Pages 43 to 53, combine the two short constructions at one common
divisor exponent and epsilon cutoff. This is the exact statement of
DecompC165b.section5_weights. CONDITIONAL on both OPEN leaves. -/
theorem section5_weights (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v0 v1 : ℝ) (b0 b1 : ℝ → ℕ → ℝ),
        0.05 < v0 ∧ v0 ≤ v1 ∧ v1 < 2.2 ∧
        RightConditions ε B v0 b0 ∧ RightConditions ε B v1 b1 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x,
            b0 x m ≤ primeWeight m ∧ primeWeight m ≤ b1 x m := by
  obtain ⟨B0, η0, hη0, h0⟩ := lower_short_weight h4 h9
  obtain ⟨B1, η1, hη1, h1⟩ := upper_short_weight h4 h9
  refine ⟨max B0 B1, min η0 η1, lt_min hη0 hη1, ?_⟩
  intro B ε hB hε hεη
  obtain ⟨v0, b0, hv0, hv01, hb0, X0, hs0⟩ := h0 B ε
    (le_trans (le_max_left _ _) hB) hε (lt_of_lt_of_le hεη (min_le_left _ _))
  obtain ⟨v1, b1, hv11, hv1, hb1, X1, hs1⟩ := h1 B ε
    (le_trans (le_max_right _ _) hB) hε (lt_of_lt_of_le hεη (min_le_right _ _))
  refine ⟨v0, v1, b0, b1, hv0, le_trans hv01 hv11, hv1, hb0, hb1,
    max X0 X1, ?_⟩
  intro x hx m hm
  exact ⟨hs0 x (le_trans (le_max_left _ _) hx) m hm,
    hs1 x (le_trans (le_max_right _ _) hx) m hm⟩

end LeanLab.BHP1997.DecompC165d
