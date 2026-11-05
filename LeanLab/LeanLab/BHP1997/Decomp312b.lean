/-
P0069, Section 4, pages 41 and 42. CODEX task312.
The upper mean-value supply is separate from the common Perron transfer.
The exact assembly is CONDITIONAL. The sealed leaf declarations are unchanged.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp312a

namespace LeanLab.BHP1997.Decomp312b
open Classical Complex DecompC165b Decomp312a Decomp312c Decomp132

/-- LEAF. Pages 41 and 42, the upper seven-step Buchstab construction,
Lemma 28 and the final density computation. Supply the upper sifted family
at one fixed positive divisor exponent, together with an auxiliary
Möbius-truncated family, both mean values 4.1, its I1 density and a
small absolute difference on I. The discarded domains and multiplicities remain part of this
input. No short-window Perron transfer is asserted. OPEN.
Choose the existential auxiliary family b with a smooth weight that tapers
at x/2 and 2x before applying MeanValue41. Keep the weight equal to 1 on
I and I1 for all sufficiently large x. This preserves the local approximation
and reference density while removing the sharp endpoint terms.
Gate QUESTION: positive density with a sharp cutoff at either endpoint
fails printed 4.1 for the principal character at q = 1. The same principal
character obstruction affects the printed Lemma 10 step bounding the
supremum norm of L. The existential choice of b permits this taper, so that
obstruction does not rule out this supply leaf. Constructing b and proving
all its estimates remain OPEN. -/
theorem upper_mean_value_supply (h4 : Thm4.Theorem4Paper) :
    ∃ B0 η : ℝ, 0 < B0 ∧ 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∃ (u1 : ℝ) (c1 b : ℝ → ℕ → ℝ),
        1 ≤ u1 ∧ u1 < 1.0001 ∧
        (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
          C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        MeanValue41 ε b ∧ ReferenceDensity u1 b ∧
        ShortApproximation ε (section4SiftedFamily c1) b ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, primeWeight k ≤ section4SiftedFamily c1 x k := by
  sorry

/-- Pages 41 and 42. The exact sealed upper leaf follows from the smaller
upper supply and common Perron inputs. CONDITIONAL on those OPEN inputs.
The existing DecompC165b declaration is unchanged. -/
theorem section4_upper_sifted_data (h4 : Thm4.Theorem4Paper) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (u1 : ℝ) (c1 : ℝ → ℕ → ℝ),
        1 ≤ u1 ∧ u1 < 1.0001 ∧
        (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
          ∀ t : ℝ, t ≤ x →
            ‖∑ k ∈ (leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ t),
              ((section4SiftedFamily c1 x k : ℂ) * χ (k : ZMod q) -
                Thm2.delta χ * u1 / Real.log x)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
        (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
          C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, primeWeight k ≤ section4SiftedFamily c1 x k := by
  obtain ⟨B0, ηs, hB0, hηs, hs⟩ := upper_mean_value_supply h4
  obtain ⟨ηp, hηp, hp⟩ := perron_transfer B0
  refine ⟨B0, min ηs ηp, lt_min hηs hηp, ?_⟩
  intro B ε hB hε hεη
  obtain ⟨u, c, b, hu, hu1, hc, hb, hm, hd, happ, hlo⟩ := hs ε hε (lt_of_lt_of_le hεη (min_le_left _ _))
  have hr := hp ε hε (lt_of_lt_of_le hεη (min_le_right _ _))
    b hb hm
  exact ⟨u, c, hu, hu1, distribution_of_approximation happ (distribution_of_reference hε.le hr hd),
    divisor_bound_mono hB0 hB hc, hlo⟩

end LeanLab.BHP1997.Decomp312b
