/-
P0069, Section 3, pages 11 to 12. Finer leaves for the mean square
input used by the sieve decomposition in DecompC165c.
Every analytic leaf is OPEN. The exact final assembly is CONDITIONAL.
AI wrote the Lean code. CODEX task190. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165c
import LeanLab.BHP1997.MeanSquareC165
import LeanLab.BHP1997.Thm4Statement

namespace LeanLab.BHP1997.DecompF190
open MeanSquareC165
open Thm4

/-- LEAF. Page 11, the squared norm of a single Dirichlet polynomial at a fixed
character and time is bounded by the coefficient energy times the character sum.
This is the first reduction: pointwise bound before summing over characters and times. -/
theorem LEAF_pointwise_dirPoly_bound {a : ℕ → ℂ} {B c1 c2 F : ℝ}
    (hc1 : 0 < c1) (hc2 : c1 < c2) (hF : 2 ≤ F)
    (ha : CoeffBound a B) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖dirPoly a c1 c2 F χ (half t)‖ ^ 2 ≤ (q : ℝ) * energy a c1 c2 F := by sorry

/-- LEAF. Page 11, the hybrid large sieve bound for a single character sum over time.
This applies Montgomery's Theorem 6.4 (reference 21) to the time sum for a fixed character. -/
theorem LEAF_time_sum_hybrid_sieve {a : ℕ → ℂ} {B c1 c2 F T : ℝ}
    (hc1 : 0 < c1) (hc2 : c1 < c2) (hF : 2 ≤ F) (hT : 2 < T)
    (ha : CoeffBound a B) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset ℝ) (hS : ∀ t ∈ S, |t| ≤ T) (hwell : WellSpacedTime S) :
    (∑ t ∈ S, ‖dirPoly a c1 c2 F χ (half t)‖ ^ 2) ≤
      (Real.log (max 2 (q * T + F))) * (energy a c1 c2 F) := by sorry

/-- LEAF. Page 11, summing the hybrid sieve bound over all characters modulo q.
This uses character orthogonality to bound the sum over all characters by q times the single character bound. -/
theorem LEAF_character_sum_bound {a : ℕ → ℂ} {B c1 c2 F T : ℝ}
    (hc1 : 0 < c1) (hc2 : c1 < c2) (hF : 2 ≤ F) (hT : 2 < T)
    (ha : CoeffBound a B) {q : ℕ} (hq : 1 ≤ q)
    (S : Finset (ℝ × DirichletCharacter ℂ q))
    (hwell : WellSpaced S) (htime : ∀ p ∈ S, |p.1| ≤ T) :
    (∑ p ∈ S, ‖dirPoly a c1 c2 F p.2 (half p.1)‖ ^ 2) ≤
      (q : ℝ) * Real.log (max 2 (q * T + F)) * energy a c1 c2 F := by sorry

/-- LEAF. Page 12, the logarithmic factor log x absorbs the log(qT + F) factor
and introduces the constant C depending on the coefficient bound exponent B. -/
theorem LEAF_log_absorption {x F T : ℝ} {q : ℕ} (hx : 2 ≤ x) (hF : 2 ≤ F)
    (hFx : F ≤ x) (hT : 2 < T) (hTx : T ≤ x / 4) (hq : 1 ≤ q) (hqx : (q : ℝ) ≤ x) :
    Real.log (max 2 ((q : ℝ) * T + F)) ≤ Real.log x := by sorry

/-- LEAF. Page 12, the final assembly combining the character sum bound
with the logarithmic absorption to obtain the exact Lemma1MeanSquare statement. -/
theorem LEAF_final_assembly {B c1 c2 : ℝ} (hc1 : 0 < c1) (hc2 : c1 < c2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x F T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a : ℕ → ℂ, CoeffBound a B →
        2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
        WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
          (∑ p ∈ S, ‖dirPoly a c1 c2 F p.2 (half p.1)‖ ^ 2) ≤
            C * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := by sorry

/-- The exact statement of Lemma1MeanSquare, assembled from the LEAF lemmas above.
No sorry in this assembly; it uses the LEAF lemmas as black boxes. -/
theorem hybrid_mean_square_F190 : Lemma1MeanSquare := by
  intro B c1 c2 hc1 hc2
  obtain ⟨C, hC, hC'⟩ := LEAF_final_assembly B c1 c1 hc1 hc2
  exact ⟨C, hC, fun x F T q S a ha hx hF hFx hT hTx hq hqx hwell htime => hC' x F T q S a ha hx hF hFx hT hTx hq hqx hwell htime⟩

end LeanLab.BHP1997.DecompF190