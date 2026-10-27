/-
P0069, Lemma 9, pages 22 and 23, with the Section 3 conventions
on page 11. The full cited mean value bound is stated here.
The last term means a sum over principal-character pairs only.
AI wrote the Lean code. CODEX task132, 2026-10-26. Goldbach is open.
-/
import LeanLab.BHP1997.Thm4Statement

namespace LeanLab.BHP1997.MeanValue132
open Classical Complex

/-- Page 22, the unweighted Dirichlet polynomial with n at most N.
The positive index range avoids the undefined classical term at n equal to 0. -/
noncomputable def partialSum {q : ℕ} (N : ℝ) (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊N⌋₊, χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t

/-- Page 22, the two error terms in Lemma 9. The final sum runs over
principal-character pairs. All characters occur in the first error term. -/
noncomputable def remainder {q : ℕ} (x N T : ℝ)
    (S : Finset (ℝ × DirichletCharacter ℂ q)) : ℝ :=
  Real.log x ^ 4 * (S.card : ℝ) * ((q : ℝ) ^ 2 / T ^ 2 + N ^ 2 / T ^ 4) +
    N ^ 2 * ∑ p ∈ S, if p.2 = 1 then 1 / (1 + |p.1|) ^ 4 else 0

/-- Lemma 9, page 22, CITED. Uniform in q, T, N and the well-spaced set.
B and C are absolute constants. The second term is the displayed error
remainder and the principal-character residue sum. -/
def Lemma9 : Prop :=
  ∃ B C : ℝ, 0 ≤ B ∧ 0 < C ∧ ∀ x N T : ℝ, ∀ q : ℕ,
    ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    2 ≤ x → 2 ≤ N → N ≤ x → 2 ≤ T → T ≤ x → 1 ≤ q → (q : ℝ) ≤ x →
    Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      ∑ p ∈ S, ‖partialSum N p.2 p.1‖ ^ 4 ≤
        C * ((q : ℝ) * T * Real.log x ^ B + remainder x N T S)

/-- Lemma 7, page 22, CITED. The fourth moment includes all characters,
not only primitive characters. Source: Ramachandra, reference 26. -/
def Lemma7 : Prop :=
  ∃ B C : ℝ, 0 ≤ B ∧ 0 < C ∧ ∀ x T : ℝ, ∀ (q : ℕ) [NeZero q],
    2 ≤ x → 0 ≤ T → T ≤ x → 1 ≤ q → (q : ℝ) ≤ x →
      (∑ χ : DirichletCharacter ℂ q,
        ∫ t in (-T)..T, ‖χ.LFunction (Thm4.half t)‖ ^ 4) ≤
          C * (q : ℝ) * T * Real.log x ^ B

/-- Lemma 8, page 22, CITED in the strip used by its contour argument.
The pole s equal to 1 is excluded. Source: Rademacher, reference 28.
The implicit constant depends on the positive epsilon. -/
def Lemma8 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 1 ≤ q →
    ∀ χ : DirichletCharacter ℂ q, ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 →
      (σ : ℂ) + t * Complex.I ≠ 1 →
      ‖χ.LFunction ((σ : ℂ) + t * Complex.I)‖ ≤
        C * (((q : ℝ) * (|t| + 1)) ^ (1 + ε - σ) +
          1 / ‖(σ : ℂ) + t * Complex.I - 1‖)

end LeanLab.BHP1997.MeanValue132
