/-
DEAD SPLIT, U-1624, 2026-11-06. Leaves 2 and 3 below are the sealed `Lemma1MeanSquare` with one
parameter hypothesis added, see `Audit1624.split_qt_of_target` and `Audit1624.split_F_of_target`,
and the assembly does not use leaf 1. The split is an equivalence and reduces nothing.
Nothing imports this file. The live route is the CITED leaf `DecompC165c.hybrid_mean_square`,
behind `AssemblyC165.theorem1`. Kept as text of record.

Split of `hybrid_mean_square` in LeanLab.BHP1997.DecompC165c into leaves.

The square sum over well-spaced time and character pairs (page 11, display 3.3,
`Lemma1MeanSquare` in MeanSquareC165) is cut into the two parameter regimes of the
bracket `q * T + F`, with the elementary per-point bound kept as its own leaf.
In the regime `F ≤ q * T` the character-and-time count dominates the bracket; in the
regime `q * T ≤ F` the length of the polynomial dominates it. Each regime is a
strict special case of the sealed statement, and the two regimes cover it, so the
assembly below needs no further input.

Every leaf is OPEN. The assembly `hybrid_mean_square_split` has no sorry.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165c

namespace LeanLab.BHP1997.DecompC165c
open MeanSquareC165

/-- LEAF 1 of 3. The elementary per-point step: one value of the Dirichlet polynomial is
bounded by the number of its terms times the coefficient energy, by Cauchy-Schwarz on the
weighted terms `a n χ(n) n^{-1/2-it}` with `|n^{-1/2-it}| = n^{-1/2}`. This is the step that
supplies the `F` term of the bracket on the diagonal, and it is the only leaf that does not
need the spacing of the point set. -/
theorem mean_square_pointwise (a : ℕ → ℂ) (c1 c2 F : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ)
    (hc1 : 0 < c1) (hc2 : c1 < c2) (hF : 0 < F) :
    ‖Thm4.dirPoly a c1 c2 F χ (Thm4.half t)‖ ^ 2 ≤
      (((⌊c2 * F⌋₊ + 1 : ℕ) : ℝ) * energy a c1 c2 F) := by
  sorry

/-- LEAF 2 of 3. The regime `F ≤ q * T`, where the character-and-time count dominates the
bracket: the square sum over the well-spaced set is at most a constant times `log x` times
`q * T + F` times the energy. This is the counting half of the split; it is the sealed
statement with the additional hypothesis `F ≤ q * T`. -/
theorem mean_square_qt_dominant :
    ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ C : ℝ, 0 < C ∧
      ∀ x F T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
        2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
        F ≤ (q : ℝ) * T → Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
          (∑ p ∈ S, ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖ ^ 2) ≤
            C * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := by
  sorry

/-- LEAF 3 of 3. The regime `q * T ≤ F`, where the polynomial length dominates the bracket:
the square sum over the well-spaced set is at most a constant times `log x` times
`q * T + F` times the energy. This is the short-counting half of the split; it is the sealed
statement with the additional hypothesis `q * T ≤ F`. -/
theorem mean_square_F_dominant :
    ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ C : ℝ, 0 < C ∧
      ∀ x F T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
        2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
        (q : ℝ) * T ≤ F → Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
          (∑ p ∈ S, ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖ ^ 2) ≤
            C * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := by
  sorry

/-- The normalized coefficient energy of page 11 is a sum of squares divided by a natural
number, hence nonnegative. Used to compare the two regime constants. -/
private theorem split_energy_nonneg (a : ℕ → ℂ) (c1 c2 F : ℝ) :
    0 ≤ energy a c1 c2 F := by
  unfold energy
  apply Finset.sum_nonneg
  intro n _
  exact div_nonneg (by positivity) (Nat.cast_nonneg n)

/-- The sealed statement of `hybrid_mean_square`, assembled from the two regime leaves: at
each parameter point one of `F ≤ q * T` and `q * T ≤ F` holds, and both regime conclusions are
bounded by the common factor `log x * (q * T + F) * G`. -/
theorem hybrid_mean_square_split : Lemma1MeanSquare := by
  intro B c1 c2 hc1 hc2
  obtain ⟨C1, hC1, h1⟩ := mean_square_qt_dominant B c1 c2 hc1 hc2
  obtain ⟨C2, hC2, h2⟩ := mean_square_F_dominant B c1 c2 hc1 hc2
  refine ⟨C1 + C2, by linarith, ?_⟩
  intro x F T q S a ha hx hF hFx hT hTx hq hqx hspace htimes
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hqT : 0 ≤ (q : ℝ) * T := by
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
    have hT0 : (0 : ℝ) ≤ T := by linarith
    exact mul_nonneg hq0 hT0
  have hQF : 0 ≤ (q : ℝ) * T + F := by linarith
  have hE : 0 ≤ energy a c1 c2 F := split_energy_nonneg a c1 c2 F
  have hbase : 0 ≤ Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F :=
    mul_nonneg (mul_nonneg hlog hQF) hE
  rcases le_total F ((q : ℝ) * T) with hdom | hdom
  · have hh := h1 x F T q S a ha hx hF hFx hT hTx hq hqx hdom hspace htimes
    calc (∑ p ∈ S, ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖ ^ 2)
        ≤ C1 * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := hh
      _ = C1 * (Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F) := by ring
      _ ≤ (C1 + C2) * (Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F) :=
          mul_le_mul_of_nonneg_right (by linarith) hbase
      _ = (C1 + C2) * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := by ring
  · have hh := h2 x F T q S a ha hx hF hFx hT hTx hq hqx hdom hspace htimes
    calc (∑ p ∈ S, ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖ ^ 2)
        ≤ C2 * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := hh
      _ = C2 * (Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F) := by ring
      _ ≤ (C1 + C2) * (Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F) :=
          mul_le_mul_of_nonneg_right (by linarith) hbase
      _ = (C1 + C2) * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := by ring

-- Axiom audit driver for the assembly.
#print axioms hybrid_mean_square_split

end LeanLab.BHP1997.DecompC165c
