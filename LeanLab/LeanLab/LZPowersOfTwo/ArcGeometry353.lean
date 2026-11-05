/-
Cutoff growth and the precise trivial arc in P0079 pages 4 and 10.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.CountBounds293

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 4, definition of L. Positive coefficient mass and epsilon
make the exponent cutoff tend to infinity with the box size. -/
theorem cutoff_tendsto353 (s : ℕ) (μ : ℕ → ℝ) (ε : ℝ)
    (hM : 0 < ∑ i : Fin s, |μ i|) (hε : 0 < ε) :
    Tendsto (cutoff293 s μ ε) atTop atTop := by
  have hk : 0 < ε / (2 * ∑ i : Fin s, |μ i|) := by positivity
  have H := (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
    (Filter.Tendsto.const_mul_atTop hk tendsto_id)
  convert H using 1
  funext X
  unfold cutoff293
  simp only [Function.comp_apply, id_eq]
  congr 1
  ring

/-- P0079 page 4, display 14, and page 10, Section 5.
For X and L at least one, the sealed complement definition is exactly the tail. -/
theorem trivial_eq_tail353 (X L : ℝ) (hX : 1 ≤ X) (hL : 1 ≤ L) :
    trivial293 X L = {α : ℝ | L ^ 2 < |α|} := by
  have hX0 : 0 < X := by linarith
  have ha : X ^ (1 / 3 : ℝ) / X ≤ L ^ 2 := by
    have hpow := Real.rpow_le_self_of_one_le hX (by norm_num : (1 / 3 : ℝ) ≤ 1)
    have hdiv : X ^ (1 / 3 : ℝ) / X ≤ 1 := (div_le_one hX0).mpr hpow
    nlinarith
  ext α
  change ¬ (|α| ≤ X ^ (1 / 3 : ℝ) / X ∨
    (X ^ (1 / 3 : ℝ) / X < |α| ∧ |α| ≤ L ^ 2)) ↔ L ^ 2 < |α|
  constructor
  · intro h
    by_contra hh
    apply h
    by_cases hα : |α| ≤ X ^ (1 / 3 : ℝ) / X
    · exact Or.inl hα
    · exact Or.inr ⟨lt_of_not_ge hα, le_of_not_gt hh⟩
  · intro h hh
    rcases hh with hh | hh <;> linarith

/-- P0079 page 10, Section 5. The complement definition of the trivial arc
is eventually the two-sided tail beyond L squared. -/
theorem trivial_eventually_tail353 (s : ℕ) (μ : ℕ → ℝ) (ε : ℝ)
    (hM : 0 < ∑ i : Fin s, |μ i|) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop,
      trivial293 X (cutoff293 s μ ε X) = {α : ℝ | (cutoff293 s μ ε X) ^ 2 < |α|} := by
  filter_upwards [(cutoff_tendsto353 s μ ε hM hε).eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℝ)] with X hL hX
  exact trivial_eq_tail353 X _ hX hL

end LeanLab.LZPowersOfTwo
