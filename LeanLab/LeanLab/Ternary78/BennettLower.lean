import LeanLab.Ternary78.ZeroSumLower

/-
AI wrote this Lean code. Binary Goldbach is open.
The only cited analytic input is BennettThm1_1, with its existing constants unchanged.
The zero count remains a parameter. No identification with L-function zeros is proved here.
Source: https://arxiv.org/abs/2005.02989 Theorem 1.1 page 2 as cited in NTChi.lean.
The printed formula was checked in the rendered arXiv page 2 during task55.
-/

namespace LeanLab.Ternary78.Bennett
open Real

/-- The lower endpoint from the existing cited Theorem 1.1. -/
noncomputable def lowerEndpoint {q : ℕ} (χ : DirichletCharacter ℂ q) (T : ℝ) : ℝ :=
  (T / Real.pi * Real.log (q * T / (2 * Real.pi * Real.exp 1)) -
    (χ (-1) : ℂ).re / 4) -
    (0.22737 * Real.log (q * (T + 2) / (2 * Real.pi)) +
      2 * Real.log (1 + Real.log (q * (T + 2) / (2 * Real.pi))) - 0.5)

/-- CONDITIONAL ON BennettThm1_1. Counts are also nonnegative. -/
theorem lowerEndpoint_le_count
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ} {Q q : ℕ} [NeZero q]
    (hB : BennettThm1_1 N Q) (hq : q ≤ Q) (hq1 : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 5 / 7 ≤ T)
    (hl : 1.567 < Real.log (q * (T + 2) / (2 * Real.pi))) :
    max 0 (lowerEndpoint χ T) ≤ (N q χ T : ℝ) := by
  have h := hB q hq hq1 χ hχ T hT hl
  apply max_le (Nat.cast_nonneg _)
  unfold lowerEndpoint
  have := (abs_le.mp h).1
  linarith

#print axioms lowerEndpoint_le_count

/-- A grid count starts at zero without asserting that N at height zero is zero. -/
noncomputable def gridCount
    (N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else N q χ (t i)

/-- Only admissible positive indices use the cited lower endpoint. -/
noncomputable def gridLower {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else
    if 5 / 7 ≤ t i ∧ 1.567 < Real.log (q * (t i + 2) / (2 * Real.pi)) then
      max 0 (lowerEndpoint χ (t i)) else 0

/-- A right endpoint discretization of a weighted zero count. -/
noncomputable def weightedCount (A f : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, (A (i + 1) - A i) * f (i + 1)

/-- CONDITIONAL ON BennettThm1_1. No monotonicity of the lower endpoint is needed. -/
theorem gridLower_le_gridCount
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ} {Q q : ℕ} [NeZero q]
    (hB : BennettThm1_1 N Q) (hq : q ≤ Q) (hq1 : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (t : ℕ → ℝ) (i : ℕ) :
    gridLower χ t i ≤ gridCount N χ t i := by
  unfold gridLower gridCount
  split_ifs with hi ha
  · exact le_rfl
  · exact lowerEndpoint_le_count hB hq hq1 χ hχ ha.1 ha.2
  · exact Nat.cast_nonneg _

#print axioms gridLower_le_gridCount

/-- CONDITIONAL ON BennettThm1_1. This is the Abel summation bridge. -/
theorem weightedCount_lower_of_bennett
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ} {Q q : ℕ} [NeZero q]
    (hB : BennettThm1_1 N Q) (hq : q ≤ Q) (hq1 : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (t f : ℕ → ℝ) (hf : ∀ i, f (i + 1) ≤ f i) (hf0 : ∀ i, 0 ≤ f i) (k : ℕ) :
    weightedCount (gridLower χ t) f k ≤ weightedCount (gridCount N χ t) f k := by
  apply LeanLab.Ternary78.Threshold.sum_lower_bound_of_counts
  · exact gridLower_le_gridCount hB hq hq1 χ hχ t
  · exact hf
  · exact hf0
  · simp [gridLower]
  · simp [gridCount]

/-- A zero weight gives an unconditional concrete instance of the conclusion. -/
example (A : ℕ → ℝ) (k : ℕ) : weightedCount A (fun _ => 0) k = 0 := by
  simp [weightedCount]

/-- Every constant nonnegative weight satisfies the two weight hypotheses. -/
example {c : ℝ} (hc : 0 ≤ c) :
    (∀ i : ℕ, (fun _ : ℕ => c) (i + 1) ≤ c) ∧
      (∀ i : ℕ, 0 ≤ (fun _ : ℕ => c) i) := ⟨fun _ => le_rfl, fun _ => hc⟩

#print axioms weightedCount_lower_of_bennett

end LeanLab.Ternary78.Bennett
