import LeanLab.Zhao2025.Display110

/-!
Nonempty abstract zero models throughout the previously uncovered interval.
These models do not assert existence of a Dirichlet L zero.
Source: Zhao 2025, displays 4.1 to 4.6, pages 13 and 14.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56
open LeanLab.Zhao2025.U6837

/-- One cluster contains a single abstract scaled zero. -/
noncomputable def smallCaseModelS (l : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then Real.exp (-(10 / 3 * l)) else 0

/-- The named small case estimates have a positive singleton model for every positive l. -/
theorem small_case_estimates_instance (l : ℝ) (hl : 0 < l) :
    SmallCaseZeroEstimates 0 l (smallCaseModelS l) ∧ 0 < smallCaseModelS l 0 := by
  let t := Real.exp (-(10 / 3 * smallCaseCutoff l))
  have hc := small_case_cutoff_spec l hl
  have ht0 : 0 ≤ t := (Real.exp_pos _).le
  have htb : t ≤ 100 * Real.exp (-2.22 * smallCaseCutoff l) := by
    have hle : t ≤ Real.exp (-2.22 * smallCaseCutoff l) :=
      Real.exp_le_exp.mpr (by nlinarith [hc.2.1])
    nlinarith [Real.exp_pos (-2.22 * smallCaseCutoff l)]
  have ht2 : t ≤ 0.02 := by
    have hle : t ≤ Real.exp (-(489 / 100 : ℝ)) :=
      Real.exp_le_exp.mpr (by nlinarith [hc.1])
    linarith [x489.2]
  constructor
  · refine ⟨fun i => if i = 0 then t else 0, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hi0 : i = 0 := by simpa using hi
      subst i
      simpa using ht0
    · intro i hi
      have hi0 : i = 0 := by simpa using hi
      subst i
      simpa using htb
    · simpa using ht2
    · simp [smallCaseModelS, t]
    · intro i hi
      omega
  · simpa [smallCaseModelS] using Real.exp_pos (-(10 / 3 * l))

/-- The repaired case zero has nonempty data for the entire positive interval to 0.01. -/
theorem small_case_inputs_instance (l : ℝ) (hl : 0 < l) (hu : l ≤ 0.01) :
    CaseInputs 0 0 l (fun _ => 0) (fun _ => 0) (smallCaseModelS l) :=
  ⟨hl, hu, (small_case_estimates_instance l hl).1⟩

/-- A first lambda of one millionth is covered by a positive gap and a positive zero weight. -/
theorem tiny_lambda_gap_example :
    0 < gap (1 / 1000000) ∧
      Real.exp (-(10 / 3 * (1 / 1000000 : ℝ))) ^ 2 ≤ 1 - gap (1 / 1000000) := by
  have hi := small_case_inputs_instance (1 / 1000000) (by norm_num) (by norm_num)
  have hb := uniform_energy (1 / 1000000) (by norm_num) 0 0 (1 / 1000000)
    (fun _ => 0) (fun _ => 0) (smallCaseModelS (1 / 1000000)) le_rfl hi
  simpa [layoutEnergy, smallCaseModelS] using hb

#print axioms small_case_estimates_instance
#print axioms small_case_inputs_instance
#print axioms tiny_lambda_gap_example
end LeanLab.Zhao2025.Task56
