import Mathlib

/-!
The explicit exponent in Wu 2004 Lemma 2.5, page 7.
Source: https://arxiv.org/abs/0705.1652.
These results concern the exponent formula only.
They do not prove the bilinear distribution estimate.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
namespace LeanLab.ChenDoubleSieve.Task668

/-- The eight printed affine pieces, extended by the outside branches. -/
def lemma25Theta (ν : ℝ) : ℝ :=
  if ν ≤ 1 / 15 then (6 - 5 * ν) / 10 else
  if ν ≤ 1 / 10 then 1 / 2 + ν else
  if ν ≤ 3 / 14 then (5 - 2 * ν) / 8 else
  if ν ≤ 1 / 4 then (3 + 2 * ν) / 6 else
  if ν ≤ 2 / 7 then (2 - ν) / 3 else
  if ν ≤ 2 / 5 then (2 + ν) / 4 else
  if ν ≤ 1 / 2 then 1 - ν else 1 / 2

/-- The printed exponent lies between one half and three fifths. -/
theorem lemma25Theta_bounds {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 1) :
    1 / 2 ≤ lemma25Theta ν ∧ lemma25Theta ν ≤ 3 / 5 := by
  unfold lemma25Theta
  split_ifs <;> constructor <;> linarith

/-- Exact values at the seven printed shared endpoints. -/
theorem lemma25Theta_breakpoints :
    lemma25Theta (1 / 15) = 17 / 30 ∧
    lemma25Theta (1 / 10) = 3 / 5 ∧
    lemma25Theta (3 / 14) = 4 / 7 ∧
    lemma25Theta (1 / 4) = 7 / 12 ∧
    lemma25Theta (2 / 7) = 4 / 7 ∧
    lemma25Theta (2 / 5) = 3 / 5 ∧
    lemma25Theta (1 / 2) = 1 / 2 := by
  norm_num [lemma25Theta]

/-- The affine exponent is strictly above one half before nu reaches one half. -/
theorem lemma25Theta_strict {ν : ℝ} (h0 : 0 < ν) (h1 : ν < 1 / 2) :
    1 / 2 < lemma25Theta ν := by
  unfold lemma25Theta
  split_ifs <;> linarith

/-- The explicit epsilon leaves a positive exponent gain over one half. -/
theorem lemma25Theta_margin {ν : ℝ} (h0 : 0 < ν) (h1 : ν < 1 / 2) :
    0 < (lemma25Theta ν - 1 / 2) / 2 ∧
      1 / 2 < lemma25Theta ν - (lemma25Theta ν - 1 / 2) / 2 := by
  have h := lemma25Theta_strict h0 h1
  constructor <;> linarith

/-- A positive epsilon obeys the paper range and retains the half level gain. -/
theorem lemma25Theta_admissible_epsilon {ν : ℝ} (h0 : 0 < ν) (h1 : ν < 1 / 2) :
    let ε : ℝ := min ν ((lemma25Theta ν - 1 / 2) / 2)
    0 < ε ∧ ε ≤ ν ∧ ν ≤ 1 - ε ∧ 1 / 2 < lemma25Theta ν - ε := by
  dsimp only
  have hg := lemma25Theta_margin h0 h1
  have he0 : 0 < min ν ((lemma25Theta ν - 1 / 2) / 2) := lt_min h0 hg.1
  have heν := min_le_left ν ((lemma25Theta ν - 1 / 2) / 2)
  have hegap := min_le_right ν ((lemma25Theta ν - 1 / 2) / 2)
  refine ⟨he0, heν, ?_, ?_⟩ <;> linarith

end LeanLab.ChenDoubleSieve.Task668
#print axioms LeanLab.ChenDoubleSieve.Task668.lemma25Theta
#print axioms LeanLab.ChenDoubleSieve.Task668.lemma25Theta_bounds
#print axioms LeanLab.ChenDoubleSieve.Task668.lemma25Theta_breakpoints
#print axioms LeanLab.ChenDoubleSieve.Task668.lemma25Theta_strict
#print axioms LeanLab.ChenDoubleSieve.Task668.lemma25Theta_margin

#print axioms LeanLab.ChenDoubleSieve.Task668.lemma25Theta_admissible_epsilon
