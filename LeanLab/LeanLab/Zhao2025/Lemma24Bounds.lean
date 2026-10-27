import Mathlib

/-!
The actual numerical conclusions of Lemma 2.4, as a cited predicate.
This predicate is distinct from the lab per case display bundle Lemma24_dichotomy.
No assertion that Dirichlet L zero data satisfy this predicate is proved here.
Source: Zhao 2025, Lemma 2.4, pages 7 and 8.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- STATED and cited. Natural index four corresponds to paper index five. -/
def Lemma24Bounds (l : ℝ) (N : ℝ → ℕ) (first : ℕ → ℝ) : Prop :=
  0 < l ∧
  (l ≤ 0.01 → N 5.68 ≤ 1) ∧
  (l ≤ 0.10 → N 3.08 ≤ 1) ∧
  (l ≤ 0.30 → N 1.58 ≤ 1) ∧
  (l ≤ 0.40 → N 1.29 ≤ 1) ∧
  (l ≤ 0.60 → N 0.92 ≤ 2) ∧
  (l ≤ 0.62 → N 0.85 ≤ 1 ∨ N 0.91 ≤ 2) ∧
  (l ≤ 0.64 → N 0.85 ≤ 2) ∧
  (l ≤ 0.68 → N 0.74 ≤ 2) ∧
  N (1.09 * Real.log l⁻¹) ≤ 1 ∧ N 0.702 ≤ 2 ∧
  ∀ i : ℕ, 4 ≤ i → 0.857 ≤ first i

/-- One abstract zero at lambda 0.005 satisfies every listed bound, with every row active. -/
theorem lemma24_nonempty_model :
    Lemma24Bounds 0.005 (fun L => if (0.005 : ℝ) ≤ L then 1 else 0)
      (fun i => if i = 0 then 0.005 else 1) ∧
    (if (0.005 : ℝ) ≤ 1 then (1 : ℕ) else 0) = 1 := by
  classical
  have hn (L : ℝ) : (if (0.005 : ℝ) ≤ L then (1 : ℕ) else 0) ≤ 1 := by
    split_ifs <;> omega
  constructor
  · refine ⟨by norm_num, (fun _ => hn _), (fun _ => hn _), (fun _ => hn _),
      (fun _ => hn _), (fun _ => (hn _).trans (by decide)),
      (fun _ => Or.inl (hn _)), (fun _ => (hn _).trans (by decide)),
      (fun _ => (hn _).trans (by decide)), hn _, (hn _).trans (by decide), ?_⟩
    intro i hi
    have hi0 : i ≠ 0 := by omega
    norm_num [hi0]
  · norm_num

#print axioms lemma24_nonempty_model

end LeanLab.Zhao2025.Task56
