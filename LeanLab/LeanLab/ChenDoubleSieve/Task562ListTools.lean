import LeanLab.ChenDoubleSieve.Task562Moments

/-!
Computable coefficient lists for Wu 2004 Lemma 5.2 page 26.
Source: https://arxiv.org/pdf/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task562
open Wu04Functional

/-- Evaluation of an explicit rational coefficient list.
Wu 2004 page 26, derived polynomial certificate representation. -/
def listEval (ts : List (ℚ × (Fin 4 → ℕ))) (y : Fin 4 → ℝ) : ℝ :=
  (ts.map fun t => (t.1 : ℝ) * ∏ j, y j ^ t.2 j).sum

/-- Exact rational moment sum of an explicit coefficient list.
Wu 2004 page 26, derived computable certificate arithmetic. -/
def listMomentQ (ts : List (ℚ × (Fin 4 → ℕ))) (a b : ℚ) : ℚ :=
  (ts.map fun t => t.1 * (b - a) ^ ((∑ j : Fin 4, t.2 j) + 4) /
    momentDenom 4 t.2).sum

/-- Every finite coefficient list evaluates continuously.
Wu 2004 page 26, derived compact integration preparation. -/
theorem listEval_continuous (ts : List (ℚ × (Fin 4 → ℕ))) : Continuous (listEval ts) := by
  induction ts with
  | nil => exact continuous_const
  | cons t ts ih =>
    change Continuous (fun y => (t.1 : ℝ) * (∏ j, y j ^ t.2 j) + listEval ts y)
    exact (by fun_prop : Continuous (fun y : Fin 4 → ℝ => (t.1 : ℝ) * ∏ j, y j ^ t.2 j)).add ih

/-- The list evaluation is integrable after translation on every ordered compact chamber.
Wu 2004 page 26, derived finite polynomial integrability. -/
theorem listEval_integrable (ts : List (ℚ × (Fin 4 → ℕ))) (a b : ℝ) :
    IntegrableOn (fun x : Fin 4 → ℝ => listEval ts (fun j => x j - a))
      (domain (fun _ => a) (fun _ => b)) volume := by
  apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
  exact ((listEval_continuous ts).comp (by fun_prop)).continuousOn

/-- Exact list moments equal the integral of the represented polynomial.
Wu 2004 page 26, derived kernel-compatible coefficient certificate theorem. -/
theorem integral_listEval (ts : List (ℚ × (Fin 4 → ℕ))) {a b : ℚ} (hab : a ≤ b) :
    (∫ x in domain (fun _ : Fin 4 => (a : ℝ)) (fun _ => (b : ℝ)),
      listEval ts (fun j => x j - (a : ℝ))) = (listMomentQ ts a b : ℝ) := by
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  induction ts with
  | nil => simp [listEval, listMomentQ]
  | cons t ts ih =>
    change (∫ x in domain (fun _ : Fin 4 => (a : ℝ)) (fun _ => (b : ℝ)),
      (t.1 : ℝ) * (∏ j, (x j - (a : ℝ)) ^ t.2 j) +
        listEval ts (fun j => x j - (a : ℝ))) = _
    have hi : IntegrableOn (fun x : Fin 4 → ℝ => (t.1 : ℝ) * ∏ j, (x j - (a : ℝ)) ^ t.2 j)
        (domain (fun _ => (a : ℝ)) (fun _ => (b : ℝ))) volume := by
      apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
      fun_prop
    rw [MeasureTheory.integral_add hi (listEval_integrable ts _ _),
      MeasureTheory.integral_const_mul, ordered_shifted_monomial 4 t.2 hab', ih]
    simp only [listMomentQ, List.map_cons, List.sum_cons]
    push_cast
    ring

end LeanLab.ChenDoubleSieve.Task562
