import LeanLab.ChenDoubleSieve.Task562Moments

/-!
Variable radius polynomial certificates for Wu 2004 Lemma 5.2 page 26.
Source: https://arxiv.org/abs/0705.1652.
These tools extend the existing exact ordered moments to every dimension.
AI wrote the Lean code. Binary Goldbach is open.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional Task562

/-- A geometric polynomial with a uniform remainder bounds a reciprocal.
Wu 2004 page 26, derived enclosure on one reciprocal cell. -/
theorem reciprocal_le_geometric (n : ℕ) {r z : ℝ} (hr : r < 1) (hz : |z| ≤ r) :
    1 / (1 - z) ≤ (∑ i ∈ range n, z ^ i) + r ^ n / (1 - r) := by
  have hr0 : 0 ≤ r := (abs_nonneg z).trans hz
  have hz1 : z < 1 := (le_abs_self z).trans_lt (hz.trans_lt hr)
  have hp : z ^ n ≤ r ^ n :=
    (le_abs_self (z ^ n)).trans (by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg z) hz n)
  have hs := geom_sum_mul_neg z n
  have he : (r ^ n / (1 - r)) * (1 - r) = r ^ n :=
    div_mul_cancel₀ _ (by linarith)
  have hR : 0 ≤ r ^ n / (1 - r) := div_nonneg (pow_nonneg hr0 n) (by linarith)
  have hm : r ^ n ≤ (r ^ n / (1 - r)) * (1 - z) := by
    nlinarith [le_abs_self z]
  rw [div_le_iff₀ (by linarith : 0 < 1 - z)]
  nlinarith

/-- A computable polynomial enclosure for one positive reciprocal factor.
Wu 2004 page 26, derived variable radius certificate data. -/
def reciprocalUpper (n : ℕ) (c r x : ℝ) : ℝ :=
  ((∑ i ∈ range n, (1 - x / c) ^ i) + r ^ n / (1 - r)) / c

/-- A cell center and relative radius certify the reciprocal polynomial.
Wu 2004 page 26, derived pointwise bound for polynomial quadrature. -/
theorem reciprocal_le_upper (n : ℕ) {c r x : ℝ} (hc : 0 < c) (hr : r < 1)
    (hx : |1 - x / c| ≤ r) : 1 / x ≤ reciprocalUpper n c r x := by
  have h := div_le_div_of_nonneg_right (reciprocal_le_geometric n hr hx) hc.le
  have hx0 : 0 < x := by
    have hl := (abs_le.mp hx).2
    have hxc : 0 < x / c := by linarith
    rcases div_pos_iff.mp hxc with hh | hh
    · exact hh.1
    · exact False.elim ((not_lt_of_ge hc.le) hh.2)
  have he : (1 / (1 - (1 - x / c))) / c = 1 / x := by
    field_simp [hc.ne', hx0.ne']
    <;> ring
  simpa only [he, reciprocalUpper] using h

/-- Exact coefficient list evaluation in arbitrary finite dimension.
Wu 2004 page 26, derived polynomial certificate representation. -/
def listEvalN {d : ℕ} (ts : List (ℚ × (Fin d → ℕ))) (y : Fin d → ℝ) : ℝ :=
  (ts.map fun t => (t.1 : ℝ) * ∏ j, y j ^ t.2 j).sum

/-- Exact rational ordered moment of an arbitrary dimensional coefficient list.
Wu 2004 page 26, derived computable arithmetic. -/
def listMomentN {d : ℕ} (ts : List (ℚ × (Fin d → ℕ))) (a b : ℚ) : ℚ :=
  (ts.map fun t => t.1 * (b - a) ^ ((∑ j : Fin d, t.2 j) + d) /
    momentDenom d t.2).sum

/-- A finite coefficient list defines a continuous polynomial.
Wu 2004 page 26, derived integration preparation. -/
theorem listEvalN_continuous {d : ℕ} (ts : List (ℚ × (Fin d → ℕ))) :
    Continuous (listEvalN ts) := by
  induction ts with
  | nil => exact continuous_const
  | cons t ts ih =>
    change Continuous (fun y => (t.1 : ℝ) * (∏ j, y j ^ t.2 j) + listEvalN ts y)
    exact (by fun_prop : Continuous (fun y : Fin d → ℝ => (t.1 : ℝ) * ∏ j, y j ^ t.2 j)).add ih

/-- Every shifted coefficient polynomial is integrable on its ordered chamber.
Wu 2004 page 26, derived compact-domain fact. -/
theorem listEvalN_integrable {d : ℕ} (ts : List (ℚ × (Fin d → ℕ))) (a b : ℝ) :
    IntegrableOn (fun x : Fin d → ℝ => listEvalN ts (fun j => x j - a))
      (domain (fun _ => a) (fun _ => b)) volume := by
  apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
  exact ((listEvalN_continuous ts).comp (by fun_prop)).continuousOn

/-- Exact ordered integration equals the rational list moment in every dimension.
Wu 2004 page 26, derived from Task562 ordered monomial moments. -/
theorem integral_listEvalN {d : ℕ} (ts : List (ℚ × (Fin d → ℕ)))
    {a b : ℚ} (hab : a ≤ b) :
    (∫ x in domain (fun _ : Fin d => (a : ℝ)) (fun _ => (b : ℝ)),
      listEvalN ts (fun j => x j - (a : ℝ))) = (listMomentN ts a b : ℝ) := by
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  induction ts with
  | nil => simp [listEvalN, listMomentN]
  | cons t ts ih =>
    change (∫ x in domain (fun _ : Fin d => (a : ℝ)) (fun _ => (b : ℝ)),
      (t.1 : ℝ) * (∏ j, (x j - (a : ℝ)) ^ t.2 j) +
        listEvalN ts (fun j => x j - (a : ℝ))) = _
    have hi : IntegrableOn (fun x : Fin d → ℝ => (t.1 : ℝ) * ∏ j, (x j - (a : ℝ)) ^ t.2 j)
        (domain (fun _ => (a : ℝ)) (fun _ => (b : ℝ))) volume := by
      apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
      fun_prop
    rw [MeasureTheory.integral_add hi (listEvalN_integrable ts _ _),
      MeasureTheory.integral_const_mul, ordered_shifted_monomial d t.2 hab', ih]
    simp only [listMomentN, List.map_cons, List.sum_cons]
    push_cast
    ring

/-- A nonzero cubic chamber moment instantiates the generic list rule.
Wu 2004 page 26, derived concrete instance. -/
theorem listMomentN_three_instance :
    (∫ x in domain (fun _ : Fin 3 => (0 : ℝ)) (fun _ => (1 : ℝ)),
      listEvalN [(1, fun _ => 1)] x) = 1 / 48 := by
  have h := integral_listEvalN (d := 3) [(1, fun _ => 1)]
    (by norm_num : (0 : ℚ) ≤ 1)
  norm_num [listMomentN, momentDenom, Fin.sum_univ_succ, Fin.init] at h
  simpa using h

end LeanLab.ChenDoubleSieve.Task587
