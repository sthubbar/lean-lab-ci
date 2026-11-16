import LeanLab.ChenDoubleSieve.Task587MixedMoments

/-!
Exact moments for a separated first interval and an ordered final block.
Source: Wu 2004 Lemma 5.2 page 26, https://arxiv.org/abs/0705.1652.
This is the geometry of D2,11 and D2,14.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional Task562

/-- Integrating the first coordinate preserves product volume.
Wu 2004 page 26, derived Fubini tool for separated moments. -/
theorem integral_first {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (hf : Integrable f volume) :
    (∫ x, f x) = ∫ u : ℝ, ∫ x : Fin n → ℝ, f (Fin.cons u x) := by
  let e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin (n + 1))).symm
  have hem : MeasurePreserving e volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1))).symm _
  have hi : Integrable (fun p => f (e p)) volume :=
    (hem.integrable_comp_emb e.measurableEmbedding).mpr hf
  rw [← hem.integral_comp' f]
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod _ hi]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with u
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  congr 1
  simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']

/-- The separated first coordinate imposes no new restriction on the later ordered block.
Wu 2004 page 26, D2,11 and D2,14 slicing identity. -/
theorem domain_cons_separated {n : ℕ} {a b c d u : ℝ} (hbc : b ≤ c)
    (hu : u ∈ Set.Icc a b) (x : Fin n → ℝ) :
    Fin.cons u x ∈ domain (Fin.cons a (fun _ => c)) (Fin.cons b (fun _ => d)) ↔
      x ∈ domain (fun _ => c) (fun _ => d) := by
  constructor
  · intro hx
    constructor
    · intro i j hij
      simpa using hx.1 (Fin.succ_le_succ_iff.mpr hij)
    · intro j
      simpa using hx.2 j.succ
  · intro hx
    constructor
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _; exact le_rfl
        · intro _; simpa using (hu.2.trans hbc).trans (hx.2 j).1
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro hij; exact False.elim (by simpa using hij)
        · intro hij; simpa using hx.1 (Fin.succ_le_succ_iff.mp hij)
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hu
      · simpa using hx.2 j

/-- The exact shifted monomial moment factors across the separated first interval.
Wu 2004 page 26, derived D2,11 and D2,14 polynomial quadrature. -/
theorem separated_ordered_monomial (n : ℕ) (k : Fin (n + 1) → ℕ)
    {a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (∫ x in domain (Fin.cons a (fun _ : Fin n => c)) (Fin.cons b (fun _ => d)),
      ∏ j, (x j - (Fin.cons a (fun _ : Fin n => c) : Fin (n + 1) → ℝ) j) ^ k j) =
      ((b - a) ^ (k 0 + 1) / (k 0 + 1)) *
      ((d - c) ^ ((∑ j, (Fin.tail k) j) + n) / momentDenom n (Fin.tail k)) := by
  let D := domain (Fin.cons a (fun _ : Fin n => c)) (Fin.cons b (fun _ => d))
  let f := fun x : Fin (n + 1) → ℝ =>
    ∏ j, (x j - (Fin.cons a (fun _ : Fin n => c) : Fin (n + 1) → ℝ) j) ^ k j
  have hD : MeasurableSet D := (Wu04I1.domain_isCompact _ _).measurableSet
  have hi : IntegrableOn f D volume := by
    apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
    fun_prop
  have hm := integral_first (D.indicator f) (hi.integrable_indicator hD)
  rw [MeasureTheory.integral_indicator hD] at hm
  have hinner (u : ℝ) : (∫ x : Fin n → ℝ, D.indicator f (Fin.cons u x)) =
      (Set.Icc a b).indicator (fun u =>
        ((d - c) ^ ((∑ j, (Fin.tail k) j) + n) / momentDenom n (Fin.tail k)) *
        (u - a) ^ k 0) u := by
    by_cases hu : u ∈ Set.Icc a b
    · have heq : (fun x : Fin n → ℝ => D.indicator f (Fin.cons u x)) =
          fun x => (domain (fun _ : Fin n => c) (fun _ => d)).indicator
            (fun x => ∏ j, (x j - c) ^ (Fin.tail k) j) x * (u - a) ^ k 0 := by
        funext x
        by_cases hx : x ∈ domain (fun _ : Fin n => c) (fun _ => d)
        · rw [indicator_of_mem ((domain_cons_separated hbc hu x).mpr hx), indicator_of_mem hx]
          simp [f, Fin.prod_univ_succ, Fin.tail, mul_comm]
        · rw [indicator_of_notMem (fun h => hx ((domain_cons_separated hbc hu x).mp h)),
            indicator_of_notMem hx]
          simp
      rw [heq, MeasureTheory.integral_mul_const,
        MeasureTheory.integral_indicator (Wu04I1.domain_isCompact _ _).measurableSet,
        ordered_shifted_monomial n (Fin.tail k) hcd, indicator_of_mem hu]
    · have hz (x : Fin n → ℝ) : D.indicator f (Fin.cons u x) = 0 := by
        apply indicator_of_notMem
        intro hx
        exact hu (by simpa using hx.2 0)
      simp only [hz, integral_zero, indicator_of_notMem hu]
  simp_rw [hinner] at hm
  rw [MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ k 0) a,
    integral_pow] at hm
  simpa only [sub_self, zero_pow (Nat.succ_ne_zero _), sub_zero, mul_comm] using hm

/-- Rational exact moments for a separated first interval and ordered remaining block.
Wu 2004 page 26, derived computable certificate arithmetic. -/
def listMomentFirst {n : ℕ} (ts : List (ℚ × (Fin (n + 1) → ℕ))) (a b c d : ℚ) : ℚ :=
  (ts.map fun t => t.1 * ((b - a) ^ (t.2 0 + 1) / (t.2 0 + 1)) *
    ((d - c) ^ ((∑ j, (Fin.tail t.2) j) + n) / momentDenom n (Fin.tail t.2))).sum

/-- Exact list integration factors over the separated first interval and ordered block.
Wu 2004 page 26, derived D2,11 and D2,14 quadrature theorem. -/
theorem integral_listEvalFirst {n : ℕ} (ts : List (ℚ × (Fin (n + 1) → ℕ)))
    {a b c d : ℚ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (∫ x in domain (Fin.cons (a : ℝ) (fun _ : Fin n => (c : ℝ)))
        (Fin.cons (b : ℝ) (fun _ => (d : ℝ))),
      listEvalN ts (fun j => x j - (Fin.cons (a : ℝ) (fun _ : Fin n => (c : ℝ)) :
        Fin (n + 1) → ℝ) j)) = (listMomentFirst ts a b c d : ℝ) := by
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hbc' : (b : ℝ) ≤ (c : ℝ) := by exact_mod_cast hbc
  have hcd' : (c : ℝ) ≤ (d : ℝ) := by exact_mod_cast hcd
  induction ts with
  | nil => simp [listEvalN, listMomentFirst]
  | cons t ts ih =>
    let lo : Fin (n + 1) → ℝ := Fin.cons (a : ℝ) (fun _ : Fin n => (c : ℝ))
    let hi : Fin (n + 1) → ℝ := Fin.cons (b : ℝ) (fun _ : Fin n => (d : ℝ))
    have ht : IntegrableOn (fun x : Fin (n + 1) → ℝ =>
        (t.1 : ℝ) * ∏ j, (x j - lo j) ^ t.2 j) (domain lo hi) volume := by
      apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
      fun_prop
    have hs : IntegrableOn (fun x : Fin (n + 1) → ℝ => listEvalN ts (fun j => x j - lo j))
        (domain lo hi) volume := by
      apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
      exact ((listEvalN_continuous ts).comp (by fun_prop)).continuousOn
    change (∫ x in domain lo hi,
      (t.1 : ℝ) * (∏ j, (x j - lo j) ^ t.2 j) + listEvalN ts (fun j => x j - lo j)) = _
    rw [MeasureTheory.integral_add ht hs, MeasureTheory.integral_const_mul,
      separated_ordered_monomial n t.2 hab' hbc' hcd', ih]
    simp only [listMomentFirst, List.map_cons, List.sum_cons]
    push_cast
    ring

end LeanLab.ChenDoubleSieve.Task587
