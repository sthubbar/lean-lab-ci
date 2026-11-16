import LeanLab.ChenDoubleSieve.Task587PolynomialTools

/-!
Exact moments for an ordered block followed by a separated interval.
Source: Wu 2004 Lemma 5.2 page 26, https://arxiv.org/abs/0705.1652.
This is the geometry of D2,10 and of the separated last-coordinate domains.
AI wrote the Lean code. Binary Goldbach is open.
-/

set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional Task562

/-- A last coordinate in a separated interval does not constrain the earlier ordered block.
Wu 2004 page 26, derived D2,10 slicing identity. -/
theorem domain_snoc_separated {n : ℕ} {a b c d u : ℝ} (hbc : b ≤ c)
    (hu : u ∈ Set.Icc c d) (x : Fin n → ℝ) :
    Fin.snoc x u ∈ domain (Fin.snoc (fun _ => a) c) (Fin.snoc (fun _ => b) d) ↔
      x ∈ domain (fun _ => a) (fun _ => b) := by
  constructor
  · intro hx
    constructor
    · intro i j hij
      simpa using hx.1 (Fin.castSucc_le_castSucc_iff.mpr hij)
    · intro j
      simpa using hx.2 j.castSucc
  · intro hx
    constructor
    · intro i j hij
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · simpa using hx.1 (Fin.castSucc_le_castSucc_iff.mp hij)
        · simpa using ((hx.2 i).2.trans hbc).trans hu.1
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · exact False.elim (by simpa using hij)
        · exact le_rfl
    · intro j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · simpa using hx.2 j
      · simpa using hu

/-- The exact shifted monomial moment factors over the two separated pieces.
Wu 2004 page 26, derived polynomial quadrature for D2,10. -/
theorem ordered_separated_monomial (n : ℕ) (k : Fin (n + 1) → ℕ)
    {a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (∫ x in domain (Fin.snoc (fun _ : Fin n => a) c) (Fin.snoc (fun _ => b) d),
      ∏ j, (x j - (Fin.snoc (fun _ : Fin n => a) c : Fin (n + 1) → ℝ) j) ^ k j) =
      ((b - a) ^ ((∑ j, (Fin.init k) j) + n) / momentDenom n (Fin.init k)) *
      ((d - c) ^ (k (Fin.last n) + 1) / (k (Fin.last n) + 1)) := by
  let D := domain (Fin.snoc (fun _ : Fin n => a) c) (Fin.snoc (fun _ => b) d)
  let f := fun x : Fin (n + 1) → ℝ =>
    ∏ j, (x j - (Fin.snoc (fun _ : Fin n => a) c : Fin (n + 1) → ℝ) j) ^ k j
  have hD : MeasurableSet D := (Wu04I1.domain_isCompact _ _).measurableSet
  have hi : IntegrableOn f D volume := by
    apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
    fun_prop
  have hm := integral_last (D.indicator f) (hi.integrable_indicator hD)
  rw [MeasureTheory.integral_indicator hD] at hm
  have hinner (u : ℝ) : (∫ x : Fin n → ℝ, D.indicator f (Fin.snoc x u)) =
      (Set.Icc c d).indicator (fun u =>
        ((b - a) ^ ((∑ j, (Fin.init k) j) + n) / momentDenom n (Fin.init k)) *
        (u - c) ^ k (Fin.last n)) u := by
    by_cases hu : u ∈ Set.Icc c d
    · have heq : (fun x : Fin n → ℝ => D.indicator f (Fin.snoc x u)) =
          fun x => (domain (fun _ : Fin n => a) (fun _ => b)).indicator
            (fun x => ∏ j, (x j - a) ^ (Fin.init k) j) x *
            (u - c) ^ k (Fin.last n) := by
        funext x
        by_cases hx : x ∈ domain (fun _ : Fin n => a) (fun _ => b)
        · rw [indicator_of_mem ((domain_snoc_separated hbc hu x).mpr hx), indicator_of_mem hx]
          simp [f, Fin.prod_univ_castSucc, Fin.init]
        · rw [indicator_of_notMem (fun h => hx ((domain_snoc_separated hbc hu x).mp h)),
            indicator_of_notMem hx]
          simp
      rw [heq, MeasureTheory.integral_mul_const,
        MeasureTheory.integral_indicator (Wu04I1.domain_isCompact _ _).measurableSet,
        ordered_shifted_monomial n (Fin.init k) hab, indicator_of_mem hu]
    · have hz (x : Fin n → ℝ) : D.indicator f (Fin.snoc x u) = 0 := by
        apply indicator_of_notMem
        intro hx
        exact hu (by simpa using hx.2 (Fin.last n))
      simp only [hz, integral_zero, indicator_of_notMem hu]
  simp_rw [hinner] at hm
  rw [MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hcd, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ k (Fin.last n)) c,
    integral_pow] at hm
  simpa only [sub_self, zero_pow (Nat.succ_ne_zero _), sub_zero] using hm

/-- The rational moment for a list on an ordered block and a separated final interval.
Wu 2004 page 26, derived computable mixed-domain certificate arithmetic. -/
def listMomentLast {n : ℕ} (ts : List (ℚ × (Fin (n + 1) → ℕ))) (a b c d : ℚ) : ℚ :=
  (ts.map fun t => t.1 *
    ((b - a) ^ ((∑ j, (Fin.init t.2) j) + n) / momentDenom n (Fin.init t.2)) *
    ((d - c) ^ (t.2 (Fin.last n) + 1) / (t.2 (Fin.last n) + 1))).sum

/-- Exact list integration on a separated mixed domain reduces to rational arithmetic.
Wu 2004 page 26, derived D2,10 quadrature theorem. -/
theorem integral_listEvalLast {n : ℕ} (ts : List (ℚ × (Fin (n + 1) → ℕ)))
    {a b c d : ℚ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (∫ x in domain (Fin.snoc (fun _ : Fin n => (a : ℝ)) (c : ℝ))
        (Fin.snoc (fun _ => (b : ℝ)) (d : ℝ)),
      listEvalN ts (fun j => x j - (Fin.snoc (fun _ : Fin n => (a : ℝ)) (c : ℝ) : Fin (n + 1) → ℝ) j)) =
      (listMomentLast ts a b c d : ℝ) := by
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hbc' : (b : ℝ) ≤ (c : ℝ) := by exact_mod_cast hbc
  have hcd' : (c : ℝ) ≤ (d : ℝ) := by exact_mod_cast hcd
  induction ts with
  | nil => simp [listEvalN, listMomentLast]
  | cons t ts ih =>
    let lo : Fin (n + 1) → ℝ := Fin.snoc (fun _ : Fin n => (a : ℝ)) (c : ℝ)
    let hi : Fin (n + 1) → ℝ := Fin.snoc (fun _ : Fin n => (b : ℝ)) (d : ℝ)
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
      ordered_separated_monomial n t.2 hab' hbc' hcd', ih]
    simp only [listMomentLast, List.map_cons, List.sum_cons]
    push_cast
    ring

end LeanLab.ChenDoubleSieve.Task587
