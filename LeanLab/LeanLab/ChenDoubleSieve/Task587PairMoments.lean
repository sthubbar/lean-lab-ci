import LeanLab.ChenDoubleSieve.Task587CellCertificate
import LeanLab.ChenDoubleSieve.Task587MixedMoments

/-!
Exact moments on the two ordered pairs of Wu 2004 Lemma 5.2 page 26, D2,18.
Source: https://arxiv.org/abs/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional Task562

/-- Fixing the last coordinate leaves an ordered pair and a separated final interval.
Wu 2004 page 26, D2,18, derived slicing identity. -/
theorem pair_domain_snoc {a b c w : ℝ} (hw : w ∈ Set.Icc b c) (x : Fin 3 → ℝ) :
    Fin.snoc x w ∈ domain (![a, a, b, b] : Fin 4 → ℝ) ![b, b, c, c] ↔
      x ∈ domain (![a, a, b] : Fin 3 → ℝ) ![b, b, w] := by
  constructor
  · intro hx
    constructor
    · intro i j hij
      simpa [Fin.snoc] using hx.1 (Fin.castSucc_le_castSucc_iff.mpr hij)
    · intro j
      fin_cases j
      · simpa [Fin.snoc] using hx.2 (0 : Fin 4)
      · simpa [Fin.snoc] using hx.2 (1 : Fin 4)
      · constructor
        · have hl := (hx.2 (2 : Fin 3).castSucc).1
          rw [Fin.snoc_castSucc] at hl
          exact hl
        · change x 2 ≤ w
          have hh := hx.1 (show (2 : Fin 3).castSucc ≤ Fin.last 3 by decide)
          simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hh
  · intro hx
    constructor
    · rw [Fin.monotone_iff_le_succ]
      intro j
      fin_cases j
      · change x 0 ≤ x 1
        exact hx.1 (by decide)
      · change x 1 ≤ x 2
        exact hx.1 (by decide)
      · change x 2 ≤ w
        simpa [Fin.snoc] using (hx.2 (2 : Fin 3)).2
    · intro j
      fin_cases j
      · simpa [Fin.snoc] using hx.2 (0 : Fin 3)
      · simpa [Fin.snoc] using hx.2 (1 : Fin 3)
      · change b ≤ x 2 ∧ x 2 ≤ c
        exact ⟨(hx.2 2).1, (hx.2 2).2.trans hw.2⟩
      · simpa [Fin.snoc] using hw

/-- A shifted monomial moment factors over the two ordered pairs.
Wu 2004 page 26, D2,18, derived exact polynomial moment. -/
theorem pair_shifted_monomial (k : Fin 4 → ℕ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ x in domain (![a, a, b, b] : Fin 4 → ℝ) ![b, b, c, c],
      ∏ j, (x j - (![a, a, b, b] : Fin 4 → ℝ) j) ^ k j) =
      ((b - a) ^ (k 0 + k 1 + 2) / momentDenom 2 ![k 0, k 1]) *
      ((c - b) ^ (k 2 + k 3 + 2) / momentDenom 2 ![k 2, k 3]) := by
  let D := domain (![a, a, b, b] : Fin 4 → ℝ) ![b, b, c, c]
  let f := fun x : Fin 4 → ℝ => ∏ j, (x j - (![a, a, b, b] : Fin 4 → ℝ) j) ^ k j
  let A : ℝ := (b - a) ^ (k 0 + k 1 + 2) / momentDenom 2 ![k 0, k 1]
  have hD : MeasurableSet D := (Wu04I1.domain_isCompact _ _).measurableSet
  have hi : IntegrableOn f D volume := by
    apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
    fun_prop
  have hm := integral_last (D.indicator f) (hi.integrable_indicator hD)
  rw [MeasureTheory.integral_indicator hD] at hm
  have hsmall (w : ℝ) (hw : w ∈ Set.Icc b c) :
      (∫ x in domain (![a, a, b] : Fin 3 → ℝ) ![b, b, w],
        ∏ j, (x j - (![a, a, b] : Fin 3 → ℝ) j) ^ (Fin.init k) j) =
      A * ((w - b) ^ (k 2 + 1) / ((k 2 : ℝ) + 1)) := by
    have h := ordered_separated_monomial 2 (Fin.init k) hab le_rfl hw.1
    have hlo : Fin.snoc (fun _ : Fin 2 => a) b = (![a, a, b] : Fin 3 → ℝ) := by
      ext j; fin_cases j <;> rfl
    have hhi : Fin.snoc (fun _ : Fin 2 => b) w = (![b, b, w] : Fin 3 → ℝ) := by
      ext j; fin_cases j <;> rfl
    rw [hlo, hhi] at h
    have hk : Fin.init (Fin.init k) = (![k 0, k 1] : Fin 2 → ℕ) := by
      ext j; fin_cases j <;> rfl
    rw [hk] at h
    simpa [A, Fin.init, Fin.sum_univ_succ, add_assoc] using h
  have hprod (x : Fin 3 → ℝ) (w : ℝ) : f (Fin.snoc x w) =
      (∏ j, (x j - (![a, a, b] : Fin 3 → ℝ) j) ^ (Fin.init k) j) * (w - b) ^ k 3 := by
    norm_num [f, Fin.prod_univ_succ, Fin.init, Fin.snoc]
    <;> ring
  have hinner (w : ℝ) : (∫ x : Fin 3 → ℝ, D.indicator f (Fin.snoc x w)) =
      (Set.Icc b c).indicator (fun w => (A / ((k 2 : ℝ) + 1)) *
        (w - b) ^ (k 2 + k 3 + 1)) w := by
    by_cases hw : w ∈ Set.Icc b c
    · have heq : (fun x : Fin 3 → ℝ => D.indicator f (Fin.snoc x w)) =
          fun x => (domain (![a, a, b] : Fin 3 → ℝ) ![b, b, w]).indicator
            (fun x => ∏ j, (x j - (![a, a, b] : Fin 3 → ℝ) j) ^ (Fin.init k) j) x *
            (w - b) ^ k 3 := by
        funext x
        by_cases hx : x ∈ domain (![a, a, b] : Fin 3 → ℝ) ![b, b, w]
        · rw [indicator_of_mem ((pair_domain_snoc hw x).mpr hx), indicator_of_mem hx]
          exact hprod x w
        · rw [indicator_of_notMem (fun h => hx ((pair_domain_snoc hw x).mp h)), indicator_of_notMem hx]
          simp
      rw [heq, MeasureTheory.integral_mul_const,
        MeasureTheory.integral_indicator (Wu04I1.domain_isCompact _ _).measurableSet,
        hsmall w hw, indicator_of_mem hw]
      calc
        _ = (A / ((k 2 : ℝ) + 1)) * ((w - b) ^ (k 2 + 1) * (w - b) ^ k 3) := by ring
        _ = _ := by
          rw [← pow_add]
          congr 2
          omega
    · have hz (x : Fin 3 → ℝ) : D.indicator f (Fin.snoc x w) = 0 := by
        apply indicator_of_notMem
        intro hx
        exact hw (by simpa [Fin.snoc] using hx.2 (3 : Fin 4))
      simp only [hz, integral_zero, indicator_of_notMem hw]
  simp_rw [hinner] at hm
  rw [MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hbc, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ (k 2 + k 3 + 1)) b,
    integral_pow] at hm
  change (∫ x in D, f x) = _
  rw [hm]
  simp [A, momentDenom, Fin.init, Fin.sum_univ_succ, div_eq_mul_inv, mul_inv_rev, add_assoc]
  <;> ring

/-- Exact list integration on two separated ordered pairs equals the rational candidate.
Wu 2004 page 26, D2,18, derived finite certificate theorem. -/
theorem integral_listEvalPair (ts : List (ℚ × (Fin 4 → ℕ))) {a b c : ℚ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ x in domain (![(a : ℝ), a, b, b] : Fin 4 → ℝ) ![b, b, c, c],
      listEvalN ts (fun j => x j - (![(a : ℝ), a, b, b] : Fin 4 → ℝ) j)) =
      (listMomentPair ts a b c : ℝ) := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hbc' : (b : ℝ) ≤ c := by exact_mod_cast hbc
  induction ts with
  | nil => simp [listEvalN, listMomentPair]
  | cons t ts ih =>
    let lo : Fin 4 → ℝ := ![(a : ℝ), a, b, b]
    let hi : Fin 4 → ℝ := ![(b : ℝ), b, c, c]
    have ht : IntegrableOn (fun x : Fin 4 → ℝ => (t.1 : ℝ) * ∏ j, (x j - lo j) ^ t.2 j)
        (domain lo hi) volume := by
      apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
      fun_prop
    have hs : IntegrableOn (fun x : Fin 4 → ℝ => listEvalN ts (fun j => x j - lo j))
        (domain lo hi) volume := by
      apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
      exact ((listEvalN_continuous ts).comp (by fun_prop)).continuousOn
    change (∫ x in domain lo hi, (t.1 : ℝ) * (∏ j, (x j - lo j) ^ t.2 j) +
      listEvalN ts (fun j => x j - lo j)) = _
    rw [MeasureTheory.integral_add ht hs, MeasureTheory.integral_const_mul,
      pair_shifted_monomial t.2 hab' hbc', ih]
    simp only [listMomentPair, List.map_cons, List.sum_cons]
    push_cast
    ring

end LeanLab.ChenDoubleSieve.Task587
