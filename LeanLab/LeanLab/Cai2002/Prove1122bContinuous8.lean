/-
Twin proof of the LEAF `leaf8_continuous` of `Split1122bSeries8.lean`.

Source: Bordignon, Johnston, Starichkova, arXiv 2207.09452, page 6, displays 13 to 18,
quoting Nathanson Theorem 9.4: the functions f_n of displays 15 to 17 are continuous
where the paper uses them, n odd with s ≥ 1 and n even with s ≥ 2, by induction on n,
since s ↦ the integral over t > s of an integrable function is continuous; display 18 with
Lemma 8 gives a summable majorant uniform in s, so the series 13 and 14 converge
uniformly and their sums are continuous.

This file proves `leaf8_continuous_twin` with no sorry upstream: the majorant uses
key_l8306, display 18 with c_n = 0.9607 for every n ≥ 1, proved in `Split306Theorem6.lean`,
not leaf306_display18, whose Table 2 part leaf306_lemma7 is still a LEAF.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Prove1122bSummable8

open Finset Real

noncomputable section

namespace LeanLab.Cai2002

/-- The tail integral s ↦ ∫ over t > s of g is continuous on [a, ∞) when g is integrable
on (a, ∞). Used for display 16 and 17, Nathanson Theorem 9.4. -/
theorem contOn_tail_integral_c8 (g : ℝ → ℝ) (a : ℝ)
    (hg : MeasureTheory.IntegrableOn g (Set.Ioi a)) :
    ContinuousOn (fun s => ∫ t in Set.Ioi s, g t) (Set.Ici a) := by
  set g' := (Set.Ioi a).indicator g with hg'def
  have hg' : MeasureTheory.Integrable g' :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Ioi).2 hg
  have hprim : Continuous fun b => ∫ x in a..b, g' x :=
    intervalIntegral.continuous_primitive (fun _ _ => hg'.intervalIntegrable) a
  refine ((continuous_const (y := ∫ t in Set.Ioi a, g t)).sub hprim).continuousOn.congr ?_
  intro s hs
  have hs' : a ≤ s := hs
  have hsplit : ∫ t in Set.Ioi a, g t = (∫ t in Set.Ioc a s, g t) + ∫ t in Set.Ioi s, g t := by
    rw [← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hg.mono_set Set.Ioc_subset_Ioi_self) (hg.mono_set (Set.Ioi_subset_Ioi hs')),
      Set.Ioc_union_Ioi_eq_Ioi hs']
  have hint : ∫ x in a..s, g' x = ∫ t in Set.Ioc a s, g t := by
    rw [intervalIntegral.integral_of_le hs']
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    simp only [hg'def]
    exact Set.indicator_of_mem (Set.Ioc_subset_Ioi_self ht) g
  simp only [Pi.sub_apply]
  rw [hint]
  linarith

/-- Integrability of t ↦ f_m(t - 1) on (a, ∞), from continuity, nonnegativity and display 18
with the integrable shifted h, BJS page 6 and Lemma 10. -/
theorem integrableOn_shift_c8 (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha : 1 ≤ a)
    (hcont : ContinuousOn (fun t => bjsF306 m (t - 1)) (Set.Ioi a))
    (hdom : ∀ t, a < t → (Odd m ∧ 1 ≤ t - 1) ∨ (Even m ∧ 2 ≤ t - 1)) :
    MeasureTheory.IntegrableOn (fun t => bjsF306 m (t - 1)) (Set.Ioi a) := by
  have hK := ((leaf306_hshift_integrable a ha).const_mul (2 * exp 2 * (0.9607 : ℝ) ^ (m - 1)))
  refine MeasureTheory.Integrable.mono' hK (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have h0 := leaf306_fn_nonneg m (t - 1) (hdom t ht)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact key_l8306 m hm (t - 1) (hdom t ht)

/-- Shift of continuity: f continuous on [a - 1, ∞) gives t ↦ f(t - 1) continuous on
[a, ∞). -/
theorem contOn_shift_c8 (f : ℝ → ℝ) (a : ℝ) (hf : ContinuousOn f (Set.Ici (a - 1))) :
    ContinuousOn (fun t => f (t - 1)) (Set.Ici a) :=
  hf.comp (continuousOn_id.sub continuousOn_const) (fun t ht => by
    simp only [Set.mem_Ici] at ht ⊢; linarith)

/-- f_1 of display 15 is continuous on [1, ∞): (3 - s)/s vanishes at s = 3. -/
theorem contOn_f1_c8 : ContinuousOn (bjsF306 1) (Set.Ici 1) := by
  have h1 : ContinuousOn (fun s : ℝ => (3 - s) / s) (Set.Ici 1) :=
    (continuousOn_const.sub continuousOn_id).div continuousOn_id
      (fun s hs => by simp only [Set.mem_Ici] at hs; positivity)
  have h2 : ContinuousOn (fun s : ℝ => max ((3 - s) / s) 0) (Set.Ici 1) :=
    (continuous_id.max continuous_const).comp_continuousOn h1
  refine h2.congr (fun s hs => ?_)
  have hs' : (1 : ℝ) ≤ s := hs
  simp only [bjsF306]
  split_ifs with h
  · exact (max_eq_left (div_nonneg (by linarith) (by linarith))).symm
  · exact (max_eq_right (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))).symm

/-- Continuity of each f_n where the paper uses it, BJS displays 15 to 17, Nathanson
Theorem 9.4: odd n on [1, ∞) and even n on [2, ∞), by induction on n. -/
theorem contOn_fn_c8 (n : ℕ) :
    (Odd n → ContinuousOn (bjsF306 n) (Set.Ici 1)) ∧
    (Even n → ContinuousOn (bjsF306 n) (Set.Ici 2)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ =>
      refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
      simp only [bjsF306]; exact continuousOn_const
    | 1, _ => exact ⟨fun _ => contOn_f1_c8, fun h => absurd h (by decide)⟩
    | m + 2, ih =>
      rcases Nat.even_or_odd (m + 2) with he | ho
      · -- even n = m + 2, display 16 on [2, ∞)
        have hodd1 : Odd (m + 1) := by
          rcases Nat.even_or_odd (m + 1) with he' | ho'
          · exact absurd he (by rw [Nat.not_even_iff_odd]; exact he'.add_one)
          · exact ho'
        have hc1 := (ih (m + 1) (by omega)).1 hodd1
        have hg : ContinuousOn (fun t => bjsF306 (m + 1) (t - 1)) (Set.Ici 2) :=
          contOn_shift_c8 _ 2 (by norm_num; exact hc1)
        have hI := integrableOn_shift_c8 (m + 1) (by omega) 2 (by norm_num)
          (hg.mono Set.Ioi_subset_Ici_self)
          (fun t ht => Or.inl ⟨hodd1, by linarith [show (2 : ℝ) < t from ht]⟩)
        have hT := contOn_tail_integral_c8 _ 2 hI
        have hne : ¬ Odd (m + 2) := by rw [Nat.not_odd_iff_even]; exact he
        refine ⟨fun h => absurd h hne, fun _ => ?_⟩
        refine (hT.div continuousOn_id (fun s hs => by
          simp only [Set.mem_Ici] at hs; simp only [id]; linarith)).congr (fun s hs => ?_)
        simp only [Pi.div_apply, id]
        simp only [bjsF306, hne, false_and, ite_false]
      · -- odd n = m + 2, displays 16 and 17 on [1, ∞)
        have hev1 : Even (m + 1) := by
          rcases Nat.even_or_odd (m + 1) with he' | ho'
          · exact he'
          · exact absurd ho (by rw [Nat.not_odd_iff_even]; exact ho'.add_one)
        have hc1 := (ih (m + 1) (by omega)).2 hev1
        have hg : ContinuousOn (fun t => bjsF306 (m + 1) (t - 1)) (Set.Ici 3) :=
          contOn_shift_c8 _ 3 (by norm_num; exact hc1)
        have hI := integrableOn_shift_c8 (m + 1) (by omega) 3 (by norm_num)
          (hg.mono Set.Ioi_subset_Ici_self)
          (fun t ht => Or.inr ⟨hev1, by linarith [show (3 : ℝ) < t from ht]⟩)
        have hT := contOn_tail_integral_c8 _ 3 hI
        have hTm : ContinuousOn
            (fun s : ℝ => ∫ t in Set.Ioi (max s 3), bjsF306 (m + 1) (t - 1)) (Set.Ici 1) :=
          hT.comp (continuous_id.max continuous_const).continuousOn
            (fun s _ => by simp only [Set.mem_Ici]; exact le_max_right _ _)
        have hne : ¬ Even (m + 2) := by rw [Nat.not_even_iff_odd]; exact ho
        refine ⟨fun _ => ?_, fun h => absurd h hne⟩
        refine (hTm.div continuousOn_id (fun s hs => by
          simp only [Set.mem_Ici] at hs; simp only [id]; linarith)).congr (fun s hs => ?_)
        simp only [Pi.div_apply, id]
        simp only [bjsF306, ho, true_and]
        split_ifs with h3
        · rw [max_eq_right h3]
        · rw [max_eq_left (le_of_lt (not_le.mp h3))]

/-- h(s) ≤ e ^ (-2) for s ≥ 1. -/
theorem hSieve_le_c8 (s : ℝ) (_hs : 1 ≤ s) : LeanLab.ChenExplicit.hSieve s ≤ exp (-2) := by
  unfold LeanLab.ChenExplicit.hSieve
  split_ifs with h2 h3
  · exact le_rfl
  · exact exp_le_exp.mpr (by linarith)
  · have hs3 : 3 < s := by linarith [not_le.mp h3]
    have hinv : 3 * s⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by linarith)]; linarith
    have he : exp (-s) ≤ exp (-2) := exp_le_exp.mpr (by linarith)
    calc 3 * s⁻¹ * exp (-s) ≤ 1 * exp (-2) :=
          mul_le_mul hinv he (exp_pos _).le (by norm_num)
      _ = exp (-2) := one_mul _

/-- The uniform majorant of display 18 with Lemma 8, c_n = 0.9607 for every n ≥ 1:
2 e^2 · 0.9607^(n-1) · e^(-2). -/
def majU8 (n : ℕ) : ℝ := 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * exp (-2)

theorem majU8_nonneg (n : ℕ) : 0 ≤ majU8 n := by
  unfold majU8; positivity

/-- The uniform majorant is summable, a geometric series of ratio 0.9607. -/
theorem majU8_summable : Summable majU8 := by
  rw [← summable_nat_add_iff 1]
  have hg : Summable (fun m : ℕ => (2 * exp 2 * exp (-2)) * (0.9607 : ℝ) ^ m) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine hg.congr (fun m => ?_)
  unfold majU8
  rw [show m + 1 - 1 = m by omega]
  ring

/-- The terms of the restricted series are bounded by the uniform majorant, by
display 18 with c_n = 0.9607, Lemma 8, and h(s) ≤ e^(-2). -/
theorem term_le_majU8 (P : ℕ → Prop) [DecidablePred P] (s : ℝ) (hs1 : 1 ≤ s)
    (hP : ∀ n, P n → (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s)) (n : ℕ) :
    ‖(if P n then bjsF306 n s else 0)‖ ≤ majU8 n := by
  split_ifs with h
  · have h0 := leaf306_fn_nonneg n s (hP n h)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp only [bjsF306]; exact majU8_nonneg 0
    · refine (key_l8306 n hn s (hP n h)).trans ?_
      unfold majU8
      have h2 : 0 ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) := by positivity
      exact mul_le_mul_of_nonneg_left (hSieve_le_c8 s hs1) h2
  · simp only [norm_zero]; exact majU8_nonneg n

/-- Twin of the LEAF `leaf8_continuous` of `Split1122bSeries8.lean`: the sums of the series
13 and 14 of BJS page 6 are continuous on [1, ∞) and [2, ∞), by continuity of each f_n and
uniform convergence under display 18 with Lemma 8. Unconditional. -/
theorem leaf8_continuous_twin :
    ContinuousOn (fun s : ℝ => ∑' n : ℕ, if Odd n then bjsF306 n s else 0) (Set.Ici 1) ∧
    ContinuousOn (fun s : ℝ => ∑' n : ℕ, if Even n then bjsF306 n s else 0) (Set.Ici 2) := by
  constructor
  · refine continuousOn_tsum (u := majU8) (fun n => ?_) majU8_summable
      (fun n s hs => term_le_majU8 Odd s hs (fun _ h => Or.inl ⟨h, hs⟩) n)
    by_cases h : Odd n
    · simp only [h, ite_true]; exact (contOn_fn_c8 n).1 h
    · simp only [h, ite_false]; exact continuousOn_const
  · refine continuousOn_tsum (u := majU8) (fun n => ?_) majU8_summable
      (fun n s hs => term_le_majU8 Even s (le_trans (by norm_num) hs)
        (fun _ h => Or.inr ⟨h, hs⟩) n)
    by_cases h : Even n
    · simp only [h, ite_true]; exact (contOn_fn_c8 n).2 h
    · simp only [h, ite_false]; exact continuousOn_const

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leaf8_continuous_twin
