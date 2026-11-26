/-
Split of leaf306_series_solve8 of Split306Theorem6.lean: the existence half of
Nathanson Theorem 9.4 as quoted by Bordignon, Johnston and Starichkova,
arXiv 2207.09452v6, papers/P0009.pdf, page 6, displays 8 and 13 to 18.
The twin leaf306_series_solve8_twin is proved from LEAF lemmas:
* summability of the series 13 and 14 from the bound 18 with Lemma 8;
* continuity of their sums, uniform convergence from the same bound;
* the termwise derivatives of s f_n(s) from displays 15 and 16, summed;
* F(3) = 2 e ^ γ / 3, the analytic core of Theorem 9.4, with display 17;
* f(2) = 0 for the series 14, the second analytic boundary value.
The reduction of the series 13 on [1, 3] to its value at s = 3 by display 17 and the
assembly into the delay differential system 8 are proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split306Theorem6

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-! ### Summability of the series 13 and 14, display 18 with Lemma 8 -/

/-- `h` of display 18 is at most `e ^ (-2)` for `s ≥ 1`. -/
private theorem hSieve_le_x8 (s : ℝ) (hs : 1 ≤ s) :
    LeanLab.ChenExplicit.hSieve s ≤ exp (-2) := by
  unfold LeanLab.ChenExplicit.hSieve
  split_ifs with h2 h3
  · exact le_rfl
  · exact exp_le_exp.mpr (by linarith)
  · have hinv : 3 * s⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by linarith)]; linarith
    have he : exp (-s) ≤ exp (-2) := exp_le_exp.mpr (by linarith)
    calc 3 * s⁻¹ * exp (-s) ≤ 1 * exp (-2) :=
          mul_le_mul hinv he (exp_pos _).le (by norm_num)
      _ = exp (-2) := one_mul _

/-- The uniform majorant of display 18 with `c_n = 0.9607`, Lemma 8, for every `n ≥ 1`:
`2 e ^ 2 · 0.9607 ^ (n - 1) · e ^ (-2)`, summable as a geometric series. -/
private theorem summable_maj_x8 :
    Summable (fun n : ℕ => 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * exp (-2)) := by
  rw [← summable_nat_add_iff 1]
  have hg : Summable (fun m : ℕ => (2 * exp 2 * exp (-2)) * (0.9607 : ℝ) ^ m) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine hg.congr (fun m => ?_)
  rw [show m + 1 - 1 = m by omega]
  ring

/-- Each term of the restricted series is bounded by the uniform majorant. -/
private theorem term_le_maj_x8 (P : ℕ → Prop) [DecidablePred P] (s : ℝ) (hs1 : 1 ≤ s)
    (hP : ∀ n, P n → (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s)) (n : ℕ) :
    ‖(if P n then bjsF306 n s else 0)‖ ≤
      2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * exp (-2) := by
  split_ifs with h
  · have h0 := leaf306_fn_nonneg n s (hP n h)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp only [bjsF306]; positivity
    · refine (key_l8306 n hn s (hP n h)).trans ?_
      have h2 : 0 ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) := by positivity
      exact mul_le_mul_of_nonneg_left (hSieve_le_x8 s hs1) h2
  · simp only [norm_zero]; positivity

/-- LEAF: BJS display 18 with Lemma 8, Nathanson Lemma 9.7, page 6: f_n(s) ≤ 2 e ^ 2 c_n ^ (n - 1) h(s)
with c_n ≤ 0.9607 for n ≥ 2, so the series 13 converges for s ≥ 1 and the series 14
for s ≥ 2. Class MEDIUM: needs the bound 18 for all n, a geometric comparison and
nonnegativity, leaf306_fn_nonneg. -/
theorem leaf8_summable :
    (∀ s : ℝ, 1 ≤ s → Summable (fun n : ℕ => if Odd n then bjsF306 n s else 0)) ∧
    (∀ s : ℝ, 2 ≤ s → Summable (fun n : ℕ => if Even n then bjsF306 n s else 0)) := by
  constructor
  · intro s hs
    exact Summable.of_norm_bounded summable_maj_x8
      (fun n => term_le_maj_x8 Odd s hs (fun _ h => Or.inl ⟨h, hs⟩) n)
  · intro s hs
    exact Summable.of_norm_bounded summable_maj_x8
      (fun n => term_le_maj_x8 Even s (by linarith) (fun _ h => Or.inr ⟨h, hs⟩) n)

/-! ### Continuity of the sums of the series 13 and 14 -/

/-- The tail integral `s ↦ ∫ over t > s of g` is continuous on `[a, ∞)` when `g` is
integrable on `(a, ∞)`. -/
private theorem contOn_tail_integral_x8 (g : ℝ → ℝ) (a : ℝ)
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

/-- Integrability of `t ↦ f_m(t - 1)` on `(a, ∞)` from continuity, nonnegativity and display 18
with the integrable shifted `h`. -/
private theorem integrableOn_shift_x8 (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha : 1 ≤ a)
    (hcont : ContinuousOn (fun t => bjsF306 m (t - 1)) (Set.Ioi a))
    (hdom : ∀ t, a < t → (Odd m ∧ 1 ≤ t - 1) ∨ (Even m ∧ 2 ≤ t - 1)) :
    MeasureTheory.IntegrableOn (fun t => bjsF306 m (t - 1)) (Set.Ioi a) := by
  have hK := ((leaf306_hshift_integrable a ha).const_mul (2 * exp 2 * (0.9607 : ℝ) ^ (m - 1)))
  refine MeasureTheory.Integrable.mono' hK (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have h0 := leaf306_fn_nonneg m (t - 1) (hdom t ht)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact key_l8306 m hm (t - 1) (hdom t ht)

/-- Shift of continuity: `f` continuous on `[a - 1, ∞)` gives `t ↦ f(t - 1)` continuous on
`[a, ∞)`. -/
private theorem contOn_shift_x8 (f : ℝ → ℝ) (a : ℝ) (hf : ContinuousOn f (Set.Ici (a - 1))) :
    ContinuousOn (fun t => f (t - 1)) (Set.Ici a) :=
  hf.comp (continuousOn_id.sub continuousOn_const) (fun t ht => by
    simp only [Set.mem_Ici] at ht ⊢; linarith)

/-- `f_1` of display 15 is continuous on `[1, ∞)`. -/
private theorem contOn_f1_x8 : ContinuousOn (bjsF306 1) (Set.Ici 1) := by
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

/-- Continuity of each `f_n` where the paper uses it: odd `n` on `[1, ∞)` and even `n` on
`[2, ∞)`, by induction on `n`. -/
private theorem contOn_fn_x8 (n : ℕ) :
    (Odd n → ContinuousOn (bjsF306 n) (Set.Ici 1)) ∧
    (Even n → ContinuousOn (bjsF306 n) (Set.Ici 2)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ =>
      refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
      simp only [bjsF306]; exact continuousOn_const
    | 1, _ => exact ⟨fun _ => contOn_f1_x8, fun h => absurd h (by decide)⟩
    | m + 2, ih =>
      rcases Nat.even_or_odd (m + 2) with he | ho
      · have hodd1 : Odd (m + 1) := by
          rcases Nat.even_or_odd (m + 1) with he' | ho'
          · exact absurd he (by rw [Nat.not_even_iff_odd]; exact he'.add_one)
          · exact ho'
        have hc1 := (ih (m + 1) (by omega)).1 hodd1
        have hg : ContinuousOn (fun t => bjsF306 (m + 1) (t - 1)) (Set.Ici 2) :=
          contOn_shift_x8 _ 2 (by norm_num; exact hc1)
        have hI := integrableOn_shift_x8 (m + 1) (by omega) 2 (by norm_num)
          (hg.mono Set.Ioi_subset_Ici_self)
          (fun t ht => Or.inl ⟨hodd1, by linarith [show (2 : ℝ) < t from ht]⟩)
        have hT := contOn_tail_integral_x8 _ 2 hI
        have hne : ¬ Odd (m + 2) := by rw [Nat.not_odd_iff_even]; exact he
        refine ⟨fun h => absurd h hne, fun _ => ?_⟩
        refine (hT.div continuousOn_id (fun s hs => by
          simp only [Set.mem_Ici] at hs; simp only [id]; linarith)).congr (fun s hs => ?_)
        simp only [Pi.div_apply, id]
        simp only [bjsF306, hne, false_and, ite_false]
      · have hev1 : Even (m + 1) := by
          rcases Nat.even_or_odd (m + 1) with he' | ho'
          · exact he'
          · exact absurd ho (by rw [Nat.not_odd_iff_even]; exact ho'.add_one)
        have hc1 := (ih (m + 1) (by omega)).2 hev1
        have hg : ContinuousOn (fun t => bjsF306 (m + 1) (t - 1)) (Set.Ici 3) :=
          contOn_shift_x8 _ 3 (by norm_num; exact hc1)
        have hI := integrableOn_shift_x8 (m + 1) (by omega) 3 (by norm_num)
          (hg.mono Set.Ioi_subset_Ici_self)
          (fun t ht => Or.inr ⟨hev1, by linarith [show (3 : ℝ) < t from ht]⟩)
        have hT := contOn_tail_integral_x8 _ 3 hI
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

/-- LEAF: continuity of the sums of the series 13 and 14 of BJS page 6, Nathanson
Theorem 9.4: each f_n is continuous where used, displays 15 to 17, and the bound 18
gives uniform convergence by the Weierstrass test. Class MEDIUM. -/
theorem leaf8_continuous :
    ContinuousOn (fun s : ℝ => ∑' n : ℕ, if Odd n then bjsF306 n s else 0) (Set.Ici 1) ∧
    ContinuousOn (fun s : ℝ => ∑' n : ℕ, if Even n then bjsF306 n s else 0) (Set.Ici 2) := by
  constructor
  · refine continuousOn_tsum (u := fun n : ℕ => 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * exp (-2))
      (fun n => ?_) summable_maj_x8
      (fun n s hs => term_le_maj_x8 Odd s hs (fun _ h => Or.inl ⟨h, hs⟩) n)
    by_cases h : Odd n
    · simp only [h, ite_true]; exact (contOn_fn_x8 n).1 h
    · simp only [h, ite_false]; exact continuousOn_const
  · refine continuousOn_tsum (u := fun n : ℕ => 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * exp (-2))
      (fun n => ?_) summable_maj_x8
      (fun n s hs => term_le_maj_x8 Even s (le_trans (by norm_num) hs)
        (fun _ h => Or.inr ⟨h, hs⟩) n)
    by_cases h : Even n
    · simp only [h, ite_true]; exact (contOn_fn_x8 n).2 h
    · simp only [h, ite_false]; exact continuousOn_const

/-! ### Termwise differentiation of the even series, display 16 -/

/-- `h(s) ≤ e ^ (-2)` for every real `s`. -/
private theorem hSieve_le_all_x8d (x : ℝ) : LeanLab.ChenExplicit.hSieve x ≤ exp (-2) := by
  unfold LeanLab.ChenExplicit.hSieve
  split_ifs with h1 h2
  · exact le_rfl
  · exact exp_le_exp.mpr (by linarith)
  · have hx : 3 < x := by linarith
    have h3 : 3 * x⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by linarith)]; linarith
    have he : exp (-x) ≤ exp (-2) := exp_le_exp.mpr (by linarith)
    have hp := exp_pos (-x)
    nlinarith

/-- Display 18 with Lemma 8, two sided: `|f_k(x)| ≤ 2 e ^ 2 0.9607 ^ (k - 1) h(x)`. -/
private theorem abs_fn_le_x8d (k : ℕ) (hk : 1 ≤ k) (x : ℝ)
    (hx : (Odd k ∧ 1 ≤ x) ∨ (Even k ∧ 2 ≤ x)) :
    |bjsF306 k x| ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (k - 1) * LeanLab.ChenExplicit.hSieve x := by
  rw [abs_of_nonneg (leaf306_fn_nonneg k x hx)]
  exact key_l8306 k hk x hx

/-- The integrand of display 16, `t ↦ f_k(t - 1)`, is integrable on `t > a` when `f_k` is
continuous beyond `a - 1` and the parity range of display 18 holds there. -/
private theorem phi_integrable_x8d (k : ℕ) (a : ℝ) (ha : 1 ≤ a)
    (hpar : ∀ x, a - 1 < x → (Odd k ∧ 1 ≤ x) ∨ (Even k ∧ 2 ≤ x))
    (hc : ContinuousOn (bjsF306 k) (Set.Ioi (a - 1))) :
    MeasureTheory.IntegrableOn (fun u => bjsF306 k (u - 1)) (Set.Ioi a) := by
  rcases Nat.eq_zero_or_pos k with h0 | hk
  · subst h0
    simp [bjsF306]
  have hc' : ContinuousOn (fun u => bjsF306 k (u - 1)) (Set.Ioi a) := by
    refine hc.comp (continuousOn_id.sub continuousOn_const) ?_
    intro u hu
    show a - 1 < u - 1
    have : a < u := hu
    linarith
  have hI := (leaf306_hshift_integrable a ha).const_mul (2 * exp 2 * (0.9607 : ℝ) ^ (k - 1))
  refine hI.mono' (hc'.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
  have hu' : a < u := hu
  rw [Real.norm_eq_abs]
  exact abs_fn_le_x8d k hk (u - 1) (hpar _ (by linarith))

/-- The tail integral `z ↦ ∫ over t > z of φ` is continuous on `[a, ∞)` when `φ` is integrable
on `t > a`. -/
private theorem contG_x8d (φ : ℝ → ℝ) (a : ℝ) (hi : MeasureTheory.IntegrableOn φ (Set.Ioi a)) :
    ContinuousOn (fun z => ∫ u in Set.Ioi z, φ u) (Set.Ici a) := by
  set ψ := (Set.Ioi a).indicator φ with hψ
  have hψi : MeasureTheory.Integrable ψ :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Ioi).2 hi
  have hcont : Continuous fun z => (∫ u in Set.Ioi a, φ u) - ∫ u in a..z, ψ u :=
    continuous_const.sub (intervalIntegral.continuous_primitive
      (fun _ _ => hψi.intervalIntegrable) a)
  refine hcont.continuousOn.congr ?_
  intro z hz
  have hz' : a ≤ z := hz
  show ∫ u in Set.Ioi z, φ u = (∫ u in Set.Ioi a, φ u) - ∫ u in a..z, ψ u
  have h1 : ∫ u in a..z, ψ u = ∫ u in a..z, φ u := by
    rw [intervalIntegral.integral_of_le hz', intervalIntegral.integral_of_le hz']
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    exact Set.indicator_of_mem (show u ∈ Set.Ioi a from hu.1) φ
  rw [h1, ← intervalIntegral.integral_Ioi_sub_Ioi hi hz']
  ring

/-- Fundamental theorem of calculus for the tail integral of display 16. -/
private theorem derivG_x8d (φ : ℝ → ℝ) (a s : ℝ) (has : a < s)
    (hi : MeasureTheory.IntegrableOn φ (Set.Ioi a)) (hc : ContinuousAt φ s) :
    HasDerivAt (fun z => ∫ u in Set.Ioi z, φ u) (-φ s) s := by
  have hII : IntervalIntegrable φ MeasureTheory.volume a s :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le has.le).2
      (hi.mono_set Set.Ioc_subset_Ioi_self)
  have hmeas : StronglyMeasurableAtFilter φ (nhds s) :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem hi.aestronglyMeasurable
      (Ioi_mem_nhds has)
  have hd := (intervalIntegral.integral_hasDerivAt_right hII hmeas hc).const_sub
    (∫ u in Set.Ioi a, φ u)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds has] with z hz
  have hz' : a ≤ z := le_of_lt hz
  rw [← intervalIntegral.integral_Ioi_sub_Ioi hi hz']
  ring

/-- Display 15: on `s > 1`, `f_1(s) = max (3 - s) 0 / s`. -/
private theorem f1_eq_x8d (s : ℝ) (hs : 1 < s) : bjsF306 1 s = max (3 - s) 0 / s := by
  simp only [bjsF306]
  split_ifs with h
  · rw [max_eq_left (by linarith)]
  · rw [max_eq_right (by linarith), zero_div]

/-- Continuity of the functions `f_n` of displays 15 to 17 where the paper uses them: odd `n`
on `s > 1` and even `n` on `s > 2`. -/
private theorem fn_continuous_x8d (k : ℕ) :
    (Odd k → ContinuousOn (bjsF306 k) (Set.Ioi 1)) ∧
    (Even k → ContinuousOn (bjsF306 k) (Set.Ioi 2)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ =>
      refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
      simp only [bjsF306]; exact continuousOn_const
    | 1, _ =>
      refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      have hc : ContinuousOn (fun s : ℝ => max (3 - s) 0 / s) (Set.Ioi 1) := by
        refine ContinuousOn.div (by fun_prop) continuousOn_id ?_
        intro x hx; have : (1 : ℝ) < x := hx; exact ne_of_gt (by linarith)
      exact hc.congr (fun s hs => f1_eq_x8d s hs)
    | m + 2, ih =>
      refine ⟨fun ho => ?_, fun he => ?_⟩
      · have hev : Even (m + 1) := by
          rcases Nat.even_or_odd (m + 1) with h | h
          · exact h
          · exact absurd ho (by rw [Nat.not_odd_iff_even]; exact h.add_one)
        have hc1 := (ih (m + 1) (by omega)).2 hev
        have hi := phi_integrable_x8d (m + 1) 3 (by norm_num)
          (fun x hx => Or.inr ⟨hev, by linarith⟩) (by norm_num; exact hc1)
        have hG := contG_x8d (fun u => bjsF306 (m + 1) (u - 1)) 3 hi
        have hcomp : ContinuousOn
            (fun s : ℝ => (∫ u in Set.Ioi (max s 3), bjsF306 (m + 1) (u - 1)) / s)
            (Set.Ioi 1) := by
          refine ContinuousOn.div ?_ continuousOn_id ?_
          · refine hG.comp (continuous_id.max continuous_const).continuousOn ?_
            intro x _; exact le_max_right x 3
          · intro x hx; have : (1 : ℝ) < x := hx; exact ne_of_gt (by linarith)
        refine hcomp.congr (fun s hs => ?_)
        simp only [bjsF306]
        split_ifs with h
        · rw [max_eq_right h.2]
        · have : 3 < s := by
            by_contra hc
            exact h ⟨ho, by linarith⟩
          rw [max_eq_left this.le]
      · have hod : Odd (m + 1) := by
          rcases Nat.even_or_odd (m + 1) with h | h
          · exact absurd he (by rw [Nat.not_even_iff_odd]; exact h.add_one)
          · exact h
        have hc1 := (ih (m + 1) (by omega)).1 hod
        have hi := phi_integrable_x8d (m + 1) 2 (by norm_num)
          (fun x hx => Or.inl ⟨hod, by linarith⟩) (by norm_num; exact hc1)
        have hG := contG_x8d (fun u => bjsF306 (m + 1) (u - 1)) 2 hi
        have hcomp : ContinuousOn
            (fun s : ℝ => (∫ u in Set.Ioi s, bjsF306 (m + 1) (u - 1)) / s) (Set.Ioi 2) := by
          refine ContinuousOn.div (hG.mono Set.Ioi_subset_Ici_self) continuousOn_id ?_
          intro x hx; have : (2 : ℝ) < x := hx; exact ne_of_gt (by linarith)
        refine hcomp.congr (fun s hs => ?_)
        have hno : ¬ (Odd (m + 2) ∧ s ≤ 3) := fun h =>
          absurd h.1 (by rw [Nat.not_odd_iff_even]; exact he)
        simp only [bjsF306, if_neg hno]

/-- Display 16 differentiated: for even `n = m + 2` and `y > 2`,
`(s f_n(s))' = - f_(n-1)(y - 1)` at `s = y`. -/
private theorem deriv_term_even_x8d (m : ℕ) (he : Even (m + 2)) (y : ℝ) (hy : 2 < y) :
    HasDerivAt (fun z => z * bjsF306 (m + 2) z) (-bjsF306 (m + 1) (y - 1)) y := by
  have hod : Odd (m + 1) := by
    rcases Nat.even_or_odd (m + 1) with h | h
    · exact absurd he (by rw [Nat.not_even_iff_odd]; exact h.add_one)
    · exact h
  have hc1 := (fn_continuous_x8d (m + 1)).1 hod
  have hi := phi_integrable_x8d (m + 1) 2 (by norm_num)
    (fun x hx => Or.inl ⟨hod, by linarith⟩) (by norm_num; exact hc1)
  have hca : ContinuousAt (fun u => bjsF306 (m + 1) (u - 1)) y := by
    have : ContinuousAt (bjsF306 (m + 1)) (y - 1) :=
      hc1.continuousAt (Ioi_mem_nhds (by linarith))
    exact ContinuousAt.comp_of_eq this (by fun_prop) rfl
  have hd := derivG_x8d (fun u => bjsF306 (m + 1) (u - 1)) 2 y hy hi hca
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hy] with z hz
  have hz' : (2 : ℝ) < z := hz
  have hno : ¬ (Odd (m + 2) ∧ z ≤ 3) := fun h =>
    absurd h.1 (by rw [Nat.not_odd_iff_even]; exact he)
  simp only [bjsF306, if_neg hno]
  field_simp

/-- The summable bound on the termwise derivatives, uniform for `y > 2`, from display 18. -/
private theorem deriv_bound_x8d (n : ℕ) (y : ℝ) (hy : 2 < y) :
    ‖(if Even n then -bjsF306 (n - 1) (y - 1) else 0)‖ ≤
      2 * (0.9607 : ℝ) ^ (n - 2) := by
  have hu : 0 ≤ 2 * (0.9607 : ℝ) ^ (n - 2) := by positivity
  split_ifs with he
  · match n, he with
    | 0, _ => simpa [bjsF306] using hu
    | 1, he => exact absurd he (by decide)
    | m + 2, he =>
      have hod : Odd (m + 1) := by
        rcases Nat.even_or_odd (m + 1) with h | h
        · exact absurd he (by rw [Nat.not_even_iff_odd]; exact h.add_one)
        · exact h
      rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega, norm_neg,
        Real.norm_eq_abs]
      have h1 := abs_fn_le_x8d (m + 1) (by omega) (y - 1) (Or.inl ⟨hod, by linarith⟩)
      rw [show m + 1 - 1 = m by omega] at h1
      have h2 := hSieve_le_all_x8d (y - 1)
      have h3 : exp 2 * exp (-2) = 1 := by rw [← exp_add]; norm_num
      have h4 : 0 ≤ 2 * exp 2 * (0.9607 : ℝ) ^ m := by positivity
      calc |bjsF306 (m + 1) (y - 1)|
          ≤ 2 * exp 2 * (0.9607 : ℝ) ^ m * LeanLab.ChenExplicit.hSieve (y - 1) := h1
        _ ≤ 2 * exp 2 * (0.9607 : ℝ) ^ m * exp (-2) := mul_le_mul_of_nonneg_left h2 h4
        _ = 2 * (0.9607 : ℝ) ^ m * (exp 2 * exp (-2)) := by ring
        _ = 2 * (0.9607 : ℝ) ^ m := by rw [h3, mul_one]
  · simpa using hu

/-- The bound sequence `2 · 0.9607 ^ (n - 2)` is summable. -/
private theorem bound_summable_x8d : Summable (fun n : ℕ => 2 * (0.9607 : ℝ) ^ (n - 2)) := by
  rw [← summable_nat_add_iff 2]
  have : (fun m : ℕ => 2 * (0.9607 : ℝ) ^ (m + 2 - 2)) = fun m => 2 * (0.9607 : ℝ) ^ m := by
    funext m; rw [show m + 2 - 2 = m by omega]
  rw [this]
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

/-- The series of `s f_n(s)` over even `n` converges for `s ≥ 2`, display 18 with Lemma 8. -/
private theorem even_summable_x8d (s : ℝ) (hs : 2 ≤ s) :
    Summable (fun n : ℕ => if Even n then s * bjsF306 n s else 0) := by
  rw [← summable_nat_add_iff 1]
  have hspos : 0 ≤ s := by linarith
  have hh := hSieve_nonneg306 s hspos
  set C := s * (2 * exp 2 * LeanLab.ChenExplicit.hSieve s) with hC
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 0.9607) (by norm_num)).mul_left C)
  · split_ifs with h
    · exact mul_nonneg hspos (leaf306_fn_nonneg _ s (Or.inr ⟨h, hs⟩))
    · exact le_rfl
  · split_ifs with h
    · have := key_l8306 (k + 1) (by omega) s (Or.inr ⟨h, hs⟩)
      rw [show k + 1 - 1 = k by omega] at this
      rw [hC]
      have : s * bjsF306 (k + 1) s ≤ s * (2 * exp 2 * (0.9607 : ℝ) ^ k *
          LeanLab.ChenExplicit.hSieve s) := mul_le_mul_of_nonneg_left this hspos
      linarith
    · positivity

/-- LEAF: display 16 for even n ≥ 2 differentiated and summed, BJS page 6, Nathanson
Theorem 9.4: (s f_n(s))' = - f_(n-1)(s - 1) for s > 2, summed over even n, which needs
termwise differentiation justified by the bound 18. Class MEDIUM. -/
theorem leaf8_deriv_even (s : ℝ) (hs : 2 < s) :
    HasDerivAt (fun t : ℝ => t * ∑' n : ℕ, if Even n then bjsF306 n t else 0)
      (-(∑' n : ℕ, if Odd n then bjsF306 n (s - 1) else 0)) s := by
  set g : ℕ → ℝ → ℝ := fun n z => if Even n then z * bjsF306 n z else 0 with hg
  set g' : ℕ → ℝ → ℝ := fun n y => if Even n then -bjsF306 (n - 1) (y - 1) else 0 with hg'
  have hfun : (fun t : ℝ => t * ∑' n : ℕ, if Even n then bjsF306 n t else 0) =
      fun z => ∑' n, g n z := by
    funext t
    rw [← tsum_mul_left]
    congr 1; funext n
    simp only [hg]
    split_ifs <;> simp
  have hderiv : ∀ n y, y ∈ Set.Ioi (2 : ℝ) → HasDerivAt (g n) (g' n y) y := by
    intro n y hy
    have hy' : (2 : ℝ) < y := hy
    by_cases he : Even n
    · match n, he with
      | 0, _ =>
        have h00 : ∀ x, bjsF306 0 x = 0 := fun _ => rfl
        simpa [hg, hg', h00] using (hasDerivAt_const y (0 : ℝ))
      | 1, he => exact absurd he (by decide)
      | m + 2, he =>
        simp only [hg, hg', if_pos he, show m + 2 - 1 = m + 1 by omega]
        exact deriv_term_even_x8d m he y hy'
    · simp only [hg, hg', if_neg he]
      exact hasDerivAt_const y (0 : ℝ)
  have hmain := hasDerivAt_tsum_of_isPreconnected bound_summable_x8d isOpen_Ioi
    isPreconnected_Ioi hderiv (fun n y hy => deriv_bound_x8d n y hy)
    (show s ∈ Set.Ioi (2 : ℝ) from hs) (even_summable_x8d s hs.le)
    (show s ∈ Set.Ioi (2 : ℝ) from hs)
  rw [hfun]
  convert hmain using 1
  have hsum : Summable (fun n => g' n s) :=
    Summable.of_norm_bounded bound_summable_x8d (fun n => deriv_bound_x8d n s hs)
  rw [hsum.tsum_eq_zero_add]
  have h0 : g' 0 s = 0 := by simp [hg', bjsF306]
  rw [h0, zero_add, ← tsum_neg]
  congr 1; funext k
  simp only [hg', Nat.even_add_one, Nat.not_even_iff_odd, Nat.add_sub_cancel]
  split_ifs <;> simp

/-- LEAF: displays 15 and 16 for odd n differentiated and summed, BJS page 6, Nathanson
Theorem 9.4: s f_1(s) = 0 for s > 3 and (s f_n(s))' = - f_(n-1)(s - 1) for odd n ≥ 3
and s ≥ 3, one sided at s = 3 where display 17 takes over. Class MEDIUM. -/
theorem leaf8_deriv_odd :
    (∀ s : ℝ, 3 < s →
      HasDerivAt (fun t : ℝ => t * ∑' n : ℕ, if Odd n then bjsF306 n t else 0)
        (-(∑' n : ℕ, if Even n then bjsF306 n (s - 1) else 0)) s) ∧
    HasDerivWithinAt (fun t : ℝ => t * ∑' n : ℕ, if Odd n then bjsF306 n t else 0)
        (-(∑' n : ℕ, if Even n then bjsF306 n 2 else 0)) (Set.Ici 3) 3 := by
  -- each odd term on `[3, ∞)` is the restriction of a globally differentiable function
  let phiExt : ℕ → ℝ → ℝ := fun m u => bjsF306 (m + 1) (max u 3 - 1)
  let KExt : ℕ → ℝ → ℝ := fun m t =>
    (∫ u in Set.Ioi (3 : ℝ), bjsF306 (m + 1) (u - 1)) - ∫ u in (3 : ℝ)..t, phiExt m u
  let gOdd : ℕ → ℝ → ℝ := fun n t => if Odd n ∧ 2 ≤ n then KExt (n - 2) t else 0
  let gOdd' : ℕ → ℝ → ℝ := fun n y => if Odd n ∧ 2 ≤ n then -phiExt (n - 2) y else 0
  have fnEvenIci : ∀ k : ℕ, Even k → ContinuousOn (bjsF306 k) (Set.Ici 2) := by
    intro k he
    match k, he with
    | 0, _ => simp only [bjsF306]; exact continuousOn_const
    | 1, he => exact absurd he (by decide)
    | j + 2, he =>
      have hod : Odd (j + 1) := by
        rcases Nat.even_or_odd (j + 1) with h | h
        · exact absurd he (by rw [Nat.not_even_iff_odd]; exact h.add_one)
        · exact h
      have hc1 := (fn_continuous_x8d (j + 1)).1 hod
      have hi := phi_integrable_x8d (j + 1) 2 (by norm_num)
        (fun x hx => Or.inl ⟨hod, by linarith⟩) (by norm_num; exact hc1)
      have hG := contG_x8d (fun u => bjsF306 (j + 1) (u - 1)) 2 hi
      have hcomp : ContinuousOn
          (fun s : ℝ => (∫ u in Set.Ioi s, bjsF306 (j + 1) (u - 1)) / s) (Set.Ici 2) := by
        refine ContinuousOn.div hG continuousOn_id ?_
        intro x hx; have : (2 : ℝ) ≤ x := hx; exact ne_of_gt (by linarith)
      refine hcomp.congr (fun s hs => ?_)
      have hno : ¬ (Odd (j + 2) ∧ s ≤ 3) := fun h =>
        absurd h.1 (by rw [Nat.not_odd_iff_even]; exact he)
      simp only [bjsF306, if_neg hno]
  have phiExt_cont : ∀ m : ℕ, Even (m + 1) → Continuous (phiExt m) := by
    intro m he
    have hc := fnEvenIci (m + 1) he
    dsimp only [phiExt]
    refine hc.comp_continuous (by fun_prop) (fun u => ?_)
    show (2 : ℝ) ≤ max u 3 - 1
    have := le_max_right u 3; linarith
  have KExt_eq : ∀ m : ℕ, Even (m + 1) → ∀ t : ℝ, 3 ≤ t →
      KExt m t = ∫ u in Set.Ioi t, bjsF306 (m + 1) (u - 1) := by
    intro m he t ht
    have hc1 := fnEvenIci (m + 1) he
    have hi := phi_integrable_x8d (m + 1) 3 (by norm_num)
      (fun x hx => Or.inr ⟨he, by linarith⟩)
      (hc1.mono (fun x hx => by have : (3 : ℝ) - 1 < x := hx; show (2 : ℝ) ≤ x; linarith))
    dsimp only [KExt]
    have h1 : ∫ u in (3 : ℝ)..t, phiExt m u =
        ∫ u in (3 : ℝ)..t, bjsF306 (m + 1) (u - 1) := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le ht] at hu
      have hu1 : (3 : ℝ) ≤ u := hu.1
      simp only [phiExt, max_eq_left hu1]
    rw [h1, ← intervalIntegral.integral_Ioi_sub_Ioi hi ht]
    ring
  have KExt_deriv : ∀ m : ℕ, Even (m + 1) → ∀ y : ℝ,
      HasDerivAt (KExt m) (-phiExt m y) y := by
    intro m he y
    have h := ((phiExt_cont m he).integral_hasStrictDerivAt 3 y).hasDerivAt.const_sub
      (∫ u in Set.Ioi (3 : ℝ), bjsF306 (m + 1) (u - 1))
    exact h
  have evenOfOdd : ∀ m : ℕ, Odd (m + 2) → Even (m + 1) := by
    intro m ho
    rcases Nat.even_or_odd (m + 1) with h | h
    · exact h
    · exact absurd ho (by rw [Nat.not_odd_iff_even]; exact h.add_one)
  have gOdd_eq : ∀ (n : ℕ) (t : ℝ), 3 ≤ t →
      gOdd n t = if Odd n then t * bjsF306 n t else 0 := by
    intro n t ht
    have htp : t ≠ 0 := by intro h; linarith
    match n with
    | 0 => simp [gOdd]
    | 1 =>
      simp only [gOdd, show ¬ (Odd 1 ∧ 2 ≤ 1) from by omega, if_false, if_pos odd_one,
        bjsF306]
      split_ifs with h
      · have : t = 3 := le_antisymm h ht
        subst this; norm_num
      · simp
    | m + 2 =>
      by_cases ho : Odd (m + 2)
      · have he := evenOfOdd m ho
        simp only [gOdd, if_pos (And.intro ho (by omega : 2 ≤ m + 2)), if_pos ho,
          show m + 2 - 2 = m by omega, KExt_eq m he t ht, bjsF306]
        split_ifs with h
        · have : t = 3 := le_antisymm h.2 ht
          subst this; field_simp
        · field_simp
      · simp [gOdd, ho]
  have gOdd_deriv : ∀ (n : ℕ) (y : ℝ), HasDerivAt (gOdd n) (gOdd' n y) y := by
    intro n y
    by_cases h : Odd n ∧ 2 ≤ n
    · have hfun : gOdd n = KExt (n - 2) := by
        funext t; simp only [gOdd, if_pos h]
      rw [hfun]; simp only [gOdd', if_pos h]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rw [show m + 2 - 2 = m by omega]
      exact KExt_deriv m (evenOfOdd m h.1) y
    · have hfun : gOdd n = fun _ => 0 := by
        funext t; simp only [gOdd, if_neg h]
      rw [hfun]; simp only [gOdd', if_neg h]
      exact hasDerivAt_const y (0 : ℝ)
  have gOdd_bound : ∀ (n : ℕ) (y : ℝ), ‖gOdd' n y‖ ≤ 2 * (0.9607 : ℝ) ^ (n - 2) := by
    intro n y
    have hu : 0 ≤ 2 * (0.9607 : ℝ) ^ (n - 2) := by positivity
    simp only [gOdd']
    split_ifs with h
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      have he := evenOfOdd m h.1
      rw [show m + 2 - 2 = m by omega, norm_neg, Real.norm_eq_abs]
      dsimp only [phiExt]
      have hx : (2 : ℝ) ≤ max y 3 - 1 := by have := le_max_right y 3; linarith
      have h1 := abs_fn_le_x8d (m + 1) (by omega) (max y 3 - 1) (Or.inr ⟨he, hx⟩)
      rw [show m + 1 - 1 = m by omega] at h1
      have h2 := hSieve_le_all_x8d (max y 3 - 1)
      have h3 : exp 2 * exp (-2) = 1 := by rw [← exp_add]; norm_num
      have h4 : 0 ≤ 2 * exp 2 * (0.9607 : ℝ) ^ m := by positivity
      calc |bjsF306 (m + 1) (max y 3 - 1)|
          ≤ 2 * exp 2 * (0.9607 : ℝ) ^ m * LeanLab.ChenExplicit.hSieve (max y 3 - 1) := h1
        _ ≤ 2 * exp 2 * (0.9607 : ℝ) ^ m * exp (-2) := mul_le_mul_of_nonneg_left h2 h4
        _ = 2 * (0.9607 : ℝ) ^ m * (exp 2 * exp (-2)) := by ring
        _ = 2 * (0.9607 : ℝ) ^ m := by rw [h3, mul_one]
    · simpa using hu
  have odd_summable : ∀ s : ℝ, 1 ≤ s →
      Summable (fun n : ℕ => if Odd n then s * bjsF306 n s else 0) := by
    intro s hs
    rw [← summable_nat_add_iff 1]
    have hspos : 0 ≤ s := by linarith
    have hh := hSieve_nonneg306 s hspos
    set C := s * (2 * exp 2 * LeanLab.ChenExplicit.hSieve s) with hC
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 0.9607) (by norm_num)).mul_left C)
    · split_ifs with h
      · exact mul_nonneg hspos (leaf306_fn_nonneg _ s (Or.inl ⟨h, hs⟩))
      · exact le_rfl
    · split_ifs with h
      · have := key_l8306 (k + 1) (by omega) s (Or.inl ⟨h, hs⟩)
        rw [show k + 1 - 1 = k by omega] at this
        rw [hC]
        have : s * bjsF306 (k + 1) s ≤ s * (2 * exp 2 * (0.9607 : ℝ) ^ k *
            LeanLab.ChenExplicit.hSieve s) := mul_le_mul_of_nonneg_left this hspos
        linarith
      · positivity
  have gsum_deriv : ∀ y : ℝ,
      HasDerivAt (fun z => ∑' n, gOdd n z) (∑' n, gOdd' n y) y := by
    intro y
    have hs3 : Summable (fun n => gOdd n 3) := by
      have h := odd_summable 3 (by norm_num)
      refine h.congr (fun n => ?_)
      exact (gOdd_eq n 3 le_rfl).symm
    exact hasDerivAt_tsum_of_isPreconnected bound_summable_x8d isOpen_univ isPreconnected_univ
      (fun n y _ => gOdd_deriv n y) (fun n y _ => gOdd_bound n y) (Set.mem_univ 3) hs3
      (Set.mem_univ y)
  have gsum'_eq : ∀ y : ℝ, 3 ≤ y →
      ∑' n, gOdd' n y = -(∑' n : ℕ, if Even n then bjsF306 n (y - 1) else 0) := by
    intro y hy
    have hsum : Summable (fun n => gOdd' n y) :=
      Summable.of_norm_bounded bound_summable_x8d (fun n => gOdd_bound n y)
    rw [hsum.tsum_eq_zero_add]
    have h0 : gOdd' 0 y = 0 := by simp [gOdd']
    rw [h0, zero_add, ← tsum_neg]
    congr 1; funext k
    rcases k with _ | k
    · simp [gOdd', bjsF306]
    · have hmax : max y 3 = y := max_eq_left hy
      simp only [gOdd', phiExt, hmax, show k + 1 + 1 - 2 = k by omega,
        show 2 ≤ k + 1 + 1 by omega, and_true, Nat.odd_add_one, Nat.not_odd_iff_even]
      split_ifs <;> simp_all [Nat.even_add_one]
  have hF : ∀ t : ℝ, 3 ≤ t →
      (t * ∑' n : ℕ, if Odd n then bjsF306 n t else 0) = ∑' n, gOdd n t := by
    intro t ht
    rw [← tsum_mul_left]
    congr 1; funext n
    rw [gOdd_eq n t ht]
    split_ifs <;> simp
  refine ⟨fun s hs => ?_, ?_⟩
  · have h := gsum_deriv s
    rw [gsum'_eq s hs.le] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hs] with z hz
    exact hF z (le_of_lt hz)
  · have h := (gsum_deriv 3).hasDerivWithinAt (s := Set.Ici 3)
    rw [gsum'_eq 3 le_rfl, show (3 : ℝ) - 1 = 2 by norm_num] at h
    exact h.congr (fun t ht => hF t ht) (hF 3 le_rfl)

/-- LEAF: the analytic core of Nathanson Theorem 9.4 as used by BJS page 6, display 13 at
s = 3: 1 + the sum of f_n(3) over odd n equals F(3) = 2 e ^ γ / 3. With display 17 this
gives F(s) = 2 e ^ γ / s on [1, 3], proved below. Class HARD: this is where e ^ γ enters,
through the asymptotics F(s), f(s) → 1 and the adjoint function argument. -/
theorem leaf8_F3 :
    HasSum (fun n : ℕ => if Odd n then bjsF306 n 3 else 0)
      (2 * exp eulerMascheroniConstant / 3 - 1) := by
  sorry

/-! ### The boundary value f(2) = 0: E(2) = 1 -/

/-- Display 18 with Lemma 8 summed over a parity class: `0 ≤ O(s)` and
`O(s) ≤ (2 e ^ 2 / 0.9607) (1 - 0.9607)⁻¹ h(s)`. -/
private theorem parity_le_x8f (P : ℕ → Prop) [DecidablePred P] (s : ℝ)
    (hP : ∀ n, P n → (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s)) (hs : 0 ≤ s) :
    0 ≤ (∑' n : ℕ, (if P n then bjsF306 n s else 0)) ∧
      (∑' n : ℕ, (if P n then bjsF306 n s else 0)) ≤
        (2 * exp 2 / 0.9607 * (1 - 0.9607)⁻¹) * LeanLab.ChenExplicit.hSieve s := by
  have hh := hSieve_nonneg306 s hs
  set A := 2 * exp 2 * LeanLab.ChenExplicit.hSieve s / 0.9607 with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact div_nonneg (mul_nonneg (by positivity) hh) (by norm_num)
  have hb : ∀ n : ℕ, (if P n then bjsF306 n s else 0) ≤ A * (0.9607 : ℝ) ^ n := by
    intro n
    rcases n with _ | k
    · split_ifs with h
      · have h0 : bjsF306 0 s = 0 := rfl
        rw [h0]
        exact mul_nonneg hA0 (by positivity)
      · exact mul_nonneg hA0 (by positivity)
    · split_ifs with h
      · have hk := key_l8306 (k + 1) (by omega) s (hP _ h)
        rw [show k + 1 - 1 = k by omega] at hk
        have he : A * (0.9607 : ℝ) ^ (k + 1) =
            2 * exp 2 * (0.9607 : ℝ) ^ k * LeanLab.ChenExplicit.hSieve s := by
          rw [hA, pow_succ]; field_simp
        rw [he]
        exact hk
      · exact mul_nonneg hA0 (by positivity)
  have hnonneg : ∀ n : ℕ, 0 ≤ (if P n then bjsF306 n s else 0) := by
    intro n
    split_ifs with h
    · rcases n with _ | k
      · exact le_rfl
      · exact leaf306_fn_nonneg _ s (hP _ h)
    · exact le_rfl
  have hgeom : Summable (fun n : ℕ => A * (0.9607 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left A
  have hPsum : Summable (fun n : ℕ => if P n then bjsF306 n s else 0) :=
    Summable.of_nonneg_of_le hnonneg hb hgeom
  refine ⟨tsum_nonneg hnonneg, ?_⟩
  have h1 := Summable.tsum_le_tsum hb hPsum hgeom
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h1
  refine h1.trans (le_of_eq ?_)
  rw [hA]; field_simp

/-- `0 ≤ Q(s)` and `Q(s) ≤ 2 M h(s)` for `s ≥ 2`, where `Q = O + E`. -/
private theorem qBound_x8f (O E : ℝ → ℝ)
    (hO : ∀ s, O s = ∑' n : ℕ, if Odd n then bjsF306 n s else 0)
    (hE : ∀ s, E s = ∑' n : ℕ, if Even n then bjsF306 n s else 0)
    (s : ℝ) (hs : 2 ≤ s) :
    0 ≤ O s + E s ∧ O s + E s ≤
      2 * (2 * exp 2 / 0.9607 * (1 - 0.9607)⁻¹) * LeanLab.ChenExplicit.hSieve s := by
  have hO1 := parity_le_x8f Odd s (fun n h => Or.inl ⟨h, by linarith⟩) (by linarith)
  have hE1 := parity_le_x8f Even s (fun n h => Or.inr ⟨h, hs⟩) (by linarith)
  rw [hO s, hE s]
  constructor
  · linarith [hO1.1, hE1.1]
  · linarith [hO1.2, hE1.2]

/-- `t h(t) ≤ 3 e ^ (-t)` for `t ≥ 3`. -/
private theorem t_mul_hSieve_x8f (t : ℝ) (ht : 3 ≤ t) :
    t * LeanLab.ChenExplicit.hSieve t ≤ 3 * exp (-t) := by
  unfold LeanLab.ChenExplicit.hSieve
  split_ifs with h1 h2
  · linarith
  · have : t = 3 := le_antisymm h2 ht
    subst this; have := exp_pos (-3 : ℝ); nlinarith
  · have htp : t ≠ 0 := by intro h; linarith
    rw [show t * (3 * t⁻¹ * exp (-t)) = 3 * exp (-t) * (t * t⁻¹) by ring,
      mul_inv_cancel₀ htp, mul_one]

/-- The invariant of `(s Q(s))' = - Q(s - 1)` tends to `0` at infinity. -/
private theorem I_tendsto_x8f (O E : ℝ → ℝ)
    (hO : ∀ s, O s = ∑' n : ℕ, if Odd n then bjsF306 n s else 0)
    (hE : ∀ s, E s = ∑' n : ℕ, if Even n then bjsF306 n s else 0) :
    Filter.Tendsto (fun s : ℝ => s * (s - 1) * (O s + E s) -
      ∫ t in (s - 1)..s, t * (O t + E t)) Filter.atTop (nhds 0) := by
  set M := 2 * exp 2 / 0.9607 * (1 - 0.9607)⁻¹ with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  have hlim : Filter.Tendsto (fun s : ℝ => 6 * M * (s * exp (-s)) + 6 * M * exp 1 * exp (-s))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun s : ℝ => s * exp (-s)) Filter.atTop (nhds 0) := by
      simpa using tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero
    simpa using (h1.const_mul (6 * M)).add (h2.const_mul (6 * M * exp 1))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop (4 : ℝ)] with s hs4
  obtain ⟨hq0, hq1⟩ := qBound_x8f O E hO hE s (by linarith)
  rw [← hM] at hq1
  have hth := t_mul_hSieve_x8f s (by linarith)
  have hA : ‖s * (s - 1) * (O s + E s)‖ ≤ 6 * M * (s * exp (-s)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hq0)]
    have e1 : s * (s - 1) * (O s + E s) ≤ s * s * (O s + E s) := by
      have h1 : 0 ≤ s * (O s + E s) := by
        have := hq0; nlinarith
      nlinarith
    have e2 : s * s * (O s + E s) ≤
        s * s * (2 * M * LeanLab.ChenExplicit.hSieve s) :=
      mul_le_mul_of_nonneg_left hq1 (by positivity)
    have e4 : 2 * M * s * (s * LeanLab.ChenExplicit.hSieve s) ≤
        2 * M * s * (3 * exp (-s)) := mul_le_mul_of_nonneg_left hth (by positivity)
    nlinarith
  have hB : ‖∫ t in (s - 1)..s, t * (O t + E t)‖ ≤ 6 * M * exp 1 * exp (-s) := by
    have hbd : ∀ t ∈ Set.uIoc (s - 1) s, ‖t * (O t + E t)‖ ≤ 6 * M * exp 1 * exp (-s) := by
      intro t ht
      rw [Set.uIoc_of_le (by linarith)] at ht
      obtain ⟨ht1, ht2⟩ := ht
      obtain ⟨p0, p1⟩ := qBound_x8f O E hO hE t (by linarith)
      rw [← hM] at p1
      have hth' := t_mul_hSieve_x8f t (by linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) p0)]
      have e2 : t * (O t + E t) ≤ t * (2 * M * LeanLab.ChenExplicit.hSieve t) :=
        mul_le_mul_of_nonneg_left p1 (by linarith)
      have e4 : 2 * M * (t * LeanLab.ChenExplicit.hSieve t) ≤ 2 * M * (3 * exp (-t)) :=
        mul_le_mul_of_nonneg_left hth' (by positivity)
      have e5 : exp (-t) ≤ exp 1 * exp (-s) := by
        rw [← exp_add]; exact exp_le_exp.mpr (by linarith)
      nlinarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rw [show s - (s - 1) = (1 : ℝ) by ring, abs_one, mul_one] at this
    exact this
  calc ‖s * (s - 1) * (O s + E s) - ∫ t in (s - 1)..s, t * (O t + E t)‖
      ≤ ‖s * (s - 1) * (O s + E s)‖ + ‖∫ t in (s - 1)..s, t * (O t + E t)‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add hA hB

/-- Displays 15 and 17: for `0 < t ≤ 3`, `t O(t) = 3 - t + 3 O(3)`. -/
private theorem tO_low_x8f (O : ℝ → ℝ)
    (hO : ∀ s, O s = ∑' n : ℕ, (if Odd n then bjsF306 n s else 0))
    (t : ℝ) (ht0 : 0 < t) (ht : t ≤ 3) : t * O t = 3 - t + 3 * O 3 := by
  have htp : t ≠ 0 := ne_of_gt ht0
  rw [hO t, hO 3]
  have hterm : ∀ n : ℕ, t * (if Odd n then bjsF306 n t else 0) =
      (if n = 1 then 3 - t else 0) + 3 * (if Odd n then bjsF306 n 3 else 0) := by
    intro n
    match n with
    | 0 => simp [bjsF306]
    | 1 =>
      simp only [bjsF306, if_pos odd_one, if_pos ht, if_true, le_refl]
      field_simp; ring
    | m + 2 =>
      have hn : m + 2 ≠ 1 := by omega
      by_cases ho : Odd (m + 2)
      · simp only [bjsF306, if_pos ho, if_neg hn, if_pos (And.intro ho ht),
          if_pos (And.intro ho (le_refl (3 : ℝ)))]
        field_simp; ring
      · simp [ho]
  have hs1 : Summable (fun n : ℕ => if n = 1 then 3 - t else 0) := by
    apply summable_of_ne_finset_zero (s := {1})
    intro n hn; simp only [Finset.mem_singleton] at hn; simp [hn]
  have hs2 : Summable (fun n : ℕ => 3 * (if Odd n then bjsF306 n 3 else 0)) :=
    (leaf8_summable.1 3 (by norm_num)).mul_left 3
  rw [← tsum_mul_left]
  simp_rw [hterm]
  rw [hs1.tsum_add hs2, tsum_ite_eq, tsum_mul_left]

/-- `t ↦ t Q(t)` is continuous on `t > 2`. -/
private theorem q_cont_x8f (O E : ℝ → ℝ)
    (hO : ∀ s, O s = ∑' n : ℕ, (if Odd n then bjsF306 n s else 0))
    (hE : ∀ s, E s = ∑' n : ℕ, (if Even n then bjsF306 n s else 0)) :
    ContinuousOn (fun t => t * (O t + E t)) (Set.Ioi 2) := by
  have hEcont : ContinuousOn (fun t => t * E t) (Set.Ioi 2) := by
    have hfun : (fun t => t * E t) =
        fun t => t * ∑' n : ℕ, (if Even n then bjsF306 n t else 0) := by
      funext t; rw [hE t]
    rw [hfun]
    exact fun x hx => (leaf8_deriv_even x hx).continuousAt.continuousWithinAt
  have hOcont : ContinuousOn (fun t => t * O t) (Set.Ioi 2) := by
    intro x hx
    have hx2 : (2 : ℝ) < x := hx
    apply ContinuousAt.continuousWithinAt
    rcases lt_trichotomy x 3 with h | h | h
    · have hc : ContinuousAt (fun t : ℝ => 3 - t + 3 * O 3) x := by fun_prop
      refine hc.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < x by linarith) h] with t ht
      exact tO_low_x8f O hO t ht.1 ht.2.le
    · subst h
      have hR : ContinuousWithinAt (fun t => t * O t) (Set.Ici 3) 3 := by
        have hfun : (fun t => t * O t) =
            fun t => t * ∑' n : ℕ, (if Odd n then bjsF306 n t else 0) := by
          funext t; rw [hO t]
        rw [hfun]
        exact leaf8_deriv_odd.2.continuousWithinAt
      have hL : ContinuousWithinAt (fun t => t * O t) (Set.Iic 3) 3 := by
        have hc : ContinuousWithinAt (fun t : ℝ => 3 - t + 3 * O 3) (Set.Iic 3) 3 :=
          (by fun_prop : Continuous (fun t : ℝ => 3 - t + 3 * O 3)).continuousWithinAt
        refine hc.congr_of_eventuallyEq ?_ (tO_low_x8f O hO 3 (by norm_num) le_rfl)
        filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (Ioi_mem_nhds (show (0 : ℝ) < 3 by norm_num))] with t ht ht0
        exact tO_low_x8f O hO t ht0 ht
      have := hL.union hR
      rwa [Set.Iic_union_Ici, continuousWithinAt_univ] at this
    · have h := (leaf8_deriv_odd.1 x h).continuousAt
      have hfun : (fun t => t * O t) =
          fun t => t * ∑' n : ℕ, (if Odd n then bjsF306 n t else 0) := by
        funext t; rw [hO t]
      rw [hfun]
      exact h
  have h := hOcont.add hEcont
  refine h.congr (fun t _ => ?_)
  simp only [Pi.add_apply]; ring

/-- `t ↦ t Q(t)` is interval integrable on `[2, b]`. -/
private theorem gint_x8f (O E : ℝ → ℝ)
    (hO : ∀ s, O s = ∑' n : ℕ, (if Odd n then bjsF306 n s else 0))
    (hE : ∀ s, E s = ∑' n : ℕ, (if Even n then bjsF306 n s else 0))
    (b : ℝ) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t => t * (O t + E t)) MeasureTheory.volume 2 b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
  have hcont : ContinuousOn (fun t => t * (O t + E t)) (Set.Ioc 2 b) :=
    (q_cont_x8f O E hO hE).mono Set.Ioc_subset_Ioi_self
  refine ⟨hcont.aestronglyMeasurable measurableSet_Ioc,
    MeasureTheory.HasFiniteIntegral.restrict_of_bounded
      (C := b * (2 * (2 * exp 2 / 0.9607 * (1 - 0.9607)⁻¹) * exp (-2))) measure_Ioc_lt_top ?_⟩
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨p0, p1⟩ := qBound_x8f O E hO hE t ht1.le
  have hh := hSieve_le_all_x8d t
  have hC0 : 0 ≤ 2 * (2 * exp 2 / 0.9607 * (1 - 0.9607)⁻¹) := by positivity
  have p2 : O t + E t ≤ 2 * (2 * exp 2 / 0.9607 * (1 - 0.9607)⁻¹) * exp (-2) := by
    have h3 := mul_le_mul_of_nonneg_left hh hC0
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) p0)]
  have e1 : t * (O t + E t) ≤ t * (2 * (2 * exp 2 / 0.9607 * (1 - 0.9607)⁻¹) * exp (-2)) :=
    mul_le_mul_of_nonneg_left p2 (by linarith)
  have e2 : t * (2 * (2 * exp 2 / 0.9607 * (1 - 0.9607)⁻¹) * exp (-2)) ≤
      b * (2 * (2 * exp 2 / 0.9607 * (1 - 0.9607)⁻¹) * exp (-2)) :=
    mul_le_mul_of_nonneg_right ht2 (by positivity)
  linarith

/-- The invariant of `(s Q(s))' = - Q(s - 1)` is constant on `[3, ∞)`. -/
private theorem I_const_x8f (O E : ℝ → ℝ)
    (hO : ∀ s, O s = ∑' n : ℕ, (if Odd n then bjsF306 n s else 0))
    (hE : ∀ s, E s = ∑' n : ℕ, (if Even n then bjsF306 n s else 0))
    (s : ℝ) (hs : 3 ≤ s) :
    s * (s - 1) * (O s + E s) - ∫ t in (s - 1)..s, t * (O t + E t) =
      3 * (3 - 1) * (O 3 + E 3) - ∫ t in ((3 : ℝ) - 1)..3, t * (O t + E t) := by
  set g : ℝ → ℝ := fun t => t * (O t + E t) with hg
  have gcont : ContinuousOn g (Set.Ioi 2) := q_cont_x8f O E hO hE
  have gint : ∀ b, 2 ≤ b → IntervalIntegrable g MeasureTheory.volume 2 b := gint_x8f O E hO hE
  set G : ℝ → ℝ := fun x => ∫ t in (2 : ℝ)..x, g t with hG
  have Gcont : ∀ b, 2 ≤ b → ContinuousOn G (Set.Icc 2 b) := by
    intro b hb
    have h := intervalIntegral.continuousOn_primitive_interval' (gint b hb) (Set.left_mem_uIcc)
    rwa [Set.uIcc_of_le hb] at h
  have Gderiv : ∀ x, 2 < x → HasDerivAt G (g x) x := by
    intro x hx
    have hmeas := gcont.stronglyMeasurableAtFilter (μ := MeasureTheory.volume) isOpen_Ioi x hx
    exact intervalIntegral.integral_hasDerivAt_right (gint x hx.le) hmeas
      (gcont.continuousAt (Ioi_mem_nhds hx))
  have gderiv : ∀ x : ℝ, 3 < x → HasDerivAt g (-(O (x - 1) + E (x - 1))) x := by
    intro x hx
    have hOfun : (fun t => t * O t) =
        fun t => t * ∑' n : ℕ, (if Odd n then bjsF306 n t else 0) := by
      funext t; rw [hO t]
    have hEfun : (fun t => t * E t) =
        fun t => t * ∑' n : ℕ, (if Even n then bjsF306 n t else 0) := by
      funext t; rw [hE t]
    have h1 : HasDerivAt (fun t => t * O t) (-E (x - 1)) x := by
      have h := leaf8_deriv_odd.1 x hx
      rw [← hOfun, ← hE (x - 1)] at h
      exact h
    have h2 : HasDerivAt (fun t => t * E t) (-O (x - 1)) x := by
      have h := leaf8_deriv_even x (by linarith)
      rw [← hEfun, ← hO (x - 1)] at h
      exact h
    have h3 := h1.add h2
    convert h3 using 1
    · funext t; simp only [hg, Pi.add_apply]; ring
    · ring
  set Phi : ℝ → ℝ := fun x => (x - 1) * g x - (G x - G (x - 1)) with hPhi
  have hPhi_eq : ∀ x : ℝ, 3 ≤ x →
      x * (x - 1) * (O x + E x) - ∫ t in (x - 1)..x, g t = Phi x := by
    intro x hx
    simp only [hPhi, hG]
    rw [intervalIntegral.integral_interval_sub_left (gint x (by linarith)) (gint (x - 1) (by linarith))]
    rw [show x * (x - 1) * (O x + E x) = (x - 1) * g x from by
      simp only [hg]; ring]
  have Phi_cont : ContinuousOn Phi (Set.Icc 3 s) := by
    have hg1 : ContinuousOn g (Set.Icc 3 s) :=
      gcont.mono (fun x hx => by have : (3 : ℝ) ≤ x := hx.1; show (2 : ℝ) < x; linarith)
    have hG1 : ContinuousOn G (Set.Icc 3 s) :=
      (Gcont s (by linarith)).mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
    have hG2 : ContinuousOn (fun x => G (x - 1)) (Set.Icc 3 s) := by
      refine (Gcont s (by linarith)).comp (continuousOn_id.sub continuousOn_const) ?_
      intro x hx
      exact ⟨by simp only [id]; linarith [hx.1], by simp only [id]; linarith [hx.2]⟩
    simp only [hPhi]
    exact ((continuousOn_id.sub continuousOn_const).mul hg1).sub (hG1.sub hG2)
  have Phi_deriv : ∀ x ∈ Set.Ioo (3 : ℝ) s, HasDerivAt Phi 0 x := by
    intro x hx
    have hx3 : (3 : ℝ) < x := hx.1
    have h1 := ((hasDerivAt_id x).sub_const 1).mul (gderiv x hx3)
    have h2 := Gderiv x (by linarith)
    have h3 : HasDerivAt (fun y => G (y - 1)) (g (x - 1)) x := by
      have h := (Gderiv (x - 1) (by linarith)).comp x ((hasDerivAt_id' x).sub_const 1)
      rw [mul_one] at h
      exact h
    have h4 := h1.sub (h2.sub h3)
    convert h4 using 1
    · funext y; simp only [hPhi, Pi.sub_apply, Pi.mul_apply, id]
    · simp only [id, hg]; ring
  rcases lt_or_eq_of_le hs with hlt | heq
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Phi (fun _ => (0 : ℝ)) hlt Phi_cont
      (fun x hx => Phi_deriv x hx)
    have hne : s - 3 ≠ 0 := by linarith
    have h0 : Phi s = Phi 3 := by
      have hh := hcd.symm
      rw [div_eq_zero_iff] at hh
      rcases hh with h | h
      · linarith
      · exact absurd h hne
    rw [hPhi_eq s hs, hPhi_eq 3 le_rfl, h0]
  · rw [heq]

/-- Display 16 integrated on `[2, t]`, `2 ≤ t ≤ 3`: `t E(t) = 2 E(2) + (t - 2) - A log (t - 1)`
with `A = 3 (1 + O(3))`, using display 17 for `O` on `[1, 3]`. -/
private theorem Eform_x8f (O E : ℝ → ℝ)
    (hO : ∀ s, O s = ∑' n : ℕ, (if Odd n then bjsF306 n s else 0))
    (hE : ∀ s, E s = ∑' n : ℕ, (if Even n then bjsF306 n s else 0))
    (A : ℝ) (hA : A = 3 + 3 * O 3) :
    ∀ t : ℝ, 2 ≤ t → t ≤ 3 → t * E t = 2 * E 2 + (t - 2) - A * log (t - 1) := by
  have Ocont : ContinuousOn O (Set.Ici 1) := by
    have hfun : O = fun s => ∑' n : ℕ, (if Odd n then bjsF306 n s else 0) := by
      funext s; rw [hO s]
    rw [hfun]
    exact leaf8_continuous.1
  intro t ht2 ht3
  have hEcont : ContinuousOn (fun u : ℝ => u * E u) (Set.Icc 2 t) := by
    have hfun : (fun u : ℝ => u * E u) =
        fun u => u * ∑' n : ℕ, (if Even n then bjsF306 n u else 0) := by
      funext u; rw [hE u]
    rw [hfun]
    exact continuousOn_id.mul (leaf8_continuous.2.mono (fun x hx => hx.1))
  have hEderiv : ∀ x ∈ Set.Ioo (2 : ℝ) t, HasDerivAt (fun u : ℝ => u * E u) (-O (x - 1)) x := by
    intro x hx
    have hfun : (fun u : ℝ => u * E u) =
        fun u => u * ∑' n : ℕ, (if Even n then bjsF306 n u else 0) := by
      funext u; rw [hE u]
    rw [hfun]
    have h := leaf8_deriv_even x (by linarith [hx.1])
    rw [← hO (x - 1)] at h
    exact h
  have hEint : IntervalIntegrable (fun u : ℝ => -O (u - 1)) MeasureTheory.volume 2 t := by
    have hc : ContinuousOn (fun u : ℝ => -O (u - 1)) (Set.uIcc (2 : ℝ) t) := by
      rw [Set.uIcc_of_le ht2]
      refine ContinuousOn.neg ?_
      refine Ocont.comp (continuousOn_id.sub continuousOn_const) ?_
      intro u hu
      simp only [Set.mem_Icc] at hu
      simp only [Set.mem_Ici]
      linarith [hu.1]
    exact hc.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht2 hEcont hEderiv hEint
  have hsub : ∫ u in (2 : ℝ)..t, -O (u - 1) = -∫ v in (1 : ℝ)..(t - 1), O v := by
    rw [intervalIntegral.integral_neg]
    congr 1
    rw [intervalIntegral.integral_comp_sub_right (f := O) (a := (2 : ℝ)) (b := t) (d := 1)]
    norm_num
  have hOint : ∀ b : ℝ, 1 ≤ b → b ≤ 3 → ∫ v in (1 : ℝ)..b, O v = A * log b - (b - 1) := by
    intro b hb hb3
    have hcongr : ∫ v in (1 : ℝ)..b, O v = ∫ v in (1 : ℝ)..b, (A / v - 1) := by
      refine intervalIntegral.integral_congr (fun v hv => ?_)
      rw [Set.uIcc_of_le hb] at hv
      have hv1 : (1 : ℝ) ≤ v := hv.1
      have hv3 : v ≤ 3 := by linarith [hv.2, hb3]
      have hv0 : (0 : ℝ) < v := by linarith
      have hvne : v ≠ 0 := ne_of_gt hv0
      have ht_ := tO_low_x8f O hO v hv0 hv3
      have h1 : O v = (3 - v + 3 * O 3) / v := by
        rw [eq_div_iff hvne]
        linarith
      rw [h1, hA]
      field_simp
      ring
    rw [hcongr]
    have hderiv : ∀ v ∈ Set.Ioo (1 : ℝ) b,
        HasDerivAt (fun v : ℝ => A * log v - v) (A / v - 1) v := by
      intro v hv
      have hv0 : (0 : ℝ) < v := by linarith [hv.1]
      have h1 : HasDerivAt (fun v : ℝ => log v) v⁻¹ v := Real.hasDerivAt_log (ne_of_gt hv0)
      have h2 := (h1.const_mul A).sub (hasDerivAt_id v)
      convert h2 using 1
      · funext w; rfl
      · rw [div_eq_mul_inv]
    have hcont : ContinuousOn (fun v : ℝ => A * log v - v) (Set.Icc 1 b) := by
      refine ContinuousOn.sub ?_ continuousOn_id
      refine ContinuousOn.const_mul ?_ A
      exact ContinuousOn.log continuousOn_id (fun v hv => ne_of_gt (by linarith [hv.1]))
    have hint : IntervalIntegrable (fun v : ℝ => A / v - 1) MeasureTheory.volume 1 b := by
      have h2 : ContinuousOn (fun v : ℝ => A / v - 1) (Set.uIcc (1 : ℝ) b) := by
        rw [Set.uIcc_of_le hb]
        refine ContinuousOn.sub ?_ continuousOn_const
        refine ContinuousOn.div continuousOn_const continuousOn_id ?_
        intro v hv
        exact ne_of_gt (by linarith [hv.1])
      exact h2.intervalIntegrable
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := fun v : ℝ => A * log v - v) hb hcont hderiv hint
    rw [h, Real.log_one]
    ring
  have hbt : 1 ≤ t - 1 := by linarith
  have hval : t * E t - 2 * E 2 = (t - 2) - A * log (t - 1) := by
    rw [← hftc, hsub, hOint (t - 1) hbt (by linarith)]
    ring
  linarith

/-- Displays 15 to 17 on `[2, 3]`: `I(3) = 2 E(2) - 2`. -/
private theorem I_three_x8f (O E : ℝ → ℝ)
    (hO : ∀ s, O s = ∑' n : ℕ, (if Odd n then bjsF306 n s else 0))
    (hE : ∀ s, E s = ∑' n : ℕ, (if Even n then bjsF306 n s else 0)) :
    3 * (3 - 1) * (O 3 + E 3) - ∫ t in ((3 : ℝ) - 1)..3, t * (O t + E t) = 2 * E 2 - 2 := by
  set A := 3 + 3 * O 3 with hA
  have hEform := Eform_x8f O E hO hE A hA
  have hE3 : 3 * E 3 = 2 * E 2 + 1 - A * log 2 := by
    have h := hEform 3 (by norm_num) le_rfl
    norm_num at h
    linarith
  have hQg : ∫ t in (2 : ℝ)..3, t * (O t + E t) =
      ∫ t in (2 : ℝ)..3, (A + 2 * E 2 - 2 - A * log (t - 1)) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] at ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have ht3 : t ≤ 3 := ht.2
    have h1 : t * O t = A - t := by
      have h := tO_low_x8f O hO t (by linarith) ht3
      rw [hA]
      linarith
    have h2 := hEform t ht2 ht3
    rw [mul_add, h1, h2]
    ring
  have hIval : ∫ t in (2 : ℝ)..3, (A + 2 * E 2 - 2 - A * log (t - 1)) =
      2 * A - 2 * A * log 2 + 2 * E 2 - 2 := by
    have hderiv : ∀ x ∈ Set.Ioo (2 : ℝ) 3,
        HasDerivAt (fun t : ℝ => (A + 2 * E 2 - 2) * (t - 2) -
          A * ((t - 1) * log (t - 1) - (t - 1))) (A + 2 * E 2 - 2 - A * log (x - 1)) x := by
      intro x hx
      have hx1 : (0 : ℝ) < x - 1 := by linarith [hx.1]
      have hxne : x - 1 ≠ 0 := ne_of_gt hx1
      have hlin : HasDerivAt (fun t : ℝ => t - 1) 1 x := (hasDerivAt_id x).sub_const 1
      have hlog : HasDerivAt (fun t : ℝ => log (t - 1)) (1 / (x - 1)) x := hlin.log hxne
      have hlogd : HasDerivAt (fun t : ℝ => (t - 1) * log (t - 1)) (log (x - 1) + 1) x := by
        have hm := hlin.mul hlog
        convert hm using 1
        simp only [div_eq_mul_inv, one_mul, mul_inv_cancel₀ hxne]
      have hA1 : HasDerivAt (fun t : ℝ => (t - 1) * log (t - 1) - (t - 1))
          (log (x - 1) + 1 - 1) x := hlogd.sub hlin
      have hA2 : HasDerivAt (fun t : ℝ => A * ((t - 1) * log (t - 1) - (t - 1)))
          (A * (log (x - 1) + 1 - 1)) x := hA1.const_mul A
      have hB : HasDerivAt (fun t : ℝ => (A + 2 * E 2 - 2) * (t - 2))
          ((A + 2 * E 2 - 2) * 1) x :=
        ((hasDerivAt_id x).sub_const 2).const_mul (A + 2 * E 2 - 2)
      have h3 := hB.sub hA2
      convert h3 using 1
      ring
    have hcont : ContinuousOn (fun t : ℝ => (A + 2 * E 2 - 2) * (t - 2) -
        A * ((t - 1) * log (t - 1) - (t - 1))) (Set.Icc 2 3) := by
      refine ContinuousOn.sub ?_ ?_
      · fun_prop
      · refine ContinuousOn.const_mul ?_ A
        refine ContinuousOn.sub ?_ ?_
        · refine ContinuousOn.mul ?_ ?_
          · fun_prop
          · refine ContinuousOn.log ?_ ?_
            · fun_prop
            · intro t ht
              have h1 : (2 : ℝ) ≤ t := ht.1
              exact ne_of_gt (by linarith)
        · fun_prop
    have hint : IntervalIntegrable (fun t : ℝ => A + 2 * E 2 - 2 - A * log (t - 1))
        MeasureTheory.volume 2 3 := by
      have h2 : ContinuousOn (fun t : ℝ => A + 2 * E 2 - 2 - A * log (t - 1))
          (Set.uIcc (2 : ℝ) 3) := by
        rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)]
        refine ContinuousOn.sub continuousOn_const ?_
        refine ContinuousOn.const_mul ?_ A
        refine ContinuousOn.log ?_ ?_
        · fun_prop
        · intro t ht
          have h1 : (2 : ℝ) ≤ t := ht.1
          exact ne_of_gt (by linarith)
      exact h2.intervalIntegrable
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := fun t : ℝ => (A + 2 * E 2 - 2) * (t - 2) -
        A * ((t - 1) * log (t - 1) - (t - 1)))
      (by norm_num : (2 : ℝ) ≤ 3) hcont hderiv hint
    rw [h]
    norm_num
    ring
  rw [show (3 : ℝ) - 1 = 2 by norm_num, hQg, hIval]
  have hQ3 : 3 * 2 * (O 3 + E 3) = 2 * A - 4 + 4 * E 2 - 2 * A * log 2 := by
    linarith
  rw [hQ3, hA]
  ring

/-- The invariant `I` is constant on `[3, ∞)` and tends to `0`, while `I(3) = 2 E(2) - 2`:
hence `E(2) = 1`, that is `f(2) = 0` in Nathanson Theorem 9.4, BJS display 8. -/
private theorem eSum_two_value_x8f :
    (∑' n : ℕ, (if Even n then bjsF306 n 2 else 0)) = 1 := by
  let O : ℝ → ℝ := fun s => ∑' n : ℕ, (if Odd n then bjsF306 n s else 0)
  let E : ℝ → ℝ := fun s => ∑' n : ℕ, (if Even n then bjsF306 n s else 0)
  have hO : ∀ s, O s = ∑' n : ℕ, (if Odd n then bjsF306 n s else 0) := fun s => rfl
  have hE : ∀ s, E s = ∑' n : ℕ, (if Even n then bjsF306 n s else 0) := fun s => rfl
  have hI3 : 3 * (3 - 1) * (O 3 + E 3) - ∫ t in ((3 : ℝ) - 1)..3, t * (O t + E t) =
      2 * E 2 - 2 := I_three_x8f O E hO hE
  have hIconst : ∀ s : ℝ, 3 ≤ s →
      s * (s - 1) * (O s + E s) - ∫ t in (s - 1)..s, t * (O t + E t) =
        3 * (3 - 1) * (O 3 + E 3) - ∫ t in ((3 : ℝ) - 1)..3, t * (O t + E t) :=
    fun s hs => I_const_x8f O E hO hE s hs
  have htend := I_tendsto_x8f O E hO hE
  have hev : (fun s : ℝ => s * (s - 1) * (O s + E s) - ∫ t in (s - 1)..s, t * (O t + E t))
      =ᶠ[Filter.atTop]
        fun _ => 3 * (3 - 1) * (O 3 + E 3) - ∫ t in ((3 : ℝ) - 1)..3, t * (O t + E t) :=
    Filter.eventually_atTop.2 ⟨3, fun s hs => hIconst s hs⟩
  have h1 : Filter.Tendsto
      (fun s : ℝ => s * (s - 1) * (O s + E s) - ∫ t in (s - 1)..s, t * (O t + E t))
      Filter.atTop
      (nhds (3 * (3 - 1) * (O 3 + E 3) - ∫ t in ((3 : ℝ) - 1)..3, t * (O t + E t))) :=
    tendsto_const_nhds.congr' hev.symm
  have h0 : 3 * (3 - 1) * (O 3 + E 3) - ∫ t in ((3 : ℝ) - 1)..3, t * (O t + E t) = 0 :=
    tendsto_nhds_unique h1 htend
  have hE2 : E 2 = 1 := by
    have h : 2 * E 2 - 2 = 0 := by rw [← hI3, h0]
    linarith
  rw [show (∑' n : ℕ, (if Even n then bjsF306 n 2 else 0)) = E 2 from (hE 2).symm]
  exact hE2

/-- LEAF: Nathanson Theorem 9.4 as used by BJS page 6, display 14 at s = 2: the sum of
f_n(2) over even n is 1, that is f(2) = 0, the continuity of f at 2 in display 8.
Class HARD: a boundary value of the series 14, part of the analytic core with leaf8_F3. -/
theorem leaf8_f2 :
    HasSum (fun n : ℕ => if Even n then bjsF306 n 2 else 0) 1 := by
  rw [show (1 : ℝ) = ∑' n : ℕ, (if Even n then bjsF306 n 2 else 0) from
    eSum_two_value_x8f.symm]
  exact (leaf8_summable.2 2 le_rfl).hasSum

/-- Odd n ≥ 2 is at least 3. Helper. -/
theorem three_le_of_odd_s8 (m : ℕ) (ho : Odd (m + 2)) : 3 ≤ m + 2 := by
  rcases m with _ | m
  · exact absurd ho (by decide)
  · omega

/-- Display 17 and 15: for 1 ≤ s ≤ 3 the odd terms are f_1(s) = (3 - s) / s plus
3 / s times the odd terms at s = 3 with n ≥ 3. -/
theorem odd_terms_le3_s8 (s : ℝ) (hs1 : 1 ≤ s) (hs3 : s ≤ 3) (n : ℕ) :
    (if Odd n then bjsF306 n s else 0) =
      (if n = 1 then (3 - s) / s else 0) +
        3 / s * (if Odd n ∧ 3 ≤ n then bjsF306 n 3 else 0) := by
  have hs0 : 0 < s := by linarith
  match n with
  | 0 => simp
  | 1 => simp [bjsF306, hs3]
  | m + 2 =>
    by_cases ho : Odd (m + 2)
    · rw [if_pos ho, if_neg (show m + 2 ≠ 1 by omega),
        if_pos (show Odd (m + 2) ∧ 3 ≤ m + 2 from ⟨ho, three_le_of_odd_s8 m ho⟩)]
      simp only [bjsF306, if_pos (And.intro ho hs3), if_pos (And.intro ho (le_refl (3 : ℝ)))]
      field_simp
      ring
    · rw [if_neg ho, if_neg (show m + 2 ≠ 1 by omega),
        if_neg (show ¬(Odd (m + 2) ∧ 3 ≤ m + 2) from fun h => ho h.1)]
      ring

/-- BJS display 13 on [1, 3] from leaf8_F3 and display 17: the odd series sums to
2 e ^ γ / s - 1. -/
theorem hasSum_odd_le3_s8 (s : ℝ) (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    HasSum (fun n : ℕ => if Odd n then bjsF306 n s else 0)
      (2 * exp eulerMascheroniConstant / s - 1) := by
  have hs0 : 0 < s := by linarith
  have h3 : HasSum (fun n : ℕ => if Odd n ∧ 3 ≤ n then bjsF306 n 3 else 0)
      (2 * exp eulerMascheroniConstant / 3 - 1) := by
    convert leaf8_F3 using 1
    funext n
    match n with
    | 0 => simp
    | 1 => simp [bjsF306]
    | m + 2 =>
      by_cases ho : Odd (m + 2)
      · rw [if_pos ⟨ho, three_le_of_odd_s8 m ho⟩, if_pos ho]
      · rw [if_neg (fun h => ho h.1), if_neg ho]
  have hsum := (hasSum_ite_eq 1 ((3 - s) / s)).add (h3.mul_left (3 / s))
  convert hsum using 1
  · funext n
    rw [odd_terms_le3_s8 s hs1 hs3 n]
  · field_simp
    ring

/-- Assembly: from the sums O, E of the series 13 and 14 with the LEAF properties, the
functions F = 2 e ^ γ / s on (0, 2], 1 + O on (2, ∞) and f = 0 on (0, 2], 1 - E on
(2, ∞) solve the system 8. Proved here. -/
theorem assembly_s8 (O E : ℝ → ℝ)
    (hOs : ∀ s : ℝ, 1 ≤ s → HasSum (fun n : ℕ => if Odd n then bjsF306 n s else 0) (O s))
    (hEs : ∀ s : ℝ, 2 ≤ s → HasSum (fun n : ℕ => if Even n then bjsF306 n s else 0) (E s))
    (hO13 : ∀ s : ℝ, 1 ≤ s → s ≤ 3 → O s = 2 * exp eulerMascheroniConstant / s - 1)
    (hE2 : E 2 = 1)
    (hOc : ContinuousOn O (Set.Ici 1)) (hEc : ContinuousOn E (Set.Ici 2))
    (hdE : ∀ s : ℝ, 2 < s → HasDerivAt (fun t => t * E t) (-O (s - 1)) s)
    (hdO : ∀ s : ℝ, 3 < s → HasDerivAt (fun t => t * O t) (-E (s - 1)) s)
    (hdO3 : HasDerivWithinAt (fun t => t * O t) (-E 2) (Set.Ici 3) 3) :
    ∃ F' f' : ℝ → ℝ, LeanLab.ChenExplicit.IsLinearSieveFns F' f' ∧
      (∀ s : ℝ, 1 ≤ s → HasSum (fun n : ℕ => if Odd n then bjsF306 n s else 0) (F' s - 1)) ∧
      (∀ s : ℝ, 2 ≤ s → HasSum (fun n : ℕ => if Even n then bjsF306 n s else 0) (1 - f' s)) := by
  set c := 2 * exp eulerMascheroniConstant with hc
  set F' : ℝ → ℝ := fun s => if s ≤ 2 then c / s else 1 + O s with hF'
  set f' : ℝ → ℝ := fun s => if s ≤ 2 then 0 else 1 - E s with hf'
  have hF1 : ∀ t : ℝ, 1 ≤ t → F' t = 1 + O t := by
    intro t ht
    simp only [hF']
    split_ifs with h
    · rw [hO13 t ht (by linarith)]; ring
    · rfl
  have hF3 : ∀ t : ℝ, 0 < t → t ≤ 3 → F' t = c / t := by
    intro t ht0 ht3
    simp only [hF']
    split_ifs with h
    · rfl
    · rw [hO13 t (by linarith) ht3]; ring
  have hf2 : ∀ t : ℝ, 2 ≤ t → f' t = 1 - E t := by
    intro t ht
    simp only [hf']
    split_ifs with h
    · have : t = 2 := le_antisymm h ht
      rw [this, hE2]; ring
    · rfl
  have hf0 : ∀ t : ℝ, t ≤ 2 → f' t = 0 := by
    intro t ht; simp only [hf', if_pos ht]
  refine ⟨F', f', ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro s hs hs2
    exact ⟨by simp only [hF', if_pos hs2, hc], hf0 s hs2⟩
  · intro x hx
    have hx0 : (0 : ℝ) < x := hx
    apply ContinuousAt.continuousWithinAt
    by_cases hx3 : x < 3
    · have hev : (fun t => c / t) =ᶠ[nhds x] F' := by
        filter_upwards [Ioo_mem_nhds hx0 hx3] with t ht
        exact (hF3 t ht.1 ht.2.le).symm
      exact ((continuousAt_const.div continuousAt_id hx0.ne')).congr hev
    · push_neg at hx3
      have hev : (fun t => 1 + O t) =ᶠ[nhds x] F' := by
        filter_upwards [Ioi_mem_nhds (show (1 : ℝ) < x by linarith)] with t ht
        exact (hF1 t (le_of_lt ht)).symm
      have hOx : ContinuousAt O x := hOc.continuousAt (Ici_mem_nhds (by linarith))
      exact (continuousAt_const.add hOx).congr hev
  · intro x hx
    have hx0 : (0 : ℝ) < x := hx
    apply ContinuousAt.continuousWithinAt
    rcases lt_trichotomy x 2 with hx2 | hx2 | hx2
    · have hev : (fun _ => (0 : ℝ)) =ᶠ[nhds x] f' := by
        filter_upwards [Iio_mem_nhds hx2] with t ht
        exact (hf0 t (le_of_lt ht)).symm
      exact continuousAt_const.congr hev
    · subst hx2
      have h1 : ContinuousWithinAt f' (Set.Iic 2) 2 := by
        have : ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Set.Iic (2 : ℝ)) 2 := continuousWithinAt_const
        refine this.congr (fun t ht => hf0 t ht) (hf0 2 le_rfl)
      have h2 : ContinuousWithinAt f' (Set.Ici 2) 2 := by
        have : ContinuousWithinAt (fun t => 1 - E t) (Set.Ici 2) 2 :=
          continuousWithinAt_const.sub (hEc 2 Set.self_mem_Ici)
        refine this.congr (fun t ht => hf2 t ht) (hf2 2 le_rfl)
      have := h1.union h2
      rw [Set.Iic_union_Ici, continuousWithinAt_univ] at this
      exact this
    · have hev : (fun t => 1 - E t) =ᶠ[nhds x] f' := by
        filter_upwards [Ioi_mem_nhds hx2] with t ht
        exact (hf2 t (le_of_lt ht)).symm
      have hEx : ContinuousAt E x := hEc.continuousAt (Ici_mem_nhds hx2)
      exact (continuousAt_const.sub hEx).congr hev
  · intro s hs
    constructor
    · -- (s F(s))' = f(s - 1)
      rcases lt_trichotomy s 3 with hs3 | hs3 | hs3
      · have hev : (fun _ : ℝ => c) =ᶠ[nhds s] (fun t => t * F' t) := by
          filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < s by linarith) hs3] with t ht
          rw [hF3 t ht.1 ht.2.le]; field_simp [ht.1.ne']
        rw [hf0 (s - 1) (by linarith)]
        exact (hasDerivAt_const s c).congr_of_eventuallyEq hev.symm
      · subst hs3
        rw [show (3 : ℝ) - 1 = 2 by norm_num, hf0 2 le_rfl]
        have h1 : HasDerivWithinAt (fun t => t * F' t) 0 (Set.Iic 3) 3 := by
          have hc0 : HasDerivWithinAt (fun _ : ℝ => c) 0 (Set.Iic (3 : ℝ)) 3 := hasDerivWithinAt_const _ _ _
          refine hc0.congr_of_eventuallyEq ?_ ?_
          · filter_upwards [inter_mem_nhdsWithin (Set.Iic (3 : ℝ))
              (Ioi_mem_nhds (show (0 : ℝ) < 3 by norm_num))] with t ht
            rw [hF3 t ht.2 ht.1]; field_simp [(show (0 : ℝ) < t from ht.2).ne']
          · rw [hF3 3 (by norm_num) le_rfl]; field_simp
        have h2 : HasDerivWithinAt (fun t => t * F' t) 0 (Set.Ici 3) 3 := by
          have hh := (hasDerivWithinAt_id (3 : ℝ) (Set.Ici 3)).add hdO3
          rw [hE2] at hh
          norm_num at hh
          refine hh.congr_of_eventuallyEq ?_ ?_
          · filter_upwards [self_mem_nhdsWithin] with t ht
            have ht' : (3 : ℝ) ≤ t := ht
            show t * F' t = id t + t * O t
            rw [hF1 t (by linarith)]; simp only [id]; ring
          · show (3 : ℝ) * F' 3 = id 3 + 3 * O 3
            rw [hF1 3 (by norm_num)]; simp only [id]; ring
        have := h1.union h2
        rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
        exact this
      · have hev : (fun t => t + t * O t) =ᶠ[nhds s] (fun t => t * F' t) := by
          filter_upwards [Ioi_mem_nhds (show (1 : ℝ) < s by linarith)] with t ht
          rw [hF1 t ht.le]; ring
        rw [hf2 (s - 1) (by linarith)]
        have hh := (hasDerivAt_id s).add (hdO s hs3)
        rw [show (1 : ℝ) + -E (s - 1) = 1 - E (s - 1) by ring] at hh
        exact hh.congr_of_eventuallyEq hev.symm
    · -- (s f(s))' = F(s - 1)
      have hev : (fun t => t - t * E t) =ᶠ[nhds s] (fun t => t * f' t) := by
        filter_upwards [Ioi_mem_nhds hs] with t ht
        rw [hf2 t ht.le]; ring
      rw [hF1 (s - 1) (by linarith)]
      have hh := (hasDerivAt_id s).sub (hdE s hs)
      rw [show (1 : ℝ) - -O (s - 1) = 1 + O (s - 1) by ring] at hh
      exact hh.congr_of_eventuallyEq hev.symm
  · intro s hs
    rw [hF1 s hs, add_sub_cancel_left]
    exact hOs s hs
  · intro s hs
    rw [hf2 s hs, sub_sub_cancel]
    exact hEs s hs

/-- Twin of leaf306_series_solve8, Nathanson Theorem 9.4 existence half, BJS page 6,
displays 8, 13 and 14, proved from the LEAF lemmas above by assembly_s8. -/
theorem leaf306_series_solve8_twin :
    ∃ F' f' : ℝ → ℝ, LeanLab.ChenExplicit.IsLinearSieveFns F' f' ∧
      (∀ s : ℝ, 1 ≤ s → HasSum (fun n : ℕ => if Odd n then bjsF306 n s else 0) (F' s - 1)) ∧
      (∀ s : ℝ, 2 ≤ s → HasSum (fun n : ℕ => if Even n then bjsF306 n s else 0) (1 - f' s)) := by
  refine assembly_s8 (fun s => ∑' n : ℕ, if Odd n then bjsF306 n s else 0)
    (fun s => ∑' n : ℕ, if Even n then bjsF306 n s else 0)
    (fun s hs => (leaf8_summable.1 s hs).hasSum) (fun s hs => (leaf8_summable.2 s hs).hasSum)
    (fun s hs1 hs3 => (hasSum_odd_le3_s8 s hs1 hs3).tsum_eq) leaf8_f2.tsum_eq
    leaf8_continuous.1 leaf8_continuous.2 leaf8_deriv_even leaf8_deriv_odd.1 ?_
  have h := leaf8_deriv_odd.2
  simpa [show (3 : ℝ) - 1 = 2 by norm_num] using h

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leaf306_series_solve8_twin
