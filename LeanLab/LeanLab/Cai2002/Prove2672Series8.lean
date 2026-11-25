/-
Independent support for the sealed series lemmas in Split1122bSeries8.
The existing Prove1122b files import that file, so importing them back would
create a cycle. The continuity argument below reuses their tail integral
and geometric majorant proofs in a separate namespace.
Source: BJS, papers/P0009.pdf, page 6, displays 15 to 18 and Lemma 8.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split306Theorem6

open Finset Real
noncomputable section
namespace LeanLab.Cai2002.Series8Proof2672

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

theorem contOn_shift_c8 (f : ℝ → ℝ) (a : ℝ) (hf : ContinuousOn f (Set.Ici (a - 1))) :
    ContinuousOn (fun t => f (t - 1)) (Set.Ici a) :=
  hf.comp (continuousOn_id.sub continuousOn_const) (fun t ht => by
    simp only [Set.mem_Ici] at ht ⊢; linarith)

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
      · have hodd1 : Odd (m + 1) := by
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
      · have hev1 : Even (m + 1) := by
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

theorem hSieve_le_c8 (s : ℝ) : LeanLab.ChenExplicit.hSieve s ≤ exp (-2) := by
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

def majU8 (n : ℕ) : ℝ := 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * exp (-2)

theorem majU8_nonneg (n : ℕ) : 0 ≤ majU8 n := by
  unfold majU8; positivity

theorem majU8_summable : Summable majU8 := by
  rw [← summable_nat_add_iff 1]
  have hg : Summable (fun m : ℕ => (2 * exp 2 * exp (-2)) * (0.9607 : ℝ) ^ m) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine hg.congr (fun m => ?_)
  unfold majU8
  rw [show m + 1 - 1 = m by omega]
  ring

theorem term_le_majU8 (P : ℕ → Prop) [DecidablePred P] (s : ℝ)
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
      exact mul_le_mul_of_nonneg_left (hSieve_le_c8 s) h2
  · simp only [norm_zero]; exact majU8_nonneg n

theorem norm_fn_le (n : ℕ) (s : ℝ)
    (hs : (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s)) :
    ‖bjsF306 n s‖ ≤ 2 * (0.9607 : ℝ) ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [bjsF306, norm_zero]
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (leaf306_fn_nonneg n s hs)]
  have hb := key_l8306 n hn s hs
  have he : exp 2 * exp (-2) = 1 := by rw [← exp_add]; norm_num
  calc bjsF306 n s
      ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * exp (-2) :=
        hb.trans (mul_le_mul_of_nonneg_left (hSieve_le_c8 s) (by positivity))
    _ = 2 * (0.9607 : ℝ) ^ (n - 1) * (exp 2 * exp (-2)) := by ring
    _ = _ := by rw [he, mul_one]

theorem derivG_d8 (φ : ℝ → ℝ) (a s : ℝ) (has : a < s)
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
  rw [← intervalIntegral.integral_Ioi_sub_Ioi hi (le_of_lt hz)]
  ring

theorem deriv_term_even_d8 (m : ℕ) (he : Even (m + 2)) (y : ℝ) (hy : 2 < y) :
    HasDerivAt (fun z => z * bjsF306 (m + 2) z) (-bjsF306 (m + 1) (y - 1)) y := by
  have hod : Odd (m + 1) := by
    rcases Nat.even_or_odd (m + 1) with h | h
    · exact absurd he (by rw [Nat.not_even_iff_odd]; exact h.add_one)
    · exact h
  have hc1 := (contOn_fn_c8 (m + 1)).1 hod
  have hc : ContinuousOn (fun u => bjsF306 (m + 1) (u - 1)) (Set.Ici 2) :=
    contOn_shift_c8 _ 2 (by norm_num; exact hc1)
  have hi := integrableOn_shift_c8 (m + 1) (by omega) 2 (by norm_num)
    (hc.mono Set.Ioi_subset_Ici_self) (fun u hu => Or.inl ⟨hod, by linarith⟩)
  have hca : ContinuousAt (fun u => bjsF306 (m + 1) (u - 1)) y :=
    hc.continuousAt (Ici_mem_nhds hy)
  have hd := derivG_d8 (fun u => bjsF306 (m + 1) (u - 1)) 2 y hy hi hca
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hy] with z hz
  have hz' : (2 : ℝ) < z := hz
  have hno : ¬ (Odd (m + 2) ∧ z ≤ 3) := fun h =>
    absurd h.1 (by rw [Nat.not_odd_iff_even]; exact he)
  simp only [bjsF306, if_neg hno]
  field_simp

theorem deriv_bound_d8 (n : ℕ) (y : ℝ) (hy : 2 < y) :
    ‖(if Even n then -bjsF306 (n - 1) (y - 1) else 0)‖ ≤ 2 * (0.9607 : ℝ) ^ (n - 2) := by
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
      simpa only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
        Nat.add_sub_cancel, norm_neg] using
        norm_fn_le (m + 1) (y - 1) (Or.inl ⟨hod, by linarith⟩)
  · simpa using hu

theorem bound_summable_d8 : Summable (fun n : ℕ => 2 * (0.9607 : ℝ) ^ (n - 2)) := by
  rw [← summable_nat_add_iff 2]
  simpa only [Nat.add_sub_cancel] using
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 0.9607)
      (by norm_num)).mul_left (2 : ℝ)

/-- Extend the even integrand continuously across the odd series endpoint. -/
def phiExt_o8 (m : ℕ) (u : ℝ) : ℝ := bjsF306 (m + 1) (max u 3 - 1)

theorem phiExt_cont_o8 (m : ℕ) (he : Even (m + 1)) : Continuous (phiExt_o8 m) := by
  have hc := (contOn_fn_c8 (m + 1)).2 he
  unfold phiExt_o8
  refine hc.comp_continuous (by fun_prop) (fun u => ?_)
  show (2 : ℝ) ≤ max u 3 - 1
  have := le_max_right u 3; linarith

def KExt_o8 (m : ℕ) (t : ℝ) : ℝ :=
  (∫ u in Set.Ioi (3 : ℝ), bjsF306 (m + 1) (u - 1)) - ∫ u in (3 : ℝ)..t, phiExt_o8 m u

theorem KExt_eq_o8 (m : ℕ) (he : Even (m + 1)) (t : ℝ) (ht : 3 ≤ t) :
    KExt_o8 m t = ∫ u in Set.Ioi t, bjsF306 (m + 1) (u - 1) := by
  have hc : ContinuousOn (fun u => bjsF306 (m + 1) (u - 1)) (Set.Ici 3) :=
    contOn_shift_c8 _ 3 (by norm_num; exact (contOn_fn_c8 (m + 1)).2 he)
  have hi := integrableOn_shift_c8 (m + 1) (by omega) 3 (by norm_num)
    (hc.mono Set.Ioi_subset_Ici_self) (fun u hu => Or.inr ⟨he, by linarith⟩)
  unfold KExt_o8
  have h1 : ∫ u in (3 : ℝ)..t, phiExt_o8 m u = ∫ u in (3 : ℝ)..t, bjsF306 (m + 1) (u - 1) := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le ht] at hu
    simp only [phiExt_o8, max_eq_left hu.1]
  rw [h1, ← intervalIntegral.integral_Ioi_sub_Ioi hi ht]
  ring

theorem KExt_deriv_o8 (m : ℕ) (he : Even (m + 1)) (y : ℝ) :
    HasDerivAt (KExt_o8 m) (-phiExt_o8 m y) y := by
  exact ((phiExt_cont_o8 m he).integral_hasStrictDerivAt 3 y).hasDerivAt.const_sub
    (∫ u in Set.Ioi (3 : ℝ), bjsF306 (m + 1) (u - 1))

theorem even_of_odd_o8 (m : ℕ) (ho : Odd (m + 2)) : Even (m + 1) := by
  rcases Nat.even_or_odd (m + 1) with h | h
  · exact h
  · exact absurd ho (by rw [Nat.not_odd_iff_even]; exact h.add_one)

def gOdd_o8 (n : ℕ) (t : ℝ) : ℝ := if Odd n ∧ 2 ≤ n then KExt_o8 (n - 2) t else 0

def gOdd'_o8 (n : ℕ) (y : ℝ) : ℝ := if Odd n ∧ 2 ≤ n then -phiExt_o8 (n - 2) y else 0

theorem gOdd_eq_o8 (n : ℕ) (t : ℝ) (ht : 3 ≤ t) :
    gOdd_o8 n t = if Odd n then t * bjsF306 n t else 0 := by
  have htp : t ≠ 0 := by intro h; linarith
  match n with
  | 0 => simp [gOdd_o8]
  | 1 =>
    simp only [gOdd_o8, show ¬ (Odd 1 ∧ 2 ≤ 1) from by omega, if_false, if_pos odd_one,
      bjsF306]
    split_ifs with h
    · have : t = 3 := le_antisymm h ht
      subst this; norm_num
    · simp
  | m + 2 =>
    by_cases ho : Odd (m + 2)
    · have he := even_of_odd_o8 m ho
      simp only [gOdd_o8, if_pos (And.intro ho (by omega : 2 ≤ m + 2)), if_pos ho,
        show m + 2 - 2 = m by omega, KExt_eq_o8 m he t ht, bjsF306]
      split_ifs with h
      · have : t = 3 := le_antisymm h.2 ht
        subst this; field_simp
      · field_simp
    · simp [gOdd_o8, ho]

theorem gOdd_deriv_o8 (n : ℕ) (y : ℝ) : HasDerivAt (gOdd_o8 n) (gOdd'_o8 n y) y := by
  by_cases h : Odd n ∧ 2 ≤ n
  · have hfun : gOdd_o8 n = KExt_o8 (n - 2) := by
      funext t; simp only [gOdd_o8, if_pos h]
    rw [hfun]; simp only [gOdd'_o8, if_pos h]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [show m + 2 - 2 = m by omega]
    exact KExt_deriv_o8 m (even_of_odd_o8 m h.1) y
  · have hfun : gOdd_o8 n = fun _ => 0 := by
      funext t; simp only [gOdd_o8, if_neg h]
    rw [hfun]; simp only [gOdd'_o8, if_neg h]
    exact hasDerivAt_const y (0 : ℝ)

theorem gOdd_bound_o8 (n : ℕ) (y : ℝ) : ‖gOdd'_o8 n y‖ ≤ 2 * (0.9607 : ℝ) ^ (n - 2) := by
  have hu : 0 ≤ 2 * (0.9607 : ℝ) ^ (n - 2) := by positivity
  unfold gOdd'_o8
  split_ifs with h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have he := even_of_odd_o8 m h.1
    rw [show m + 2 - 2 = m by omega, norm_neg]
    unfold phiExt_o8
    have hx : (2 : ℝ) ≤ max y 3 - 1 := by have := le_max_right y 3; linarith
    simpa only [Nat.add_sub_cancel] using
      norm_fn_le (m + 1) (max y 3 - 1) (Or.inr ⟨he, hx⟩)
  · simpa using hu

theorem gsum'_eq_o8 (y : ℝ) (hy : 3 ≤ y) :
    ∑' n, gOdd'_o8 n y = -(∑' n : ℕ, if Even n then bjsF306 n (y - 1) else 0) := by
  have hsum : Summable (fun n => gOdd'_o8 n y) :=
    Summable.of_norm_bounded bound_summable_d8 (fun n => gOdd_bound_o8 n y)
  rw [hsum.tsum_eq_zero_add]
  have h0 : gOdd'_o8 0 y = 0 := by simp [gOdd'_o8]
  rw [h0, zero_add, ← tsum_neg]
  congr 1; funext k
  rcases k with _ | k
  · simp [gOdd'_o8, bjsF306]
  · have hmax : max y 3 = y := max_eq_left hy
    simp only [gOdd'_o8, phiExt_o8, hmax, show k + 1 + 1 - 2 = k by omega,
      show 2 ≤ k + 1 + 1 by omega, and_true, Nat.odd_add_one, Nat.not_odd_iff_even]
    split_ifs <;> simp_all [Nat.even_add_one]

end LeanLab.Cai2002.Series8Proof2672
