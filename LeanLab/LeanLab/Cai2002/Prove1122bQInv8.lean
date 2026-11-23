/-
Twin proofs of the LEAFs `leafB8_IQ_tendsto` and `leafB8_IQ_const` of
`Split1122bBoundary8.lean`.

Source: Bordignon, Johnston, Starichkova, arXiv 2207.09452v6, papers/P0009.pdf, page 6,
displays 13 to 18, quoting Nathanson Theorem 9.4. Write Q = O + E for the sum of f_n over
all n and I(s) = s (s - 1) Q(s) - the integral of t Q(t) over [s - 1, s].

* Tendsto: by display 18 with Lemma 8, key_l8306 with c_n = 0.9607, and
  leaf306_fn_nonneg, 0 ≤ Q(s) ≤ C h(s) with t h(t) ≤ 3 e ^ -t for t ≥ 3, so both parts of
  I(s) are bounded by a multiple of (s + e) e ^ -s, which tends to 0.
* Const: for s > 3 the PROVED derivative twins give (s Q(s))' = - Q(s - 1); with
  g(t) = t Q(t) continuous on t > 2, where for 2 < t ≤ 3 the odd part is t O(t) =
  3 - t + 3 O(3) by displays 15 and 17, the derivative of I vanishes on (3, ∞), and I is
  continuous on [3, ∞) because g is bounded on (2, b]; the mean value theorem gives
  constancy.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122bBoundary8
import LeanLab.Cai2002.Prove1122bDerivOdd8

open Finset Real

noncomputable section

namespace LeanLab.Cai2002

/-- Display 18 summed: a parity part of the series is at most M h(s). -/
theorem paritySum_le_q8 (P : ℕ → Prop) [DecidablePred P] (s : ℝ)
    (hP : ∀ n, P n → (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s)) (hs : 0 ≤ s) :
    (∑' n : ℕ, if P n then bjsF306 n s else 0) ≤
      (2 * exp 2 / 0.9607 * (1 - 0.9607)⁻¹) * LeanLab.ChenExplicit.hSieve s := by
  have hh := hSieve_nonneg306 s hs
  set A := 2 * exp 2 * LeanLab.ChenExplicit.hSieve s / 0.9607 with hA
  have hA0 : 0 ≤ A := by positivity
  have hb : ∀ n : ℕ, (if P n then bjsF306 n s else 0) ≤ A * (0.9607 : ℝ) ^ n := by
    intro n
    rcases n with _ | k
    · split_ifs
      · show (0 : ℝ) ≤ _; positivity
      · positivity
    · split_ifs with h
      · have := key_l8306 (k + 1) (by omega) s (hP _ h)
        rw [show k + 1 - 1 = k by omega] at this
        have he : A * (0.9607 : ℝ) ^ (k + 1) =
            2 * exp 2 * (0.9607 : ℝ) ^ k * LeanLab.ChenExplicit.hSieve s := by
          rw [hA, pow_succ]; field_simp
        rw [he]; exact this
      · positivity
  have hsum := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 0.9607)
    (by norm_num)).mul_left A
  have h1 := Summable.tsum_le_tsum hb (parity_summableB8 P s hP hs) hsum
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h1
  calc _ ≤ A * (1 - 0.9607)⁻¹ := h1
    _ = _ := by rw [hA]; ring

theorem paritySum_nonneg_q8 (P : ℕ → Prop) [DecidablePred P] (s : ℝ)
    (hP : ∀ n, P n → (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s)) :
    0 ≤ ∑' n : ℕ, if P n then bjsF306 n s else 0 := by
  refine tsum_nonneg (fun n => ?_)
  split_ifs with h
  · rcases n with _ | k
    · exact le_refl (0 : ℝ)
    · exact leaf306_fn_nonneg _ s (hP _ h)
  · exact le_rfl

/-- The constant of the bound Q ≤ 2 M h. -/
def mQ8 : ℝ := 2 * exp 2 / 0.9607 * (1 - 0.9607)⁻¹

theorem mQ8_pos : 0 < mQ8 := by unfold mQ8; positivity

/-- 0 ≤ Q(s) ≤ 2 M h(s) for s ≥ 2. -/
theorem qBound_q8 (s : ℝ) (hs : 2 ≤ s) :
    0 ≤ oSumB8 s + eSumB8 s ∧
      oSumB8 s + eSumB8 s ≤ 2 * mQ8 * LeanLab.ChenExplicit.hSieve s := by
  have hO := paritySum_le_q8 Odd s (fun n h => Or.inl ⟨h, by linarith⟩) (by linarith)
  have hE := paritySum_le_q8 Even s (fun n h => Or.inr ⟨h, hs⟩) (by linarith)
  have hO0 := paritySum_nonneg_q8 Odd s (fun n h => Or.inl ⟨h, by linarith⟩)
  have hE0 := paritySum_nonneg_q8 Even s (fun n h => Or.inr ⟨h, hs⟩)
  unfold oSumB8 eSumB8
  unfold mQ8
  constructor <;> linarith

/-- t h(t) ≤ 3 e ^ -t for t ≥ 3. -/
theorem t_hSieve_le_q8 (t : ℝ) (ht : 3 ≤ t) :
    t * LeanLab.ChenExplicit.hSieve t ≤ 3 * exp (-t) := by
  unfold LeanLab.ChenExplicit.hSieve
  split_ifs with h1 h2
  · linarith
  · have : t = 3 := le_antisymm h2 ht
    subst this; have := exp_pos (-3 : ℝ); nlinarith
  · have htp : t ≠ 0 := by intro h; linarith
    rw [show t * (3 * t⁻¹ * exp (-t)) = 3 * exp (-t) * (t * t⁻¹) by ring,
      mul_inv_cancel₀ htp, mul_one]

/-- Twin of the LEAF `leafB8_IQ_tendsto` of `Split1122bBoundary8.lean`. -/
theorem leafB8_IQ_tendsto_twin : Filter.Tendsto qInvB8 Filter.atTop (nhds 0) := by
  have hM := mQ8_pos
  have hlim : Filter.Tendsto (fun s : ℝ => 6 * mQ8 * (s * exp (-s)) + 6 * mQ8 * exp 1 *
      exp (-s)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun s : ℝ => s * exp (-s)) Filter.atTop (nhds 0) := by
      simpa using tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero
    simpa using (h1.const_mul (6 * mQ8)).add (h2.const_mul (6 * mQ8 * exp 1))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop (4 : ℝ)] with s hs
  unfold qInvB8
  obtain ⟨hq0, hq1⟩ := qBound_q8 s (by linarith)
  have hth := t_hSieve_le_q8 s (by linarith)
  have hhs := hSieve_nonneg306 s (by linarith)
  -- first part
  have hA : ‖s * (s - 1) * (oSumB8 s + eSumB8 s)‖ ≤ 6 * mQ8 * (s * exp (-s)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hq0)]
    have e1 : s * (s - 1) * (oSumB8 s + eSumB8 s) ≤ s * s * (oSumB8 s + eSumB8 s) := by
      have : 0 ≤ s * (oSumB8 s + eSumB8 s) := by positivity
      nlinarith
    have e2 : s * s * (oSumB8 s + eSumB8 s) ≤ s * s * (2 * mQ8 * LeanLab.ChenExplicit.hSieve s) :=
      mul_le_mul_of_nonneg_left hq1 (by positivity)
    have e3 : s * s * (2 * mQ8 * LeanLab.ChenExplicit.hSieve s) =
        2 * mQ8 * s * (s * LeanLab.ChenExplicit.hSieve s) := by ring
    have e4 : 2 * mQ8 * s * (s * LeanLab.ChenExplicit.hSieve s) ≤ 2 * mQ8 * s * (3 * exp (-s)) :=
      mul_le_mul_of_nonneg_left hth (by positivity)
    nlinarith
  -- integral part
  have hB : ‖∫ t in (s - 1)..s, t * (oSumB8 t + eSumB8 t)‖ ≤ 6 * mQ8 * exp 1 * exp (-s) := by
    have hbd : ∀ t ∈ Set.uIoc (s - 1) s, ‖t * (oSumB8 t + eSumB8 t)‖ ≤
        6 * mQ8 * exp 1 * exp (-s) := by
      intro t ht
      rw [Set.uIoc_of_le (by linarith)] at ht
      obtain ⟨ht1, ht2⟩ := ht
      obtain ⟨p0, p1⟩ := qBound_q8 t (by linarith)
      have hth' := t_hSieve_le_q8 t (by linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) p0)]
      have e2 : t * (oSumB8 t + eSumB8 t) ≤ t * (2 * mQ8 * LeanLab.ChenExplicit.hSieve t) :=
        mul_le_mul_of_nonneg_left p1 (by linarith)
      have e4 : 2 * mQ8 * (t * LeanLab.ChenExplicit.hSieve t) ≤ 2 * mQ8 * (3 * exp (-t)) :=
        mul_le_mul_of_nonneg_left hth' (by positivity)
      have e5 : exp (-t) ≤ exp 1 * exp (-s) := by
        rw [← exp_add]; exact exp_le_exp.mpr (by linarith)
      nlinarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rw [show s - (s - 1) = (1 : ℝ) by ring, abs_one, mul_one] at this
    exact this
  calc ‖s * (s - 1) * (oSumB8 s + eSumB8 s) - ∫ t in (s - 1)..s, t * (oSumB8 t + eSumB8 t)‖
      ≤ ‖s * (s - 1) * (oSumB8 s + eSumB8 s)‖ +
          ‖∫ t in (s - 1)..s, t * (oSumB8 t + eSumB8 t)‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add hA hB

/-! ### Constancy of I on [3, ∞) -/

/-- g(t) = t Q(t). -/
def gQ8 (t : ℝ) : ℝ := t * (oSumB8 t + eSumB8 t)

/-- Displays 15 and 17: for 0 < t ≤ 3, t O(t) = 3 - t + 3 O(3). -/
theorem tO_low_q8 (t : ℝ) (ht0 : 0 < t) (ht : t ≤ 3) :
    t * oSumB8 t = 3 - t + 3 * oSumB8 3 := by
  have htp : t ≠ 0 := ne_of_gt ht0
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
    (parity_summableB8 Odd 3 (fun n h => Or.inl ⟨h, by norm_num⟩) (by norm_num)).mul_left 3
  unfold oSumB8
  rw [← tsum_mul_left]
  simp_rw [hterm]
  rw [hs1.tsum_add hs2, tsum_ite_eq, tsum_mul_left]

/-- t O(t) is continuous on t > 2. -/
theorem tO_cont_q8 : ContinuousOn (fun t => t * oSumB8 t) (Set.Ioi 2) := by
  intro x hx
  have hx2 : (2 : ℝ) < x := hx
  apply ContinuousAt.continuousWithinAt
  rcases lt_trichotomy x 3 with h | h | h
  · have hc : ContinuousAt (fun t : ℝ => 3 - t + 3 * oSumB8 3) x := by fun_prop
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < x by linarith) h] with t ht
    exact tO_low_q8 t ht.1 ht.2.le
  · subst h
    have hR : ContinuousWithinAt (fun t => t * oSumB8 t) (Set.Ici 3) 3 :=
      leaf8_deriv_odd_twin.2.continuousWithinAt
    have hL : ContinuousWithinAt (fun t => t * oSumB8 t) (Set.Iic 3) 3 := by
      have hc : ContinuousWithinAt (fun t : ℝ => 3 - t + 3 * oSumB8 3) (Set.Iic 3) 3 :=
        (by fun_prop : Continuous (fun t : ℝ => 3 - t + 3 * oSumB8 3)).continuousWithinAt
      refine hc.congr_of_eventuallyEq ?_ (tO_low_q8 3 (by norm_num) le_rfl)
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Ioi_mem_nhds (show (0 : ℝ) < 3 by norm_num))] with t ht ht0
      exact tO_low_q8 t ht0 ht
    have := hL.union hR
    rwa [Set.Iic_union_Ici, continuousWithinAt_univ] at this
  · exact (leaf8_deriv_odd_twin.1 x h).continuousAt

/-- g is continuous on t > 2. -/
theorem gQ8_cont : ContinuousOn gQ8 (Set.Ioi 2) := by
  have hE : ContinuousOn (fun t => t * eSumB8 t) (Set.Ioi 2) := fun x hx =>
    (leaf8_deriv_even_twin x hx).continuousAt.continuousWithinAt
  have := tO_cont_q8.add hE
  refine this.congr (fun t _ => ?_)
  simp only [gQ8, Pi.add_apply]; ring

/-- (s Q(s))' = - Q(s - 1) for s > 3. -/
theorem gQ8_deriv (s : ℝ) (hs : 3 < s) :
    HasDerivAt gQ8 (-(oSumB8 (s - 1) + eSumB8 (s - 1))) s := by
  have hO : HasDerivAt (fun t => t * oSumB8 t) (-eSumB8 (s - 1)) s :=
    leaf8_deriv_odd_twin.1 s hs
  have hE : HasDerivAt (fun t => t * eSumB8 t) (-oSumB8 (s - 1)) s :=
    leaf8_deriv_even_twin s (by linarith)
  have := hO.add hE
  convert this using 1
  · funext t; simp only [gQ8, Pi.add_apply]; ring
  · ring

/-- g is interval integrable on [2, b]: continuous on (2, b] and bounded there. -/
theorem gQ8_int (b : ℝ) (hb : 2 ≤ b) : IntervalIntegrable gQ8 MeasureTheory.volume 2 b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
  have hcont : ContinuousOn gQ8 (Set.Ioc 2 b) := gQ8_cont.mono Set.Ioc_subset_Ioi_self
  refine ⟨hcont.aestronglyMeasurable measurableSet_Ioc,
    MeasureTheory.HasFiniteIntegral.restrict_of_bounded (C := b * (2 * mQ8 * exp (-2)))
      measure_Ioc_lt_top ?_⟩
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨p0, p1⟩ := qBound_q8 t ht1.le
  have hh := hSieve_le_d8 t
  have hM := mQ8_pos
  have p2 : oSumB8 t + eSumB8 t ≤ 2 * mQ8 * exp (-2) := by
    have := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * mQ8)
    linarith
  simp only [gQ8]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) p0)]
  have e1 : t * (oSumB8 t + eSumB8 t) ≤ t * (2 * mQ8 * exp (-2)) :=
    mul_le_mul_of_nonneg_left p2 (by linarith)
  have e2 : t * (2 * mQ8 * exp (-2)) ≤ b * (2 * mQ8 * exp (-2)) :=
    mul_le_mul_of_nonneg_right ht2 (by positivity)
  linarith

/-- The primitive G(x) = ∫ over [2, x] of g. -/
def GQ8 (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, gQ8 t

theorem GQ8_cont (b : ℝ) (hb : 2 ≤ b) : ContinuousOn GQ8 (Set.Icc 2 b) := by
  have h := intervalIntegral.continuousOn_primitive_interval' (gQ8_int b hb)
    (Set.left_mem_uIcc)
  rw [Set.uIcc_of_le hb] at h
  exact h

theorem GQ8_deriv (x : ℝ) (hx : 2 < x) : HasDerivAt GQ8 (gQ8 x) x := by
  have hmeas := gQ8_cont.stronglyMeasurableAtFilter (μ := MeasureTheory.volume) isOpen_Ioi x hx
  exact intervalIntegral.integral_hasDerivAt_right (gQ8_int x hx.le) hmeas
    (gQ8_cont.continuousAt (Ioi_mem_nhds hx))

/-- Φ(s) = (s - 1) g(s) - (G(s) - G(s - 1)). -/
def PhiQ8 (s : ℝ) : ℝ := (s - 1) * gQ8 s - (GQ8 s - GQ8 (s - 1))

theorem qInv_eq_Phi_q8 (s : ℝ) (hs : 3 ≤ s) : qInvB8 s = PhiQ8 s := by
  unfold qInvB8 PhiQ8 GQ8
  rw [intervalIntegral.integral_interval_sub_left (gQ8_int s (by linarith))
    (gQ8_int (s - 1) (by linarith))]
  simp only [gQ8]; ring

theorem Phi_deriv_q8 (s : ℝ) (hs : 3 < s) : HasDerivAt PhiQ8 0 s := by
  have h1 := ((hasDerivAt_id s).sub_const 1).mul (gQ8_deriv s hs)
  have h2 := GQ8_deriv s (by linarith)
  have h3 : HasDerivAt (fun x => GQ8 (x - 1)) (gQ8 (s - 1)) s := by
    have := (GQ8_deriv (s - 1) (by linarith)).comp s ((hasDerivAt_id' s).sub_const 1)
    rw [mul_one] at this
    exact this
  have := h1.sub (h2.sub h3)
  convert this using 1
  · funext x; simp only [PhiQ8, Pi.sub_apply, Pi.mul_apply, id]
  · simp only [id, gQ8]; ring

theorem Phi_cont_q8 (b : ℝ) (hb : 3 ≤ b) : ContinuousOn PhiQ8 (Set.Icc 3 b) := by
  have hg : ContinuousOn gQ8 (Set.Icc 3 b) :=
    gQ8_cont.mono (fun x hx => by have : (3 : ℝ) ≤ x := hx.1; show (2 : ℝ) < x; linarith)
  have hG : ContinuousOn GQ8 (Set.Icc 3 b) :=
    (GQ8_cont b (by linarith)).mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
  have hG1 : ContinuousOn (fun x => GQ8 (x - 1)) (Set.Icc 3 b) := by
    refine (GQ8_cont b (by linarith)).comp (continuousOn_id.sub continuousOn_const) ?_
    intro x hx
    exact ⟨by simp only [id]; linarith [hx.1], by simp only [id]; linarith [hx.2]⟩
  unfold PhiQ8
  exact ((continuousOn_id.sub continuousOn_const).mul hg).sub (hG.sub hG1)

/-- Twin of the LEAF `leafB8_IQ_const` of `Split1122bBoundary8.lean`. -/
theorem leafB8_IQ_const_twin (s : ℝ) (hs : 3 ≤ s) : qInvB8 s = qInvB8 3 := by
  rw [qInv_eq_Phi_q8 s hs, qInv_eq_Phi_q8 3 le_rfl]
  rcases hs.lt_or_eq with h | h
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope PhiQ8 (fun _ => (0 : ℝ)) h
      (Phi_cont_q8 s hs) (fun x hx => Phi_deriv_q8 x hx.1)
    have hne : s - 3 ≠ 0 := by linarith
    have := hcd.symm
    rw [div_eq_zero_iff] at this
    rcases this with h0 | h0
    · linarith
    · exact absurd h0 hne
  · rw [h]

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leafB8_IQ_tendsto_twin
#print axioms LeanLab.Cai2002.leafB8_IQ_const_twin
