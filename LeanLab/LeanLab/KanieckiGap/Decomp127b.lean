/-
P0022, pages 371 to 373. Complete the guarded interval proof at real starting
points through the real paper cutoff. The late range generalizes the existing
Kaniecki1995.L5.range34G proof, which only uses real inequalities internally.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.KanieckiGap.Guarded127
import LeanLab.KanieckiGap.RealIntervals127

namespace LeanLab.KanieckiGap.Decomp127b

open LeanLab.Kaniecki1995 LeanLab.Kaniecki1995.L5 Real MeasureTheory

/-- LEAF. Pages 372 and 373, displays 23 to 27. The guarded measure and
numerical argument applies to every real starting point in the late range.
CONDITIONAL ON RH, guarded Lemma 5 and the displayed measure bound. -/
theorem large_real_range (hRH : RiemannHypothesis) (h5 : Lemma5G) (h23 : Eq23) (x : ℝ)
    (hx1 : Real.exp 78.5 < (x : ℝ)) (hx2 : (x : ℝ) ≤ n0) : HasOddPairSumIn x 1.4045e12 := by
  by_contra hno
  set X : ℝ := (x : ℝ) with hXdef
  have hX0 : 0 < X := lt_trans (Real.exp_pos _) hx1
  have hX1 : 1 < X := lt_trans (by
    have : (1 : ℝ) < Real.exp 78.5 := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by norm_num)
    exact this) hx1
  set L := Real.log X with hLdef
  have hL1 : 78.5 < L := (Real.lt_log_iff_exp_lt hX0).2 hx1
  have hL2 : L ≤ Real.exp 11.503 := (Real.log_le_iff_le_exp hX0).2 (by simpa [n0] using hx2)
  set T := 2 * X / 1.4045e12 with hTdef
  have hT0 : 0 < T := by positivity
  have hlogT : Real.log T = L - Real.log (1.4045e12 / 2) := by
    rw [hTdef, show 2 * X / 1.4045e12 = X / (1.4045e12 / 2) by ring,
      Real.log_div hX0.ne' (by norm_num)]
  obtain ⟨kk1, kk2⟩ := kk_bounds
  have hlogT51 : 51 ≤ Real.log T := by rw [hlogT]; linarith
  have hTexp : Real.exp 51 ≤ T := by rw [← Real.exp_log hT0]; exact Real.exp_le_exp.2 hlogT51
  have hT1 : 1 < T := by linarith [exp51_ge]
  have hT702 : 7.02 < T := by linarith [exp51_ge]
  obtain ⟨hs0, hs1, _⟩ := sig_facts (le_refl 51) hTexp
  have hHle : (1.4045e12 : ℝ) ≤ 2 * Real.exp (-12) * X := by
    have : Real.exp 51 ≤ Real.exp (-12) * X := by
      have h1 : Real.exp 51 * Real.exp 12 ≤ X := by
        rw [← Real.exp_add]; exact le_trans (Real.exp_le_exp.2 (by norm_num)) hx1.le
      rw [Real.exp_neg]
      rw [le_inv_mul_iff₀ (Real.exp_pos _)]; linarith [mul_comm (Real.exp 51) (Real.exp 12)]
    linarith [exp51_ge]
  have hlow := h23 X 1.4045e12 aK cK (by norm_num) hHle (by norm_num [aK]) (by norm_num [aK])
    (by norm_num [cK]) (by norm_num [cK]) hno
  have hJI : JInt (2 * X / 1.4045e12) (sig aK cK (2 * X / 1.4045e12)) ≤
      IInt (2 * X / 1.4045e12) (sig aK cK (2 * X / 1.4045e12)) :=
    lintegral_mono_set (Set.Ioi_subset_Ioi (by norm_num))
  have hpos : 0 < Real.log T ^ 2 / T := by positivity
  rcases le_or_gt L 84000 with hL84 | hL84
  · have hI := h5 hRH aK cK T 1.07 hT702 (by norm_num [cK]) (by norm_num) (by norm_num [aK])
      (by linarith) guardK
    have hJc := Jconst_set1 (le_refl 51) hTexp
    set U := 1 / π * (√(fK aK cK T 1.07) + √(f6 aK cK T) + √(f7 aK cK T)) ^ 2 *
      Real.log T ^ 2 / T with hU
    have hU0 : 0 ≤ U := by
      rw [hU, mul_div_assoc]; exact mul_nonneg (by have := Real.pi_pos; positivity) hpos.le
    have hlowU := (ENNReal.ofReal_le_ofReal_iff hU0).1 (hlow.trans (hJI.trans hI))
    have hUK : U < 0.271 * Real.log T ^ 2 / T := by
      rw [hU, mul_div_assoc, mul_div_assoc]; exact mul_lt_mul_of_pos_right hJc hpos
    have h25 := eq25 hX1 (by norm_num) hT1 hlowU hUK
    rw [← hTdef, hlogT] at h25
    have := a2_range3 kk1 kk2 hL1.le hL84
    linarith
  · have hlogT4 : 83970 ≤ Real.log T := by rw [hlogT]; linarith
    have hTexp4 : Real.exp 83970 ≤ T := by
      rw [← Real.exp_log hT0]; exact Real.exp_le_exp.2 hlogT4
    have hI := h5 hRH aK cK T 1.00013 hT702 (by norm_num [cK]) (by norm_num) (by norm_num [aK])
      (by linarith) guardK
    have hJc := Jconst_set2 hTexp4
    set U := 1 / π * (√(fK aK cK T 1.00013) + √(f6 aK cK T) + √(f7 aK cK T)) ^ 2 *
      Real.log T ^ 2 / T with hU
    have hU0 : 0 ≤ U := by
      rw [hU, mul_div_assoc]; exact mul_nonneg (by have := Real.pi_pos; positivity) hpos.le
    have hlowU := (ENNReal.ofReal_le_ofReal_iff hU0).1 (hlow.trans (hJI.trans hI))
    have hUK : U < 0.1973261 * Real.log T ^ 2 / T := by
      rw [hU, mul_div_assoc, mul_div_assoc]; exact mul_lt_mul_of_pos_right hJc hpos
    have h25 := eq25 hX1 (by norm_num) hT1 hlowU hUK
    rw [← hTdef, hlogT] at h25
    have := a3_range4 kk1 kk2 hL84.le hL2
    linarith

/-- LEAF. Page 371. The first range extends to real starts by a ceiling.
The proved width 18 leaves ample room inside the paper width.
CONDITIONAL ON Young-Potler. -/
theorem small_real_range (hY : KanieckiGap.YoungPotler) (x : ℝ)
    (hx0 : 0 ≤ x) (hxN : x ≤ 72630000000000) : HasOddPairSumIn x 1.4045e12 := by
  obtain ⟨p, q, hp, hq, op, oq, hlo, hhi⟩ := LeanLab.Kaniecki1995.range1
    (EndpointTransfer127.paper_of_right hY) ⌈x⌉₊ (Nat.ceil_le.mpr hxN)
  refine ⟨p, q, hp, hq, op, oq, ?_, ?_⟩
  · have : (⌈x⌉₊ : ℝ) ≤ ((p + q : ℕ) : ℝ) := by exact_mod_cast hlo
    exact (Nat.le_ceil x).trans this
  · have : ((p + q : ℕ) : ℝ) ≤ (⌈x⌉₊ : ℝ) + 18 := by exact_mod_cast hhi
    linarith [Nat.ceil_lt_add_one hx0]

/-- LEAF. Page 371, the second nested gap estimate. Apply Lemma 6 at x and
at lambda x, or the finite table when the latter is small.
CONDITIONAL ON RH, Schoenfeld61 and Young-Potler. -/
theorem nested_gap_middle (hRH : RiemannHypothesis)
    (hS : LeanLab.DERZ1997.Schoenfeld61) (hY : KanieckiGap.YoungPotler)
    (x : ℝ) (hxN : 72630000000000 < x) (hxE : x ≤ Real.exp 78.5) :
    (LeanLab.Kaniecki1995.lam (LeanLab.Kaniecki1995.lam x) : ℝ) ≤ 1.22e12 := by
  have h6 := Decomp127.lemma6_real hS hY
  have hfirst := h6 hRH x (by linarith)
  have hbound : gL6 x ≤ 5.4599e19 :=
    (LeanLab.Kaniecki1995.gL6_mono (by linarith) hxE).trans a1_gL6_e785
  have hlambda : (LeanLab.Kaniecki1995.lam x : ℝ) ≤ 5.46e19 := by linarith
  by_cases hs : (LeanLab.Kaniecki1995.lam x : ℝ) ≤ 2.3e9
  · have hmono := RealIntervals127.lam_mono
      (show (LeanLab.Kaniecki1995.lam x : ℝ) ≤ 72630000000000 by linarith)
    have htable := EndpointTransfer127.paper_of_right hY
    unfold LeanLab.Kaniecki1995.YoungPotler at htable
    have hmR : (LeanLab.Kaniecki1995.lam (LeanLab.Kaniecki1995.lam x) : ℝ) ≤
        (LeanLab.Kaniecki1995.lam 72630000000000 : ℝ) := by exact_mod_cast hmono
    have : (LeanLab.Kaniecki1995.lam (LeanLab.Kaniecki1995.lam x) : ℝ) ≤ 778 :=
      hmR.trans htable
    linarith
  · have hsecond := h6 hRH (LeanLab.Kaniecki1995.lam x) (by linarith)
    have hupper : gL6 (LeanLab.Kaniecki1995.lam x) ≤ 1.22e12 :=
      (LeanLab.Kaniecki1995.gL6_mono (by linarith) hlambda).trans a1_gL6_546
    linarith

/-- LEAF. Page 371. Corrected Lemma 7 and the preceding nested bound give
the real middle interval. CONDITIONAL ON RH, Schoenfeld61 and Young-Potler. -/
theorem middle_real_range (hRH : RiemannHypothesis)
    (hS : LeanLab.DERZ1997.Schoenfeld61) (hY : KanieckiGap.YoungPotler)
    (x : ℝ) (hxN : 72630000000000 < x) (hxE : x ≤ Real.exp 78.5) :
    HasOddPairSumIn x 1.4045e12 := by
  obtain ⟨p, q, hp, op, hq, oq, hlo, hhi⟩ :=
    RealIntervals127.lemma7_closed_real x (by linarith)
  have hgap := nested_gap_middle hRH hS hY x hxN hxE
  exact ⟨p, q, hp, hq, op, oq, hlo.le, by linarith⟩

/-- Page 373. The full real interval statement, including the part between
floor n0 and n0. The assembly has no admitted step. CONDITIONAL ON RH,
guarded Lemma 5, Schoenfeld61 and Young-Potler. -/
theorem real_interval_from_guarded (hRH : RiemannHypothesis)
    (h5 : LeanLab.Kaniecki1995.L5.Lemma5G) (hS : LeanLab.DERZ1997.Schoenfeld61)
    (hY : KanieckiGap.YoungPotler) :
    ∀ x : ℝ, 0 ≤ x → x ≤ n0 → HasOddPairSumIn x 1.4045e12 := by
  intro x hx0 hxN
  by_cases hs : x ≤ 72630000000000
  · exact small_real_range hY x hx0 hs
  · by_cases hm : x ≤ Real.exp 78.5
    · exact middle_real_range hRH hS hY x (lt_of_not_ge hs) hm
    · exact large_real_range hRH h5 LeanLab.Kaniecki1995.eq23 x (lt_of_not_ge hm) hxN

end LeanLab.KanieckiGap.Decomp127b

#print axioms LeanLab.KanieckiGap.Decomp127b.large_real_range
#print axioms LeanLab.KanieckiGap.Decomp127b.small_real_range
#print axioms LeanLab.KanieckiGap.Decomp127b.nested_gap_middle
#print axioms LeanLab.KanieckiGap.Decomp127b.middle_real_range
#print axioms LeanLab.KanieckiGap.Decomp127b.real_interval_from_guarded
