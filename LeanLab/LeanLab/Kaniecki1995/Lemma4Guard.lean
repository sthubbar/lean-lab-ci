/-
P0022, Kaniecki 1995. CLOUD 20261020T2317Z-cloud53, unit U-6765, T1.

QUESTION, p. 364: Lemma 4 is stated for every `a > 1, c > 0`, but its proof applies Lemma 3,
p. 363, which assumes `e^{-c} + e^{-ac} < (a - 1) c`; Lemma 4 and Lemma 5 do not carry this
condition, and at `(a - 1) c = e^{-c} + e^{-ac}` the factor `f₅` divides by zero. In Lean that
division gives `f₅ = 0`, so `Statements.Lemma4` and `Statements.Lemma5` then claim a bound with
`f = f₁` only, which a mpmath check suggests is false, see PROGRESS.md U-6765. Then every
theorem CONDITIONAL ON `Lemma4` or `Lemma5` would rest on a false hypothesis.
This file states `Lemma4G` and `Lemma5G` with Lemma 3's condition added, the faithful reading,
proves `Lemma5G` from `Lemma4G` and the named inputs of Lemma 5, checks the condition at the
Section 3 parameters `a = 1.96745, c = 1.32149` in `guardK`, and reruns the Section 3 assembly of
Reduction.lean, copied with only `Lemma5` replaced by `Lemma5G`, since Section 3 uses Lemma 5
only at those parameters.
AI wrote this Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Kaniecki1995.Lemma5Bound22
import LeanLab.Kaniecki1995.Lemma6Trudgian

namespace LeanLab.Kaniecki1995.L5

open LeanLab.Kaniecki1995 Real MeasureTheory

/-- Lemma 4, pp. 364-365, inequality (8), with Lemma 3's condition `e^{-c} + e^{-ac} < (a-1)c`. -/
def Lemma4G : Prop :=
  RiemannHypothesis → ∀ a c T α : ℝ, 7.02 < T → 0 < c → 1 < α → 1 < a → sig a c T ≤ 3 / 4 →
    Real.exp (-c) + Real.exp (-(a * c)) < (a - 1) * c →
    lemma4Int T (sig a c T) ≤ ENNReal.ofReal (fK a c T α * Real.log T ^ 2 / T)

/-- Lemma 5, p. 368, inequality (17), with the same condition. -/
def Lemma5G : Prop :=
  RiemannHypothesis → ∀ a c T α : ℝ, 7.02 < T → 0 < c → 1 < α → 1 < a → sig a c T ≤ 3 / 4 →
    Real.exp (-c) + Real.exp (-(a * c)) < (a - 1) * c →
    IInt T (sig a c T) ≤ ENNReal.ofReal
      (1 / π * (√(fK a c T α) + √(f6 a c T) + √(f7 a c T)) ^ 2 * Real.log T ^ 2 / T)

/-- the guarded forms are weaker than the printed ones -/
theorem lemma4G_of_lemma4 (h4 : Lemma4) : Lemma4G :=
  fun hRH a c T α hT hc hα ha hs _ => h4 hRH a c T α hT hc hα ha hs

theorem lemma5G_of_lemma5 (h5 : Lemma5) : Lemma5G :=
  fun hRH a c T α hT hc hα ha hs _ => h5 hRH a c T α hT hc hα ha hs

/-- Lemma 3's condition at the Section 3 parameters, p. 372: `e^{-c} + e^{-ac} < (a-1)c`. -/
theorem guardK : Real.exp (-cK) + Real.exp (-(aK * cK)) < (aK - 1) * cK := by
  have h1 : Real.exp (-cK) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by norm_num [cK])
  have h2 : Real.exp (-(aK * cK)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by norm_num [aK, cK])
  have h3 := Real.exp_neg_one_lt_d9
  have : (1.2 : ℝ) < (aK - 1) * cK := by norm_num [aK, cK]
  linarith

/-- **Lemma 5, guarded**, CONDITIONAL ON `Lemma4G`, `Parseval1920` under RH, `Bound21`,
`Bound22`. -/
theorem lemma5G_of (h4 : Lemma4G) (hP : Parseval1920) (h21 : Bound21) (h22 : Bound22) :
    Lemma5G := fun hRH a c T α hT hc hα ha hs hg =>
  lemma5_at hRH hP h21 h22 hT hc ha hs (h4 hRH a c T α hT hc hα ha hs hg)

/-! ### Section 3 assembly with `Lemma5G`, copied from Reduction.lean -/

theorem range34G (hRH : RiemannHypothesis) (h5 : Lemma5G) (h23 : Eq23) (x : ℕ)
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

theorem interval_ofG (hRH : RiemannHypothesis) (h5 : Lemma5G) (h23 : Eq23) (h6 : Lemma6)
    (hYP : YoungPotler) : IntervalProperty := by
  intro x hx
  rcases Nat.lt_or_ge 72630000000000 x with h1 | h1
  · by_cases h2 : (x : ℝ) ≤ Real.exp 78.5
    · exact range2 hRH h6 hYP x h1 h2
    · push Not at h2
      obtain ⟨p, q, hp, hq, hop, hoq, hlo, hhi⟩ := range34G hRH h5 h23 x h2 hx
      refine ⟨p, q, hp, hq, hop, hoq, by exact_mod_cast hlo, ?_⟩
      have : ((p + q : ℕ) : ℝ) ≤ ((x + 1404500000000 : ℕ) : ℝ) := by push_cast at hhi ⊢; linarith
      exact_mod_cast this
  · obtain ⟨p, q, hp, hq, hop, hoq, hlo, hhi⟩ := range1 hYP x h1
    exact ⟨p, q, hp, hq, hop, hoq, hlo, by omega⟩

theorem theoremOdd_ofG (h5 : Lemma5G) (h23 : Eq23) (h6 : Lemma6) (hYP : YoungPotler)
    (hS : Sinisalo) (hCW : ChenWang) : TheoremOdd :=
  fun hRH => odd_of_interval (interval_ofG hRH h5 h23 h6 hYP) hCW hYP hS

/-- The Theorem, even part, p. 362: CONDITIONAL on Lemma 5, (23), Lemma 6, [16], [1]. -/
theorem theoremEven_ofG (h5 : Lemma5G) (h23 : Eq23) (h6 : Lemma6) (hYP : YoungPotler)
    (hCW : ChenWang) : TheoremEven :=
  fun hRH hG => even_of_interval (interval_ofG hRH h5 h23 h6 hYP) hCW hG

theorem remark_ofG (h5 : Lemma5G) (h23 : Eq23) : RemarkStatement := by
  intro hRH x hx
  by_contra hno
  have hX0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  set L := Real.log x with hLdef
  have hL : 84000 ≤ L := (Real.le_log_iff_exp_le hX0).2 hx
  have hX1 : 1 < x := by
    have : (1 : ℝ) < Real.exp 84000 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by norm_num)
    linarith
  set h := 144 * L ^ 2 with hhdef
  have hh0 : 0 < h := by positivity
  obtain ⟨hM, hR⟩ := p373_remark_num hL
  set T := 2 * x / h with hTdef
  have hT0 : 0 < T := by positivity
  have hlogT : Real.log T = L + Real.log 2 - Real.log h := by
    rw [hTdef, Real.log_div (by positivity) hh0.ne', Real.log_mul (by norm_num) hX0.ne']; ring
  have hTexp4 : Real.exp 83970 ≤ T := by
    rw [← Real.exp_log hT0]; exact Real.exp_le_exp.2 (by rw [hlogT]; exact hM)
  have hTexp : Real.exp 51 ≤ T := (Real.exp_le_exp.2 (by norm_num)).trans hTexp4
  have hT1 : 1 < T := by linarith [exp51_ge]
  have hT702 : 7.02 < T := by linarith [exp51_ge]
  obtain ⟨hs0, hs1, _⟩ := sig_facts (le_refl 51) hTexp
  have hh7 : (7 : ℝ) ≤ h := by rw [hhdef]; nlinarith
  have hHle : h ≤ 2 * Real.exp (-12) * x := by
    have h1 : Real.exp 12 ≤ T := (Real.exp_le_exp.2 (by norm_num)).trans hTexp4
    have h2 : h * T = 2 * x := by rw [hTdef]; field_simp
    have h3 : h * Real.exp 12 ≤ 2 * x := by rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hh0.le
    rw [Real.exp_neg, mul_comm 2, mul_assoc, le_inv_mul_iff₀ (Real.exp_pos _)]
    linarith
  have hlow := h23 x h aK cK hh7 hHle (by norm_num [aK]) (by norm_num [aK])
    (by norm_num [cK]) (by norm_num [cK]) hno
  have hJI : JInt (2 * x / h) (sig aK cK (2 * x / h)) ≤ IInt (2 * x / h) (sig aK cK (2 * x / h)) :=
    lintegral_mono_set (Set.Ioi_subset_Ioi (by norm_num))
  have hpos : 0 < Real.log T ^ 2 / T := by
    have : 0 < Real.log T := by rw [hlogT]; linarith
    positivity
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
  have h25 := eq25 hX1 hh0 hT1 hlowU hUK
  rw [← hTdef, hlogT] at h25
  linarith


/-- **The Remark, p. 373**, CONDITIONAL ON `Lemma4G` and the four named inputs of Lemma 5. -/
theorem remark_of_lemma4G (h4 : Lemma4G) (hP : Parseval1920) (h21 : Bound21) (hK : Kernel9)
    (hC : Const451) : RemarkStatement :=
  remark_ofG (lemma5G_of h4 hP h21 (bound22_of hK hC)) eq23

/-- **Theorem, odd part, p. 362**, CONDITIONAL ON `Lemma4G`, the four named inputs of Lemma 5,
the three Dudek chain inputs of Lemma 6, Young-Potler, Sinisalo and Chen-Wang. -/
theorem theoremOdd_of_lemma4G (h4 : Lemma4G) (hP : Parseval1920) (h21 : Bound21)
    (hK : Kernel9) (hC : Const451)
    (hN : LeanLab.Dudek2014.SigmaT.TrudgianN70 LeanLab.PNTPort.ExplicitPsi1.Trivial.gZ)
    (hSch : LeanLab.Dudek2014.Section22.Schoenfeld)
    (hG : LeanLab.GoldbachGaps.Sumset.GapBound1476) (hYP : YoungPotler) (hS : Sinisalo)
    (hCW : ChenWang) : TheoremOdd :=
  theoremOdd_ofG (lemma5G_of h4 hP h21 (bound22_of hK hC)) eq23
    (L6T.lemma6_of_trudgian hN hSch hG) hYP hS hCW

/-- **Theorem, even part, p. 362**, CONDITIONAL ON `Lemma4G`, the four named inputs of Lemma 5,
the three Dudek chain inputs of Lemma 6, Young-Potler and Chen-Wang. -/
theorem theoremEven_of_lemma4G (h4 : Lemma4G) (hP : Parseval1920) (h21 : Bound21)
    (hK : Kernel9) (hC : Const451)
    (hN : LeanLab.Dudek2014.SigmaT.TrudgianN70 LeanLab.PNTPort.ExplicitPsi1.Trivial.gZ)
    (hSch : LeanLab.Dudek2014.Section22.Schoenfeld)
    (hG : LeanLab.GoldbachGaps.Sumset.GapBound1476) (hYP : YoungPotler) (hCW : ChenWang) :
    TheoremEven :=
  theoremEven_ofG (lemma5G_of h4 hP h21 (bound22_of hK hC)) eq23
    (L6T.lemma6_of_trudgian hN hSch hG) hYP hCW

end LeanLab.Kaniecki1995.L5

#print axioms LeanLab.Kaniecki1995.L5.guardK
#print axioms LeanLab.Kaniecki1995.L5.lemma5G_of
#print axioms LeanLab.Kaniecki1995.L5.range34G
#print axioms LeanLab.Kaniecki1995.L5.interval_ofG
#print axioms LeanLab.Kaniecki1995.L5.theoremOdd_ofG
#print axioms LeanLab.Kaniecki1995.L5.theoremEven_ofG
#print axioms LeanLab.Kaniecki1995.L5.remark_ofG
#print axioms LeanLab.Kaniecki1995.L5.remark_of_lemma4G
#print axioms LeanLab.Kaniecki1995.L5.theoremOdd_of_lemma4G
#print axioms LeanLab.Kaniecki1995.L5.theoremEven_of_lemma4G

