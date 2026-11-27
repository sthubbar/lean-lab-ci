import LeanLab.Halupczok2012.Statements
import LeanLab.Halupczok2012.Fourier398
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
Leaves for `kawada_thm22_display24`, Halupczok journal pages 338 to 339, Theorem 2.2,
display 2.4, adapted from Kawada 1993 Theorem 2, sections 3 to 6.
https://doi.org/10.5802/jtnb.839

The adapted circle method of Kawada is cut into three pieces:
the circle method identity, the minor arc estimate of Kawada section 4 with
display 3.5 and 3.6, and the major arc estimate of Kawada displays 3.7 to 3.14.
The assembly `kawada_thm22_display24_of_leaves` is proved here sorry free.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp598Theorem6LeavesKawada

open Finset MeasureTheory
open scoped Classical

/-- Kawada page 45: `e(α) = exp(2πiα)`. -/
noncomputable def eA (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- The `p2` exponential sum, Kawada page 45 `P_{aq}` adapted as on Halupczok page 338:
`∑_{X2 < p ≤ X2+Y, p ≡ a2 (q2)} log p e(pα)`, with the logarithmic prime weight of display 2.4. -/
noncomputable def P2 (X2 Y : ℝ) (q2 : ℕ) (a2 : ℤ) (α : ℝ) : ℂ :=
  ∑ p ∈ (range (⌊X2 + Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ X2 < p ∧ (p : ℝ) ≤ X2 + Y ∧
      (p : ℤ) ≡ a2 [ZMOD q2]),
    (Real.log p : ℂ) * eA (p * α)

/-- The `p3` exponential sum over the window of Halupczok page 339,
`∑_{2X1 - X2 - Y < p ≤ 2X1 + 2Y - X2} log p e(pα)`; Kawada page 45 `P(α)` adapted. -/
noncomputable def P3 (X1 X2 Y : ℝ) (α : ℝ) : ℂ :=
  ∑ p ∈ (range (⌊2 * X1 + 2 * Y - X2⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
      2 * X1 - X2 - Y < p ∧ (p : ℝ) ≤ 2 * X1 + 2 * Y - X2),
    (Real.log p : ℂ) * eA (p * α)

/-- The integrand of Kawada display 3.4 for `k = 2`, `b1 = m`. -/
noncomputable def circF (X1 X2 Y : ℝ) (q2 : ℕ) (a2 : ℤ) (m : ℕ) (α : ℝ) : ℂ :=
  P2 X2 Y q2 a2 α * P3 X1 X2 Y α * eA (-(m : ℝ) * α)

/-- Kawada page 45: the unit interval `[x^{-1/6}, 1 + x^{-1/6}]`, here with `x = X1`. -/
noncomputable def unitDom (X1 : ℝ) : Set ℝ :=
  Set.Icc (X1 ^ (-(1 / 6) : ℝ)) (1 + X1 ^ (-(1 / 6) : ℝ))

/-- Kawada page 45 major arcs `M = ⋃_{q ≤ Q1} ⋃_{(c,q)=1} [c/q - Δ, c/q + Δ]`. -/
noncomputable def majorArcs (Q1 Δ : ℝ) : Set ℝ :=
  ⋃ q ∈ Icc 1 ⌊Q1⌋₊, ⋃ c ∈ (Icc 1 q).filter (fun c => Nat.Coprime c q),
    Set.Icc ((c : ℝ) / q - Δ) ((c : ℝ) / q + Δ)

/-- Kawada page 46 parameters for `k = 2`, with `L = log Y`:
`Q1 = L^C` and `Δ = Y^{-1} L^{2A + 2C + 2}`. -/
noncomputable def kMajor (A C Y : ℝ) : Set ℝ :=
  majorArcs (Real.log Y ^ C) (Y⁻¹ * Real.log Y ^ (2 * A + 2 * C + 2))

/-- LEAF: circle method identity, Kawada display 3.4 for k = 2 with the p3 window of
Halupczok page 339. Class MEDIUM. P0077 page 338 display 2.4, Kawada 1993 page 47.
Orthogonality of e(nα) on a unit interval; X2 ≤ 2X1 - Y puts every p3 = 2k - p2 in the window. -/
theorem leaf_circle_identity (X1 X2 Y : ℝ) (q2 : ℕ) (a2 : ℤ) (k : ℕ)
    (hY : 0 < Y) (hX2 : X2 ≤ 2 * X1 - Y) (hk : k ∈ kRange X1 Y) :
    (binSumAP X2 Y q2 a2 (2 * k) : ℂ) =
      ∫ α in unitDom X1, circF X1 X2 Y q2 a2 (2 * k) α := by
  have hkw := (Fourier398.window_mem X1 Y k).mp hk
  let U := (range (⌊X2 + Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ X2 < p ∧
    (p : ℝ) ≤ X2 + Y ∧ (p : ℤ) ≡ a2 [ZMOD q2])
  let V := (range (⌊2 * X1 + 2 * Y - X2⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
    2 * X1 - X2 - Y < p ∧ (p : ℝ) ≤ 2 * X1 + 2 * Y - X2)
  let w := fun p : ℕ => (Real.log p : ℂ)
  have hphase (t : ℝ) : eA t = Decomp398a.phase t := by
    unfold eA Decomp398a.phase LeanLab.PNTPort.LargeSieve.e
    congr 1
    push_cast
    ring
  have hint : (∫ α in unitDom X1, circF X1 X2 Y q2 a2 (2 * k) α) =
      ∑ p ∈ U, ∑ j ∈ V, if p + j = 2 * k then w p * w j else 0 := by
    unfold circF P2 P3 unitDom
    simp_rw [hphase]
    rw [add_comm 1 (X1 ^ (-(1 / 6) : ℝ))]
    exact Fourier398.finite_convolution U V w w (2 * k) _
  have hinner : ∀ p ∈ U, (∑ j ∈ V, if p + j = 2 * k then w p * w j else 0) =
      if p ≤ 2 * k ∧ (2 * k - p).Prime then w p * w (2 * k - p) else 0 := by
    intro p hp
    have hpU := (mem_filter.mp hp).2
    by_cases hc : p ≤ 2 * k ∧ (2 * k - p).Prime
    · rw [ite_eq_left hc]
      have hcast : ((2 * k - p : ℕ) : ℝ) = 2 * (k : ℝ) - p := by
        rw [Nat.cast_sub hc.1]
        push_cast
        ring
      have hjlo : 2 * X1 - X2 - Y < ((2 * k - p : ℕ) : ℝ) := by
        rw [hcast]
        linarith [hpU.2.2.1]
      have hjhi : ((2 * k - p : ℕ) : ℝ) ≤ 2 * X1 + 2 * Y - X2 := by
        rw [hcast]
        linarith [hpU.2.1]
      have hj : 2 * k - p ∈ V := by
        refine mem_filter.mpr ⟨mem_range.mpr ?_, hc.2, hjlo, hjhi⟩
        exact Nat.lt_succ_of_le (Nat.le_floor hjhi)
      rw [sum_eq_single_of_mem (2 * k - p) hj]
      · simp [Nat.add_sub_of_le hc.1]
      · intro j hj hjne
        rw [ite_eq_right]
        omega
    · rw [ite_eq_right hc]
      apply sum_eq_zero
      intro j hj
      rw [ite_eq_right]
      intro he
      have hjp := (mem_filter.mp hj).2.1
      have hsub : 2 * k - p = j := by omega
      exact hc ⟨by omega, hsub.symm ▸ hjp⟩
  have hset : U.filter (fun p => p ≤ 2 * k ∧ (2 * k - p).Prime) =
      (range (2 * k + 1)).filter (fun p : ℕ => p.Prime ∧ (2 * k - p).Prime ∧
        X2 < p ∧ (p : ℝ) ≤ X2 + Y ∧ (p : ℤ) ≡ a2 [ZMOD q2]) := by
    ext p
    simp only [U, mem_filter, mem_range]
    constructor
    · rintro ⟨⟨hpr, hp, hlo, hhi, hmod⟩, hle, hsub⟩
      exact ⟨by omega, hp, hsub, hlo, hhi, hmod⟩
    · rintro ⟨hpr, hp, hsub, hlo, hhi, hmod⟩
      exact ⟨⟨Nat.lt_succ_of_le (Nat.le_floor hhi), hp, hlo, hhi, hmod⟩, by omega, hsub⟩
  rw [hint]
  symm
  calc
    _ = ∑ p ∈ U, if p ≤ 2 * k ∧ (2 * k - p).Prime then w p * w (2 * k - p) else 0 :=
      sum_congr rfl hinner
    _ = ∑ p ∈ U.filter (fun p => p ≤ 2 * k ∧ (2 * k - p).Prime), w p * w (2 * k - p) :=
      (sum_filter _ _).symm
    _ = _ := by
      rw [hset]
      simp only [binSumAP, w, Complex.ofReal_sum, Complex.ofReal_mul]

/-- LEAF: minor arc estimate, Kawada section 4 display 3.5 with Bessel's inequality and
Cauchy Schwarz display 3.6, for k = 2. Class HARD. P0077 pages 338 to 339, display 2.4:
the interval endpoints do not matter on the minor arcs, only Y ≫ X1^{2/3+ε} is used. -/
theorem leaf_minor_arcs :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C0 : ℝ, ∀ C : ℝ, C0 ≤ C → ∃ B : ℝ, 0 < B ∧
    ∀ c1 c3 : ℝ, 0 < c1 → 0 < c3 → ∀ a2 : ℤ, ∃ K Y0 : ℝ,
    ∀ X1 X2 Y Q2 : ℝ, Y0 ≤ Y → c1 * X1 ^ (2 / 3 + ε) ≤ Y →
      Y ≤ X1 → Y ≤ X2 → X2 ≤ 2 * X1 - Y →
      1 ≤ Q2 → Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-B) →
      ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ kRange X1 Y,
        ‖∫ α in unitDom X1 \ kMajor A C Y, circF X1 X2 Y q2 a2 (2 * k) α‖ ≤
          K * Y ^ 2 * Real.log Y ^ (-A) := by
  sorry

/-- LEAF: major arc estimate, Kawada displays 3.7 to 3.14 with section 5 displays 3.8, 3.9
and section 6 display 3.12, for k = 2. Class HARD. P0077 page 339, display 2.4: uses
Q2 ≪ Y X2^{-1/2} L^{-B}, Lemma 3 of Kawada, and the singular series S of display 1.1. -/
theorem leaf_major_arcs :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C0 : ℝ, ∀ C : ℝ, C0 ≤ C → ∃ B : ℝ, 0 < B ∧
    ∀ c1 c3 : ℝ, 0 < c1 → 0 < c3 → ∀ a2 : ℤ, ∃ K Y0 : ℝ,
    ∀ X1 X2 Y Q2 : ℝ, Y0 ≤ Y → c1 * X1 ^ (2 / 3 + ε) ≤ Y →
      Y ≤ X1 → Y ≤ X2 → X2 ≤ 2 * X1 - Y →
      1 ≤ Q2 → Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-B) →
      ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ kRange X1 Y,
        ‖(∫ α in unitDom X1 ∩ kMajor A C Y, circF X1 X2 Y q2 a2 (2 * k) α) -
          (Sqa (2 * k) q2 a2 * Y : ℝ)‖ ≤
          K * Y ^ 2 * Real.log Y ^ (-A) := by
  sorry

theorem eA_continuous : Continuous eA := by
  unfold eA
  fun_prop

theorem circF_continuous (X1 X2 Y : ℝ) (q2 : ℕ) (a2 : ℤ) (m : ℕ) :
    Continuous (circF X1 X2 Y q2 a2 m) := by
  have he := eA_continuous
  unfold circF P2 P3
  refine Continuous.mul (Continuous.mul ?_ ?_) (he.comp (by fun_prop))
  · exact continuous_finsetSum _ fun p _ => continuous_const.mul (he.comp (by fun_prop))
  · exact continuous_finsetSum _ fun p _ => continuous_const.mul (he.comp (by fun_prop))

theorem majorArcs_measurable (Q1 Δ : ℝ) : MeasurableSet (majorArcs Q1 Δ) := by
  unfold majorArcs
  refine Finset.measurableSet_biUnion _ fun q _ => ?_
  exact Finset.measurableSet_biUnion _ fun c _ => measurableSet_Icc

/-- The split of the full circle integral into major and minor arcs, Kawada display 3.4. -/
theorem circ_split (X1 X2 Y : ℝ) (q2 : ℕ) (a2 : ℤ) (m : ℕ) (S : Set ℝ) (hS : MeasurableSet S) :
    (∫ α in unitDom X1 ∩ S, circF X1 X2 Y q2 a2 m α) +
      (∫ α in unitDom X1 \ S, circF X1 X2 Y q2 a2 m α) =
      ∫ α in unitDom X1, circF X1 X2 Y q2 a2 m α := by
  apply integral_inter_add_sdiff hS
  exact (circF_continuous X1 X2 Y q2 a2 m).integrableOn_Icc

/-- Assembly: Halupczok Theorem 2.2, display 2.4, from the three leaves. Exact parent statement
of `Decomp598Theorem6.kawada_thm22_display24`. -/
theorem kawada_thm22_display24_of_leaves :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ B : ℝ, 0 < B ∧
    ∀ c1 c3 : ℝ, 0 < c1 → 0 < c3 → ∀ a2 : ℤ, ∃ C Y0 : ℝ,
    ∀ X1 X2 Y Q2 : ℝ, Y0 ≤ Y → c1 * X1 ^ (2 / 3 + ε) ≤ Y →
      Y ≤ X1 → Y ≤ X2 → X2 ≤ 2 * X1 - Y →
      1 ≤ Q2 → Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-B) →
      ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ kRange X1 Y,
        |binSumAP X2 Y q2 a2 (2 * k) - Sqa (2 * k) q2 a2 * Y| ≤
          C * Y ^ 2 * Real.log Y ^ (-A) := by
  intro A ε hA hε
  obtain ⟨Cm, hm⟩ := leaf_minor_arcs A ε hA hε
  obtain ⟨CM, hM⟩ := leaf_major_arcs A ε hA hε
  obtain ⟨Bm, hBm, hm⟩ := hm (max Cm CM) (le_max_left _ _)
  obtain ⟨BM, hBM, hM⟩ := hM (max Cm CM) (le_max_right _ _)
  refine ⟨max Bm BM, lt_max_of_lt_left hBm, ?_⟩
  intro c1 c3 hc1 hc3 a2
  obtain ⟨Km, Ym, hm⟩ := hm c1 c3 hc1 hc3 a2
  obtain ⟨KM, YM, hM⟩ := hM c1 c3 hc1 hc3 a2
  refine ⟨KM + Km, max (max Ym YM) (Real.exp 1), ?_⟩
  intro X1 X2 Y Q2 hY0 h1 h2 h3 h4 hQ1 hQ2
  have hYe : Real.exp 1 ≤ Y := le_trans (le_max_right _ _) hY0
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos 1) hYe
  have hL : 1 ≤ Real.log Y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hYe
  have hX2pos : 0 < X2 := lt_of_lt_of_le hYpos h3
  have hbase : 0 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) := by
    have := Real.rpow_pos_of_pos hX2pos (-(1 / 2) : ℝ)
    positivity
  have hQm : Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-Bm) := by
    refine hQ2.trans (mul_le_mul_of_nonneg_left ?_ hbase)
    exact Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg (le_max_left _ _))
  have hQM : Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-BM) := by
    refine hQ2.trans (mul_le_mul_of_nonneg_left ?_ hbase)
    exact Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg (le_max_right _ _))
  have bm := hm X1 X2 Y Q2 (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY0)
    h1 h2 h3 h4 hQ1 hQm
  have bM := hM X1 X2 Y Q2 (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY0)
    h1 h2 h3 h4 hQ1 hQM
  have hpt : ∀ q2 ∈ Icc 1 ⌊Q2⌋₊, ∀ k ∈ kRange X1 Y,
      |binSumAP X2 Y q2 a2 (2 * k) - Sqa (2 * k) q2 a2 * Y| ≤
        ‖(∫ α in unitDom X1 ∩ kMajor A (max Cm CM) Y, circF X1 X2 Y q2 a2 (2 * k) α) -
          (Sqa (2 * k) q2 a2 * Y : ℝ)‖ +
        ‖∫ α in unitDom X1 \ kMajor A (max Cm CM) Y, circF X1 X2 Y q2 a2 (2 * k) α‖ := by
    intro q2 _ k hk
    have hid := leaf_circle_identity X1 X2 Y q2 a2 k hYpos h4 hk
    rw [← circ_split X1 X2 Y q2 a2 (2 * k) (kMajor A (max Cm CM) Y)
      (majorArcs_measurable _ _)] at hid
    have hn : |binSumAP X2 Y q2 a2 (2 * k) - Sqa (2 * k) q2 a2 * Y| =
        ‖((binSumAP X2 Y q2 a2 (2 * k) : ℝ) : ℂ) - ((Sqa (2 * k) q2 a2 * Y : ℝ) : ℂ)‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hn, hid]
    rw [add_sub_right_comm]
    exact norm_add_le _ _
  calc
    _ ≤ ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ kRange X1 Y,
        (‖(∫ α in unitDom X1 ∩ kMajor A (max Cm CM) Y, circF X1 X2 Y q2 a2 (2 * k) α) -
          (Sqa (2 * k) q2 a2 * Y : ℝ)‖ +
        ‖∫ α in unitDom X1 \ kMajor A (max Cm CM) Y, circF X1 X2 Y q2 a2 (2 * k) α‖) :=
      sum_le_sum fun q2 hq => sum_le_sum fun k hk => hpt q2 hq k hk
    _ = _ + _ := by simp_rw [sum_add_distrib]
    _ ≤ KM * Y ^ 2 * Real.log Y ^ (-A) + Km * Y ^ 2 * Real.log Y ^ (-A) := add_le_add bM bm
    _ = _ := by ring

end LeanLab.Halupczok2012.Decomp598Theorem6LeavesKawada
