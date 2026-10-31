import LeanLab.HeathBrownPuchta.Assembly
import LeanLab.HeathBrownPuchta.Decomp1530c

/-!
P0012 Theorem 1, page 1, and its completion on pages 27 and 28.
The final statement is exactly the type of Linnik.heathBrownPuchta.
The prior Assembly file proves an implication from analytic inputs.
This file supplies a decomposition of those inputs for the actual integrals.
Each open leaf names the paper results it still needs.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HeathBrownPuchta.Decomp130

open Real Filter MeasureTheory LeanLab.Linnik
open LeanLab.HeathBrownPuchta.Decomp1530a
open LeanLab.HeathBrownPuchta.Decomp1530b
open LeanLab.HeathBrownPuchta.Decomp1530c
open LeanLab.HeathBrownPuchta.Assembly

/-- Paper page 14, display 23, the twin prime product. -/
noncomputable def C0 : ℝ :=
  ∏' p : ℕ, if p.Prime ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1

/-- Paper page 27, the chosen major arc parameter. -/
noncomputable def P (N : ℕ) (w : ℝ) : ℝ := (N : ℝ) ^ (45 / 154 - 4 * w)

/-- Paper page 3, the major arcs in the unit interval. -/
def majorArcs (N : ℕ) (w : ℝ) : Set ℝ :=
  {α ∈ Set.Icc (0 : ℝ) 1 | ∃ (a : ℤ) (q : ℕ), 0 < q ∧ (q : ℝ) ≤ P N w ∧
    |α - (a : ℝ) / q| ≤ P N w / (q * N)}

/-- Paper page 2, the exceptional set at the unconditional lambda. -/
def exceptional (N : ℕ) : Set ℝ :=
  {α ∈ Set.Icc (0 : ℝ) 1 | (863665 / 1000000 : ℝ) * Lpar N 13 ≤ ‖Tp (Lpar N 13) α‖}

/-- Paper page 27, the integrand at K equal to 13. -/
noncomputable def integrand (N : ℕ) (w α : ℝ) : ℂ :=
  Sp N w α ^ 2 * Tp (Lpar N 13) α ^ 13 * ee (-(α * N))

/-- Paper page 27, the real part of the representation integral. -/
noncomputable def R (N : ℕ) (w : ℝ) : ℝ := (Rint N w (Lpar N 13) 13).re

/-- Paper pages 20 and 28, the major arc contribution. -/
noncomputable def maj (N : ℕ) (w : ℝ) : ℝ :=
  ∫ α in majorArcs N w, (integrand N w α).re

/-- Paper page 28, the minor arcs outside the exceptional set. -/
noncomputable def mout (N : ℕ) (w : ℝ) : ℝ :=
  ∫ α in (Set.Icc (0 : ℝ) 1 \ majorArcs N w) \ exceptional N, (integrand N w α).re

/-- Paper page 28, the minor arcs inside the exceptional set. -/
noncomputable def minr (N : ℕ) (w : ℝ) : ℝ :=
  ∫ α in (Set.Icc (0 : ℝ) 1 \ majorArcs N w) ∩ exceptional N, (integrand N w α).re

/-- Paper pages 20 and 28, the common scale of the three estimates. -/
noncomputable def X (N : ℕ) : ℝ :=
  C0 * N * (Lpar N 13 : ℝ) ^ (13 - 2) / Real.log 2 ^ 2

/-- LEAF. Paper page 28, partition of the representation integral.
This uses only integrability and the disjoint partition of the unit interval. -/
theorem integral_split (N : ℕ) (w : ℝ) :
    R N w = maj N w + mout N w + minr N w := by
  have hc : Continuous (integrand N w) := by unfold integrand Sp Tp ee; fun_prop
  have hi : IntegrableOn (integrand N w) (Set.Icc (0 : ℝ) 1) volume :=
    hc.continuousOn.integrableOn_compact isCompact_Icc
  have hir : IntegrableOn (fun α => (integrand N w α).re) (Set.Icc (0 : ℝ) 1) volume :=
    hi.re
  have hm : MeasurableSet (majorArcs N w) := by
    unfold majorArcs
    simp only [Set.ofPred_and, Set.ofPred_exists]
    refine measurableSet_Icc.inter (MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun q => ?_)
    measurability
  have ha : MeasurableSet (exceptional N) := by
    unfold exceptional
    have ht : Continuous (fun α : ℝ => ‖Tp (Lpar N 13) α‖) := by unfold Tp ee; fun_prop
    exact measurableSet_Icc.inter (measurableSet_le measurable_const ht.measurable)
  have hmSub : majorArcs N w ⊆ Set.Icc (0 : ℝ) 1 := fun α hα => hα.1
  have hh := integral_inter_add_sdiff hm hir
  rw [Set.inter_eq_right.mpr hmSub] at hh
  have hh' := integral_inter_add_sdiff ha (hir.mono_set (show Set.Icc (0 : ℝ) 1 \ majorArcs N w ⊆ Set.Icc (0 : ℝ) 1 from Set.sdiff_subset))
  have hR : R N w = ∫ α in Set.Icc (0 : ℝ) 1, (integrand N w α).re := by
    unfold R Rint
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
    exact (integral_re hi).symm
  rw [hR]
  unfold maj mout minr
  linarith

/-- LEAF. Paper pages 25 and 26, displays 40 and 41.
The C2 bound uses Liu, Liu and Wang 1999, display 3.9, through the paper's proof.
The C0 bound uses the finite product and telescoping tail of display 40. -/
theorem constants : 66 / 100 ≤ C0 ∧
    LeanLab.HeathBrownPuchta.Lemma8Const.C2 ≤ 22141 / 10000 := by
  sorry

/-- LEAF. Paper page 2, the logarithmic length gives a positive linear lower scale. -/
theorem scale (hC0 : 0 < C0) :
    ∃ c > 0, ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ≤ X N := by
  apply LeanLab.HeathBrownPuchta.Assembly.scale_of_L hC0 13 (fun N => Lpar N 13)
  filter_upwards [eventually_ge_atTop 52] with N hN
  unfold Lpar
  apply Nat.le_floor
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ h2]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_mul]
  apply Real.log_le_log (by norm_num)
  have hh : (52 : ℝ) ≤ N := by exact_mod_cast hN
  norm_num
  linarith

/-- LEAF. Paper page 20, Lemma 7, used on page 28 at K equal to 13.
The proof uses Gallagher's major arc method and the density inputs of Section 3.
All sufficiently small positive w are allowed. -/
theorem major_estimate : ∃ w0 > (0 : ℝ), ∀ w : ℝ, 0 < w → w ≤ w0 →
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      Even N → (27895 / 10000 * (1 - 3 * w) - ε) * X N ≤ maj N w := by
  sorry

/-- LEAF. Paper page 28, outside the exceptional set, using Lemmas 8 to 10.
Chen's prime pair bound is cited on page 21 and remains an outside input here. -/
theorem minor_out_estimate : ∃ w0 > (0 : ℝ), ∀ w : ℝ, 0 < w → w ≤ w0 →
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      |mout N w| ≤ (C9 (78342 / 10000) LeanLab.HeathBrownPuchta.Lemma8Const.C2 C0 w *
        (863665 / 1000000) ^ (13 - 2) + ε) * X N := by
  sorry

/-- LEAF. Paper pages 27 and 28, Lemma 1 with Vaughan Theorem 3.1.
The exponent E exceeds 109/154 and is uniform in sufficiently small positive w. -/
theorem minor_in_estimate : ∃ E : ℝ, 109 / 154 < E ∧
    ∃ w0 > (0 : ℝ), ∀ w : ℝ, 0 < w → w ≤ w0 →
      ∀ δ > 0, ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
        |minr N w| ≤ C * (N : ℝ) ^ (2 * (263 / 308 + 3 * w) - E + δ) := by
  sorry

/-- The exact cited Theorem 1, paper page 1, assembled from the open analytic leaves.
CONDITIONAL ON those leaves and the open circle identity of Decomp1530c.
The assembly has no sorry of its own. -/
theorem theorem1 : AllLargeEven (LinnikExact 13) := by
  obtain ⟨hc0, hc2⟩ := constants
  obtain ⟨wa, hwa, hmajor⟩ := major_estimate
  obtain ⟨wb, hwb, hout⟩ := minor_out_estimate
  obtain ⟨E, hE, wd, hwd, hin⟩ := minor_in_estimate
  let w := min (min wa wb) (min wd (min (1 / 100000 : ℝ) ((E - 109 / 154) / 12)))
  have hw : 0 < w := lt_min (lt_min hwa hwb)
    (lt_min hwd (lt_min (by norm_num) (by linarith)))
  have hwa' : w ≤ wa := (min_le_left _ _).trans (min_le_left _ _)
  have hwb' : w ≤ wb := (min_le_left _ _).trans (min_le_right _ _)
  have hwd' : w ≤ wd := (min_le_right _ _).trans (min_le_left _ _)
  have hwsmall : w ≤ 1 / 100000 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hwE : w ≤ (E - 109 / 154) / 12 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hC0p : 0 < C0 := by linarith
  have hX0 (N : ℕ) : 0 ≤ X N := by unfold X; positivity
  have hC9 : 0 ≤ C9 (78342 / 10000) LeanLab.HeathBrownPuchta.Lemma8Const.C2 C0 w := by
    unfold C9
    have hC2 := Decomp1530b.C2_nonneg'
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  let I : AnalyticInputs 13 (863665 / 1000000) (263 / 308 + 3 * w) E w := {
    R := fun N => if Even N then R N w else 3 * X N
    maj := fun N => if Even N then maj N w else 3 * X N
    mout := fun N => if Even N then mout N w else 0
    minr := fun N => if Even N then minr N w else 0
    X := X
    C2 := LeanLab.HeathBrownPuchta.Lemma8Const.C2
    C0 := C0
    split := fun N => by
      by_cases hN : Even N
      · simpa only [if_pos hN] using integral_split N w
      · simp only [if_neg hN]; ring
    scale := scale hC0p
    bound_C2 := hc2
    bound_C0 := hc0
    lemma7 := fun ε hε => by
      filter_upwards [hmajor w hw hwa' ε hε] with N hN
      by_cases he : Even N
      · simpa only [if_pos he] using hN he
      · simp only [if_neg he]
        have hc : 27895 / 10000 * (1 - 3 * w) - ε ≤ (3 : ℝ) := by linarith
        exact mul_le_mul_of_nonneg_right hc (hX0 N)
    lemma9_out := fun ε hε => by
      filter_upwards [hout w hw hwb' ε hε] with N hN
      by_cases he : Even N
      · simpa only [if_pos he] using hN
      · simp only [if_neg he, abs_zero]
        have hx := hX0 N
        positivity
    lemma1_in := fun δ hδ => by
      obtain ⟨C, hC⟩ := hin w hw hwd' δ hδ
      refine ⟨|C|, ?_⟩
      filter_upwards [hC] with N hN
      by_cases he : Even N
      · simp only [if_pos he]
        exact hN.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
      · simp only [if_neg he, abs_zero]
        positivity }
  have hgap : 2 * (263 / 308 + 3 * w) - 1 < E := by linarith
  have hcrit : 13968 / 1000 * (863665 / 1000000 : ℝ) ^ (13 - 2) <
      27895 / 10000 * (1 - 3 * w) := by
    have hh := crit13
    nlinarith
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp
    (section6_positive I hw.le hwsmall (by norm_num) hgap hcrit)
  refine ⟨N0, fun N hEven hN => ?_⟩
  apply circle_positive (w := w) (L := Lpar N 13)
  have hp := hN0 N hN.le
  simpa only [I, if_pos hEven, R] using hp

end LeanLab.HeathBrownPuchta.Decomp130
