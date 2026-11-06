import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.BuchstabBounds
import LeanLab.ChenDoubleSieve.JPanelArithmetic
import LeanLab.ChenDoubleSieve.SigmaCertificate
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
A finite part of the sharp Buchstab tail bound used in the numerical leaves.
Source: https://arxiv.org/pdf/0705.1652, page 9 Lemma 2.10 and page 42.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set Finset MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Task350
open Wu04Functional Wu04Buchstab Wu04Integral Wu04Panels

/-- Rational upper panels for the logarithmic integral in omega at four.
Source: page 9 defining delay equation, derived finite certificate data. -/
def upperJPanel (j : ℕ) : ℚ :=
  let a : ℚ := 2 + j / 24
  let b : ℚ := 2 + (j + 1) / 24
  logUpperQ 8 (a - 1) * logUpperQ 8 (b / a) +
    ((b - a) - a * logLowerQ 8 (b / a)) / (a - 1)

/-- The finite rational panel sum has the required room.
Source: page 9 defining equation, derived arithmetic certificate. -/
theorem upperJPanel_sum : (∑ j ∈ range 24, upperJPanel j) ≤ (1473 / 10000 : ℚ) := by
  decide +kernel

/-- Twenty four rational logarithm panels bound the integral needed at four.
Source: page 9 Lemma 2.10, derived numerical bound. -/
theorem J_two_three_upper : (∫ t in (2 : ℝ)..3, log (t - 1) / t) ≤ 1473 / 10000 := by
  have hp := (J_partition_arithmetic 8 24 (fun j => 2 + (j : ℝ) / 24) (by
    intro j hj
    constructor <;> push_cast <;> linarith [Nat.cast_nonneg (α := ℝ) j])).2
  norm_num only [Nat.cast_ofNat, Nat.cast_zero, zero_div, add_zero, div_self (by norm_num : (24 : ℝ) ≠ 0)] at hp
  have hc : ((∑ j ∈ range 24, upperJPanel j : ℚ) : ℝ) =
      ∑ j ∈ range 24, JUpper 8 (2 + (j : ℝ) / 24) (2 + ((j + 1 : ℕ) : ℝ) / 24) := by
    push_cast
    apply sum_congr rfl
    intro j hj
    simp only [upperJPanel, JUpper]
    push_cast
    simp only [logUpperQ_cast, logLowerQ_cast]
    push_cast
    rfl
  have hq : ((∑ j ∈ range 24, upperJPanel j : ℚ) : ℝ) ≤ (1473 / 10000 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).2 upperJPanel_sum
    convert hh using 1 <;> norm_num
  rw [hc] at hq
  exact hp.trans hq

/-- The delay equation gives an exact logarithmic formula at four.
Source: page 9 Lemma 2.10, derived method of steps identity. -/
theorem buchstab_four_formula {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    4 * ω 4 = 1 + log 3 + ∫ t in (2 : ℝ)..3, log (t - 1) / t := by
  have hc : ContinuousOn (fun t : ℝ => t * ω t) (Icc 3 4) :=
    continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
  have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc 3 4) := by
    rw [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)]
    apply hω.1.comp (by fun_prop)
    intro t ht
    change 1 ≤ t - 1
    linarith [ht.1]
  have he := integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (3 : ℝ) ≤ 4) hc
    (fun t ht => hω.2.2 t (by linarith [ht.1])) hci.intervalIntegrable
  have hi : (∫ t in (3 : ℝ)..4, ω (t - 1)) =
      log (3 / 2 : ℝ) + ∫ t in (2 : ℝ)..3, log (t - 1) / t := by
    calc
      _ = ∫ t in (3 : ℝ)..4, (1 + log (t - 2)) / (t - 1) := by
        apply integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)] at ht
        convert formula_two_three hω (u := t - 1) ⟨by linarith [ht.1], by linarith [ht.2]⟩ using 1 <;> ring
      _ = ∫ t in (2 : ℝ)..3, (1 + log (t - 1)) / t := by
        have hs := integral_comp_sub_right (fun t : ℝ => (1 + log (t - 1)) / t)
          (a := 3) (b := 4) 1
        norm_num only [show (3 - 1 : ℝ) = 2 by norm_num, show (4 - 1 : ℝ) = 3 by norm_num] at hs
        convert hs using 1
        apply integral_congr
        intro t _
        congr 2 <;> ring
      _ = _ := by
        have h1 : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / t) volume 2 3 := by
          apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)]
          exact continuousOn_const.div continuousOn_id (fun t ht => by linarith [ht.1])
        rw [show (fun t : ℝ => (1 + log (t - 1)) / t) =
          (fun t => 1 / t + log (t - 1) / t) by funext t; ring,
          integral_add h1 (J_integrable (by norm_num) (by norm_num))]
        simp only [one_div, integral_inv_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 3)]
  rw [hi] at he
  have h3 := formula_two_three hω (u := 3) (by norm_num)
  norm_num only [show (3 - 1 : ℝ) = 2 by norm_num] at h3
  have hl : log (3 / 2 : ℝ) = log 3 - log 2 := log_div (by norm_num) (by norm_num)
  rw [hl, h3] at he
  linarith

/-- The exact endpoint is below the sharp tail constant.
Source: page 9 Lemma 2.10, derived finite numerical check. -/
theorem buchstab_four_upper {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    ω 4 ≤ 280761 / 500000 := by
  have he := buchstab_four_formula hω
  have hj := J_two_three_upper
  have hl : log (3 : ℝ) ≤ 1098613 / 1000000 := by
    apply (log_bounds 16 (y := 3) (by norm_num)).2.trans
    norm_num [logUpper, logLower, sum_range_succ]
  linarith

/-- Concavity and two rational logarithm bounds give a lower strip.
Source: page 9 Lemma 2.10, derived helper for backward propagation. -/
theorem buchstab_lower_five_halves_three {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : u ∈ Icc (5 / 2 : ℝ) 3) : 280761 / 500000 ≤ ω u := by
  have hl1 : (4054 / 10000 : ℝ) ≤ log (3 / 2 : ℝ) := by
    apply le_trans _ (log_bounds 8 (y := 3 / 2) (by norm_num)).1
    norm_num [logLower, sum_range_succ]
  have hl2 : (6931 / 10000 : ℝ) ≤ log (2 : ℝ) := by
    apply le_trans _ (log_bounds 8 (y := 2) (by norm_num)).1
    norm_num [logLower, sum_range_succ]
  have ha : 0 ≤ 6 - 2 * u := by linarith [hu.2]
  have hb : 0 ≤ 2 * u - 5 := by linarith [hu.1]
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2
    (x := (3 / 2 : ℝ)) (y := (2 : ℝ)) (by norm_num) (by norm_num)
    ha hb (by ring : (6 - 2 * u) + (2 * u - 5) = 1)
  simp only [smul_eq_mul] at hlog
  have he : (6 - 2 * u) * (3 / 2 : ℝ) + (2 * u - 5) * 2 = u - 1 := by ring
  rw [he] at hlog
  have h1 := mul_le_mul_of_nonneg_left hl1 ha
  have h2 := mul_le_mul_of_nonneg_left hl2 hb
  rw [formula_two_three hω ⟨by linarith [hu.1], hu.2⟩, le_div_iff₀ (by linarith [hu.1])]
  linarith

/-- The first half of the sharp compact tail follows from the checked endpoint.
Source: page 9 Lemma 2.10, derived finite delay equation estimate. -/
theorem buchstab_seven_halves_to_four {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : u ∈ Icc (7 / 2 : ℝ) 4) : ω u ≤ 280761 / 500000 := by
  have hc : ContinuousOn (fun t : ℝ => t * ω t) (Icc u 4) :=
    continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1, hu.1]))
  have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc u 4) := by
    rw [uIcc_of_le hu.2]
    apply hω.1.comp (by fun_prop)
    intro t ht
    change 1 ≤ t - 1
    linarith [ht.1, hu.1]
  have he := integral_eq_sub_of_hasDerivAt_of_le hu.2 hc
    (fun t ht => hω.2.2 t (by linarith [ht.1, hu.1])) hci.intervalIntegrable
  have hi : (4 - u) * (280761 / 500000 : ℝ) ≤ ∫ t in u..4, ω (t - 1) := by
    have hm := integral_mono_on (μ := volume) hu.2 intervalIntegrable_const hci.intervalIntegrable
      (fun t ht => buchstab_lower_five_halves_three hω ⟨by linarith [ht.1, hu.1], by linarith [ht.2]⟩)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
  have h4 := buchstab_four_upper hω
  apply (mul_le_mul_iff_right₀ (by linarith [hu.1] : 0 < u)).mp
  nlinarith

end LeanLab.ChenDoubleSieve.Task350
