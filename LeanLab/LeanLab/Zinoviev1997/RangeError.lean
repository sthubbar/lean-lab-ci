/-
AI wrote this Lean code. Codex task69, 2026-10-25.
The elementary change of integration range in Lemma 3.2, pages 355 to 356.
The geometric bound with constant one quarter gives a sufficient error of 0.0043 N squared.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.ModelTail
import LeanLab.Zinoviev1997.ArcTail
import LeanLab.Zinoviev1997.ArcArithmetic

namespace LeanLab.Zinoviev1997
open Real Finset Filter Topology ArithmeticFunction LeanLab.CircleOrth MeasureTheory
open LeanLab.HardyLittlewood1923.U1438

/-- The major arc radius is positive and below one half at the theorem's threshold. -/
theorem arcRadius_mem (N q : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) (hq : 0 < q) :
    0 < arcRadius N q ∧ arcRadius N q ≤ 1 / 2 := by
  have hn : (0 : ℝ) < N := by linarith
  have hl : 46 ≤ Real.log N := le_trans log_1e20_ge (Real.log_le_log (by norm_num) hN)
  have hφ : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hs : (8 : ℝ) ≤ Real.sqrt N := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 8) hn.le).mpr
    linarith
  have hlog : Real.log N ≤ 2 * Real.sqrt N := by
    have h := Real.log_le_rpow_div hn.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  have hsq := Real.sq_sqrt hn.le
  unfold arcRadius
  constructor
  · positivity
  · have hlead : 2 * Real.log N / (Nat.totient q * N) ≤ 2 * Real.log N / N := by
      apply div_le_div_of_nonneg_left (by positivity) hn
      nlinarith
    have hh : 2 * Real.log N / N ≤ (1 / 2 : ℝ) := by
      rw [div_le_iff₀ hn]
      nlinarith
    exact hlead.trans hh

/-- The model tail at the paper's radius has the required phi squared scaling. -/
theorem modelTail_arcRadius (N q : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) (hq : 0 < q) :
    ‖modelTail N (arcRadius N q)‖ ≤
      (Nat.totient q : ℝ) ^ 2 * (N : ℝ) ^ 2 / (256 * Real.log N ^ 2) := by
  have hn : 0 < N := by
    have : (0 : ℝ) < N := by linarith
    exact_mod_cast this
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hl : 0 < Real.log N := by
    have : (1 : ℝ) < N := by linarith
    exact Real.log_pos this
  obtain ⟨hδ, hδ'⟩ := arcRadius_mem N q hN hq
  calc
    _ ≤ 1 / (64 * arcRadius N q ^ 2) := modelTail_norm_le N hn _ hδ hδ'
    _ = _ := by
      unfold arcRadius
      field_simp
      ring

/-- The range extension error after summing reduced residues through the cutoff. -/
noncomputable def rangeError (N : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 (arcCutoff N), (singTerm N q : ℂ) * modelTail N (arcRadius N q)

/-- A sufficient replacement for display 3.13, using the weaker chord constant. -/
theorem rangeError_norm_le (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) :
    ‖rangeError N‖ ≤ 0.0043 * (N : ℝ) ^ 2 := by
  have hl : 0 < Real.log N := by
    have : (1 : ℝ) < N := by linarith
    exact Real.log_pos this
  have hq : (arcCutoff N : ℝ) ≤ 1.1 * Real.log N ^ 2 := Nat.floor_le (by positivity)
  have hb : ∀ q ∈ Finset.Icc 1 (arcCutoff N),
      ‖(singTerm N q : ℂ) * modelTail N (arcRadius N q)‖ ≤
        (N : ℝ) ^ 2 / (256 * Real.log N ^ 2) := by
    intro q hqq
    have hq0 : 0 < q := (Finset.mem_Icc.mp hqq).1
    have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq0
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ (1 / (Nat.totient q : ℝ) ^ 2) *
          ((Nat.totient q : ℝ) ^ 2 * (N : ℝ) ^ 2 / (256 * Real.log N ^ 2)) :=
        mul_le_mul (abs_singTerm_le N q hq0) (modelTail_arcRadius N q hN hq0)
          (norm_nonneg _) (by positivity)
      _ = _ := by field_simp
  unfold rangeError
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 (arcCutoff N),
        ‖(singTerm N q : ℂ) * modelTail N (arcRadius N q)‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 (arcCutoff N), (N : ℝ) ^ 2 / (256 * Real.log N ^ 2) :=
      Finset.sum_le_sum hb
    _ = (arcCutoff N : ℝ) * ((N : ℝ) ^ 2 / (256 * Real.log N ^ 2)) := by
      simp [Nat.card_Icc]
    _ ≤ (1.1 * Real.log N ^ 2) * ((N : ℝ) ^ 2 / (256 * Real.log N ^ 2)) :=
      mul_le_mul_of_nonneg_right hq (by positivity)
    _ = 0.004296875 * (N : ℝ) ^ 2 := by field_simp; ring
    _ ≤ _ := by nlinarith [sq_nonneg (N : ℝ)]

/-- The remainder split before the two elementary tail steps.
Only the three local approximation errors remain as bounded inputs. -/
def Lemma32LocalInput (N : ℕ) : Prop :=
  ∃ r₁ r₂ r₃ : ℂ,
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs N,
      SZ N α ^ 3 * ee (-((N : ℤ) * α))) - (sing3 N : ℂ) * modelIntegral N =
      r₁ + r₂ + r₃ - rangeError N -
        (((∑' i : ℕ, singTerm N (i + (arcCutoff N + 1)) : ℝ) : ℂ) * modelIntegral N) ∧
    ‖r₁‖ ≤ 0.0008 * (N : ℝ) ^ 2 ∧ ‖r₂‖ ≤ 0.012 * (N : ℝ) ^ 2 ∧
    ‖r₃‖ ≤ 0.003 * (N : ℝ) ^ 2

/-- Lemma 3.2 with only its three local errors and exact decomposition left conditional. -/
theorem lemma32_of_local (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (h : Lemma32LocalInput N) : Lemma32Input N (sing3 N) := by
  obtain ⟨r₁, r₂, r₃, he, h₁, h₂, h₃⟩ := h
  have hr := rangeError_norm_le N hN
  have hn : 0 < N := by
    have : (0 : ℝ) < N := by linarith
    exact_mod_cast this
  have ht := lemma32_tail_error N (arcCutoff N) hn (arcCutoff_ge_2200 N hN)
  unfold Lemma32Input
  rw [he]
  have ha := norm_sub_le (r₁ + r₂ + r₃ - rangeError N)
    ((((∑' i : ℕ, singTerm N (i + (arcCutoff N + 1)) : ℝ) : ℂ) * modelIntegral N))
  have hb := norm_sub_le (r₁ + r₂ + r₃) (rangeError N)
  have hc := norm_add_le (r₁ + r₂) r₃
  have hd := norm_add_le r₁ r₂
  nlinarith [sq_nonneg (N : ℝ)]

/-- Theorem 3.4 with the elementary model and both tails discharged. -/
theorem zinoviev_of_local (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) (hodd : Odd N)
    (h21 : Lemma21Input N) (h32 : Lemma32LocalInput N) : IsTernarySum N :=
  zinoviev_of_two_lemmas N hN hodd h21 (lemma32_of_local N hN h32)

end LeanLab.Zinoviev1997
