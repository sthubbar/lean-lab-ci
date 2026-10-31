import LeanLab.LZCesaroShort.Statements
import LeanLab.LZCesaroShort.ResolvedStatements
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Exp
import LeanLab.LZCesaroShort.Theorem1Short
import LeanLab.LZCesaroShort.Theorem1Full
import LeanLab.LZCesaroShort.Theorem1Printed

namespace LeanLab.LZCesaroShort

open Complex MeasureTheory Finset

open scoped ArithmeticFunction.vonMangoldt Chebyshev

/-- LEAF arXiv:1606.00869v2 page 2, bounds the sum by Ka. -/
theorem theorem1_leaf_1 (hRH : RiemannHypothesis) : ∃ Ka : ℝ, ∃ N0a : ℕ, ∀ N H : ℕ, N0a ≤ N → 2 ≤ H → H ≤ N →
  ∀ i < 2 * H + 1 - 1, |∑ j ∈ range (i + 1), (Real.exp (-((N - H + j : ℕ) : ℝ) / N) * (R (N - H + j)
    - (2 * ψ ((N - H + j : ℕ) : ℝ) - ((N - H + j : ℕ) : ℝ))) * w N H (N - H + j))| ≤ Ka * N * Real.log N ^ 2 * Real.log (2 * H) := by
  obtain ⟨Ka, hKa, hTa⟩ := theorem2a_full hRH
  refine ⟨Ka, 10 ^ 20, fun N H hN hH hHlt i hi => ?_⟩
  have hN20 : (10 : ℝ) ^ 20 ≤ N := by
    have : (10 ^ 20 : ℕ) ≤ N := hN
    exact_mod_cast this
  have hH1 : 1 ≤ H := by omega
  have hHNn : H ≤ N := hHlt
  set b : ℕ → ℝ := fun j => Real.exp (-((N - H + j : ℕ) : ℝ) / N) * (R (N - H + j)
    - (2 * ψ ((N - H + j : ℕ) : ℝ) - ((N - H + j : ℕ) : ℝ))) * w N H (N - H + j)
  have hG : ∀ i ≤ 2 * H, ∑ j ∈ range (i + 1), b j = wsum N H ((i : ℝ) - H) := by
    intro i hi'
    unfold wsum
    rw [filter_eq_Icc hHNn hi', sum_Icc_eq_range]
  rw [hG i (by omega)]
  refine hTa N H _ hN20 hH1 hHlt ?_ ?_
  · have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith
  · have : (i : ℝ) < 2 * H := by exact_mod_cast (by omega : i < 2 * H)
    linarith

/-- LEAF arXiv:1606.00869v2 page 2. bounds the other sum by Kb. -/
theorem theorem1_leaf_2 (hRH : RiemannHypothesis) : ∃ Kb : ℝ, ∃ N0b : ℕ, ∀ N H : ℕ, N0b ≤ N → 2 ≤ H → H ≤ N →
  |∑ j ∈ range (2 * H + 1), (Real.exp (-((N - H + j : ℕ) : ℝ) / N) * (R (N - H + j)
    - (2 * ψ ((N - H + j : ℕ) : ℝ) - ((N - H + j : ℕ) : ℝ))) * w N H (N - H + j))| ≤ Kb * N * Real.log (2 * (N : ℝ) ^ 2 / H) := by
  obtain ⟨Kb, hKb, hTb⟩ := theorem2b_full hRH
  refine ⟨Kb * 2, 10 ^ 20, fun N H hN hH hHlt => ?_⟩
  have hN20 : (10 : ℝ) ^ 20 ≤ N := by
    have : (10 ^ 20 : ℕ) ≤ N := hN
    exact_mod_cast this
  have hH1 : 1 ≤ H := by omega
  have hHNn : H ≤ N := hHlt
  set b : ℕ → ℝ := fun j => Real.exp (-((N - H + j : ℕ) : ℝ) / N) * (R (N - H + j)
    - (2 * ψ ((N - H + j : ℕ) : ℝ) - ((N - H + j : ℕ) : ℝ))) * w N H (N - H + j)
  have hG : ∀ i ≤ 2 * H, ∑ j ∈ range (i + 1), b j = wsum N H ((i : ℝ) - H) := by
    intro i hi'
    unfold wsum
    rw [filter_eq_Icc hHNn hi', sum_Icc_eq_range]
  rw [hG (2 * H) le_rfl]
  have : ((2 * H : ℕ) : ℝ) - H = H := by push_cast; ring
  rw [this]
  have hTb_val := hTb N H hN20 hH1 hHlt
  have hN_pos : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) hN20
  have hH_pos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hlog_ineq : Real.log (2 * (N : ℝ) / H) ^ 2 ≤ 2 * Real.log (2 * (N : ℝ) ^ 2 / H) := by sorry
  have h_kb : Kb * (N : ℝ) * Real.log (2 * (N : ℝ) / H) ^ 2 ≤ Kb * 2 * (N : ℝ) * Real.log (2 * (N : ℝ) ^ 2 / H) := by
    calc Kb * (N : ℝ) * Real.log (2 * (N : ℝ) / H) ^ 2
      _ ≤ Kb * (N : ℝ) * (2 * Real.log (2 * (N : ℝ) ^ 2 / H)) := by
        exact mul_le_mul_of_nonneg_left hlog_ineq (by positivity)
      _ = Kb * 2 * (N : ℝ) * Real.log (2 * (N : ℝ) ^ 2 / H) := by ring
  exact hTb_val.trans h_kb

/-- LEAF arXiv:1606.00869v2 page 2. Main term error. -/
theorem theorem1_leaf_3 (_hRH : RiemannHypothesis) : ∃ Kc : ℝ, ∃ N0c : ℕ, ∀ N H : ℕ, N0c ≤ N → 2 ≤ H → H ≤ N →
  ‖2 / (H : ℂ) * (((∑ n ∈ Icc (N - H) (N + H), ((H : ℝ) - |(n : ℝ) - N|) * (ψ n - n) : ℝ) : ℂ) + ZH N H)‖ ≤ Kc * N := by
  obtain ⟨N8, K8, h8⟩ := lz_lemma8_proved
  refine ⟨2 * |K8|, N8, fun N H hN hH hHlt => ?_⟩
  have hHNn : H ≤ N := hHlt
  have hl8 := h8 N H hN (by omega) hHNn
  rw [norm_mul, norm_div, Complex.norm_ofNat, Complex.norm_natCast]
  have hP' : ‖(((∑ n ∈ Icc (N - H) (N + H), ((H : ℝ) - |(n : ℝ) - N|) * (ψ n - n) : ℝ) : ℂ) + ZH N H)‖ ≤ |K8| * H * N := by
    refine hl8.trans ?_
    have := le_abs_self K8
    have : 0 ≤ (H : ℝ) * N := by positivity
    nlinarith
  calc 2 / (H : ℝ) * ‖(((∑ n ∈ Icc (N - H) (N + H), ((H : ℝ) - |(n : ℝ) - N|) * (ψ n - n) : ℝ) : ℂ) + ZH N H)‖ ≤ 2 / H * (|K8| * H * N) :=
        mul_le_mul_of_nonneg_left hP' (by positivity)
    _ = 2 * |K8| * N := by field_simp

/-- LEAF arXiv:1606.00869v2 page 2. Abel transform bound. -/
theorem theorem1_leaf_4 (hRH : RiemannHypothesis) : ∃ Kd : ℝ, ∃ N0d : ℕ, ∀ N H : ℕ, N0d ≤ N → 2 ≤ H → H ≤ N →
  |∑ n ∈ Icc (N - H) (N + H), w N H n * (R n - (2 * ψ (n : ℝ) - n))| ≤ Kd * (N * Real.log (2 * (N : ℝ) ^ 2 / H) + H * Real.log N ^ 2 * Real.log (2 * H)) := by sorry

/-- LEAF: The exact Theorem 1 Prop is conditional on the two bounds alone. -/
theorem theorem1_assembly (hRH : RiemannHypothesis) : Theorem1 := by
  obtain ⟨Kd, N0d, hKd⟩ := theorem1_leaf_4 hRH
  obtain ⟨Kc, N0c, hKc⟩ := theorem1_leaf_3 hRH
  refine ⟨Kd + Kc, fun N H hN2 hH1 hHlt => ?_⟩
  have hN20 : max N0d N0c ≤ N := by
    sorry
  have h_leaf_3 := hKc N H (le_trans (le_max_right _ _) hN20) (by sorry) hHlt
  have h_leaf_4 := hKd N H (le_trans (le_max_left _ _) hN20) (by sorry) hHlt
  have h_cesaro : (cesaro N H : ℝ) = ∑ n ∈ Icc (N - H) (N + H), w N H n * (R n - (2 * ψ (n : ℝ) - n))
        + H * N + 2 / H * ∑ n ∈ Icc (N - H) (N + H), ((H : ℝ) - |(n : ℝ) - N|) * (ψ n - n) := by
    sorry
  have h1 : ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖
      ≤ ‖(((∑ n ∈ Icc (N - H) (N + H), w N H n * (R n - (2 * ψ (n : ℝ) - n)) : ℝ) : ℂ))‖ + ‖2 / (H : ℂ) * (((∑ n ∈ Icc (N - H) (N + H), ((H : ℝ) - |(n : ℝ) - N|) * (ψ n - n) : ℝ) : ℂ) + ZH N H)‖ := by
    sorry
  sorry

end LeanLab.LZCesaroShort
