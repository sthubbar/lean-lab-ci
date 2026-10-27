/-
P0069, page 4, Theorem 3 II. This audit concerns the unrestricted
lambda quantifier in the sealed lab Prop. It does not edit that Prop.
At lambda equal to 2 the requested lower bound exceeds all available
integers for every sufficiently large h. This is a QUESTION about the
range convention, not a claim against the short interval result.
AI wrote the Lean code. CODEX task132, 2026-10-26. Goldbach is open.
-/
import LeanLab.BHP1997.Statements

namespace LeanLab.BHP1997.Range132
open Classical Real Filter

/-- Page 4 range audit. At lambda equal to 2 every sufficiently large h
fails the lower bound in the lab Prop, using Nat.count_le alone. -/
theorem eventually_bad_square :
    ∃ H : ℕ, 2 ≤ H ∧ ∀ h : ℕ, H ≤ h →
      ¬ (0.05 * (h : ℝ) ^ (2 : ℝ) / Real.log h <
        (Nat.primeCounting h : ℝ) -
          ((Finset.Iic ⌊(h : ℝ) - (h : ℝ) ^ (2 : ℝ)⌋₊).filter Nat.Prime).card) := by
  have hsmall : ∀ᶠ x : ℝ in atTop, Real.log x ≤ 0.01 * x := by
    filter_upwards [(isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).bound
      (show (0 : ℝ) < 0.01 by norm_num), eventually_ge_atTop 1] with x hx hx1
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (by linarith : 0 ≤ x), Real.rpow_one] using hx
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨⌈max R 2⌉₊, ?_, ?_⟩
  · exact_mod_cast le_trans (le_max_right R 2) (Nat.le_ceil (max R 2))
  · intro h hh
    have hhR : max R 2 ≤ (h : ℝ) := Nat.ceil_le.mp hh
    have hh2 : (2 : ℝ) ≤ h := le_trans (le_max_right R 2) hhR
    have hlog := hR h (le_trans (le_max_left R 2) hhR)
    have hlog0 : 0 < Real.log h := Real.log_pos (by linarith)
    have hcount : (Nat.primeCounting h : ℝ) ≤ h + 1 := by
      exact_mod_cast (Nat.count_le (p := Nat.Prime) (n := h + 1))
    have hthreshold : 2 * (h : ℝ) ≤ 0.05 * (h : ℝ) ^ (2 : ℝ) / Real.log h := by
      rw [Real.rpow_two, le_div_iff₀ hlog0]
      nlinarith [mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ h)]
    have hnonneg : (0 : ℝ) ≤
        (((Finset.Iic ⌊(h : ℝ) - (h : ℝ) ^ (2 : ℝ)⌋₊).filter Nat.Prime).card : ℝ) :=
      Nat.cast_nonneg _
    intro hg
    linarith


/-- Page 4 range audit. The unrestricted lab Prop Theorem3II is false:
lambda equal to 2 forces a linear exceptional count. The intended short
interval range remains a QUESTION. The sealed Prop is preserved. -/
theorem theorem3II_unrestricted_false : ¬ Theorem3II := by
  intro hthm
  obtain ⟨B, C, hC⟩ := hthm 2 (by norm_num) 2 (by norm_num)
  obtain ⟨H, hH2, hH⟩ := eventually_bad_square
  have E : ∀ᶠ N : ℕ in atTop,
      C ≤ (N : ℝ) ∧ 2 * H ≤ N ∧ 2 ≤ N ∧ 4 * |B| < Real.log N ^ 2 := by
    have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by norm_num)).comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop C),
      eventually_ge_atTop (2 * H), eventually_ge_atTop 2,
      hlog.eventually (eventually_gt_atTop (4 * |B|))] with N h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨N, hNC, hNH, hN2, hNB⟩ := E.exists
  have hbound := hC N hNC
  let bad : Finset ℕ := (Finset.Icc 2 N).filter (fun h : ℕ =>
    ¬ (0.05 * (h : ℝ) ^ (2 : ℝ) / Real.log h < (Nat.primeCounting h : ℝ) -
      ((Finset.Iic ⌊(h : ℝ) - (h : ℝ) ^ (2 : ℝ)⌋₊).filter Nat.Prime).card))
  have hsub : Finset.Icc H N ⊆ bad := by
    intro h hh
    obtain ⟨hhH, hhN⟩ := Finset.mem_Icc.mp hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_trans hH2 hhH, hhN⟩, hH h hhH⟩
  have hcard : N + 1 - H ≤ bad.card := by
    simpa only [Nat.card_Icc] using Finset.card_le_card hsub
  have hhalf : (N : ℝ) / 2 ≤ bad.card := by
    have : N ≤ 2 * bad.card := by omega
    have hr : (N : ℝ) ≤ 2 * (bad.card : ℝ) := by exact_mod_cast this
    linarith
  have hlog0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hupper : B * (N : ℝ) / Real.log (N : ℝ) ^ 2 < (N : ℝ) / 4 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [le_abs_self B, mul_pos hN0 (show 0 < Real.log (N : ℝ) ^ 2 - 4 * |B| by linarith)]
  have hbound' : (bad.card : ℝ) ≤ B * N / Real.log (N : ℝ) ^ 2 := by
    simpa only [bad, Nat.floor_natCast, Real.rpow_two] using hbound
  linarith


end LeanLab.BHP1997.Range132
