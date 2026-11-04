import LeanLab.GoldbachGaps.Goldston1990Main

/-!
P0030 Goldston 1990 page 286, the size range in Corollary 2.
This audits a proposed implication between size conditions in the task300 repair.
The witness does not assert the variance hypothesis of either corollary.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.GoldbachGaps.Goldston1990
open Real Filter Topology

/-- The fixed logarithmic lower bound and the theorem's upper size range do not force
log squared N divided by K to tend to zero. -/
theorem size_range_not_log_little_o (C : ℝ) (hC : 0 < C) :
    ∃ K : ℕ → ℕ,
      (∀ᶠ N : ℕ in atTop, C * Real.log N ^ 2 ≤ K N ∧
        (K N : ℝ) ≤ N / Real.log N ^ 3) ∧
      ¬ Tendsto (fun N : ℕ => Real.log N ^ 2 / K N) atTop (nhds 0) := by
  let K : ℕ → ℕ := fun N => ⌈C * Real.log N ^ 2⌉₊
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun N : ℕ => Real.log N ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp hlog
  have hceil : Tendsto (fun N : ℕ => (K N : ℝ) / Real.log N ^ 2) atTop (nhds C) :=
    (tendsto_nat_ceil_mul_div_atTop hC.le).comp hsq
  have hinv : Tendsto (fun N : ℕ => Real.log N ^ 2 / K N) atTop (nhds (1 / C)) := by
    simpa only [inv_div, one_div] using hceil.inv₀ hC.ne'
  refine ⟨K, ?_, ?_⟩
  · have hsmall : ∀ᶠ x : ℝ in atTop, (C + 1) * Real.log x ^ 5 < x := by
      have h := (Real.isLittleO_pow_log_id_atTop (n := 5)).const_mul_left (C + 1)
      have he := h.eventuallyLT_norm_of_eventually_pos (by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        simpa only [id_eq, Real.norm_eq_abs, abs_of_pos hx] using hx)
      filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with x hx hpos
      exact lt_of_le_of_lt (le_abs_self _) (by
        simpa [Real.norm_eq_abs, abs_of_pos hpos] using hx)
    have hn := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmall
    filter_upwards [hn, hlog.eventually_ge_atTop 1] with N hN hL
    refine ⟨Nat.le_ceil _, ?_⟩
    have hLpos : 0 < Real.log N := by linarith
    have hLsq : 1 ≤ Real.log N ^ 2 := one_le_pow₀ hL
    have hk : (K N : ℝ) ≤ (C + 1) * Real.log N ^ 2 := by
      have hc := (Nat.ceil_lt_add_one
        (show 0 ≤ C * Real.log N ^ 2 by positivity)).le
      change (⌈C * Real.log N ^ 2⌉₊ : ℝ) ≤ _
      nlinarith
    rw [le_div_iff₀ (pow_pos hLpos 3)]
    calc (K N : ℝ) * Real.log N ^ 3
        ≤ ((C + 1) * Real.log N ^ 2) * Real.log N ^ 3 :=
          mul_le_mul_of_nonneg_right hk (pow_nonneg hLpos.le 3)
      _ = (C + 1) * Real.log N ^ 5 := by ring
      _ ≤ N := hN.le
  · intro hz
    have heq := tendsto_nhds_unique hinv hz
    have hp : (0 : ℝ) < 1 / C := one_div_pos.mpr hC
    linarith

end LeanLab.GoldbachGaps.Goldston1990
