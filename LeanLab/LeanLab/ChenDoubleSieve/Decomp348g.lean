import LeanLab.ChenDoubleSieve.Decomp348f

/-!
Uniform finite level range for the prime sums in Wu 2004 equation 10.5.
Source: https://arxiv.org/pdf/0705.1652, pages 38 and 39.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348
open Task275
open Wu04Functional (IsLinearSieve)

/-- Fixing d subtracts its logarithmic size from the residual level. -/
theorem lowerLevel_divisor (B : ℝ) {N d : ℕ} (hN : 2 ≤ N) (hd : 1 ≤ d) :
    lowerLevel B N d = lowerLevel B N 1 - 12 * log d / log N := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  unfold lowerLevel
  simp only [Nat.cast_one, div_one]
  rw [log_div (div_pos (rpow_pos_of_pos hpos _) (rpow_pos_of_pos hlog _)).ne' hdpos.ne',
    log_rpow hpos]
  norm_num [kappa1]
  field_simp
  <;> ring

/-- All residual levels with d at most N to one third lie in one to six eventually. -/
theorem lowerLevel_window (B : ℝ) (hB : 0 < B) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ d : ℕ, 1 ≤ d →
      (d : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) → lowerLevel B N d ∈ Icc (1 : ℝ) 6 := by
  have hb : ∀ᶠ N : ℕ in atTop, 5 < lowerLevel B N 1 :=
    (lowerLevel_one_tendsto B).eventually (eventually_gt_nhds (by norm_num))
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ log (N : ℝ) :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hb.and hl)
  refine ⟨max 2 K, ?_⟩
  intro N hN d hd hbound
  have hN2 : 2 ≤ N := by omega
  obtain ⟨hbase, hlogone⟩ := hK N (by omega)
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := by linarith
  have hll : 0 ≤ log (log (N : ℝ)) := log_nonneg hlogone
  have hdl : 0 ≤ log (d : ℝ) := log_nonneg (by exact_mod_cast hd)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdup : log (d : ℝ) ≤ (1 / 3 : ℝ) * log N := by
    have he := log_le_log hdpos hbound
    rwa [log_rpow hpos] at he
  have hcorr : 0 ≤ 12 * log (d : ℝ) / log N := by positivity
  have hcorrup : 12 * log (d : ℝ) / log N ≤ 4 :=
    (div_le_iff₀ hlog).2 (by linarith)
  have hbaseup : lowerLevel B N 1 ≤ 6 := by
    rw [lowerLevel_one B hN2]
    have he : 0 ≤ 12 * B * (log (log (N : ℝ)) / log N) := by positivity
    linarith
  rw [lowerLevel_divisor B hN2 hd]
  exact ⟨by linarith, by linarith⟩

/-- The actual finite lower sieve values are uniformly bounded on these divisor ranges.
CONDITIONAL ON IsLinearSieve only. -/
theorem lower_values_bounded (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) : ∃ M : ℝ, 0 ≤ M ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N → ∀ d : ℕ, 1 ≤ d →
        (d : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) → |f (lowerLevel B N d)| ≤ M := by
  have hc : ContinuousOn f (Icc (1 : ℝ) 6) := h.2.1.mono (by
    intro u hu
    change 0 < u
    linarith [hu.1])
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  obtain ⟨N0, hN0⟩ := lowerLevel_window B hB
  refine ⟨max M 0, le_max_right _ _, N0, ?_⟩
  intro N hN d hd hb
  have he := hM _ (hN0 N hN d hd hb)
  rw [Real.norm_eq_abs] at he
  exact he.trans (le_max_left _ _)

end LeanLab.ChenDoubleSieve.Task348
