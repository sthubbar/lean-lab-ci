import LeanLab.ChenDoubleSieve.Decomp367b

/-!
Remove the finite logarithmic loss before the F5 partial summation.
Source: https://arxiv.org/pdf/0705.1652, pages 38 and 39 equation 10.5.
Only continuity and the proved one dimensional prime mass limit are used.
The moving triangular integral limit remains OPEN.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task367
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- The finite logarithmic perturbation is independent of the fixed divisor. -/
theorem lowerLevel_shift (B : ℝ) {N d : ℕ} (hN : 2 ≤ N) (hd : 1 ≤ d) :
    lowerLevel B N d - lowerLevel 0 N d = lowerLevel B N 1 - 6 := by
  rw [lowerLevel_divisor B hN hd, lowerLevel_divisor 0 hN hd,
    lowerLevel_one 0 hN]
  ring

/-- The zero loss residual level lies between one and six on the F5 product range. -/
theorem lowerLevel_zero_window {N d : ℕ} (hN : 2 ≤ N) (hd : 1 ≤ d)
    (hb : (d : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ)) :
    lowerLevel 0 N d ∈ Icc (1 : ℝ) 6 := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlo : 0 ≤ log (d : ℝ) := log_nonneg (by exact_mod_cast hd)
  have hup : log (d : ℝ) ≤ (1 / 3 : ℝ) * log N := by
    have he := log_le_log hdpos hb
    rwa [log_rpow hpos] at he
  have he : 12 * log (d : ℝ) / log N ≤ 4 :=
    (div_le_iff₀ hlog).2 (by linarith)
  have hz : 0 ≤ 12 * log (d : ℝ) / log N := by positivity
  rw [lowerLevel_divisor 0 hN hd, lowerLevel_one 0 hN]
  constructor <;> nlinarith

/-- The change in the lower sieve function caused by the finite logarithmic
loss tends uniformly to zero on all actual F5 products.
CONDITIONAL ON IsLinearSieve only. -/
theorem lower_values_shift_small (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ d : ℕ, 1 ≤ d →
      (d : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) →
      |f (lowerLevel B N d) - f (lowerLevel 0 N d)| ≤ ε := by
  have hc : ContinuousOn f (Icc (1 : ℝ) 6) := h.2.1.mono (by
    intro u hu
    change 0 < u
    linarith [hu.1])
  obtain ⟨δ, hδ, hcont⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) ε hε
  have hs : ∀ᶠ N : ℕ in atTop, |lowerLevel B N 1 - 6| < δ := by
    have he := (lowerLevel_one_tendsto B).sub_const 6
    have hz : Tendsto (fun N : ℕ => |lowerLevel B N 1 - 6|) atTop (𝓝 0) := by
      simpa only [sub_self, abs_zero] using he.abs
    exact hz.eventually (eventually_lt_nhds hδ)
  obtain ⟨M, hM⟩ := eventually_atTop.1 hs
  obtain ⟨J, hJ⟩ := lowerLevel_window B hB
  refine ⟨max 2 (max M J), ?_⟩
  intro N hN d hd hb
  have hnear : dist (lowerLevel B N d) (lowerLevel 0 N d) < δ := by
    rw [Real.dist_eq, lowerLevel_shift B (by omega) hd]
    exact hM N (by omega)
  simpa only [Real.dist_eq] using
    (hcont _ (hJ N (by omega) d hd hb) _
      (lowerLevel_zero_window (by omega) hd hb) hnear).le

/-- The reciprocal F5 sum is unchanged in the limit by removing the logarithmic loss.
CONDITIONAL ON IsLinearSieve only. No two dimensional integral limit is used. -/
theorem reciprocalFullSum5_shift_small (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      |reciprocalFullSum5 f B N - reciprocalFullSum5 f 0 N| ≤ ε := by
  obtain ⟨K, hK, M, hM⟩ := fullPairs5_mass_bounded
  obtain ⟨J, hJ⟩ := lower_values_shift_small F f h B hB (ε / K) (by positivity)
  refine ⟨max M J, ?_⟩
  intro N hN
  have he : reciprocalFullSum5 f B N - reciprocalFullSum5 f 0 N =
      ∑ p ∈ fullPairs5 N,
        (f (lowerLevel B N (p.1 * p.2)) - f (lowerLevel 0 N (p.1 * p.2))) /
          ((p.1 : ℝ) * p.2) := by
    simp only [reciprocalFullSum5, ← sum_sub_distrib, sub_div]
  rw [he]
  calc
    _ ≤ ∑ p ∈ fullPairs5 N,
        |(f (lowerLevel B N (p.1 * p.2)) - f (lowerLevel 0 N (p.1 * p.2))) /
          ((p.1 : ℝ) * p.2)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ fullPairs5 N, (ε / K) * (1 / ((p.1 : ℝ) * p.2)) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hd, hb⟩ := fullPairs5_product hp
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p.1 : ℝ) * p.2)]
      simpa only [div_eq_mul_inv, one_mul] using
        div_le_div_of_nonneg_right (hJ N (by omega) _ hd hb)
          (by positivity : (0 : ℝ) ≤ (p.1 : ℝ) * p.2)
    _ = (ε / K) * pairMass (fullPairs5 N) := by simp only [pairMass, mul_sum]
    _ ≤ (ε / K) * K := mul_le_mul_of_nonneg_left (hM N (by omega)) (by positivity)
    _ = ε := by field_simp

/-- The actual F5 limit is reduced to the zero loss reciprocal sum limit.
CONDITIONAL ON IsLinearSieve and the explicit zero loss integral limit. -/
theorem lowerSum5_of_zero_loss (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B)
    (hzero : Tendsto (reciprocalFullSum5 f 0) evenAtTop (𝓝 (lowerIntegral5 f))) :
    Tendsto (lowerSum5 f B) evenAtTop (𝓝 (lowerIntegral5 f)) := by
  apply lowerSum5_of_reciprocal F f h B hB
  have hd : Tendsto (fun N => dist (reciprocalFullSum5 f 0 N)
      (reciprocalFullSum5 f B N)) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨K, hK⟩ := reciprocalFullSum5_shift_small F f h B hB (ε / 2) (by positivity)
    refine ⟨K, ?_⟩
    intro N hN
    simpa only [Real.dist_eq, sub_zero, abs_abs, abs_sub_comm] using
      (hK N hN).trans_lt (by linarith : ε / 2 < ε)
  exact hzero.congr_dist (tendsto_inf_left hd)

end LeanLab.ChenDoubleSieve.Task367
