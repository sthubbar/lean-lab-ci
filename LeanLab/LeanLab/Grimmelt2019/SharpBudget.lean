/-
AI wrote this Lean code for CODEX task03.
P0074, pages 13 and 14, the log-power saving in the character error.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.ConvolutionSharp

namespace LeanLab.Grimmelt2019.MainTerm
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

/-- The sharp error gives the paper's negative A over two log power plus an endpoint term. -/
theorem sharp_log_power_bound {L Y A K cν cω E : ℝ} {Q : ℕ}
    (hL : 1 ≤ L) (hY : 0 ≤ Y) (hK : 0 ≤ K) (hcν : 0 ≤ cν) (hE : 0 ≤ E)
    (hQ : (Q : ℝ) ≤ L ^ A) (hEb : E ≤ K * Y * L ^ (-2 * A)) :
    cν * (Q : ℝ) * Real.sqrt Q * (2 * E + |cω|) ≤
      2 * cν * K * Y * L ^ (-A / 2) + cν * |cω| * L ^ (3 * A / 2) := by
  have hLp : 0 < L := by linarith
  have hsqrt : Real.sqrt Q ≤ L ^ (A / 2) := by
    calc
      _ ≤ Real.sqrt (L ^ A) := Real.sqrt_le_sqrt hQ
      _ = (L ^ A) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
      _ = L ^ (A / 2) := by rw [← Real.rpow_mul hLp.le]; congr 1; ring
  have hQpow : (Q : ℝ) * Real.sqrt Q ≤ L ^ (3 * A / 2) := by
    calc
      _ ≤ L ^ A * L ^ (A / 2) := mul_le_mul hQ hsqrt (Real.sqrt_nonneg _) (by positivity)
      _ = L ^ (3 * A / 2) := by rw [← Real.rpow_add hLp]; congr 1; ring
  have hprod : L ^ (3 * A / 2) * L ^ (-2 * A) = L ^ (-A / 2) := by
    rw [← Real.rpow_add hLp]
    congr 1
    ring
  calc
    _ ≤ (cν * L ^ (3 * A / 2)) * (2 * (K * Y * L ^ (-2 * A)) + |cω|) := by
      apply mul_le_mul
      · nlinarith only [mul_le_mul_of_nonneg_left hQpow hcν]
      · linarith
      · positivity
      · positivity
    _ = 2 * cν * K * Y * (L ^ (3 * A / 2) * L ^ (-2 * A)) +
        cν * |cω| * L ^ (3 * A / 2) := by ring
    _ = _ := by rw [hprod]

/-- The normalized sharp error tends to zero for each positive A. -/
theorem sharp_error_eventually_small {A : ℝ} (hA : 0 < A) (C D ε : ℝ) (hε : 0 < ε) :
    ∃ Y0 : ℝ, ∀ Y : ℝ, Y0 ≤ Y →
      C * Real.log Y ^ (-A / 2) + D * Real.log Y ^ (3 * A / 2) / Y ≤ ε := by
  have h1 : Tendsto (fun Y : ℝ => Real.log Y ^ (-A / 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop (show 0 < A / 2 by linarith)).comp Real.tendsto_log_atTop
  have h2 : Tendsto (fun Y : ℝ => Real.log Y ^ (3 * A / 2) / Y) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (3 * A / 2) (show 0 < (1 : ℝ) by norm_num)).tendsto_div_nhds_zero
  have ht : Tendsto (fun Y : ℝ => C * Real.log Y ^ (-A / 2) +
      D * (Real.log Y ^ (3 * A / 2) / Y)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using
      (tendsto_const_nhds.mul h1).add (tendsto_const_nhds.mul h2)
  have he := (tendsto_order.mp ht).2 ε hε
  obtain ⟨Y0, hY0⟩ := eventually_atTop.mp he
  refine ⟨Y0, fun Y hY => ?_⟩
  have h := (hY0 Y hY).le
  simpa only [mul_div_assoc] using h

/-- The sharp error leaves half of a positive main term for large Y. -/
theorem sharp_budget_eventually {A K cν cω s0 : ℝ} (hA : 0 < A)
    (hK : 0 ≤ K) (hcν : 0 < cν) (hcω : 0 < cω) (hs0 : 0 < s0) :
    ∃ Y0 : ℝ, ∀ Y : ℝ, Y0 ≤ Y → ∀ (Q : ℕ) (E : ℝ), 0 ≤ E →
      (Q : ℝ) ≤ Real.log Y ^ A → E ≤ K * Y * Real.log Y ^ (-2 * A) →
      (cν * cω * s0 / 2) * Y ≤ cν * cω * Y * s0 -
        cν * (Q : ℝ) * Real.sqrt Q * (2 * E + |cω|) := by
  let ε := cν * cω * s0 / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨Y0, hY0⟩ := sharp_error_eventually_small hA
    (2 * cν * K) (cν * |cω|) ε hε
  refine ⟨max Y0 (Real.exp 1), ?_⟩
  intro Y hY Q E hE hQ hEb
  have hYe : Real.exp 1 ≤ Y := (le_max_right _ _).trans hY
  have hYp : 0 < Y := (Real.exp_pos _).trans_le hYe
  have hlog : 1 ≤ Real.log Y := (Real.le_log_iff_exp_le hYp).mpr hYe
  have hsmall := hY0 Y ((le_max_left _ _).trans hY)
  have hscaled := mul_le_mul_of_nonneg_right hsmall hYp.le
  have hid : (2 * cν * K * Real.log Y ^ (-A / 2) +
      cν * |cω| * Real.log Y ^ (3 * A / 2) / Y) * Y =
      2 * cν * K * Y * Real.log Y ^ (-A / 2) +
      cν * |cω| * Real.log Y ^ (3 * A / 2) := by
    field_simp
    <;> ring
  rw [hid] at hscaled
  have hb := sharp_log_power_bound (cω := cω) hlog hYp.le hK hcν.le hE hQ hEb
  dsimp [ε] at hscaled
  nlinarith only [hb, hscaled]

#print axioms sharp_budget_eventually
#print axioms sharp_log_power_bound
#print axioms sharp_error_eventually_small
end LeanLab.Grimmelt2019.MainTerm
