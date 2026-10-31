/-
P0017 p. 1748 Section 6: the conjectured upper bound on the least Goldbach prime
implies divergence of log n divided by the square of log p of n.
The theorem isolates the analytic implication for an arbitrary index filter.
The conjectured bound is an explicit hypothesis. It is not proved here.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import Mathlib
open Filter
open scoped Topology
namespace LeanLab.Richstein2001

/-- LEAF. P0017 p. 1748 Section 6, last sentence.
CONDITIONAL ON the eventual growth bound and on p being at least 2.
The bound forces the logarithmic quotient to tend to infinity. -/
theorem quotient_tendsto116 {α : Type*} {l : Filter α} (x p : α → ℝ)
    (hx : Tendsto x l atTop) (C : ℝ) (hC : 0 < C)
    (hp : ∀ᶠ a in l, 2 ≤ p a ∧
      p a ≤ C * Real.log (x a) ^ 2 * Real.log (Real.log (x a))) :
    Tendsto (fun a => Real.log (x a) / Real.log (p a) ^ 2) l atTop := by
  let K : ℝ := |Real.log C| + 3
  have hl : Tendsto (fun a => Real.log (x a)) l atTop := Real.tendsto_log_atTop.comp hx
  have hll : Tendsto (fun a => Real.log (Real.log (x a))) l atTop := Real.tendsto_log_atTop.comp hl
  have hsmall : Tendsto (fun a => K ^ 2 * (Real.log (Real.log (x a)) ^ 2 / Real.log (x a)))
      l (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 (by norm_num)).comp hl
    simpa using h.const_mul (K ^ 2)
  have hpos : ∀ᶠ a in l, 0 < Real.log (p a) ^ 2 / Real.log (x a) := by
    filter_upwards [hp, hl.eventually_gt_atTop 0] with a hpa hlogx
    have hlogp : 0 < Real.log (p a) := Real.log_pos (by linarith [hpa.1])
    positivity
  have hle : ∀ᶠ a in l,
      Real.log (p a) ^ 2 / Real.log (x a) ≤ K ^ 2 *
        (Real.log (Real.log (x a)) ^ 2 / Real.log (x a)) := by
    filter_upwards [hp, hl.eventually_gt_atTop 0, hll.eventually_ge_atTop 1]
      with a hpa hlogx hloglogx
    have hpx : 0 < p a := by linarith [hpa.1]
    have hlogp : 0 < Real.log (p a) := Real.log_pos (by linarith [hpa.1])
    have hpoly : p a ≤ C * Real.log (x a) ^ 3 := by
      calc p a ≤ C * Real.log (x a) ^ 2 * Real.log (Real.log (x a)) := hpa.2
           _ ≤ C * Real.log (x a) ^ 2 * Real.log (x a) :=
             mul_le_mul_of_nonneg_left (Real.log_le_self hlogx.le) (by positivity)
           _ = C * Real.log (x a) ^ 3 := by ring
    have hlogbound : Real.log (p a) ≤ Real.log C + 3 * Real.log (Real.log (x a)) := by
      have h := Real.log_le_log hpx hpoly
      rw [Real.log_mul (ne_of_gt hC) (by positivity), Real.log_pow] at h
      norm_num at h ⊢
      exact h
    have hconst : Real.log C ≤ |Real.log C| * Real.log (Real.log (x a)) := by
      calc Real.log C ≤ |Real.log C| := le_abs_self _
           _ ≤ |Real.log C| * Real.log (Real.log (x a)) := by
             nlinarith [abs_nonneg (Real.log C)]
    have hb : Real.log (p a) ≤ K * Real.log (Real.log (x a)) := by
      dsimp [K]
      nlinarith
    have hsq := pow_le_pow_left₀ hlogp.le hb 2
    calc Real.log (p a) ^ 2 / Real.log (x a) ≤
          (K * Real.log (Real.log (x a))) ^ 2 / Real.log (x a) :=
            div_le_div_of_nonneg_right hsq hlogx.le
         _ = _ := by ring
  have hz : Tendsto (fun a => Real.log (p a) ^ 2 / Real.log (x a)) l (𝓝 0) :=
    squeeze_zero' (hpos.mono fun _ h => h.le) hle hsmall
  have hgt : Tendsto (fun a => Real.log (p a) ^ 2 / Real.log (x a)) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz, hpos⟩
  have hi := hgt.inv_tendsto_nhdsGT_zero
  change Tendsto (fun a => (Real.log (p a) ^ 2 / Real.log (x a))⁻¹) l atTop at hi
  simpa only [inv_div] using hi
end LeanLab.Richstein2001
