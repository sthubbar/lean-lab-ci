import LeanLab.ExceptionalSet.Decomp462f

/-!
P0082 page 359, audit of the formal Vaaler approximation split.
Source: https://doi.org/10.5802/aif.1621
The paper omits the discrepancy argument and does not assert this uniform approximation.
The formal auxiliary contradicts continuity at the jump of an interval indicator.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp462h

open Real MeasureTheory Filter Topology
open LeanLab.ExceptionalSet.U1539 (eC)
/-- P0082 page 359, audit of a formal auxiliary that the paper does not state.
At degree four and the half interval, the claimed uniform error two fifths
contradicts continuity at the right endpoint. This is a QUESTION about the
formal split only. No paper error is asserted. -/
theorem not_vaaler_trig_majorant_at_four :
    ¬ (∃ c : ℕ → ℂ, (∀ h ∈ Finset.Icc 1 4, ‖c h‖ ≤ 2 / ((h : ℝ) + 1)) ∧
      ∀ θ : ℝ, |(if (0 : ℝ) ≤ Int.fract θ ∧ Int.fract θ < 1 / 2 then (1 : ℝ) else 0) - (1 / 2 - 0)
        - ∑ h ∈ Finset.Icc 1 4, (c h * eC (h * θ)).re| ≤ 2 / ((4 : ℝ) + 1)) := by
  rintro ⟨c, hc, happrox⟩
  let P : ℝ → ℝ := fun θ => ∑ h ∈ Finset.Icc 1 4, (c h * eC (h * θ)).re
  have hP : Continuous P := by unfold P eC; fun_prop
  have hinside (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1 / 2) : (1 / 10 : ℝ) ≤ P θ := by
    have hfr : Int.fract θ = θ := Int.fract_eq_self.mpr ⟨hθ0, by linarith⟩
    have h := happrox θ
    rw [hfr, if_pos ⟨hθ0, hθ1⟩] at h
    have hh := (abs_le.mp h).2
    change _ - _ - P θ ≤ _ at hh
    norm_num at hh
    linarith
  let u : ℕ → ℝ := fun n => 1 / 2 - (1 / 2) * (1 / ((n : ℝ) + 1))
  have hu (n : ℕ) : 0 ≤ u n ∧ u n < 1 / 2 := by
    have hp : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    have hle : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
    dsimp only [u]
    constructor <;> linarith
  have hlim : Tendsto u atTop (nhds (1 / 2 : ℝ)) := by
    simpa only [mul_zero, sub_zero] using
      (tendsto_const_nhds.sub
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2)))
  have hclosed : IsClosed {θ : ℝ | (1 / 10 : ℝ) ≤ P θ} := isClosed_le continuous_const hP
  have hlo : (1 / 10 : ℝ) ≤ P (1 / 2) :=
    hclosed.mem_of_tendsto hlim (Eventually.of_forall fun n => hinside _ (hu n).1 (hu n).2)
  have h := happrox (1 / 2)
  have hfr : Int.fract (1 / 2 : ℝ) = 1 / 2 := Int.fract_eq_self.mpr (by norm_num)
  rw [hfr, if_neg (by norm_num : ¬ ((0 : ℝ) ≤ (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 / 2))] at h
  change |(0 : ℝ) - (1 / 2 - 0) - P (1 / 2)| ≤ 2 / ((4 : ℝ) + 1) at h
  have hh := (abs_le.mp h).1
  linarith

/-- P0082 page 359, exact negation of the universal formal majorant leaf.
The witness is H four, z1 one half and z2 zero. The original leaf is preserved. -/
theorem not_leaf_vaaler_trig_majorant :
    ¬ (∀ (H : ℕ) (z₁ z₂ : ℝ), 0 ≤ z₂ → z₂ < z₁ → z₁ ≤ 1 →
      ∃ c : ℕ → ℂ, (∀ h ∈ Finset.Icc 1 H, ‖c h‖ ≤ 2 / ((h : ℝ) + 1)) ∧
      ∀ θ : ℝ, |(if z₂ ≤ Int.fract θ ∧ Int.fract θ < z₁ then (1 : ℝ) else 0) - (z₁ - z₂)
        - ∑ h ∈ Finset.Icc 1 H, (c h * eC (h * θ)).re| ≤ 2 / ((H : ℝ) + 1)) := by
  intro h
  exact not_vaaler_trig_majorant_at_four (h 4 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num))

end LeanLab.ExceptionalSet.Decomp462h
