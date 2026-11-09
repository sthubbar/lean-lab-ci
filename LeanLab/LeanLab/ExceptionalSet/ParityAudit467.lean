import LeanLab.ExceptionalSet.KernelTransform264

/-!
P0082 page370, the literal periodization printed before display40.
The source defines w_e of t as w of two t plus one on page367.
The printed periodization has period one half and is nonzero at three quarters.
This is a QUESTION about that formula, not a refutation of Theorem1.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.ParityAudit467
open LeanLab.ExceptionalSet.KernelTransform264

/-- P0082 page370 before display40, read literally using the page367
formula w_e of t equals w of two t plus one. This is real valued data. -/
noncomputable def printedParityPeriodization (Δ x : ℝ) : ℝ :=
  ∑' k : ℤ, weight Δ (2 * ((k : ℝ) - 2 * x) + 1)

/-- P0082 page370 literal formula. Shifting the argument by one half
shifts its integer summation index by one. -/
theorem printed_half_periodic (Δ : ℝ) :
    Function.Periodic (printedParityPeriodization Δ) (1 / 2) := by
  intro x
  unfold printedParityPeriodization
  calc
    _ = ∑' k : ℤ, weight Δ (2 * (((k + 1 : ℤ) : ℝ) - 2 * (x + 1 / 2)) + 1) :=
      (Equiv.tsum_eq (Equiv.addRight (1 : ℤ)) _).symm
    _ = _ := by
      apply tsum_congr
      intro k
      congr 1
      push_cast
      ring

/-- P0082 page370 literal formula. Exactly one summand survives at three
quarters. Its value is one for every admissible smoothing width. -/
theorem printed_at_three_quarters (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    printedParityPeriodization Δ (3 / 4) = 1 := by
  unfold printedParityPeriodization
  rw [tsum_eq_single (1 : ℤ)]
  · convert weight_one hΔ hΔ1 (show |(0 : ℝ)| ≤ 1 - Δ by simpa using hΔ1.le) using 1; norm_num
  · intro k hk
    apply weight_zero hΔ hΔ1
    have hcases : k ≤ 0 ∨ 2 ≤ k := by omega
    rw [le_abs]
    rcases hcases with hk0 | hk2
    · right
      have hr : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
      linarith
    · left
      have hr : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      linarith

/-- P0082 page370 claim immediately after its literal formula. The printed
function does not vanish on the closed interval from one half to one. -/
theorem not_printed_vanishes (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    ¬ (∀ x ∈ Set.Icc (1 / 2 : ℝ) 1, printedParityPeriodization Δ x = 0) := by
  intro h
  have hc := h (3 / 4) (by norm_num)
  rw [printed_at_three_quarters Δ hΔ hΔ1] at hc
  norm_num at hc

/-- Derived correction of the page370 periodization. Replace k by twice k
inside w_e. The definition has the support properties asserted in the text. -/
noncomputable def correctedParityPeriodization (Δ x : ℝ) : ℝ :=
  ∑' k : ℤ, weight Δ (2 * (2 * (k : ℝ) - 2 * x) + 1)

/-- Derived correction of the page370 periodization. It has period one. -/
theorem corrected_one_periodic (Δ : ℝ) :
    Function.Periodic (correctedParityPeriodization Δ) 1 := by
  intro x
  unfold correctedParityPeriodization
  calc
    _ = ∑' k : ℤ, weight Δ (2 * (2 * ((k + 1 : ℤ) : ℝ) - 2 * (x + 1)) + 1) :=
      (Equiv.tsum_eq (Equiv.addRight (1 : ℤ)) _).symm
    _ = _ := by
      apply tsum_congr
      intro k
      congr 1
      push_cast
      ring

/-- Derived correction of the page370 periodization. Every summand
vanishes on the closed interval from one half to one. -/
theorem corrected_vanishes (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (x : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) 1) :
    correctedParityPeriodization Δ x = 0 := by
  unfold correctedParityPeriodization
  suffices hz : (fun k : ℤ => weight Δ (2 * (2 * (k : ℝ) - 2 * x) + 1)) =
      (fun _ : ℤ => 0) by rw [hz, tsum_zero]
  funext k
  apply weight_zero hΔ hΔ1
  have hk : k ≤ 0 ∨ 1 ≤ k := by omega
  rw [le_abs]
  rcases hk with hk | hk
  · right
    have hr : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    linarith [hx.1]
  · left
    have hr : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith [hx.2]

/-- Derived correction of the page370 periodization. In the interior
plateau from Delta over four to one half minus Delta over four, its value is one. -/
theorem corrected_plateau (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (x : ℝ) (hleft : Δ / 4 ≤ x) (hright : x ≤ 1 / 2 - Δ / 4) :
    correctedParityPeriodization Δ x = 1 := by
  have hx0 : 0 ≤ x := by linarith
  have hxhalf : x ≤ 1 / 2 := by linarith
  unfold correctedParityPeriodization
  rw [tsum_eq_single (0 : ℤ)]
  · apply weight_one hΔ hΔ1
    norm_num only [Int.cast_zero, mul_zero, zero_sub]
    rw [abs_le]
    constructor <;> linarith
  · intro k hk
    apply weight_zero hΔ hΔ1
    have hcases : k ≤ -1 ∨ 1 ≤ k := by omega
    rw [le_abs]
    rcases hcases with hk | hk
    · right
      have hr : (k : ℝ) ≤ -1 := by exact_mod_cast hk
      linarith
    · left
      have hr : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith

/-- Derived correction of the page370 periodization. Its value at one
quarter is one, so its asserted support does not come from a zero function. -/
theorem corrected_at_one_quarter (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    correctedParityPeriodization Δ (1 / 4) = 1 := by
  unfold correctedParityPeriodization
  rw [tsum_eq_single (0 : ℤ)]
  · convert weight_one hΔ hΔ1 (show |(0 : ℝ)| ≤ 1 - Δ by simpa using hΔ1.le) using 1; norm_num
  · intro k hk
    apply weight_zero hΔ hΔ1
    have hcases : k ≤ -1 ∨ 1 ≤ k := by omega
    rw [le_abs]
    rcases hcases with hk0 | hk1
    · right
      have hr : (k : ℝ) ≤ -1 := by exact_mod_cast hk0
      linarith
    · left
      have hr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      linarith

end LeanLab.ExceptionalSet.ParityAudit467
