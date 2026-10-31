import LeanLab.GoldbachAverage.Decomp124

/-!
A negative result for reusing the Theorem 2 envelope in the proof of Theorem 3.
P0098 pages 162, 163 and 167 use two different sampling scales.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.SamplingLimit124

/-- The square root x log x envelope is not bounded by a constant times square root x.
Source context: the two distinct sampling scales on P0098 page 167.
This is a limitation of the envelope, not a claim that a sampled set violates a bound. -/
theorem sqrt_log_envelope_exceeds (C : ℝ) :
    ∃ x : ℝ, 2 ≤ x ∧ C * Real.sqrt x < Real.sqrt (x * Real.log x) := by
  let x := Real.exp ((|C| + 2) ^ 2)
  have hc : 0 ≤ |C| + 2 := by positivity
  have hlog : Real.log x = (|C| + 2) ^ 2 := Real.log_exp _
  have hsq : 4 ≤ (|C| + 2) ^ 2 := by nlinarith [abs_nonneg C]
  have hex := Real.add_one_le_exp ((|C| + 2) ^ 2)
  have hx : 2 ≤ x := by dsimp [x]; linarith
  refine ⟨x, hx, ?_⟩
  rw [Real.sqrt_mul (by linarith : 0 ≤ x), hlog, Real.sqrt_sq hc]
  have hp : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hlt : C < |C| + 2 := by linarith [le_abs_self C]
  nlinarith [mul_pos hp (sub_pos.mpr hlt)]

/-- No constant removes the log factor from the Theorem 2 envelope.
Source context: P0098 page 167, the Theorem 2 route alone cannot prove Theorem 3. -/
theorem no_uniform_sqrt_envelope :
    ¬ ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → Real.sqrt (x * Real.log x) ≤ C * Real.sqrt x := by
  rintro ⟨C, hC⟩
  obtain ⟨x, hx, hlt⟩ := sqrt_log_envelope_exceeds C
  exact (not_lt_of_ge (hC x hx)) hlt

end LeanLab.GoldbachAverage.SamplingLimit124
