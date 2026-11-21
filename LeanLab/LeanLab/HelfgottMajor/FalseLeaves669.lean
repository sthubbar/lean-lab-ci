import LeanLab.HelfgottMajor.FALSE_conductor_log_le_quarter_exp

/-!
Audit of DecompF1618 and DecompF1619 against P0014 page 38, display 4.26.
These sealed leaves omit a restriction tying the conductor to the height.
Their statements remain unchanged. These refutations use no admitted zero count.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.FalseLeaves669
open Real

/-- The base height conductor leaf of DecompF1618 is false. The existing explicit witness
for its parent already contradicts it at height one hundred. -/
theorem conductor_base_height_false :
    ¬ ∀ (q : ℕ), q ≠ 0 →
      0.15 * log q + 3.389 ≤ exp (0.6 * (100 : ℝ)) / 4 := by
  intro h
  exact (not_le.mpr FalseConductorLog.conductor_log_gt_quarter_exp_at_witness)
    (h _ FalseConductorLog.witness_log_ge.1)

/-- The first leaf of DecompF1619 is false. At height one hundred the proposed upper bound
is one thousand. The nonzero natural ceiling of exp of one thousand and one exceeds it. -/
theorem log_conductor_height_sq_false :
    ¬ ∀ (q : ℕ), q ≠ 0 → ∀ (t : ℝ), 100 ≤ t →
      log (q : ℝ) ≤ 0.1 * t ^ 2 := by
  intro h
  let q : ℕ := ⌈exp (1001 : ℝ)⌉₊
  have hq : exp (1001 : ℝ) ≤ (q : ℝ) := Nat.le_ceil _
  have hpos : (0 : ℝ) < q := (exp_pos _).trans_le hq
  have hn : q ≠ 0 := by exact_mod_cast hpos.ne'
  have hl : (1001 : ℝ) ≤ log (q : ℝ) := by
    simpa using Real.log_le_log (exp_pos _) hq
  have hw := h q hn 100 le_rfl
  norm_num at hw
  linarith

end LeanLab.HelfgottMajor.FalseLeaves669

#print axioms LeanLab.HelfgottMajor.FalseLeaves669.conductor_base_height_false
#print axioms LeanLab.HelfgottMajor.FalseLeaves669.log_conductor_height_sq_false
