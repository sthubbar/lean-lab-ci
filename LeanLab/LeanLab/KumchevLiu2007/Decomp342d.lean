/-
The cutoff comparison in the proof of display 50 on page 14.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp342c
import LeanLab.KumchevLiu2007.Decomp292c

namespace LeanLab.KumchevLiu2007.Task342d

open Real

/-- Page 14 proof of display 50. Exact cutoff order supply with an explicit threshold. -/
theorem cutoff_order (ε : ℝ) (hε : 0 < ε) :
    ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      Q ≤ y ^ (1 / 3 : ℝ) := by
  refine ⟨max 2 (Real.exp ((3 / ε) ^ ε⁻¹)), le_max_left _ _, ?_⟩
  intro x y Q hx hy hQ
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hxpos : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hlarge : (3 / ε) ^ ε⁻¹ ≤ Real.log x := by
    have h := (le_max_right _ _).trans hx
    rw [← Real.exp_log hxpos] at h
    exact Real.exp_le_exp.mp h
  have hpow : 3 / ε ≤ Real.log x ^ ε := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ (3 / ε) ^ ε⁻¹) hlarge hε.le
    rwa [Real.rpow_inv_rpow (by positivity) hε.ne'] at h
  have harg : Real.log x ^ (1 - ε) ≤ Real.log x * (ε / 3) := by
    rw [Real.rpow_sub hl, Real.rpow_one]
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hl ε)]
    have h := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ ε / 3)
    have hconst : (ε / 3) * (3 / ε) = 1 := by field_simp
    rw [hconst] at h
    nlinarith
  calc
    Q ≤ Real.exp (Real.log x ^ (1 - ε)) := hQ
    _ ≤ Real.exp (Real.log x * (ε / 3)) := Real.exp_le_exp.mpr harg
    _ = x ^ (ε / 3) := (Real.rpow_def_of_pos hxpos _).symm
    _ = (x ^ ε) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_mul hxpos.le]
      congr 1
      ring
    _ ≤ y ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hy (by norm_num)

end LeanLab.KumchevLiu2007.Task342d
