/-
The angular gap in the outer Mellin kernel is positive for fixed N.
It has no positive lower bound uniform in N at frequency one.
Source: original page 157, argument identity preceding equation 4.4.
This concerns a split explanation. It is not a paper error.
-/
import LeanLab.Linnik1951.SPLIT_abstract_outer_kernels442

namespace LeanLab.Linnik1951
open Filter
open scoped Topology

/-- The page 157 angular gap at frequency one tends to zero as N tends to infinity. -/
theorem outer_angular_gap_tendsto_zero452 :
    Tendsto (fun N : ℕ => Real.pi / 2 -
      Complex.arg (((1 / (N : ℝ) : ℝ) : ℂ) +
        ((2 * Real.pi : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => (1 / (N : ℝ))) atTop (𝓝 0) := by
    exact tendsto_one_div_atTop_nhds_zero_nat
  have hz : Tendsto (fun N : ℕ => (((1 / (N : ℝ) : ℝ) : ℂ) +
      ((2 * Real.pi : ℝ) : ℂ) * Complex.I)) atTop
      (𝓝 (((2 * Real.pi : ℝ) : ℂ) * Complex.I)) := by
    simpa using (Complex.continuous_ofReal.tendsto 0 |>.comp hinv).add_const
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I)
  have hslit : (((2 * Real.pi : ℝ) : ℂ) * Complex.I) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
    exact ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.pi)
  have harg : Complex.arg (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = Real.pi / 2 := by
    apply Complex.arg_eq_pi_div_two_iff.mpr
    constructor
    · simp
    · simp; positivity
  simpa only [Function.comp_def, harg, sub_self] using
    ((tendsto_const_nhds (x := Real.pi / 2)).sub
      ((Complex.continuousAt_arg hslit).tendsto.comp hz))

/-- No fixed positive angular gap holds for every sufficiently large N at frequency one. -/
theorem outer_angular_gap_not_uniform452 :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      δ ≤ Real.pi / 2 - Complex.arg (((1 / (N : ℝ) : ℝ) : ℂ) +
        ((2 * Real.pi : ℝ) : ℂ) * Complex.I) := by
  rintro ⟨δ, hδ, hbound⟩
  have hle : δ ≤ 0 := ge_of_tendsto outer_angular_gap_tendsto_zero452 hbound
  linarith

/-- Frequency one lies in the outer interval for R one at every N at least four. -/
theorem outer_frequency_one_admissible452 (N : ℕ) (hN : 4 ≤ N) :
    1 ≤ (N : ℝ) ^ (2 / 7 : ℝ) ∧
      (1 : ℝ) ∈ Set.Icc (4 / (N : ℝ)) (1 / (1 : ℝ)) := by
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
  constructor
  · exact Real.one_le_rpow (by linarith) (by norm_num)
  · constructor
    · exact (div_le_one (by linarith : (0 : ℝ) < N)).mpr hn
    · norm_num

/-- Page 157 angular identity with an explicit upper bound for its gap. -/
theorem angular_gap_le_ratio452 (z : ℂ) (hr : 0 < z.re) (hi : 0 < z.im) :
    Real.pi / 2 - z.arg ≤ z.re / z.im := by
  have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr)
  have ha : z.arg = Real.arctan (z.im / z.re) := by
    rw [← Complex.tan_arg]
    exact (Real.arctan_tan (abs_lt.mp harg).1 (abs_lt.mp harg).2).symm
  rw [ha, ← Real.arctan_inv_of_pos (div_pos hi hr), inv_div]
  exact Real.arctan_le_self (div_nonneg hr.le hi.le)

end LeanLab.Linnik1951
