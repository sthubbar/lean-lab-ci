import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LeanLab.KumchevLiu2007.Task701

/-- P0088 page 10, Lemma 3.3, a derived obstruction to the current Perron estimate.
At fixed M K X equal to two, the pointwise remainder majorant asks for T at
least four K. Its logarithm cannot be bounded by a constant times log four
uniformly in K. -/
theorem perron_logarithm_majorant_not_uniform :
    ¬ ∃ C : ℝ, ∀ K : ℕ, 2 ≤ K → Real.log (4 * (K : ℝ)) ≤ C * Real.log 4 := by
  rintro ⟨C, hC⟩
  let K := max 2 ⌈Real.exp (C * Real.log 4 + 1)⌉₊
  have hK : 2 ≤ K := le_max_left _ _
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have heK : Real.exp (C * Real.log 4 + 1) ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 2 ⌈Real.exp (C * Real.log 4 + 1)⌉₊)
  have hL : C * Real.log 4 < Real.log (4 * (K : ℝ)) := by
    apply (Real.lt_log_iff_exp_lt (by positivity)).mpr
    exact (Real.exp_lt_exp.mpr (by linarith)).trans_le (heK.trans (by linarith))
  exact (not_lt_of_ge (hC K hK)) hL

end LeanLab.KumchevLiu2007.Task701
