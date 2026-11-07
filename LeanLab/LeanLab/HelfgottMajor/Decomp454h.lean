import LeanLab.HelfgottMajor.Decomp388a
import LeanLab.HelfgottMajor.ZeroCount1623

/-!
Elementary supplies for remaining sibling leaves in the assigned folder.
Source P0014 page 38 display 4.26 and page 43 display 4.42.
The sibling files are unchanged for their file reviewers to repoint.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp454h
open Real Decomp388a

/-- Both closed Gaussian energy constants in P0014 display 4.42 are nonnegative. -/
theorem leaf_plancherel_constants_nonneg : 0 ≤ Sec45.nTwo ∧ 0 ≤ Sec45.nLog := by
  constructor
  · unfold Sec45.nTwo
    positivity
  · unfold Sec45.nLog
    have heq : π ^ 2 + 2 * eulerMascheroniConstant ^ 2 +
        8 * eulerMascheroniConstant * log 2 + 8 * log 2 ^ 2 =
          π ^ 2 + 2 * (eulerMascheroniConstant + 2 * log 2) ^ 2 := by ring
    rw [heq]
    positivity

/-- The elementary square root assembly used for Gaussian energies in display 4.42. -/
theorem leaf_sqrt_sum_le (a b T : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (_hT : 0 ≤ T) :
    sqrt (a + b) * sqrt T ≤ sqrt a * sqrt T + sqrt b * sqrt T := by
  have h : sqrt (a + b) ≤ sqrt a + sqrt b := by
    apply (sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_sqrt ha, sq_sqrt hb, mul_nonneg (sqrt_nonneg a) (sqrt_nonneg b)]
  simpa only [add_mul] using mul_le_mul_of_nonneg_right h (sqrt_nonneg T)

/-- The plane indexed multiplicity count is nondecreasing with the height.
Derived bookkeeping for P0014 page 38, display 4.26.
-/
theorem zeroCount_mono_height (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    {s t : ℝ} (hst : s ≤ t) : zeroCount χ s ≤ zeroCount χ t := by
  classical
  have hs (u : ℝ) : Summable (zeroWeight χ u) := by
    apply summable_of_hasFiniteSupport
    apply (ZeroCount1623.stripZeros_finite χ u).subset
    intro ρ hρ
    by_contra hz
    have hz' : ¬(DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ u) := hz
    have hzero : zeroWeight χ u ρ = 0 := by simp [zeroWeight, Set.indicator, hz']
    exact hρ hzero
  apply (hs s).tsum_le_tsum _ (hs t)
  intro ρ
  by_cases hz : DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ s
  · have hzt : DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ t :=
      ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.trans hst⟩
    simp [zeroWeight, hz, hzt]
  · simp only [zeroWeight, Set.indicator, Set.mem_ofPred_eq, hz, ite_false]
    split_ifs <;> positivity

/-- The short height scalar budget is smallest at its upper endpoint.
Derived arithmetic for the short range of P0014 page 38, display 4.26.
-/
theorem short_height_endpoint_le (q : ℕ) [NeZero q] (t : ℝ) (ht : 1 ≤ t)
    (hqt : q * t ≤ 2 * π) :
    0.5 * log (2 * π) + 17.7 - (2 / q) * log (2 * π * exp 1) ≤
      0.5 * log (q * t) + 17.7 - (t / π) * log (2 * π * exp 1) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have ht0 : 0 < t := by linarith
  let A : ℝ := 2 * π / q
  have hA : 0 < A := by dsimp [A]; positivity
  have hta : t ≤ A := (le_div_iff₀ hq).mpr (by nlinarith [hqt])
  have hlog : log A - log t ≤ (A - t) / t := by
    have h := log_le_sub_one_of_pos (div_pos hA ht0)
    rw [log_div hA.ne' ht0.ne'] at h
    convert h using 1
    field_simp
  have hlog' : log A - log t ≤ A - t :=
    hlog.trans (div_le_self (sub_nonneg.mpr hta) ht)
  have heq : log (2 * π) - log ((q : ℝ) * t) = log A - log t := by
    dsimp only [A]
    rw [log_div (by positivity) hq.ne', log_mul hq.ne' ht0.ne']
    ring
  have hL : π / 2 ≤ log (2 * π * exp 1) := by
    rw [log_mul (by positivity : (2 * π : ℝ) ≠ 0) (exp_ne_zero 1), log_exp]
    linarith [LeanLab.HelfgottMajor.log_two_pi_gt, pi_lt_four]
  have hmul := mul_le_mul_of_nonneg_left hL (sub_nonneg.mpr hta)
  have haeq : 2 / (q : ℝ) = A / π := by dsimp [A]; field_simp
  rw [haeq]
  have hlog2 : log (2 * π) - log ((q : ℝ) * t) ≤ A - t := by rw [heq]; exact hlog'
  have hdiv := (div_le_div_of_nonneg_right hmul pi_pos.le)
  have hid : (A - t) * (π / 2) / π = (A - t) / 2 := by field_simp
  rw [hid] at hdiv
  have hid2 : (A - t) * log (2 * π * exp 1) / π =
      (A / π - t / π) * log (2 * π * exp 1) := by ring
  rw [hid2] at hdiv
  linarith

end LeanLab.HelfgottMajor.Decomp454h
