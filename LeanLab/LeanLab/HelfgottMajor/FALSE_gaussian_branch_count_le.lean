import LeanLab.HelfgottMajor.FALSE_feed1122_exp_branch_tsum_le

/-!
Conditional Lean refutation of `SplitGaussian123.gaussian_branch_count_le` of DecompF547.lean,
route burst S1 burst-20261124. No existing file is edited and no statement is changed.

The leaf bounds the one sided sum over strip zeros above T of the multiplicity times
exp of minus 0.1065 times the square of Im ρ over pi abs delta by `gaussianTailIntegral q δ T`,
the integral of the same weight against the bare density of display 4.35, P0014 page 41. The
Gaussian weight falls by a large factor over a short height, so a single zero just above T
outweighs the whole integral, which `TailIntegral123.gaussian_integral_bound` bounds by
0.18787 abs delta log(qT/2π) times the weight at T. This is the boundary term that page 38
drops after display 4.28; the audit notes/burst-20261122/HelfgottMajor-tail_branch_audit.md,
unit P1122-0039, found the leaf false numerically, falsifier AGREE.

For q = 1 the character is trivial and `L` is the Riemann zeta function. Its 30th zero has
ordinate 101.317851..., inside the window from 101.3 to 101.32 used below; Mathlib records no
nontrivial zeta zero, so the existence of that zero is the explicit hypothesis `hzero`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1124GaussianBranch
open Real

/-- Conditional refutation of `SplitGaussian123.gaussian_branch_count_le`, general form. If a
zero of `L(·, χ)` in the open strip lies above the cutoff `T` so close to it that its own Gaussian
weight beats the PROVED upper bound `TailIntegral123.gaussian_integral_bound` of the tail
integral, P0014 page 42 displays 4.37 to 4.41, then the conjunction of summability and the
bound fails: the weighted sum is at least the one term of that zero, multiplicity at least one. -/
theorem refute_general (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hδ : δ ≠ 0) (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzero : ∃ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < ρ.im ∧
      0.18787 * |δ| * log (q * T / (2 * π)) * exp (-0.1065 * (T / (π * |δ|)) ^ 2) <
        exp (-0.1065 * (ρ.im / (π * |δ|)) ^ 2)) :
    ¬ (Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im} =>
          (ZeroCount1623.mult χ ρ.val : ℝ) *
            if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2)) ∧
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) *
            if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2)) ≤
        TailIntegral123.gaussianTailIntegral q δ T) := by
  rintro ⟨hs, hle⟩
  obtain ⟨ρ, hρ, h0, h1, hTim, hlt⟩ := hzero
  have hT0 : (0 : ℝ) < T := by
    have := (le_max_right _ _).trans hT; linarith
  have him : 0 < ρ.im := hT0.trans hTim
  let ρ' : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im} := ⟨ρ, hρ, h0, h1, him, hTim⟩
  have hterm := hs.le_tsum ρ' (fun _ _ => by
    simp only [hδ, ite_false]; positivity)
  have hm : (1 : ℝ) ≤ (ZeroCount1623.mult χ ρ : ℝ) := by
    exact_mod_cast Feed1122ExpBranch.one_le_mult_feed χ hρ h1
  have hbound := TailIntegral123.gaussian_integral_bound q δ T hδ hT
  have hge : Real.exp (-0.1065 * (ρ.im / (π * |δ|)) ^ 2) ≤
      (ZeroCount1623.mult χ ρ'.val : ℝ) *
        (if δ = 0 then 0 else Real.exp (-0.1065 * (ρ'.val.im / (π * |δ|)) ^ 2)) := by
    simp only [hδ, ite_false]
    have := Real.exp_pos (-0.1065 * (ρ.im / (π * |δ|)) ^ 2)
    show _ ≤ (ZeroCount1623.mult χ ρ : ℝ) * _
    nlinarith
  linarith [hge.trans (hterm.trans (hle.trans hbound))]

/-- The numerical inequality of the instance q = 1, delta = 1, T = 101.3: for a height at most
101.32 the Gaussian weight exceeds 0.18787 log(101.3/2π) times the weight at 101.3. -/
theorem concrete_ineq (γ : ℝ) (h1 : 101.3 < γ) (h2 : γ ≤ 101.32) :
    0.18787 * |(1 : ℝ)| * log (((1 : ℕ) : ℝ) * 101.3 / (2 * π)) *
        exp (-0.1065 * (101.3 / (π * |(1 : ℝ)|)) ^ 2) <
      exp (-0.1065 * (γ / (π * |(1 : ℝ)|)) ^ 2) := by
  have hpi3 := pi_gt_three
  have hpi4 := pi_lt_four
  simp only [abs_one, mul_one, Nat.cast_one, one_mul]
  have hlog : log (101.3 / (2 * π)) < 3 := by
    rw [Real.log_lt_iff_lt_exp (by positivity)]
    have he := Real.exp_one_gt_d9
    have h3 : exp 3 = exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3, div_lt_iff₀ (by positivity)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) he.le 3]
  have hlog0 : 0 ≤ log (101.3 / (2 * π)) := Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
  set A := (101.3 / π) ^ 2
  set B := (γ / π) ^ 2
  have hBA : B - A ≤ 0.46 := by
    simp only [A, B, div_pow]
    rw [← sub_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hsplit : exp (-0.1065 * B) = exp (-0.1065 * A) * exp (-(0.1065 * (B - A))) := by
    rw [← Real.exp_add]; ring_nf
  have hex : 1 - 0.1065 * (B - A) ≤ exp (-(0.1065 * (B - A))) := by
    have := Real.add_one_le_exp (-(0.1065 * (B - A))); linarith
  have hEA := Real.exp_pos (-0.1065 * A)
  rw [hsplit]
  have : 0.18787 * log (101.3 / (2 * π)) < exp (-(0.1065 * (B - A))) := by nlinarith
  nlinarith
/-- Conditional refutation of `gaussian_branch_count_le` at q = 1, delta = 1, T = 101.3, for any
character mod 1, so for the Riemann zeta function, given one zero of `L` in the open strip with
ordinate in the window from 101.3 to 101.32, as the 30th zeta zero 1/2 + 101.317851... i. -/
theorem FALSE_gaussian_branch_count_le (χ : DirichletCharacter ℂ 1)
    (hzero : ∃ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ 101.3 < ρ.im ∧ ρ.im ≤ 101.32) :
    ¬ (Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ (101.3 : ℝ) < ρ.im} =>
          (ZeroCount1623.mult χ ρ.val : ℝ) *
            if (1 : ℝ) = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |(1 : ℝ)|)) ^ 2)) ∧
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ (101.3 : ℝ) < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) *
            if (1 : ℝ) = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |(1 : ℝ)|)) ^ 2)) ≤
        TailIntegral123.gaussianTailIntegral (1 : ℕ) 1 101.3) := by
  obtain ⟨ρ, hρ, h0, h1, hlo, hhi⟩ := hzero
  have hT : max (4 * π ^ 2 * |(1 : ℝ)|) 100 ≤ (101.3 : ℝ) := by
    have := pi_lt_four
    have h3 : (0 : ℝ) < π := pi_pos
    rw [abs_one, mul_one, max_le_iff]
    constructor
    · have : π < 3.2 := by linarith [pi_lt_d2]
      nlinarith
    · norm_num
  exact refute_general 1 χ 1 101.3 one_ne_zero hT
    ⟨ρ, hρ, h0, h1, hlo, concrete_ineq ρ.im hlo hhi⟩

/-- The same refutation against the universally quantified sealed statement. -/
theorem FALSE_gaussian_branch_count_le_forall
    (hzero : ∃ ρ : ℂ, DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ 101.3 < ρ.im ∧ ρ.im ≤ 101.32) :
    ¬ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ),
      max (4 * π ^ 2 * |δ|) 100 ≤ T →
      Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im} =>
          (ZeroCount1623.mult χ ρ.val : ℝ) *
            if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2)) ∧
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) *
            if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2)) ≤
        TailIntegral123.gaussianTailIntegral q δ T := by
  intro h
  have hT : max (4 * π ^ 2 * |(1 : ℝ)|) 100 ≤ (101.3 : ℝ) := by
    have h3 : (0 : ℝ) < π := pi_pos
    rw [abs_one, mul_one, max_le_iff]
    constructor
    · have : π < 3.2 := by linarith [pi_lt_d2]
      nlinarith
    · norm_num
  exact FALSE_gaussian_branch_count_le 1 hzero (h 1 1 1 101.3 hT)

end LeanLab.HelfgottMajor.Feed1124GaussianBranch
