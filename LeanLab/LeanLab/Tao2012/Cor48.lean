/-
Tao 2012, P0007, unit U-0924, run 20261018T0803Z-19871. arXiv 1201.6656 v4, read in
Claude in Chrome, arxiv.org/html/1201.6656, 2026-10-18.

Corollary 4.8 of the paper, Corollary 4.9 in the HTML numbering, and its use in the proof of
Proposition 8.4. The corollary assumes the cutoff is L²-normalised, ‖η‖₂ = 1, and then gives
∫_{‖α‖ ≤ r} |S_{η,q}(x, α)|² dα ≥ 0.94 x. Section 8 applies it to η₁, whose squared L² norm
is 2/3 by (8.2), and prints the lower bound 0.92 x.

This file proves:
* `S_smul`, `sq_integral_smul`: S is linear in the cutoff, so the L² integral scales by c².
* `hyp_48` to `hyp_412`: the corollary's hypotheses (4.8) to (4.12) hold for the
  normalised cutoff √(3/2) η₁ at x ≥ 8.7e36, c = 0.1, r = T₀ / (3.6 π x), T₀ = 3.29e9.
* `scaled_lower`: what the corollary then gives for η₁ is 0.94 · 2/3 x, below 0.92 x.
* `prop84_chain_fails`, `eq817_chain_fails`: with that bound the subtraction in the proof of
  Proposition 8.4 gives more than 7.09, and the Hölder step for (8.17) then exceeds 0.56.

The analytic statements stay cited; only scaling and arithmetic are proved here.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.Tao2012.Cor48

open Real Complex MeasureTheory

/-- The paper's sum `S_{η,q}(x, α) = ∑ Λ(n) 1_{(n,q)=1} η(n/x) e(αn)`, truncated at `N`;
`η` has compact support, so a large enough `N` gives the full sum. -/
noncomputable def S (η : ℝ → ℝ) (q N : ℕ) (x α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N,
    ((ArithmeticFunction.vonMangoldt n : ℝ) * (if Nat.Coprime n q then 1 else 0) *
      η (n / x) : ℝ) * Complex.exp (2 * π * Complex.I * α * n)

/-- `S` is linear in the cutoff. -/
theorem S_smul (c : ℝ) (η : ℝ → ℝ) (q N : ℕ) (x α : ℝ) :
    S (fun t => c * η t) q N x α = c * S η q N x α := by
  unfold S
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  ring

/-- The L² integral over any set scales by `c²`. -/
theorem sq_integral_smul (c : ℝ) (η : ℝ → ℝ) (q N : ℕ) (x : ℝ) (s : Set ℝ) :
    ∫ α in s, ‖S (fun t => c * η t) q N x α‖ ^ 2 =
      c ^ 2 * ∫ α in s, ‖S η q N x α‖ ^ 2 := by
  have : ∀ α, ‖S (fun t => c * η t) q N x α‖ ^ 2 = c ^ 2 * ‖S η q N x α‖ ^ 2 := by
    intro α
    rw [S_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  simp_rw [this]
  exact integral_const_mul _ _

/-- Corollary 4.8 applied to a cutoff of squared L² norm `L2sq`: by scaling to norm one,
a lower bound `0.94 x` for the normalised cutoff is `0.94 · L2sq · x` for the original. -/
theorem scaled_bound {I : ℝ → ℝ} {L2sq x : ℝ} (hL : 0 < L2sq)
    (hI : ∀ c : ℝ, I c = c ^ 2 * I 1)
    (hcor : 0.94 * x ≤ I (1 / Real.sqrt L2sq)) : 0.94 * L2sq * x ≤ I 1 := by
  rw [hI, div_pow, one_pow, Real.sq_sqrt hL.le] at hcor
  have h := mul_le_mul_of_nonneg_left hcor hL.le
  have e : L2sq * (1 / L2sq * I 1) = I 1 := by field_simp
  rw [e] at h
  linarith

/-! ## The hypotheses of Corollary 4.8 for the normalised cutoff `√(3/2) η₁`

Norms from (8.3), (8.7), (8.9), scaled by `√(3/2)`: `‖η‖∞ = √(3/2) ≤ 1.25`, `‖η‖∞⁴ = 9/4`,
`‖ηη'‖₁ = 3/2`, `‖η'η' + ηη''‖₁ = 60`. -/

noncomputable def T0 : ℝ := 3.29e9

theorem sqrt32_le : Real.sqrt (3 / 2) ≤ 1.25 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

theorem sqrt32_pow4 : Real.sqrt (3 / 2) ^ 4 = 9 / 4 := by
  have h : Real.sqrt (3 / 2) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  calc Real.sqrt (3 / 2) ^ 4 = (Real.sqrt (3 / 2) ^ 2) ^ 2 := by ring
    _ = 9 / 4 := by rw [h]; norm_num

/-- (4.8): `c x ≥ 10^8` with `c = 0.1`. -/
theorem hyp_48 {x : ℝ} (hx : 8.7e36 ≤ x) : (1e8 : ℝ) ≤ 0.1 * x := by linarith

/-- (4.9): `x ≥ 10^4 ‖ηη'‖₁ = 10^4 · 3/2`. -/
theorem hyp_49 {x : ℝ} (hx : 8.7e36 ≤ x) : (1e4 : ℝ) * (3 / 2) ≤ x := by linarith

/-- (4.10): `log (c x) ≥ 5 ‖ηη'‖₁ = 7.5`, from `e^{7.5} < e^8 < 3^8 < 8.7e35`. -/
theorem hyp_410 {x : ℝ} (hx : 8.7e36 ≤ x) : (5 : ℝ) * (3 / 2) ≤ Real.log (0.1 * x) := by
  have hpos : (0 : ℝ) < 0.1 * x := by linarith
  have h8 : Real.exp 8 < 0.1 * x := by
    have h1 : Real.exp 1 ^ 8 < (3 : ℝ) ^ 8 :=
      pow_lt_pow_left₀ (by have := Real.exp_one_lt_d9; linarith) (Real.exp_pos 1).le
        (by norm_num)
    rw [← Real.exp_nat_mul] at h1
    norm_num at h1
    linarith
  have := (Real.lt_log_iff_exp_lt hpos).mpr h8
  linarith

/-- (4.11): `x ≥ 10^8 ‖η‖∞⁴ = 10^8 · 9/4`. -/
theorem hyp_411 {x : ℝ} (hx : 8.7e36 ≤ x) : (1e8 : ℝ) * Real.sqrt (3 / 2) ^ 4 ≤ x := by
  rw [sqrt32_pow4]; linarith

/-- (4.12): `r x ≥ 20 ‖η'η' + ηη''‖₁ ‖η‖∞` with `r = T₀ / (3.6 π x)`, so `r x = T₀ / (3.6 π)`. -/
theorem hyp_412 {x : ℝ} (hx : 8.7e36 ≤ x) :
    (20 : ℝ) * 60 * Real.sqrt (3 / 2) ≤ T0 / (3.6 * π * x) * x := by
  have hx0 : 0 < x := by linarith
  have : T0 / (3.6 * π * x) * x = T0 / (3.6 * π) := by field_simp
  rw [this, le_div_iff₀ (by positivity)]
  have hpi := Real.pi_lt_d2
  have := sqrt32_le
  have h0 : 0 ≤ Real.sqrt (3 / 2) := Real.sqrt_nonneg _
  unfold T0
  nlinarith [Real.pi_pos]

/-- The range of `r` the corollary needs: `1/(2x) ≤ r ≤ 1/2`. -/
theorem r_range {x : ℝ} (hx : 8.7e36 ≤ x) :
    1 / (2 * x) ≤ T0 / (3.6 * π * x) ∧ T0 / (3.6 * π * x) ≤ 1 / 2 := by
  have hx0 : 0 < x := by linarith
  have hpi := Real.pi_gt_three
  have hpi2 := Real.pi_lt_d2
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    unfold T0; nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    unfold T0; nlinarith

/-! ## What the corollary gives for `η₁`, against what Section 8 prints -/

/-- `0.94 · ‖η₁‖₂² = 0.94 · 2/3 < 0.627 < 0.92`. -/
theorem scaled_lower : (0.94 : ℝ) * (2 / 3) < 0.627 ∧ (0.627 : ℝ) < 0.92 := by
  constructor <;> norm_num

/-- With `(8.13)`, `D = (N₀/3)(1 + O*(10^{-10}))`, the lower bound on the strongly major arc
is `0.94 · 2/3 · (1 - 10^{-10})²`, about `0.6267`, times `(N₀/3)² x`, and subtracting it from
the `8.001` of `bracket_le` leaves more than `7.37`, above the printed `7.09`. -/
theorem prop84_chain_fails :
    (7.37 : ℝ) < 8.001 - 0.94 * (2 / 3) * (1 - 1e-10) ^ 2 ∧ (7.09 : ℝ) < 7.37 := by
  constructor <;> norm_num

/-- The Hölder step for (8.17): the `L^∞` bound `0.078` of (8.18) times the `L²` bound must be
at most `0.56`, and `0.56` is what the main term `2/3 - 0.1` of Proposition 8.3 allows. With the
printed `7.09` it holds; with `7.37` it fails, even against `2/3 - 0.1`. -/
theorem eq817_chain_fails :
    (0.078 : ℝ) * 7.09 ≤ 0.56 ∧ (0.56 : ℝ) < 2 / 3 - 0.1 ∧ 2 / 3 - 0.1 < (0.078 : ℝ) * 7.37 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- Repair, arithmetic only: the chain closes if the error in Proposition 8.3 is at most
`0.09` rather than `0.1`, since `0.078 · 7.38 < 2/3 - 0.09`. The lab's 2026-10-18 recomputation
of (8.14) to (8.16) put that error near 0.035; that recomputation is not in Lean. -/
theorem repair_margin :
    8.001 - 0.94 * (2 / 3) * (1 - 1e-10) ^ 2 < (7.38 : ℝ) ∧
      (0.078 : ℝ) * 7.38 < 2 / 3 - 0.09 := by
  constructor <;> norm_num

#print axioms S_smul
#print axioms sq_integral_smul
#print axioms scaled_bound
#print axioms sqrt32_le
#print axioms sqrt32_pow4
#print axioms hyp_48
#print axioms hyp_49
#print axioms hyp_410
#print axioms hyp_411
#print axioms hyp_412
#print axioms r_range
#print axioms scaled_lower
#print axioms prop84_chain_fails
#print axioms eq817_chain_fails
#print axioms repair_margin

end LeanLab.Tao2012.Cor48
