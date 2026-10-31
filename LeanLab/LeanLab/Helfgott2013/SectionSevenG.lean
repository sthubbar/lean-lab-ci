/-
# Helfgott 2013, arXiv 1312.7748v2, Section 7.3, the VNODE-LP integral behind (7.31)

Unit U-1120, T1 PROVE, P0001, run 20261019T2303Z-16260.

The paper, Section 7.3 just before (7.31), read in Claude in Chrome on arxiv.org/html/1312.7748:

  C_{φ,2,K} = −∫_{1/K}^1 φ(w) log w dw ≤ −∫_0^1 φ(w) log w dw
            ≤ −∫_0^1 w² e^{−w²/2} log w dw ≤ 0.093426,

"where again we use VNODE-LP for rigorous numerical integration", φ(t) = t² e^{−t²/2}; then
since |φ|₁ = √(π/2), (7.31): (C_{φ,2,K}/|φ|₁)/log K ≤ 0.07455/log((log y)/2).

Here the lab replaces VNODE-LP by a proof: e^{x} ≤ Σ_{i<7} x^i/i! + |x|^7 · 8/(7!·7) for
|x| ≤ 1, Mathlib's `Real.exp_bound`, at x = −w²/2, and the moments
∫₀¹ w^{m+1} (−log w) dw = 1/(m+2)². The bound obtained is 0.0934250136, true value about
0.0934250023, so 0.093426 holds with margin 9.9·10⁻⁷.

* `log_moment`: ∫₀¹ −w^{m+1} log w dw = 1/(m+2)².
* `vnode_integral_le`: −∫₀¹ w² e^{−w²/2} log w dw ≤ 0.093426.
* `tail_le_full`: for 0 ≤ a ≤ 1, −∫_a^1 ≤ −∫_0^1, the first inequality, as φ log w ≤ 0 on [0, 1].
* `eq_7_31_const`: 0.093426/√(π/2) ≤ 0.07455, so with the two above the constant of (7.31).

PROVED unconditional. AI wrote this Lean code. Ternary Goldbach is Helfgott's theorem; binary
Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Helfgott2013.SectionSevenG

open Real Finset intervalIntegral

/-- `w ↦ w^{m+1} (−log w)` written through `w log w` so that it is visibly continuous. -/
lemma continuous_moment (m : ℕ) : Continuous fun w : ℝ => -(w ^ m * (w * Real.log w)) := by
  have := Real.continuous_mul_log
  fun_prop

/-- **Log moments.** `∫₀¹ −w^{m+1} log w dw = 1/(m+2)²`. -/
theorem log_moment (m : ℕ) :
    ∫ w in (0 : ℝ)..1, -(w ^ m * (w * Real.log w)) = 1 / ((m : ℝ) + 2) ^ 2 := by
  have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  set F : ℝ → ℝ := fun w => w ^ (m + 2) / ((m : ℝ) + 2) ^ 2 - w ^ (m + 1) * (w * Real.log w) / ((m : ℝ) + 2)
    with hF
  have hFc : Continuous F := by
    have := Real.continuous_mul_log
    simp only [hF]
    fun_prop
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F (-(x ^ m * (x * Real.log x))) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have h1 := (hasDerivAt_pow (m + 2) x).div_const (((m : ℝ) + 2) ^ 2)
    have h2 := ((hasDerivAt_pow (m + 1) x).mul (Real.hasDerivAt_mul_log hx0)).div_const ((m : ℝ) + 2)
    convert h1.sub h2 using 1
    field_simp
    push_cast
    ring
  rw [integral_eq_sub_of_hasDerivAt_of_le zero_le_one hFc.continuousOn hderiv
    ((continuous_moment m).intervalIntegrable 0 1)]
  simp [hF]

/-- The coefficients of the majorant: `(−1/2)^i/i!` for `i < 7`, and the `exp_bound` error
`8/(7!·7)/2^7` at `i = 7`. -/
noncomputable def coef (i : ℕ) : ℝ :=
  if i < 7 then (-1 / 2 : ℝ) ^ i / (i.factorial : ℝ) else (8 / (5040 * 7) : ℝ) / 2 ^ 7

/-- The integrand `w² e^{−w²/2} (−log w)`. -/
noncomputable def g (w : ℝ) : ℝ := w ^ 2 * Real.exp (-w ^ 2 / 2) * -Real.log w

/-- The majorant, a combination of log moments. -/
noncomputable def h (w : ℝ) : ℝ :=
  ∑ i ∈ range 8, coef i * -(w ^ (2 * i + 1) * (w * Real.log w))

lemma continuous_g : Continuous g := by
  have hc : Continuous fun w : ℝ => w * (w * Real.log w) := by
    have := Real.continuous_mul_log; fun_prop
  have : g = fun w => -(Real.exp (-w ^ 2 / 2) * (w * (w * Real.log w))) := by
    funext w; simp only [g]; ring
  rw [this]; fun_prop

lemma continuous_h : Continuous h := by
  unfold h
  refine continuous_finsetSum _ fun i _ => ?_
  exact continuous_const.mul (continuous_moment (2 * i + 1))

lemma g_le_h {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) : g w ≤ h w := by
  obtain ⟨h0, h1⟩ := hw
  set x : ℝ := -w ^ 2 / 2 with hx
  have hxabs : |x| ≤ 1 := by
    rw [hx, abs_le]; constructor <;> nlinarith [sq_nonneg w]
  have hb := Real.exp_bound hxabs (n := 7) (by norm_num)
  have hexp : Real.exp x ≤ ∑ m ∈ range 7, x ^ m / (m.factorial : ℝ) +
      |x| ^ 7 * ((Nat.succ 7 : ℝ) / ((Nat.factorial 7 : ℝ) * 7)) := by
    have := (abs_le.1 hb).2; linarith
  have hlog : 0 ≤ -Real.log w := by
    have := Real.log_nonpos h0 h1; linarith
  have hw2 : 0 ≤ w ^ 2 := sq_nonneg w
  have hxa : |x| = w ^ 2 / 2 := by
    rw [hx, abs_of_nonpos (by nlinarith [sq_nonneg w])]; ring
  calc g w = w ^ 2 * Real.exp x * -Real.log w := by simp [g, hx]
    _ ≤ w ^ 2 * (∑ m ∈ range 7, x ^ m / (m.factorial : ℝ) +
          |x| ^ 7 * ((Nat.succ 7 : ℝ) / ((Nat.factorial 7 : ℝ) * 7))) * -Real.log w := by
        gcongr
    _ = h w := by
        rw [hxa, hx]
        simp only [h, coef, sum_range_succ, sum_range_zero, Nat.factorial]
        norm_num
        ring

/-- **The VNODE-LP integral of Section 7.3**: `−∫₀¹ w² e^{−w²/2} log w dw ≤ 0.093426`. -/
theorem vnode_integral_le : ∫ w in (0 : ℝ)..1, g w ≤ 0.093426 := by
  have hmono : ∫ w in (0 : ℝ)..1, g w ≤ ∫ w in (0 : ℝ)..1, h w :=
    integral_mono_on zero_le_one (continuous_g.intervalIntegrable 0 1)
      (continuous_h.intervalIntegrable 0 1) fun w hw => g_le_h hw
  have hval : ∫ w in (0 : ℝ)..1, h w = ∑ i ∈ range 8, coef i * (1 / ((((2 * i + 1 : ℕ) : ℝ)) + 2) ^ 2) := by
    unfold h
    rw [intervalIntegral.integral_finsetSum (by
      intro i _
      exact (continuous_const.mul (continuous_moment (2 * i + 1))).intervalIntegrable 0 1)]
    refine sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul, log_moment]
  rw [hval] at hmono
  refine hmono.trans ?_
  simp only [coef, sum_range_succ, sum_range_zero, Nat.factorial]
  norm_num

/-- The first step: for `0 ≤ a ≤ 1`, `−∫_a^1 φ log ≤ −∫_0^1 φ log`, the integrand being `≥ 0`. -/
theorem tail_le_full {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫ w in a..1, g w ≤ ∫ w in (0 : ℝ)..1, g w := by
  have hint := fun u v => continuous_g.intervalIntegrable (μ := MeasureTheory.volume) u v
  rw [← integral_add_adjacent_intervals (hint 0 a) (hint a 1)]
  have : 0 ≤ ∫ w in (0 : ℝ)..a, g w := by
    refine integral_nonneg ha0 fun w hw => ?_
    have h0 : 0 ≤ w := hw.1
    have h1 : w ≤ 1 := hw.2.trans ha1
    have := Real.log_nonpos h0 h1
    unfold g
    have := Real.exp_pos (-w ^ 2 / 2)
    have := sq_nonneg w
    have : 0 ≤ w ^ 2 * Real.exp (-w ^ 2 / 2) := by positivity
    nlinarith
  linarith

/-- `0.093426 / √(π/2) ≤ 0.07455`, the constant of (7.31). -/
theorem eq_7_31_const : (0.093426 : ℝ) / Real.sqrt (π / 2) ≤ 0.07455 := by
  have hs : (1.25322 : ℝ) ≤ Real.sqrt (π / 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have := Real.pi_gt_d4
    linarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- (7.31) assembled: for `1 ≤ K`, `(−∫_{1/K}^1 φ log)/√(π/2) ≤ 0.07455`. -/
theorem eq_7_31 {K : ℝ} (hK : 1 ≤ K) :
    (∫ w in (1 / K)..1, g w) / Real.sqrt (π / 2) ≤ 0.07455 := by
  have hpos : 0 < Real.sqrt (π / 2) := Real.sqrt_pos.2 (by positivity)
  have h1 := tail_le_full (a := 1 / K) (by positivity) (by rw [div_le_one (by linarith)]; exact hK)
  have h2 := vnode_integral_le
  calc (∫ w in (1 / K)..1, g w) / Real.sqrt (π / 2) ≤ 0.093426 / Real.sqrt (π / 2) := by
        gcongr; linarith
    _ ≤ 0.07455 := eq_7_31_const

end LeanLab.Helfgott2013.SectionSevenG
