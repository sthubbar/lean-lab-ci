/-
U-1435, PC 20261021T1403Z-5629, track T1, P0039 L. Grimmelt, J. Teräväinen, arXiv 2508.16400.
AI-written Lean code, Claude, 2026-10-21. Binary Goldbach is OPEN.

The constant `c₀ = 0.06140` of (3.9), the δ₁ → 0 limit of

  ∏_{P₁ ≤ p < N^{1/10}} (1 - 1/p)⁻¹ ( Σ_d λ^ω_M(d)/φ(d) - (3/5 + δ₁) c_{E₃*} Σ_d λ^Ω_M(d)/φ(d) ),

with linear sieve functions `F`, `f` at level `N^{1/2}`:
* the ω part is `f(5) - ½ ∫_{1/10}^{1/3} F(5 - 10t) dt/t`, Chen's weight `1 - S/2` of (3.11);
* the Ω part is the upper sieve of the switched prime to `N^{1/6}`, value `F(3) = 2e^γ/3` on
  `V(N^{1/6})`, and the Mertens ratio `V(N^{1/6})/V(N^{1/10}) → 3/5` enters exactly once, as in
  `GT2025.switch_bound`;
* `c_{E₃*} = c_{B₁}(N) log N / 2 + c_{B₂}(N) log N → I_B₁ / 2`, from (3.1) to (3.3).

Writing `f(5) = (2e^γ/5)(log 4 + J₁)`, `∫ F(5-10t) dt/t = 2e^γ (log 3 / 5 + J₂)` and
`(3/5) (I_B₁/2) F(3) = 2e^γ I_B₁/10`, one gets `c₀ = 2e^γ K` with `K` below. The three integrals
`J₁ J₂ I_B₁` are defined here as Lean integrals; their numerical brackets come from the mpmath
computation build/u1435_c0.py at 30 digits and are a NAMED CITED HYPOTHESIS `IntegralBrackets`.
Everything else, log 2 and log 3 from Mathlib, is proved.
-/
import Mathlib

open Real intervalIntegral

namespace LeanLab.ChenPrimeExceptional.U1435

noncomputable section

/-- `s F(s) / (2e^γ)` for `1 ≤ s ≤ 5`, the linear sieve upper function. -/
def Fn (s : ℝ) : ℝ := if s ≤ 3 then 1 else 1 + ∫ t in (2 : ℝ)..(s - 1), log (t - 1) / t

/-- `J₁ = ∫_3^4 dt/t ∫_2^{t-1} log(u-1)/u du`, so `5 f(5)/(2e^γ) = log 4 + J₁`. -/
def J1 : ℝ := ∫ t in (3 : ℝ)..4, (∫ u in (2 : ℝ)..(t - 1), log (u - 1) / u) / t

/-- `J₂ = ∫_{1/10}^{1/5} Fn(5-10t) / (t (5 - 10t)) dt`, the `s ∈ [3, 4]` piece. -/
def J2 : ℝ := ∫ t in (1 / 10 : ℝ)..(1 / 5), Fn (5 - 10 * t) / (t * (5 - 10 * t))

/-- `I_B₁ = N log N c_{B₁}(N)`-density of (3.1) at δ₁ = 0, inner `t₂` integral done:
`∫_{1/10}^{1/3} log(2 - 3t)/(t(1 - t)) dt`. -/
def IB1 : ℝ := ∫ t in (1 / 10 : ℝ)..(1 / 3), log (2 - 3 * t) / (t * (1 - t))

/-- `c₀ / (2e^γ)`. -/
def K : ℝ := (log 4 + J1) / 5 - (log 3 / 5 + J2) / 2 - IB1 / 10

/-- `c₀ = 2 e^γ K`, the δ₁ → 0 value of the left side of (3.9). -/
def c0 : ℝ := 2 * exp eulerMascheroniConstant * K

/-- The same with the Mertens ratio `3/5` omitted, i.e. as printed (3.12) would need it if the
switched term had no `r_{N^{1/10}}(n+2)`, but the term were kept at full size. -/
def K_no35 : ℝ := (log 4 + J1) / 5 - (log 3 / 5 + J2) / 2 - IB1 / 6

/-- The `s ≤ 3` piece of `∫ F(5-10t) dt/t`: `∫_{1/5}^{1/3} dt/(t(5-10t)) = log 3 / 5`. -/
theorem closed_piece :
    ∫ t in (1 / 5 : ℝ)..(1 / 3), 1 / (t * (5 - 10 * t)) = log 3 / 5 := by
  have hderiv : ∀ x ∈ Set.uIcc (1 / 5 : ℝ) (1 / 3),
      HasDerivAt (fun t => (log t - log (5 - 10 * t)) / 5) (1 / (x * (5 - 10 * x))) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    obtain ⟨h1, h2⟩ := hx
    have hx0 : x ≠ 0 := by intro h; rw [h] at h1; norm_num at h1
    have hy0 : 5 - 10 * x ≠ 0 := by intro h; linarith
    have hl1 := hasDerivAt_log hx0
    have hl2 : HasDerivAt (fun t => log (5 - 10 * t)) ((0 - 10 * 1) / (5 - 10 * x)) x := by
      have := ((hasDerivAt_const x (5 : ℝ)).sub ((hasDerivAt_id x).const_mul 10)).log hy0
      simpa using this
    have := (hl1.sub hl2).div_const 5
    convert this using 1
    have hy0' : (5 : ℝ) - x * 10 ≠ 0 := by intro h; apply hy0; linarith
    field_simp
    ring
  rw [integral_eq_sub_of_hasDerivAt hderiv]
  · have h3 : (5 : ℝ) - 10 * (1 / 3) = 5 / 3 := by norm_num
    have h5 : (5 : ℝ) - 10 * (1 / 5) = 3 := by norm_num
    simp only [h3, h5]
    rw [log_div (by norm_num) (by norm_num), log_div (by norm_num) (by norm_num),
      log_div (by norm_num) (by norm_num)]
    simp only [log_one]
    ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact (continuousOn_id.mul (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)))
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num)] at hx
      obtain ⟨h1, h2⟩ := hx
      apply mul_ne_zero
      · intro h; rw [h] at h1; norm_num at h1
      · intro h; linarith

/-- **Named cited hypothesis.** Brackets of the three integrals, from build/u1435_c0.py, mpmath
at 30 digits: `J₁ = 0.014886346727…`, `J₂ = 0.208074927984…`, `I_B₁ = 0.490995201004…`, the last
checked against the direct double integral over the region of (3.1). Not proved in Lean. -/
def IntegralBrackets : Prop :=
  0.014886 ≤ J1 ∧ J1 ≤ 0.014887 ∧ 0.208074 ≤ J2 ∧ J2 ≤ 0.208075 ∧
    0.490995 ≤ IB1 ∧ IB1 ≤ 0.490996

/-- **Named cited hypothesis.** `e^γ = 1.78107241799…`. -/
def ExpGammaBracket : Prop :=
  1.7810724 ≤ exp eulerMascheroniConstant ∧ exp eulerMascheroniConstant ≤ 1.7810725

theorem log4_bounds : 1.3862943606 < log 4 ∧ log 4 < 1.3862943616 := by
  have h : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
  rw [h]
  constructor <;> linarith [log_two_gt_d9, log_two_lt_d9]

theorem log3_bounds : 1.0986122885 < log 3 ∧ log 3 < 1.0986122888 := by
  have h := log_three_near_10
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- **c₀/(2e^γ) bracket, CONDITIONAL ON `IntegralBrackets`.** -/
theorem K_bracket (h : IntegralBrackets) : 0.017237 ≤ K ∧ K ≤ 0.017239 := by
  obtain ⟨a1, a2, b1, b2, c1, c2⟩ := h
  obtain ⟨l4a, l4b⟩ := log4_bounds
  obtain ⟨l3a, l3b⟩ := log3_bounds
  unfold K
  constructor <;> linarith

/-- **c₀ > 0, CONDITIONAL ON `IntegralBrackets` only.** -/
theorem c0_pos (h : IntegralBrackets) : 0 < c0 := by
  unfold c0
  have := (K_bracket h).1
  have he := exp_pos eulerMascheroniConstant
  positivity

/-- **c₀ ∈ [0.06140, 0.06141], CONDITIONAL ON `IntegralBrackets` and `ExpGammaBracket`.**
The paper's printed value 0.06140 is confirmed: the mpmath value is 0.0614039983813822…. -/
theorem c0_bracket (h : IntegralBrackets) (hg : ExpGammaBracket) :
    0.06140 ≤ c0 ∧ c0 ≤ 0.06141 := by
  obtain ⟨k1, k2⟩ := K_bracket h
  obtain ⟨g1, g2⟩ := hg
  unfold c0
  constructor <;> nlinarith

/-- **Without the 3/5, CONDITIONAL ON `IntegralBrackets`:** the bracket of (3.9) would be
negative, so the factor `3/5` is needed for `c₀ > 0`; with it entering once `c₀ > 0`. -/
theorem K_no35_neg (h : IntegralBrackets) : K_no35 < 0 := by
  obtain ⟨a1, a2, b1, b2, c1, c2⟩ := h
  obtain ⟨l4a, l4b⟩ := log4_bounds
  obtain ⟨l3a, l3b⟩ := log3_bounds
  unfold K_no35
  linarith

/-- Vacuity of `IntegralBrackets`-style hypotheses: the bracket conditions are jointly
satisfiable by reals, at the midpoints, and then `K` as a formula is in range. -/
theorem brackets_vacuity :
    ∃ j1 j2 i : ℝ, 0.014886 ≤ j1 ∧ j1 ≤ 0.014887 ∧ 0.208074 ≤ j2 ∧ j2 ≤ 0.208075 ∧
      0.490995 ≤ i ∧ i ≤ 0.490996 ∧
      0.017237 ≤ (log 4 + j1) / 5 - (log 3 / 5 + j2) / 2 - i / 10 := by
  refine ⟨0.0148863, 0.2080749, 0.4909952, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_⟩
  obtain ⟨l4a, _⟩ := log4_bounds
  obtain ⟨_, l3b⟩ := log3_bounds
  linarith

end

end LeanLab.ChenPrimeExceptional.U1435

open LeanLab.ChenPrimeExceptional.U1435 in
#print axioms closed_piece
open LeanLab.ChenPrimeExceptional.U1435 in
#print axioms log4_bounds
open LeanLab.ChenPrimeExceptional.U1435 in
#print axioms log3_bounds
open LeanLab.ChenPrimeExceptional.U1435 in
#print axioms K_bracket
open LeanLab.ChenPrimeExceptional.U1435 in
#print axioms c0_pos
open LeanLab.ChenPrimeExceptional.U1435 in
#print axioms c0_bracket
open LeanLab.ChenPrimeExceptional.U1435 in
#print axioms K_no35_neg
open LeanLab.ChenPrimeExceptional.U1435 in
#print axioms brackets_vacuity
