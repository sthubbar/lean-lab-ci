/-
AI wrote this Lean code, Claude, ROUTE BURST S70, burst-20261122, unit ep2022_split.
Split of the LEAF `ProgressionS63.ep2022_theorem1`, Ernvall-Hytonen and Palojarvi,
arXiv 2003.01925v4, Theorem 1 p. 2, along the paper's own proof in Section 4, pp. 40 to 46:
* `thm3`, LEAF HARD: Theorem 3 p. 3, the GRH bound for psi of x, q, a; the analytic core.
* `lemma31`, LEAF MEDIUM: Lemma 31 pp. 40 to 41, the integral estimate of S from the
  Theorem 3 bound, a real analysis step.
* `display_50_53`, LEAF MEDIUM: the partial summation identities (50) and (53) p. 44.
* `display_51`, `display_52`, LEAF MEDIUM: the bounds (51) and (52) p. 44 from
  Rosser-Schoenfeld 1962 Theorem 13, psi minus theta below 1.42620 sqrt x.
* `final_combination`, LEAF MEDIUM: the simplification on pp. 45 to 46 with Lemmas 11
  and 32, a pure inequality between explicit functions of x and q.
* `ep2022_theorem1_of_leaves`, PROVED: the triangle inequality assembling them into the
  exact statement of `ProgressionS63.ep2022_theorem1`.
The constants were read on the rendered pages 3, 40, 41 and 44 of the arXiv PDF. Note the
term `x^(1/4) log log √x` of Lemma 31, which the text extraction drops to `log log x`.
A Python check of `final_combination` over q from 3 to 10^40 and x/q from 1 to 10^80 found
slack at least 154.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.ChenThresholdGRH

namespace LeanLab.BS2022GRH.ProgressionEPS70
open Real Finset Classical ChenThresholdGRH
noncomputable section

/-- psi of x, q, a of EP2022 p. 44: the sum of the von Mangoldt function over
`n ≤ x` with `n ≡ a mod q`. -/
def psiAP (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q), (ArithmeticFunction.vonMangoldt n : ℝ)

/-- theta of x, q, a of EP2022 p. 44: the sum of `log p` over primes `p ≤ x`,
`p ≡ a mod q`. -/
def thetaAP (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ (range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % q = a % q), log p

/-- `R₁(q)` of EP2022 Theorem 3 p. 3, three cases of q. -/
def R1 (q : ℕ) : ℝ :=
  if (q : ℝ) < 4 * 10 ^ 5 then
    0.014 * √(q : ℝ) * log q + 0.034 * √(q : ℝ) + 3.679 * log q + 263.886
  else if (q : ℝ) < 10 ^ 29 then 1.858 * log q ^ 2 + 3.679 * log q + 104.626
  else (0.297 * log (log q) + 0.603) * log q ^ 2 + 3.679 * log q + 104.626

/-- The right side of EP2022 Theorem 3 p. 3. -/
def thm3RHS (q : ℕ) (x : ℝ) : ℝ :=
  (1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π)) * √x * log x ^ 2
  + (0.184 * log q + 8.250) * √x * log x
  + (5.314 * log q + 124.318) * √x
  + (5.048 * log q ^ 2 + 109.573 * log q + 725.316) * √x / log x
  + (2.015 * log q + 0.5) * log x + R1 q

/-- The right side of EP2022 Lemma 31 pp. 40 to 41. -/
def lemma31RHS (q : ℕ) (x : ℝ) : ℝ :=
  (1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π)) * √x * log x
  + (0.184 * log q + 8.396) * √x
  + (6.05 * log q + 157.318) * √x / log x
  + (5.048 * log q ^ 2 + 152.085 * log q + 1719.86) * √x / log x ^ 2
  + (0.184 * log q + 8.250) * x ^ ((1 : ℝ) / 4) * log (log √x)
  + (5.254 * log q ^ 2 + 121.765 * log q + 937.202) * x ^ ((1 : ℝ) / 4)
  - (11.364 * log q + 281.636) * x ^ ((1 : ℝ) / 4) / log x
  - (10.096 * log q ^ 2 + 261.658 * log q + 2445.176) * x ^ ((1 : ℝ) / 4) / log x ^ 2
  + (80.768 * log q ^ 2 + 1753.168 * log q + 11605.056) * x ^ ((1 : ℝ) / 4) / log x ^ 3
      * (x ^ ((1 : ℝ) / 4) - 1)
  + (2.015 * log q + 0.5) * log (log x) + 2.754 * log q + 0.534 + R1 q / log 2

/-- The right side of EP2022 display (52) p. 44. -/
def display52RHS (x : ℝ) : ℝ :=
  11.4096 * √x / log x ^ 2 + 1.4262 * x ^ ((1 : ℝ) / 4) / log 2
  - 2.8524 * x ^ ((1 : ℝ) / 4) / log x - 11.4096 * x ^ ((1 : ℝ) / 4) / log x ^ 2

/-- LEAF: EP2022 Theorem 3 p. 3, GRH bound for psi of x, q, a. HARD, the analytic core of
the paper, Section 3, from the explicit formula for psi of x and chi. -/
theorem thm3 (hG : GRH) (q a : ℕ) (x : ℝ) (ha : Nat.Coprime a q) (hq : 3 ≤ q) (hx : 2 ≤ x) :
    |psiAP q a x - x / (q.totient : ℝ)| < thm3RHS q x := by
  sorry

/-- LEAF: EP2022 Lemma 31 pp. 40 to 41. MEDIUM, real analysis: integrate the Theorem 3
bound for `S(t) = psi(t; q, a) - t / phi(q)`, displays (40) to (49). The paper states the
one sided form; its proof bounds `|S|` from (40), which gives the absolute form here. -/
theorem lemma31 (q a : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : (q : ℝ) ≤ x)
    (hS : ∀ t : ℝ, 2 ≤ t → t ≤ x → |psiAP q a t - t / (q.totient : ℝ)| < thm3RHS q t) :
    |(psiAP q a x - x / (q.totient : ℝ)) / log x
      + ∫ t in (2 : ℝ)..x, (psiAP q a t - t / (q.totient : ℝ)) / (t * log t ^ 2)|
      < lemma31RHS q x := by
  sorry

/-- PROVED: `θ(x; q, a)` as an indicator sum over `[0, ⌊x⌋]`. -/
theorem thetaAP_eq_Icc (q a : ℕ) (x : ℝ) : thetaAP q a x =
    ∑ n ∈ Icc 0 ⌊x⌋₊, if n.Prime ∧ n % q = a % q then log n else 0 := by
  unfold thetaAP; rw [Nat.range_succ_eq_Icc_zero, sum_filter]

/-- EP2022 p. 44, first display of the proof of Theorem 1, partial summation:
`π(x; q, a) = θ(x; q, a) / log x + ∫₂ˣ θ(t; q, a) / (t log² t) dt` for `x ≥ 2`.
Was a LEAF; PROVED by S70 by Abel summation, adapting Mathlib's proof of
`Chebyshev.primeCounting_eq_theta_div_log_add_integral` to a residue class. -/
theorem display_50_partial (q a : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : 2 ≤ x) :
    ((((range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℕ) : ℝ)
      = thetaAP q a x / log x + ∫ t in (2 : ℝ)..x, thetaAP q a t / (t * log t ^ 2) := by
  rw [card_eq_sum_ones, Nat.range_succ_eq_Icc_zero, sum_filter]
  push_cast
  let A : ℕ → ℝ := Set.indicator {n | n.Prime ∧ n % q = a % q} (fun n ↦ log n)
  trans ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * A n
  · refine sum_congr rfl fun n hn ↦ ?_
    split_ifs with h
    · have : log n ≠ 0 := log_ne_zero_of_pos_of_ne_one (mod_cast h.1.pos) (mod_cast h.1.ne_one)
      simp [A, h, field]
    · simp [A, h]
  rw [sum_mul_eq_sub_integral_mul₁ A (f := fun n ↦ (log n)⁻¹) (by simp [A, Nat.not_prime_zero])
    (by simp [A, Nat.not_prime_one]), ← intervalIntegral.integral_of_le hx]
  · have int_deriv (f : ℝ → ℝ) :
        ∫ u in 2..x, deriv (fun x ↦ (log x)⁻¹) u * f u =
        ∫ u in 2..x, f u * -(u * log u ^ 2)⁻¹ :=
      intervalIntegral.integral_congr fun u _ ↦ by simp [field]
    rw [int_deriv]
    simp [A, Set.indicator_apply, thetaAP_eq_Icc]
    grind
  · intro z ⟨_, _⟩
    have : z ≠ 0 := by linarith
    have : log z ≠ 0 := by apply log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun z ⟨_, _⟩ ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have : z ≠ 0 := by linarith
    have : log z ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 <| log_ne_zero_of_pos_of_ne_one ?_ ?_ <;> linarith
    exact ContinuousAt.continuousWithinAt <| by fun_prop

/-- PROVED: `ψ(x; q, a)` is monotone in `x`. -/
theorem psiAP_mono (q a : ℕ) : Monotone (psiAP q a) := by
  intro x y hxy
  unfold psiAP
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, le_trans hn.1.2 (Nat.floor_le_floor hxy)⟩, hn.2⟩
  · intro n _ _; exact ArithmeticFunction.vonMangoldt_nonneg

/-- PROVED: `θ(x; q, a)` is monotone in `x`. -/
theorem thetaAP_mono (q a : ℕ) : Monotone (thetaAP q a) := by
  intro x y hxy
  unfold thetaAP
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [mem_filter, mem_range] at hn ⊢
    exact ⟨by have h : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy; omega, hn.2⟩
  · intro n hn _
    exact log_nonneg (by exact_mod_cast (mem_filter.1 hn).2.1.one_lt.le)

theorem cont_weight (x : ℝ) (hx : 2 ≤ x) :
    ContinuousOn (fun t : ℝ => 1 / (t * log t ^ 2)) (Set.uIcc 2 x) := by
  rw [Set.uIcc_of_le hx]
  refine ContinuousOn.div continuousOn_const ?_ ?_
  · refine ContinuousOn.mul continuousOn_id ((continuousOn_log.mono ?_).pow 2)
    intro t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
  · intro t ht
    have h1 : 0 < t := by linarith [ht.1]
    have h2 : 0 < log t := log_pos (by linarith [ht.1])
    positivity

theorem ii_of_mono (f : ℝ → ℝ) (hf : Monotone f) (x : ℝ) (hx : 2 ≤ x) :
    IntervalIntegrable (fun t => f t / (t * log t ^ 2)) MeasureTheory.volume 2 x := by
  have h := (hf.intervalIntegrable (μ := MeasureTheory.volume) (a := 2) (b := x)).mul_continuousOn (cont_weight x hx)
  refine h.congr ?_
  intro t _
  show f t * (1 / (t * log t ^ 2)) = f t / (t * log t ^ 2)
  rw [mul_one_div]

/-- PROVED, Rosser-Schoenfeld 1962 (7.6) at `ξ = 2`, used in EP2022 p. 44:
`∫₂ˣ dt / log² t = li x - x / log x - li 2 + 2 / log 2`. -/
theorem integral_inv_log_sq (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, 1 / log t ^ 2 = liPV x - x / log x - liPV 2 + 2 / log 2 := by
  have hsub : ∀ t ∈ Set.uIcc 2 x, 1 < t := by
    intro t ht; rw [Set.uIcc_of_le hx] at ht; linarith [ht.1]
  have key : ∀ t ∈ Set.uIcc 2 x,
      HasDerivAt (fun t => t / log t) (1 / log t - 1 / log t ^ 2) t := by
    intro t ht
    have h1 := hsub t ht
    have ht0 : t ≠ 0 := by linarith
    have hl : log t ≠ 0 := (log_pos h1).ne'
    have h := (hasDerivAt_id' t).div (hasDerivAt_log ht0) hl
    convert h using 1
    field_simp
  have hc1 : ContinuousOn (fun t : ℝ => 1 / log t) (Set.uIcc 2 x) := by
    refine ContinuousOn.div continuousOn_const (continuousOn_log.mono ?_) ?_
    · intro t ht; have := hsub t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith
    · intro t ht; exact (log_pos (hsub t ht)).ne'
  have hc2 : ContinuousOn (fun t : ℝ => 1 / log t ^ 2) (Set.uIcc 2 x) := by
    refine ContinuousOn.div continuousOn_const ((continuousOn_log.mono ?_).pow 2) ?_
    · intro t ht; have := hsub t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith
    · intro t ht; exact pow_ne_zero 2 (log_pos (hsub t ht)).ne'
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt key ((hc1.sub hc2).intervalIntegrable)
  rw [intervalIntegral.integral_sub hc1.intervalIntegrable hc2.intervalIntegrable] at hI
  have hli := liPV_eq_add hx
  linarith

/-- EP2022 displays (50) and (53) p. 44. Was a LEAF; PROVED by S70 from the partial
summation LEAF `display_50_partial`, the li identity `integral_inv_log_sq` and the
monotonicity of `ψ(x; q, a)` and `θ(x; q, a)` for integrability. -/
theorem display_50_53 (q a : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : 2 ≤ x) :
    ((((range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℕ) : ℝ)
        - liPV x / (q.totient : ℝ)
      = ((psiAP q a x - x / (q.totient : ℝ)) / log x
          + ∫ t in (2 : ℝ)..x, (psiAP q a t - t / (q.totient : ℝ)) / (t * log t ^ 2))
        + (thetaAP q a x - psiAP q a x) / log x
        + (∫ t in (2 : ℝ)..x, (thetaAP q a t - psiAP q a t) / (t * log t ^ 2))
        + (-liPV 2 + 2 / log 2) / (q.totient : ℝ) := by
  have hphi : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 (by omega)
  have hl : 0 < log x := log_pos (by linarith)
  have iP := ii_of_mono _ (psiAP_mono q a) x hx
  have iT := ii_of_mono _ (thetaAP_mono q a) x hx
  have iL : IntervalIntegrable (fun t : ℝ => t / (q.totient : ℝ) / (t * log t ^ 2))
      MeasureTheory.volume 2 x :=
    ii_of_mono (fun t => t / (q.totient : ℝ))
      (fun s t h => div_le_div_of_nonneg_right h hphi.le) x hx
  have e1 : (∫ t in (2 : ℝ)..x, (psiAP q a t - t / (q.totient : ℝ)) / (t * log t ^ 2))
      = (∫ t in (2 : ℝ)..x, psiAP q a t / (t * log t ^ 2))
        - ∫ t in (2 : ℝ)..x, t / (q.totient : ℝ) / (t * log t ^ 2) := by
    rw [← intervalIntegral.integral_sub iP iL]
    congr 1; ext t; ring
  have e2 : (∫ t in (2 : ℝ)..x, (thetaAP q a t - psiAP q a t) / (t * log t ^ 2))
      = (∫ t in (2 : ℝ)..x, thetaAP q a t / (t * log t ^ 2))
        - ∫ t in (2 : ℝ)..x, psiAP q a t / (t * log t ^ 2) := by
    rw [← intervalIntegral.integral_sub iT iP]
    congr 1; ext t; ring
  have e3 : (∫ t in (2 : ℝ)..x, t / (q.totient : ℝ) / (t * log t ^ 2))
      = (1 / (q.totient : ℝ)) * ∫ t in (2 : ℝ)..x, 1 / log t ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hx] at ht
    have h1 : t ≠ 0 := by linarith [ht.1]
    field_simp
  rw [display_50_partial q a x hq hx, e1, e2, e3, integral_inv_log_sq x hx]
  field_simp
  ring

/-- LEAF: Rosser-Schoenfeld 1962 Theorem 13, display (3.36) p. 71, cited by EP2022 p. 44 as
[11] Theorem 13: `ψ(x) - θ(x) < 1.42620 x^{1/2}` for `0 < x`. A classical cited input,
checked on the rendered page. EASY to state, its proof in the source is a tabulation for
`x < 50653` and an analytic argument above. -/
theorem rs62_thm13 (x : ℝ) (hx : 0 < x) :
    Chebyshev.psi x - Chebyshev.theta x < 1.4262 * √x := by
  sorry

/-- PROVED: `θ(x; q, a)` is the prime part of the sum defining `ψ(x; q, a)`. -/
theorem thetaAP_eq (q a : ℕ) (x : ℝ) : thetaAP q a x =
    ∑ n ∈ ((Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q)).filter (fun n => n.Prime),
      (ArithmeticFunction.vonMangoldt n : ℝ) := by
  unfold thetaAP
  have hs : (range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % q = a % q)
      = ((Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q)).filter (fun n => n.Prime) := by
    ext n
    simp only [mem_filter, mem_range, mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨⟨h2.one_lt.le, by omega⟩, h3⟩, h2⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨by omega, h4, h3⟩
  rw [hs]
  refine sum_congr rfl fun n hn => ?_
  rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.1 hn).2]

/-- PROVED: EP2022 p. 44 before (51), `0 ≤ ψ(x; q, a) - θ(x; q, a) ≤ ψ(x) - θ(x)`. -/
theorem psiAP_sub_thetaAP_bounds (q a : ℕ) (x : ℝ) :
    0 ≤ psiAP q a x - thetaAP q a x ∧
      psiAP q a x - thetaAP q a x ≤ Chebyshev.psi x - Chebyshev.theta x := by
  have hsplit := sum_filter_add_sum_filter_not ((Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q))
    (fun n => n.Prime) (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
  have hd : psiAP q a x - thetaAP q a x =
      ∑ n ∈ ((Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q)).filter (fun n => ¬ n.Prime),
        (ArithmeticFunction.vonMangoldt n : ℝ) := by
    rw [thetaAP_eq]; unfold psiAP; linarith
  rw [hd, Chebyshev.psi_sub_theta_eq_sum_not_prime]
  constructor
  · exact sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg
  · apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [mem_filter, mem_Icc, mem_Ioc] at hn ⊢
      exact ⟨⟨by omega, hn.1.1.2⟩, hn.2⟩
    · intro n _ _; exact ArithmeticFunction.vonMangoldt_nonneg

/-- EP2022 display (51) p. 44. Was a LEAF; PROVED by S70 from `rs62_thm13` and
`psiAP_sub_thetaAP_bounds`, so it is CONDITIONAL ON the cited Rosser-Schoenfeld 1962
Theorem 13 only. -/
theorem display_51 (q a : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : 2 ≤ x) :
    |(thetaAP q a x - psiAP q a x) / log x| < 1.4262 * √x / log x := by
  have hl : 0 < log x := log_pos (by linarith)
  obtain ⟨h0, h1⟩ := psiAP_sub_thetaAP_bounds q a x
  have h2 := rs62_thm13 x (by linarith)
  rw [abs_div, abs_of_pos hl, abs_sub_comm, abs_of_nonneg h0]
  exact div_lt_div_of_pos_right (by linarith) hl

open intervalIntegral in
/-- PROVED: `∫ₐᵇ dt / (t log² t) = 1 / log a - 1 / log b` on `(1, ∞)`. -/
theorem int_inv_tlog2 {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    ∫ t in a..b, 1 / (t * log t ^ 2) = -1 / log b - -1 / log a := by
  have hsub : ∀ t ∈ Set.uIcc a b, 1 < t := by
    intro t ht; rcases Set.mem_uIcc.1 ht with h | h <;> linarith [h.1, h.2, min_le_left a b]
  have key : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t => -1 / log t) (1 / (t * log t ^ 2)) t := by
    intro t ht
    have h1 := hsub t ht
    have ht0 : t ≠ 0 := by linarith
    have hl : log t ≠ 0 := (log_pos h1).ne'
    have h := ((hasDerivAt_log ht0).inv hl).neg
    convert h using 1
    · ext s; simp [neg_div]
    · field_simp
  have hc : ContinuousOn (fun t : ℝ => 1 / (t * log t ^ 2)) (Set.uIcc a b) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · refine ContinuousOn.mul continuousOn_id ((continuousOn_log.mono ?_).pow 2)
      intro t ht; have := hsub t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith
    · intro t ht; have := hsub t ht; have := log_pos this; positivity
  exact integral_eq_sub_of_hasDerivAt key hc.intervalIntegrable

open intervalIntegral in
/-- PROVED: `∫ₐᵇ dt / √t = 2√b - 2√a` on `(0, ∞)`. -/
theorem int_inv_sqrt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t in a..b, 1 / √t = 2 * √b - 2 * √a := by
  have hsub : ∀ t ∈ Set.uIcc a b, 0 < t := by
    intro t ht; rcases Set.mem_uIcc.1 ht with h | h <;> linarith [h.1, h.2]
  have key : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t => 2 * √t) (1 / √t) t := by
    intro t ht
    have h1 := hsub t ht
    have h := (hasDerivAt_sqrt h1.ne').const_mul 2
    convert h using 1
    have : 0 < √t := sqrt_pos.2 h1
    field_simp
  have hc : ContinuousOn (fun t : ℝ => 1 / √t) (Set.uIcc a b) := by
    refine ContinuousOn.div continuousOn_const continuous_sqrt.continuousOn ?_
    intro t ht; exact (sqrt_pos.2 (hsub t ht)).ne'
  exact integral_eq_sub_of_hasDerivAt key hc.intervalIntegrable

/-- PROVED: `x^{1/4} = √√x`. -/
theorem rpow_quarter (x : ℝ) (hx : 0 ≤ x) : x ^ ((1 : ℝ) / 4) = √(√x) := by
  rw [sqrt_eq_rpow, sqrt_eq_rpow, ← rpow_mul hx]; norm_num

open intervalIntegral in
/-- EP2022 display (52) p. 44, the calculus half: the integral of the (51) bound,
`1.4262 ∫₂ˣ √t / (t log² t) dt`, is at most the printed right side, by splitting at `√x`,
`√t ≤ x^{1/4}` below and `log t ≥ log √x` above. Was a LEAF; PROVED by S70 along the
paper's own computation, both orientations of the split point handled. -/
theorem display_52_calc (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, 1.4262 * √t / (t * log t ^ 2) ≤ display52RHS x := by
  set s := √x with hs_def
  set r := √s with hr_def
  have hx0 : 0 ≤ x := by linarith
  have hs2 : √2 ≤ s := sqrt_le_sqrt hx
  have h2 : (1.4 : ℝ) < √2 := by
    rw [show (1.4 : ℝ) = √(1.4 ^ 2) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs1 : 1 < s := by linarith
  have hsx : s ≤ x := by
    rw [hs_def, sqrt_le_left (by linarith)]; nlinarith
  have hr0 : 0 < r := sqrt_pos.2 (by linarith)
  have hlogs : log s = log x / 2 := by rw [hs_def, log_sqrt hx0]
  have hlx : 0 < log x := log_pos (by linarith)
  -- continuity of F on any interval inside (1, ∞)
  have hF : ∀ a b : ℝ, 1 < a → 1 < b →
      ContinuousOn (fun t : ℝ => √t / (t * log t ^ 2)) (Set.uIcc a b) := by
    intro a b ha hb
    have hsub : ∀ t ∈ Set.uIcc a b, 1 < t := by
      intro t ht; rcases Set.mem_uIcc.1 ht with h | h <;> linarith [h.1, h.2]
    refine ContinuousOn.div continuous_sqrt.continuousOn ?_ ?_
    · refine ContinuousOn.mul continuousOn_id ((continuousOn_log.mono ?_).pow 2)
      intro t ht; have := hsub t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith
    · intro t ht; have := hsub t ht; have := log_pos this; positivity
  have hg : ∀ a b : ℝ, 1 < a → 1 < b →
      ContinuousOn (fun t : ℝ => 1 / (t * log t ^ 2)) (Set.uIcc a b) := by
    intro a b ha hb
    have hsub : ∀ t ∈ Set.uIcc a b, 1 < t := by
      intro t ht; rcases Set.mem_uIcc.1 ht with h | h <;> linarith [h.1, h.2]
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · refine ContinuousOn.mul continuousOn_id ((continuousOn_log.mono ?_).pow 2)
      intro t ht; have := hsub t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith
    · intro t ht; have := hsub t ht; have := log_pos this; positivity
  have hcs : ContinuousOn (fun t : ℝ => 1 / √t) (Set.uIcc s x) := by
    refine ContinuousOn.div continuousOn_const continuous_sqrt.continuousOn ?_
    intro t ht; rw [Set.uIcc_of_le hsx] at ht; exact (sqrt_pos.2 (by linarith [ht.1])).ne'
  -- pull out the constant
  have hconst : (∫ t in (2 : ℝ)..x, 1.4262 * √t / (t * log t ^ 2))
      = 1.4262 * ∫ t in (2 : ℝ)..x, √t / (t * log t ^ 2) := by
    rw [← integral_const_mul]; congr 1; ext t; ring
  have hsplit : (∫ t in (2 : ℝ)..x, √t / (t * log t ^ 2))
      = (∫ t in (2 : ℝ)..s, √t / (t * log t ^ 2)) + ∫ t in s..x, √t / (t * log t ^ 2) :=
    (integral_add_adjacent_intervals ((hF 2 s (by norm_num) hs1).intervalIntegrable)
      ((hF s x hs1 (by linarith)).intervalIntegrable)).symm
  -- part A
  have hA : (∫ t in (2 : ℝ)..s, √t / (t * log t ^ 2))
      ≤ r * (-1 / log s - -1 / log 2) := by
    rw [← int_inv_tlog2 (by norm_num) hs1, ← integral_const_mul]
    rcases le_or_gt 2 s with h | h
    · apply integral_mono_on h ((hF 2 s (by norm_num) hs1).intervalIntegrable)
        ((continuousOn_const.mul (hg 2 s (by norm_num) hs1)) |>.intervalIntegrable)
      intro t ht
      have ht1 : 1 < t := by linarith [ht.1]
      have hd : 0 < t * log t ^ 2 := by have := log_pos ht1; positivity
      have : √t ≤ r := sqrt_le_sqrt ht.2
      show √t / (t * log t ^ 2) ≤ r * (1 / (t * log t ^ 2))
      rw [mul_one_div, div_le_div_iff_of_pos_right hd]; exact this
    · rw [integral_symm s 2, integral_symm s 2, neg_le_neg_iff]
      apply integral_mono_on h.le ((continuousOn_const.mul (hg s 2 hs1 (by norm_num))) |>.intervalIntegrable)
        ((hF s 2 hs1 (by norm_num)).intervalIntegrable)
      intro t ht
      have ht1 : 1 < t := by linarith [ht.1]
      have hd : 0 < t * log t ^ 2 := by have := log_pos ht1; positivity
      have : r ≤ √t := sqrt_le_sqrt ht.1
      show r * (1 / (t * log t ^ 2)) ≤ √t / (t * log t ^ 2)
      rw [mul_one_div, div_le_div_iff_of_pos_right hd]; exact this
  -- part B
  have hB : (∫ t in s..x, √t / (t * log t ^ 2))
      ≤ 4 / log x ^ 2 * (2 * √x - 2 * √s) := by
    rw [← int_inv_sqrt (by linarith) (by linarith), ← integral_const_mul]
    apply integral_mono_on hsx ((hF s x hs1 (by linarith)).intervalIntegrable)
      ((continuousOn_const.mul hcs) |>.intervalIntegrable)
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : 0 < t := by linarith
    have hst : 0 < √t := sqrt_pos.2 ht0
    have hlt : log s ≤ log t := log_le_log (by linarith) ht.1
    have hlt0 : 0 < log t := log_pos ht1
    have hsq : t = √t * √t := (mul_self_sqrt ht0.le).symm
    have hlog2 : log x ^ 2 ≤ 4 * log t ^ 2 := by nlinarith
    show √t / (t * log t ^ 2) ≤ 4 / log x ^ 2 * (1 / √t)
    rw [show √t / (t * log t ^ 2) = 1 / (√t * log t ^ 2) by
      rw [div_eq_div_iff (by positivity) (by positivity), ← mul_assoc, mul_self_sqrt ht0.le]; ring]
    rw [div_le_iff₀ (by positivity)]
    have : 1 / √t * (4 / log x ^ 2) * (√t * log t ^ 2) = 4 * log t ^ 2 / log x ^ 2 := by
      field_simp
    rw [mul_comm (4 / log x ^ 2), this, le_div_iff₀ (by positivity)]
    linarith
  rw [hconst, hsplit]
  have hfin : 1.4262 * (r * (-1 / log s - -1 / log 2) + 4 / log x ^ 2 * (2 * √x - 2 * √s))
      = display52RHS x := by
    unfold display52RHS
    rw [rpow_quarter x hx0, ← hs_def, ← hr_def, hlogs]
    field_simp
    ring
  rw [← hfin]
  have := add_le_add hA hB
  nlinarith

/-- EP2022 display (52) p. 44. Was a LEAF; PROVED by S70 from `rs62_thm13`,
`psiAP_sub_thetaAP_bounds` and the calculus LEAF `display_52_calc`. -/
theorem display_52 (q a : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : 2 ≤ x) :
    |∫ t in (2 : ℝ)..x, (thetaAP q a t - psiAP q a t) / (t * log t ^ 2)|
      ≤ display52RHS x := by
  have hcont : ContinuousOn (fun t : ℝ => 1.4262 * √t / (t * log t ^ 2)) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx]
    refine ContinuousOn.div (by fun_prop) ?_ ?_
    · refine ContinuousOn.mul continuousOn_id ((continuousOn_log.mono ?_).pow 2)
      intro t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
    · intro t ht
      have h1 : 0 < t := by linarith [ht.1]
      have h2 : 0 < log t := log_pos (by linarith [ht.1])
      positivity
  refine le_trans ?_ (display_52_calc x hx)
  rw [← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le hx ?_ (hcont.intervalIntegrable)
  refine Filter.Eventually.of_forall fun t ht => ?_
  have h1 : 0 < t := by linarith [ht.1]
  have h2 : 0 < log t := log_pos (by linarith [ht.1])
  have hd : 0 < t * log t ^ 2 := by positivity
  obtain ⟨h0, h3⟩ := psiAP_sub_thetaAP_bounds q a t
  have h4 := rs62_thm13 t h1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hd, abs_sub_comm, abs_of_nonneg h0]
  exact div_le_div_of_nonneg_right (by linarith) hd.le

/-- LEAF: EP2022 pp. 45 to 46, the simplification of the assembled bound to the form of
Theorem 1, with Lemmas 11 and 32 and the value of `li 2`. MEDIUM, an inequality between
explicit functions of `x ≥ q ≥ 3`. -/
theorem final_combination (q : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : (q : ℝ) ≤ x) :
    lemma31RHS q x + 1.4262 * √x / log x + display52RHS x
        + |-liPV 2 + 2 / log 2| / (q.totient : ℝ) ≤
      (1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π)) * √x * log x
      + (0.184 * log q + 8.396) * √x
      + (6.05 * log q + 158.745) * √x / log x
      + (5.048 * log q ^ 2 + 152.085 * log q + 1731.270) * √x / log x ^ 2
      + (0.184 * log q + 8.250) * x ^ ((1 : ℝ) / 4) * log (log x)
      + (5.254 * log q ^ 2 + 121.765 * log q + 939.260) * x ^ ((1 : ℝ) / 4)
      + (80.768 * log q ^ 2 + 1753.168 * log q + 11605.056) * √x / log x ^ 3
      - 237.934 := by
  sorry

/-- PROVED from the LEAFs above: EP2022 Theorem 1 p. 2, in the exact form of
`ProgressionS63.ep2022_theorem1`. -/
theorem ep2022_theorem1_of_leaves (hG : GRH) (q a : ℕ) (x : ℝ)
    (ha : Nat.Coprime a q) (hq : 3 ≤ q) (hx : (q : ℝ) ≤ x) :
    |((((range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℕ) : ℝ)
        - liPV x / (q.totient : ℝ)| <
      (1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π)) * √x * log x
      + (0.184 * log q + 8.396) * √x
      + (6.05 * log q + 158.745) * √x / log x
      + (5.048 * log q ^ 2 + 152.085 * log q + 1731.270) * √x / log x ^ 2
      + (0.184 * log q + 8.250) * x ^ ((1 : ℝ) / 4) * log (log x)
      + (5.254 * log q ^ 2 + 121.765 * log q + 939.260) * x ^ ((1 : ℝ) / 4)
      + (80.768 * log q ^ 2 + 1753.168 * log q + 11605.056) * √x / log x ^ 3
      - 237.934 := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hphi : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 (by omega)
  rw [display_50_53 q a x hq hx2]
  have hA := lemma31 q a x hq hx (fun t ht1 _ => thm3 hG q a t ha hq ht1)
  have hB := display_51 q a x hq hx2
  have hC := display_52 q a x hq hx2
  have hD : |(-liPV 2 + 2 / log 2) / (q.totient : ℝ)| = |-liPV 2 + 2 / log 2| / (q.totient : ℝ) := by
    rw [abs_div, abs_of_pos hphi]
  have hF := final_combination q x hq hx
  calc _ ≤ |(psiAP q a x - x / (q.totient : ℝ)) / log x
          + ∫ t in (2 : ℝ)..x, (psiAP q a t - t / (q.totient : ℝ)) / (t * log t ^ 2)|
        + |(thetaAP q a x - psiAP q a x) / log x|
        + |∫ t in (2 : ℝ)..x, (thetaAP q a t - psiAP q a t) / (t * log t ^ 2)|
        + |(-liPV 2 + 2 / log 2) / (q.totient : ℝ)| := by
          refine le_trans (abs_add_le _ _) ?_
          gcongr
          refine le_trans (abs_add_le _ _) ?_
          gcongr
          exact abs_add_le _ _
    _ < _ := by rw [hD]; linarith

end

end LeanLab.BS2022GRH.ProgressionEPS70

#print axioms LeanLab.BS2022GRH.ProgressionEPS70.ep2022_theorem1_of_leaves
#print axioms LeanLab.BS2022GRH.ProgressionEPS70.thetaAP_eq
#print axioms LeanLab.BS2022GRH.ProgressionEPS70.psiAP_sub_thetaAP_bounds
#print axioms LeanLab.BS2022GRH.ProgressionEPS70.display_51
#print axioms LeanLab.BS2022GRH.ProgressionEPS70.display_52
#print axioms LeanLab.BS2022GRH.ProgressionEPS70.integral_inv_log_sq
#print axioms LeanLab.BS2022GRH.ProgressionEPS70.display_50_53
#print axioms LeanLab.BS2022GRH.ProgressionEPS70.display_50_partial
#print axioms LeanLab.BS2022GRH.ProgressionEPS70.display_52_calc
