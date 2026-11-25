/-
burst-20261122 S124, step feed1122-DecompJ409-p2. P0014 Proposition 4.6, page 43, display 4.43,
for the Gaussian, in the PRINTED form with 1 + 5 abs delta, split along the proof on pages 43
and 44 and the lab route of HelfgottMajor.Lemma41Corrected123.

The printed step |η'|₂ + 2π abs δ |η|₂ ≤ 1 + 5 abs δ of page 44 fails once abs δ is at least 2/5,
HelfgottMajor.Lemma41Terms.printed_fails, and the corrected Lemma 4.1 of the lab carries an extra
log x for even characters. The lab pieces of Lemmas 4.1, 4.4 and 4.5 therefore give display 4.43
with 1 + 6 abs delta only. The printed constant is still reached here: for sqrt x at least
2 (log q + 6) the extra (log q + 6) abs δ x^(-3/2) fits in the slack of the residue budget, and for
smaller x the trivial bound of the sum and of its main term already lies below the x^(-1/2) term
of display 4.43. The only new LEAF is that trivial bound for the sum.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.DecompJ409LeavesProp46
import LeanLab.HelfgottArcs.HeartHat
import LeanLab.HelfgottMajor.Lemma41Corrected123
import LeanLab.ChebyshevExplicit.SharperConstants

namespace LeanLab.HelfgottArcs.DecompJ409LeavesProp46S124Prop46
open Real MeasureTheory
open LeanLab.HelfgottArcs LeanLab.HelfgottMajor LeanLab.HelfgottMajor.SplitGaussian123
open LeanLab.HelfgottArcs.DecompJ409LeavesProp46
open scoped ArithmeticFunction

section TrivialBound
open Chebyshev
open scoped ArithmeticFunction

/-! PROVED helpers for `schi_etaHeart_trivial`, S152. Chebyshev psi n ≤ 1.59 n for every n:
lcm of 1..n at most 4^n by a kernel table below 600, the lab bound
`ChebyshevExplicit.psi_le_110556` above. Then Abel majorization and the sum integral
comparison against the one sided Gaussian integral x sqrt(2π)/2. AI wrote this Lean code. -/


def lcmRec : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.lcm (lcmRec n) (n + 1)

theorem lcmUpto_dvd_L (n : ℕ) : Nat.lcmUpto n ∣ lcmRec n := by
  unfold Nat.lcmUpto
  apply Finset.lcm_dvd
  intro i hi
  simp only [Finset.mem_Icc] at hi
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [lcmRec]
    rcases Nat.lt_or_ge i (n+1) with h | h
    · exact (ih ⟨hi.1, by omega⟩).trans (Nat.dvd_lcm_left _ _)
    · have : i = n + 1 := by omega
      subst this; exact Nat.dvd_lcm_right _ _

set_option maxRecDepth 100000 in
theorem L_le : ∀ n < 600, lcmRec n ≤ 4 ^ n := by decide +kernel

theorem L_pos (n : ℕ) : 0 < lcmRec n := by
  induction n with
  | zero => simp [lcmRec]
  | succ n ih => simp only [lcmRec]; exact Nat.lcm_pos ih (Nat.succ_pos n)

theorem psi_small (n : ℕ) (hn : n < 600) : ψ n ≤ 1.59 * n := by
  rw [psi_eq_log_lcmUpto]
  have h1 : (Nat.lcmUpto n : ℝ) ≤ (4 : ℝ) ^ n := by
    have := Nat.le_of_dvd (L_pos n) (lcmUpto_dvd_L n)
    exact_mod_cast this.trans (L_le n hn)
  have h0 : (0 : ℝ) < Nat.lcmUpto n := by exact_mod_cast Nat.lcmUpto_pos n
  have h2 := Real.log_le_log h0 h1
  rw [Real.log_pow] at h2
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h5 := Real.log_two_lt_d9
  have hn0 : (0 : ℝ) ≤ n := by positivity
  nlinarith

theorem log_le_quarter {x : ℝ} (hx : 0 < x) : Real.log x ≤ 1.4716 * √(√x) := by
  set y := √(√x)
  have hy : 0 < y := by positivity
  have hly : Real.log y = Real.log x / 4 := by
    simp only [y]; rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hx.le]; ring
  have he := Real.exp_one_gt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have h1 := Real.log_le_sub_one_of_pos (div_pos hy he0)
  rw [Real.log_div hy.ne' he0.ne', Real.log_exp] at h1
  have h2 : y / Real.exp 1 ≤ 0.3679 * y := by
    rw [div_le_iff₀ he0]; nlinarith
  linarith

theorem psi_large (n : ℕ) (hn : 600 ≤ n) : ψ n ≤ 1.59 * n := by
  have h := LeanLab.ChebyshevExplicit.psi_le_110556 n
  have hN' : (600 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (0 : ℝ) < n := by linarith
  have hl := log_le_quarter hx
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  set s := √(n : ℝ)
  have hs2 : s ^ 2 = n := Real.sq_sqrt hx.le
  have hs : 24.49 ≤ s := Real.le_sqrt_of_sq_le (by nlinarith)
  have hy2 : √s ^ 2 = s := Real.sq_sqrt (by positivity)
  have hy0 : 0 ≤ √s := Real.sqrt_nonneg _
  have hlog2 : Real.log n ^ 2 ≤ 1.4716 ^ 2 * s := by
    have := pow_le_pow_left₀ hl0 hl 2
    rw [mul_pow, hy2] at this; exact this
  nlinarith

theorem psi_le_159 (n : ℕ) : ψ n ≤ 1.59 * n := by
  rcases Nat.lt_or_ge n 600 with h | h
  · exact psi_small n h
  · exact psi_large n h

theorem abel_major (u v w : ℕ → ℝ) (hw : Antitone w) (hw0 : ∀ n, 0 ≤ w n)
    (hUV : ∀ n, ∑ i ∈ Finset.range n, u i ≤ ∑ i ∈ Finset.range n, v i) (N : ℕ) :
    ∑ i ∈ Finset.range N, u i * w i ≤ ∑ i ∈ Finset.range N, v i * w i := by
  have key : ∀ N, (∑ i ∈ Finset.range N, v i - ∑ i ∈ Finset.range N, u i) * w N ≤
      ∑ i ∈ Finset.range N, (v i - u i) * w i := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      have hD := hUV (N + 1)
      rw [Finset.sum_range_succ, Finset.sum_range_succ] at hD
      have hwN : w (N + 1) ≤ w N := hw (Nat.le_succ N)
      nlinarith [mul_le_mul_of_nonneg_left hwN (sub_nonneg.mpr hD)]
  have h1 := key N
  have h2 : 0 ≤ (∑ i ∈ Finset.range N, v i - ∑ i ∈ Finset.range N, u i) * w N :=
    mul_nonneg (sub_nonneg.mpr (hUV N)) (hw0 N)
  have h3 : ∑ i ∈ Finset.range N, (v i - u i) * w i =
      ∑ i ∈ Finset.range N, v i * w i - ∑ i ∈ Finset.range N, u i * w i := by
    rw [← Finset.sum_sub_distrib]; congr 1; ext i; ring
  linarith

theorem sum_range_vonMangoldt_succ (n : ℕ) :
    ∑ i ∈ Finset.range n, Λ (i + 1) = ψ n := by
  induction n with
  | zero => simp [psi]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, psi, psi, Nat.floor_natCast, Nat.floor_natCast,
      Finset.sum_Ioc_succ_top (Nat.zero_le n)]

theorem partial_le {x : ℝ} (hx : 1 ≤ x) (N : ℕ) :
    ∑ i ∈ Finset.range N, Λ i * etaHeart (i / x) ≤ 2 * x := by
  have hx0 : 0 < x := by linarith
  set b : ℝ := 1 / (2 * x ^ 2) with hbdef
  have hb : 0 < b := by positivity
  set w : ℝ → ℝ := fun t => Real.exp (-b * t ^ 2) with hwdef
  have heta : ∀ i : ℕ, etaHeart ((i + 1 : ℕ) / x) = w ((i + 1 : ℕ) : ℝ) := by
    intro i
    have hp : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) / x := by positivity
    simp only [etaHeart, hp, ite_true, hwdef, hbdef]
    congr 1; field_simp
  have hanti : AntitoneOn w (Set.Icc 0 (0 + (N : ℝ))) := by
    intro s hs t ht hst
    simp only [hwdef]
    apply Real.exp_le_exp.mpr
    have : s ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hs.1 hst 2
    nlinarith
  cases N with
  | zero => simp; linarith
  | succ M =>
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_div, ArithmeticFunction.map_zero, zero_mul, add_zero]
  have hrw : ∀ i ∈ Finset.range M, Λ (i + 1) * etaHeart (((i + 1 : ℕ) : ℝ) / x) =
      Λ (i + 1) * w (((i + 1 : ℕ) : ℝ)) := by
    intro i _; rw [heta]
  rw [Finset.sum_congr rfl hrw]
  have hwa : Antitone (fun i : ℕ => w ((i + 1 : ℕ) : ℝ)) := by
    intro i j hij
    simp only [hwdef]
    apply Real.exp_le_exp.mpr
    have hij' : ((i + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hij
    have : ((i + 1 : ℕ) : ℝ) ^ 2 ≤ ((j + 1 : ℕ) : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hij' 2
    nlinarith
  have hmaj := abel_major (fun i => Λ (i + 1)) (fun _ => (1.59 : ℝ))
    (fun i => w ((i + 1 : ℕ) : ℝ)) hwa (fun _ => by positivity)
    (fun n => by
      simp only [sum_range_vonMangoldt_succ, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have := psi_le_159 n; linarith) M
  have hint : ∑ i ∈ Finset.range M, w (0 + ((i + 1 : ℕ) : ℝ)) ≤ ∫ t in (0 : ℝ)..0 + M, w t :=
    (hanti.mono (by
      intro t ht; refine ⟨ht.1, ht.2.trans ?_⟩; push_cast; linarith)).sum_le_integral
  simp only [zero_add] at hint
  have hInt : IntegrableOn w (Set.Ioi 0) := (integrable_exp_neg_mul_sq hb).integrableOn
  have hle : ∫ t in (0 : ℝ)..M, w t ≤ ∫ t in Set.Ioi 0, w t := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    apply setIntegral_mono_set hInt
    · exact Filter.Eventually.of_forall (fun t => by simp only [hwdef]; positivity)
    · exact Set.Ioc_subset_Ioi_self.eventuallyLE
  have hg : ∫ t in Set.Ioi 0, w t = √(π / b) / 2 := integral_gaussian_Ioi b
  have hsq : √(π / b) ≤ 2.51 * x := by
    rw [show π / b = π * (2 * x ^ 2) by rw [hbdef]; field_simp]
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.pi_lt_d2]
  have hsum : ∑ i ∈ Finset.range M, (1.59 : ℝ) * w ((i + 1 : ℕ) : ℝ) =
      1.59 * ∑ i ∈ Finset.range M, w ((i + 1 : ℕ) : ℝ) := by rw [Finset.mul_sum]
  have hsum2 : ∑ i ∈ Finset.range M, w ((i + 1 : ℕ) : ℝ) ≤ 2.51 * x / 2 := by
    linarith
  linarith

end TrivialBound

/-- PROVED S152, was LEAF: the trivial bound for the twisted Gaussian sum of P0014 display 4.43, by partial
summation from the Chebyshev bound psi of y below 1.03883 y of Rosser and Schoenfeld 1962,
Theorem 12, the bound Helfgott uses for prime sums throughout P0014: the sum is at most
1.03883 sqrt(π/2) x, below 2 x. Class MEDIUM. Proved in S152 with psi n at most 1.59 n in
place of the cited 1.03883 n, so with no cited input. -/
theorem schi_etaHeart_trivial {q : ℕ} (χ : DirichletCharacter ℂ q) (δ x : ℝ) (hx : 1 ≤ x) :
    ‖Schi etaHeart χ δ x‖ ≤ 2 * x := by
  have hnn : ∀ y, 0 ≤ etaHeart y := by
    intro y; unfold etaHeart; split_ifs <;> positivity
  set g : ℕ → ℝ := fun n => Λ n * etaHeart (n / x) with hgdef
  have hg0 : ∀ n, 0 ≤ g n := fun n =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hnn _)
  have hgs : Summable g := summable_of_sum_range_le hg0 (partial_le hx)
  have hb : ∀ n : ℕ, ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * e (δ * n / x) *
      (etaHeart (n / x) : ℂ)‖ ≤ g n := by
    intro n
    have h1 : ‖e (δ * n / x)‖ = 1 := by
      simp [e, Complex.norm_exp, Complex.mul_re]
    rw [norm_mul, norm_mul, norm_mul, h1, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      abs_of_nonneg (hnn _), mul_one]
    have hc := DirichletCharacter.norm_le_one χ (n : ZMod q)
    have he := hnn (n / x)
    have hl := (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    simp only [hgdef]
    have := mul_le_mul_of_nonneg_left hc (mul_nonneg hl he)
    nlinarith
  unfold Schi
  calc _ ≤ ∑' n, g n := tsum_of_norm_bounded hgs.hasSum hb
    _ ≤ 2 * x := Real.tsum_le_of_sum_range_le hg0 (partial_le hx)

/-- PROVED. The main term of display 4.43 has norm at most the integral of the one sided
Gaussian, sqrt(2π)/2, by display 4.42 on page 43. -/
theorem fhat_etaHeart_norm_le (t : ℝ) : ‖fhat etaHeart t‖ ≤ 2 := by
  have hnn : ∀ y, 0 ≤ etaHeart y := by
    intro y; unfold etaHeart; split_ifs <;> positivity
  have hnorm : ∀ y : ℝ, ‖e (-(y * t)) * (etaHeart y : ℂ)‖ = etaHeart y := by
    intro y
    have h1 : ‖e (-(y * t))‖ = 1 := by
      simp [e, Complex.norm_exp, Complex.mul_re]
    rw [norm_mul, h1, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnn y)]
  have hint : ∫ y : ℝ, etaHeart y = sqrt (2 * π) / 2 := by
    have h0 := fhat_etaHeart_zero
    unfold fhat at h0
    have he : ∀ y : ℝ, e (-(y * 0)) = 1 := by intro y; simp [e]
    simp only [he, one_mul] at h0
    rw [integral_complex_ofReal] at h0
    exact_mod_cast h0
  calc ‖fhat etaHeart t‖ ≤ ∫ y : ℝ, ‖e (-(y * t)) * (etaHeart y : ℂ)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ y : ℝ, etaHeart y := by simp_rw [hnorm]
    _ = sqrt (2 * π) / 2 := hint
    _ ≤ 2 := by
      have h : sqrt (2 * π) ≤ 4 := by
        rw [sqrt_le_left (by norm_num)]
        nlinarith [pi_lt_four]
      linarith

/-- PROVED. The arithmetic of page 44 with the corrected inputs, for sqrt x at least
2 (log q + 6): the contour error with 1 + 6 abs δ and the residue budget fit in display 4.43
with 1 + 5 abs δ. -/
theorem large_x_budget {L d s : ℝ} (hL : 0 ≤ L) (hd : 0 ≤ d) (hs : 2 * (L + 6) ≤ s) :
    (L + 6.01) * (1 + 6 * d) / s + 13.347 * d + 16.695 ≤
      (L + 6) * (1 + 5 * d) / s + 14 * d + 17 := by
  have hs0 : 0 < s := by linarith
  have key : ((L + 6.01) * (1 + 6 * d) - (L + 6) * (1 + 5 * d)) / s ≤ 0.6 * d + 0.3 := by
    rw [div_le_iff₀ hs0]
    nlinarith [mul_nonneg hd hL, mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 0.6 * d + 0.3)]
  have he : (L + 6.01) * (1 + 6 * d) / s =
      (L + 6) * (1 + 5 * d) / s + ((L + 6.01) * (1 + 6 * d) - (L + 6) * (1 + 5 * d)) / s := by
    ring
  rw [he]
  linarith

/-- The exact parent `prop_4_6` statement from the leaves: the trivial bound leaf above and the
lab pieces of Lemmas 4.1, 4.4 and 4.5 behind Lemma41Corrected123. -/
theorem prop_4_6_of_leaves (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T0 : ℝ) (hT0 : max (4 * π ^ 2 * |δ|) 100 ≤ T0)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T0 → s.re = 1 / 2) :
    MajorShape etaHeart χ δ x (errGauss q T0 δ x) := by
  unfold MajorShape errGauss
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < sqrt x := sqrt_pos.mpr hx0
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hL : 0 ≤ log (q : ℝ) := log_nonneg hq1
  have hT100 : 100 ≤ T0 := (le_max_right _ _).trans hT0
  have hsT : 10 ≤ sqrt T0 := by
    rw [show (10 : ℝ) = sqrt 100 by rw [show (100 : ℝ) = 10 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt hT100
  have hlqT : log (q : ℝ) ≤ log (q * T0) := log_le_log (by linarith) (by nlinarith)
  have hHnn : 0 ≤ log (q * T0 / (2 * π)) * (4.329 * exp (-0.1598 * T0) +
      0.802 * |δ| * exp (-0.1065 * (T0 / (π * |δ|)) ^ 2)) := by
    apply mul_nonneg
    · apply log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith [pi_lt_four]
    · positivity
  set A := 2.337 * √T0 * log (q * T0) + 21.817 * √T0 + 2.85 * log q + 74.38 with hA
  have hA8 : 8 * (log q + 6) ≤ A := by
    have : 23.37 * log (q : ℝ) ≤ 2.337 * √T0 * log (q * T0) := by
      nlinarith [mul_le_mul hsT hlqT hL (by linarith)]
    rw [hA]; nlinarith
  have hsq : sqrt x * sqrt x = x := mul_self_sqrt hx0.le
  have heq : (log (q * T0 / (2 * π)) * (4.329 * exp (-0.1598 * T0) +
      0.802 * |δ| * exp (-0.1065 * (T0 / (π * |δ|)) ^ 2)) + A / √x +
      (3 * log q + 14 * |δ| + 17) / x + (log q + 6) * (1 + 5 * |δ|) / (x * √x)) * x =
      log (q * T0 / (2 * π)) * (4.329 * exp (-0.1598 * T0) +
        0.802 * |δ| * exp (-0.1065 * (T0 / (π * |δ|)) ^ 2)) * x + A * √x +
      (3 * log q + 14 * |δ| + 17) + (log q + 6) * (1 + 5 * |δ|) / √x := by
    generalize hroot : sqrt x = s at hsq hs0
    have hsne : s ≠ 0 := hs0.ne'
    rw [← hsq]
    field_simp
  rw [heq]
  have hnn2 : 0 ≤ (3 * log (q : ℝ) + 14 * |δ| + 17) := by positivity
  have hnn3 : 0 ≤ (log (q : ℝ) + 6) * (1 + 5 * |δ|) / √x := by positivity
  by_cases hsmall : sqrt x < 2 * (log q + 6)
  · -- small x: the trivial bound
    have h1 := schi_etaHeart_trivial χ δ x hx
    have h2 : ‖(if q = 1 then fhat etaHeart (-δ) * x else 0)‖ ≤ 2 * x := by
      split_ifs
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
        exact mul_le_mul_of_nonneg_right (fhat_etaHeart_norm_le _) hx0.le
      · simp; linarith
    have h3 := norm_sub_le (Schi etaHeart χ δ x) (if q = 1 then fhat etaHeart (-δ) * x else 0)
    have h4 : 4 * x ≤ A * √x := by
      calc 4 * x = (4 * √x) * √x := by rw [mul_assoc, hsq]
        _ ≤ A * √x := mul_le_mul_of_nonneg_right (by linarith) hs0.le
    have hHx := mul_nonneg hHnn hx0.le
    linarith
  · push_neg at hsmall
    obtain ⟨R, hR, hE⟩ := Lemma41Corrected123.explicit_formula_remainder_corrected x hx q χ hχ δ
      T0 hT0 hzeros
    have hLz := Lemma41Corrected123.low_zero_bound_slack x hx q χ hχ δ T0 hT0 hzeros
    have hHz := SplitGaussian123.high_zero_bound x hx q χ hχ δ T0 hT0 hzeros
    have hlogx : log x ≤ 2 * sqrt x := by
      have h := log_le_sub_one_of_pos hs0
      rw [log_sqrt hx0.le] at h
      linarith
    have htri : ‖Schi etaHeart χ δ x -
        (if q = 1 then fhat etaHeart (-δ) * x else 0)‖ ≤
        ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
          lowZeros χ δ x T0 + highZeros χ δ x T0 + R‖ +
          ‖lowZeros χ δ x T0‖ + ‖highZeros χ δ x T0‖ + ‖R‖ := by
      calc
        _ = ‖(Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
            lowZeros χ δ x T0 + highZeros χ δ x T0 + R) -
            lowZeros χ δ x T0 - highZeros χ δ x T0 - R‖ := by congr 1; abel
        _ ≤ _ := (norm_sub_le _ _).trans (by
          gcongr
          exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _))
    have hb := large_x_budget hL (abs_nonneg δ) hsmall
    have hLz' : ‖lowZeros χ δ x T0‖ ≤ (A - 2) * sqrt x := by rw [hA]; exact hLz
    nlinarith

end LeanLab.HelfgottArcs.DecompJ409LeavesProp46S124Prop46
