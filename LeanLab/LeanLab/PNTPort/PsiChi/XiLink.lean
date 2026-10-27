import LeanLab.Xi2012.Statements

/-!
# AUDIT: Xi 2012's Siegel-Walfisz Prop is false as encoded

Lab proof, unit U-5212, CLOUD 20261019T0514Z-cloud17. AI wrote this file. A misformalization
in the lab's own encoding of P0056, not an error of the paper.

`Xi2012.thetaReal X y q a`, the lab's first encoding of `ϑ`, renamed when `Xi2012.theta` was
re-encoded in U-5213, sums `log p` over `p ∈ X` with `(p : ℝ) ≤ y ∧ p % q = a % q`; the finset
is coerced to `Finset ℝ`, so `%` is the real `EuclideanDomain` remainder, which is `0` for every
nonzero divisor, `real_mod_eq_zero`. The congruence condition is therefore void,
`theta_res_irrelevant`, and `Xi2012.SiegelWalfiszReal primesUpTo (fun _ => 1)` asks `θ(x)` to be
close to both `x/φ(1) = x` and `x/φ(3) = x/2`. `xi_siegelWalfisz_false` proves its negation with
no analytic input. Every Xi2012 result taking that hypothesis is vacuous as encoded.
-/

open Real Finset

namespace LeanLab.PNTPort.PsiChi

lemma real_mod_eq_zero (a b : ℝ) (hb : b ≠ 0) : a % b = 0 := by
  rw [EuclideanDomain.mod_eq_sub_mul_div, mul_div_cancel₀ a hb, sub_self]

lemma theta_res_irrelevant (X : Finset ℕ) (y : ℝ) {q a q' a' : ℕ} (hq : q ≠ 0) (hq' : q' ≠ 0) :
    Xi2012.thetaReal X y q a = Xi2012.thetaReal X y q' a' := by
  have h1 : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have h2 : (q' : ℝ) ≠ 0 := by exact_mod_cast hq'
  unfold Xi2012.thetaReal
  congr 1
  apply Finset.filter_congr
  intro p _
  simp only [real_mod_eq_zero _ _ h1, real_mod_eq_zero _ _ h2]

theorem xi_siegelWalfisz_false : ¬ Xi2012.SiegelWalfiszReal Xi2012.primesUpTo (fun _ => 1) := by
  intro h
  obtain ⟨C, hC⟩ := h 1 one_pos
  set L₀ := max 3 (4 * |C| + 1) with hL₀
  set x : ℕ := ⌈Real.exp L₀⌉₊ with hx
  have hL3 : 3 ≤ L₀ := le_max_left _ _
  have hLC : 4 * |C| + 1 ≤ L₀ := le_max_right _ _
  have hex : Real.exp L₀ ≤ x := Nat.le_ceil _
  have he3 : (20 : ℝ) ≤ Real.exp L₀ := by
    have := Real.add_one_le_exp L₀
    have h3 : Real.exp 3 ≤ Real.exp L₀ := Real.exp_le_exp.mpr hL3
    have : (20 : ℝ) ≤ Real.exp 3 := by
      have := Real.exp_one_gt_d9
      have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      have h27 : (2.718 : ℝ) ≤ Real.exp 1 := le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)
      have := pow_le_pow_left₀ (by norm_num) h27 3
      norm_num at this; linarith
    linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hx2 : 2 ≤ x := by exact_mod_cast (show (2 : ℝ) ≤ x by linarith)
  have hL : L₀ ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hex
  have hlogpos : 0 < Real.log x := by linarith
  -- q = 1 and q = 3, y = x
  have h1 := hC x hx2 1 le_rfl (by rw [Real.rpow_one]; push_cast; linarith) 0 (Nat.coprime_one_right 0)
    x (by positivity) le_rfl
  have h3 := hC x hx2 3 (by norm_num) (by rw [Real.rpow_one]; push_cast; linarith) 1
    (Nat.coprime_one_left 3) x (by positivity) le_rfl
  rw [theta_res_irrelevant _ _ (q := 3) (a := 1) (q' := 1) (a' := 0) (by norm_num) one_ne_zero]
    at h3
  have hφ3 : ((Nat.totient 3 : ℕ) : ℝ) = 2 := by
    rw [Nat.totient_prime Nat.prime_three]; norm_num
  rw [hφ3] at h3
  simp only [Nat.totient_one, Nat.cast_one, div_one, one_mul] at h1 h3
  set θ := Xi2012.thetaReal (Xi2012.primesUpTo x) (x : ℝ) 1 0
  have hsq : (2 : ℝ) * 1 = 2 := by norm_num
  rw [show ((2 : ℝ) * 1) = 2 by norm_num, Real.rpow_two] at h1 h3
  rw [abs_le] at h1 h3
  have hB : (x : ℝ) / 2 ≤ 2 * (C * x / Real.log x ^ 2) := by linarith [h1.1, h1.2, h3.1, h3.2]
  have hL2 : 4 * |C| + 1 ≤ Real.log x ^ 2 := by nlinarith
  rw [mul_div_assoc', le_div_iff₀ (by positivity)] at hB
  have : C ≤ |C| := le_abs_self C
  nlinarith
