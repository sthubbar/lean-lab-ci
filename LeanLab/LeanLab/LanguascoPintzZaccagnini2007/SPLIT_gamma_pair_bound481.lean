import LeanLab.LanguascoPintzZaccagnini2007.Decomp481c

/-!
Split of `gamma_pair_bound481` of `Decomp481c`.

The target bounds the norm of `gammaPair481 s t n` by `π * n` for `s, t` with real parts in
`[1/2, 1]` and `1 ≤ n`. `gammaPair481` is a product of two independent factors,

`gammaPair481 s t n = (Γ s * Γ t / Γ (s + t)) * (n : ℂ) ^ (s + t - 1)`,

so the norm is the product of the two factor norms and the two are estimated separately.

The first factor is the Beta quotient. The Beta integral is the modulus-majorant of the Gamma
quotient: replacing each exponent `s`, `t` by its real part can only enlarge the integral of the
modulus, and at real parts at least one half the Beta integral is largest at the smallest
parameters, where it equals `π`. Hence the quotient is at most `π` in this strip.

The second factor is a complex power of a positive integer base. Its norm is the real power
`n ^ ((s + t).re - 1)`, and since `(s + t).re ≤ 2` the exponent is at most `1`, while the base is
at least `1`, so that power is at most `n`.

`gamma_pair_bound481_split` below is proved from the five leaves with no `sorry`, and does not use
`gamma_pair_bound481`.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real
open scoped Classical

noncomputable section

/-- LEAF. First step: identify the modulus of the Gamma quotient with the modulus of the Beta
integral. In the strip of the target both real parts are positive, so the Beta integral exists and
the Gamma factors multiply to `Γ (s + t)` times it; dividing by the nonvanishing `Γ (s + t)` gives
the identity of norms. This is the reduction step, an identity and not an estimate. -/
theorem gamma_ratio_norm_eq_beta481 {s t : ℂ}
    (hs0 : (1 / 2 : ℝ) ≤ s.re) (ht0 : (1 / 2 : ℝ) ≤ t.re) :
    ‖Complex.Gamma s * Complex.Gamma t / Complex.Gamma (s + t)‖ =
      ‖Complex.betaIntegral s t‖ := by
  sorry

/-- LEAF. Second step: the Beta integral of the complex pair is dominated by the Beta integral of
its real parts. The integrand of the real-part Beta integral is the pointwise modulus of the
integrand of the complex one, so the norm of the integral is at most the integral of the modulus,
which is the real-part Beta integral. -/
theorem beta_norm_le_re_beta481 {s t : ℂ}
    (hs0 : (1 / 2 : ℝ) ≤ s.re) (ht0 : (1 / 2 : ℝ) ≤ t.re) :
    ‖Complex.betaIntegral s t‖ ≤ ‖Complex.betaIntegral (s.re : ℂ) (t.re : ℂ)‖ := by
  sorry

/-- LEAF. Third step: the real-parameter Beta integral is at most `π` once both parameters are at
least one half. On `(0, 1)` the integrand decreases in each parameter, so the integral is largest at
the pair `(1/2, 1/2)`, where it equals the square of `Γ (1/2)` divided by `Γ 1`, that is `π`. -/
theorem beta_real_half_le_pi481 {a b : ℝ}
    (ha : (1 / 2 : ℝ) ≤ a) (hb : (1 / 2 : ℝ) ≤ b) :
    ‖Complex.betaIntegral (a : ℂ) (b : ℂ)‖ ≤ Real.pi := by
  sorry

/-- LEAF. Fourth step: the norm of the power factor is the real power at the real part of the
exponent. The base is the positive integer `n`, so the norm of `n ^ w` is `n ^ w.re`. -/
theorem cpow_norm_eq481 {s t : ℂ} {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (s + t - 1)‖ = (n : ℝ) ^ ((s + t).re - 1) := by
  sorry

/-- LEAF. Fifth step: a real power of a base at least one is at most the base itself when the
exponent is at most one. Here `σ = (s + t).re` is at most two, so the exponent `σ - 1` is at most
one, and the base `n` is at least one. -/
theorem rpow_sub_one_le_self481 {n : ℕ} {σ : ℝ} (hn : 1 ≤ n) (hσ : σ ≤ 2) :
    (n : ℝ) ^ (σ - 1) ≤ (n : ℝ) := by
  sorry

/-- The target of `Decomp481c`, proved from the leaves above with no `sorry`: the Gamma quotient is
at most `π`, the power factor is at most `n`, and both are nonnegative, so their product is at most
`π * n`. -/
theorem gamma_pair_bound481_split {s t : ℂ}
    (hs0 : (1 / 2 : ℝ) ≤ s.re) (ht0 : (1 / 2 : ℝ) ≤ t.re)
    (hs1 : s.re ≤ 1) (ht1 : t.re ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖gammaPair481 s t n‖ ≤ Real.pi * n := by
  have hA : ‖Complex.Gamma s * Complex.Gamma t / Complex.Gamma (s + t)‖ ≤ Real.pi := by
    rw [gamma_ratio_norm_eq_beta481 hs0 ht0]
    exact (beta_norm_le_re_beta481 hs0 ht0).trans (beta_real_half_le_pi481 hs0 ht0)
  have hB : ‖(n : ℂ) ^ (s + t - 1)‖ ≤ (n : ℝ) := by
    rw [cpow_norm_eq481 (s := s) (t := t) hn]
    refine rpow_sub_one_le_self481 hn ?_
    have hst : (s + t).re = s.re + t.re := Complex.add_re s t
    linarith
  rw [gammaPair481, norm_mul]
  exact mul_le_mul hA hB (norm_nonneg _) Real.pi_pos.le

#print axioms LeanLab.LPZ2007.gamma_pair_bound481_split

end

end LeanLab.LPZ2007
