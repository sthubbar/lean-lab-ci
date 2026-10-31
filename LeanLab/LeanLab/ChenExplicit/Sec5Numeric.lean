/-
AI-written Lean code, Claude, 2026-10-18, run 20261018T1203Z-2488, unit U-0941.
P0010 T. Yamada, Explicit Chen's theorem, arXiv 1511.03409v2, Section 5, (63), (64),
(79), (82), (83) and Theorem 5.1, read in Claude in Chrome on ar5iv.

The numerical steps of Section 5 that turn the sieve constant `255.84406` and `298.87013`
of Theorem 3.1 into Theorem 5.1's `0.5198 ε₀(N)` and `767.7471 / log^{1/2} N`.
`log D = μ log N` with `1/2 - e^{-16} < μ ≤ 1/2`, Yamada's (63); `log^{3/2}` is `x √x`.
* PROVED `exp_neg16_lt`: `e^{-16} < 1.13 · 10⁻⁷`.
* PROVED `eq79_const`: `255.84406 (1 + 1/57) / μ^{3/2} < 736.33191`, MATCH.
* PROVED `eq82`: the whole of (82) for `log N ≥ 10⁴`, MATCH. Its second term is
  `298.87013 · 2^{3/2}` rounded and alone misses the `e^{-16}` correction, about `2.9 · 10⁻⁴`;
  the first term's room `10⁻⁵ / log N` absorbs it once `log N ≥ 10⁴`; not a finding.
* PROVED `eq83_const`: `2 · 845.33239 = 1690.66478`, which is `100` below the printed
  `1790.6648`; the printed constant is weaker, so Theorem 5.1 holds as printed.
* PROVED `thm51_const`: `736.33192 + 1790.6648 / 57 < 767.7471` and `0.1733 + 0.3465 = 0.5198`,
  MATCH; with `1690.66478` Theorem 5.1's constant could be `766`, `thm51_const_sharp`.
Chen's theorem is known; binary Goldbach is OPEN.
-/
import Mathlib

open Real

noncomputable section
namespace LeanLab.ChenExplicit.YamadaSec5

/-- `e^{-16} < 1.13 · 10⁻⁷`. -/
theorem exp_neg16_lt : exp (-16) < 113 / 10 ^ 9 := by
  have h1 := Real.exp_one_gt_d9
  have h16 : exp 16 = exp 1 ^ 16 := by rw [← Real.exp_nat_mul]; norm_num
  have hpow : (2.7182818283 : ℝ) ^ 16 < exp 1 ^ 16 :=
    pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  rw [Real.exp_neg, h16, inv_lt_comm₀ (by positivity) (by norm_num)]
  have : (113 / 10 ^ 9 : ℝ)⁻¹ < (2.7182818283 : ℝ) ^ 16 := by norm_num
  linarith

/-- `√μ ≥ 0.707106701` when `μ > 1/2 - e^{-16}`. -/
lemma sqrt_mu_ge (μ : ℝ) (hμ : 1 / 2 - exp (-16) < μ) : (707106701 / 10 ^ 9 : ℝ) ≤ √μ := by
  have := exp_neg16_lt
  rw [Real.le_sqrt (by norm_num) (by linarith)]
  nlinarith

lemma mu_ge (μ : ℝ) (hμ : 1 / 2 - exp (-16) < μ) : (1 / 2 - 113 / 10 ^ 9 : ℝ) < μ := by
  have := exp_neg16_lt; linarith

/-- (79): `255.84406 (1 + ε₀) / log^{3/2} D < 736.33191 / log^{3/2} N` at `ε₀ ≤ 1/57`. -/
theorem eq79_const (μ : ℝ) (hμ : 1 / 2 - exp (-16) < μ) :
    25584406 / 10 ^ 5 * (1 + 1 / 57) / (μ * √μ) < 73633191 / 10 ^ 5 := by
  have hs := sqrt_mu_ge μ hμ
  have hm := mu_ge μ hμ
  have hpos : 0 < μ * √μ := by
    have : 0 < √μ := by linarith
    have : 0 < μ := by linarith
    positivity
  rw [div_lt_iff₀ hpos]
  have : (1 / 2 - 113 / 10 ^ 9 : ℝ) * (707106701 / 10 ^ 9) ≤ μ * √μ :=
    mul_le_mul hm.le hs (by norm_num) (by linarith)
  nlinarith

/-- **(82), PROVED** for `log N = L ≥ 10⁴`: `0.0866 / log D + 298.87013 / log^{3/2} D` is below
`0.17321 / log N + 845.33239 / log^{3/2} N`, with `log D = μ L`. -/
theorem eq82 (μ L : ℝ) (hμ : 1 / 2 - exp (-16) < μ) (hμ1 : μ ≤ 1 / 2) (hL : 10 ^ 4 ≤ L) :
    866 / 10 ^ 4 / (μ * L) + 29887013 / 10 ^ 5 / (μ * L * √(μ * L)) <
      17321 / 10 ^ 5 / L + 84533239 / 10 ^ 5 / (L * √L) := by
  have hs := sqrt_mu_ge μ hμ
  have hm := mu_ge μ hμ
  have hμ0 : 0 < μ := by linarith
  have hL0 : 0 < L := by linarith
  set r := √L with hr
  have hr2 : r ^ 2 = L := Real.sq_sqrt hL0.le
  have hr100 : 100 ≤ r := by
    rw [hr, Real.le_sqrt (by norm_num) hL0.le]; linarith
  have hsm : √(μ * L) = √μ * r := Real.sqrt_mul hμ0.le L
  rw [hsm]
  set m := √μ with hmdef
  have hm0 : 0 < m := by linarith
  -- first term: 0.0866 / μ ≤ 0.17320004 ; second: 298.87013 / (μ m) ≤ 845.33267
  have t1 : 866 / 10 ^ 4 / μ ≤ 1732000400 / 10 ^ 10 := by
    rw [div_le_iff₀ hμ0]; nlinarith
  have hμm : (1 / 2 - 113 / 10 ^ 9 : ℝ) * (707106701 / 10 ^ 9) ≤ μ * m :=
    mul_le_mul hm.le hs (by norm_num) (by linarith)
  have t2 : 29887013 / 10 ^ 5 / (μ * m) ≤ 845332670 / 10 ^ 6 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have e1 : 866 / 10 ^ 4 / (μ * L) = 866 / 10 ^ 4 / μ / L := by ring
  have e2 : 29887013 / 10 ^ 5 / (μ * L * (m * r)) = 29887013 / 10 ^ 5 / (μ * m) / (L * r) := by
    ring
  rw [e1, e2]
  have hLr : 0 < L * r := by positivity
  have a1 : 866 / 10 ^ 4 / μ / L ≤ 1732000400 / 10 ^ 10 / L := div_le_div_of_nonneg_right t1 hL0.le
  have a2 : 29887013 / 10 ^ 5 / (μ * m) / (L * r) ≤ 845332670 / 10 ^ 6 / (L * r) :=
    div_le_div_of_nonneg_right t2 hLr.le
  -- the room 1e-5 / L beats the deficit 2.8e-4 / (L r) once r ≥ 100
  have key : 1732000400 / 10 ^ 10 / L + 845332670 / 10 ^ 6 / (L * r) <
      17321 / 10 ^ 5 / L + 84533239 / 10 ^ 5 / (L * r) := by
    have : (845332670 / 10 ^ 6 - 84533239 / 10 ^ 5 : ℝ) / (L * r) <
        (17321 / 10 ^ 5 - 1732000400 / 10 ^ 10) / L := by
      rw [div_lt_div_iff₀ hLr hL0]; nlinarith
    have q1 : (845332670 / 10 ^ 6 - 84533239 / 10 ^ 5 : ℝ) / (L * r) =
        845332670 / 10 ^ 6 / (L * r) - 84533239 / 10 ^ 5 / (L * r) := sub_div _ _ _
    have q2 : (17321 / 10 ^ 5 - 1732000400 / 10 ^ 10 : ℝ) / L =
        17321 / 10 ^ 5 / L - 1732000400 / 10 ^ 10 / L := sub_div _ _ _
    linarith
  linarith

/-- (83): `2 · 0.17321 ≤ 0.3465` MATCH, and `2 · 845.33239 = 1690.66478`, `100` below the
printed `1790.6648`. -/
theorem eq83_const :
    2 * (17321 / 10 ^ 5 : ℝ) ≤ 3465 / 10 ^ 4 ∧
      2 * (84533239 / 10 ^ 5 : ℝ) = 169066478 / 10 ^ 5 ∧
      2 * (84533239 / 10 ^ 5 : ℝ) + 99 < 17906648 / 10 ^ 4 := by
  norm_num

/-- Theorem 5.1's constants from (79) and (83) at `ε₀ ≤ 1/57`, MATCH. -/
theorem thm51_const :
    (73633192 / 10 ^ 5 : ℝ) + 17906648 / 10 ^ 4 / 57 < 7677471 / 10 ^ 4 ∧
      (1733 / 10 ^ 4 : ℝ) + 3465 / 10 ^ 4 = 5198 / 10 ^ 4 := by
  norm_num

/-- With the doubled (82) constant `1690.66478` in (83), Theorem 5.1's `767.7471` could be `766`. -/
theorem thm51_const_sharp : (73633192 / 10 ^ 5 : ℝ) + 169066478 / 10 ^ 5 / 57 < 766 := by
  norm_num

end LeanLab.ChenExplicit.YamadaSec5
