/-
Burst burst-20261122, session S83, OMOS FEED. P0069 Baker Harman Pintz 1997, proof of Lemma 29 on
pages 43 and 44, the case of one character in F, nonprincipal.
This file splits `Prep1121LowExc.leaf_char_nonprincipal` of Prep1121LowExcLemma29 along the paper's
own two sentences: first [30] Lemma 3.19, Titchmarsh 1986, the finite Perron formula, printed as
[29] in P0069, see NOTE U-1745 in Prep1121LowExcLemma29, which replaces the window sum by a Perron
integral at height Y with error O(Y^eps); then the variant of [8] Lemma 2 on page 44 together with
the kernel bound, which bounds the mean square of that Perron integral over y.
Here Y = x^(11/20+eps), T2 = Y/(qQ) and delta chi = 0 since chi is not principal.

LEAFs:
* `leaf_cnp_perron_pointwise`, HARD, [30] Lemma 3.19 for the finite Dirichlet polynomial;
* `leaf_cnp_perron_integrable`, MEDIUM, the Perron integral is continuous in y, so its square is
  integrable on [Y/2, 3Y];
* `leaf_cnp_mean_square`, HARD, page 44, the variant of [8] Lemma 2 and the kernel bound.
PROVED here: `cnp_combine`, the elementary square inequality and integration, and
`leaf_char_nonprincipal_split`, with exactly the statement of `leaf_char_nonprincipal`.
No new definition, no existing statement changed.
AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.Prep1121LowExcLemma29

namespace LeanLab.BHP1997.Prep1121LowExc
open Classical Complex DecompC165b LowerShortC165
open scoped BigOperators
open MeasureTheory

/-- LEAF: page 43, proof of Lemma 29, first display: by [30] Lemma 3.19, Titchmarsh 1986, printed
as [29], the window sum `Σ_{m ∈ J, y ≤ m ≤ y + yz} b(m) χ(m)` equals
`(1/2πi) ∫_{1/2-iY}^{1/2+iY} G(s, χ) ((y+yz)^s - y^s)/s ds` plus `O(Y^ε)`, P0069 Baker Harman
Pintz 1997. Here `ds = i dt`, so the factor is `(2π)^(-1)`, and the paper's `ε` in `O(Y^ε)` is
taken as `1/100`, so the squared error is at most `K Y^(1/50)`, uniformly for `y` in `[Y/2, 3Y]`.
For the finite sum over `m ∈ J = (Y, 2Y]` this is the per term truncated Perron formula at
abscissa `1/2`, with error `|b(m)| min(1, y/(Y |y - m|))` summed over `m`, which is
`≪ Y^(1/200) log Y` by the divisor bound on `b`. The constants depend on `b` and `ε`. HARD. -/
theorem leaf_cnp_perron_pointwise (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ y ∈ Set.uIcc (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)),
          ‖(∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (b x m : ℂ) * χ (m : ZMod q)) -
              (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
                ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                  (∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2 ≤
            K * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ) := by
  sorry

/-- LEAF: page 44, proof of Lemma 29, the hypothesis "whenever g is continuous" of the variant of
[8] Lemma 2, P0069 Baker Harman Pintz 1997: the Perron integral of page 43 at height `Y` is a
continuous function of `y` on `[Y/2, 3Y]`, since `y > 0` there and the integrand is continuous in
`(y, t)` on a compact set, so its square norm is interval integrable. MEDIUM. -/
theorem leaf_cnp_perron_integrable (b : ℝ → ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          IntervalIntegrable (fun y : ℝ => ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹ *
                ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                  (∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2)
            volume (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) := by
  sorry

/-- LEAF: page 44, proof of Lemma 29, "By a variant of [8], Lemma 2", Harman 1982 Lemma 2 as in
NOTE U-1744, and the bound `|((1+z)^s - 1)/s|^2 ≪ 1/(T2^2 + t^2)`, P0069 Baker Harman Pintz 1997:
the mean square over `y` in `[Y/2, 3Y]` of the Perron integral of page 43 at height `Y` is
`≪ Y^2 ∫_{-Y}^{Y} |G(1/2+it, χ)|^2 / (T2^2 + t^2) dt`, the first step of the display after 5.4.
Here `(y+yz)^s = y^s (1+z)^s`, `y^s = y^(1/2) y^(it)`, and `T2 = Y/(qQ)` with `1/(6 T2) ≤ z ≤ 6/T2`
by the hypotheses on `z`; then Plancherel after `y = e^v` as in NOTE U-1744. The constant is
absolute. HARD. -/
theorem leaf_cnp_mean_square (b : ℝ → ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)), ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹ *
                ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                  (∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2 ≤
            K * (x ^ (11 / 20 + ε)) ^ 2 *
              (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                    (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                  ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) := by
  sorry

/-- The elementary step of page 43: from `|f - P|^2 ≤ K1 M` pointwise and the mean square bound
for `P`, by `|f|^2 ≤ 2|f - P|^2 + 2|P|^2` and integration. PROVED. -/
theorem cnp_combine {a c : ℝ} (hac : a ≤ c) (f P : ℝ → ℂ) {K1 K2 M J : ℝ}
    (h1 : ∀ y ∈ Set.uIcc a c, ‖f y - P y‖ ^ 2 ≤ K1 * M)
    (hP : IntervalIntegrable (fun y => ‖P y‖ ^ 2) volume a c)
    (h2 : ∫ y in a..c, ‖P y‖ ^ 2 ≤ K2 * J) :
    ∫ y in a..c, ‖f y‖ ^ 2 ≤ 2 * (K2 * J) + 2 * (K1 * M) * (c - a) := by
  have hpt : ∀ y ∈ Set.uIcc a c, ‖f y‖ ^ 2 ≤ 2 * ‖P y‖ ^ 2 + 2 * (K1 * M) := by
    intro y hy
    have h := h1 y hy
    have htri : ‖f y‖ ≤ ‖f y - P y‖ + ‖P y‖ := by
      calc ‖f y‖ = ‖(f y - P y) + P y‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have h0 : 0 ≤ ‖f y‖ := norm_nonneg _
    have hsq : ‖f y‖ ^ 2 ≤ (‖f y - P y‖ + ‖P y‖) ^ 2 := pow_le_pow_left₀ h0 htri 2
    nlinarith [sq_nonneg (‖f y - P y‖ - ‖P y‖)]
  have hKM : 0 ≤ K1 * M := le_trans (sq_nonneg _) (h1 a Set.left_mem_uIcc)
  have hg : IntervalIntegrable (fun y => 2 * ‖P y‖ ^ 2 + 2 * (K1 * M)) volume a c :=
    (hP.const_mul 2).add intervalIntegrable_const
  have hPn : 0 ≤ ∫ y in a..c, ‖P y‖ ^ 2 :=
    intervalIntegral.integral_nonneg hac (fun y _ => sq_nonneg _)
  have hca : 0 ≤ (K1 * M) * (c - a) := mul_nonneg hKM (sub_nonneg.mpr hac)
  by_cases hf : IntervalIntegrable (fun y => ‖f y‖ ^ 2) volume a c
  · calc ∫ y in a..c, ‖f y‖ ^ 2 ≤ ∫ y in a..c, (2 * ‖P y‖ ^ 2 + 2 * (K1 * M)) :=
          intervalIntegral.integral_mono_on hac hf hg
            (fun y hy => hpt y (by rwa [Set.uIcc_of_le hac]))
      _ = 2 * (∫ y in a..c, ‖P y‖ ^ 2) + (c - a) * (2 * (K1 * M)) := by
          rw [intervalIntegral.integral_add (hP.const_mul 2) intervalIntegrable_const,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ _ := by nlinarith [h2]
  · rw [intervalIntegral.integral_undef hf]
    nlinarith

/-- P0069 page 43 to 44, proof of Lemma 29, the case `χ ∈ F`. Exactly the statement of
`leaf_char_nonprincipal`. PROVED from the three LEAFs above and `cnp_combine`, using `δχ = 0`. -/
theorem leaf_char_nonprincipal_split (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖(∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (b x m : ℂ) * χ (m : ZMod q)) -
              Thm2.delta χ * (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
                ∫ t in (-Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(Real.exp (Real.log x ^ (1 / 3 : ℝ))),
                  (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                      (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2 ≤
            K * (x ^ (11 / 20 + ε)) ^ 2 *
              (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                    (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                  ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
            K * x ^ (11 / 20 + ε) * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ) := by
  obtain ⟨K1, hK1, C1, hC1⟩ := leaf_cnp_perron_pointwise b hε hb
  obtain ⟨C2, hC2⟩ := leaf_cnp_perron_integrable b hε
  obtain ⟨K2, hK2, C3, hC3⟩ := leaf_cnp_mean_square b hε
  refine ⟨max (2 * K2) (5 * K1), le_max_of_le_left (by linarith), max (max C1 C2) (max C3 1), ?_⟩
  intro x hx q hq1 hq2 z hz1 hz2 χ hχ
  have hx1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : C2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : C3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx4 : (1 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hY0 : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
  have hac : x ^ (11 / 20 + ε) / 2 ≤ 3 * x ^ (11 / 20 + ε) := by linarith
  have hd : Thm2.delta χ = 0 := by simp [Thm2.delta, hχ]
  simp only [hd, zero_mul, sub_zero]
  have key := cnp_combine hac _ _ (hC1 x hx1 q hq1 hq2 z hz1 hz2 χ hχ)
    (hC2 x hx2 q hq1 hq2 z hz1 hz2 χ hχ) (hC3 x hx3 q hq1 hq2 z hz1 hz2 χ hχ)
  refine le_trans key ?_
  have hJ : 0 ≤ (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                    (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                  ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
  have hYe : 0 ≤ (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ) := Real.rpow_nonneg hY0 _
  have hK2' : 2 * K2 ≤ max (2 * K2) (5 * K1) := le_max_left _ _
  have hK1' : 5 * K1 ≤ max (2 * K2) (5 * K1) := le_max_right _ _
  have e1 := mul_le_mul_of_nonneg_right hK2' (mul_nonneg (sq_nonneg (x ^ (11 / 20 + ε))) hJ)
  have e2 := mul_le_mul_of_nonneg_right hK1' (mul_nonneg hY0 hYe)
  nlinarith

end LeanLab.BHP1997.Prep1121LowExc
