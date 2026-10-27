/-
P0071 Languasco and Perelli 1996, proof of Theorem 3, the term I₂⁺, page 356, read from the page
images of papers/P0071.pdf. Unit U-5069, CLOUD 20261019T0213Z-cloud14.

Setting: `Q = X^θ/2`, `V = X^{1-θ}/q = X/(2qQ)`, `K = X Q^{-1/2}`, `h = qQ/2`; GMC(θ) gives
`F(X, u; q, a) ≤ c u` on `V ≤ u ≤ X` with `c = C q² X^ε`. (15) bounds I₂⁺ by
`X^{2+ε} (K^{-2}(F(K) + F(2V)) + ∫_{2V}^K u^{-3}(F(u) + F(2V)) du)`, and (14) multiplies by
`X^ε/(q⁴Q²)`. The paper says "we easily see that the total contribution of I₂⁺ to (14) is
≪ X^{1+ε}/qQ".
PROVED: `two_V_lt_K`, `2V < K` once `X^{θ/2} > √2/q`; the closed forms of `∫_{2V}^K u^{-2}` and
`∫_{2V}^K u^{-3}`; `bracket_le` and `bracket_integral`, the bracket of (15) is at most `(7/4) c/V`; and
`I2plus_contribution`, the contribution to (14) is at most `(7/2) C X^{1+3ε}/(qQ)`, which is the
paper's bound with ε renamed. MATCH.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.LanguascoPerelli1996.B.Thm3I2
open Real intervalIntegral

/-- `∫_a^b u^{-2} du = 1/a - 1/b` for `0 < a ≤ b`. -/
theorem integral_inv_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ u in a..b, (u ^ 2)⁻¹ = 1 / a - 1 / b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => -u⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rw [Set.uIcc_of_le hab] at hx; exact (lt_of_lt_of_le ha hx.1).ne'
    have h := (hasDerivAt_inv hx0).neg
    rw [neg_neg] at h
    exact h
  have hint : IntervalIntegrable (fun u : ℝ => (u ^ 2)⁻¹) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx; rw [Set.uIcc_of_le hab] at hx
    exact pow_ne_zero 2 (lt_of_lt_of_le ha hx.1).ne'
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- `∫_a^b u^{-3} du = (1/a² - 1/b²)/2` for `0 < a ≤ b`. -/
theorem integral_inv_cube {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ u in a..b, (u ^ 3)⁻¹ = (1 / a ^ 2 - 1 / b ^ 2) / 2 := by
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => -(u ^ 2)⁻¹ / 2) ((x ^ 3)⁻¹) x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rw [Set.uIcc_of_le hab] at hx; exact (lt_of_lt_of_le ha hx.1).ne'
    have h2 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have := ((h2.inv (pow_ne_zero 2 hx0)).neg).div_const 2
    convert this using 1
    field_simp
  have hint : IntervalIntegrable (fun u : ℝ => (u ^ 3)⁻¹) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx; rw [Set.uIcc_of_le hab] at hx
    exact pow_ne_zero 3 (lt_of_lt_of_le ha hx.1).ne'
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  field_simp
  ring

/-- `2V < K`, page 356: with `V = X/(2qQ)` and `K = X/√Q` this is `√Q < qQ`, true for
`q ≥ 1` and `Q > 1`. -/
theorem two_V_lt_K {X q Q : ℝ} (hX : 0 < X) (hq : 1 ≤ q) (hQ : 1 < Q) :
    2 * (X / (2 * q * Q)) < X / Q ^ (1 / 2 : ℝ) := by
  have hQ0 : 0 < Q := by linarith
  have hs : 0 < Q ^ (1 / 2 : ℝ) := rpow_pos_of_pos hQ0 _
  have hsq : Q ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) = Q := by
    rw [← rpow_add hQ0]; norm_num
  have hs1 : Q ^ (1 / 2 : ℝ) < Q := by nlinarith [one_lt_rpow hQ (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [show 2 * (X / (2 * q * Q)) = X / (q * Q) by field_simp]
  rw [div_lt_div_iff₀ (by positivity) hs]
  have : Q ^ (1 / 2 : ℝ) < q * Q := by nlinarith
  nlinarith [mul_lt_mul_of_pos_left this hX]

/-- The bracket of (15) with `F(u) ≤ cu`: `K^{-2}(cK + 2cV) + ∫_{2V}^K u^{-3}(cu + 2cV) du`,
the integral in closed form, is at most `(7/4) c/V`. -/
theorem bracket_le {c V K : ℝ} (hc : 0 ≤ c) (hV : 0 < V) (hVK : 2 * V < K) :
    (c * K + c * (2 * V)) / K ^ 2 +
        (c * (1 / (2 * V) - 1 / K) + c * (2 * V) * ((1 / (2 * V) ^ 2 - 1 / K ^ 2) / 2)) ≤
      7 / 4 * c / V := by
  have hK : 0 < K := by linarith
  rw [div_add' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) hV]
  have e : ((c * K + c * (2 * V)) + (c * (1 / (2 * V) - 1 / K) +
      c * (2 * V) * ((1 / (2 * V) ^ 2 - 1 / K ^ 2) / 2)) * K ^ 2) * V =
      c * (K * V + 2 * V ^ 2 + 3 / 4 * K ^ 2 - K * V - V ^ 2) := by
    field_simp; ring
  rw [e]
  have : K * V + 2 * V ^ 2 + 3 / 4 * K ^ 2 - K * V - V ^ 2 ≤ 7 / 4 * K ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this hc]

/-- The bracket of (15) with the integral itself: `F(u) ≤ cu` and `F(2V) ≤ 2cV` give
`K^{-2}(cK + 2cV) + ∫_{2V}^K u^{-3}(cu + 2cV) du ≤ (7/4) c/V`. -/
theorem bracket_integral {c V K : ℝ} (hc : 0 ≤ c) (hV : 0 < V) (hVK : 2 * V < K) :
    (c * K + c * (2 * V)) / K ^ 2 + ∫ u in (2 * V)..K, (u ^ 3)⁻¹ * (c * u + c * (2 * V)) ≤
      7 / 4 * c / V := by
  have h2V : 0 < 2 * V := by linarith
  have hle : 2 * V ≤ K := hVK.le
  have hcongr : ∫ u in (2 * V)..K, (u ^ 3)⁻¹ * (c * u + c * (2 * V)) =
      ∫ u in (2 * V)..K, (c * (u ^ 2)⁻¹ + c * (2 * V) * (u ^ 3)⁻¹) := by
    apply integral_congr
    intro u hu
    rw [Set.uIcc_of_le hle] at hu
    have hu0 : u ≠ 0 := (lt_of_lt_of_le h2V hu.1).ne'
    simp only
    field_simp
  have hi2 : IntervalIntegrable (fun u : ℝ => c * (u ^ 2)⁻¹) MeasureTheory.volume (2 * V) K := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx; rw [Set.uIcc_of_le hle] at hx
    exact pow_ne_zero 2 (lt_of_lt_of_le h2V hx.1).ne'
  have hi3 : IntervalIntegrable (fun u : ℝ => c * (2 * V) * (u ^ 3)⁻¹) MeasureTheory.volume
      (2 * V) K := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx; rw [Set.uIcc_of_le hle] at hx
    exact pow_ne_zero 3 (lt_of_lt_of_le h2V hx.1).ne'
  rw [hcongr, integral_add hi2 hi3, integral_const_mul, integral_const_mul,
    integral_inv_sq h2V hle, integral_inv_cube h2V hle]
  exact bracket_le hc hV hVK

/-- The contribution of I₂⁺ to (14): `X^ε/(q⁴Q²) · X^{2+ε} · (7/4) c/V` with `c = Cq²X^ε` and
`V = X/(2qQ)` equals `(7/2) C X^{1+3ε}/(qQ)`. -/
theorem I2plus_contribution {X q Q C ε : ℝ} (hX : 0 < X) (hq : 0 < q) (hQ : 0 < Q) :
    X ^ ε / (q ^ 4 * Q ^ 2) * X ^ (2 + ε) * (7 / 4 * (C * q ^ 2 * X ^ ε) / (X / (2 * q * Q))) =
      7 / 2 * C * X ^ (1 + 3 * ε) / (q * Q) := by
  have h1 : X ^ (2 + ε) = X ^ 2 * X ^ ε := by
    rw [rpow_add hX, rpow_two]
  have h2 : X ^ (1 + 3 * ε) = X * (X ^ ε) ^ 3 := by
    rw [rpow_add hX, rpow_one, mul_comm 3 ε, rpow_mul hX.le]; norm_cast
  have hXe : 0 < X ^ ε := rpow_pos_of_pos hX ε
  rw [h1, h2]
  field_simp
  ring

/-- I₂⁻, (16), p. 357: `h² F(X, 2V) ≤ h² · C q² (2V) X^ε` with `h = qQ/2` contributes
`C X^{1+2ε}/(4qQ)` to (14). -/
theorem I2minus_contribution {X q Q C ε : ℝ} (hX : 0 < X) (hq : 0 < q) (hQ : 0 < Q) :
    X ^ ε / (q ^ 4 * Q ^ 2) * ((q * Q / 2) ^ 2 * (C * q ^ 2 * (2 * (X / (2 * q * Q))) * X ^ ε)) =
      C * X ^ (1 + 2 * ε) / (4 * (q * Q)) := by
  have h2 : X ^ (1 + 2 * ε) = X * (X ^ ε) ^ 2 := by
    rw [rpow_add hX, rpow_one, mul_comm 2 ε, rpow_mul hX.le]; norm_cast
  rw [h2]; field_simp; ring

/-- GMC at `2X` applies to `u ≥ 2V`: `(2X)^{1-θ}/q ≤ 2V = 2X^{1-θ}/q` for `θ ≥ 0`. -/
theorem gmc_range_2X {X θ q : ℝ} (hX : 0 < X) (hθ : 0 ≤ θ) (hq : 0 < q) :
    (2 * X) ^ (1 - θ) / q ≤ 2 * (X ^ (1 - θ) / q) := by
  rw [mul_rpow (by norm_num) hX.le, mul_div_assoc]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc (2 : ℝ) ^ (1 - θ) ≤ 2 ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 2 := rpow_one 2

/-- J₂, (19), first term: `(hX/K) max F(2X, u) ≤ (hX/K) C q² K X^ε` contributes
`C X^{1+2ε}/(2qQ)` to (14). -/
theorem J2_first {X q Q K C ε : ℝ} (hX : 0 < X) (hq : 0 < q) (hQ : 0 < Q) (hK : 0 < K) :
    X ^ ε / (q ^ 4 * Q ^ 2) * (q * Q / 2 * X / K * (C * q ^ 2 * K * X ^ ε)) =
      C * X ^ (1 + 2 * ε) / (2 * (q * Q)) := by
  have h2 : X ^ (1 + 2 * ε) = X * (X ^ ε) ^ 2 := by
    rw [rpow_add hX, rpow_one, mul_comm 2 ε, rpow_mul hX.le]; norm_cast
  rw [h2]; field_simp

/-- J₂, (19), second term: `∫_{2V}^K u^{-3/2} (cu)^{1/2} du = c^{1/2} log(K/2V)`. -/
theorem J2_integral {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 < a) (hab : a ≤ b) :
    ∫ u in a..b, u ^ (-(3 : ℝ) / 2) * (c * u) ^ (1 / 2 : ℝ) = c ^ (1 / 2 : ℝ) * Real.log (b / a) := by
  have hcongr : ∫ u in a..b, u ^ (-(3 : ℝ) / 2) * (c * u) ^ (1 / 2 : ℝ) =
      ∫ u in a..b, c ^ (1 / 2 : ℝ) * u⁻¹ := by
    apply integral_congr
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
    simp only
    rw [mul_rpow hc hu0.le, mul_left_comm, ← rpow_add hu0, ← rpow_neg_one]
    norm_num
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [hcongr, integral_const_mul, integral_inv_of_pos ha hb]

/-- J₂, second term, contribution: `hX · c log²(K/2V)` with `c = C q² X^ε`, `h = qQ/2`, gives
`C X^{1+2ε} log²(K/2V)/(2qQ)`, a power of log over the paper's bound. -/
theorem J2_second {X q Q C ε l : ℝ} (hX : 0 < X) (hq : 0 < q) (hQ : 0 < Q) :
    X ^ ε / (q ^ 4 * Q ^ 2) * (q * Q / 2 * X * (C * q ^ 2 * X ^ ε) * l ^ 2) =
      C * X ^ (1 + 2 * ε) * l ^ 2 / (2 * (q * Q)) := by
  have h2 : X ^ (1 + 2 * ε) = X * (X ^ ε) ^ 2 := by
    rw [rpow_add hX, rpow_one, mul_comm 2 ε, rpow_mul hX.le]; norm_cast
  rw [h2]; field_simp

end LeanLab.LanguascoPerelli1996.B.Thm3I2

