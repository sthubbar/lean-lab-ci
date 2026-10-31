/-
P0022, Kaniecki 1995, Lemma 5, p. 368, from Lemma 4 and the three steps of its proof,
pp. 369-370. CLOUD 20261020T2317Z-cloud53, unit U-6765, T1.

The proof of Lemma 5 has four inputs and one assembly step:
* (18) and Parseval, then (20) inserted into (19): `I ≤ (1/π) ∫_0^∞ k(t) |ζ'/ζ(s) + B(s) + C(s)|² dt`
  with `k(t) = |(e^{δ s} - 1)/s|²`, `e^δ = 1 + 1/T`, `s = σ + it`,
  `B(s) = Σ Λ(n)/n^{2s}` and `C(s) = Σ_p log p/(p^s (p^{2s} - 1))`. Named input `Parseval1920`,
  CONDITIONAL ON RH, since the contour shift behind (18) needs no zeros right of `σ`.
* Lemma 4 bounds `I₁ = ∫ k |ζ'/ζ|²`. Named input `Lemma4` of Statements.lean.
* (21) bounds `I₂ = ∫ k |B|²`. Named input `Bound21`.
* (22) bounds `I₃ = ∫ k |C|²`. Named input `Bound22`.
* Minkowski's inequality in `L²(k dt)`: `I ≤ (1/π)(I₁^{1/2} + I₂^{1/2} + I₃^{1/2})²`, and the
  algebra `f₆ log² T/T` and `f₇ log² T/T` equal the right sides of (21) and (22).
  PROVED here, with the measurability of the three functions, so no cited input is used there.

Main result `lemma5_of`: `Lemma4 → Parseval1920 → Bound21 → Bound22 → Lemma5`.
AI wrote this Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Kaniecki1995.Statements

namespace LeanLab.Kaniecki1995.L5

open LeanLab.Kaniecki1995 Real Complex MeasureTheory
open scoped ArithmeticFunction.vonMangoldt LSeries.notation ENNReal

/-! ### The functions of (19) and (20), p. 369 -/

/-- `s = σ + it`. -/
noncomputable def sAt (σ t : ℝ) : ℂ := (σ : ℂ) + t * I

/-- `B(s) = Σ_{n ≥ 1} Λ(n)/n^{2s}`, the first sum of (20), p. 369. -/
noncomputable def dirB (σ t : ℝ) : ℂ := LSeries ↗Λ (2 * sAt σ t)

/-- The term `log p/(p^s (p^{2s} - 1))` of the second sum of (20), zero off the primes. -/
noncomputable def primeTerm (s : ℂ) (n : ℕ) : ℂ :=
  if n.Prime then (Real.log n : ℂ) / ((n : ℂ) ^ s * ((n : ℂ) ^ (2 * s) - 1)) else 0

/-- `C(s) = Σ_p log p/(p^s (p^{2s} - 1))`, the second sum of (20), p. 369. -/
noncomputable def primeC (σ t : ℝ) : ℂ := ∑' n : ℕ, primeTerm (sAt σ t) n

/-- `∫_0^∞ |(e^{δ(σ+it)} - 1)/(σ+it)|² |F(t)|² dt`, the shape of `I₁, I₂, I₃`, p. 369. -/
noncomputable def wInt (T σ : ℝ) (F : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (kern T σ t * ‖F t‖ ^ 2)

/-- `I₁` is the left side of (8), Lemma 4. -/
theorem lemma4Int_eq (T σ : ℝ) :
    lemma4Int T σ = wInt T σ (fun t => logDerivZeta (sAt σ t)) := rfl

/-! ### The named inputs, pp. 369-370 -/

/-- (18), Parseval, and (20) inserted into (19), p. 369: under RH, for `T > 7.02` and
`1/2 < σ ≤ 3/4`, `I ≤ (1/π) ∫_0^∞ k |ζ'/ζ + B + C|² dt`. CITED, the paper's reference [12]. -/
def Parseval1920 : Prop :=
  RiemannHypothesis → ∀ T σ : ℝ, 7.02 < T → 1 / 2 < σ → σ ≤ 3 / 4 →
    IInt T σ ≤ ENNReal.ofReal (1 / π) *
      wInt T σ (fun t => logDerivZeta (sAt σ t) + dirB σ t + primeC σ t)

/-- (21), p. 370: `I₂ < π/(T(1-σ/T)) (0.886 + log² T/(8Ta²c²) + log T/(4T²ac))`, with
`σ = 1/2 + ac/log T`. Stated with `≤`, weaker than the printed `<`. CITED from the paper's own
proof, which uses (9), (10) and `(ζ'/ζ)'(2) ≤ 0.886`. -/
def Bound21 : Prop :=
  ∀ a c T : ℝ, 7.02 < T → 0 < c → 1 < a → sig a c T ≤ 3 / 4 →
    wInt T (sig a c T) (dirB (sig a c T)) ≤
      ENNReal.ofReal (π / (T * (1 - sig a c T / T)) *
        (0.886 + Real.log T ^ 2 / (8 * T * a ^ 2 * c ^ 2) + Real.log T / (4 * T ^ 2 * a * c)))

/-- (22), p. 370: `I₃ < 4.51 π/(T(1-σ/T))`. Stated with `≤`. CITED from the paper's own proof,
which uses (9), (10) and `(Σ_p log p/(√p (p-1)))² < 4.51`. -/
def Bound22 : Prop :=
  ∀ T σ : ℝ, 7.02 < T → 1 / 2 < σ → σ ≤ 3 / 4 →
    wInt T σ (primeC σ) ≤ ENNReal.ofReal (4.51 * π / (T * (1 - σ / T)))

/-! ### Minkowski's inequality with a weight, PROVED -/

theorem ofReal_sq_eq (w : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal (w * x ^ 2) = ENNReal.ofReal (√w * x) ^ (2 : ℝ) := by
  rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity)]
  rcases le_or_gt 0 w with hw | hw
  · rw [mul_pow, Real.sq_sqrt hw]
  · rw [Real.sqrt_eq_zero'.mpr hw.le, zero_mul, zero_pow two_ne_zero,
      ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hw.le (by positivity))]
    simp

/-- **Minkowski's inequality in `L²(w dμ)` for three functions.** -/
theorem minkowski3 {μ : Measure ℝ} {w : ℝ → ℝ} (hw : Measurable w)
    {A B C : ℝ → ℂ} (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) :
    ∫⁻ t, ENNReal.ofReal (w t * ‖A t + B t + C t‖ ^ 2) ∂μ ≤
      ((∫⁻ t, ENNReal.ofReal (w t * ‖A t‖ ^ 2) ∂μ) ^ (1 / 2 : ℝ) +
       (∫⁻ t, ENNReal.ofReal (w t * ‖B t‖ ^ 2) ∂μ) ^ (1 / 2 : ℝ) +
       (∫⁻ t, ENNReal.ofReal (w t * ‖C t‖ ^ 2) ∂μ) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
  set e : (ℝ → ℂ) → ℝ → ℝ≥0∞ := fun F t => ENNReal.ofReal (√(w t) * ‖F t‖) with he
  have hme : ∀ F : ℝ → ℂ, Measurable F → Measurable (e F) := fun F hF =>
    (hw.sqrt.mul hF.norm).ennreal_ofReal
  have hconv : ∀ F : ℝ → ℂ, ∫⁻ t, ENNReal.ofReal (w t * ‖F t‖ ^ 2) ∂μ =
      ∫⁻ t, e F t ^ (2 : ℝ) ∂μ := fun F =>
    lintegral_congr fun t => ofReal_sq_eq (w t) (norm_nonneg _)
  rw [hconv, hconv, hconv, hconv]
  have hpt : ∀ t, e (fun t => A t + B t + C t) t ≤ e A t + e B t + e C t := by
    intro t
    simp only [he]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : ‖A t + B t + C t‖ ≤ ‖A t‖ + ‖B t‖ + ‖C t‖ :=
      (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    have h0 : 0 ≤ √(w t) := Real.sqrt_nonneg _
    nlinarith
  have hmono : ∫⁻ t, e (fun t => A t + B t + C t) t ^ (2 : ℝ) ∂μ ≤
      ∫⁻ t, ((e A + e B) + e C) t ^ (2 : ℝ) ∂μ :=
    lintegral_mono fun t => ENNReal.rpow_le_rpow (hpt t) (by norm_num)
  have hL1 := ENNReal.lintegral_Lp_add_le (μ := μ) ((hme A hA).add (hme B hB)).aemeasurable
    (hme C hC).aemeasurable (p := 2) (by norm_num)
  have hL2 := ENNReal.lintegral_Lp_add_le (μ := μ) (hme A hA).aemeasurable
    (hme B hB).aemeasurable (p := 2) (by norm_num)
  set X := ∫⁻ t, e (fun t => A t + B t + C t) t ^ (2 : ℝ) ∂μ
  have hX : X = (X ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
    rw [← ENNReal.rpow_mul]; norm_num
  rw [hX]
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  calc X ^ (1 / 2 : ℝ) ≤ (∫⁻ t, ((e A + e B) + e C) t ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hmono (by norm_num)
    _ ≤ _ := hL1
    _ ≤ _ := by gcongr

/-! ### Measurability of the weight and of the three functions -/

theorem continuous_sAt (σ : ℝ) : Continuous (sAt σ) := by
  unfold sAt; fun_prop

theorem measurable_kern (T σ : ℝ) : Measurable (kern T σ) := by
  unfold kern; fun_prop

theorem sAt_re (σ t : ℝ) : (sAt σ t).re = σ := by simp [sAt]

theorem measurable_logDerivZeta {σ : ℝ} (hσ : σ < 1) :
    Measurable fun t => logDerivZeta (sAt σ t) := by
  unfold logDerivZeta
  have hz : Continuous fun t => riemannZeta (sAt σ t) := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    have hne : sAt σ t ≠ 1 := by
      intro h; have := congrArg Complex.re h; rw [sAt_re] at this; simp at this; linarith
    exact (differentiableAt_riemannZeta hne).continuousAt.comp (continuous_sAt σ).continuousAt
  exact ((measurable_deriv riemannZeta).comp (continuous_sAt σ).measurable).div hz.measurable

theorem continuous_dirB {σ : ℝ} (hσ : 1 / 2 < σ) : Continuous (dirB σ) := by
  unfold dirB LSeries
  have hsum : Summable fun n => ‖LSeries.term ↗Λ ((2 * σ : ℝ) : ℂ) n‖ :=
    summable_norm_iff.2 (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simp; linarith))
  refine continuous_tsum (fun n => ?_) hsum (fun n t => ?_)
  · rcases eq_or_ne n 0 with rfl | hn
    · simp only [LSeries.term_zero]; exact continuous_const
    · simp only [LSeries.term_of_ne_zero hn]
      have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      refine continuous_const.div (((continuous_const.mul (continuous_sAt σ))).const_cpow
        (Or.inl hn')) fun t => ?_
      rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  · rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp [sAt]

/-- the summable majorant of `primeTerm`: `8 n^{-5/4}` on the primes -/
noncomputable def uC (n : ℕ) : ℝ := if n.Prime then 8 * (n : ℝ) ^ (-(5 / 4 : ℝ)) else 0

theorem summable_uC : Summable uC := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((Real.summable_nat_rpow.2 (by norm_num : -(5 / 4 : ℝ) < -1)).mul_left 8)
  · unfold uC; split_ifs <;> positivity
  · unfold uC; split_ifs
    · exact le_rfl
    · positivity

/-- `|p^{2s} - 1| ≥ p/2` for a prime `p` and `Re s ≥ 1/2` -/
theorem half_le_norm_den {s : ℂ} (hs : 1 / 2 ≤ s.re) {n : ℕ} (hn : n.Prime) :
    (n : ℝ) / 2 ≤ ‖(n : ℂ) ^ (2 * s) - 1‖ := by
  have hx2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
  have h2 : ‖(n : ℂ) ^ (2 * s)‖ = (n : ℝ) ^ (2 * s.re) := by
    rw [norm_natCast_cpow_of_pos hn.pos]; simp
  have hB : (n : ℝ) ≤ (n : ℝ) ^ (2 * s.re) := by
    conv_lhs => rw [← Real.rpow_one (n : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have := norm_sub_norm_le ((n : ℂ) ^ (2 * s)) 1
  rw [h2, norm_one] at this
  linarith

theorem norm_primeTerm_le {s : ℂ} (hs : 1 / 2 ≤ s.re) (n : ℕ) : ‖primeTerm s n‖ ≤ uC n := by
  unfold primeTerm uC
  split_ifs with hn
  swap; · simp
  have hx2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
  set x : ℝ := (n : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  have h1 : ‖(n : ℂ) ^ s‖ = x ^ s.re := norm_natCast_cpow_of_pos hn.pos s
  have hA : x ^ (1 / 2 : ℝ) ≤ x ^ s.re := Real.rpow_le_rpow_of_exponent_le (by linarith) hs
  have hD := half_le_norm_den hs hn
  have hL : Real.log x ≤ x ^ (1 / 4 : ℝ) / (1 / 4) := Real.log_le_rpow_div hx0.le (by norm_num)
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have key : x ^ (-(5 / 4 : ℝ)) * x ^ (1 / 2 : ℝ) * x ^ (1 : ℝ) = x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; norm_num
  rw [Real.rpow_one] at key
  have hP : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hQ : 0 < x ^ (-(5 / 4 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  rw [norm_div, norm_mul, h1, Complex.norm_real, Real.norm_of_nonneg hlog0]
  have hden : 0 < x ^ s.re * ‖(n : ℂ) ^ (2 * s) - 1‖ :=
    mul_pos (hP.trans_le hA) (by linarith)
  rw [div_le_iff₀ hden]
  calc Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by linarith
    _ = 8 * x ^ (-(5 / 4 : ℝ)) * (x ^ (1 / 2 : ℝ) * (x / 2)) := by rw [← key]; ring
    _ ≤ 8 * x ^ (-(5 / 4 : ℝ)) * (x ^ s.re * ‖(n : ℂ) ^ (2 * s) - 1‖) := by
        gcongr

theorem continuous_primeC {σ : ℝ} (hσ : 1 / 2 ≤ σ) : Continuous (primeC σ) := by
  unfold primeC
  refine continuous_tsum (fun n => ?_) summable_uC
    (fun n t => norm_primeTerm_le (by rw [sAt_re]; exact hσ) n)
  unfold primeTerm
  by_cases hn : n.Prime
  · simp only [hn, ite_true]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne_zero
    refine continuous_const.div ((((continuous_sAt σ)).const_cpow (Or.inl hn')).mul
      ((((continuous_const.mul (continuous_sAt σ))).const_cpow (Or.inl hn')).sub
        continuous_const)) fun t => ?_
    refine mul_ne_zero ?_ ?_
    · rw [Ne, Complex.cpow_eq_zero_iff]; tauto
    · intro h
      have hD := half_le_norm_den (s := sAt σ t) (by rw [sAt_re]; exact hσ) hn
      rw [h, norm_zero] at hD
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
      linarith
  · simp only [hn, ite_false]; exact continuous_const

/-! ### Lemma 5 from Lemma 4 and the three named inputs -/

theorem ofReal_rpow_half (X : ℝ) : ENNReal.ofReal X ^ (1 / 2 : ℝ) = ENNReal.ofReal (√X) := by
  rcases le_or_gt 0 X with hX | hX
  · rw [ENNReal.ofReal_rpow_of_nonneg hX (by norm_num), Real.sqrt_eq_rpow]
  · rw [ENNReal.ofReal_of_nonpos hX.le, Real.sqrt_eq_zero'.mpr hX.le, ENNReal.ofReal_zero,
      ENNReal.zero_rpow_of_pos (by norm_num)]

theorem sig_gt_half {a c T : ℝ} (hT : 7.02 < T) (hc : 0 < c) (ha : 1 < a) :
    1 / 2 < sig a c T := by
  unfold sig
  have : 0 < Real.log T := Real.log_pos (by linarith)
  have : 0 < a * c / Real.log T := div_pos (by nlinarith) this
  linarith

theorem f6_eq {a c T : ℝ} (hT : 7.02 < T) (hs : sig a c T ≤ 3 / 4) :
    f6 a c T * Real.log T ^ 2 / T = π / (T * (1 - sig a c T / T)) *
      (0.886 + Real.log T ^ 2 / (8 * T * a ^ 2 * c ^ 2) + Real.log T / (4 * T ^ 2 * a * c)) := by
  unfold f6
  have hL : Real.log T ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hT0 : T ≠ 0 := by positivity
  have h1 : 1 - sig a c T / T ≠ 0 := by
    have : sig a c T / T < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  field_simp

theorem f7_eq {a c T : ℝ} (hT : 7.02 < T) (hs : sig a c T ≤ 3 / 4) :
    f7 a c T * Real.log T ^ 2 / T = 4.51 * π / (T * (1 - sig a c T / T)) := by
  unfold f7
  have hL : Real.log T ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hT0 : T ≠ 0 := by positivity
  have h1 : 1 - sig a c T / T ≠ 0 := by
    have : sig a c T / T < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  field_simp

/-- **Lemma 5 at one parameter point**: from Lemma 4's inequality (8) at `(a, c, T, α)`,
`Parseval1920` under RH, `Bound21` and `Bound22`. -/
theorem lemma5_at (hRH : RiemannHypothesis) (hP : Parseval1920) (h21 : Bound21) (h22 : Bound22)
    {a c T α : ℝ} (hT : 7.02 < T) (hc : 0 < c) (ha : 1 < a) (hs : sig a c T ≤ 3 / 4)
    (h1 : lemma4Int T (sig a c T) ≤ ENNReal.ofReal (fK a c T α * Real.log T ^ 2 / T)) :
    IInt T (sig a c T) ≤ ENNReal.ofReal
      (1 / π * (√(fK a c T α) + √(f6 a c T) + √(f7 a c T)) ^ 2 * Real.log T ^ 2 / T) := by
  set σ := sig a c T with hσdef
  have hσ1 : 1 / 2 < σ := sig_gt_half hT hc ha
  have hM := minkowski3 (μ := volume.restrict (Set.Ioi (0 : ℝ))) (measurable_kern T σ)
    (measurable_logDerivZeta (σ := σ) (by linarith)) (continuous_dirB hσ1).measurable
    (continuous_primeC hσ1.le).measurable
  change wInt T σ (fun t => logDerivZeta (sAt σ t)) ≤ _ at h1
  have h2 : wInt T σ (dirB σ) ≤ ENNReal.ofReal (f6 a c T * Real.log T ^ 2 / T) := by
    rw [f6_eq hT hs]; exact h21 a c T hT hc ha hs
  have h3 : wInt T σ (primeC σ) ≤ ENNReal.ofReal (f7 a c T * Real.log T ^ 2 / T) := by
    rw [f7_eq hT hs]; exact h22 T σ hT hσ1 hs
  have hP' := hP hRH T σ hT hσ1 hs
  set X := Real.log T ^ 2 / T with hX
  have hX0 : 0 ≤ X := by rw [hX]; have : 0 < T := by linarith
                         positivity
  have e1 : fK a c T α * Real.log T ^ 2 / T = fK a c T α * X := by rw [hX]; ring
  have e2 : f6 a c T * Real.log T ^ 2 / T = f6 a c T * X := by rw [hX]; ring
  have e3 : f7 a c T * Real.log T ^ 2 / T = f7 a c T * X := by rw [hX]; ring
  rw [e1] at h1; rw [e2] at h2; rw [e3] at h3
  calc IInt T σ ≤ ENNReal.ofReal (1 / π) *
        wInt T σ (fun t => logDerivZeta (sAt σ t) + dirB σ t + primeC σ t) := hP'
    _ ≤ ENNReal.ofReal (1 / π) * ((wInt T σ (fun t => logDerivZeta (sAt σ t))) ^ (1 / 2 : ℝ) +
          (wInt T σ (dirB σ)) ^ (1 / 2 : ℝ) + (wInt T σ (primeC σ)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        gcongr; exact hM
    _ ≤ ENNReal.ofReal (1 / π) * (ENNReal.ofReal (fK a c T α * X) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (f6 a c T * X) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (f7 a c T * X) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        gcongr
    _ = ENNReal.ofReal (1 / π * (√(fK a c T α) + √(f6 a c T) + √(f7 a c T)) ^ 2 *
          Real.log T ^ 2 / T) := by
        rw [ofReal_rpow_half, ofReal_rpow_half, ofReal_rpow_half,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.sqrt_mul' _ hX0, Real.sqrt_mul' _ hX0, Real.sqrt_mul' _ hX0]
        have hsq : √X ^ 2 = X := Real.sq_sqrt hX0
        rw [hX] at hsq ⊢
        linear_combination (1 / π * (√(fK a c T α) + √(f6 a c T) + √(f7 a c T)) ^ 2) * hsq


/-- **Kaniecki 1995, Lemma 5, p. 368**, CONDITIONAL ON Lemma 4, `Parseval1920` under RH,
`Bound21` and `Bound22`. The Minkowski step and the measurability are PROVED. -/
theorem lemma5_of (h4 : Lemma4) (hP : Parseval1920) (h21 : Bound21) (h22 : Bound22) :
    Lemma5 := fun hRH a c T α hT hc hα ha hs =>
  lemma5_at hRH hP h21 h22 hT hc ha hs (h4 hRH a c T α hT hc hα ha hs)

end LeanLab.Kaniecki1995.L5

#print axioms LeanLab.Kaniecki1995.L5.minkowski3
#print axioms LeanLab.Kaniecki1995.L5.measurable_logDerivZeta
#print axioms LeanLab.Kaniecki1995.L5.continuous_dirB
#print axioms LeanLab.Kaniecki1995.L5.continuous_primeC
#print axioms LeanLab.Kaniecki1995.L5.norm_primeTerm_le
#print axioms LeanLab.Kaniecki1995.L5.f6_eq
#print axioms LeanLab.Kaniecki1995.L5.f7_eq
#print axioms LeanLab.Kaniecki1995.L5.lemma5_at
#print axioms LeanLab.Kaniecki1995.L5.lemma5_of

