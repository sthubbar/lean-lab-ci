/-
P0069 Baker Harman Pintz 1997, pages 6 and 7, displays 2.4 and 2.5.
Display 2.5 for a single major arc: the integral of S1 S2 e(-Nt) over the arc centered
at r/q differs from the principal model, the Ramanujan summand times the short eta
integral of display 2.6, by the arc length times the pointwise replacement errors of
S1 and of S2. For a modulus that is not squarefree the model vanishes and only the
trivial bound for S2 is used.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
import LeanLab.BHP1997.Route512MajorSq

namespace LeanLab.BHP1997.Route512Major
open Classical Complex MeasureTheory Set

/-- P0069 page 7 display 2.5, pointwise form on one arc: at `r/q + η` with `|η| ≤ h` the
product S1 S2 differs from the product of the two principal models by at most the S1
replacement error times the trivial bound `V` for S2, plus the size of the S1 model times
the S2 replacement error. The coefficients `a` are supported on integers coprime to `q`,
hypothesis iii of Theorem 2; the coefficients `b` are arbitrary. -/
theorem major_pointwise512j (loI hiI loJ hiJ : ℕ) (a b : ℕ → ℂ) {q : ℕ} [NeZero q] (r : ℕ)
    (hr : Nat.Coprime r q) (w₁ w₂ : ℂ) (M₁ M₂ V T₁ T₂ h : ℝ)
    (hT₁ : (hiI : ℝ) ≤ T₁) (hT₂ : (hiJ : ℝ) ≤ T₂) (hh : 0 ≤ h)
    (hsupp : ∀ k ∈ Finset.Ioc loI hiI, a k ≠ 0 → Nat.Coprime k q)
    (h1 : ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ T₁ →
      ‖∑ k ∈ (Finset.Ioc loI hiI).filter (fun k : ℕ => (k : ℝ) ≤ t),
        (a k * χ (k : ZMod q) - Thm2.delta χ * w₁)‖ ≤ M₁)
    (h4 : ∀ n : ℕ, n ∣ q → ∀ χ : DirichletCharacter ℂ n, ∀ t : ℝ, t ≤ T₂ →
      ‖∑ m ∈ (Finset.Ioc loJ hiJ).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (b m * χ (m : ZMod n) - Thm2.delta χ * w₂)‖ ≤ M₂)
    (hV : ∑ m ∈ Finset.Ioc loJ hiJ, ‖b m‖ ≤ V) (η : ℝ) (hη : |η| ≤ h) :
    ‖(∑ k ∈ Finset.Ioc loI hiI,
          a k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) *
        (∑ m ∈ Finset.Ioc loJ hiJ,
          b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) -
      ((q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ) * w₁ *
          ∑ k ∈ Finset.Ioc loI hiI, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) *
        ((q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ) * w₂ *
          ∑ m ∈ Finset.Ioc loJ hiJ, @fourier 1 (m : ℤ) (η : AddCircle (1 : ℝ)))‖ ≤
      Real.sqrt q * ((1 + 2 * Real.pi * h * ((hiI - loI : ℕ) : ℝ)) * M₁) * V +
        ‖w₁‖ * ((hiI - loI : ℕ) : ℝ) *
          (Real.sqrt q * (q.divisors.card : ℝ) ^ 2 *
            ((1 + 2 * Real.pi * h * ((hiJ - loJ : ℕ) : ℝ)) * M₂)) := by
  have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans (h1 1 T₁ le_rfl)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (h4 1 (one_dvd q) 1 T₂ le_rfl)
  have hφ : (1 : ℝ) ≤ (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have h2π : 0 ≤ 2 * Real.pi * h := mul_nonneg Real.two_pi_pos.le hh
  have hfI : 0 ≤ 1 + 2 * Real.pi * h * ((hiI - loI : ℕ) : ℝ) :=
    add_nonneg zero_le_one (mul_nonneg h2π (Nat.cast_nonneg _))
  have hfJ : 0 ≤ 1 + 2 * Real.pi * h * ((hiJ - loJ : ℕ) : ℝ) :=
    add_nonneg zero_le_one (mul_nonneg h2π (Nat.cast_nonneg _))
  have hB1nn : 0 ≤ Real.sqrt q * ((1 + 2 * Real.pi * h * ((hiI - loI : ℕ) : ℝ)) * M₁) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hfI hM₁)
  have hB2nn : 0 ≤ Real.sqrt q * (q.divisors.card : ℝ) ^ 2 *
      ((1 + 2 * Real.pi * h * ((hiJ - loJ : ℕ) : ℝ)) * M₂) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (mul_nonneg hfJ hM₂)
  have hrU : IsUnit (((r : ℕ) : ℤ) : ZMod q) := by
    rw [Int.cast_natCast]
    exact (ZMod.isUnit_iff_coprime r q).mpr hr
  have hc : ‖(q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ)‖ ≤ 1 := by
    rw [norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_intCast]
    have hμ : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
    calc _ ≤ 1 * 1 := mul_le_mul (inv_le_one_of_one_le₀ hφ) hμ (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hEI : ‖∑ k ∈ Finset.Ioc loI hiI, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))‖ ≤
      ((hiI - loI : ℕ) : ℝ) := by
    calc _ ≤ ∑ k ∈ Finset.Ioc loI hiI, ‖@fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))‖ :=
          norm_sum_le _ _
      _ = _ := by simp
  have hd1 := major_character512j loI hiI a ((r : ℕ) : ℤ) hrU w₁ M₁ T₁ hT₁
    (fun k hk hak => (ZMod.isUnit_iff_coprime k q).mpr (hsupp k hk hak)) h1 η
  rw [gauss_principal512j, Int.cast_natCast] at hd1
  have hB1 : Real.sqrt q * ((1 + 2 * Real.pi * |η| * ((hiI - loI : ℕ) : ℝ)) * M₁) ≤
      Real.sqrt q * ((1 + 2 * Real.pi * h * ((hiI - loI : ℕ) : ℝ)) * M₁) := by
    gcongr
  have hS2 : ‖∑ m ∈ Finset.Ioc loJ hiJ,
      b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))‖ ≤ V := by
    refine le_trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)) hV
    rw [norm_mul, fourier_norm512j, mul_one]
  have hS1' : ‖(q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ) * w₁ *
      ∑ k ∈ Finset.Ioc loI hiI, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))‖ ≤
        ‖w₁‖ * ((hiI - loI : ℕ) : ℝ) := by
    rw [norm_mul, norm_mul]
    calc _ ≤ 1 * ‖w₁‖ * ((hiI - loI : ℕ) : ℝ) := by gcongr
      _ = _ := by ring
  have hsecond : ‖(q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ) * w₁ *
        ∑ k ∈ Finset.Ioc loI hiI, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))‖ *
      ‖(∑ m ∈ Finset.Ioc loJ hiJ,
          b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) -
        (q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ) * w₂ *
          ∑ m ∈ Finset.Ioc loJ hiJ, @fourier 1 (m : ℤ) (η : AddCircle (1 : ℝ))‖ ≤
      ‖w₁‖ * ((hiI - loI : ℕ) : ℝ) *
        (Real.sqrt q * (q.divisors.card : ℝ) ^ 2 *
          ((1 + 2 * Real.pi * h * ((hiJ - loJ : ℕ) : ℝ)) * M₂)) := by
    by_cases hsq : Squarefree q
    · have hd2 := major_squarefree512j loJ hiJ b hsq ((r : ℕ) : ℤ) hrU w₂ M₂ T₂ hT₂ h4 η
      rw [gauss_principal512j, Int.cast_natCast] at hd2
      have hB2 : Real.sqrt q * (q.divisors.card : ℝ) ^ 2 *
            ((1 + 2 * Real.pi * |η| * ((hiJ - loJ : ℕ) : ℝ)) * M₂) ≤
          Real.sqrt q * (q.divisors.card : ℝ) ^ 2 *
            ((1 + 2 * Real.pi * h * ((hiJ - loJ : ℕ) : ℝ)) * M₂) := by
        gcongr
      exact mul_le_mul hS1' (hd2.trans hB2) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
      simp only [Int.cast_zero, mul_zero, zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) hB2nn
  calc
    _ = ‖((∑ k ∈ Finset.Ioc loI hiI,
            a k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) -
          (q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ) * w₁ *
            ∑ k ∈ Finset.Ioc loI hiI, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) *
          (∑ m ∈ Finset.Ioc loJ hiJ,
            b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) +
        ((q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ) * w₁ *
            ∑ k ∈ Finset.Ioc loI hiI, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) *
          ((∑ m ∈ Finset.Ioc loJ hiJ,
            b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) -
          (q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ) * w₂ *
            ∑ m ∈ Finset.Ioc loJ hiJ, @fourier 1 (m : ℤ) (η : AddCircle (1 : ℝ)))‖ := by
      congr 1
      ring
    _ ≤ _ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      exact add_le_add (mul_le_mul (hd1.trans hB1) hS2 (norm_nonneg _) hB1nn) hsecond

/-- P0069 page 7 display 2.5 for one arc: the integral of S1 S2 e(-Nt) over the arc of
half width `h` centered at `r/q` differs from `μ(q)²/φ(q)² w₁ w₂ e(-Nr/q)` times the short
eta integral of display 2.6 by at most the arc length `2h` times the pointwise error of
`major_pointwise512j`. The integrand and the eta integrand are the bodies of
`integrand512`. -/
theorem major_arc512j (loI hiI loJ hiJ : ℕ) (a b : ℕ → ℂ) {q : ℕ} [NeZero q] (r : ℕ)
    (hr : Nat.Coprime r q) (w₁ w₂ : ℂ) (M₁ M₂ V T₁ T₂ h : ℝ) (N : ℕ)
    (hT₁ : (hiI : ℝ) ≤ T₁) (hT₂ : (hiJ : ℝ) ≤ T₂) (hh : 0 ≤ h)
    (hsupp : ∀ k ∈ Finset.Ioc loI hiI, a k ≠ 0 → Nat.Coprime k q)
    (h1 : ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ T₁ →
      ‖∑ k ∈ (Finset.Ioc loI hiI).filter (fun k : ℕ => (k : ℝ) ≤ t),
        (a k * χ (k : ZMod q) - Thm2.delta χ * w₁)‖ ≤ M₁)
    (h4 : ∀ n : ℕ, n ∣ q → ∀ χ : DirichletCharacter ℂ n, ∀ t : ℝ, t ≤ T₂ →
      ‖∑ m ∈ (Finset.Ioc loJ hiJ).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (b m * χ (m : ZMod n) - Thm2.delta χ * w₂)‖ ≤ M₂)
    (hV : ∑ m ∈ Finset.Ioc loJ hiJ, ‖b m‖ ≤ V) :
    ‖(∫ t in Icc ((r : ℝ) / q - h) ((r : ℝ) / q + h),
        (∑ k ∈ Finset.Ioc loI hiI, a k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
          (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))) *
            @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) -
      (ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * (w₁ * w₂) *
        @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ)) *
        ∫ η in (-h)..h,
          (∑ k ∈ Finset.Ioc loI hiI, (1 : ℂ) * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) *
            (∑ m ∈ Finset.Ioc loJ hiJ, (1 : ℂ) * @fourier 1 (m : ℤ) (η : AddCircle (1 : ℝ))) *
              @fourier 1 (-(N : ℤ)) (η : AddCircle (1 : ℝ))‖ ≤
      2 * h * (Real.sqrt q * ((1 + 2 * Real.pi * h * ((hiI - loI : ℕ) : ℝ)) * M₁) * V +
        ‖w₁‖ * ((hiI - loI : ℕ) : ℝ) *
          (Real.sqrt q * (q.divisors.card : ℝ) ^ 2 *
            ((1 + 2 * Real.pi * h * ((hiJ - loJ : ℕ) : ℝ)) * M₂))) := by
  have hmodel := model_arc512j (Finset.Ioc loI hiI) (Finset.Ioc loJ hiJ) N
    ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * (w₁ * w₂))
    ((r : ℝ) / q) h hh
  have hpoly : ∀ (S : Finset ℕ) (c : ℕ → ℂ), Continuous (fun t : ℝ =>
      ∑ k ∈ S, c k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) := fun S c =>
    continuous_finsetSum S fun k _ => continuous_const.mul
      ((map_continuous (fourier (T := (1 : ℝ)) (k : ℤ))).comp (AddCircle.continuous_mk' 1))
  have hpoly1 : ∀ (S : Finset ℕ), Continuous (fun t : ℝ =>
      ∑ k ∈ S, @fourier 1 (k : ℤ) ((t - (r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))) := fun S =>
    continuous_finsetSum S fun k _ =>
      ((map_continuous (fourier (T := (1 : ℝ)) (k : ℤ))).comp (AddCircle.continuous_mk' 1)).comp
        (continuous_id.sub continuous_const)
  have he : Continuous (fun t : ℝ => @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) :=
    (map_continuous (fourier (T := (1 : ℝ)) (-(N : ℤ)))).comp (AddCircle.continuous_mk' 1)
  have hF : Continuous (fun t : ℝ =>
      (∑ k ∈ Finset.Ioc loI hiI, a k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
        (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))) *
          @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) :=
    ((hpoly _ a).mul (hpoly _ b)).mul he
  have hG : Continuous (fun t : ℝ =>
      (ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * (w₁ * w₂) *
        ((∑ k ∈ Finset.Ioc loI hiI,
            @fourier 1 (k : ℤ) ((t - (r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))) *
          (∑ m ∈ Finset.Ioc loJ hiJ,
            @fourier 1 (m : ℤ) ((t - (r : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))) *
          @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) :=
    (continuous_const.mul ((hpoly1 _).mul (hpoly1 _))).mul he
  rw [← hmodel, ← integral_sub hF.integrableOn_Icc hG.integrableOn_Icc]
  have hpt : ∀ t ∈ Icc ((r : ℝ) / q - h) ((r : ℝ) / q + h),
      ‖(∑ k ∈ Finset.Ioc loI hiI, a k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
          (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))) *
            @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ)) -
        (ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * (w₁ * w₂) *
          ((∑ k ∈ Finset.Ioc loI hiI,
              @fourier 1 (k : ℤ) ((t - (r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))) *
            (∑ m ∈ Finset.Ioc loJ hiJ,
              @fourier 1 (m : ℤ) ((t - (r : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))) *
            @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))‖ ≤
      Real.sqrt q * ((1 + 2 * Real.pi * h * ((hiI - loI : ℕ) : ℝ)) * M₁) * V +
        ‖w₁‖ * ((hiI - loI : ℕ) : ℝ) *
          (Real.sqrt q * (q.divisors.card : ℝ) ^ 2 *
            ((1 + 2 * Real.pi * h * ((hiJ - loJ : ℕ) : ℝ)) * M₂)) := by
    intro t ht
    have hη : |t - (r : ℝ) / q| ≤ h := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hk := major_pointwise512j loI hiI loJ hiJ a b r hr w₁ w₂ M₁ M₂ V T₁ T₂ h hT₁ hT₂ hh
      hsupp h1 h4 hV (t - (r : ℝ) / q) hη
    rw [add_sub_cancel] at hk
    calc
      _ = ‖((∑ k ∈ Finset.Ioc loI hiI, a k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
            (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))) -
          ((q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ) * w₁ *
              ∑ k ∈ Finset.Ioc loI hiI,
                @fourier 1 (k : ℤ) ((t - (r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))) *
            ((q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ) * w₂ *
              ∑ m ∈ Finset.Ioc loJ hiJ,
                @fourier 1 (m : ℤ) ((t - (r : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))) *
          @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))‖ := by
        congr 1
        ring
      _ = _ := by rw [norm_mul, fourier_norm512j, mul_one]
      _ ≤ _ := hk
  have hvol : (volume : Measure ℝ) (Icc ((r : ℝ) / q - h) ((r : ℝ) / q + h)) < ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hfin := norm_setIntegral_le_of_norm_le_const hvol hpt
  rw [Real.volume_real_Icc_of_le (by linarith)] at hfin
  refine hfin.trans (le_of_eq ?_)
  ring

end LeanLab.BHP1997.Route512Major
