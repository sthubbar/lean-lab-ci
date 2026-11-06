import LeanLab.HardyLittlewood1923.Decomp448b
import LeanLab.HardyLittlewood1923.Convolution448
import LeanLab.HardyLittlewood1923.Decomp415b
import LeanLab.HardyLittlewood1923.Decomp276g

/-!
AI wrote this Lean code for CODEX task448.
P0004 page 7 equations 1.46 and 1.47 and page 22 equation 3.115.
Goldbach is OPEN.
-/
namespace LeanLab.HardyLittlewood1923.Decomp448c
open Real MeasureTheory Finset
open LeanLab.HardyLittlewood1923.Decomp276b
open LeanLab.HardyLittlewood1923.Decomp276a
open LeanLab.HardyLittlewood1923.Decomp415b

/-- P0004 page 22 equation 3.115. The radial coefficient for the cubic prime series. -/
noncomputable def tripleCoeff (n m : ℕ) : ℂ :=
  (nur 3 m : ℂ) * Complex.exp (-(m : ℂ) / n)

/-- P0004 page 22 equation 3.115. A polynomial majorant ensures absolute convergence. -/
theorem tripleCoeff_summable {n : ℕ} (hn : 0 < n) :
    Summable (fun m : ℕ => ‖tripleCoeff n m‖) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb (m : ℕ) : nur 3 m ≤ 4 * (m : ℝ) ^ 5 := by
    by_cases hm : m = 0
    · have h := nur_le 3 0
      simpa [hm] using h
    · have h := Decomp276g.nur_le_power_log 2 m (by omega)
      calc
        _ ≤ 4 * (m : ℝ) ^ 2 * Real.log m ^ 3 := by norm_num at h; exact h
        _ ≤ 4 * (m : ℝ) ^ 2 * (m : ℝ) ^ 3 := by
          gcongr
          exact Real.log_le_self (Nat.cast_nonneg m)
        _ = _ := by ring
  have hs := (Real.summable_pow_mul_exp_neg_nat_mul 5
    (by positivity : 0 < 1 / (n : ℝ))).mul_left 4
  apply hs.of_norm_bounded
  intro m
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [tripleCoeff, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (nur_nonneg 3 m), Complex.norm_exp]
  have hre : (-(m : ℂ) / n).re = -(m : ℝ) / n := by simp
  rw [hre]
  calc
    _ ≤ (4 * (m : ℝ) ^ 5) * Real.exp (-(m : ℝ) / n) := by
      gcongr
      exact hb m
    _ = _ := by
      rw [show -(m : ℝ) / n = -(1 / (n : ℝ)) * m by ring]
      ring

/-- LEAF. P0004 page 7 equations 1.46 and 1.47 and page 22 before equation 3.115.
Multiplication of the absolutely convergent prime series counts ordered prime triples.
This is a power series identity. It contains no angular integration or extracted coefficient. -/
theorem prime_cube_expansion {n : ℕ} (hn : 0 < n) (θ : ℝ) :
    primeSeries (localY n θ) ^ 3 =
      ∑' m : ℕ, (nur 3 m : ℂ) * Complex.exp (-(m : ℂ) * localY n θ) := by
  have hz : 0 < (localY n θ).re := by rw [localY_re]; positivity
  exact Convolution448.primeSeries_power hz 3

/-- P0004 page 22 equation 3.115.
The cubic power series has the radial triple coefficients as natural Fourier modes.
Uses the proved prime_cube_expansion. -/
theorem cubic_fourier_expansion {n : ℕ} (hn : 0 < n) (θ : ℝ) :
    primeSeries (localY n θ) ^ 3 =
      ∑' m : ℕ, tripleCoeff n m * fourier (T := 2 * π) (m : ℤ) θ := by
  rw [prime_cube_expansion hn]
  apply tsum_congr
  intro m
  rw [localY, Fourier448.exponential_mode]
  simp only [tripleCoeff, div_eq_mul_inv, one_div]
  ring

/-- P0004 page 22 equation 3.115.
The exact sealed coefficient identity follows from convolution and proved Fourier integration.
Uses the proved prime_cube_expansion. -/
theorem coefficient_integral {n : ℕ} (hn : 4 ≤ n) :
    (nur 3 n : ℂ) = (1 / (2 * π : ℂ)) *
      ∫ θ in (0 : ℝ)..(2 * π), Complex.exp ((n : ℂ) * localY n θ) *
        primeSeries (localY n θ) ^ 3 := by
  have hnpos : 0 < n := by omega
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hc := Fourier448.fourierCoeffOn_nat_series (tripleCoeff n)
    (tripleCoeff_summable hnpos) (n : ℤ)
  simp only [Int.natCast_nonneg, not_lt_of_ge, if_false, Int.toNat_natCast] at hc
  have hfun : (fun θ : ℝ => primeSeries (localY n θ) ^ 3) =
      (fun θ : ℝ => ∑' m : ℕ, tripleCoeff n m * fourier (T := 2 * π) (m : ℤ) θ) :=
    funext (cubic_fourier_expansion hnpos)
  rw [← hfun, fourierCoeffOn_eq_integral] at hc
  simp only [sub_zero, smul_eq_mul, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat] at hc
  have hw (θ : ℝ) : Complex.exp ((n : ℂ) * localY n θ) =
      Complex.exp 1 * fourier (T := 2 * π - 0) (-(n : ℤ)) θ := by
    rw [fourier_coe_apply]
    have he : (n : ℂ) * localY n θ = 1 +
        (2 * π * Complex.I * (-(n : ℤ)) * θ / ((2 * π - 0 : ℝ) : ℂ)) := by
      simp only [localY, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat,
        Complex.ofReal_zero, sub_zero, Int.cast_neg, Int.cast_natCast]
      have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp
      <;> ring
    rw [he, Complex.exp_add]
    simp only [Int.cast_neg, Int.cast_natCast]
  simp_rw [hw, mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  symm
  calc
    _ = Complex.exp 1 * tripleCoeff n n := by rw [← hc]; ring
    _ = (nur 3 n : ℂ) := by
      rw [tripleCoeff, neg_div, div_self hnC]
      rw [show Complex.exp 1 * ((nur 3 n : ℂ) * Complex.exp (-1)) =
          (nur 3 n : ℂ) * (Complex.exp 1 * Complex.exp (-1)) by ring,
        ← Complex.exp_add]
      simp

/-- P0004 page 22 equations 3.115 and 3.116.
Uses the proved finite covering. -/
theorem coefficient_dissection {n : ℕ} (hn : 4 ≤ n) :
    (nur 3 n : ℂ) =
      ∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
        Complex.exp (-2 * π * Complex.I * (n : ℂ) * p / q) * primeArc n p q := by
  have hnpos : 0 < n := by omega
  let f : ℝ → ℂ := fun θ => Complex.exp ((n : ℂ) * localY n θ) *
    primeSeries (localY n θ) ^ 3
  have hw : Continuous (fun θ : ℝ => Complex.exp ((n : ℂ) * localY n θ)) := by
    unfold localY
    fun_prop
  have hf : Continuous f := hw.mul ((Series415.continuous_prime_circle hnpos).pow 3)
  have hp : Function.Periodic f (2 * π) := by
    intro θ
    have hwper := circle_weight_periodic n θ
    have hfper := Series415.periodic_prime_circle n θ
    dsimp only at hwper hfper
    dsimp only [f]
    rw [hwper, hfper]
  have hpart := Decomp448a.farey_integral_dissection
    (show 1 ≤ Nat.sqrt n from Nat.le_sqrt.mpr (by omega)) f hf hp
  rw [coefficient_integral hn, ← hpart, mul_sum]
  apply sum_congr rfl
  intro q hq
  rw [mul_sum]
  apply sum_congr rfl
  intro p hpq
  have hshift (θ : ℝ) :
      Complex.exp ((n : ℂ) * localY n (2 * π * (p : ℝ) / q + θ)) =
        Complex.exp (-2 * π * Complex.I * (n : ℂ) * p / q) *
          Complex.exp ((n : ℂ) * localY n θ) := by
    rw [show (n : ℂ) * localY n (2 * π * (p : ℝ) / q + θ) =
        (-2 * π * Complex.I * (n : ℂ) * p / q) + (n : ℂ) * localY n θ by
      simp only [localY, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_mul,
        Complex.ofReal_ofNat, Complex.ofReal_natCast]
      ring, Complex.exp_add]
  rw [primeArc]
  calc
    _ = (1 / (2 * π : ℂ)) *
        ∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
          Complex.exp (-2 * π * Complex.I * (n : ℂ) * p / q) *
            (Complex.exp ((n : ℂ) * localY n θ) *
              primeSeries (localY n (2 * π * (p : ℝ) / q + θ)) ^ 3) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro θ hθ
      dsimp [f]
      rw [hshift]
      ring
    _ = _ := by rw [intervalIntegral.integral_const_mul]; ring

/-- P0004 pages 22 to 25 equations 3.119 and 3.142.
Uses the proved finite covering. The local cubic transfer is proved. -/
theorem coefficient_transfer {n : ℕ} (hn : 4 ≤ n) {E : ℝ} (hE : 0 ≤ E)
    (hbound : ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤ E) :
    ‖(nur 3 n : ℂ) - fareyModel n‖ ≤
      (3 * Real.exp 1 / (4 * π)) * E *
        ((∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
          ∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
            ‖primeSeries (localY n (2 * π * (p : ℝ) / q + θ))‖ ^ 2) +
         (∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
          ∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
            ‖localPhi n q θ‖ ^ 2)) := by
  rw [coefficient_dissection hn, fareyModel, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
        ‖Complex.exp (-2 * π * Complex.I * (n : ℂ) * p / q) *
          (primeArc n p q - modelArc n p q)‖ :=
      (norm_sum_le _ _).trans (sum_le_sum fun q _ => norm_sum_le _ _)
    _ ≤ ∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
        (3 * Real.exp 1 / (4 * π)) * E *
          ((∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
            ‖primeSeries (localY n (2 * π * (p : ℝ) / q + θ))‖ ^ 2) +
           (∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
            ‖localPhi n q θ‖ ^ 2)) := by
      apply sum_le_sum
      intro q hq
      apply sum_le_sum
      intro p hp
      have hphase : ‖Complex.exp (-2 * π * Complex.I * (n : ℂ) * p / q)‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      rw [norm_mul, hphase, one_mul]
      exact primeArc_error hn (mem_Icc.mp hq).1 (mem_Icc.mp hq).2
        (mem_range.mp (mem_filter.mp hp).1) (mem_filter.mp hp).2 hE
        (hbound q (mem_Icc.mp hq).1 (mem_Icc.mp hq).2 p
          (mem_range.mp (mem_filter.mp hp).1) (mem_filter.mp hp).2)
    _ = _ := by simp_rw [mul_add, sum_add_distrib, mul_sum]

#print axioms tripleCoeff_summable
#print axioms prime_cube_expansion
#print axioms cubic_fourier_expansion
#print axioms coefficient_integral
#print axioms coefficient_dissection
#print axioms coefficient_transfer
end LeanLab.HardyLittlewood1923.Decomp448c
