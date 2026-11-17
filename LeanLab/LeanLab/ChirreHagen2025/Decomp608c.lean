import LeanLab.ChirreHagen2025.Decomp608a

/-!
Berndt 1972 page 154 display 3.7, normalized periodic Bernoulli bounds.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp608c
open MeasureTheory Set Complex
/-- Berndt 1972 page 154 display 3.7, the uniform constant four for degree at least two. -/
theorem bernoulli_uniform_bound (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    |bernoulliFun n x / (n.factorial : ℝ)| ≤ 4 / (2 * Real.pi) ^ n := by
  have hs := hasSum_one_div_nat_pow_mul_fourier hn hx
  have hb := hs.norm_le_of_bounded (hasSum_zeta_two.mul_left 2) (fun m => ?_)
  · have hf : (0 : ℝ) < n.factorial := by positivity
    have hp : (0 : ℝ) < (2 * Real.pi) ^ n := by positivity
    have heq : ‖-(2 * (Real.pi : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
        (bernoulliFun n x : ℂ)‖ = (2 * Real.pi) ^ n / n.factorial * |bernoulliFun n x| := by
      simp [norm_mul, norm_div, norm_pow, abs_of_pos Real.pi_pos]
    rw [heq] at hb
    rw [abs_div, abs_of_pos hf]
    apply (div_le_div_iff₀ hf hp).2
    have hpi : 2 * (Real.pi ^ 2 / 6) ≤ 4 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have h := hb.trans hpi
    apply (div_le_iff₀ hf).mp ?_
    convert h using 1 <;> ring
  · by_cases hm : m = 0
    · subst m
      simp [show n ≠ 0 by omega]
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
      have hmp : (0 : ℝ) < m := by positivity
      have hpow : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ n := pow_le_pow_right₀ hm1 hn
      have hf1 : ‖fourier (m : ℤ) (x : UnitAddCircle)‖ = 1 := by
        simp [fourier_apply]
      have hf2 : ‖fourier (-(m : ℤ)) (x : UnitAddCircle)‖ = 1 := by
        simp [fourier_apply]
      have hsum : ‖fourier (m : ℤ) (x : UnitAddCircle) +
          (-1 : ℂ) ^ n * fourier (-(m : ℤ)) (x : UnitAddCircle)‖ ≤ 2 := by
        calc
          _ ≤ ‖fourier (m : ℤ) (x : UnitAddCircle)‖ +
              ‖(-1 : ℂ) ^ n * fourier (-(m : ℤ)) (x : UnitAddCircle)‖ := norm_add_le _ _
          _ = 2 := by norm_num [hf1, hf2, norm_mul, norm_pow]
      simp only [norm_mul, norm_div, norm_one, norm_pow, Complex.norm_natCast]
      calc
        _ ≤ 1 / (m : ℝ) ^ n * 2 := mul_le_mul_of_nonneg_left hsum (by positivity)
        _ ≤ 2 * (1 / (m : ℝ) ^ 2) := by
          have := one_div_le_one_div_of_le (pow_pos hmp 2) hpow
          nlinarith

/-- Berndt 1972 pages 151 and 152, periodic normalized Bernoulli function.
At integer points use the left polynomial endpoint. Integrals ignore these points. -/
noncomputable def periodicBernoulli (n : ℕ) (x : ℝ) : ℝ :=
  bernoulliFun n (Int.fract x) / (n.factorial : ℝ)

/-- Berndt 1972 page 155, the elementary degree-one periodic bound. -/
theorem periodicBernoulli_one_bound (x : ℝ) : |periodicBernoulli 1 x| ≤ 1 / 2 := by
  simp only [periodicBernoulli, bernoulliFun_one, Nat.factorial_one, Nat.cast_one, div_one]
  rw [abs_le]
  constructor
  · linarith [Int.fract_nonneg x]
  · linarith [Int.fract_lt_one x]

/-- Berndt 1972 page 154 display 3.7, the valid constant-four estimate. -/
theorem periodicBernoulli_uniform_bound (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    |periodicBernoulli n x| ≤ 4 / (2 * Real.pi) ^ n := by
  by_cases h1 : n = 1
  · subst n
    apply (periodicBernoulli_one_bound x).trans
    simp only [pow_one]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).2
    linarith [Real.pi_lt_four]
  · exact bernoulli_uniform_bound n (by omega) (Int.fract x)
      ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

/-- Berndt 1972 page 154 display 3.7 at odd degree three.
A direct cubic estimate supplies the first valid odd base case. -/
theorem periodicBernoulli_three_bound (x : ℝ) : |periodicBernoulli 3 x| ≤ 2 / (2 * Real.pi) ^ 3 := by
  let y := Int.fract x
  have hy0 : 0 ≤ y := Int.fract_nonneg x
  have hy1 : y ≤ 1 := (Int.fract_lt_one x).le
  have hb : bernoulliFun 3 y = y ^ 3 - (3 / 2 : ℝ) * y ^ 2 + (1 / 2 : ℝ) * y := by
    norm_num [bernoulliFun, Polynomial.bernoulli_def, Finset.sum_range_succ,
      bernoulli_eq_bernoulli'_of_ne_one (by decide : (0 : ℕ) ≠ 1),
      bernoulli_eq_bernoulli'_of_ne_one (by decide : (2 : ℕ) ≠ 1),
      bernoulli_eq_bernoulli'_of_ne_one (by decide : (3 : ℕ) ≠ 1)]
    ring
  let v := 2 * y - 1
  have hv : v ^ 2 ≤ 1 := by dsimp [v]; nlinarith
  have hprod : 0 ≤ (1 - 3 * v ^ 2) ^ 2 * (4 - 3 * v ^ 2) :=
    mul_nonneg (sq_nonneg _) (by nlinarith)
  have hs : ((v ^ 3 - v) / 48) ^ 2 ≤ (401 / 50000 : ℝ) ^ 2 := by
    nlinarith only [hprod]
  have ha : |(v ^ 3 - v) / 48| ≤ (401 / 50000 : ℝ) := by
    nlinarith [sq_abs ((v ^ 3 - v) / 48), abs_nonneg ((v ^ 3 - v) / 48)]
  have heq : periodicBernoulli 3 x = (v ^ 3 - v) / 48 := by
    rw [periodicBernoulli]
    change bernoulliFun 3 y / (Nat.factorial 3 : ℝ) = _
    rw [hb]
    norm_num
    dsimp [v]
    ring
  rw [heq]
  apply ha.trans
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 * Real.pi) ^ 3)).2
  calc
    (401 / 50000 : ℝ) * (2 * Real.pi) ^ 3 ≤ (401 / 50000 : ℝ) * (2 * 3.1416) ^ 3 := by
      gcongr
      exact Real.pi_lt_d4.le
    _ ≤ 2 := by norm_num

end LeanLab.ChirreHagen2025.Decomp608c
