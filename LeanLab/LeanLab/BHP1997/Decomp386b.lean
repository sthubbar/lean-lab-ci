/-
P0069, pages 24 and 25, Lemma 11. CODEX task386.
Three contour estimates supply the sealed Perron comparison.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp386c
import LeanLab.BHP1997.Decomp312a
import LeanLab.BHP1997.DecompC165c

namespace LeanLab.BHP1997.Decomp386b
open Classical Complex Decomp312c Decomp386a
open scoped BigOperators

/-- Page 24, the finite polynomial F on the long coefficient support. -/
noncomputable def criticalPolynomial (a : ℝ → ℕ → ℝ) (x t : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
    (a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half t

/-- Page 25, the vertical Perron integral in display 4.3.
The real parametrization cancels the factor i from ds. -/
noncomputable def windowContour (a : ℝ → ℕ → ℝ) (x y T : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T,
    criticalPolynomial a x t χ *
      (((x : ℂ) ^ Thm4.half t - ((x - y : ℝ) : ℂ) ^ Thm4.half t) / Thm4.half t)

/-- Page 25, the common low height center E below display 4.4. -/
noncomputable def lowCenter (a : ℝ → ℕ → ℝ) (x : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ t in (-(Real.exp (Real.log x ^ (1 / 3 : ℝ))))..(Real.exp (Real.log x ^ (1 / 3 : ℝ))),
      criticalPolynomial a x t χ * (x : ℂ) ^ (Thm4.half t - 1)

/-- LEAF. Page 25, display 4.3, with the stated heights from page 24.
Only sharp Perron truncation and its coefficient error are required.
No mean value or reference average is used. -/
theorem truncated_perron_window (B : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ a : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
      ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ, 1 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, ∀ y : ℝ, 2 ≤ y → y ≤ referenceWidth x →
        ‖(∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊, (a x k : ℂ) * χ (k : ZMod q)) -
          windowContour a x y (x ^ (0.45 - 2 * ε / 3)) χ‖ ≤
            C * x ^ (0.55 + 11 * ε / 12) := by
  sorry

/-- Page 25, the finite critical line polynomial is continuous in height. -/
theorem criticalPolynomial_continuous (a : ℝ → ℕ → ℝ) {x : ℝ} (_hx : 3 ≤ x)
    {q : ℕ} (χ : DirichletCharacter ℂ q) : Continuous (fun t => criticalPolynomial a x t χ) := by
  have hhalf : Continuous Thm4.half := by unfold Thm4.half; fun_prop
  unfold criticalPolynomial
  apply continuous_finsetSum
  intro k hk
  have hk0 : k ≠ 0 := by
    have hh := (Finset.mem_Ioc.mp hk).1
    omega
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  exact continuous_const.div (hhalf.const_cpow (Or.inl hkC))
    (fun t => Complex.cpow_ne_zero_iff.mpr (Or.inl hkC))

/-- Page 25, the Perron kernel is continuous in height on every positive window. -/
theorem windowKernel_continuous {x y : ℝ} (hx : 0 < x) (hxy : 0 < x - y) :
    Continuous (fun t =>
      ((x : ℂ) ^ Thm4.half t - ((x - y : ℝ) : ℂ) ^ Thm4.half t) / Thm4.half t) := by
  have hhalf : Continuous Thm4.half := by unfold Thm4.half; fun_prop
  apply ((hhalf.const_cpow (Or.inl (by exact_mod_cast ne_of_gt hx))).sub
    (hhalf.const_cpow (Or.inl (by exact_mod_cast ne_of_gt hxy)))).div hhalf
  intro t ht
  have hre := congrArg Complex.re ht
  simp [Thm4.half] at hre

/-- Page 25, display 4.4 with an explicit bound for the polynomial.
The remaining analytic input is only a uniform bound on F at low heights. -/
theorem low_height_remainder_bound (a : ℝ → ℕ → ℝ) {x y M : ℝ}
    (hx : 3 ≤ x) (hy : 0 ≤ y) (hyw : y ≤ referenceWidth x) (hM : 0 ≤ M)
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hF : ∀ t : ℝ, |t| ≤ Real.exp (Real.log x ^ (1 / 3 : ℝ)) →
      ‖criticalPolynomial a x t χ‖ ≤ M) :
    ‖windowContour a x y (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ -
      (y : ℂ) * lowCenter a x χ‖ ≤
        ‖(1 / (2 * Real.pi) : ℂ)‖ * 4 * M *
          (Real.exp (Real.log x ^ (1 / 3 : ℝ))) ^ 2 *
          (x / 2) ^ (-(3 / 2 : ℝ)) * y ^ 2 := by
  let T : ℝ := Real.exp (Real.log x ^ (1 / 3 : ℝ))
  let F : ℝ → ℂ := fun t => criticalPolynomial a x t χ
  let K : ℝ → ℂ := fun t =>
    ((x : ℂ) ^ Thm4.half t - ((x - y : ℝ) : ℂ) ^ Thm4.half t) / Thm4.half t
  let L : ℝ → ℂ := fun t => (y : ℂ) * (x : ℂ) ^ (Thm4.half t - 1)
  have hx0 : 0 < x := by linarith
  have hyhalf : y ≤ x / 2 := hyw.trans (referenceWidth_lt_half_x hx).le
  have hxy : 0 < x - y := by linarith
  have hT : 1 ≤ T := by
    apply Real.one_le_exp
    exact Real.rpow_nonneg (Real.log_nonneg (by linarith : 1 ≤ x)) _
  have hT0 : 0 ≤ T := by linarith
  have hhalf : Continuous Thm4.half := by unfold Thm4.half; fun_prop
  have hFc : Continuous F := criticalPolynomial_continuous a hx χ
  have hKc : Continuous K := windowKernel_continuous hx0 hxy
  have hLc : Continuous L := continuous_const.mul
    ((hhalf.sub continuous_const).const_cpow (Or.inl (by exact_mod_cast ne_of_gt hx0)))
  have he : windowContour a x y T χ - (y : ℂ) * lowCenter a x χ =
      (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T, F t * (K t - L t) := by
    simp_rw [mul_sub]
    have hiK : IntervalIntegrable (fun t => F t * K t) MeasureTheory.volume (-T) T :=
      (hFc.mul hKc).intervalIntegrable _ _
    have hiL : IntervalIntegrable (fun t => F t * L t) MeasureTheory.volume (-T) T :=
      (hFc.mul hLc).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hiK hiL]
    have hlin : (∫ t in (-T)..T, F t * L t) =
        (y : ℂ) * ∫ t in (-T)..T, F t * (x : ℂ) ^ (Thm4.half t - 1) := by
      dsimp [L]
      simp_rw [show ∀ t : ℝ, F t * ((y : ℂ) * (x : ℂ) ^ (Thm4.half t - 1)) =
        (y : ℂ) * (F t * (x : ℂ) ^ (Thm4.half t - 1)) by intro t; ring]
      exact intervalIntegral.integral_const_mul _ _
    rw [hlin]
    dsimp [windowContour, lowCenter, T, F, K]
    ring
  have hb : ∀ t ∈ Set.uIoc (-T) T,
      ‖F t * (K t - L t)‖ ≤ M * (2 * T) * (x / 2) ^ (-(3 / 2 : ℝ)) * y ^ 2 := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith : -T ≤ T)] at ht
    have htT : |t| ≤ T := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have hs : ‖Thm4.half t - 1‖ ≤ 2 * T := by
      have he : Thm4.half t - 1 = (- (1 / 2 : ℝ) : ℂ) + (t : ℂ) * I := by
        unfold Thm4.half
        push_cast
        ring
      rw [he]
      calc
        _ ≤ ‖(- (1 / 2 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = (1 / 2 : ℝ) + |t| := by simp [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 2 * T := by linarith
    have hkernel := Decomp386c.perron_kernel_first_order_bound hx0 hy hyhalf t
    change ‖K t - L t‖ ≤ _ at hkernel
    rw [norm_mul]
    calc
      _ ≤ M * (‖Thm4.half t - 1‖ * (x / 2) ^ (-(3 / 2 : ℝ)) * y ^ 2) :=
        mul_le_mul (hF t htT) hkernel (norm_nonneg _) hM
      _ ≤ M * ((2 * T) * (x / 2) ^ (-(3 / 2 : ℝ)) * y ^ 2) := by gcongr
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [he, norm_mul]
  have htlen : |T - -T| = 2 * T := by rw [abs_of_nonneg (by linarith)]; ring
  rw [htlen] at hi
  have hmul := mul_le_mul_of_nonneg_left hi (norm_nonneg (1 / (2 * Real.pi) : ℂ))
  convert hmul using 1; dsimp [T]; ring

/-- Page 25, display 4.4 follows from a uniform logarithmic polynomial bound.
This separates the coefficient moment input from the contour calculation. -/
theorem low_height_of_log_bound (a : ℝ → ℕ → ℝ) (C D X : ℝ)
    (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hF : ∀ x : ℝ, X ≤ x → ∀ q : ℕ, 1 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      ‖criticalPolynomial a x t χ‖ ≤ C * x ^ (1 / 2 : ℝ) * Real.log x ^ D) :
    ∀ A : ℝ, 0 < A → ∃ K Y : ℝ, ∀ x : ℝ, Y ≤ x →
    ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q,
    ∀ y : ℝ, 2 ≤ y → y ≤ referenceWidth x →
      ‖windowContour a x y (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ -
        (y : ℂ) * lowCenter a x χ‖ ≤ K * y * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨Xlog, hlog⟩ := Filter.eventually_atTop.mp
    (Decomp386c.eventually_log_power_le_low_height (D + A))
  let N : ℝ := ‖(1 / (2 * Real.pi) : ℂ)‖
  let K : ℝ := N * 4 * C * (2 : ℝ) ^ (3 / 2 : ℝ)
  have hK : 0 ≤ K := by dsimp [K, N]; positivity
  refine ⟨K, max X (max Xlog 3), ?_⟩
  intro x hx q hq χ y hy hyw
  simp only [max_le_iff] at hx
  obtain ⟨hxX, hxlog, hx3⟩ := hx
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hy0 : 0 ≤ y := by linarith
  let h : ℝ := Real.log x ^ (1 / 3 : ℝ)
  have hb := low_height_remainder_bound a hx3 hy0 hyw
    (show 0 ≤ C * x ^ (1 / 2 : ℝ) * Real.log x ^ D by positivity) χ
    (fun t ht => hF x hxX q hq χ t)
  have hscale : x ^ (1 / 2 : ℝ) * (x / 2) ^ (-(3 / 2 : ℝ)) =
      (2 : ℝ) ^ (3 / 2 : ℝ) / x := by
    rw [Real.div_rpow hx0.le (by norm_num)]
    calc
      _ = (x ^ (1 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ))) / (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by ring
      _ = x ^ (-1 : ℝ) / (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hx0]
        norm_num
      _ = x⁻¹ / ((2 : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
        rw [Real.rpow_neg_one, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (2 : ℝ) ^ (3 / 2 : ℝ) / x := by rw [div_inv_eq_mul, div_eq_mul_inv]; ring
  have hwidth : y ≤ x * Real.exp (-3 * h) := hyw
  have hexp : (Real.exp h) ^ 2 * Real.exp (-3 * h) = Real.exp (-h) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsave : Real.log x ^ D * Real.exp (-h) ≤ Real.log x ^ (-A) := by
    have he : Real.log x ^ D = Real.log x ^ (D + A) * Real.log x ^ (-A) := by
      rw [← Real.rpow_add hl0]
      congr 1
      ring
    rw [he]
    calc
      _ ≤ Real.exp h * Real.log x ^ (-A) * Real.exp (-h) := by
        gcongr
        exact hlog x hxlog
      _ = Real.log x ^ (-A) := by
        rw [mul_right_comm, ← Real.exp_add]
        simp
  have hs : N * 4 * (C * x ^ (1 / 2 : ℝ) * Real.log x ^ D) *
      (Real.exp h) ^ 2 * (x / 2) ^ (-(3 / 2 : ℝ)) * y ^ 2 =
      K * Real.log x ^ D * (Real.exp h) ^ 2 * (y / x) * y := by
    dsimp [K]
    calc
      _ = (N * 4 * C * Real.log x ^ D * (Real.exp h) ^ 2 * y ^ 2) *
        (x ^ (1 / 2 : ℝ) * (x / 2) ^ (-(3 / 2 : ℝ))) := by ring
      _ = _ := by rw [hscale]; ring
  change _ ≤ N * 4 * (C * x ^ (1 / 2 : ℝ) * Real.log x ^ D) *
    (Real.exp h) ^ 2 * (x / 2) ^ (-(3 / 2 : ℝ)) * y ^ 2 at hb
  rw [hs] at hb
  have hyx : y / x ≤ Real.exp (-3 * h) := (div_le_iff₀ hx0).mpr (by simpa [mul_comm] using hwidth)
  calc
    _ ≤ K * Real.log x ^ D * (Real.exp h) ^ 2 * (y / x) * y := hb
    _ ≤ K * Real.log x ^ D * (Real.exp h) ^ 2 * Real.exp (-3 * h) * y := by gcongr
    _ = K * y * (Real.log x ^ D * Real.exp (-h)) := by
      rw [mul_assoc (K * Real.log x ^ D), hexp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (mul_nonneg hK hy0)

/-- Page 25, an auxiliary first divisor moment for the displayed bound on F.
Reuses Mathlib's exact divisor summatory identity and harmonic estimate. -/
theorem divisor_sum_bound (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (n.divisors.card : ℝ)) ≤
      (N : ℝ) * (1 + Real.log N) := by
  have hid := congrArg (fun n : ℕ => (n : ℝ))
    (ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div N)
  simp only [Nat.cast_sum, ArithmeticFunction.sigma_zero_apply] at hid
  rw [hid]
  have hset : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 N, (N : ℝ) / (n : ℝ) :=
      Finset.sum_le_sum (fun n hn => Nat.cast_div_le)
    _ = (N : ℝ) * (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [Finset.mul_sum, hset]
      apply Finset.sum_congr rfl
      intro n hn
      rw [div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (Nat.cast_nonneg N)

/-- Page 25, the displayed polynomial bound holds without a logarithmic loss
when the divisor exponent is nonpositive. -/
theorem polynomial_bound_nonpositive {B : ℝ} (hB : B ≤ 0) (a : ℝ → ℕ → ℝ)
    {C : ℝ} (ha : ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    {x : ℝ} (hx : 3 ≤ x) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖criticalPolynomial a x t χ‖ ≤ 4 * |C| * x ^ (1 / 2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  let S := Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊
  have hcard : (S.card : ℝ) ≤ 2 * x := by
    calc
      _ ≤ (⌊2 * x⌋₊ : ℝ) := by
        dsimp [S]
        rw [Nat.card_Ioc]
        exact_mod_cast Nat.sub_le ⌊2 * x⌋₊ ⌊x / 2⌋₊
      _ ≤ _ := Nat.floor_le (by linarith : 0 ≤ 2 * x)
  have hterm : ∀ k ∈ S,
      ‖(a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half t‖ ≤
        |C| * (x / 2) ^ (-(1 / 2 : ℝ)) := by
    intro k hk
    obtain ⟨hkl, hku⟩ := Finset.mem_Ioc.mp hk
    have hk0 : k ≠ 0 := by omega
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
    have hτ : 1 ≤ (k.divisors.card : ℝ) := by
      have h : 1 ≤ k.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk0⟩
      exact_mod_cast h
    have hpow : (k.divisors.card : ℝ) ^ B ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hτ hB
    have hcoeff : |a x k| ≤ |C| := by
      calc
        _ ≤ C * (k.divisors.card : ℝ) ^ B := ha x k
        _ ≤ |C| * (k.divisors.card : ℝ) ^ B :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ _ := mul_le_of_le_one_right (abs_nonneg C) hpow
    have htwist : ‖(a x k : ℂ) * χ (k : ZMod q)‖ ≤ |C| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg _) (DirichletCharacter.norm_le_one χ _)).trans hcoeff
    have hre : (Thm4.half t).re = (1 / 2 : ℝ) := by simp [Thm4.half]
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hk0), hre, div_eq_mul_inv,
      ← Real.rpow_neg hkpos.le]
    apply mul_le_mul htwist _ (Real.rpow_nonneg hkpos.le _) (abs_nonneg C)
    exact Real.rpow_le_rpow_of_nonpos (by linarith : 0 < x / 2)
      ((Nat.floor_lt' hk0).mp hkl).le (by norm_num)
  have hxs : x * x ^ (-(1 / 2 : ℝ)) = x ^ (1 / 2 : ℝ) := by
    calc
      _ = x ^ (1 : ℝ) * x ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + (-(1 / 2 : ℝ))) := (Real.rpow_add hx0 _ _).symm
      _ = _ := by norm_num
  have hscale : x * (x / 2) ^ (-(1 / 2 : ℝ)) =
      (2 : ℝ) ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
    rw [Real.div_rpow hx0.le (by norm_num), ← mul_div_assoc, hxs,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
  have htwo : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := Real.rpow_one _
  calc
    _ ≤ ∑ k ∈ S, ‖(a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half t‖ := norm_sum_le _ _
    _ ≤ (S.card : ℝ) * (|C| * (x / 2) ^ (-(1 / 2 : ℝ))) := by
      simpa using Finset.sum_le_sum hterm
    _ ≤ (2 * x) * (|C| * (x / 2) ^ (-(1 / 2 : ℝ))) := by gcongr
    _ = (2 * |C|) * ((2 : ℝ) ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by
      calc
        _ = (2 * |C|) * (x * (x / 2) ^ (-(1 / 2 : ℝ))) := by ring
        _ = _ := by rw [hscale]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left htwo
        (show 0 ≤ 2 * |C| * x ^ (1 / 2 : ℝ) by positivity)
      nlinarith

/-- Page 25, the polynomial logarithmic bound has exponent zero for every
nonpositive divisor exponent. -/
theorem divisor_log_bound_nonpositive (B : ℝ) (hB : B ≤ 0) (a : ℝ → ℕ → ℝ)
    (ha : ∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ C D X : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ x : ℝ, X ≤ x →
    ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      ‖criticalPolynomial a x t χ‖ ≤ C * x ^ (1 / 2 : ℝ) * Real.log x ^ D := by
  obtain ⟨C, ha⟩ := ha
  refine ⟨4 * |C|, 0, 3, by positivity, le_rfl, ?_⟩
  intro x hx q hq χ t
  simpa using polynomial_bound_nonpositive hB a ha hx χ t

/-- Page 25, the displayed polynomial bound for divisor exponents at most one.
The first divisor moment gives one logarithmic loss. -/
theorem polynomial_bound_le_one {B : ℝ} (hB : B ≤ 1) (a : ℝ → ℕ → ℝ)
    {C : ℝ} (ha : ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    {x : ℝ} (hx : 3 ≤ x) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖criticalPolynomial a x t χ‖ ≤ 12 * |C| * x ^ (1 / 2 : ℝ) * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hl1 : 1 ≤ Real.log x := by
    apply (Real.le_log_iff_exp_le hx0).2
    exact le_of_lt (Real.exp_one_lt_d9.trans
      (show (2.7182818286 : ℝ) < 3 by norm_num)) |>.trans hx
  have hl0 : 0 ≤ Real.log x := by linarith
  let S := Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊
  let N := ⌊2 * x⌋₊
  have hN1 : (1 : ℕ) ≤ N := (Nat.le_floor_iff (by linarith : 0 ≤ 2 * x)).mpr (by norm_num; linarith)
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNx : (N : ℝ) ≤ 2 * x := Nat.floor_le (by linarith : 0 ≤ 2 * x)
  have hsubset : S ⊆ Finset.Ioc 0 N := by
    intro k hk
    obtain ⟨hkl, hku⟩ := Finset.mem_Ioc.mp hk
    exact Finset.mem_Ioc.mpr ⟨by omega, hku⟩
  have hsum : (∑ k ∈ S, (k.divisors.card : ℝ)) ≤ (2 * x) * (3 * Real.log x) := by
    have hlogN : Real.log N ≤ Real.log (2 * x) := Real.log_le_log hN0 hNx
    have hlog2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    have hlog2x : 1 + Real.log (2 * x) ≤ 3 * Real.log x := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne']
      linarith
    calc
      _ ≤ ∑ k ∈ Finset.Ioc 0 N, (k.divisors.card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun k hk hnot => Nat.cast_nonneg _)
      _ ≤ (N : ℝ) * (1 + Real.log N) := divisor_sum_bound N
      _ ≤ (N : ℝ) * (1 + Real.log (2 * x)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      _ ≤ (2 * x) * (1 + Real.log (2 * x)) :=
        mul_le_mul_of_nonneg_right hNx (by have := Real.log_nonneg (by linarith : 1 ≤ 2 * x); linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog2x (by linarith)
  have hterm : ∀ k ∈ S,
      ‖(a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half t‖ ≤
        |C| * (k.divisors.card : ℝ) * (x / 2) ^ (-(1 / 2 : ℝ)) := by
    intro k hk
    obtain ⟨hkl, hku⟩ := Finset.mem_Ioc.mp hk
    have hk0 : k ≠ 0 := by omega
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
    have hτ : 1 ≤ (k.divisors.card : ℝ) := by
      have h : 1 ≤ k.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk0⟩
      exact_mod_cast h
    have hpow : (k.divisors.card : ℝ) ^ B ≤ (k.divisors.card : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hτ hB
    have hcoeff : |a x k| ≤ |C| * (k.divisors.card : ℝ) := by
      calc
        _ ≤ C * (k.divisors.card : ℝ) ^ B := ha x k
        _ ≤ |C| * (k.divisors.card : ℝ) ^ B :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
    have htwist : ‖(a x k : ℂ) * χ (k : ZMod q)‖ ≤ |C| * (k.divisors.card : ℝ) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg _) (DirichletCharacter.norm_le_one χ _)).trans hcoeff
    have hre : (Thm4.half t).re = (1 / 2 : ℝ) := by simp [Thm4.half]
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hk0), hre,
      div_eq_mul_inv, ← Real.rpow_neg hkpos.le]
    apply mul_le_mul htwist _ (Real.rpow_nonneg hkpos.le _) (by positivity)
    exact Real.rpow_le_rpow_of_nonpos (by linarith : 0 < x / 2)
      ((Nat.floor_lt' hk0).mp hkl).le (by norm_num)
  have hxs : x * x ^ (-(1 / 2 : ℝ)) = x ^ (1 / 2 : ℝ) := by
    calc
      _ = x ^ (1 : ℝ) * x ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + (-(1 / 2 : ℝ))) := (Real.rpow_add hx0 _ _).symm
      _ = _ := by norm_num
  have hscale : x * (x / 2) ^ (-(1 / 2 : ℝ)) =
      (2 : ℝ) ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
    rw [Real.div_rpow hx0.le (by norm_num), ← mul_div_assoc, hxs,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
  have htwo : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := Real.rpow_one _
  calc
    _ ≤ ∑ k ∈ S, ‖(a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half t‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ S, |C| * (k.divisors.card : ℝ) * (x / 2) ^ (-(1 / 2 : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = (|C| * (x / 2) ^ (-(1 / 2 : ℝ))) * ∑ k ∈ S, (k.divisors.card : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (|C| * (x / 2) ^ (-(1 / 2 : ℝ))) * ((2 * x) * (3 * Real.log x)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (6 * |C| * Real.log x) * ((2 : ℝ) ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by
      calc
        _ = (6 * |C| * Real.log x) * (x * (x / 2) ^ (-(1 / 2 : ℝ))) := by ring
        _ = _ := by rw [hscale]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left htwo
        (show 0 ≤ 6 * |C| * Real.log x * x ^ (1 / 2 : ℝ) by positivity)
      nlinarith

/-- Page 25, the polynomial logarithmic bound for divisor exponents at most one. -/
theorem divisor_log_bound_le_one (B : ℝ) (hB : B ≤ 1) (a : ℝ → ℕ → ℝ)
    (ha : ∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ C D X : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ x : ℝ, X ≤ x →
    ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      ‖criticalPolynomial a x t χ‖ ≤ C * x ^ (1 / 2 : ℝ) * Real.log x ^ D := by
  obtain ⟨C, ha⟩ := ha
  refine ⟨12 * |C|, 1, 3, by positivity, by norm_num, ?_⟩
  intro x hx q hq χ t
  simpa using polynomial_bound_le_one hB a ha hx χ t

/-- Page 25, display 4.4 for every divisor exponent at most one.
This uses the first divisor moment and no OPEN leaf. -/
theorem low_height_comparison_le_one (B : ℝ) (hB : B ≤ 1) (a : ℝ → ℕ → ℝ)
    (ha : ∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
    ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q,
    ∀ y : ℝ, 2 ≤ y → y ≤ referenceWidth x →
      ‖windowContour a x y (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ -
        (y : ℂ) * lowCenter a x χ‖ ≤ C * y * Real.log x ^ (-A) := by
  obtain ⟨C, D, X, hC, hD, hF⟩ := divisor_log_bound_le_one B hB a ha
  exact low_height_of_log_bound a C D X hC hD hF

/-- LEAF. Page 25, the displayed bound on F between 4.3 and 4.4.
Only a logarithmic divisor moment bound on the finite polynomial is required.
There is no contour, window comparison or mean value conclusion. -/
theorem divisor_polynomial_log_bound (B : ℝ) (a : ℝ → ℕ → ℝ)
    (ha : ∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ C D X : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ x : ℝ, X ≤ x →
    ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      ‖criticalPolynomial a x t χ‖ ≤ C * x ^ (1 / 2 : ℝ) * Real.log x ^ D := by
  by_cases hB : B ≤ 1
  · exact divisor_log_bound_le_one B hB a ha
  · sorry

/-- Page 25, display 4.4.
Only the low height Taylor error is required. The divisor bound supplies
polynomial growth and the reference width absorbs every logarithmic loss.
CONDITIONAL on divisor_polynomial_log_bound. -/
theorem low_height_comparison (B : ℝ) (a : ℝ → ℕ → ℝ)
    (ha : ∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
    ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q,
    ∀ y : ℝ, 2 ≤ y → y ≤ referenceWidth x →
      ‖windowContour a x y (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ -
        (y : ℂ) * lowCenter a x χ‖ ≤ C * y * Real.log x ^ (-A) := by
  obtain ⟨C, D, X, hC, hD, hF⟩ := divisor_polynomial_log_bound B a ha
  exact low_height_of_log_bound a C D X hC hD hF

/-- Page 25, display 4.4 is proved for nonpositive divisor exponents.
This uses the clean exponent zero polynomial bound and no OPEN leaf. -/
theorem low_height_comparison_nonpositive (B : ℝ) (hB : B ≤ 0) (a : ℝ → ℕ → ℝ)
    (ha : ∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
    ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q,
    ∀ y : ℝ, 2 ≤ y → y ≤ referenceWidth x →
      ‖windowContour a x y (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ -
        (y : ℂ) * lowCenter a x χ‖ ≤ C * y * Real.log x ^ (-A) := by
  obtain ⟨C, D, X, hC, hD, hF⟩ := divisor_log_bound_nonpositive B hB a ha
  exact low_height_of_log_bound a C D X hC hD hF

/-- Page 25, the two high height pieces between displays 4.4 and 4.5.
The mean value input and the kernel bound control these pieces.
There is no coefficient or endpoint truncation conclusion. -/
theorem high_height_comparison {ε : ℝ} (hε : 0 < ε) (hεu : ε < 1 / 10)
    (a : ℝ → ℕ → ℝ) (hm : MeanValue41 ε a) :
    ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
    ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
    ∀ χ : DirichletCharacter ℂ q, ∀ y : ℝ, 2 ≤ y → y ≤ referenceWidth x →
      ‖windowContour a x y (x ^ (0.45 - 2 * ε / 3)) χ -
        windowContour a x y (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ‖ ≤
          C * y * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C, X, hmean⟩ := hm A hA
  have hα : 0 < 0.45 - 2 * ε / 3 := by linarith
  obtain ⟨Xh, hh⟩ := Filter.eventually_atTop.mp
    (Decomp386c.eventually_low_height_le_power hα)
  let N : ℝ := ‖(1 / (2 * Real.pi) : ℂ)‖
  refine ⟨2 * N * |C| * (2 : ℝ) ^ (1 / 2 : ℝ), max X (max Xh 3), ?_⟩
  intro x hx q hq hqx χ y hy hyw
  simp only [max_le_iff] at hx
  obtain ⟨hxX, hxH, hx3⟩ := hx
  have hx0 : 0 < x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hyhalf : y ≤ x / 2 := hyw.trans (referenceWidth_lt_half_x hx3).le
  have hxy : 0 < x - y := by linarith
  let T0 : ℝ := Real.exp (Real.log x ^ (1 / 3 : ℝ))
  let T1 : ℝ := x ^ (0.45 - 2 * ε / 3)
  let F : ℝ → ℂ := fun t => criticalPolynomial a x t χ
  let K : ℝ → ℂ := fun t =>
    ((x : ℂ) ^ Thm4.half t - ((x - y : ℝ) : ℂ) ^ Thm4.half t) / Thm4.half t
  let R : ℝ := (x / 2) ^ (-(1 / 2 : ℝ)) * y
  let M : ℝ := |C| * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have hp : ∀ σ ∈ ({-1, 1} : Finset ℝ),
      (∫ t in T0..T1, ‖F (σ * t)‖) ≤ M := by
    intro σ hσ
    have h := hmean x hxX q hq hqx χ σ hσ
    change (∫ t in T0..T1, ‖F (σ * t)‖) ≤ _ at h
    apply h.trans
    dsimp [M]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hx0.le _)) hL
  have hplus : (∫ t in T0..T1, ‖F t‖) ≤ M := by
    simpa using hp 1 (by simp)
  have hminus : (∫ t in T0..T1, ‖F (-t)‖) ≤ M := by
    simpa using hp (-1) (by simp)
  have ht := Decomp386c.two_tail_norm_bound F K
    (criticalPolynomial_continuous a hx3 χ) (windowKernel_continuous hx0 hxy)
    (hh x hxH) (show 0 ≤ R by dsimp [R]; positivity)
    (fun t => Decomp386c.perron_kernel_bound hx0 hy0 hyhalf t) hplus hminus
  have hpow : (x / 2) ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.div_rpow hx0.le (by norm_num), Real.rpow_neg hx0.le,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  have hfinal : N * (2 * R * M) =
      (2 * N * |C| * (2 : ℝ) ^ (1 / 2 : ℝ)) * y * Real.log x ^ (-A) := by
    dsimp [R, M]
    calc
      _ = (2 * N * |C| * y * Real.log x ^ (-A)) *
        ((x / 2) ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [hpow]; ring
  unfold windowContour
  rw [← mul_sub, norm_mul]
  change N * ‖(∫ t in (-T1)..T1, F t * K t) -
      ∫ t in (-T0)..T0, F t * K t‖ ≤ _
  exact (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq hfinal

/-- Pages 11 and 25, the divisor bound controls each twisted coefficient
on the long polynomial support by every positive power of x. -/
theorem twisted_coefficient_bound (B δ : ℝ) (hδ : 0 < δ)
    (a : ℝ → ℕ → ℝ)
    (ha : ∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 1 ≤ x → ∀ q : ℕ,
    ∀ χ : DirichletCharacter ℂ q, ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ 2 * x →
      ‖(a x k : ℂ) * χ (k : ZMod q)‖ ≤ D * x ^ δ := by
  obtain ⟨C, hcoeff⟩ := ha
  obtain ⟨K, hK, hk⟩ := DecompC165c.coeff_small_power_any B δ hδ
  let b : ℕ → ℂ := fun n => if n = 0 then 0 else ((n.divisors.card : ℝ) ^ B : ℝ)
  have hb : Thm4.CoeffBound b B := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp only [b, ite_true, norm_zero]
      positivity
    · simp only [b, hn, ite_false, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact le_rfl
  refine ⟨|C| * K * (2 : ℝ) ^ δ, by positivity, ?_⟩
  intro x hx q χ k hk1 hkx
  have hk0 : k ≠ 0 := by omega
  have hdiv : (k.divisors.card : ℝ) ^ B ≤ K * (k : ℝ) ^ δ := by
    simpa only [b, hk0, ite_false, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using hk b hb k hk1
  calc
    ‖(a x k : ℂ) * χ (k : ZMod q)‖ ≤ |a x k| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (DirichletCharacter.norm_le_one χ _)
    _ ≤ C * (k.divisors.card : ℝ) ^ B := hcoeff x k
    _ ≤ |C| * (k.divisors.card : ℝ) ^ B :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |C| * (K * (k : ℝ) ^ δ) := mul_le_mul_of_nonneg_left hdiv (abs_nonneg _)
    _ ≤ |C| * (K * (2 * x) ^ δ) := by
      gcongr
    _ = (|C| * K * (2 : ℝ) ^ δ) * x ^ δ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ x)]
      ring

/-- Page 25, an auxiliary obstruction for display 4.4.
A fixed positive coefficient power loss cannot be absorbed by the
subexponential width saving. This is a failed bound, not a paper error. -/
theorem small_power_low_height_obstruction {δ : ℝ} (hδ : 0 < δ) (A : ℝ) :
    ¬ ∃ C X : ℝ, ∀ x : ℝ, max X 3 ≤ x →
      x ^ δ * Real.exp (-Real.log x ^ (1 / 3 : ℝ)) ≤ C * Real.log x ^ A := by
  rintro ⟨C, X, hb⟩
  let c : ℝ := 1 / (|C| + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hδ2 : 0 < δ / 2 := by linarith
  have hs := (isLittleO_log_rpow_rpow_atTop A hδ2).def hc
  have ht := Decomp386c.eventually_low_height_le_power hδ2
  obtain ⟨x, hxsmall, hxheight, hx⟩ :=
    (hs.and (ht.and (Filter.eventually_ge_atTop (max X 3)))).exists
  have hx3 : 3 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl0 _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hxsmall
  have hp : 0 < x ^ (δ / 2) := Real.rpow_pos_of_pos hx0 _
  have hratio : |C| * c < 1 := by
    dsimp [c]
    rw [one_div, ← div_eq_mul_inv, div_lt_one (by positivity)]
    linarith [abs_nonneg C]
  have hlow : x ^ (δ / 2) ≤ x ^ δ * Real.exp (-Real.log x ^ (1 / 3 : ℝ)) := by
    calc
      _ = x ^ δ / x ^ (δ / 2) := by
        rw [← Real.rpow_sub hx0]
        congr 1
        ring
      _ ≤ x ^ δ / Real.exp (Real.log x ^ (1 / 3 : ℝ)) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) (Real.exp_pos _) hxheight
      _ = _ := by rw [Real.exp_neg, div_eq_mul_inv]
  have hh : x ^ (δ / 2) ≤ |C| * (c * x ^ (δ / 2)) := by
    calc
      _ ≤ x ^ δ * Real.exp (-Real.log x ^ (1 / 3 : ℝ)) := hlow
      _ ≤ C * Real.log x ^ A := hb x hx
      _ ≤ |C| * Real.log x ^ A :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hl0 _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hxsmall (abs_nonneg C)
  nlinarith

/-- Page 25, displays 4.3 to 4.5 and finite centering.
This has the exact conclusion of the sealed leaf. It is CONDITIONAL on
truncated_perron_window and divisor_polynomial_log_bound.
The high height estimate is proved from MeanValue41. -/
theorem perron_window_comparison (B : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ a : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
      MeanValue41 ε a → WindowComparison ε a := by
  obtain ⟨η, hη, htrunc⟩ := truncated_perron_window B
  refine ⟨min η (1 / 10), lt_min hη (by norm_num), ?_⟩
  intro ε hε hεη a ha hm
  have hεη' : ε < η := lt_of_lt_of_le hεη (min_le_left _ _)
  have hεu : ε < 1 / 10 := lt_of_lt_of_le hεη (min_le_right _ _)
  obtain ⟨Ct, Xt, ht⟩ := htrunc ε hε hεη' a ha
  let p : ℝ := 0.55 + 11 * ε / 12
  have hp : 0 < p := by dsimp [p]; linarith
  obtain ⟨D, hD, hd⟩ := twisted_coefficient_bound B p hp a ha
  intro A hA
  obtain ⟨Cl, Xl, hl⟩ := low_height_comparison B a ha A hA
  obtain ⟨Ch, Xh, hh⟩ := high_height_comparison hε hεu a hm A hA
  obtain ⟨Xw, hw⟩ := Filter.eventually_atTop.mp
    (Decomp312a.reference_width_long (ε := 0) (by norm_num))
  let K : ℝ := |Ct| + |Cl| + |Ch|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨2 * K + 9 * D, max Xt (max Xl (max Xh (max Xw 3))), ?_⟩
  intro x hx q hq hqx χ y hy hyw
  simp only [max_le_iff] at hx
  obtain ⟨hxt, hxl, hxh, hxw, hx3⟩ := hx
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hw2 : 2 ≤ referenceWidth x := by
    have hs := hw x hxw
    have hr : 1 ≤ x ^ (11 / 20 + (0 : ℝ)) := Real.one_le_rpow hx1 (by norm_num)
    linarith
  have hwx : referenceWidth x ≤ x := referenceWidth_le_x hx1
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have hP : 0 ≤ x ^ p := Real.rpow_nonneg hx0 _
  have hcoeff : ∀ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
      ‖(a x k : ℂ) * χ (k : ZMod q)‖ ≤ D * x ^ p := by
    intro k hk
    have hi := window_subset_I1 hx3 (by linarith : 0 ≤ referenceWidth x) le_rfl hk
    obtain ⟨hkl, hku⟩ := Finset.mem_Ioc.mp hi
    have hk1 : 1 ≤ k := by omega
    have hkx : (k : ℝ) ≤ 2 * x :=
      (by exact_mod_cast hku : (k : ℝ) ≤ (⌊2 * x⌋₊ : ℝ)).trans
        (Nat.floor_le (by linarith : 0 ≤ 2 * x))
    exact hd x hx1 q χ k hk1 hkx
  have hcomp : ∀ z : ℝ, 2 ≤ z → z ≤ referenceWidth x →
      ‖(∑ k ∈ Finset.Ioc ⌊x - z⌋₊ ⌊x⌋₊, (a x k : ℂ) * χ (k : ZMod q)) -
        (z : ℂ) * lowCenter a x χ‖ ≤ K * (z * Real.log x ^ (-A) + x ^ p) := by
    intro z hz hzw
    have ht' := ht x hxt q hq χ z hz hzw
    have hl' := hl x hxl q hq χ z hz hzw
    have hh' := hh x hxh q hq hqx χ z hz hzw
    have hz0 : 0 ≤ z := by linarith
    have ht'' : Ct * x ^ p ≤ |Ct| * x ^ p :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hP
    have hl'' : Cl * z * Real.log x ^ (-A) ≤ |Cl| * z * Real.log x ^ (-A) := by
      gcongr
      exact le_abs_self _
    have hh'' : Ch * z * Real.log x ^ (-A) ≤ |Ch| * z * Real.log x ^ (-A) := by
      gcongr
      exact le_abs_self _
    have he : (∑ k ∈ Finset.Ioc ⌊x - z⌋₊ ⌊x⌋₊, (a x k : ℂ) * χ (k : ZMod q)) -
        (z : ℂ) * lowCenter a x χ =
        ((∑ k ∈ Finset.Ioc ⌊x - z⌋₊ ⌊x⌋₊, (a x k : ℂ) * χ (k : ZMod q)) -
          windowContour a x z (x ^ (0.45 - 2 * ε / 3)) χ) +
        (windowContour a x z (x ^ (0.45 - 2 * ε / 3)) χ -
          windowContour a x z (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ) +
        (windowContour a x z (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ -
          (z : ℂ) * lowCenter a x χ) := by ring
    rw [he]
    have hn := (norm_add_le
      (((∑ k ∈ Finset.Ioc ⌊x - z⌋₊ ⌊x⌋₊, (a x k : ℂ) * χ (k : ZMod q)) -
        windowContour a x z (x ^ (0.45 - 2 * ε / 3)) χ) +
        (windowContour a x z (x ^ (0.45 - 2 * ε / 3)) χ -
        windowContour a x z (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ))
      (windowContour a x z (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ -
        (z : ℂ) * lowCenter a x χ)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    have htP : 0 ≤ |Ct| * (z * Real.log x ^ (-A)) := by positivity
    have hlP : 0 ≤ |Cl| * x ^ p := by positivity
    have hhP : 0 ≤ |Ch| * x ^ p := by positivity
    dsimp [K]
    change _ ≤ Ct * x ^ p at ht'
    nlinarith
  have hc := center_from_continuous_comparison
    (fun k => (a x k : ℂ) * χ (k : ZMod q)) (lowCenter a x χ)
    hw2 hwx hK hL hP (mul_nonneg hD hP) hcoeff hcomp hy hyw
  change ‖∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊,
    ((a x k : ℂ) * χ (k : ZMod q) - referenceAverage a x χ)‖ ≤ _ at hc
  have hDP : 0 ≤ 9 * D * (y * Real.log x ^ (-A)) := by positivity
  change _ ≤ (2 * K + 9 * D) * (y * Real.log x ^ (-A) + x ^ p)
  nlinarith

end LeanLab.BHP1997.Decomp386b
