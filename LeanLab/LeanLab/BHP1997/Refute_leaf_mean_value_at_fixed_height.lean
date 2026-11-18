/-
P0069, page 24, display 4.1. FABLE PROVE SPRINT S9, unit BHP1997/SPLIT_lower_mean_value_supply.
Refutation of `leaf_mean_value_at_fixed_height`, the first leaf of the split of the
auxiliary supply leaf. No statement on main is changed, no definition is added, and no
sorry is used.

The leaf asserts the mean value 4.1 for the sifted version of every family `c0` with a
divisor bound. Counterexample: the two bounded families `cos(τ log k)` and
`sin(τ log k)`, where `τ = exp((log x)^(1/3))` is the lower height of the integral.
Their Dirichlet polynomials `Dc` and `Ds` satisfy `Dc + i Ds = Σ w_k k^(-1/2) k^(i(τ - t))`,
whose real part near `t = τ` is at least half of the sum of `k^(-1/2)` over the primes
in `(x/2, 2x]`. The Chebyshev bounds for theta in Mathlib make that sum at least
`c x^(1/2) / log x`, so one of the two mean values is at least `c x^(1/2) (log x)^(-2)`,
against the claimed `C x^(1/2) (log x)^(-3)`.

AI wrote the Lean code. Goldbach is open and this does not bear on it.
-/
import LeanLab.BHP1997.SPLIT_leaf_auxiliary_family_supply

namespace LeanLab.BHP1997.Decomp312a
open Classical Complex DecompC165b Decomp312c Decomp132
open scoped BigOperators
open Filter

/-- Standard real analysis. For `L ≥ 8` the cube root of `L` is at most `L / 4`. -/
theorem rpow_third_le {L : ℝ} (hL : 8 ≤ L) : L ^ (1 / 3 : ℝ) ≤ L / 4 := by
  have hL0 : 0 ≤ L := by linarith
  have e : (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ := by norm_num
  rw [e]
  set u : ℝ := L ^ (((3 : ℕ) : ℝ)⁻¹) with hu
  have hu3 : u ^ 3 = L := Real.rpow_inv_natCast_pow hL0 (by norm_num)
  have hu0 : 0 ≤ u := Real.rpow_nonneg hL0 _
  have hu2 : 2 ≤ u := by
    by_contra hlt
    have : u ^ 3 < 2 ^ 3 := pow_lt_pow_left₀ (not_le.mp hlt) hu0 (by norm_num)
    linarith
  have : 0 ≤ u * (u ^ 2 - 4) := mul_nonneg hu0 (by nlinarith)
  nlinarith

/-- Standard real analysis. For `L ≥ 1024` the power `L^(9/10)` is at most `L / 2`. -/
theorem rpow_nine_tenths_le {L : ℝ} (hL : 1024 ≤ L) : L ^ (9 / 10 : ℝ) ≤ L / 2 := by
  have hL0 : 0 ≤ L := by linarith
  have e : (9 / 10 : ℝ) = ((10 : ℕ) : ℝ)⁻¹ * ((9 : ℕ) : ℝ) := by norm_num
  rw [e, Real.rpow_mul hL0, Real.rpow_natCast]
  set v : ℝ := L ^ (((10 : ℕ) : ℝ)⁻¹) with hv
  have hv10 : v ^ 10 = L := Real.rpow_inv_natCast_pow hL0 (by norm_num)
  have hv0 : 0 ≤ v := Real.rpow_nonneg hL0 _
  have hv2 : 2 ≤ v := by
    by_contra hlt
    have : v ^ 10 < 2 ^ 10 := pow_lt_pow_left₀ (not_le.mp hlt) hv0 (by norm_num)
    linarith
  have h9 : 0 ≤ v ^ 9 := pow_nonneg hv0 9
  have : v ^ 10 = v ^ 9 * v := by ring
  nlinarith

/-- Standard complex analysis. The real part of a unit phase `e^(iτ log k)` with real
weight `w`, divided by `k^(1/2 + it)`, is `w k^(-1/2) cos((τ - t) log k)`. -/
theorem cpow_half_phase (w τ t : ℝ) {k : ℕ} (hk : k ≠ 0) :
    ((((w * Real.cos (τ * Real.log k) : ℝ) : ℂ) +
        ((w * Real.sin (τ * Real.log k) : ℝ) : ℂ) * I) / (k : ℂ) ^ Thm4.half t).re =
      w * Real.exp (-(Real.log k / 2)) * Real.cos ((τ - t) * Real.log k) := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hlog : Complex.log (k : ℂ) = ((Real.log k : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg k)]
  rw [Complex.cpow_def_of_ne_zero hk0, hlog, Thm4.half]
  set L : ℝ := Real.log k with hL
  have e1 : ((w * Real.cos (τ * L) : ℝ) : ℂ) + ((w * Real.sin (τ * L) : ℝ) : ℂ) * I =
      (w : ℂ) * Complex.exp (((τ * L : ℝ) : ℂ) * I) := by
    rw [Complex.exp_mul_I]
    push_cast
    ring
  rw [e1, mul_div_assoc, ← Complex.exp_sub, Complex.re_ofReal_mul, Complex.exp_re]
  have hre : (((τ * L : ℝ) : ℂ) * I - (L : ℂ) * (1 / 2 + (t : ℂ) * I)).re = -(L / 2) := by
    simp
    ring
  have him : (((τ * L : ℝ) : ℂ) * I - (L : ℂ) * (1 / 2 + (t : ℂ) * I)).im = (τ - t) * L := by
    simp
    ring
  rw [hre, him]
  ring

/-- Standard analysis. The integrand of display 4.1 is continuous in the height when
no index vanishes. -/
theorem continuous_dirichlet_norm (s : Finset ℕ) (hs : ∀ k ∈ s, k ≠ 0) (a : ℕ → ℂ)
    (σ : ℝ) :
    Continuous fun t : ℝ => ‖∑ k ∈ s, a k / (k : ℂ) ^ Thm4.half (σ * t)‖ := by
  refine continuous_norm.comp (continuous_finset_sum _ fun k hk => ?_)
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hs k hk)
  have hc : Continuous fun t : ℝ => Thm4.half (σ * t) := by
    unfold Thm4.half
    fun_prop
  refine Continuous.div continuous_const (hc.const_cpow (Or.inl hk0)) (fun t => ?_)
  rw [Ne, Complex.cpow_eq_zero_iff]
  tauto

/-- Standard analysis. A continuous nonnegative function that is at least `V` on an
initial piece of length `δ` has integral at least `δ V`. -/
theorem integral_ge_initial_piece {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    {a b δ V : ℝ} (hδ : 0 ≤ δ) (hab : a + δ ≤ b)
    (hV : ∀ t ∈ Set.Icc a (a + δ), V ≤ f t) :
    δ * V ≤ ∫ t in a..b, f t := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := MeasureTheory.volume) a (a + δ))
    (hf.intervalIntegrable (μ := MeasureTheory.volume) (a + δ) b)
  have h2 : 0 ≤ ∫ t in (a + δ)..b, f t :=
    intervalIntegral.integral_nonneg hab (fun t _ => hf0 t)
  have h1 : (∫ _t in a..(a + δ), V) ≤ ∫ t in a..(a + δ), f t :=
    intervalIntegral.integral_mono_on (by linarith) (continuous_const.intervalIntegrable _ _)
      (hf.intervalIntegrable a (a + δ)) hV
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  have : a + δ - a = δ := by ring
  rw [this] at h1
  linarith

/-- Chebyshev, from `Chebyshev.theta_ge` and `Chebyshev.theta_le_log4_mul_x` in
Mathlib. For `j ≥ 100` the primes in `(j^4, 4 j^4]` have total logarithm at least `j^4`. -/
theorem prime_log_sum_window {j : ℕ} (hj : 100 ≤ j) :
    ((j : ℝ) ^ 4) ≤ ∑ k ∈ Finset.Ioc (j ^ 4) (4 * j ^ 4),
      (if k.Prime then Real.log k else 0) := by
  have hjr : (100 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
  have hsum : Chebyshev.theta ((4 * j ^ 4 : ℕ) : ℝ) =
      Chebyshev.theta ((j ^ 4 : ℕ) : ℝ) +
        ∑ k ∈ Finset.Ioc (j ^ 4) (4 * j ^ 4), (if k.Prime then Real.log k else 0) := by
    unfold Chebyshev.theta
    rw [Nat.floor_natCast, Nat.floor_natCast, Finset.sum_filter, Finset.sum_filter]
    exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (by omega)).symm
  have hup := Chebyshev.theta_le_log4_mul_x (x := ((j ^ 4 : ℕ) : ℝ)) (Nat.cast_nonneg _)
  have hlo := Chebyshev.theta_ge (4 * j ^ 4)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow]
    norm_num
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  -- the square root
  have hsq : Real.sqrt ((4 * j ^ 4 : ℕ) : ℝ) = 2 * (j : ℝ) ^ 2 := by
    have : ((4 * j ^ 4 : ℕ) : ℝ) = (2 * (j : ℝ) ^ 2) ^ 2 := by
      push_cast
      ring
    rw [this, Real.sqrt_sq (by positivity)]
  -- the logarithms are at most 8 j
  have hlogA : Real.log (((4 * j ^ 4 : ℕ) : ℝ) + 1) ≤ 8 * (j : ℝ) := by
    have h1 : ((4 * j ^ 4 : ℕ) : ℝ) + 1 ≤ (2 * (j : ℝ)) ^ 4 := by
      push_cast
      have : (1 : ℝ) ≤ (j : ℝ) ^ 4 := one_le_pow₀ (by linarith)
      nlinarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    have h3 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * (j : ℝ))
    push_cast at h2 ⊢
    linarith
  have hlogB : Real.log ((4 * j ^ 4 : ℕ) : ℝ) ≤ 8 * (j : ℝ) := by
    have hpos : (0 : ℝ) < ((4 * j ^ 4 : ℕ) : ℝ) := by
      push_cast
      positivity
    exact (Real.log_le_log hpos (by linarith)).trans hlogA
  rw [hsq] at hlo
  have hprod : 2 * (2 * (j : ℝ) ^ 2) * Real.log ((4 * j ^ 4 : ℕ) : ℝ) ≤
      2 * (2 * (j : ℝ) ^ 2) * (8 * (j : ℝ)) :=
    mul_le_mul_of_nonneg_left hlogB (by positivity)
  have hj3 : (100 : ℝ) * (j : ℝ) ^ 3 ≤ (j : ℝ) ^ 4 := by
    have : (j : ℝ) ^ 4 = (j : ℝ) * (j : ℝ) ^ 3 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hjr (by positivity)
  have hj1 : (j : ℝ) ≤ (j : ℝ) ^ 3 := by
    have : (1 : ℝ) ≤ (j : ℝ) ^ 2 := one_le_pow₀ (by linarith)
    nlinarith
  have hj4 : (0 : ℝ) ≤ (j : ℝ) ^ 4 := by positivity
  push_cast at hlo hup hsum hprod hlogA
  nlinarith

/-- The pointwise lower bound behind the refutation. For coefficient functions equal
to `w cos(τ log k)` and `w sin(τ log k)` on the window, with `w ≥ 0` equal to 1 at
primes, and a height `t` with `|τ - t| log N ≤ 1`, the two Dirichlet polynomial norms
of display 4.1 at the principal character modulo 1 add up to at least the weighted
prime sum. -/
theorem two_family_pointwise (m N : ℕ) (w a b : ℕ → ℝ) (τ t : ℝ)
    (hw0 : ∀ k, 0 ≤ w k) (hwp : ∀ k ∈ Finset.Ioc m N, k.Prime → w k = 1)
    (ha : ∀ k ∈ Finset.Ioc m N, a k = w k * Real.cos (τ * Real.log k))
    (hb : ∀ k ∈ Finset.Ioc m N, b k = w k * Real.sin (τ * Real.log k))
    (ht : |τ - t| * Real.log N ≤ 1) :
    1 / 2 * Real.exp (-(Real.log N / 2)) / Real.log N *
        ∑ k ∈ Finset.Ioc m N, (if k.Prime then Real.log k else 0) ≤
      ‖∑ k ∈ Finset.Ioc m N, ((a k : ℝ) : ℂ) * (1 : DirichletCharacter ℂ 1) (k : ZMod 1) /
          (k : ℂ) ^ Thm4.half (1 * t)‖ +
      ‖∑ k ∈ Finset.Ioc m N, ((b k : ℝ) : ℂ) * (1 : DirichletCharacter ℂ 1) (k : ZMod 1) /
          (k : ℂ) ^ Thm4.half (1 * t)‖ := by
  set Dc : ℂ := ∑ k ∈ Finset.Ioc m N, ((a k : ℝ) : ℂ) *
    (1 : DirichletCharacter ℂ 1) (k : ZMod 1) / (k : ℂ) ^ Thm4.half (1 * t) with hDc
  set Ds : ℂ := ∑ k ∈ Finset.Ioc m N, ((b k : ℝ) : ℂ) *
    (1 : DirichletCharacter ℂ 1) (k : ZMod 1) / (k : ℂ) ^ Thm4.half (1 * t) with hDs
  have h1 : (Dc + I * Ds).re ≤ ‖Dc‖ + ‖Ds‖ := by
    refine (Complex.re_le_norm _).trans ((norm_add_le _ _).trans ?_)
    rw [norm_mul, Complex.norm_I, one_mul]
  have hχ : ∀ k : ℕ, (1 : DirichletCharacter ℂ 1) (k : ZMod 1) = 1 := fun k =>
    MulChar.one_apply (isUnit_of_subsingleton _)
  have h2 : Dc + I * Ds = ∑ k ∈ Finset.Ioc m N,
      (((w k * Real.cos (τ * Real.log k) : ℝ) : ℂ) +
        ((w k * Real.sin (τ * Real.log k) : ℝ) : ℂ) * I) / (k : ℂ) ^ Thm4.half t := by
    rw [hDc, hDs, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [ha k hk, hb k hk, hχ k, one_mul t]
    ring
  rw [h2, Complex.re_sum] at h1
  refine le_trans ?_ h1
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  have hkm := Finset.mem_Ioc.mp hk
  have hk0 : k ≠ 0 := by omega
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
  have hkN : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkm.2
  have hlk0 : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hlkN : Real.log k ≤ Real.log N := Real.log_le_log (by linarith) hkN
  rw [cpow_half_phase _ _ _ hk0]
  have habs : |(τ - t) * Real.log k| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hlk0]
    exact (mul_le_mul_of_nonneg_left hlkN (abs_nonneg _)).trans ht
  have hcos : 1 / 2 ≤ Real.cos ((τ - t) * Real.log k) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := (τ - t) * Real.log k)
    have hsq : ((τ - t) * Real.log k) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr habs
    linarith
  have hexp : Real.exp (-(Real.log N / 2)) ≤ Real.exp (-(Real.log k / 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hE0 : 0 < Real.exp (-(Real.log N / 2)) := Real.exp_pos _
  split_ifs with hp
  · rw [hwp k hk hp, one_mul]
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hp.two_le
    have hlN : 0 < Real.log N := Real.log_pos (by linarith)
    have hfrac : Real.log k / Real.log N ≤ 1 := (div_le_one hlN).mpr hlkN
    have hfrac0 : 0 ≤ Real.log k / Real.log N := div_nonneg hlk0 hlN.le
    have e : 1 / 2 * Real.exp (-(Real.log N / 2)) / Real.log N * Real.log k =
        1 / 2 * Real.exp (-(Real.log N / 2)) * (Real.log k / Real.log N) := by ring
    rw [e]
    calc 1 / 2 * Real.exp (-(Real.log N / 2)) * (Real.log k / Real.log N)
        ≤ 1 / 2 * Real.exp (-(Real.log N / 2)) * 1 :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = Real.exp (-(Real.log N / 2)) * (1 / 2) := by ring
      _ ≤ Real.exp (-(Real.log k / 2)) * Real.cos ((τ - t) * Real.log k) :=
          mul_le_mul hexp hcos (by norm_num) (Real.exp_pos _).le
  · rw [mul_zero]
    exact mul_nonneg (mul_nonneg (hw0 k) (Real.exp_pos _).le) (by linarith)

/-- The sifted weight takes values in the unit interval. -/
theorem siftedWeight_unit (n z : ℕ) : 0 ≤ siftedWeight n z ∧ siftedWeight n z ≤ 1 := by
  unfold siftedWeight
  split_ifs <;> norm_num

/-- A family bounded by 1 that vanishes at index 0 has a sifted version with the
divisor bound at exponent 1 and constant 1. This is the hypothesis of the leaf. -/
theorem sifted_divisor_bound_of_bounded (c : ℝ → ℕ → ℝ) (hc : ∀ x k, |c x k| ≤ 1)
    (hc0 : ∀ x, c x 0 = 0) :
    ∃ C : ℝ, ∀ x k, |section4SiftedFamily c x k| ≤
      C * ((k.divisors.card : ℕ) : ℝ) ^ (1 : ℝ) := by
  refine ⟨1, fun x k => ?_⟩
  rw [Real.rpow_one, one_mul]
  by_cases hk : k = 0
  · subst hk
    simp [section4SiftedFamily, hc0]
  · have hcard : (1 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Finset.card_ne_zero.mpr (Nat.nonempty_divisors.mpr hk))
    obtain ⟨hs0, hs1⟩ := siftedWeight_unit k ⌈Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊
    unfold section4SiftedFamily
    rw [abs_mul, abs_of_nonneg hs0]
    calc |c x k| * siftedWeight k ⌈Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊ ≤ 1 * 1 :=
          mul_le_mul (hc x k) hs1 hs0 zero_le_one
      _ ≤ _ := by linarith

/-- FALSE as stated: `leaf_mean_value_at_fixed_height`, the first leaf of the split of
the auxiliary supply leaf. Page 24, display 4.1. The leaf asserts the mean value 4.1
for the sifted version of every family with a divisor bound. Read it at the two
bounded families `cos(τ log k)` and `sin(τ log k)` with `τ = exp((log x)^(1/3))`, at
height sign 1, saving `A = 3`, modulus 1 and `x = 2 j^4` for a large integer `j`. By
`two_family_pointwise` and `prime_log_sum_window` the two integrands add up to at
least `c x^(1/2) / log x` on a height interval of length `1 / log(2x)` at the lower
limit, so the two integrals cannot both be at most `C x^(1/2) (log x)^(-3)`. -/
theorem leaf_mean_value_at_fixed_height_false :
    ¬ (type_of% @leaf_mean_value_at_fixed_height) := by
  intro H
  let τ : ℝ → ℝ := fun x => Real.exp (Real.log x ^ (1 / 3 : ℝ))
  let cc : ℝ → ℕ → ℝ := fun x k => if k = 0 then 0 else Real.cos (τ x * Real.log k)
  let cs : ℝ → ℕ → ℝ := fun x k => if k = 0 then 0 else Real.sin (τ x * Real.log k)
  have hcc := sifted_divisor_bound_of_bounded cc (fun x k => by
    show |if k = 0 then (0 : ℝ) else Real.cos (τ x * Real.log k)| ≤ 1
    split_ifs
    · simp
    · exact Real.abs_cos_le_one _) (fun x => by simp [cc])
  have hcs := sifted_divisor_bound_of_bounded cs (fun x k => by
    show |if k = 0 then (0 : ℝ) else Real.sin (τ x * Real.log k)| ≤ 1
    split_ifs
    · simp
    · exact Real.abs_sin_le_one _) (fun x => by simp [cs])
  obtain ⟨C1, X1, h1⟩ := H 1 le_rfl (1 / 10) (by norm_num) le_rfl cc hcc 1 (by simp) 3
    (by norm_num)
  obtain ⟨C2, X2, h2⟩ := H 1 le_rfl (1 / 10) (by norm_num) le_rfl cs hcs 1 (by simp) 3
    (by norm_num)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = |C1| + |C2| := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = ⌈max (max (max X1 X2) 100) (Real.exp (1024 + 64 * K))⌉₊ :=
    ⟨_, rfl⟩
  have hjge : max (max (max X1 X2) 100) (Real.exp (1024 + 64 * K)) ≤ (j : ℝ) := by
    rw [hj]
    exact Nat.le_ceil _
  have hjr : (100 : ℝ) ≤ (j : ℝ) := ((le_max_right _ _).trans (le_max_left _ _)).trans hjge
  have hj100 : 100 ≤ j := by exact_mod_cast hjr
  have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 2 * (j : ℝ) ^ 4 := ⟨_, rfl⟩
  have hjx : (j : ℝ) ≤ x := by
    have h3 : (1 : ℝ) ≤ (j : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    have : (j : ℝ) ^ 4 = (j : ℝ) * (j : ℝ) ^ 3 := by ring
    rw [hx, this]
    nlinarith
  have hx0 : 0 < x := by linarith
  have hX1 : X1 ≤ x :=
    ((((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hjge).trans hjx
  have hX2 : X2 ≤ x :=
    ((((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hjge).trans hjx
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log x := ⟨_, rfl⟩
  have hL : 1024 + 64 * K ≤ L := by
    have h1' : 1024 + 64 * K ≤ Real.log (j : ℝ) :=
      (Real.le_log_iff_exp_le hj0).mpr ((le_max_right _ _).trans hjge)
    rw [hLdef]
    exact h1'.trans (Real.log_le_log hj0 hjx)
  have hL1 : 1024 ≤ L := by linarith
  have hxexp : Real.exp L = x := by rw [hLdef, Real.exp_log hx0]
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (L / 2) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; exact Real.exp_pos _
  have hEE : E * E = x := by
    rw [hE, ← Real.exp_add, ← hxexp]
    congr 1
    ring
  have hE2 : 2 ≤ E := by
    rw [hE]
    have := Real.add_one_le_exp (L / 2)
    linarith
  -- the window
  have hfl1 : ⌊x / 2⌋₊ = j ^ 4 := by
    have : x / 2 = ((j ^ 4 : ℕ) : ℝ) := by
      rw [hx]
      push_cast
      ring
    rw [this, Nat.floor_natCast]
  have hfl2 : ⌊2 * x⌋₊ = 4 * j ^ 4 := by
    have : 2 * x = ((4 * j ^ 4 : ℕ) : ℝ) := by
      rw [hx]
      push_cast
      ring
    rw [this, Nat.floor_natCast]
  have hq : ((1 : ℕ) : ℝ) ≤ Real.log x ^ (3 : ℝ) := by
    have := Real.one_le_rpow (by linarith : (1 : ℝ) ≤ L) (by norm_num : (0 : ℝ) ≤ 3)
    rw [← hLdef]
    simpa using this
  have a1 := h1 x hX1 1 le_rfl hq 1
  have a2 := h2 x hX2 1 le_rfl hq 1
  rw [hfl1, hfl2, ← hLdef] at a1 a2
  -- the logarithm of the upper end
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = Real.log ((4 * j ^ 4 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hΛL : Λ = Real.log 2 + L := by
    have : ((4 * j ^ 4 : ℕ) : ℝ) = 2 * x := by
      rw [hx]
      push_cast
      ring
    rw [hΛ, this, Real.log_mul (by norm_num) hx0.ne', hLdef]
  have hΛ0 : 0 < Λ := by linarith
  have hΛ1 : 1 ≤ Λ := by linarith
  have hΛ2 : Λ ≤ 2 * L := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / Λ := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one hΛ0]
    exact hΛ1
  have hδΛ : δ * Λ = 1 := by
    rw [hδ]
    field_simp
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = 1 / 2 * Real.exp (-(Λ / 2)) / Λ * (j : ℝ) ^ 4 := ⟨_, rfl⟩
  -- the sifted weight keeps the primes of the window
  have hwp : ∀ k ∈ Finset.Ioc (j ^ 4) (4 * j ^ 4), k.Prime →
      siftedWeight k ⌈Real.exp (L ^ (9 / 10 : ℝ))⌉₊ = 1 := by
    intro k hk hp
    unfold siftedWeight
    rw [if_pos]
    right
    rw [hp.minFac_eq, Nat.ceil_le]
    have hkm : ((j ^ 4 : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Finset.mem_Ioc.mp hk).1.le
    have h9 := rpow_nine_tenths_le hL1
    have hexp : Real.exp (L ^ (9 / 10 : ℝ)) ≤ E := by
      rw [hE]
      exact Real.exp_le_exp.mpr h9
    have hEx : E ≤ x / 2 := by
      have := mul_le_mul_of_nonneg_left hE2 hE0.le
      linarith
    have : x / 2 = ((j ^ 4 : ℕ) : ℝ) := by
      rw [hx]
      push_cast
      ring
    linarith
  have hk0 : ∀ k ∈ Finset.Ioc (j ^ 4) (4 * j ^ 4), k ≠ 0 := by
    intro k hk
    have := (Finset.mem_Ioc.mp hk).1
    omega
  -- pointwise lower bound on the initial piece
  have hpt : ∀ t ∈ Set.Icc (τ x) (τ x + δ), V ≤
      ‖∑ k ∈ Finset.Ioc (j ^ 4) (4 * j ^ 4), ((section4SiftedFamily cc x k : ℝ) : ℂ) *
          (1 : DirichletCharacter ℂ 1) (k : ZMod 1) / (k : ℂ) ^ Thm4.half (1 * t)‖ +
      ‖∑ k ∈ Finset.Ioc (j ^ 4) (4 * j ^ 4), ((section4SiftedFamily cs x k : ℝ) : ℂ) *
          (1 : DirichletCharacter ℂ 1) (k : ZMod 1) / (k : ℂ) ^ Thm4.half (1 * t)‖ := by
    intro t ht
    have habs : |τ x - t| * Real.log ((4 * j ^ 4 : ℕ) : ℝ) ≤ 1 := by
      rw [← hΛ, ← hδΛ]
      refine mul_le_mul_of_nonneg_right ?_ hΛ0.le
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hmain := two_family_pointwise (j ^ 4) (4 * j ^ 4)
      (fun k => siftedWeight k ⌈Real.exp (L ^ (9 / 10 : ℝ))⌉₊)
      (fun k => section4SiftedFamily cc x k) (fun k => section4SiftedFamily cs x k)
      (τ x) t (fun k => (siftedWeight_unit k _).1) hwp
      (fun k hk => by
        show (if k = 0 then (0 : ℝ) else Real.cos (τ x * Real.log k)) *
          siftedWeight k ⌈Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊ = _
        rw [if_neg (hk0 k hk), ← hLdef, mul_comm])
      (fun k hk => by
        show (if k = 0 then (0 : ℝ) else Real.sin (τ x * Real.log k)) *
          siftedWeight k ⌈Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊ = _
        rw [if_neg (hk0 k hk), ← hLdef, mul_comm])
      habs
    refine le_trans ?_ hmain
    rw [hV, ← hΛ]
    exact mul_le_mul_of_nonneg_left (prime_log_sum_window hj100) (by positivity)
  -- continuity of the two integrands
  have hcc' := continuous_dirichlet_norm (Finset.Ioc (j ^ 4) (4 * j ^ 4)) hk0
    (fun k => ((section4SiftedFamily cc x k : ℝ) : ℂ) *
      (1 : DirichletCharacter ℂ 1) (k : ZMod 1)) 1
  have hcs' := continuous_dirichlet_norm (Finset.Ioc (j ^ 4) (4 * j ^ 4)) hk0
    (fun k => ((section4SiftedFamily cs x k : ℝ) : ℂ) *
      (1 : DirichletCharacter ℂ 1) (k : ZMod 1)) 1
  -- the initial piece fits below the upper height
  have hab : τ x + δ ≤ x ^ (0.45 - 2 * (1 / 10) / 3 : ℝ) := by
    have h3 := rpow_third_le (by linarith : (8 : ℝ) ≤ L)
    have hτ : τ x ≤ Real.exp (L / 4) := by
      show Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ _
      rw [← hLdef]
      exact Real.exp_le_exp.mpr h3
    have hT : Real.exp (L / 4) * Real.exp (L / 8) ≤ x ^ (0.45 - 2 * (1 / 10) / 3 : ℝ) := by
      rw [show (0.45 - 2 * (1 / 10) / 3 : ℝ) = 23 / 60 by norm_num,
        Real.rpow_def_of_pos hx0, ← hLdef, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      linarith
    have h8 : 2 ≤ Real.exp (L / 8) := by
      have := Real.add_one_le_exp (L / 8)
      linarith
    have h4 : 1 ≤ Real.exp (L / 4) := Real.one_le_exp (by linarith)
    have h5 := mul_le_mul_of_nonneg_left h8 (by linarith : (0 : ℝ) ≤ Real.exp (L / 4))
    linarith
  have hI := integral_ge_initial_piece (hcc'.add hcs')
    (fun t => add_nonneg (norm_nonneg _) (norm_nonneg _)) hδ0 hab hpt
  simp only [Pi.add_apply] at hI
  have hτx : τ x = Real.exp (L ^ (1 / 3 : ℝ)) := by
    show Real.exp (Real.log x ^ (1 / 3 : ℝ)) = _
    rw [hLdef]
  rw [intervalIntegral.integral_add (hcc'.intervalIntegrable _ _)
    (hcs'.intervalIntegrable _ _), hτx] at hI
  -- compare with the two claimed bounds
  have hx12 : x ^ (1 / 2 : ℝ) = E := by
    rw [Real.rpow_def_of_pos hx0, ← hLdef, hE]
    congr 1
    ring
  have hL0 : 0 < L := by linarith
  have hLpow : L ^ (-(3 : ℝ)) = (L ^ 3)⁻¹ := by
    rw [Real.rpow_neg hL0.le]
    norm_num
  rw [hx12, hLpow] at a1 a2
  have hinv0 : 0 ≤ E * (L ^ 3)⁻¹ := by positivity
  have hup : δ * V ≤ K * (E * (L ^ 3)⁻¹) := by
    have b1 : C1 * E * (L ^ 3)⁻¹ ≤ |C1| * (E * (L ^ 3)⁻¹) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self C1) hinv0
    have b2 : C2 * E * (L ^ 3)⁻¹ ≤ |C2| * (E * (L ^ 3)⁻¹) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self C2) hinv0
    rw [hK]
    linarith
  -- the lower bound in closed form
  have hj4 : (j : ℝ) ^ 4 = E * E / 2 := by
    rw [hEE, hx]
    ring
  have hexpΛ : E⁻¹ / 2 ≤ Real.exp (-(Λ / 2)) := by
    have e : -(Λ / 2) = -(L / 2) + -(Real.log 2 / 2) := by
      rw [hΛL]
      ring
    rw [e, Real.exp_add, Real.exp_neg (L / 2), ← hE]
    have h2 : (1 / 2 : ℝ) ≤ Real.exp (-(Real.log 2 / 2)) := by
      have h3 : Real.exp (-Real.log 2) ≤ Real.exp (-(Real.log 2 / 2)) :=
        Real.exp_le_exp.mpr (by linarith)
      rw [Real.exp_neg, Real.exp_log (by norm_num)] at h3
      linarith
    have hEi : 0 ≤ E⁻¹ := by positivity
    calc E⁻¹ / 2 = E⁻¹ * (1 / 2) := by ring
      _ ≤ E⁻¹ * Real.exp (-(Real.log 2 / 2)) := mul_le_mul_of_nonneg_left h2 hEi
  have e1 : δ * V = Real.exp (-(Λ / 2)) * ((j : ℝ) ^ 4 / (2 * Λ ^ 2)) := by
    rw [hδ, hV]
    field_simp
  have e2 : E⁻¹ / 2 * ((j : ℝ) ^ 4 / (2 * Λ ^ 2)) = E / (8 * Λ ^ 2) := by
    rw [hj4]
    field_simp
    ring
  have h8L : 8 * Λ ^ 2 ≤ 32 * L ^ 2 := by
    have h := pow_le_pow_left₀ hΛ0.le hΛ2 2
    have h' : (2 * L) ^ 2 = 4 * L ^ 2 := by ring
    linarith
  have hlow : E / (32 * L ^ 2) ≤ δ * V := by
    rw [e1]
    calc E / (32 * L ^ 2) ≤ E / (8 * Λ ^ 2) :=
          div_le_div_of_nonneg_left hE0.le (by positivity) h8L
      _ = E⁻¹ / 2 * ((j : ℝ) ^ 4 / (2 * Λ ^ 2)) := e2.symm
      _ ≤ Real.exp (-(Λ / 2)) * ((j : ℝ) ^ 4 / (2 * Λ ^ 2)) :=
          mul_le_mul_of_nonneg_right hexpΛ (by positivity)
  have hfin := hlow.trans hup
  rw [div_le_iff₀ (by positivity)] at hfin
  have e3 : K * (E * (L ^ 3)⁻¹) * (32 * L ^ 2) = 32 * K * E / L := by
    field_simp
  rw [e3, le_div_iff₀ hL0] at hfin
  have hpos := mul_pos hE0 (by linarith : 0 < L - 32 * K)
  have hexpand : E * (L - 32 * K) = E * L - 32 * K * E := by ring
  rw [hexpand] at hpos
  linarith

end LeanLab.BHP1997.Decomp312a
