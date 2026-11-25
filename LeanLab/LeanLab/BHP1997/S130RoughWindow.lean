/-
Burst 2026-11-22, session S130: `DQ517Window.leaf_rough_window_density` split once more along
the paper. Source: P0069 Baker Harman Pintz 1997, page 51, display 5.17: "a straightforward
consequence of the prime number theorem, with error term `Y exp(-ε L^(1/2))`".

The proved log power form `LowerShortC165.rough_interval_density` of `RoughDensity517e` is an
induction on the number of prime factors of the rough number, through the finite Buchstab
identity, with three inputs. This file redoes that induction and its inputs with the error
`exp(-N (log X)^(1/3))` of display 5.17 in place of a log power:

* `leaf_strong_prime_prefix_level`: the prime count on intervals below `Y` with the error
  `Y exp(-N (log X)^(1/3))`, by partial summation at modulus `1`, `PNTPort.BVMax.abel_bound`,
  from the strong prime number theorem `LeanLab.PNTPort.psi_explicit_strong`;
* `strong_prime_weight_transfer`, `strong_buchstab_telescope`, `strong_lattice_abel`: the three
  inputs, by the proofs of their log power forms;
* `strong_buchstab_main_term`, `strong_rough_density_strip` and
  `leaf_rough_window_density_of_s130`, the last with exactly the statement of
  `DQ517Window.leaf_rough_window_density`.

Nothing is left open in this file. No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.RoughDensity517e
import LeanLab.PNTPort.BVMax.Primes
import LeanLab.PNTPort.StrongPNT.Bridge

namespace LeanLab.BHP1997.S130RoughWindow
open Classical
open scoped BigOperators
open LeanLab.BHP1997.LowerShortC165
open LeanLab.BHP1997.Task308 (roughIndicator)
open LeanLab.ChenDoubleSieve.Wu04Functional
open LeanLab.BHP1997.Decomp132
open LeanLab.PNTPort.BVMax (EE CC cc EE_small abel_bound CC_eq thetaN)

/-! ### Proved helpers -/

/-- Page 51 display 5.17: `log X ≤ 6 exp((log X)^(1/3))`, from `l ^ 3 / 3! ≤ exp l`; one factor
`log X` lost to the harmonic sum over the least prime factor is absorbed by one unit of `N`. -/
theorem log_le_six_exp_cuberoot {X : ℝ} (hX : 1 ≤ X) :
    Real.log X ≤ 6 * Real.exp (Real.log X ^ (1 / 3 : ℝ)) := by
  have hlx : 0 ≤ Real.log X := Real.log_nonneg hX
  set l := Real.log X ^ (1 / 3 : ℝ) with hl
  have hl0 : 0 ≤ l := Real.rpow_nonneg hlx _
  have hl3 : l ^ 3 = Real.log X := by
    rw [hl, ← Real.rpow_natCast, ← Real.rpow_mul hlx]
    norm_num
  have h2 := Real.pow_div_factorial_le_exp l hl0 3
  have hfac : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hfac] at h2
  rw [← hl3]
  linarith

/-- Page 51 display 5.17: a negative power of `X` is below `K exp(-N (log X)^(1/3))`, the
form in which errors of size `b / z` with `z ≥ X ^ c` are absorbed: with `l ^ 3 = log X` and
`s ^ 2 = N / c`, `N l ≤ N s + c l ^ 3`. -/
theorem s130_rpow_neg_le_exp {c N : ℝ} (hc : 0 < c) (hN : 0 < N) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 3 ≤ X →
      X ^ (-c) ≤ K * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  set s := Real.sqrt (N / c) with hs
  refine ⟨Real.exp (N * s), Real.exp_pos _, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hlx : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  set l := Real.log X ^ (1 / 3 : ℝ) with hl
  have hl0 : 0 ≤ l := Real.rpow_nonneg hlx _
  have hl3 : l ^ 3 = Real.log X := by
    rw [hl, ← Real.rpow_natCast, ← Real.rpow_mul hlx]
    norm_num
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : c * s ^ 2 = N := by
    rw [hs, Real.sq_sqrt (by positivity)]
    field_simp
  rw [Real.rpow_def_of_pos hX0, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [← hl3]
  rcases le_or_gt l s with h | h
  · nlinarith [mul_nonneg hN.le (sub_nonneg.2 h), mul_nonneg hc.le (pow_nonneg hl0 3)]
  · have e : c * l ^ 3 - N * l = c * l * (l - s) * (l + s) := by rw [← hs2]; ring
    have h1 : 0 ≤ c * l * (l - s) * (l + s) :=
      mul_nonneg (mul_nonneg (mul_nonneg hc.le hl0) (sub_nonneg.2 h.le)) (add_nonneg hl0 hs0)
    nlinarith [mul_nonneg hN.le hs0]

/-- Page 51 display 5.17: one factor `log X` is absorbed by one unit of `N`. -/
theorem s130_exp_succ_mul_log_le {X : ℝ} (hX : 1 ≤ X) (N : ℝ) :
    Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) * Real.log X ≤
      6 * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  have h6 := log_le_six_exp_cuberoot hX
  have e : Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) *
      Real.exp (Real.log X ^ (1 / 3 : ℝ)) = Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE0 := (Real.exp_pos (-(N + 1) * Real.log X ^ (1 / 3 : ℝ))).le
  calc _ ≤ Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) *
        (6 * Real.exp (Real.log X ^ (1 / 3 : ℝ))) := mul_le_mul_of_nonneg_left h6 hE0
    _ = _ := by rw [← e]; ring

/-! ### The prime number theorem step and the three inputs of the Buchstab recursion -/

/-! ### The strong prime number theorem in the form of the recursion -/

/-- `Icc 1 N = Ioc 0 N` on the naturals. -/
theorem s130_icc_eq_ioc (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

/-- Page 51 display 5.17: the prime weight prefix sum is `EE 1 0` of `PNTPort.BVMax`, the
prime count minus `liN`. -/
theorem s130_prefix_eq_EE (N : ℕ) :
    ∑ k ∈ Finset.Ioc 0 N, (primeWeight k - 1 / Real.log (k : ℝ)) = EE 1 0 N := by
  unfold EE
  rw [s130_icc_eq_ioc]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 := (Finset.mem_Ioc.mp hn).1
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 1 := by omega
    subst this
    simp [cc, primeWeight, Nat.not_prime_one]
  · have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast h)
    unfold cc primeWeight
    simp only [h, ↓reduceIte, Nat.mod_one, true_and, Nat.totient_one, Nat.cast_one]
    split_ifs <;> field_simp
    simp

/-- `CC 1 0 n = θ(n) - (n - 1)`. -/
theorem s130_CC_eq_theta (n : ℕ) (hn : 1 ≤ n) :
    CC 1 0 n = Chebyshev.theta n - ((n : ℝ) - 1) := by
  rw [CC_eq 1 0 n hn]
  have : thetaN n 1 0 = Chebyshev.theta n := by
    unfold thetaN Chebyshev.theta
    rw [Nat.floor_natCast, s130_icc_eq_ioc]
    simp only [Nat.mod_one, true_and]
  rw [this]
  simp

/-- Partial summation, `PNTPort.BVMax.abel_bound` at `q = 1`: `|EE 1 0 N| ≤ 2 M`. -/
theorem s130_EE_bound (N : ℕ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ n ∈ Finset.Icc 2 N, |CC 1 0 n| ≤ M) :
    |EE 1 0 N| ≤ 2 * M := by
  have hlog2 : 1 / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  rcases Nat.lt_or_ge N 2 with h | h
  · rw [EE_small 1 0 N h, abs_zero]; positivity
  · refine (abel_bound 1 0 N h M hM).trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith

/-- `|θ(n) - n + 1| ≤ |K| n exp(-c √log n) + 2 √n log n + 1` for `n ≥ 2`. -/
theorem s130_CC_le {c K : ℝ}
    (hK : ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ K * x * Real.exp (-c * Real.sqrt (Real.log x)))
    (n : ℕ) (hn : 2 ≤ n) :
    |CC 1 0 n| ≤ |K| * n * Real.exp (-c * Real.sqrt (Real.log n)) +
      2 * Real.sqrt n * Real.log n + 1 := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [s130_CC_eq_theta n (by omega)]
  have h1 := hK n hn2
  have h2 := Chebyshev.psi_sub_theta_le (x := (n : ℝ)) (by linarith)
  have h3 := Chebyshev.theta_le_psi (n : ℝ)
  have h4 : K * n * Real.exp (-c * Real.sqrt (Real.log n)) ≤
      |K| * n * Real.exp (-c * Real.sqrt (Real.log n)) := by
    have := le_abs_self K
    have : 0 ≤ (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log n)) := by positivity
    nlinarith
  rw [abs_le] at h1 ⊢
  constructor <;> nlinarith


/-- `√Y ≤ Y X ^ (-c/2)` once `Y ≥ X ^ c`. -/
theorem s130_sqrt_le_mul_rpow {c X Y : ℝ} (hX0 : 0 < X) (hY : X ^ c ≤ Y) :
    Real.sqrt Y ≤ Y * X ^ (-(c / 2)) := by
  have hXs : X ^ (c / 2) ≤ Real.sqrt Y := by
    rw [show c / 2 = c * (1 / 2) by ring, Real.rpow_mul hX0.le, ← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hY
  have hp : 0 < X ^ (c / 2) := Real.rpow_pos_of_pos hX0 _
  have hY0 : 0 ≤ Y := (Real.rpow_pos_of_pos hX0 c).le.trans hY
  have hs0 : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
  rw [Real.rpow_neg hX0.le, ← div_eq_mul_inv, le_div_iff₀ hp]
  have := mul_le_mul_of_nonneg_left hXs hs0
  rwa [Real.mul_self_sqrt hY0] at this

/-- Page 51 display 5.17: the prime number theorem error `n exp(-c' √log n)` at `n ≤ Y` is at
most `√Y`, or `Y exp(-c' √(c/2) √log X)` once `n > √Y ≥ X ^ (c/2)`. -/
theorem s130_big_term_le {c c' X Y : ℝ} (hc : 0 < c) (hc' : 0 < c') (hX1 : 1 ≤ X)
    (hY : X ^ c ≤ Y) (n : ℕ) (hn : 2 ≤ n) (hnY : (n : ℝ) ≤ Y) :
    (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log n)) ≤
      Real.sqrt Y + Y * Real.exp (-(c' * Real.sqrt (c / 2)) * Real.sqrt (Real.log X)) := by
  have hX0 : 0 < X := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hY0 : 0 ≤ Y := (Real.rpow_pos_of_pos hX0 c).le.trans hY
  have hs0 : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
  have hE2 := (Real.exp_pos (-(c' * Real.sqrt (c / 2)) * Real.sqrt (Real.log X))).le
  by_cases h : (n : ℝ) ≤ Real.sqrt Y
  · have he : Real.exp (-c' * Real.sqrt (Real.log n)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := Real.sqrt_nonneg (Real.log n)
      nlinarith
    have : (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log n)) ≤ n := by
      have := mul_le_mul_of_nonneg_left he hn0.le
      linarith
    nlinarith [mul_nonneg hY0 hE2]
  · rw [not_le] at h
    have hYn : Y < (n : ℝ) ^ 2 := (Real.sqrt_lt' hn0).mp h
    have hlX : c * Real.log X ≤ Real.log Y := by
      have h1 := Real.log_le_log (Real.rpow_pos_of_pos hX0 c) hY
      rwa [Real.log_rpow hX0] at h1
    have hYpos : 0 < Y := lt_of_lt_of_le (Real.rpow_pos_of_pos hX0 c) hY
    have hlY : Real.log Y ≤ 2 * Real.log n := by
      have := Real.log_le_log hYpos hYn.le
      rwa [Real.log_pow, Nat.cast_ofNat] at this
    have hlx0 : 0 ≤ Real.log X := Real.log_nonneg hX1
    have hl : c / 2 * Real.log X ≤ Real.log n := by linarith
    have hsq : Real.sqrt (c / 2) * Real.sqrt (Real.log X) ≤ Real.sqrt (Real.log n) := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt hl
    have he : Real.exp (-c' * Real.sqrt (Real.log n)) ≤
        Real.exp (-(c' * Real.sqrt (c / 2)) * Real.sqrt (Real.log X)) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hsq hc'.le
      nlinarith
    calc (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log n))
        ≤ Y * Real.exp (-(c' * Real.sqrt (c / 2)) * Real.sqrt (Real.log X)) :=
          mul_le_mul hnY he (Real.exp_pos _).le hY0
      _ ≤ _ := by linarith


/-- Page 51 before display 5.17, the square root log error beats every fixed `T0` power; a copy
of `DQ517StrongPNTInput.eventually_exp_sqrt_log_le`. -/
theorem s130_eventually_exp_sqrt_log_le {c : ℝ} (hc : 0 < c) (N : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp (-c * Real.sqrt (Real.log x)) ≤
        Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
  have ht : Filter.Tendsto (fun u : ℝ => N * u ^ (-(1 / 6 : ℝ))) Filter.atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul N
  have hs : ∀ᶠ u : ℝ in Filter.atTop, N * u ^ (-(1 / 6 : ℝ)) < c :=
    ht.eventually (eventually_lt_nhds hc)
  filter_upwards [Real.tendsto_log_atTop.eventually hs,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hl : 0 < Real.log x := Real.log_pos hx1
  have he : Real.sqrt (Real.log x) * Real.log x ^ (-(1 / 6 : ℝ)) =
      Real.log x ^ (1 / 3 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hl]
    congr 1
    norm_num
  have hmul : N * Real.log x ^ (1 / 3 : ℝ) ≤ c * Real.sqrt (Real.log x) := by
    calc
      _ = Real.sqrt (Real.log x) * (N * Real.log x ^ (-(1 / 6 : ℝ))) := by
        rw [← he]
        ring
      _ ≤ Real.sqrt (Real.log x) * c :=
        mul_le_mul_of_nonneg_left hx.le (Real.sqrt_nonneg (Real.log x))
      _ = _ := by ring
  apply Real.exp_le_exp.mpr
  linarith

/-- PROVED: page 51 display 5.17, the prime number theorem with error term `Y exp(-ε L^(1/2))`,
in the form used in the Buchstab recursion. For `X ^ c ≤ Y ≤ X` the prime count on any
`(L, i]` with `i ≤ Y` is the sum of `1 / log k` up to `Y exp(-N (log X)^(1/3))`, for every `N`.
Strong form of `LowerShortC165.prime_prefix_level`. Proof: partial summation
`PNTPort.BVMax.abel_bound` at modulus `1` from the strong prime number theorem
`LeanLab.PNTPort.psi_explicit_strong` and `Chebyshev.psi_sub_theta_le`; terms `n ≤ √Y` cost
`√Y ≤ Y X^(-c/2)`, terms `n > √Y` have `log n ≥ (c/2) log X`. -/
theorem leaf_strong_prime_prefix_level {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ Cq : ℝ, 0 < Cq ∧ ∀ X : ℝ, Cq ≤ X → ∀ Y : ℝ, X ^ c ≤ Y → Y ≤ X →
      ∀ L i : ℕ, L ≤ i → (i : ℝ) ≤ Y →
        |∑ k ∈ Finset.Ioc L i, (primeWeight k - 1 / Real.log (k : ℝ))| ≤
          Cq * Y * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  obtain ⟨c', hc', K, hK⟩ := LeanLab.PNTPort.psi_explicit_strong
  obtain ⟨K1, hK1, hK1X⟩ := s130_rpow_neg_le_exp (c := c / 2) (by positivity)
    (N := N + 1) (by linarith)
  have hd : 0 < c' * Real.sqrt (c / 2) := mul_pos hc' (Real.sqrt_pos.mpr (by positivity))
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.mp (s130_eventually_exp_sqrt_log_le hd N)
  set A : ℝ := 3 + |K| with hA
  have hA0 : 0 < A := by positivity
  refine ⟨max (max X1 3) (4 * (6 * A * K1 + |K|)), by positivity,
    fun X hX Y hXY hYX L i hLi hiY => ?_⟩
  have hX3 : 3 ≤ X := ((le_max_right _ _).trans (le_max_left _ _)).trans hX
  have hXX1 : X1 ≤ X := ((le_max_left _ _).trans (le_max_left _ _)).trans hX
  have hCq : 4 * (6 * A * K1 + |K|) ≤ max (max X1 3) (4 * (6 * A * K1 + |K|)) := le_max_right _ _
  have hX0 : 0 < X := by linarith
  have hX1' : (1 : ℝ) ≤ X := by linarith
  have hlog1 : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hX0).mpr (by linarith [Real.exp_one_lt_d9])
  have hY1 : 1 ≤ Y := (Real.one_le_rpow hX1' hc.le).trans hXY
  have hY0 : 0 ≤ Y := by linarith
  have hsY1 : 1 ≤ Real.sqrt Y := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hY1
  set E2 := Real.exp (-(c' * Real.sqrt (c / 2)) * Real.sqrt (Real.log X)) with hE2
  set M := A * (Y * X ^ (-(c / 2))) * Real.log X + |K| * Y * E2 with hMdef
  have hE20 : 0 ≤ E2 := (Real.exp_pos _).le
  have hsq := s130_sqrt_le_mul_rpow hX0 hXY
  have hM0 : 0 ≤ M := by positivity
  have hMn : ∀ n ∈ Finset.Icc 2 i, |CC 1 0 n| ≤ M := by
    intro n hn
    obtain ⟨hn2, hni⟩ := Finset.mem_Icc.mp hn
    have hnY : (n : ℝ) ≤ Y := (Nat.cast_le.mpr hni).trans hiY
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have h1 := s130_CC_le hK n hn2
    have h2 := s130_big_term_le hc hc' hX1' hXY n hn2 hnY
    have hsn : Real.sqrt n ≤ Real.sqrt Y := Real.sqrt_le_sqrt hnY
    have hln : Real.log n ≤ Real.log X := Real.log_le_log hn0 (hnY.trans hYX)
    have hln0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have h3 : |K| * ((n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log n))) ≤
        |K| * (Real.sqrt Y + Y * E2) := mul_le_mul_of_nonneg_left h2 (abs_nonneg K)
    have h4 : 2 * Real.sqrt n * Real.log n ≤ 2 * Real.sqrt Y * Real.log X := by
      have := mul_le_mul hsn hln hln0 (Real.sqrt_nonneg Y)
      linarith
    have h5 : Real.sqrt Y * Real.log X ≤ Y * X ^ (-(c / 2)) * Real.log X :=
      mul_le_mul_of_nonneg_right hsq (by linarith)
    have h6 : |K| * Real.sqrt Y ≤ |K| * (Real.sqrt Y * Real.log X) := by
      have := mul_le_mul_of_nonneg_left
        (show Real.sqrt Y ≤ Real.sqrt Y * Real.log X by nlinarith) (abs_nonneg K)
      exact this
    have h7 : (1 : ℝ) ≤ Real.sqrt Y * Real.log X := by nlinarith
    have hK0 := abs_nonneg K
    calc |CC 1 0 n| ≤ |K| * n * Real.exp (-c' * Real.sqrt (Real.log n)) +
          2 * Real.sqrt n * Real.log n + 1 := h1
      _ ≤ |K| * (Real.sqrt Y + Y * E2) + 2 * Real.sqrt Y * Real.log X +
          Real.sqrt Y * Real.log X := by nlinarith
      _ ≤ A * (Real.sqrt Y * Real.log X) + |K| * Y * E2 := by rw [hA]; nlinarith
      _ ≤ M := by
          rw [hMdef]
          have := mul_le_mul_of_nonneg_left h5 hA0.le
          nlinarith
  have hsplit : ∑ k ∈ Finset.Ioc L i, (primeWeight k - 1 / Real.log (k : ℝ)) =
      EE 1 0 i - EE 1 0 L := by
    rw [← s130_prefix_eq_EE, ← s130_prefix_eq_EE]
    have := Finset.sum_Ioc_consecutive (fun k => primeWeight k - 1 / Real.log (k : ℝ))
      (Nat.zero_le L) hLi
    linarith
  have hEi := s130_EE_bound i hM0 hMn
  have hEL := s130_EE_bound L hM0 (fun n hn => hMn n (by
    obtain ⟨a1, a2⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨a1, a2.trans hLi⟩))
  set l := Real.log X ^ (1 / 3 : ℝ) with hl
  have hk1 := hK1X X hX3
  have hk2 := s130_exp_succ_mul_log_le hX1' N
  rw [← hl] at hk1 hk2
  have hsq2 := hX1 X hXX1
  rw [← hl, ← hE2] at hsq2
  have hEN : 0 ≤ Real.exp (-N * l) := (Real.exp_pos _).le
  have hM1 : M ≤ (6 * A * K1 + |K|) * Y * Real.exp (-N * l) := by
    have a1 : X ^ (-(c / 2)) * Real.log X ≤ K1 * (Real.exp (-(N + 1) * l) * Real.log X) := by
      have := mul_le_mul_of_nonneg_right hk1 (by linarith : (0 : ℝ) ≤ Real.log X)
      linarith
    have a2 : K1 * (Real.exp (-(N + 1) * l) * Real.log X) ≤ K1 * (6 * Real.exp (-N * l)) :=
      mul_le_mul_of_nonneg_left hk2 hK1.le
    have a3 : A * Y * (X ^ (-(c / 2)) * Real.log X) ≤ A * Y * (K1 * (6 * Real.exp (-N * l))) :=
      mul_le_mul_of_nonneg_left (a1.trans a2) (by positivity)
    have a4 : |K| * Y * E2 ≤ |K| * Y * Real.exp (-N * l) :=
      mul_le_mul_of_nonneg_left hsq2 (by positivity)
    calc M = A * Y * (X ^ (-(c / 2)) * Real.log X) + |K| * Y * E2 := by rw [hMdef]; ring
      _ ≤ A * Y * (K1 * (6 * Real.exp (-N * l))) + |K| * Y * Real.exp (-N * l) :=
          add_le_add a3 a4
      _ = _ := by ring
  rw [hsplit]
  calc |EE 1 0 i - EE 1 0 L| ≤ |EE 1 0 i| + |EE 1 0 L| := abs_sub _ _
    _ ≤ 2 * M + 2 * M := add_le_add hEi hEL
    _ ≤ 4 * ((6 * A * K1 + |K|) * Y * Real.exp (-N * l)) := by linarith
    _ = (4 * (6 * A * K1 + |K|)) * Y * Real.exp (-N * l) := by ring
    _ ≤ _ := by gcongr

/-- PROVED: page 51 display 5.17, the prime number
theorem with error term `Y exp(-ε L^(1/2))` applied to the least prime factor `p ≥ z` in the
Buchstab recursion for the rough cofactor of display 5.15. The sum over primes `p ≥ z` of `[a < p]` plus the Buchstab density sums at
level `p` over the cofactors equals the sum over all integers `k ≥ z` of the same weight over
`log k`, with error `b exp(-N (log X)^(1/3))` for every `N`. Strong form of
`LowerShortC165.prime_weight_transfer`, by its proof: `prime_transfer_abstract` with the prime
count error of `leaf_strong_prime_prefix_level` at `N + 2`, two factors `log X` absorbed by
`s130_exp_succ_mul_log_le`. -/
theorem strong_prime_weight_transfer (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
            ((if a < p then (1 : ℝ) else 0) +
              ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
                ω (Real.log m / Real.log p) / Real.log p) -
          ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
            ((if a < k then (1 : ℝ) else 0) +
              ∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
                ω (Real.log m / Real.log k) / Real.log k) / Real.log k| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  obtain ⟨Cq, hCq, hpnt⟩ := leaf_strong_prime_prefix_level hc (N + 1 + 1) (by linarith)
  have hE : (0 : ℝ) ≤ 2 / c + 1 := by positivity
  refine ⟨max ((4 : ℝ) ^ (1 / c)) 4 + Cq + 36 * (3 + 4 * (2 / c + 1)) * Cq, by positivity,
    fun X hX z hzX a b ha hb => ?_⟩
  have hpos2 : 0 < 36 * (3 + 4 * (2 / c + 1)) * Cq := by positivity
  have hX4 : 4 ≤ X := by linarith [le_max_right ((4 : ℝ) ^ (1 / c)) 4]
  have hXc : (4 : ℝ) ^ (1 / c) ≤ X := by linarith [le_max_left ((4 : ℝ) ^ (1 / c)) 4]
  have hXq : Cq ≤ X := by
    have : (0 : ℝ) ≤ max ((4 : ℝ) ^ (1 / c)) 4 := by positivity
    linarith
  have hX0 : 0 < X := by linarith
  have hlog1 : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hX0).mpr (by linarith [Real.exp_one_lt_d9])
  have hlog0 : 0 < Real.log X := by linarith
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hLA : 0 ≤ Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := (Real.exp_pos _).le
  have hr0 : 0 ≤ Real.exp (-(N + 1 + 1) * Real.log X ^ (1 / 3 : ℝ)) := (Real.exp_pos _).le
  have h4z : (4 : ℝ) ≤ z := by
    calc (4 : ℝ) = ((4 : ℝ) ^ (1 / c)) ^ c := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
      _ ≤ X ^ c := Real.rpow_le_rpow (by positivity) hXc hc.le
      _ ≤ z := hzX
  have hz4 : 4 ≤ z := by exact_mod_cast h4z
  have hz0 : (0 : ℝ) < z := by linarith
  have hlogz : Real.log X ≤ 1 / c * Real.log z := by
    have h1 := Real.log_le_log (Real.rpow_pos_of_pos hX0 c) hzX
    rw [Real.log_rpow hX0] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / c)
    have e : 1 / c * (c * Real.log X) = Real.log X := by field_simp
    linarith
  have hlogk : ∀ k : ℕ, 3 ≤ k → 1 ≤ Real.log k := by
    intro k hk
    have h3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
    exact (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
  by_cases hzb : z ≤ b
  swap
  · have hK : (Finset.Icc 1 b).filter (fun k => z ≤ k) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun k hk => by
        have := (Finset.mem_Icc.mp hk).2
        omega)
    have hP : (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun k hk => by
        have := (Finset.mem_Icc.mp hk).2
        omega)
    rw [hK, hP, Finset.sum_empty, Finset.sum_empty, sub_zero, abs_zero]
    positivity
  have hmain := prime_transfer_abstract
    (fun m k : ℕ => ω (Real.log m / Real.log k) / Real.log k) (a := a)
    (E := 2 / c + 1) (R := Cq * Real.exp (-(N + 1 + 1) * Real.log X ^ (1 / 3 : ℝ))) (by omega : 2 ≤ z) hzb hE
    (by positivity)
    (by
      intro m k hm hmk
      have hl := hlogk k (by omega)
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hu : Real.log m / Real.log k < 1 := by
        rw [div_lt_one (by linarith)]
        exact Real.log_lt_log hm0 (by exact_mod_cast hmk)
      rw [hz _ hu, zero_div])
    (by
      intro m i hzi him hmb
      have hi3 : 3 ≤ i := by omega
      have hi0 : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hi2 : i + 1 ≤ i ^ 2 := by nlinarith
      have hzi2 : z ≤ i ^ 2 := le_trans (by omega) hi2
      have h1 : Real.log z ≤ 2 * Real.log i := by
        have := Real.log_le_log hz0 (by exact_mod_cast hzi2 : (z : ℝ) ≤ (i : ℝ) ^ 2)
        rw [Real.log_pow] at this
        push_cast at this
        linarith
      have h2 : Real.log m ≤ Real.log X :=
        Real.log_le_log hm0 (le_trans (by exact_mod_cast hmb) hb)
      have h3 : 1 / c * Real.log z ≤ 1 / c * (2 * Real.log i) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have hM : Real.log m ≤ 2 / c * Real.log i := by
        have e : 1 / c * (2 * Real.log i) = 2 / c * Real.log i := by ring
        linarith
      exact density_level_step hω hz hi3 him hM)
    (by
      intro m k hzk
      have hl := hlogk k (by omega)
      rw [abs_div, abs_of_pos (by linarith : 0 < Real.log k)]
      exact (div_le_one (by linarith)).mpr ((abs_buchstab_le_one hω hz _).trans hl))
    (by
      intro Y hzY hYb L i hLi hiY
      exact le_of_le_of_eq (hpnt X hXq Y (hzX.trans hzY) (hYb.trans hb) L i hLi hiY) (by ring))
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hlb0 : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ b))
  have hlb : Real.log b ≤ Real.log X := Real.log_le_log hbpos hb
  have hpow2 : Real.exp (-(N + 1 + 1) * Real.log X ^ (1 / 3 : ℝ)) * Real.log X ^ 2 ≤ 36 * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
    have k1 := s130_exp_succ_mul_log_le (by linarith : (1 : ℝ) ≤ X) (N + 1)
    have k2 := s130_exp_succ_mul_log_le (by linarith : (1 : ℝ) ≤ X) N
    calc Real.exp (-(N + 1 + 1) * Real.log X ^ (1 / 3 : ℝ)) * Real.log X ^ 2 =
          (Real.exp (-(N + 1 + 1) * Real.log X ^ (1 / 3 : ℝ)) * Real.log X) * Real.log X := by ring
      _ ≤ (6 * Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ))) * Real.log X :=
          mul_le_mul_of_nonneg_right k1 hlog0.le
      _ = 6 * (Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) * Real.log X) := by ring
      _ ≤ 6 * (6 * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ))) := by gcongr
      _ = 36 * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by ring
  have h1 : 1 + Real.log b ≤ 2 * Real.log X := by linarith
  have h2 : 1 + (2 / c + 1) * (1 + Real.log b) ≤ (1 + 2 * (2 / c + 1)) * Real.log X := by
    nlinarith
  have h3 : (1 + (2 / c + 1) * (1 + Real.log b)) * (1 + Real.log b) ≤
      ((1 + 2 * (2 / c + 1)) * Real.log X) * (2 * Real.log X) :=
    mul_le_mul h2 h1 (by linarith) (by positivity)
  have h4 : 1 ≤ Real.log X ^ 2 := by nlinarith
  have hCb : 0 ≤ Cq * Real.exp (-(N + 1 + 1) * Real.log X ^ (1 / 3 : ℝ)) * b := by positivity
  calc _ ≤ Cq * Real.exp (-(N + 1 + 1) * Real.log X ^ (1 / 3 : ℝ)) * b + (1 + (2 / c + 1) * (1 + Real.log b)) *
        (Cq * Real.exp (-(N + 1 + 1) * Real.log X ^ (1 / 3 : ℝ)) * b * (1 + Real.log b)) := hmain
    _ = Cq * Real.exp (-(N + 1 + 1) * Real.log X ^ (1 / 3 : ℝ)) * b *
        (1 + (1 + (2 / c + 1) * (1 + Real.log b)) * (1 + Real.log b)) := by ring
    _ ≤ Cq * Real.exp (-(N + 1 + 1) * Real.log X ^ (1 / 3 : ℝ)) * b *
        ((3 + 4 * (2 / c + 1)) * Real.log X ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hCb
        nlinarith
    _ = (3 + 4 * (2 / c + 1)) * Cq * b * (Real.exp (-(N + 1 + 1) * Real.log X ^ (1 / 3 : ℝ)) * Real.log X ^ 2) := by ring
    _ ≤ (3 + 4 * (2 / c + 1)) * Cq * b * (36 * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ))) := by gcongr
    _ = 36 * (3 + 4 * (2 / c + 1)) * Cq * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by ring
    _ ≤ _ := by
        have : (0 : ℝ) ≤ max ((4 : ℝ) ^ (1 / c)) 4 := by positivity
        gcongr
        linarith

/-- PROVED: page 51 display 5.17, the continuous Buchstab identity `u ω(u) = 1 + ∫_1^{u-1} ω`
summed over an interval, with the error of 5.17. The Buchstab density sum at level `z`
over `(a, b]` is the sum of the prime densities `1 / log n`, `n ≥ z`, plus the sum over levels
`z ≤ k < n` of `ω(log (n / k) / log k) / (k log^2 k)`, with error `b exp(-N (log X)^(1/3))`.
Strong form of `LowerShortC165.buchstab_telescope`, by its proof: `buchstab_telescope_term` bounds
each term by `(2 / c + 6) / z`, and `1 / z ≤ X ^ (-c)` beats `exp(-N (log X)^(1/3))`. -/
theorem strong_buchstab_telescope (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log z) / Real.log z -
          ∑ n ∈ Finset.Ioc a b, ((if z ≤ n then 1 / Real.log n else 0) +
            ∑ k ∈ Finset.Ico z n, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2))| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  obtain ⟨K, hK, hKX⟩ := s130_rpow_neg_le_exp hc hN
  have hc6 : 0 < 2 * (1 / c) + 6 := by positivity
  refine ⟨max ((3 : ℝ) ^ (1 / c)) 3 + (2 * (1 / c) + 6) * K, by positivity,
    fun X hX z hzX a b ha hb => ?_⟩
  have hK2 : 0 < (2 * (1 / c) + 6) * K := by positivity
  have hX3 : 3 ≤ X := by linarith [le_max_right ((3 : ℝ) ^ (1 / c)) 3]
  have hXc : (3 : ℝ) ^ (1 / c) ≤ X := by linarith [le_max_left ((3 : ℝ) ^ (1 / c)) 3]
  have hX0 : 0 < X := by linarith
  have h3z : (3 : ℝ) ≤ z := by
    calc (3 : ℝ) = ((3 : ℝ) ^ (1 / c)) ^ c := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
      _ ≤ X ^ c := Real.rpow_le_rpow (by positivity) hXc hc.le
      _ ≤ z := hzX
  have hz3 : 3 ≤ z := by exact_mod_cast h3z
  have hz0 : (0 : ℝ) < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogz : Real.log X ≤ 1 / c * Real.log z := by
    have h1 := Real.log_le_log (Real.rpow_pos_of_pos hX0 c) hzX
    rw [Real.log_rpow hX0] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / c)
    have e : 1 / c * (c * Real.log X) = Real.log X := by field_simp
    linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ n ∈ Finset.Ioc a b, |ω (Real.log n / Real.log z) / Real.log z -
      ((if z ≤ n then 1 / Real.log n else 0) +
        ∑ k ∈ Finset.Ico z n, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2))| ≤
      (2 * (1 / c) + 6) / (z : ℝ) := by
    intro n hn
    obtain ⟨hna, hnb⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    by_cases hzn : z ≤ n
    · rw [ite_eq_left hzn]
      refine buchstab_telescope_term hω hz hz3 hzn ?_
      exact (Real.log_le_log hn0 (le_trans (by exact_mod_cast hnb) hb)).trans hlogz
    · rw [ite_eq_right hzn, Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty, add_zero,
        sub_zero]
      have hu : Real.log n / Real.log z < 1 := by
        rw [div_lt_one hlz]
        exact Real.log_lt_log hn0 (by exact_mod_cast (by omega : n < z))
      rw [hz _ hu, zero_div, abs_zero]
      positivity
  have hzinv : 1 / (z : ℝ) ≤ K * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
    have h1 : 1 / (z : ℝ) ≤ X ^ (-c) := by
      rw [Real.rpow_neg hX0.le, one_div]
      exact inv_anti₀ (Real.rpow_pos_of_pos hX0 c) hzX
    exact h1.trans (hKX X hX3)
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hLA : 0 ≤ Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := (Real.exp_pos _).le
  calc _ ≤ ∑ n ∈ Finset.Ioc a b, |ω (Real.log n / Real.log z) / Real.log z -
      ((if z ≤ n then 1 / Real.log n else 0) +
        ∑ k ∈ Finset.Ico z n, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Ioc a b, (2 * (1 / c) + 6) / (z : ℝ) := Finset.sum_le_sum hterm
    _ = ((b - a : ℕ) : ℝ) * ((2 * (1 / c) + 6) * (1 / (z : ℝ))) := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
        ring
    _ ≤ (b : ℝ) * ((2 * (1 / c) + 6) * (K * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)))) := by
        have : ((b - a : ℕ) : ℝ) ≤ b := by exact_mod_cast Nat.sub_le b a
        gcongr
    _ = (2 * (1 / c) + 6) * K * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by ring
    _ ≤ (max ((3 : ℝ) ^ (1 / c)) 3 + (2 * (1 / c) + 6) * K) * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
        have : (0 : ℝ) ≤ max ((3 : ℝ) ^ (1 / c)) 3 := by positivity
        gcongr
        linarith

/-- PROVED: page 51 display 5.17, the lattice half of the Buchstab identity for densities, with
the error of 5.17. The sum over `n` in `(a, b]` and levels `z ≤ k < n` of
`ω(log (n / k) / log k) / (k log^2 k)` is the sum over levels `k ≥ z` of the Buchstab density
sums at level `k` over the cofactors in `(a / k, b / k]`, over `log k`, with error
`b exp(-N (log X)^(1/3))`. Strong form of `LowerShortC165.lattice_abel`, by its proof, which bounds
the error by `8 b log X / z`, and `log X / z` beats `exp(-N (log X)^(1/3))`. -/
theorem strong_lattice_abel (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, ∑ k ∈ Finset.Ico z n,
            ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) -
          ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
            (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
              ω (Real.log m / Real.log k) / Real.log k) / Real.log k| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  obtain ⟨K, hK, hKX⟩ := s130_rpow_neg_le_exp hc (N := N + 1) (by linarith)
  refine ⟨max ((3 : ℝ) ^ (1 / c)) 3 + 48 * K, by positivity, fun X hX z hzX a b ha hb => ?_⟩
  have hX3 : 3 ≤ X := by linarith [le_max_right ((3 : ℝ) ^ (1 / c)) 3]
  have hXc : (3 : ℝ) ^ (1 / c) ≤ X := by linarith [le_max_left ((3 : ℝ) ^ (1 / c)) 3]
  have hX0 : 0 < X := by linarith
  have hz3 : 3 ≤ z := three_le_level hc hXc hzX
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hlog1 : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hX0).mpr (by linarith [Real.exp_one_lt_d9])
  have hlog0 : 0 < Real.log X := by linarith
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hlogk : ∀ k : ℕ, 3 ≤ k → 1 ≤ Real.log k := by
    intro k hk
    have h3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
    exact (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
  have hswap : ∑ n ∈ Finset.Ioc a b, ∑ k ∈ Finset.Ico z n,
        ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) =
      ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k), ∑ n ∈ Finset.Ioc a b,
        ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) := by
    calc _ = ∑ n ∈ Finset.Ioc a b, ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
          ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) := by
          refine Finset.sum_congr rfl fun n hn => Finset.sum_subset ?_ ?_
          · intro k hk
            have h1 := Finset.mem_Ico.mp hk
            have h2 := Finset.mem_Ioc.mp hn
            exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, h1.1⟩
          · intro k hk hnot
            obtain ⟨hk1, hzk⟩ := Finset.mem_filter.mp hk
            have hnk : n ≤ k := by
              by_contra h
              exact hnot (Finset.mem_Ico.mpr ⟨hzk, by omega⟩)
            have hn0 : (0 : ℝ) < n := by
              exact_mod_cast (by have := (Finset.mem_Ioc.mp hn).1; omega : 0 < n)
            have hl := hlogk k (by omega)
            have hu : Real.log n / Real.log k - 1 < 1 := by
              have h3 : Real.log n / Real.log k ≤ 1 :=
                (div_le_one (by linarith)).mpr (Real.log_le_log hn0 (by exact_mod_cast hnk))
              linarith
            rw [hz _ hu, zero_div]
      _ = _ := Finset.sum_comm
  have hlevel : ∀ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
      (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
          ω (Real.log m / Real.log k) / Real.log k) / Real.log k =
        ∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
          (if k ∣ n then (k : ℝ) else 0) := by
    intro k hk
    obtain ⟨hk1, hzk⟩ := Finset.mem_filter.mp hk
    have hkb : k ≤ b := (Finset.mem_Icc.mp hk1).2
    have hk3 : 3 ≤ k := by omega
    have hl := hlogk k hk3
    have hκ0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have h1 : ∀ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
          (if k ∣ n then (k : ℝ) else 0) =
        if k ∣ n then ω (Real.log ((k * (n / k) : ℕ) : ℝ) / Real.log k - 1) /
          (k * Real.log k ^ 2) * k else 0 := by
      intro n _
      by_cases hd : k ∣ n
      · simp only [hd, ite_true]
        rw [Nat.mul_div_cancel' hd]
      · simp [hd]
    rw [Finset.sum_congr rfl h1, sum_dvd_reindex_real (by omega : 1 ≤ k) a b
      (fun m : ℕ => ω (Real.log ((k * m : ℕ) : ℝ) / Real.log k - 1) /
          (k * Real.log k ^ 2) * k),
      cofactor_one_split (by omega : 2 ≤ k) hkb]
    have h0 : ω (Real.log ((k * 1 : ℕ) : ℝ) / Real.log k - 1) / (k * Real.log k ^ 2) * k = 0 := by
      rw [mul_one, div_self (by linarith), sub_self, hz 0 (by norm_num), zero_div, zero_mul]
    rw [h0, ite_self, zero_add, Finset.sum_div]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : (0 : ℝ) < m := by
      exact_mod_cast (by have := (Finset.mem_Ioc.mp hm).1; omega : 0 < m)
    have e : Real.log ((k * m : ℕ) : ℝ) / Real.log k - 1 = Real.log m / Real.log k := by
      push_cast
      rw [Real.log_mul hκ0.ne' hm0.ne']
      field_simp
      ring
    rw [e]
    field_simp
  rw [hswap, Finset.sum_congr rfl hlevel, ← Finset.sum_sub_distrib]
  have hkbound : ∀ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
      |∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) -
        ∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
          (if k ∣ n then (k : ℝ) else 0)| ≤
        4 * Real.log X * (b * (1 / (k : ℝ) ^ 2)) := by
    intro k hk
    obtain ⟨hk1, hzk⟩ := Finset.mem_filter.mp hk
    have hk3 : 3 ≤ k := by omega
    have hl := hlogk k hk3
    have hκ0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hrhs : 0 ≤ 4 * Real.log X * (b * (1 / (k : ℝ) ^ 2)) := by positivity
    have e : ∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) -
        ∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
          (if k ∣ n then (k : ℝ) else 0) =
        -∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
          ((if k ∣ n then (k : ℝ) else 0) - 1) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [e, abs_neg]
    by_cases hkb : k ^ 2 ≤ b
    · have hab : a ≤ b ∨ b < a := le_or_gt a b
      rcases hab with hab | hab
      · have hkb' : (k : ℝ) ^ 2 ≤ b := by exact_mod_cast hkb
        have hbpos : (0 : ℝ) < b := lt_of_lt_of_le (by positivity) hkb'
        have h1 : 1 ≤ (b : ℝ) * (1 / (k : ℝ) ^ 2) := by
          rw [mul_one_div, le_div_iff₀ (by positivity), one_mul]
          exact hkb'
        have h2 : Real.log b ≤ Real.log X := Real.log_le_log hbpos hb
        calc _ ≤ 3 + Real.log b := lattice_level_bound hω hz hk3 ha hab
          _ ≤ 4 * Real.log X * 1 := by linarith
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
      · rw [Finset.Ioc_eq_empty_of_le hab.le, Finset.sum_empty, abs_zero]
        exact hrhs
    · have hzero : ∑ n ∈ Finset.Ioc a b,
          ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
            ((if k ∣ n then (k : ℝ) else 0) - 1) = 0 := by
        refine Finset.sum_eq_zero fun n hn => ?_
        obtain ⟨hna, hnb⟩ := Finset.mem_Ioc.mp hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hu : Real.log n / Real.log k - 1 < 1 := by
          have h2l : Real.log n < 2 * Real.log k := by
            have := Real.log_lt_log hn0
              (by exact_mod_cast (by omega : n < k ^ 2) : (n : ℝ) < (k : ℝ) ^ 2)
            rw [Real.log_pow] at this
            push_cast at this
            linarith
          have : Real.log n / Real.log k < 2 := (div_lt_iff₀ (by linarith)).mpr h2l
          linarith
        rw [hz _ hu, zero_div, zero_mul]
      rw [hzero, abs_zero]
      exact hrhs
  have hsum : ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k), 1 / (k : ℝ) ^ 2 ≤ 2 / (z : ℝ) := by
    refine le_trans ?_ (sum_inv_sq_Ico (by omega : 2 ≤ z) (max z (b + 1)) (le_max_left _ _))
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
    intro k hk
    obtain ⟨hk1, hzk⟩ := Finset.mem_filter.mp hk
    have hkb : k ≤ b := (Finset.mem_Icc.mp hk1).2
    exact Finset.mem_Ico.mpr ⟨hzk, lt_of_lt_of_le (by omega : k < b + 1) (le_max_right _ _)⟩
  have hzinv : 1 / (z : ℝ) ≤ K * Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) := by
    have h1 : 1 / (z : ℝ) ≤ X ^ (-c) := by
      rw [Real.rpow_neg hX0.le, one_div]
      exact inv_anti₀ (Real.rpow_pos_of_pos hX0 c) hzX
    exact h1.trans (hKX X hX3)
  have hpow : Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) * Real.log X ≤ 6 * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) :=
    s130_exp_succ_mul_log_le (by linarith) N
  have hLA : 0 ≤ Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := (Real.exp_pos _).le
  calc _ ≤ ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
        |∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) -
          ∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
            (if k ∣ n then (k : ℝ) else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
        4 * Real.log X * (b * (1 / (k : ℝ) ^ 2)) := Finset.sum_le_sum hkbound
    _ = 4 * Real.log X * b * ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
        1 / (k : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ 4 * Real.log X * b * (2 * (K * Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)))) := by
        have h2 : 2 / (z : ℝ) = 2 * (1 / (z : ℝ)) := by ring
        have h3 : 2 / (z : ℝ) ≤ 2 * (K * Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ))) := by
          rw [h2]
          exact mul_le_mul_of_nonneg_left hzinv (by norm_num)
        exact mul_le_mul_of_nonneg_left (hsum.trans h3) (by positivity)
    _ = 8 * K * b * (Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) * Real.log X) := by ring
    _ ≤ 8 * K * b * (6 * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ))) := by gcongr
    _ = 48 * K * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by ring
    _ ≤ (max ((3 : ℝ) ^ (1 / c)) 3 + 48 * K) * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
        have : (0 : ℝ) ≤ max ((3 : ℝ) ^ (1 / c)) 3 := by positivity
        gcongr
        linarith

/-! ### Proved steps -/

/-- Page 51 display 5.17, the main term of the Buchstab recursion with the error of 5.17:
assembled from the three inputs exactly as `LowerShortC165.buchstab_main_term`. -/
theorem strong_buchstab_main_term (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log z) / Real.log z -
          ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
            ((if a < p then (1 : ℝ) else 0) +
              ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
                ω (Real.log m / Real.log p) / Real.log p)| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  obtain ⟨CA, hCA, hA'⟩ := strong_prime_weight_transfer ω hω hz hc N hN
  obtain ⟨C1, hC1, h1'⟩ := strong_buchstab_telescope ω hω hz hc N hN
  obtain ⟨C2, hC2, h2'⟩ := strong_lattice_abel ω hω hz hc N hN
  refine ⟨CA + C1 + C2, by positivity, fun X hX z hzX a b ha hb => ?_⟩
  have hAb := hA' X (by linarith) z hzX a b ha hb
  have h1 := h1' X (by linarith) z hzX a b ha hb
  have h2 := h2' X (by linarith) z hzX a b ha hb
  have hid : ∑ n ∈ Finset.Ioc a b, (if z ≤ n then 1 / Real.log (n : ℝ) else 0) =
      ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
        (if a < k then (1 : ℝ) else 0) / Real.log k := by
    have hI : Finset.Ioc a b = (Finset.Icc 1 b).filter (fun k => a < k) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hI, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : a < k <;> by_cases h2 : z ≤ k <;> simp [h1, h2]
  have e1 : ∑ n ∈ Finset.Ioc a b, ((if z ≤ n then 1 / Real.log (n : ℝ) else 0) +
        ∑ k ∈ Finset.Ico z n, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2)) =
      ∑ n ∈ Finset.Ioc a b, (if z ≤ n then 1 / Real.log (n : ℝ) else 0) +
        ∑ n ∈ Finset.Ioc a b, ∑ k ∈ Finset.Ico z n,
          ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) := Finset.sum_add_distrib
  have e2 : ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
        ((if a < k then (1 : ℝ) else 0) +
          ∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
            ω (Real.log m / Real.log k) / Real.log k) / Real.log k =
      ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
          (if a < k then (1 : ℝ) else 0) / Real.log k +
        ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
          (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
            ω (Real.log m / Real.log k) / Real.log k) / Real.log k := by
    simp only [add_div, Finset.sum_add_distrib]
  rw [e1, hid] at h1
  rw [e2] at hAb
  obtain ⟨hA1, hA2⟩ := abs_le.mp hAb
  obtain ⟨h11, h12⟩ := abs_le.mp h1
  obtain ⟨h21, h22⟩ := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith

/-- Page 51 display 5.17, the induction on the number of prime factors with the error of 5.17,
as `LowerShortC165.rough_density_strip`: the case `k` at each level `p ≥ z` with `N + 1`, the
harmonic sum over `p` costing `2 log X ≤ 12 exp((log X)^(1/3))`, and `strong_buchstab_main_term`. -/
theorem strong_rough_density_strip (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (k : ℕ) : ∀ N : ℝ, 0 < N →
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X → b < z ^ (k + 1) →
        |∑ n ∈ Finset.Ioc a b, (roughIndicator n z -
            ω (Real.log n / Real.log z) / Real.log z)| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  induction k with
  | zero =>
    intro N hN
    refine ⟨1, one_pos, fun X hX z _ a b ha _ hbz => ?_⟩
    rw [zero_add, pow_one] at hbz
    have hzero : ∑ n ∈ Finset.Ioc a b, (roughIndicator n z -
        ω (Real.log n / Real.log z) / Real.log z) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      obtain ⟨hna, hnb⟩ := Finset.mem_Ioc.mp hn
      have hnz : n < z := lt_of_le_of_lt hnb hbz
      have hr : roughIndicator n z = 0 := by
        unfold roughIndicator
        rw [ite_eq_right]
        rintro (h | h)
        · omega
        · have := Nat.minFac_le (by omega : 0 < n)
          omega
      have hlz : 0 < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
      have hu : Real.log n / Real.log z < 1 := by
        rw [div_lt_one hlz]
        exact Real.log_lt_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hnz)
      rw [hr, hz _ hu]
      simp
    rw [hzero, abs_zero]
    have := Real.exp_pos (-N * Real.log X ^ (1 / 3 : ℝ))
    positivity
  | succ k ih =>
    intro N hN
    obtain ⟨C1, hC1, h1⟩ := ih (N + 1) (by linarith)
    obtain ⟨C2, hC2, h2⟩ := strong_buchstab_main_term ω hω hz hc N hN
    refine ⟨max (max C1 C2) 3 + 12 * C1 + C2, by positivity,
      fun X hX z hzX a b ha hb hbz => ?_⟩
    have hm3 : (3 : ℝ) ≤ max (max C1 C2) 3 := le_max_right _ _
    have hm1 : C1 ≤ max (max C1 C2) 3 := (le_max_left _ _).trans (le_max_left _ _)
    have hm2 : C2 ≤ max (max C1 C2) 3 := (le_max_right _ _).trans (le_max_left _ _)
    have hX1 : C1 ≤ X := by linarith
    have hX2 : C2 ≤ X := by linarith
    have hX3 : 3 ≤ X := by linarith
    have hlog1 : 1 ≤ Real.log X :=
      (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
    have hlog0 : 0 < Real.log X := by linarith
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    set l := Real.log X ^ (1 / 3 : ℝ) with hl
    have hpow : Real.exp (-(N + 1) * l) * (2 * Real.log X) ≤ 12 * Real.exp (-N * l) := by
      have h6 := log_le_six_exp_cuberoot (by linarith : (1 : ℝ) ≤ X)
      rw [← hl] at h6
      have e : Real.exp (-(N + 1) * l) * Real.exp l = Real.exp (-N * l) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hE0 : 0 ≤ Real.exp (-(N + 1) * l) := (Real.exp_pos _).le
      calc Real.exp (-(N + 1) * l) * (2 * Real.log X)
          ≤ Real.exp (-(N + 1) * l) * (2 * (6 * Real.exp l)) :=
            mul_le_mul_of_nonneg_left (by linarith) hE0
        _ = 12 * (Real.exp (-(N + 1) * l) * Real.exp l) := by ring
        _ = 12 * Real.exp (-N * l) := by rw [e]
    have hL0 : 0 ≤ Real.exp (-(N + 1) * l) := (Real.exp_pos _).le
    have hsplit : ∀ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
        ∑ m ∈ Finset.Ioc (a / p) (b / p), roughIndicator m p =
          (if a < p then (1 : ℝ) else 0) +
            ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p), roughIndicator m p := by
      intro p hp
      obtain ⟨hpI, hpp, -⟩ := Finset.mem_filter.mp hp
      rw [cofactor_one_split hpp.two_le (Finset.mem_Icc.mp hpI).2 (fun m => roughIndicator m p)]
      simp [roughIndicator]
    have key : ∑ n ∈ Finset.Ioc a b, (roughIndicator n z -
          ω (Real.log n / Real.log z) / Real.log z) =
        ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
          ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
            (roughIndicator m p - ω (Real.log m / Real.log p) / Real.log p) -
        (∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log z) / Real.log z -
          ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
            ((if a < p then (1 : ℝ) else 0) +
              ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
                ω (Real.log m / Real.log p) / Real.log p)) := by
      rw [Finset.sum_sub_distrib, rough_sum_decomp z a b ha, Finset.sum_congr rfl hsplit]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      ring
    have hinner : ∀ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
        |∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
            (roughIndicator m p - ω (Real.log m / Real.log p) / Real.log p)| ≤
          C1 * b * Real.exp (-(N + 1) * l) * (p : ℝ)⁻¹ := by
      intro p hp
      obtain ⟨hpI, hpp, hzp⟩ := Finset.mem_filter.mp hp
      have hp0 : 0 < p := hpp.pos
      have hbp : b / p < p ^ (k + 1) := by
        rw [Nat.div_lt_iff_lt_mul hp0, ← pow_succ]
        exact lt_of_lt_of_le hbz (Nat.pow_le_pow_left hzp _)
      have hcast : ((b / p : ℕ) : ℝ) ≤ (b : ℝ) / p := Nat.cast_div_le
      have hbpX : ((b / p : ℕ) : ℝ) ≤ X :=
        le_trans (by exact_mod_cast Nat.div_le_self b p) hb
      have h := h1 X hX1 p (hzX.trans (by exact_mod_cast hzp)) (max (a / p) 1) (b / p)
        (le_max_right _ _) hbpX hbp
      calc _ ≤ C1 * ((b / p : ℕ) : ℝ) * Real.exp (-(N + 1) * l) := h
        _ ≤ C1 * ((b : ℝ) / p) * Real.exp (-(N + 1) * l) := by gcongr
        _ = _ := by rw [div_eq_mul_inv]; ring
    have hharm : ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p), ((p : ℝ))⁻¹ ≤
        2 * Real.log X := by
      have hs : ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p), ((p : ℝ))⁻¹ ≤
          ∑ p ∈ Finset.Icc 1 b, ((p : ℝ))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => by positivity)
      have hh : ∑ p ∈ Finset.Icc 1 b, ((p : ℝ))⁻¹ = (harmonic b : ℝ) := by
        simp [harmonic_eq_sum_Icc]
      have hl' : Real.log b ≤ Real.log X := by
        rcases Nat.eq_zero_or_pos b with h0 | h0
        · subst h0
          simpa using hlog0.le
        · exact Real.log_le_log (by exact_mod_cast h0) hb
      have := harmonic_le_one_add_log b
      linarith
    have hleaf := h2 X hX2 z hzX a b ha hb
    have hEN : 0 ≤ Real.exp (-N * l) := (Real.exp_pos _).le
    rw [key]
    calc _ ≤ |∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
              ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
                (roughIndicator m p - ω (Real.log m / Real.log p) / Real.log p)| +
            C2 * b * Real.exp (-N * l) := (abs_sub _ _).trans (by gcongr)
      _ ≤ ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
              C1 * b * Real.exp (-(N + 1) * l) * (p : ℝ)⁻¹ + C2 * b * Real.exp (-N * l) := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hinner)
      _ ≤ C1 * b * Real.exp (-(N + 1) * l) * (2 * Real.log X) +
            C2 * b * Real.exp (-N * l) := by
          rw [← Finset.mul_sum]
          gcongr
      _ = C1 * b * (Real.exp (-(N + 1) * l) * (2 * Real.log X)) +
            C2 * b * Real.exp (-N * l) := by ring
      _ ≤ C1 * b * (12 * Real.exp (-N * l)) + C2 * b * Real.exp (-N * l) := by
          gcongr
      _ = (12 * C1 + C2) * b * Real.exp (-N * l) := by ring
      _ ≤ (max (max C1 C2) 3 + 12 * C1 + C2) * b * Real.exp (-N * l) := by
          gcongr
          linarith

/-- PROVED: page 51 display 5.17, with exactly the statement
of `DQ517Window.leaf_rough_window_density`. From `strong_rough_density_strip` with `k` past
`1 / c`, as `LowerShortC165.rough_interval_density`. -/
theorem leaf_rough_window_density_of_s130 (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, (Task308.roughIndicator n z -
            ω (Real.log n / Real.log z) / Real.log z)| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := strong_rough_density_strip ω hω hz hc ⌈1 / c⌉₊ N hN
  refine ⟨C + 2, by linarith, fun X hX z hzX a b ha hb => ?_⟩
  have hX1 : 1 < X := by linarith
  have hk : 1 < c * ((⌈1 / c⌉₊ + 1 : ℕ) : ℝ) := by
    have h1 : 1 / c ≤ (⌈1 / c⌉₊ : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hc] at h1
    push_cast
    nlinarith
  have hbz : b < z ^ (⌈1 / c⌉₊ + 1) := by
    have h3 : X < (z : ℝ) ^ (⌈1 / c⌉₊ + 1) := by
      calc X = X ^ (1 : ℝ) := (Real.rpow_one X).symm
        _ < X ^ (c * ((⌈1 / c⌉₊ + 1 : ℕ) : ℝ)) := Real.rpow_lt_rpow_of_exponent_lt hX1 hk
        _ = (X ^ c) ^ (⌈1 / c⌉₊ + 1) := by
            rw [Real.rpow_mul (by linarith), Real.rpow_natCast]
        _ ≤ (z : ℝ) ^ (⌈1 / c⌉₊ + 1) :=
            pow_le_pow_left₀ (Real.rpow_nonneg (by linarith) _) hzX _
    exact_mod_cast lt_of_le_of_lt hb h3
  have hE := (Real.exp_pos (-N * Real.log X ^ (1 / 3 : ℝ))).le
  calc _ ≤ C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := h X (by linarith) z hzX a b ha hb hbz
    _ ≤ (C + 2) * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
        have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
        gcongr
        linarith

end LeanLab.BHP1997.S130RoughWindow
