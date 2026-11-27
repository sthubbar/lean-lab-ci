/-
Burst 2026-11-22, BHP1997, wave 3: the two window leaves of `DQ517WindowSplit`,
`leaf_two_window` and `leaf_four_window`, split once along the paper.
Source: P0069 Baker Harman Pintz 1997, page 51, display 5.17: "It is a straightforward
consequence of the prime number theorem, with error term `Y exp(-ε L^(1/2))`, that ...".

The E2 and E4 terms of b0, display 5.15 on page 50, are sums over outer primes `p1 p2` or
`p1 p2 p3 p4` of the rough indicator of the cofactor. The prime number theorem enters twice:
* for the primes of the rough cofactor, giving its Buchstab density `ω(u) / log z` on every
  integer interval: `leaf_rough_window_density`, HARD;
* for the outer primes, turning the sum of those Buchstab densities into the E2 or E4 integral
  at `m = Z ^ s`: `leaf_two_main_window` and `leaf_four_main_window`, HARD.
This is the cut of the proved prefix assembly `LowerPrincipal517g.two_rough_density_of_leaves`
and `four_rough_density_of_leaves`, with every log power error replaced by the error of 5.17,
`Y T0^(-5)` where `T0 = exp(L^(1/3))`. The prime number theorem error `exp(-ε L^(1/2))` of the
paper beats every power of `T0`, so the leaves are stated with the error `exp(-N L^(1/3))`, the
form of the lab input `DQ517StrongPNTInput.psi_error_stretched`.

PROVED here, from the three leaves: `two_window_of_leaves` and `four_window_of_leaves`, with
exactly the statements of `DQ517Window.leaf_two_window` and `DQ517Window.leaf_four_window`,
which now close by them.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DQLowerExceptionalMeanSquareDecisions
import LeanLab.BHP1997.LowerPrincipal517g

namespace LeanLab.BHP1997.DQ517Window
open Classical Complex Decomp132 DecompC165b DecompC165d LowerShortC165 LowerShortMeanSquare
open LeanLab.BHP1997.DQLowerExceptionalMeanSquare
open scoped BigOperators

/-! ### Strong error bookkeeping -/

/-- Page 51 display 5.17, the strong error of the prime number theorem beats every fixed power
of `T0` with room for polynomial log factors: for every `c > 0`, `k >= 0` and `N > 0` there is
a threshold beyond which `exp(-c sqrt(log X)) (log X)^k <= exp(-N (log X)^(1/3))`. This is the
one-step bookkeeping that turns the square root log error of the strong prime number theorem
into the stretched error `exp(-N L^(1/3))` of the window leaves, while absorbing the
polynomial log factors that the partial summation chain multiplies into it. -/
theorem exp_sqrt_log_poly_le_third {c N k : ℝ} (hc : 0 < c) (hN : 0 < N) (hk : 0 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X →
      Real.exp (-c * Real.sqrt (Real.log X)) * Real.log X ^ k ≤
        Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  set M := N + k * (1 + Real.log 6) with hMdef
  have hM0 : 0 < M := by
    have hlog6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    have hnk : 0 ≤ k * (1 + Real.log 6) := by positivity
    unfold M hMdef
    linarith
  obtain ⟨C0, hC0⟩ :=
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 6 by norm_num)).eventually
      (eventually_lt_nhds (hc / hM0))
  refine ⟨Real.exp (max C0 1), Real.exp_pos _, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) < X := by
    have h2 : (1 : ℝ) < Real.exp (max C0 1) := Real.exp_pos _
    exact h2.trans (Real.exp_le_exp.mpr hX)
  have hlpos : 0 < Real.log X := Real.log_pos hX1
  set l := Real.log X with hl
  have hlc : (0 : ℝ) ≤ l := hlpos.le
  have hl1 : (1 : ℝ) ≤ l := by
    have h2 : (1 : ℝ) < Real.exp (max C0 1) := Real.exp_pos _
    have h3 : Real.exp (max C0 1) ≤ X := Real.exp_le_exp.mpr hX
    have h4 : Real.exp 1 ≤ Real.exp (max C0 1) := Real.exp_le_exp.mpr (le_max_right _ _)
    have h5 : Real.exp 1 ≤ X := le_trans h4 h3
    have h6 : (1 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) (le_of_lt (Real.exp_pos 1))
    have h7 : Real.log (Real.exp 1) ≤ Real.log X := Real.log_le_log h6 h5
    rw [Real.log_exp] at h7
    exact h7
  set t := l ^ (1 / 3 : ℝ) with htdef
  have ht0 : 0 ≤ t := Real.rpow_nonneg hlc _
  have htpos : 0 < t := by
    rw [htdef]
    exact Real.rpow_pos_of_pos hlpos _
  have ht1 : (1 : ℝ) ≤ t := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hlc, Real.rpow_one]
    exact hl1
  have hc0 : l ^ (-(1 / 6 : ℝ)) < c / M := hC0 l (Real.tendsto_log_atTop hlpos)
  have hroot : 0 < l ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hlpos _
  have hcM : M < c * l ^ (1 / 6 : ℝ) := by
    rw [div_lt_iff₀ hroot] at hc0
    calc M = M * 1 := by ring
      _ ≤ M * l ^ (1 / 6 : ℝ) := by
          exact mul_le_mul_of_nonneg_left (by rw [← Real.rpow_natCast, ← Real.rpow_mul hlc,
            show ((6 : ℕ) : ℝ) * (1 / 6) = 1 by norm_num, Real.rpow_one]; exact hl1) hM0.le
      _ < c * l ^ (1 / 6 : ℝ) := by
          exact lt_of_le_of_lt hc0 (by rw [div_mul_eq_mul_div, div_lt_iff₀ hroot] at hc0 ⊢ <;>
            exact hc0)
  have hcube : t ^ 3 = l := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hlc]
    norm_num
  have htfact : t ^ 3 ≤ 6 * Real.exp t := by
    have h := Real.pow_div_factorial_le_exp t ht0 3
    have hfac : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num
    simpa [hfac] using h
  have h3log : Real.log l ≤ t + Real.log 6 := by
    have h1 : Real.log (t ^ 3) ≤ Real.log (6 * Real.exp t) :=
      Real.log_le_log (by positivity) htfact
    rw [hcube, Real.log_mul (by positivity) (Real.exp_pos t), Real.log_pow,
      show ((3 : ℕ) : ℝ) = 3 by norm_num] at h1
    linarith
  have hkey : -c * Real.sqrt l + k * Real.log l ≤ -N * t := by
    have hspl : Real.sqrt l = t * l ^ (1 / 6 : ℝ) := by
      rw [Real.sqrt_eq_rpow, htdef, ← Real.rpow_add hlc]
      congr 1
      norm_num
    have hlogl : Real.log l = 3 * Real.log t := by
      rw [← hcube, Real.log_pow, show ((3 : ℕ) : ℝ) = 3 by norm_num]
    have hstep1 : c * Real.sqrt l ≥ (N + k * (1 + Real.log 6)) * t := by
      rw [hspl]
      calc c * (t * l ^ (1 / 6 : ℝ)) = (c * l ^ (1 / 6 : ℝ)) * t := by ring
        _ > M * t := mul_lt_mul_of_pos_right hcM htpos
        _ = (N + k * (1 + Real.log 6)) * t := by rw [hMdef]
    have hstep2 : k * Real.log l ≤ k * t + k * Real.log 6 := by
      rw [hlogl]
      nlinarith [hk, Real.log_nonneg (show (2 : ℝ) ≤ 6 by norm_num)]
    have ht3 : (0 : ℝ) ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    nlinarith [hstep1, hstep2, ht1, ht3, hk]
  have hpow : Real.log X ^ k = Real.exp (Real.log l * k) := (Real.exp_log hlpos).symm
  rw [hpow, Real.exp_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-! ### The three leaves -/

/-- LEAF: page 51 display 5.17, the prime number theorem for the primes of the rough cofactor
`n3` or `n5` of display 5.15. HARD. P0069: "a straightforward consequence of the prime number
theorem, with error term `Y exp(-ε L^(1/2))`". On every integer interval `(a, b]` below `X`,
numbers with no prime factor below `z ≥ X ^ c` have density `ω(log n / log z) / log z`, error
`b exp(-N (log X)^(1/3))` for every `N`. Strong error form of
`LowerShortC165.leaf_rough_interval_density`; route: Buchstab's identity with the error of
`DQ517StrongPNTInput.psi_error_stretched`. -/
theorem leaf_rough_window_density (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, (Task308.roughIndicator n z -
            ω (Real.log n / Real.log z) / Real.log z)| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  sorry

/-- LEAF: page 51 display 5.17, the prime number theorem applied to the outer primes `p1`, `p2`
of the E2 sum of display 5.15. HARD. P0069: "a straightforward consequence of the prime number
theorem, with error term `Y exp(-ε L^(1/2))`". With the rough cofactor `n3 = m / (p1 p2)`
replaced by its Buchstab density at level `p2`, the sum over prime pairs with exponents in E2
has local density `(1 / log Z) ∫∫_{E2} ω((s - β1 - β2) / β2) / (β1 β2^2)` at `m = Z^s`, with
error `O(Y T0^(-5))` on every integer subinterval of J. The window form of
`LowerShortC165.leaf_two_density_main`. -/
theorem leaf_two_main_window (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ a b : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ ≤ a →
      b ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc a b,
        ((∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
              i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
                lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
            if i.1 * i.2 ∣ m then
              ω (Real.log ((m / (i.1 * i.2) : ℕ) : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ)
            else 0) -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by
  sorry

/-- LEAF: page 51 display 5.17, the prime number theorem applied to the outer primes `p1` to
`p4` of the E4 sum of display 5.15. HARD. P0069: "a straightforward consequence of the prime
number theorem, with error term `Y exp(-ε L^(1/2))`". With the rough cofactor
`n5 = m / (p1 p2 p3 p4)` replaced by its Buchstab density at level `p4`, the sum over prime
quadruples with exponents in E4 has local density the E4 integral of page 51 with `1` replaced
by `s`, over `log Z`, at `m = Z^s`, with error `O(Y T0^(-5))` on every integer subinterval of J.
The window form of `LowerShortC165.leaf_four_density_main`. -/
theorem leaf_four_main_window (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ a b : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ ≤ a →
      b ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc a b,
        ((∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
              i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
                i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
                lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                  (expo ε x i.2.2.2)),
            if i.1 * i.2.1 * i.2.2.1 * i.2.2.2 ∣ m then
              ω (Real.log ((m / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2) : ℕ) : ℝ) /
                  Real.log (i.2.2.2 : ℝ)) / Real.log (i.2.2.2 : ℝ)
            else 0) -
          lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by
  sorry

/-! ### Proved steps -/

/-- Page 51 display 5.17. The summation of the rough density estimate over the outer primes of
a subtracted sum of display 5.15, as `LowerPrincipal517g.rough_family_density_sum`, for any
error factor `E ≥ 0` in place of a log power. -/
theorem rough_family_window_sum (ω : ℝ → ℝ) {c C E X : ℝ} (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hmain : ∀ z : ℕ, X ^ c ≤ (z : ℝ) → ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
      |∑ n ∈ Finset.Ioc a b, (Task308.roughIndicator n z -
          ω (Real.log n / Real.log z) / Real.log z)| ≤ C * b * E)
    {ι : Type} (I : Finset ι) (d z : ι → ℕ) (L U : ℕ) (M : ℝ)
    (hI : ∀ i ∈ I, 1 ≤ d i ∧ d i ≤ L ∧ X ^ c ≤ (z i : ℝ)) (hU : (U : ℝ) ≤ X)
    (hM : ∑ i ∈ I, (1 : ℝ) / (d i : ℝ) ≤ M) :
    |∑ m ∈ Finset.Ioc L U, ∑ i ∈ I, (if d i ∣ m then
        Task308.roughIndicator (m / d i) (z i) -
          ω (Real.log ((m / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)
        else 0)| ≤ C * M * U * E := by
  have hUnn : (0 : ℝ) ≤ (U : ℝ) := Nat.cast_nonneg U
  rw [Finset.sum_comm]
  have hterm : ∀ i ∈ I, |∑ m ∈ Finset.Ioc L U, (if d i ∣ m then
        Task308.roughIndicator (m / d i) (z i) -
          ω (Real.log ((m / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)
        else 0)| ≤ C * U * E * ((1 : ℝ) / (d i : ℝ)) := by
    intro i hi
    obtain ⟨hd1, hdL, hz⟩ := hI i hi
    have hd0 : 0 < d i := hd1
    rw [real_sum_dvd_reindex hd1 L U
      (fun m => Task308.roughIndicator (m / d i) (z i) -
          ω (Real.log ((m / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ))]
    have hre : ∑ n ∈ Finset.Ioc (L / d i) (U / d i),
        (Task308.roughIndicator (d i * n / d i) (z i) -
          ω (Real.log ((d i * n / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)) =
        ∑ n ∈ Finset.Ioc (L / d i) (U / d i),
          (Task308.roughIndicator n (z i) -
            ω (Real.log (n : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Nat.mul_div_cancel_left n hd0]
    rw [hre]
    have hcast : ((U / d i : ℕ) : ℝ) ≤ (U : ℝ) / (d i : ℝ) := Nat.cast_div_le
    have hUd : (U : ℝ) / (d i : ℝ) ≤ U :=
      div_le_self hUnn (by exact_mod_cast hd1)
    have hb := hmain (z i) hz (L / d i) (U / d i)
      (Nat.div_pos hdL hd0) (hcast.trans (hUd.trans hU))
    calc |∑ n ∈ Finset.Ioc (L / d i) (U / d i),
          (Task308.roughIndicator n (z i) -
            ω (Real.log (n : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ))|
        ≤ C * ((U / d i : ℕ) : ℝ) * E := hb
      _ ≤ C * ((U : ℝ) / (d i : ℝ)) * E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcast hC) hE
      _ = C * U * E * ((1 : ℝ) / (d i : ℝ)) := by ring
  have hK : 0 ≤ C * U * E := mul_nonneg (mul_nonneg hC hUnn) hE
  calc |∑ i ∈ I, ∑ m ∈ Finset.Ioc L U, (if d i ∣ m then
        Task308.roughIndicator (m / d i) (z i) -
          ω (Real.log ((m / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)
        else 0)|
      ≤ ∑ i ∈ I, C * U * E * ((1 : ℝ) / (d i : ℝ)) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = C * U * E * ∑ i ∈ I, (1 : ℝ) / (d i : ℝ) := by rw [Finset.mul_sum]
    _ ≤ C * U * E * M := mul_le_mul_of_nonneg_left hM hK
    _ = C * M * U * E := by ring

/-- `T0 = exp((log x)^(1/3))` written as a cube root: `T0 ^ k = exp(k l)` with `l ^ 3 = log x`. -/
theorem perronT0_pow (x : ℝ) (k : ℕ) :
    perronT0 x ^ k = Real.exp (k * Real.log x ^ (1 / 3 : ℝ)) := by
  rw [perronT0, ← Real.exp_nat_mul]

/-- Page 51 display 5.17, the log powers of the outer reciprocal sums are below `T0 ^ 5`:
`L ^ 4 ≤ 512 T0 ^ 5` once `0 ≤ L ≤ 4 log x`, from `l ^ 12 ≤ 12! / 5 ^ 12 · exp(5 l)`. -/
theorem pow_four_le_perronT0 {x L : ℝ} (hx : 1 ≤ x) (hL0 : 0 ≤ L) (hL : L ≤ 4 * Real.log x) :
    L ^ 4 ≤ 512 * perronT0 x ^ 5 := by
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  set l := Real.log x ^ (1 / 3 : ℝ) with hl
  have hl0 : 0 ≤ l := Real.rpow_nonneg hlx _
  have hl3 : l ^ 3 = Real.log x := by
    rw [hl, ← Real.rpow_natCast, ← Real.rpow_mul hlx]
    norm_num
  have h1 : L ^ 4 ≤ (4 * l ^ 3) ^ 4 := pow_le_pow_left₀ hL0 (hl3 ▸ hL) 4
  have h2 := Real.pow_div_factorial_le_exp (5 * l) (by positivity) 12
  rw [perronT0_pow]
  push_cast
  have hfac : ((Nat.factorial 12 : ℕ) : ℝ) = 479001600 := by norm_num [Nat.factorial]
  rw [hfac, mul_pow] at h2
  have h3 : (4 * l ^ 3) ^ 4 = 256 * l ^ 12 := by ring
  have hl12 : 0 ≤ l ^ 12 := by positivity
  nlinarith

/-- Page 51 display 5.17: the strong prime number theorem error at a scale `X` with
`log X ≥ log x / 8` is below `T0 ^ (-10)`, for `N = 20`. -/
theorem exp_decay_le_perronT0 {x X : ℝ} (hx : 1 ≤ x) (hX : Real.log x / 8 ≤ Real.log X) :
    Real.exp (-20 * Real.log X ^ (1 / 3 : ℝ)) ≤ (perronT0 x ^ 10)⁻¹ := by
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  set l := Real.log x ^ (1 / 3 : ℝ) with hl
  have hl0 : 0 ≤ l := Real.rpow_nonneg hlx _
  have hl3 : l ^ 3 = Real.log x := by
    rw [hl, ← Real.rpow_natCast, ← Real.rpow_mul hlx]
    norm_num
  have hcube : (l / 2) ^ 3 ≤ Real.log X := by
    have : (l / 2) ^ 3 = Real.log x / 8 := by rw [div_pow, hl3]; norm_num
    rw [this]; exact hX
  have hroot : l / 2 ≤ Real.log X ^ (1 / 3 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) hcube (show (0 : ℝ) ≤ 1 / 3 by norm_num)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by
      norm_num, Real.rpow_one] at h
  rw [perronT0_pow, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  push_cast
  linarith

/-- Page 51 display 5.17, the arithmetic of the final bound: the rough error summed over the
outer primes, `C0 M b E`, with `M ≤ 512 T0 ^ 5`, `b ≤ 2 Y` and `E ≤ T0 ^ (-10)`, is at most
`1024 C0 Y T0 ^ (-5)`. -/
theorem window_error_arith {C0 M b E Y T : ℝ} (hC0 : 0 ≤ C0) (hM0 : 0 ≤ M) (hb0 : 0 ≤ b)
    (hE0 : 0 ≤ E) (hT : 0 < T) (hM : M ≤ 512 * T ^ 5) (hb : b ≤ 2 * Y)
    (hE : E ≤ (T ^ 10)⁻¹) :
    C0 * M * b * E ≤ 1024 * C0 * Y * (T ^ 5)⁻¹ := by
  have hT5 : 0 < T ^ 5 := pow_pos hT 5
  have hY0 : 0 ≤ Y := by linarith
  calc C0 * M * b * E ≤ C0 * (512 * T ^ 5) * (2 * Y) * (T ^ 10)⁻¹ :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hM hC0) hb hb0
          (mul_nonneg hC0 (by positivity))) hE hE0
          (mul_nonneg (mul_nonneg hC0 (by positivity)) (by linarith))
    _ = 1024 * C0 * Y * (T ^ 5)⁻¹ := by
        rw [show T ^ 10 = T ^ 5 * T ^ 5 by ring]
        field_simp
        ring

/-- Page 3 and page 51: the sizes of `Y = x ^ (11/20 + ε)` used in the assembly, for large `x`. -/
theorem window_scale_facts {ε x C0 : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hx36 : (2 : ℝ) ^ 36 ≤ x) (hxC : C0 ^ 2 ≤ x) :
    (4 : ℝ) ^ 9 ≤ x ^ (11 / 20 + ε) ∧ C0 ≤ x ^ (11 / 20 + ε) ∧
      Real.log x / 8 ≤ Real.log (2 * x ^ (11 / 20 + ε)) ∧
      1 ≤ Real.log (2 * x ^ (11 / 20 + ε)) ∧
      2 * Real.log (2 * x ^ (11 / 20 + ε)) ≤ 4 * Real.log x := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx36
  have hx2 : (2 : ℝ) ≤ x := le_trans (by norm_num) hx36
  have hxpos : 0 < x := by linarith
  have hY49 : (4 : ℝ) ^ 9 ≤ x ^ (11 / 20 + ε) := by
    refine Decomp514a.shortY_ge_of_sq_le hε hx1 ?_
    have h49 : ((4 : ℝ) ^ 9) ^ 2 = (2 : ℝ) ^ 36 := by norm_num
    rw [h49]
    exact hx36
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY49
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlogY : Real.log (x ^ (11 / 20 + ε)) = (11 / 20 + ε) * Real.log x :=
    Real.log_rpow hxpos _
  have hl2Y : Real.log (x ^ (11 / 20 + ε)) ≤ Real.log (2 * x ^ (11 / 20 + ε)) :=
    Real.log_le_log hYpos (by linarith)
  have hYx : x ^ (11 / 20 + ε) ≤ x := by
    calc x ^ (11 / 20 + ε) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num at hε8 ⊢; linarith)
      _ = x := Real.rpow_one x
  refine ⟨hY49, Decomp514a.shortY_ge_of_sq_le hε hx1 hxC, ?_, ?_, ?_⟩
  · rw [hlogY] at hl2Y
    nlinarith
  · rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    nlinarith
  · have h1 : Real.log (2 * x ^ (11 / 20 + ε)) ≤ Real.log (x ^ 2) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith

/-- PROVED from the three leaves of this file: page 51 display 5.17, the E2 term, with exactly
the statement of `DQ517Window.leaf_two_window`. The E2 sum is the family sum over prime pairs,
`Decomp514a.lowerTwoTerms_eq_family`; the rough cofactor is replaced by its Buchstab density by
`leaf_rough_window_density` at the scale `2 Y` with `N = 20`, summed over the pairs with
`Decomp514a.pair_reciprocal_sum_le`; the rest is `leaf_two_main_window`. -/
theorem two_window_of_leaves (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ a b : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ ≤ a →
      b ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc a b, (lowerTwoTerms ε x m -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by
  obtain ⟨C0, hC0, hbb⟩ := leaf_rough_window_density ω hω hz (c := 1 / 10) (by norm_num)
    20 (by norm_num)
  obtain ⟨C1, hmainleaf⟩ := leaf_two_main_window ω hω hz hε hε8
  refine ⟨max (1024 * C0 + C1) (max ((2 : ℝ) ^ 36) (max (C0 ^ 2) C1)), ?_⟩
  intro x hx a b ha hb
  have hCm : 1024 * C0 + C1 ≤ max (1024 * C0 + C1) (max ((2 : ℝ) ^ 36) (max (C0 ^ 2) C1)) :=
    le_max_left _ _
  have hx36 : (2 : ℝ) ^ 36 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxC : C0 ^ 2 ≤ x :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hx
  have hxC1 : C1 ≤ x :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx36
  obtain ⟨hY49, hYC, hlog8, hL1, hL4⟩ := window_scale_facts hε hε8 hx36 hxC
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY49
  have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    Nat.floor_le (by linarith)
  have hN1 : 1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ :=
    Nat.le_floor (by rw [Nat.cast_one]; linarith)
  have hbR : (b : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := (Nat.cast_le.mpr hb).trans hNle
  have hsp := family_density_split
    (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
        (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
        i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
          lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)))
    (Finset.Ioc a b)
    (lowerTwoTerms ε x)
    (fun m : ℕ => lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x))
    (fun (i : ℕ × ℕ) (m : ℕ) => Task308.roughIndicator (m / (i.1 * i.2)) i.2)
    (fun (i : ℕ × ℕ) (m : ℕ) =>
      ω (Real.log ((m / (i.1 * i.2) : ℕ) : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ))
    (fun (i : ℕ × ℕ) (m : ℕ) => i.1 * i.2 ∣ m)
    (fun m hm => by
      have hm' := Finset.mem_Ioc.mp hm
      exact Decomp514a.lowerTwoTerms_eq_family ε x (by omega) (hm'.2.trans hb))
  have h1 := rough_family_window_sum ω hC0.le (Real.exp_pos _).le
    (hbb (2 * x ^ (11 / 20 + ε)) (by linarith))
    (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
        (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
        i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
          lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)))
    (fun i : ℕ × ℕ => i.1 * i.2) (fun i : ℕ × ℕ => i.2)
    a b ((2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 2)
    (by
      intro i hi
      obtain ⟨-, hp1, hp2, -, hdisc⟩ := Finset.mem_filter.mp hi
      obtain ⟨hb1, hb2⟩ := Decomp514a.lowerTwo_outer_bounds hε8 hY49 hp1 hp2 hdisc
      exact ⟨Nat.mul_pos hp1.pos hp2.pos, hb1.trans ha, hb2⟩)
    hbR
    (by
      refine le_trans (Decomp514a.pair_reciprocal_sum_le ⌊2 * x ^ (11 / 20 + ε)⌋₊ _
        (Finset.filter_subset _ _)) ?_
      have hNR : (1 : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by exact_mod_cast hN1
      have hlogN0 : 0 ≤ Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := Real.log_nonneg hNR
      have hlogN : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤
          Real.log (2 * x ^ (11 / 20 + ε)) := Real.log_le_log (by linarith) hNle
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2)
  have h2 := hmainleaf x hxC1 a b ha hb
  have hM : (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 2 ≤ 512 * perronT0 x ^ 5 :=
    (pow_le_pow_right₀ (by linarith) (by norm_num : 2 ≤ 4)).trans
      (pow_four_le_perronT0 hx1 (by linarith) hL4)
  have h3 := window_error_arith hC0.le (sq_nonneg _) (Nat.cast_nonneg b) (Real.exp_pos _).le
    (Real.exp_pos _) hM hbR (exp_decay_le_perronT0 hx1 hlog8)
  refine (congrArg abs hsp).le.trans ((abs_add_le _ _).trans
    ((add_le_add (h1.trans h3) h2).trans ?_))
  have hT : 0 ≤ (perronT0 x ^ 5)⁻¹ := inv_nonneg.mpr (pow_nonneg (Real.exp_pos _).le 5)
  calc 1024 * C0 * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ +
        C1 * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹
      = (1024 * C0 + C1) * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) := by ring
    _ ≤ max (1024 * C0 + C1) (max ((2 : ℝ) ^ 36) (max (C0 ^ 2) C1)) *
          (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) :=
        mul_le_mul_of_nonneg_right hCm (mul_nonneg hYpos.le hT)
    _ = _ := by ring

/-- PROVED from the three leaves of this file: page 51 display 5.17, the E4 term, with exactly
the statement of `DQ517Window.leaf_four_window`. The E4 sum is the family sum over prime
quadruples, `Decomp514a.four_terms_eq_family`; the rough cofactor is replaced by its Buchstab
density by `leaf_rough_window_density` at the scale `2 Y` with `N = 20`, summed over the
quadruples with `Decomp514a.four_reciprocal_sum_le`; the rest is `leaf_four_main_window`. -/
theorem four_window_of_leaves (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ a b : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ ≤ a →
      b ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc a b, (lowerFourTerms ε x m -
          lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by
  obtain ⟨C0, hC0, hbb⟩ := leaf_rough_window_density ω hω hz (c := 1 / 10) (by norm_num)
    20 (by norm_num)
  obtain ⟨C1, hmainleaf⟩ := leaf_four_main_window ω hω hz hε hε8
  refine ⟨max (1024 * C0 + C1) (max ((2 : ℝ) ^ 36) (max (C0 ^ 2) C1)), ?_⟩
  intro x hx a b ha hb
  have hCm : 1024 * C0 + C1 ≤ max (1024 * C0 + C1) (max ((2 : ℝ) ^ 36) (max (C0 ^ 2) C1)) :=
    le_max_left _ _
  have hx36 : (2 : ℝ) ^ 36 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxC : C0 ^ 2 ≤ x :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hx
  have hxC1 : C1 ≤ x :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx36
  obtain ⟨hY49, hYC, hlog8, hL1, hL4⟩ := window_scale_facts hε hε8 hx36 hxC
  have hY43 : (4 : ℝ) ^ 3 ≤ x ^ (11 / 20 + ε) := le_trans (by norm_num) hY49
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY49
  have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    Nat.floor_le (by linarith)
  have hN1 : 1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ :=
    Nat.le_floor (by rw [Nat.cast_one]; linarith)
  have hbR : (b : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := (Nat.cast_le.mpr hb).trans hNle
  have hsp := family_density_split
    (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
        (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
        (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
        (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
        i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
          i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
          lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
            (expo ε x i.2.2.2)))
    (Finset.Ioc a b)
    (lowerFourTerms ε x)
    (fun m : ℕ => lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x))
    (fun (i : ℕ × ℕ × ℕ × ℕ) (m : ℕ) =>
      Task308.roughIndicator (m / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2)) i.2.2.2)
    (fun (i : ℕ × ℕ × ℕ × ℕ) (m : ℕ) =>
      ω (Real.log ((m / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2) : ℕ) : ℝ) /
          Real.log (i.2.2.2 : ℝ)) / Real.log (i.2.2.2 : ℝ))
    (fun (i : ℕ × ℕ × ℕ × ℕ) (m : ℕ) => i.1 * i.2.1 * i.2.2.1 * i.2.2.2 ∣ m)
    (fun m hm => by
      have hm' := Finset.mem_Ioc.mp hm
      exact Decomp514a.four_terms_eq_family ε x (by omega) (hm'.2.trans hb))
  have h1 := rough_family_window_sum ω hC0.le (Real.exp_pos _).le
    (hbb (2 * x ^ (11 / 20 + ε)) (by linarith))
    (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
        (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
        (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
        (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
        i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
          i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
          lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
            (expo ε x i.2.2.2)))
    (fun i : ℕ × ℕ × ℕ × ℕ => i.1 * i.2.1 * i.2.2.1 * i.2.2.2)
    (fun i : ℕ × ℕ × ℕ × ℕ => i.2.2.2)
    a b ((2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 4)
    (by
      intro i hi
      obtain ⟨-, hp1, hp2, hp3, hp4, -, -, -, hreg⟩ := Finset.mem_filter.mp hi
      obtain ⟨hb1, hb2⟩ := Decomp514a.four_outer_bounds hε hε8 hY43 hp1 hp2 hp3 hp4 hreg
      exact ⟨Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp1.pos hp2.pos) hp3.pos) hp4.pos,
        hb1.trans ha, hb2⟩)
    hbR
    (by
      refine le_trans (Decomp514a.four_reciprocal_sum_le ⌊2 * x ^ (11 / 20 + ε)⌋₊ _
        (Finset.filter_subset _ _)) ?_
      have hNR : (1 : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by exact_mod_cast hN1
      have hlogN0 : 0 ≤ Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := Real.log_nonneg hNR
      have hlogN : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤
          Real.log (2 * x ^ (11 / 20 + ε)) := Real.log_le_log (by linarith) hNle
      exact pow_le_pow_left₀ (by linarith) (by linarith) 4)
  have h2 := hmainleaf x hxC1 a b ha hb
  have hM : (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 4 ≤ 512 * perronT0 x ^ 5 :=
    pow_four_le_perronT0 hx1 (by linarith) hL4
  have h3 := window_error_arith hC0.le (by positivity) (Nat.cast_nonneg b) (Real.exp_pos _).le
    (Real.exp_pos _) hM hbR (exp_decay_le_perronT0 hx1 hlog8)
  refine (congrArg abs hsp).le.trans ((abs_add_le _ _).trans
    ((add_le_add (h1.trans h3) h2).trans ?_))
  have hT : 0 ≤ (perronT0 x ^ 5)⁻¹ := inv_nonneg.mpr (pow_nonneg (Real.exp_pos _).le 5)
  calc 1024 * C0 * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ +
        C1 * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹
      = (1024 * C0 + C1) * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) := by ring
    _ ≤ max (1024 * C0 + C1) (max ((2 : ℝ) ^ 36) (max (C0 ^ 2) C1)) *
          (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) :=
        mul_le_mul_of_nonneg_right hCm (mul_nonneg hYpos.le hT)
    _ = _ := by ring

end LeanLab.BHP1997.DQ517Window
