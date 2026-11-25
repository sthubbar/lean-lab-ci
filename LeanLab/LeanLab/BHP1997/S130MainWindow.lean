/-
Session S130, burst 2026-11-22: the two main window leaves of `DQ517WindowLeaves`,
`leaf_two_main_window` and `leaf_four_main_window`, split once along the paper.
Source: P0069 Baker Harman Pintz 1997, page 51, display 5.17: "a straightforward consequence of
the prime number theorem, with error term `Y exp(-ε L^(1/2))`".

The log power forms of these statements are PROVED in the lab: `LowerShortC165.two_density_main`
of `TwoDensityMain517.lean` and `LowerShortC165.four_density_main` of `FourDensityMain517.lean`.
This file follows exactly the same route, with every error `log^(-A) x` replaced by the error
`T0 ^ (-5)` of 5.17, `T0 = exp(L^(1/3))`:
* a window `(a, b]` of J is the difference of two prefixes `(⌊Y⌋, b]` and `(⌊Y⌋, a]`,
  `window_of_prefix`, PROVED;
* the sum over `m` and over the outer primes is interchanged and the multiples are reindexed by
  the cofactor, `two_density_swap_combine` and `four_density_swap_combine`, already PROVED;
* the cofactor comparison, no prime number theorem, saves a power of `Y`:
  `two_cofactor_strong`, `four_cofactor_strong`, PROVED here as in `two_cofactor_riemann` and
  `four_cofactor_riemann`, with `log_pow_T0_le`;
* the pointwise density in `m`: the assemblies of `two_pair_density_pointwise` and
  `four_quad_density_pointwise` are redone, `two_pointwise_strong` and
  `four_pointwise_strong`, PROVED from the LEAF pieces with error `T0 ^ (-5)`:
  for E2 the two prime number theorem steps `leaf_two_first_prime_strong`,
  `leaf_two_second_prime_strong`, HARD, and the Riemann sum `leaf_two_riemann_strong`, MEDIUM;
  for E4 the four partial summations `leaf_four_transfer_p1_strong` to
  `leaf_four_transfer_p4_strong`, HARD, and the Riemann sum
  `leaf_four_integer_riemann_strong`, MEDIUM. Their log power forms are all PROVED in the lab;
  the prime number theorem input with error `exp(-c L^(1/2))` is
  `LeanLab.PNTPort.psi_explicit_strong`, and the Riemann sums save a power of `Y`.

PROVED from the pieces: `two_main_window_of_s130` and `four_main_window_of_s130`, verbatim the
statements of `DQ517Window.leaf_two_main_window` and `DQ517Window.leaf_four_main_window`.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.TwoDensityMain517
import LeanLab.BHP1997.FourDensityMain517
import LeanLab.BHP1997.DQLowerExceptionalMeanSquareDecisions

namespace LeanLab.BHP1997.S130MainWindow
open Classical Complex Decomp132 DecompC165b DecompC165d LowerShortC165 Decomp514a
open LeanLab.BHP1997.DQLowerExceptionalMeanSquare
open scoped BigOperators

/-- Page 51 display 5.17, the window form: a sum over a window `(a, b]` of J is the difference
of two sums over prefixes of J, so a bound `B` on every prefix gives `2 B` on every window. -/
theorem window_of_prefix (f : ℕ → ℝ) {L0 N : ℕ} {B : ℝ}
    (hpre : ∀ U : ℕ, U ≤ N → |∑ m ∈ Finset.Ioc L0 U, f m| ≤ B) {a b : ℕ}
    (ha : L0 ≤ a) (hb : b ≤ N) :
    |∑ m ∈ Finset.Ioc a b, f m| ≤ 2 * B := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hpre N le_rfl)
  rcases le_or_gt a b with hab | hab
  · have h := Finset.sum_Ioc_consecutive f ha hab
    have e : ∑ m ∈ Finset.Ioc a b, f m =
        ∑ m ∈ Finset.Ioc L0 b, f m - ∑ m ∈ Finset.Ioc L0 a, f m := by linarith
    rw [e]
    have h1 := hpre b hb
    have h2 := hpre a (hab.trans hb)
    calc _ ≤ |∑ m ∈ Finset.Ioc L0 b, f m| + |∑ m ∈ Finset.Ioc L0 a, f m| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  · rw [Finset.Ioc_eq_empty_of_le hab.le, Finset.sum_empty, abs_zero]
    linarith

/-! ### E2 -/

/-- Page 51 display 5.17, sizes: `log^k x · T0^5 ≤ x ^ (11/200)` for large `x`, since
`T0 = exp(L^(1/3))` is below every power of `x`. -/
theorem log_pow_T0_le (k : ℕ) : ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
    Real.log x ^ k * perronT0 x ^ 5 ≤ x ^ (11 / 200 : ℝ) := by
  have h1 := (isLittleO_log_rpow_rpow_atTop (k : ℝ) (by norm_num : (0 : ℝ) < 11 / 400)).bound
    (by norm_num : (0 : ℝ) < 1)
  have h2 := eventually_T0_le_power521 (α := 11 / 2000) (by norm_num)
  obtain ⟨C, hC⟩ := Filter.eventually_atTop.mp
    (h1.and (h2.and (Filter.eventually_gt_atTop (1 : ℝ))))
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨a, b, c⟩ := hC x hx
  have hl : 0 < Real.log x := Real.log_pos c
  have hx0 : 0 < x := by linarith
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at a
  have e3 : Real.log x ^ (k : ℝ) = Real.log x ^ k := Real.rpow_natCast _ _
  rw [e3] at a
  have hT5 : perronT0 x ^ 5 ≤ (x ^ (11 / 2000 : ℝ)) ^ 5 :=
    pow_le_pow_left₀ (perronT0_pos x).le b 5
  have e5 : (x ^ (11 / 2000 : ℝ)) ^ 5 = x ^ (11 / 400 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have e : x ^ (11 / 200 : ℝ) = x ^ (11 / 400 : ℝ) * x ^ (11 / 400 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  rw [e]
  exact mul_le_mul a (hT5.trans e5.le) (pow_nonneg (perronT0_pos x).le 5) (Real.rpow_nonneg hx0.le _)

/-- PROVED: page 51 display 5.17, the cofactor variable `n3` of the E2 sum of display 5.15,
with the error of 5.17. No prime number theorem: for each prime pair the cofactor sum of the
Buchstab density over `n` in `(Y / (p1 p2), U / (p1 p2)]` is the average over `m` in `(Y, U]`
of the density at `m / (p1 p2)`. The proof of `LowerShortC165.two_cofactor_riemann` bounds the
total error by `576 Y log^3 x / (2 Y)^(1/10)`, a power of `Y` saved, below `Y T0^(-5)` by
`log_pow_T0_le`; the proof is that proof with the last comparison changed. -/
theorem two_cofactor_strong (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ U : ℕ, U ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
            i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
              lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
          ((∑ n ∈ Finset.Ioc (⌊x ^ (11 / 20 + ε)⌋₊ / (i.1 * i.2)) (U / (i.1 * i.2)),
              ω (Real.log (n : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ)) -
            ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ U,
              ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ))) / Real.log (i.2 : ℝ)) /
                Real.log (i.2 : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ)))| ≤
        C * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by
  obtain ⟨C1, hC1⟩ := log_pow_T0_le 3
  refine ⟨max (max 576 C1) ((2 : ℝ) ^ 36), fun x hx U hU => ?_⟩
  have hC576 : (576 : ℝ) ≤ max (max 576 C1) ((2 : ℝ) ^ 36) :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hxC1 : C1 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx36 : (2 : ℝ) ^ 36 ≤ x := (le_max_right _ _).trans hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx36
  have hxpos : 0 < x := by linarith
  have hY49 : (4 : ℝ) ^ 9 ≤ x ^ (11 / 20 + ε) := by
    refine shortY_ge_of_sq_le hε hx1 ?_
    have h49 : ((4 : ℝ) ^ 9) ^ 2 = (2 : ℝ) ^ 36 := by norm_num
    rw [h49]
    exact hx36
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY49
  have hY1 : (1 : ℝ) ≤ x ^ (11 / 20 + ε) := le_trans (by norm_num) hY49
  have hl1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hxpos]
    have h1 := Real.exp_one_lt_d9
    have h2 : (3 : ℝ) ≤ 2 ^ 36 := by norm_num
    linarith
  have hlam0 : 0 < Real.log x := by linarith
  obtain ⟨-, hlX2⟩ := log_scale_bounds hε hε8 hxpos hl1
  have hl0 : 0 ≤ Real.log (2 * x ^ (11 / 20 + ε)) := Real.log_nonneg (by linarith)
  have hW : 0 < (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    Nat.floor_le (by linarith)
  have hN1 : 1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ :=
    Nat.le_floor (by rw [Nat.cast_one]; linarith)
  have hU' : (U : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := (Nat.cast_le.mpr hU).trans hNle
  have hlogN : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ Real.log (2 * x ^ (11 / 20 + ε)) :=
    Real.log_le_log (by exact_mod_cast hN1) hNle
  have hlogN0 : 0 ≤ Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := Real.log_natCast_nonneg _
  have hR0 : 0 ≤ 8 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + 8 := by linarith
  have hT0 : 0 ≤ 2 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) :=
    div_nonneg (by linarith) hW.le
  have hRT : 0 ≤ (8 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + 8) *
      (2 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) := mul_nonneg hR0 hT0
  refine (two_cofactor_sum_bound (Finset.filter_subset _ _) _ hRT (fun i hi => ?_)).trans ?_
  · obtain ⟨hp1, hp2, -, hE⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨-, hWp⟩ := lowerTwo_outer_bounds hε8 hY49 hp1 hp2 hE
    exact two_cofactor_pair_term ω hω hz _ hp1 hp2 hW hWp hU' (by linarith)
  -- the final comparison of sizes
  have ha : 8 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + 8 ≤ 32 * Real.log x := by linarith
  have hb : (1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ)) ^ 2 ≤ 9 * Real.log x ^ 2 := by
    have h1 : 1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 3 * Real.log x := by linarith
    have h2 := pow_le_pow_left₀ (by linarith) h1 2
    have h3 : (3 * Real.log x) ^ 2 = 9 * Real.log x ^ 2 := by ring
    linarith
  have hprod : (8 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + 8) *
      (2 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) *
      (1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ)) ^ 2 ≤
      32 * Real.log x * (2 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) *
        (9 * Real.log x ^ 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_right ha hT0) hb (sq_nonneg _)
      (mul_nonneg (by linarith) hT0)
  have hWge : x ^ (11 / 200 : ℝ) ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) := by
    have h1 : x ^ (11 / 20 : ℝ) ≤ x ^ (11 / 20 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    calc x ^ (11 / 200 : ℝ) = (x ^ (11 / 20 : ℝ)) ^ (1 / 10 : ℝ) := by
          rw [← Real.rpow_mul (by linarith)]; norm_num
      _ ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hxpos.le _) (by linarith) (by norm_num)
  have hT5 : 0 < perronT0 x ^ 5 := pow_pos (perronT0_pos x) 5
  have hsmall : Real.log x ^ 3 / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) ≤
      (perronT0 x ^ 5)⁻¹ := by
    rw [div_le_iff₀ hW]
    have h4 : Real.log x ^ 3 * perronT0 x ^ 5 ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) :=
      (hC1 x hxC1).trans hWge
    calc Real.log x ^ 3 = (perronT0 x ^ 5)⁻¹ * (Real.log x ^ 3 * perronT0 x ^ 5) := by
          rw [mul_comm (Real.log x ^ 3), ← mul_assoc, inv_mul_cancel₀ hT5.ne', one_mul]
      _ ≤ (perronT0 x ^ 5)⁻¹ * (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) :=
          mul_le_mul_of_nonneg_left h4 (inv_nonneg.mpr hT5.le)
  have hL : 0 ≤ (perronT0 x ^ 5)⁻¹ := inv_nonneg.mpr hT5.le
  calc (8 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + 8) *
        (2 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) *
        (1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ)) ^ 2
      ≤ 32 * Real.log x * (2 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) *
        (9 * Real.log x ^ 2) := hprod
    _ = 576 * x ^ (11 / 20 + ε) *
        (Real.log x ^ 3 / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) := by ring
    _ ≤ 576 * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ :=
        mul_le_mul_of_nonneg_left hsmall (by linarith)
    _ ≤ max (max 576 C1) ((2 : ℝ) ^ 36) * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC576 hYpos.le) hL

/-- LEAF: page 51 display 5.17, the prime number theorem with error `exp(-ε L^(1/2))` for the
first outer prime `p1` of the E2 sum of display 5.15 at one point `m` of J. HARD. For each
prime `p2 = b` the sum over the primes `p1 = a > b` of the E2 weight is replaced by the sum over
the integers `a > b` with density `1 / log a`, error `T0^(-5)` after summing over `b`. Strong
error form of `LowerShortC165.two_pair_first_prime`. -/
theorem leaf_two_first_prime_strong (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, primeWeight b *
          ∑ a ∈ Finset.Ioc b ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            (primeWeight a - 1 / Real.log (a : ℝ)) *
              (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0)| ≤ C * (perronT0 x ^ 5)⁻¹ := by
  sorry

/-- LEAF: page 51 display 5.17, the prime number theorem with error `exp(-ε L^(1/2))` for the
second outer prime `p2` of the E2 sum of display 5.15 at one point `m` of J. HARD. For each
integer `a` the sum over the primes `p2 = b < a` of the E2 weight is replaced by the sum over
the integers `b < a` with density `1 / log b`, error `T0^(-5)` after summing over `a`. Strong
error form of `LowerShortC165.two_pair_second_prime`. -/
theorem leaf_two_second_prime_strong (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ a ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, 1 / Real.log (a : ℝ) *
          ∑ b ∈ Finset.Ico 1 a,
            (primeWeight b - 1 / Real.log (b : ℝ)) *
              (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0)| ≤ C * (perronT0 x ^ 5)⁻¹ := by
  sorry

/-- LEAF: page 51 display 5.17, the E2 sum of display 5.15 at one point `m` of J, the passage
from the sum over integer pairs to the E2 integral of page 51 with `1` replaced by
`s = log m / log Z`, error `T0^(-5)`. MEDIUM. No prime number theorem: a Riemann sum of a
function of bounded variation on cells of size `1 / (a log a)` with `a ≥ Y^(1/10)`, so a power
of `Y` is saved. Strong error form of `LowerShortC165.two_pair_riemann`. -/
theorem leaf_two_riemann_strong (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          ∑ a ∈ Finset.Ioc b ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log (b : ℝ)))) -
        lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x)| ≤ C * (perronT0 x ^ 5)⁻¹ := by
  sorry

/-- PROVED from the three pointwise E2 leaves, page 51 display 5.17 at one point `m` of J: the
strong error form of `LowerShortC165.two_pair_density_pointwise`, by the same assembly with
`two_pair_sum_iterated` and `two_pair_sum_split`. -/
theorem two_pointwise_strong (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
            i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
              lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
          ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ))) / Real.log (i.2 : ℝ)) /
            Real.log (i.2 : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ))) -
        lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x)| ≤ C * (perronT0 x ^ 5)⁻¹ := by
  obtain ⟨C1, hC1⟩ := leaf_two_first_prime_strong ω hω hz hε hε8
  obtain ⟨C2, hC2⟩ := leaf_two_second_prime_strong ω hω hz hε hε8
  obtain ⟨C3, hC3⟩ := leaf_two_riemann_strong ω hω hz hε hε8
  refine ⟨max (max C1 C2) (max C3 (|C1| + |C2| + |C3| + 1)), fun x hx m hm1 hm2 => ?_⟩
  have hx1 : C1 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx2 : C2 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx3 : C3 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hC : |C1| + |C2| + |C3| + 1 ≤ max (max C1 C2) (max C3 (|C1| + |C2| + |C3| + 1)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hL : 0 ≤ (perronT0 x ^ 5)⁻¹ := inv_nonneg.mpr (pow_nonneg (perronT0_pos x).le 5)
  have b1 := hC1 x hx1 m hm1 hm2
  have b2 := hC2 x hx2 m hm1 hm2
  have b3 := hC3 x hx3 m hm1 hm2
  have hiter := two_pair_sum_iterated ⌊2 * x ^ (11 / 20 + ε)⌋₊
    (fun a b => lowerTwoDiscarded ε (expo ε x a) (expo ε x b))
    (fun a b => ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
      Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ)))
  have hsplit := two_pair_sum_split ⌊2 * x ^ (11 / 20 + ε)⌋₊ primeWeight
    (fun n => 1 / Real.log (n : ℝ))
    (fun a b => if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
      ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
        Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ)) else 0)
  beta_reduce at hiter hsplit
  rw [hiter, hsplit]
  have a1 := abs_le.mp b1
  have a2 := abs_le.mp b2
  have a3 := abs_le.mp b3
  have k1 := mul_le_mul_of_nonneg_right (le_abs_self C1) hL
  have k2 := mul_le_mul_of_nonneg_right (le_abs_self C2) hL
  have k3 := mul_le_mul_of_nonneg_right (le_abs_self C3) hL
  have k4 := mul_le_mul_of_nonneg_right hC hL
  have k5 : (|C1| + |C2| + |C3| + 1) * (perronT0 x ^ 5)⁻¹ =
      |C1| * (perronT0 x ^ 5)⁻¹ + |C2| * (perronT0 x ^ 5)⁻¹ + |C3| * (perronT0 x ^ 5)⁻¹ +
        (perronT0 x ^ 5)⁻¹ := by ring
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]

/-- PROVED from the E2 pieces, page 51 display 5.17 on every prefix of J with the error
`Y T0^(-5)`: the assembly of `LowerShortC165.two_density_main` by
`two_density_swap_combine`. -/
theorem two_prefix_strong (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ U : ℕ, U ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ U,
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
  obtain ⟨CA, hCA⟩ := two_pointwise_strong ω hω hz hε hε8
  obtain ⟨CB, hCB⟩ := two_cofactor_strong ω hω hz hε hε8
  refine ⟨max (max CA CB) (|CB| + 2 * |CA| + 1), fun x hx U hU => ?_⟩
  have hxA : CA ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxB : CB ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hC3 : |CB| + 2 * |CA| + 1 ≤ max (max CA CB) (|CB| + 2 * |CA| + 1) := le_max_right _ _
  have hx1 : (1 : ℝ) ≤ x := by
    have h1 := abs_nonneg CA
    have h2 := abs_nonneg CB
    linarith
  have hYpos : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hL : 0 ≤ (perronT0 x ^ 5)⁻¹ := inv_nonneg.mpr (pow_nonneg (perronT0_pos x).le 5)
  have hYL : 0 ≤ x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := mul_nonneg hYpos.le hL
  have hU' : (U : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    (Nat.cast_le.mpr hU).trans (Nat.floor_le (by positivity))
  have hB' := hCB x hxB U hU
  have hmain := two_density_swap_combine
    (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
      (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
      i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
        lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)))
    (fun i : ℕ × ℕ => i.1 * i.2)
    (fun i hi => by
      have hi' := (Finset.mem_filter.mp hi).2
      exact Nat.mul_pos hi'.1.pos hi'.2.1.pos)
    (fun (i : ℕ × ℕ) (n : ℕ) =>
      ω (Real.log (n : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ))
    (fun (i : ℕ × ℕ) (m : ℕ) =>
      ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ))) / Real.log (i.2 : ℝ)) /
        Real.log (i.2 : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ)))
    (fun m : ℕ => lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
      Real.log (scaleZ ε x))
    ⌊x ^ (11 / 20 + ε)⌋₊ U (|CA| * (perronT0 x ^ 5)⁻¹)
    (CB * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹)
    (mul_nonneg (abs_nonneg CA) hL) hB'
    (fun m hm => by
      have hm' := Finset.mem_Ioc.mp hm
      exact (hCA x hxA m hm'.1 (hm'.2.trans hU)).trans
        (mul_le_mul_of_nonneg_right (le_abs_self CA) hL))
  refine hmain.trans ?_
  have h1 : CB * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ ≤
      |CB| * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self CB) hYL
  have h2 : (U : ℝ) * (|CA| * (perronT0 x ^ 5)⁻¹) ≤
      2 * |CA| * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) :=
    calc (U : ℝ) * (|CA| * (perronT0 x ^ 5)⁻¹)
        ≤ 2 * x ^ (11 / 20 + ε) * (|CA| * (perronT0 x ^ 5)⁻¹) :=
          mul_le_mul_of_nonneg_right hU' (mul_nonneg (abs_nonneg CA) hL)
      _ = 2 * |CA| * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) := by ring
  have h3 := mul_le_mul_of_nonneg_right hC3 hYL
  have h4 : (|CB| + 2 * |CA| + 1) * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) =
      |CB| * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) +
        2 * |CA| * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) +
        x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by ring
  have h5 : max (max CA CB) (|CB| + 2 * |CA| + 1) * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ =
      max (max CA CB) (|CB| + 2 * |CA| + 1) *
        (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) := by ring
  linarith

/-- PROVED from the E2 pieces of this file: verbatim the statement of
`DQ517Window.leaf_two_main_window`, page 51 display 5.17, by `two_prefix_strong` and
`window_of_prefix`. -/
theorem two_main_window_of_s130 (ω : ℝ → ℝ)
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
  obtain ⟨C, hC⟩ := two_prefix_strong ω hω hz hε hε8
  refine ⟨max C (2 * |C|), fun x hx a b ha hb => ?_⟩
  have hxC : C ≤ x := (le_max_left _ _).trans hx
  have hw := window_of_prefix _ (hC x hxC) ha hb
  refine hw.trans ?_
  have hL : 0 ≤ (perronT0 x ^ 5)⁻¹ := inv_nonneg.mpr (pow_nonneg (perronT0_pos x).le 5)
  have hYL : 0 ≤ x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ :=
    mul_nonneg (Real.rpow_nonneg (by
      have := abs_nonneg C
      have := le_max_right C (2 * |C|)
      linarith) _) hL
  calc 2 * (C * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹)
      = 2 * C * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) := by ring
    _ ≤ max C (2 * |C|) * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) :=
        mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_left (le_abs_self C) (by norm_num)).trans
            (le_max_right _ _)) hYL
    _ = _ := by ring

/-! ### E4 -/

/-- PROVED: page 51 display 5.17, the cofactor variable `n5` of the E4 sum reached from display
5.15, with the error of 5.17. No prime number theorem: for each prime quadruple the
cofactor sum of the Buchstab density over `n` in `(Y / (p1 p2 p3 p4), U / (p1 p2 p3 p4)]` is
the average over `m` in `(Y, U]` of the density at `m / (p1 p2 p3 p4)`. The proof of
`LowerShortC165.four_cofactor_riemann` costs `7 U / (p1 p2 p3 p4 ^ 2)` per quadruple with
`p4 ≥ (2 Y)^(1/10)`, a power of `Y` saved, below `Y T0^(-5)` by `log_pow_T0_le`; the
proof is that proof with the last comparison changed. -/
theorem four_cofactor_strong (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ U : ℕ, U ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
              i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
                i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
                lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                  (expo ε x i.2.2.2)),
          ((∑ n ∈ Finset.Ioc (⌊x ^ (11 / 20 + ε)⌋₊ / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2))
                (U / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2)),
              ω (Real.log (n : ℝ) / Real.log (i.2.2.2 : ℝ)) / Real.log (i.2.2.2 : ℝ)) -
            ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ U,
              ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
                  (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
                Real.log (i.2.2.2 : ℝ) /
                  ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ)))| ≤
        C * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by
  obtain ⟨C1, hC1⟩ := log_pow_T0_le 4
  refine ⟨max (max C1 ((2 : ℝ) ^ 12)) (max (Real.exp 2) 224), fun x hx U hU => ?_⟩
  have hxC1 : C1 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx12 : (2 : ℝ) ^ 12 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hxe : Real.exp 2 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hC224 : (224 : ℝ) ≤ max (max C1 ((2 : ℝ) ^ 12)) (max (Real.exp 2) 224) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx12
  have hxpos : 0 < x := by linarith
  have hY43 : (4 : ℝ) ^ 3 ≤ x ^ (11 / 20 + ε) := by
    refine Decomp514a.four_shortY_ge_of_sq_le hε hx1 ?_
    have h43 : ((4 : ℝ) ^ 3) ^ 2 = (2 : ℝ) ^ 12 := by norm_num
    rw [h43]
    exact hx12
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY43
  have hl2 : 2 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hxe
  have hlpos : 0 < Real.log x := by linarith
  have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    Nat.floor_le (by linarith)
  have hU' : (U : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := (Nat.cast_le.mpr hU).trans hNle
  have hN1 : (1 : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by
    have : 1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; linarith)
    exact_mod_cast this
  -- the level saving
  have hW : x ^ (11 / 200 : ℝ) ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) := by
    have hYge : x ^ (11 / 20 : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by
      have h := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : (11 / 20 : ℝ) ≤ 11 / 20 + ε)
      linarith
    calc x ^ (11 / 200 : ℝ) = (x ^ (11 / 20 : ℝ)) ^ (1 / 10 : ℝ) := by
          rw [← Real.rpow_mul hxpos.le]; norm_num
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hxpos.le _) hYge (by norm_num)
  have hL4 : 0 < Real.log x ^ (4 : ℕ) := pow_pos hlpos 4
  have hT5 : 0 < perronT0 x ^ 5 := pow_pos (perronT0_pos x) 5
  have hWlow : Real.log x ^ (4 : ℕ) * perronT0 x ^ 5 ≤
      (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) := (hC1 x hxC1).trans hW
  have hWpos : 0 < (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) :=
    lt_of_lt_of_le (mul_pos hL4 hT5) hWlow
  -- the reciprocal sum
  have hrec := Decomp514a.four_reciprocal_sum_le ⌊2 * x ^ (11 / 20 + ε)⌋₊
    (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
      (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
      (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
      (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
      i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
        i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
        lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
          (expo ε x i.2.2.2))) (Finset.filter_subset _ _)
  have hlogN : 1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * Real.log x := by
    have h1 : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ Real.log (2 * x ^ (11 / 20 + ε)) :=
      Real.log_le_log (by linarith) hNle
    rw [Real.log_mul (by norm_num) hYpos.ne', Real.log_rpow hxpos] at h1
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    have h3 : (11 / 20 + ε) * Real.log x ≤ 3 / 5 * Real.log x :=
      mul_le_mul_of_nonneg_right (by norm_num at hε8 ⊢; linarith) hlpos.le
    linarith
  have hlogN0 : 0 ≤ 1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by
    have := Real.log_nonneg hN1
    linarith
  have hrec2 := hrec.trans (pow_le_pow_left₀ hlogN0 hlogN 4)
  -- each quadruple
  have hterm : ∀ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
              i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
      |(∑ n ∈ Finset.Ioc (⌊x ^ (11 / 20 + ε)⌋₊ / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2))
                (U / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2)),
              ω (Real.log (n : ℝ) / Real.log (i.2.2.2 : ℝ)) / Real.log (i.2.2.2 : ℝ)) -
            ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ U,
              ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
                  (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
                Real.log (i.2.2.2 : ℝ) /
                  ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ))| ≤
        14 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) *
          (1 / ((i.1 * i.2.1 * i.2.2.1 * i.2.2.2 : ℕ) : ℝ)) := by
    intro i hi
    obtain ⟨-, hp1, hp2, hp3, hp4, -, -, -, hreg⟩ := Finset.mem_filter.mp hi
    obtain ⟨-, hb2⟩ := Decomp514a.four_outer_bounds hε hε8 hY43 hp1 hp2 hp3 hp4 hreg
    have hdpos : 1 ≤ i.1 * i.2.1 * i.2.2.1 * i.2.2.2 :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp1.pos hp2.pos) hp3.pos) hp4.pos
    have h := four_cofactor_block hω hz hdpos hp4.two_le ⌊x ^ (11 / 20 + ε)⌋₊ U
    simp only [Nat.cast_mul] at h ⊢
    refine h.trans ?_
    have hd0 : (0 : ℝ) < (i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ) := by
      have : (0 : ℝ) < ((i.1 * i.2.1 * i.2.2.1 * i.2.2.2 : ℕ) : ℝ) := by exact_mod_cast hdpos
      simpa only [Nat.cast_mul] using this
    have hp40 : (0 : ℝ) < (i.2.2.2 : ℝ) := by exact_mod_cast hp4.pos
    rw [div_le_iff₀ (mul_pos hd0 hp40)]
    have hWne := hWpos.ne'
    have hDne := hd0.ne'
    have e : 14 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) *
        (1 / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ))) *
        ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ) * (i.2.2.2 : ℝ)) =
        14 * x ^ (11 / 20 + ε) * ((i.2.2.2 : ℝ) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) := by
      have gen : ∀ K W D q : ℝ, W ≠ 0 → D ≠ 0 → K / W * (1 / D) * (D * q) = K * (q / W) := by
        intro K W D q hW hD
        field_simp
      exact gen _ _ _ _ hWne hDne
    rw [e]
    have h1 : (1 : ℝ) ≤ (i.2.2.2 : ℝ) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) := by
      rw [le_div_iff₀ hWpos, one_mul]
      exact hb2
    nlinarith
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.mul_sum]
  have hK0 : 0 ≤ 14 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) := by
    positivity
  refine (mul_le_mul_of_nonneg_left hrec2 hK0).trans ?_
  have hfin : 14 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) *
      (2 * Real.log x) ^ 4 ≤ 224 * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hWpos]
    have h1 : Real.log x ^ (4 : ℕ) ≤
        (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) * (perronT0 x ^ 5)⁻¹ := by
      calc Real.log x ^ (4 : ℕ) = (Real.log x ^ (4 : ℕ) * perronT0 x ^ 5) * (perronT0 x ^ 5)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hT5.ne', mul_one]
        _ ≤ _ := mul_le_mul_of_nonneg_right hWlow (inv_nonneg.mpr hT5.le)
    have e2 : 14 * x ^ (11 / 20 + ε) * (2 * Real.log x) ^ 4 =
        224 * x ^ (11 / 20 + ε) * Real.log x ^ (4 : ℕ) := by ring
    have e3 : 224 * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ *
        (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) = 224 * x ^ (11 / 20 + ε) *
        ((2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) * (perronT0 x ^ 5)⁻¹) := by ring
    rw [e2, e3]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  refine hfin.trans ?_
  have hLn : 0 ≤ (perronT0 x ^ 5)⁻¹ := inv_nonneg.mpr hT5.le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC224 hYpos.le) hLn

/-- LEAF: page 51 display 5.17, the prime number theorem with error `exp(-ε L^(1/2))`,
partial summation in the outer prime `p1` of the E4 sum at one point `m` of J, the other three outer
variables held fixed with arbitrary weights bounded by 2: replacing the prime indicator by the
density `1 / log n` changes the sum by `O(T0^(-5))`. HARD. Strong error form of
`LowerShortC165.four_transfer_p1`. -/
theorem leaf_four_transfer_p1_strong (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      ∀ a2 a3 a4 : ℕ → ℝ, (∀ n, |a2 n| ≤ 2) → (∀ n, |a3 n| ≤ 2) → (∀ n, |a4 n| ≤ 2) →
      |∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          (primeWeight i.1 - 1 / Real.log (i.1 : ℝ)) * a2 i.2.1 * a3 i.2.2.1 * a4 i.2.2.2 *
          (ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
              (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
            Real.log (i.2.2.2 : ℝ) /
              ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ)))| ≤ C * (perronT0 x ^ 5)⁻¹ := by
  sorry

/-- LEAF: page 51 display 5.17, the prime number theorem with error `exp(-ε L^(1/2))`,
partial summation in the outer prime `p2` of the E4 sum at one point `m` of J, the other three outer
variables held fixed with arbitrary weights bounded by 2: replacing the prime indicator by the
density `1 / log n` changes the sum by `O(T0^(-5))`. HARD. Strong error form of
`LowerShortC165.four_transfer_p2`. -/
theorem leaf_four_transfer_p2_strong (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      ∀ a1 a3 a4 : ℕ → ℝ, (∀ n, |a1 n| ≤ 2) → (∀ n, |a3 n| ≤ 2) → (∀ n, |a4 n| ≤ 2) →
      |∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          a1 i.1 * (primeWeight i.2.1 - 1 / Real.log (i.2.1 : ℝ)) * a3 i.2.2.1 * a4 i.2.2.2 *
          (ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
              (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
            Real.log (i.2.2.2 : ℝ) /
              ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ)))| ≤ C * (perronT0 x ^ 5)⁻¹ := by
  sorry

/-- LEAF: page 51 display 5.17, the prime number theorem with error `exp(-ε L^(1/2))`,
partial summation in the outer prime `p3` of the E4 sum at one point `m` of J, the other three outer
variables held fixed with arbitrary weights bounded by 2: replacing the prime indicator by the
density `1 / log n` changes the sum by `O(T0^(-5))`. HARD. Strong error form of
`LowerShortC165.four_transfer_p3`. -/
theorem leaf_four_transfer_p3_strong (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      ∀ a1 a2 a4 : ℕ → ℝ, (∀ n, |a1 n| ≤ 2) → (∀ n, |a2 n| ≤ 2) → (∀ n, |a4 n| ≤ 2) →
      |∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          a1 i.1 * a2 i.2.1 * (primeWeight i.2.2.1 - 1 / Real.log (i.2.2.1 : ℝ)) * a4 i.2.2.2 *
          (ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
              (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
            Real.log (i.2.2.2 : ℝ) /
              ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ)))| ≤ C * (perronT0 x ^ 5)⁻¹ := by
  sorry

/-- LEAF: page 51 display 5.17, the prime number theorem with error `exp(-ε L^(1/2))`,
partial summation in the outer prime `p4` of the E4 sum at one point `m` of J, the other three outer
variables held fixed with arbitrary weights bounded by 2: replacing the prime indicator by the
density `1 / log n` changes the sum by `O(T0^(-5))`. HARD. Strong error form of
`LowerShortC165.four_transfer_p4`. -/
theorem leaf_four_transfer_p4_strong (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      ∀ a1 a2 a3 : ℕ → ℝ, (∀ n, |a1 n| ≤ 2) → (∀ n, |a2 n| ≤ 2) → (∀ n, |a3 n| ≤ 2) →
      |∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          a1 i.1 * a2 i.2.1 * a3 i.2.2.1 * (primeWeight i.2.2.2 - 1 / Real.log (i.2.2.2 : ℝ)) *
          (ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
              (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
            Real.log (i.2.2.2 : ℝ) /
              ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ)))| ≤ C * (perronT0 x ^ 5)⁻¹ := by
  sorry

/-- LEAF: page 51 display 5.17, the E4 sum at one point `m` of J after the prime number
theorem in each outer variable: the sum over integer quadruples with exponents in E4, each
weighted by `1 / log n`, is `1 / log Z` times the E4 integral of page 51 with `1` replaced by
`s`, error `T0^(-5)`. MEDIUM. No prime number theorem: a Riemann sum on cells of size
`1 / (n log n)` with `n ≥ Y^(1/10)`, so a power of `Y` is saved. Strong error form of
`LowerShortC165.four_integer_riemann`. -/
theorem leaf_four_integer_riemann_strong (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          1 / Real.log (i.1 : ℝ) * (1 / Real.log (i.2.1 : ℝ)) * (1 / Real.log (i.2.2.1 : ℝ)) * (1 / Real.log (i.2.2.2 : ℝ)) *
          (ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
              (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
            Real.log (i.2.2.2 : ℝ) /
              ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ)))) -
        lowerFourDensityAt ω ε (Real.log (m : ℝ) / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x)| ≤ C * (perronT0 x ^ 5)⁻¹ := by
  sorry

/-- PROVED from the five pointwise E4 leaves above by the assembly of
`LowerShortC165.four_quad_density_pointwise`, `four_hybrid_telescope`.
Page 51 display 5.17, the prime number theorem with error `exp(-ε L^(1/2))` for the
outer primes `p1`, `p2`, `p3`, `p4` of the E4 sum reached from display 5.15, at one point `m`
of J. The sum over the prime quadruples with exponents in E4 of
`ω(log (m / (p1 p2 p3 p4)) / log p4) / log p4` weighted by `1 / (p1 p2 p3 p4)` is `1 / log Z`
times the E4 integral of page 51 with `1` replaced by `s`, at `m = Z^s`, error `T0^(-5)`.
Strong error form of `LowerShortC165.four_quad_density_pointwise`, whose route is partial
summation in each prime, `four_transfer_p1` to `four_transfer_p4`, and the Riemann sum
`four_integer_riemann`. -/
theorem four_pointwise_strong (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
              i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
                i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
                lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                  (expo ε x i.2.2.2)),
          ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
                  (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
                Real.log (i.2.2.2 : ℝ) /
                  ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ))) -
        lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x)| ≤ C * (perronT0 x ^ 5)⁻¹ := by
  obtain ⟨C1, h1⟩ := leaf_four_transfer_p1_strong ω hω hz hε hε8
  obtain ⟨C2, h2⟩ := leaf_four_transfer_p2_strong ω hω hz hε hε8
  obtain ⟨C3, h3⟩ := leaf_four_transfer_p3_strong ω hω hz hε hε8
  obtain ⟨C4, h4⟩ := leaf_four_transfer_p4_strong ω hω hz hε hε8
  obtain ⟨C5, h5⟩ := leaf_four_integer_riemann_strong ω hω hz hε hε8
  refine ⟨max (max (max C1 C2) (max C3 C4)) (max C5 (|C1| + |C2| + |C3| + |C4| + |C5| + 1)),
    fun x hx m hm1 hm2 => ?_⟩
  have hx1 : C1 ≤ x :=
    (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hx))
  have hx2 : C2 ≤ x :=
    (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hx))
  have hx3 : C3 ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hx))
  have hx4 : C4 ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hx))
  have hx5 : C5 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hC6 : |C1| + |C2| + |C3| + |C4| + |C5| + 1 ≤
      max (max (max C1 C2) (max C3 C4)) (max C5 (|C1| + |C2| + |C3| + |C4| + |C5| + 1)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hxone : (1 : ℝ) ≤ x := by
    have := abs_nonneg C1
    have := abs_nonneg C2
    have := abs_nonneg C3
    have := abs_nonneg C4
    have := abs_nonneg C5
    linarith
  have hL : 0 ≤ (perronT0 x ^ 5)⁻¹ := inv_nonneg.mpr (pow_nonneg (perronT0_pos x).le 5)
  have pw2 : ∀ n : ℕ, |primeWeight n| ≤ 2 := fun n => by
    unfold primeWeight
    split_ifs <;> norm_num
  have e1 := h1 x hx1 m hm1 hm2 primeWeight primeWeight primeWeight pw2 pw2 pw2
  have e2 := h2 x hx2 m hm1 hm2 (fun n : ℕ => 1 / Real.log (n : ℝ)) primeWeight primeWeight
    four_inv_log_le_two pw2 pw2
  have e3 := h3 x hx3 m hm1 hm2 (fun n : ℕ => 1 / Real.log (n : ℝ))
    (fun n : ℕ => 1 / Real.log (n : ℝ)) primeWeight four_inv_log_le_two four_inv_log_le_two pw2
  have e4 := h4 x hx4 m hm1 hm2 (fun n : ℕ => 1 / Real.log (n : ℝ))
    (fun n : ℕ => 1 / Real.log (n : ℝ)) (fun n : ℕ => 1 / Real.log (n : ℝ))
    four_inv_log_le_two four_inv_log_le_two four_inv_log_le_two
  have e5 := h5 x hx5 m hm1 hm2
  have tel := four_hybrid_telescope
    (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)))
    (fun i : ℕ × ℕ × ℕ × ℕ => primeWeight i.1)
    (fun i : ℕ × ℕ × ℕ × ℕ => primeWeight i.2.1)
    (fun i : ℕ × ℕ × ℕ × ℕ => primeWeight i.2.2.1)
    (fun i : ℕ × ℕ × ℕ × ℕ => primeWeight i.2.2.2)
    (fun i : ℕ × ℕ × ℕ × ℕ => 1 / Real.log (i.1 : ℝ))
    (fun i : ℕ × ℕ × ℕ × ℕ => 1 / Real.log (i.2.1 : ℝ))
    (fun i : ℕ × ℕ × ℕ × ℕ => 1 / Real.log (i.2.2.1 : ℝ))
    (fun i : ℕ × ℕ × ℕ × ℕ => 1 / Real.log (i.2.2.2 : ℝ))
    (fun i : ℕ × ℕ × ℕ × ℕ => (ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
              (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
            Real.log (i.2.2.2 : ℝ) /
              ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ))))
  rw [four_prime_filter_sum]
  have b1 := (abs_le.mp e1)
  have b2 := (abs_le.mp e2)
  have b3 := (abs_le.mp e3)
  have b4 := (abs_le.mp e4)
  have b5 := (abs_le.mp e5)
  have c1 := mul_le_mul_of_nonneg_right (le_abs_self C1) hL
  have c2 := mul_le_mul_of_nonneg_right (le_abs_self C2) hL
  have c3 := mul_le_mul_of_nonneg_right (le_abs_self C3) hL
  have c4 := mul_le_mul_of_nonneg_right (le_abs_self C4) hL
  have c5 := mul_le_mul_of_nonneg_right (le_abs_self C5) hL
  have c6 := mul_le_mul_of_nonneg_right hC6 hL
  have c7 : (|C1| + |C2| + |C3| + |C4| + |C5| + 1) * (perronT0 x ^ 5)⁻¹ =
      |C1| * (perronT0 x ^ 5)⁻¹ + |C2| * (perronT0 x ^ 5)⁻¹ + |C3| * (perronT0 x ^ 5)⁻¹ +
        |C4| * (perronT0 x ^ 5)⁻¹ + |C5| * (perronT0 x ^ 5)⁻¹ + (perronT0 x ^ 5)⁻¹ := by ring
  rw [abs_le]
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2]

/-- PROVED from the E4 pieces, page 51 display 5.17 on every prefix of J with the error
`Y T0^(-5)`: the assembly of `LowerShortC165.four_density_main` by
`four_density_swap_combine`. -/
theorem four_prefix_strong (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ U : ℕ, U ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ U,
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
  obtain ⟨CA, hCA⟩ := four_pointwise_strong ω hω hz hε hε8
  obtain ⟨CB, hCB⟩ := four_cofactor_strong ω hω hz hε hε8
  refine ⟨max (max CA CB) (|CB| + 2 * |CA| + 1), fun x hx U hU => ?_⟩
  have hxA : CA ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxB : CB ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hC3 : |CB| + 2 * |CA| + 1 ≤ max (max CA CB) (|CB| + 2 * |CA| + 1) := le_max_right _ _
  have hx1 : (1 : ℝ) ≤ x := by
    have h1 := abs_nonneg CA
    have h2 := abs_nonneg CB
    linarith
  have hYpos : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hL : 0 ≤ (perronT0 x ^ 5)⁻¹ := inv_nonneg.mpr (pow_nonneg (perronT0_pos x).le 5)
  have hYL : 0 ≤ x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := mul_nonneg hYpos.le hL
  have hU' : (U : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    (Nat.cast_le.mpr hU).trans (Nat.floor_le (by positivity))
  have hB' := hCB x hxB U hU
  have hmain := four_density_swap_combine
    (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
              i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
                i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
                lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                  (expo ε x i.2.2.2)))
    (fun i : ℕ × ℕ × ℕ × ℕ => i.1 * i.2.1 * i.2.2.1 * i.2.2.2)
    (fun i hi => by
      obtain ⟨-, hp1, hp2, hp3, hp4, -⟩ := Finset.mem_filter.mp hi
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp1.pos hp2.pos) hp3.pos) hp4.pos)
    (fun (i : ℕ × ℕ × ℕ × ℕ) (n : ℕ) =>
      ω (Real.log (n : ℝ) / Real.log (i.2.2.2 : ℝ)) / Real.log (i.2.2.2 : ℝ))
    (fun (i : ℕ × ℕ × ℕ × ℕ) (m : ℕ) =>
      ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
                  (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
                Real.log (i.2.2.2 : ℝ) /
                  ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ)))
    (fun m : ℕ => lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
      Real.log (scaleZ ε x))
    ⌊x ^ (11 / 20 + ε)⌋₊ U (|CA| * (perronT0 x ^ 5)⁻¹)
    (CB * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹)
    (mul_nonneg (abs_nonneg CA) hL) hB'
    (fun m hm => by
      have hm' := Finset.mem_Ioc.mp hm
      exact (hCA x hxA m hm'.1 (hm'.2.trans hU)).trans
        (mul_le_mul_of_nonneg_right (le_abs_self CA) hL))
  refine hmain.trans ?_
  have h1 : CB * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ ≤
      |CB| * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self CB) hYL
  have h2 : (U : ℝ) * (|CA| * (perronT0 x ^ 5)⁻¹) ≤
      2 * |CA| * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) :=
    calc (U : ℝ) * (|CA| * (perronT0 x ^ 5)⁻¹)
        ≤ 2 * x ^ (11 / 20 + ε) * (|CA| * (perronT0 x ^ 5)⁻¹) :=
          mul_le_mul_of_nonneg_right hU' (mul_nonneg (abs_nonneg CA) hL)
      _ = 2 * |CA| * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) := by ring
  have h3 := mul_le_mul_of_nonneg_right hC3 hYL
  have h4 : (|CB| + 2 * |CA| + 1) * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) =
      |CB| * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) +
        2 * |CA| * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) +
        x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by ring
  have h5 : max (max CA CB) (|CB| + 2 * |CA| + 1) * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ =
      max (max CA CB) (|CB| + 2 * |CA| + 1) *
        (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) := by ring
  linarith

/-- PROVED from the E4 pieces of this file: verbatim the statement of
`DQ517Window.leaf_four_main_window`, page 51 display 5.17, by `four_prefix_strong` and
`window_of_prefix`. -/
theorem four_main_window_of_s130 (ω : ℝ → ℝ)
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
  obtain ⟨C, hC⟩ := four_prefix_strong ω hω hz hε hε8
  refine ⟨max C (2 * |C|), fun x hx a b ha hb => ?_⟩
  have hxC : C ≤ x := (le_max_left _ _).trans hx
  have hw := window_of_prefix _ (hC x hxC) ha hb
  refine hw.trans ?_
  have hL : 0 ≤ (perronT0 x ^ 5)⁻¹ := inv_nonneg.mpr (pow_nonneg (perronT0_pos x).le 5)
  have hYL : 0 ≤ x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ :=
    mul_nonneg (Real.rpow_nonneg (by
      have := abs_nonneg C
      have := le_max_right C (2 * |C|)
      linarith) _) hL
  calc 2 * (C * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹)
      = 2 * C * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) := by ring
    _ ≤ max C (2 * |C|) * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) :=
        mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_left (le_abs_self C) (by norm_num)).trans
            (le_max_right _ _)) hYL
    _ = _ := by ring

end LeanLab.BHP1997.S130MainWindow
