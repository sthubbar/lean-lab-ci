/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character, the
E2 sum of display 5.15, page 50: the outer primes `p1`, `p2` at one point `m` of J.

The paper proves 5.17 with the words "a straightforward consequence of the prime number
theorem". For the sum over the prime pairs `p2 < p1` with exponents in E2 this file writes
the consequence as three one variable steps and proves the exact algebra between them:

* `two_pair_sum_split`: with `w` the indicator of the primes and `l n = 1 / log n`, the double
  sum over `w b w a` is the double sum over `l b l a` plus two error sums, one with the factor
  `w a - l a` for each fixed `b`, one with the factor `w b - l b` for each fixed integer `a`;
* `two_pair_first_prime`, in `TwoDensityMain517d.lean`: the first error sum, the prime number
  theorem with partial summation in `p1` for each fixed prime `p2`;
* `two_pair_second_prime`, in `TwoDensityMain517d.lean`: the second error sum, the prime
  number theorem with partial summation in `p2` for each fixed integer `a`;
* `two_pair_riemann`: the double sum over integers with the densities `1 / (log a log b)` is
  the E2 integral of page 51 at `s = log m / log Z`. No prime number theorem is used in this
  step. It is split here into its two one variable passages from a sum to an integral,
  `leaf_two_pair_riemann_first` and `leaf_two_pair_riemann_second`, which are the two open
  leaves.

`two_pair_density_pointwise` is proved from these three statements.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a
import LeanLab.BHP1997.BuchstabIntegral517
import LeanLab.BHP1997.TwoDensityMain517d

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d Decomp514a
open scoped BigOperators
open MeasureTheory


/-! ### Stage 1: sum against integral, cell by cell -/

/-- Cell integrability passes to the whole interval. -/
theorem intervalIntegrable_of_cells {φ : ℝ → ℝ} {A : ℕ}
    (hint : ∀ n : ℕ, A < n → IntervalIntegrable φ volume ((n : ℝ) - 1) (n : ℝ)) :
    ∀ B : ℕ, A ≤ B → IntervalIntegrable φ volume (A : ℝ) (B : ℝ) := by
  intro B hAB
  induction B, hAB using Nat.le_induction with
  | base =>
    refine ⟨?_, ?_⟩ <;>
      exact MeasureTheory.IntegrableOn.of_measure_zero (by simp)
  | succ b hab ih =>
    have hcast : ((b + 1 : ℕ) : ℝ) - 1 = (b : ℝ) := by push_cast; ring
    have hcell : IntervalIntegrable φ volume (b : ℝ) ((b + 1 : ℕ) : ℝ) := by
      have h := hint (b + 1) (Nat.lt_succ_of_le hab)
      rwa [hcast] at h
    exact ih.trans hcell

/-- P0069 page 51 display 5.17, passage from the integers of an interval to the integral.
If on each cell `(n-1, n]` the value at the right endpoint is within `δ n` of the values
on the cell, then the sum over the integers of `(A, B]` is within `∑ δ` of the integral.
This is the cell by cell form of `BuchstabIntegral517.sum_sub_integral_le_of_lipschitz`,
whose constant multiplies the whole length of the interval and therefore does not decay;
here `δ n` may decay like `1/n^2`. -/
theorem sum_sub_integral_le_of_cell (φ : ℝ → ℝ) (δ : ℕ → ℝ) (A : ℕ)
    (hδ0 : ∀ n : ℕ, A < n → 0 ≤ δ n)
    (hint : ∀ n : ℕ, A < n → IntervalIntegrable φ volume ((n : ℝ) - 1) (n : ℝ))
    (hosc : ∀ n : ℕ, A < n → ∀ t ∈ Set.Icc ((n : ℝ) - 1) (n : ℝ), |φ (n : ℝ) - φ t| ≤ δ n) :
    ∀ B : ℕ, A ≤ B →
      |(∑ n ∈ Finset.Ioc A B, φ n) - ∫ t in (A : ℝ)..(B : ℝ), φ t| ≤
        ∑ n ∈ Finset.Ioc A B, δ n := by
  intro B hAB
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hcast : ((b + 1 : ℕ) : ℝ) - 1 = (b : ℝ) := by push_cast; ring
    have hcell : IntervalIntegrable φ volume (b : ℝ) ((b + 1 : ℕ) : ℝ) := by
      have h := hint (b + 1) (Nat.lt_succ_of_le hab)
      rwa [hcast] at h
    have hAb : IntervalIntegrable φ volume (A : ℝ) (b : ℝ) :=
      intervalIntegrable_of_cells hint b hab
    have hadd := intervalIntegral.integral_add_adjacent_intervals hAb hcell
    -- the last cell
    have hlast : |φ ((b + 1 : ℕ) : ℝ) - ∫ t in (b : ℝ)..((b + 1 : ℕ) : ℝ), φ t| ≤
        δ (b + 1) := by
      have hconst : (∫ _t in (b : ℝ)..((b + 1 : ℕ) : ℝ), φ ((b + 1 : ℕ) : ℝ)) =
          φ ((b + 1 : ℕ) : ℝ) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        have h1 : ((b + 1 : ℕ) : ℝ) - (b : ℝ) = 1 := by push_cast; ring
        rw [h1, one_mul]
      have hdiff : φ ((b + 1 : ℕ) : ℝ) - ∫ t in (b : ℝ)..((b + 1 : ℕ) : ℝ), φ t =
          ∫ t in (b : ℝ)..((b + 1 : ℕ) : ℝ), (φ ((b + 1 : ℕ) : ℝ) - φ t) := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const hcell, hconst]
      rw [hdiff]
      have hb1le : (b : ℝ) ≤ ((b + 1 : ℕ) : ℝ) := by push_cast; linarith
      have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (b : ℝ)) (b := ((b + 1 : ℕ) : ℝ)) (C := δ (b + 1))
        (f := fun t => φ ((b + 1 : ℕ) : ℝ) - φ t) (by
          intro t ht
          rw [show Set.uIoc (b : ℝ) ((b + 1 : ℕ) : ℝ) =
              Set.Ioc (b : ℝ) ((b + 1 : ℕ) : ℝ) from Set.uIoc_of_le hb1le] at ht
          have htm : t ∈ Set.Icc (((b + 1 : ℕ) : ℝ) - 1) ((b + 1 : ℕ) : ℝ) := by
            rw [hcast]
            exact ⟨le_of_lt ht.1, ht.2⟩
          rw [Real.norm_eq_abs]
          exact hosc (b + 1) (Nat.lt_succ_of_le hab) t htm)
      rw [Real.norm_eq_abs] at hbnd
      have hone : |((b + 1 : ℕ) : ℝ) - (b : ℝ)| = 1 := by
        rw [show ((b + 1 : ℕ) : ℝ) - (b : ℝ) = 1 by push_cast; ring]; norm_num
      rw [hone, mul_one] at hbnd
      exact hbnd
    rw [Finset.sum_Ioc_succ_top hab, ← hadd]
    have he : (∑ n ∈ Finset.Ioc A b, φ n) + φ ((b + 1 : ℕ) : ℝ) -
        ((∫ t in (A : ℝ)..(b : ℝ), φ t) + ∫ t in (b : ℝ)..((b + 1 : ℕ) : ℝ), φ t) =
        ((∑ n ∈ Finset.Ioc A b, φ n) - ∫ t in (A : ℝ)..(b : ℝ), φ t) +
          (φ ((b + 1 : ℕ) : ℝ) - ∫ t in (b : ℝ)..((b + 1 : ℕ) : ℝ), φ t) := by ring
    rw [he, Finset.sum_Ioc_succ_top hab]
    exact (abs_add_le _ _).trans (add_le_add ih hlast)


/-! ### Stage 2: a log power is smaller than any power of `x` -/

/-- `log x` is at most `x ^ r / r` for `x > 0`, `r > 0` (from `log y ≤ y - 1` at `y = x ^ r`). -/
theorem log_le_rpow_div {x r : ℝ} (hx : 0 < x) (hr : 0 < r) :
    Real.log x ≤ x ^ r / r := by
  have hxr : 0 < x ^ r := Real.rpow_pos_of_pos hx r
  have h1 : Real.log x * r = Real.log (x ^ r) := by
    rw [Real.log_rpow hx r]; ring
  have h2 : Real.log (x ^ r) ≤ x ^ r - 1 := Real.log_le_sub_one_of_pos hxr
  have h3 : Real.log x * r ≤ x ^ r := by linarith
  rw [le_div_iff₀ hr]
  linarith

/-- `(log x) ^ m` is bounded by a constant times `x ^ c`, for every real `m` and every `c > 0`. -/
theorem exists_log_rpow_le_mul_rpow {c : ℝ} (hc : 0 < c) (m : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → Real.log x ^ m ≤ C * x ^ c := by
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases le_or_gt m 0 with hm | hm
  · refine ⟨(Real.log 2) ^ m / 2 ^ c, by positivity, fun x hx => ?_⟩
    have hx0 : 0 < x := by linarith
    have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
    have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have hle : Real.log x ^ m ≤ Real.log 2 ^ m :=
      Real.rpow_le_rpow_of_nonpos h2 hl2 hm
    have hx2 : (1:ℝ) ≤ x ^ c := Real.one_le_rpow (by linarith : (1:ℝ) ≤ x) hc.le
    have hxe : (1:ℝ) ≤ (2:ℝ) ^ c := Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 2) hc.le
    have hpos : 0 < (2:ℝ) ^ c := Real.rpow_pos_of_pos (by norm_num) c
    have hxc : (2:ℝ) ^ c ≤ x ^ c := Real.rpow_le_rpow (by norm_num) hx hc.le
    have hlm : 0 < Real.log 2 ^ m := Real.rpow_pos_of_pos h2 m
    have hkey : Real.log 2 ^ m ≤ Real.log 2 ^ m / (2:ℝ) ^ c * x ^ c := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
      exact mul_le_mul_of_nonneg_left hxc hlm.le
    linarith
  · refine ⟨(c / m) ^ (-m), by positivity, fun x hx => ?_⟩
    have hx0 : 0 < x := by linarith
    have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
    have hr : 0 < c / m := by positivity
    have h1 : Real.log x ≤ x ^ (c / m) / (c / m) := log_le_rpow_div hx0 hr
    have hle : Real.log x ^ m ≤ (x ^ (c / m) / (c / m)) ^ m :=
      Real.rpow_le_rpow hl0.le h1 hm.le
    have hrr : (x ^ (c / m) / (c / m)) ^ m = x ^ c / (c / m) ^ m := by
      rw [Real.div_rpow (Real.rpow_pos_of_pos hx0 (c / m)).le hr.le,
        ← Real.rpow_mul hx0.le (c / m) m, show c / m * m = c from by field_simp]
    have key : x ^ c / (c / m) ^ m = (c / m) ^ (-m) * x ^ c := by
      rw [Real.rpow_neg hr.le, div_eq_inv_mul, mul_comm]
    exact hle.trans (le_of_eq (hrr.trans key))


/-- The absorption used at the end of both leaves: a factor `x ^ (-c)` with `c > 0`, times any
fixed log power, is bounded by `C log ^ (-A) x`. -/
theorem rpow_neg_mul_log_rpow_le {c : ℝ} (hc : 0 < c) (j A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      x ^ (-c) * Real.log x ^ j ≤ C * Real.log x ^ (-A) := by
  obtain ⟨C, hC0, hC⟩ := exists_log_rpow_le_mul_rpow (c := c / 2) (by linarith) (j + A)
  refine ⟨C, hC0, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 : Real.log x ^ (j + A) ≤ C * x ^ (c / 2) := hC x hx
  have hsplit : Real.log x ^ (j + A) = Real.log x ^ j * Real.log x ^ A :=
    Real.rpow_add hl0 j A
  have hA0 : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hl0 A
  have hxj : Real.log x ^ j = Real.log x ^ (j + A) / Real.log x ^ A := by
    rw [hsplit, mul_div_cancel_right₀ _ (ne_of_gt hA0)]
  have hxc : 0 < x ^ (-c) := Real.rpow_pos_of_pos hx0 _
  have hgp : (1:ℝ) ≤ x ^ (c / 2) :=
    Real.one_le_rpow (le_trans (by norm_num) hx) (by linarith)
  have hnc : x ^ (-(c / 2)) ≤ 1 := by
    rw [Real.rpow_neg hx0.le]
    simpa [one_div] using one_div_le_one_div_of_le zero_lt_one hgp
  have hlogneg : (0:ℝ) ≤ Real.log x ^ (-A) := Real.rpow_nonneg hl0.le _
  calc x ^ (-c) * Real.log x ^ j
      = x ^ (-c) * (Real.log x ^ (j + A) / Real.log x ^ A) := by rw [hxj]
    _ ≤ x ^ (-c) * (C * x ^ (c / 2) / Real.log x ^ A) := by
        refine mul_le_mul_of_nonneg_left ?_ hxc.le
        exact div_le_div_of_nonneg_right h1 hA0.le
    _ = C * (x ^ (-c) * x ^ (c / 2)) * Real.log x ^ (-A) := by
        rw [Real.rpow_neg hl0.le, div_eq_mul_inv]; ring
    _ = C * x ^ (-(c / 2)) * Real.log x ^ (-A) := by
        rw [show x ^ (-c) * x ^ (c / 2) = x ^ (-(c / 2)) by
          rw [← Real.rpow_add hx0]; ring_nf]
    _ ≤ C * 1 * Real.log x ^ (-A) := by
        refine mul_le_mul_of_nonneg_right ?_ hlogneg
        exact mul_le_mul_of_nonneg_left hnc hC0.le
    _ = C * Real.log x ^ (-A) := by ring

/-- `log t - log a ≤ (t - a) / a` for `0 < a ≤ t`. -/
theorem log_sub_log_le_div {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    Real.log t - Real.log a ≤ (t - a) / a := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  rw [← Real.log_div ht.ne' ha.ne']
  have h1 : Real.log (t / a) ≤ t / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2 : t / a - 1 = (t - a) / a := by rw [div_sub_one ha.ne']
  linarith


/-! ### Stage 3: the two objects are the same function of the exponent `α` -/

/-- The Buchstab argument of the leaf, in the exponent variables `α = log a / log Z`,
`β = log b / log Z`: `(s - α - β)/β = log (m/(a b)) / log b` for `s = log m / log Z`. -/
theorem two_pair_arg_eq {Z m a b : ℝ} (hZ : 0 < Real.log Z) (hm : 0 < m) (ha : 0 < a)
    (hb : 1 < b) :
    (Real.log m / Real.log Z - Real.log a / Real.log Z - Real.log b / Real.log Z) /
        (Real.log b / Real.log Z) = Real.log (m / (a * b)) / Real.log b := by
  have hb0 : 0 < b := by linarith
  have hlb : 0 < Real.log b := Real.log_pos hb
  have hab : 0 < a * b := by positivity
  rw [Real.log_div hm.ne' hab.ne', Real.log_mul ha.ne' hb0.ne']
  field_simp
  ring


/-- On one cell `a ≤ t ≤ a + 1` with `a ≥ 4`, on which the Buchstab argument is at least one,
the smooth factor `ω(log (m/(a b)) / log b) / (a log a)` moves by at most `8 / (a^2 log a)`.
This is the per cell oscillation that makes `sum_sub_integral_le_of_cell` give a decaying bound
(compare `BuchstabIntegral517.sum_sub_integral_le_of_lipschitz`, whose constant does not decay). -/
theorem two_pair_cell_osc {ω : ℝ → ℝ} (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {m b a t : ℝ} (hb : 2 ≤ b) (hm : 0 < m) (ha : 4 ≤ a) (ht : a ≤ t) (hta : t ≤ a + 1)
    (hu : 1 ≤ Real.log (m / (t * b)) / Real.log b) :
    |ω (Real.log (m / (t * b)) / Real.log b) / (t * Real.log t) -
        ω (Real.log (m / (a * b)) / Real.log b) / (a * Real.log a)| ≤
      8 / (a ^ 2 * Real.log a) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 0 < Real.log b := Real.log_pos (by linarith)
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by
    have h1 : Real.log (1/2:ℝ) ≤ 1/2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h2 : Real.log (1/2:ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    linarith
  have hlb2 : (1/2:ℝ) ≤ Real.log b := by
    have h : Real.log 2 ≤ Real.log b := Real.log_le_log (by norm_num) hb
    linarith
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := by linarith
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlat : Real.log a ≤ Real.log t := Real.log_le_log (by linarith) ht
  -- the two Buchstab arguments, and their order
  set ua : ℝ := Real.log (m / (a * b)) / Real.log b with hua
  set ut : ℝ := Real.log (m / (t * b)) / Real.log b with hut
  have htab : 0 < t * b := by positivity
  have haab : 0 < a * b := by positivity
  have harg : ut - ua = Real.log (a / t) / Real.log b := by
    rw [hua, hut, ← sub_div, ← Real.log_div (ne_of_gt (by positivity : (0:ℝ) < m / (t * b)))
      (ne_of_gt (by positivity : (0:ℝ) < m / (a * b)))]
    congr 1
    field_simp
  have hlogat : Real.log (a / t) ≤ 0 := by
    apply Real.log_nonpos
    · positivity
    · rw [div_le_one ht0]; exact ht
  have hut_le : ut ≤ ua := by
    have : ut - ua ≤ 0 := by rw [harg]; exact div_nonpos_of_nonpos_of_nonneg hlogat hb1.le
    linarith
  have hua1 : 1 ≤ ua := le_trans hu hut_le
  -- Lipschitz of omega
  have hw : |ω ut - ω ua| ≤ ua - ut := by
    have h1 : |ω ut - ω ua| ≤ |ut - ua| := buchstab_lipschitz_abs hω hz hu hua1
    rw [abs_of_nonpos (by linarith : ut - ua ≤ 0)] at h1
    linarith
  -- the change of the Buchstab argument across the cell
  have hdu : ua - ut ≤ 2 / a := by
    have h2 : ua - ut = Real.log (t / a) / Real.log b := by
      rw [← neg_sub, harg]; rw [show a / t = (t / a)⁻¹ by field_simp]
      rw [Real.log_inv]; ring
    have h3 : Real.log (t / a) ≤ (t - a) / a := by
      rw [Real.log_div ht0.ne' ha0.ne']
      exact log_sub_log_le_div ha0 ht
    have h4 : (t - a) / a ≤ 1 / a :=
      div_le_div_of_nonneg_right (by linarith : t - a ≤ 1) ha0.le
    have h5 : Real.log (t / a) ≤ 1 / a := le_trans h3 h4
    rw [h2]
    have h6 : (1 / a) / (1 / 2) = 2 / a := by field_simp
    calc Real.log (t / a) / Real.log b ≤ (1 / a) / Real.log b :=
          div_le_div_of_nonneg_right h5 hb1.le
      _ ≤ (1 / a) / (1 / 2) := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hlb2
      _ = 2 / a := h6
  -- the difference of the two reciprocal logarithms
  have hlog : |1 / (t * Real.log t) - 1 / (a * Real.log a)| ≤ 6 / (a ^ 2 * Real.log a) := by
    have hkey : 1 / (t * Real.log t) - 1 / (a * Real.log a) =
        (a * Real.log a - t * Real.log t) / (a * t * Real.log a * Real.log t) := by
      field_simp
    have hden : 0 < a * t * Real.log a * Real.log t := by positivity
    have hden2 : a ^ 2 * Real.log a * Real.log a ≤ a * t * Real.log a * Real.log t := by
      have h1 : a * a ≤ a * t := by
        exact mul_le_mul_of_nonneg_left ht ha0.le
      have h2 : Real.log a * Real.log a ≤ Real.log a * Real.log t :=
        mul_le_mul_of_nonneg_left hlat hla.le
      nlinarith
    have htl : t * Real.log t ≥ a * Real.log a := by
      have h1 := mul_le_mul ht hlat hla.le (by linarith : (0:ℝ) ≤ t)
      simpa using h1
    have hnum : |a * Real.log a - t * Real.log t| = t * Real.log t - a * Real.log a := by
      rw [abs_of_nonpos (by linarith)]; ring
    have hnum2 : t * Real.log t - a * Real.log a ≤ (t - a) * (Real.log (a + 1) + 1) := by
      have e1 : t * Real.log t - a * Real.log a =
          (t - a) * Real.log t + a * (Real.log t - Real.log a) := by ring
      have e2 : (t - a) * Real.log t ≤ (t - a) * Real.log (a + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact Real.log_le_log (by linarith) hta
      have e3 : a * (Real.log t - Real.log a) ≤ a * ((t - a) / a) := by
        refine mul_le_mul_of_nonneg_left ?_ ha0.le
        exact log_sub_log_le_div ha0 ht
      have e4 : a * ((t - a) / a) = t - a := by field_simp
      have e5 : (t - a) * Real.log (a + 1) + (t - a) = (t - a) * (Real.log (a + 1) + 1) := by
        ring
      rw [e1]
      nlinarith [e2, e3, e4, e5]
    have hnum3 : (t - a) * (Real.log (a + 1) + 1) ≤ Real.log (a + 1) + 1 := by
      have hX : (0:ℝ) < Real.log (a + 1) + 1 := by
        have h : 0 < Real.log (a + 1) := Real.log_pos (by linarith)
        linarith
      have h1 : (t - a) * (Real.log (a + 1) + 1) ≤ 1 * (Real.log (a + 1) + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) hX.le
      linarith
    have hla1 : Real.log (a + 1) ≤ Real.log a + 1 / a := by
      have h := log_sub_log_le_div ha0 (by linarith : a ≤ a + 1)
      have e : a + 1 - a = 1 := by ring
      rw [e] at h
      linarith
    have hla2 : 1 / a ≤ 1 / 4 := by
      apply one_div_le_one_div_of_le (by norm_num); linarith
    have hlog4 : (1:ℝ) ≤ Real.log a := by
      have h : Real.log 4 ≤ Real.log a := Real.log_le_log (by norm_num) ha
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
        push_cast; ring
      linarith
    have hb1 : Real.log (a + 1) + 1 ≤ 6 * Real.log a := by
      have : Real.log (a + 1) ≤ Real.log a + 1 / 4 := le_trans hla1 (by linarith [hla2])
      nlinarith
    have hstep : (t * Real.log t - a * Real.log a) / (a * t * Real.log a * Real.log t) ≤
        6 / (a ^ 2 * Real.log a) := by
      rw [div_le_div_iff₀ hden (by positivity)]
      nlinarith [hnum2, hnum3, hb1, hden2, Real.log_pos (by linarith : (1:ℝ) < a + 1)]
    rw [hkey, abs_div, abs_of_pos hden, hnum]
    calc (t * Real.log t - a * Real.log a) / (a * t * Real.log a * Real.log t) ≤
          6 / (a ^ 2 * Real.log a) := hstep
      _ = 6 / (a ^ 2 * Real.log a) := rfl
  -- assemble
  have hsplit : ω ut / (t * Real.log t) - ω ua / (a * Real.log a) =
      (ω ut - ω ua) / (t * Real.log t) + ω ua * (1 / (t * Real.log t) - 1 / (a * Real.log a)) := by
    field_simp
    ring
  have hw1 : ω ua ≤ 1 := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz ua
  have hw0 : 0 ≤ ω ua := Decomp514a.two_density_buchstab_nonneg hω hz ua
  have htla : a * Real.log a ≤ t * Real.log t := by
    have h1 := mul_le_mul ht hlat hla.le (by linarith : (0:ℝ) ≤ t)
    simpa using h1
  have hden_t : 0 < t * Real.log t := by positivity
  have h1 : |(ω ut - ω ua) / (t * Real.log t)| ≤ 2 / (a ^ 2 * Real.log a) := by
    have hbnd : |ω ut - ω ua| ≤ 2 / a := le_trans hw hdu
    have hpos : 0 < a ^ 2 * Real.log a := by positivity
    rw [abs_div, abs_of_pos hden_t, div_le_div_iff₀ hden_t hpos]
    have hmul : |ω ut - ω ua| * (a ^ 2 * Real.log a) ≤ (2 / a) * (a ^ 2 * Real.log a) :=
      mul_le_mul_of_nonneg_right hbnd hpos.le
    have heq : (2 / a) * (a ^ 2 * Real.log a) = 2 * (a * Real.log a) := by
      field_simp
    have h2 : 2 * (a * Real.log a) ≤ 2 * (t * Real.log t) := by linarith
    linarith [hmul, heq, h2]
  have h2 : |ω ua * (1 / (t * Real.log t) - 1 / (a * Real.log a))| ≤
      6 / (a ^ 2 * Real.log a) := by
    rw [abs_mul, abs_of_nonneg hw0]
    calc ω ua * |1 / (t * Real.log t) - 1 / (a * Real.log a)|
        ≤ 1 * (6 / (a ^ 2 * Real.log a)) := by
          refine mul_le_mul hw1 hlog (abs_nonneg _) (by norm_num)
      _ = 6 / (a ^ 2 * Real.log a) := one_mul _
  rw [hsplit]
  have := abs_add_le ((ω ut - ω ua) / (t * Real.log t))
    (ω ua * (1 / (t * Real.log t) - 1 / (a * Real.log a)))
  have hsum : 2 / (a ^ 2 * Real.log a) + 6 / (a ^ 2 * Real.log a) =
      8 / (a ^ 2 * Real.log a) := by ring
  linarith [this]


/-- Order transfer: if `t` is not in `[α, α')`, then `α ≤ t` and `α' ≤ t` agree. -/
theorem le_iff_of_not_switch {α α' t : ℝ} (h : α ≤ α') (hno : ¬(α ≤ t ∧ t ≤ α')) :
    (α ≤ t ↔ α' ≤ t) := by
  constructor
  · intro h1
    by_contra h2
    push_neg at h2
    exact hno ⟨h1, le_of_lt h2⟩
  · intro h1; linarith

/-- Order transfer in the reverse form. -/
theorem le_iff_of_not_switch' {α α' t : ℝ} (h : α ≤ α') (hno : ¬(α ≤ t ∧ t ≤ α')) :
    (t ≤ α ↔ t ≤ α') := by
  constructor
  · intro h1; linarith
  · intro h1
    by_contra h2
    push_neg at h2
    exact hno ⟨le_of_lt h2, h1⟩

/-- P0069 page 51: the discarded region `E₂` as a function of the first exponent `α`. Every atom of
`lowerTwoDiscarded` is of the form `α ≤ L` or `L ≤ α` with `L` affine in `β`, so between
consecutive switch points the truth value does not change. The hypotheses are the atom-wise
transfers `t ≤ α ↔ t ≤ α'` and `α ≤ t ↔ α' ≤ t` at the fourteen switch points
`1/2`, `β`, `1 - 2β`, `1/2 + c₃ - 2ε - 2β`, `(2 + θ - ε - 7β)/4`, `1/2 - (θ + 3c₁)/4 + ε - β`,
`(2 + θ - ε - 5β)/4`, `1/2 - (θ + c₁)/4 + ε - β`, `(36θ - 2)/11 - ε`, `2β - θ + ε`,
`(2 ∓ (θ - ε) - 3β)/4` and `(2 ∓ (θ - ε) - β)/4`. -/
theorem sect_same {ε β α α' : ℝ} (hα : α ≤ α')
    (h1 : β ≤ α ↔ β ≤ α') (h2 : α ≤ 1/2 ↔ α' ≤ 1/2)
    (h3 : α + 2*β ≤ 1 ↔ α' + 2*β ≤ 1)
    (h4 : α + 2*β ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε ↔
          α' + 2*β ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε)
    (h5 : 4*α + 7*β ≤ 2+2*(1/16-1/10^5)-ε ↔ 4*α' + 7*β ≤ 2+2*(1/16-1/10^5)-ε)
    (h6 : 1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β ↔
          1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α' + β)
    (h7 : 4*α + 5*β ≤ 2+2*(1/16-1/10^5)-ε ↔ 4*α' + 5*β ≤ 2+2*(1/16-1/10^5)-ε)
    (h8 : 1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β ↔
          1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α' + β)
    (h11 : 2*β - (2*(1/16-1/10^5)) + ε ≤ α ↔ 2*β - (2*(1/16-1/10^5)) + ε ≤ α')
    (h12 : α ≤ (36*(2*(1/16-1/10^5))-2)/11-ε ↔ α' ≤ (36*(2*(1/16-1/10^5))-2)/11-ε)
    (h13 : |4*α + 3*β - 2| ≤ 2*(1/16-1/10^5)-ε ↔ |4*α' + 3*β - 2| ≤ 2*(1/16-1/10^5)-ε)
    (h14 : |4*α + β - 2| ≤ 2*(1/16-1/10^5)-ε ↔ |4*α' + β - 2| ≤ 2*(1/16-1/10^5)-ε) :
    (lowerTwoDiscarded ε α β ↔ lowerTwoDiscarded ε α' β) := by
  unfold lowerTwoDiscarded upperPairRegion
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h11, h12, h13, h14]


/-! ### Stage 4: the change of variables `a = Z ^ α` -/

/-- The passage from the exponent `α` to the integer `a`: `dα = da / (a log Z)`, so an integral over
`α ∈ [1/10, 1/2]` is an integral over `a ∈ [Z^(1/10), Z^(1/2)]`. No hypothesis on `g` is needed
(`intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg`, the monotone case). -/
theorem integral_log_subst {Z : ℝ} (hZ : 1 < Z) (g : ℝ → ℝ) :
    (∫ a in Z ^ (1/10:ℝ)..Z ^ (1/2:ℝ), g (Real.log a / Real.log Z) * (1 / (a * Real.log Z))) =
      ∫ α in (1/10:ℝ)..(1/2:ℝ), g α := by
  have hZ0 : 0 < Z := by linarith
  have hL : 0 < Real.log Z := Real.log_pos hZ
  have ha0 : 0 < Z ^ (1/10:ℝ) := Real.rpow_pos_of_pos hZ0 _
  have hb0 : 0 < Z ^ (1/2:ℝ) := Real.rpow_pos_of_pos hZ0 _
  have hab : Z ^ (1/10:ℝ) ≤ Z ^ (1/2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)
  have hmin : min (Z ^ (1/10:ℝ)) (Z ^ (1/2:ℝ)) = Z ^ (1/10:ℝ) := min_eq_left hab
  have hfa : Real.log (Z ^ (1/10:ℝ)) / Real.log Z = 1/10 := by
    rw [Real.log_rpow hZ0]; field_simp
  have hfb : Real.log (Z ^ (1/2:ℝ)) / Real.log Z = 1/2 := by
    rw [Real.log_rpow hZ0]; field_simp
  have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (f := fun a : ℝ => Real.log a / Real.log Z) (f' := fun a : ℝ => 1 / (a * Real.log Z))
    (a := Z ^ (1/10:ℝ)) (b := Z ^ (1/2:ℝ)) (g := g)
    (by
      refine ContinuousOn.div_const ?_ _
      refine Real.continuousOn_log.mono ?_
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hx0
      rw [Set.uIcc_of_le hab] at hx
      rw [hx0] at hx
      linarith [hx.1])
    (by
      intro x hx
      have hx0 : x ≠ 0 := by
        have h1 : Z ^ (1/10:ℝ) < x := by rw [← hmin]; exact hx.1
        have : (0:ℝ) < Z ^ (1/10:ℝ) := ha0
        linarith
      have hd := (Real.hasDerivAt_log hx0).div_const (Real.log Z)
      convert hd using 1
      field_simp)
    (by
      intro x hx
      have hx0 : 0 < x := by
        have h1 : Z ^ (1/10:ℝ) < x := by rw [← hmin]; exact hx.1
        have : (0:ℝ) < Z ^ (1/10:ℝ) := ha0
        linarith
      positivity)
  rw [hfa, hfb] at h
  simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h


/-! ### Stage 5: the leaf's summand is the density `Φ` times the weight `1 / (b log^2 b)` -/

/-- The summand of `leaf_two_pair_riemann_first` at `(a, b)` is the density
`[E₂] ω (log (m/(a b)) / log b) / (a log a)` of `leaf_two_pair_riemann_second` at `a`, times the
weight `1 / (b log^2 b)` of the outer variable. This is the only point at which the two leaves
share their integrand; the arithmetic is `1/log b / (a b) * (1/log a * 1/log b) =
1/(a log a) * 1/(b log^2 b)`. -/
theorem summand_eq_density_weight (ω : ℝ → ℝ) {ε x : ℝ} {m a b : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
        ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
          Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
      else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log (b : ℝ))) =
      (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
        ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
          ((a : ℝ) * Real.log (a : ℝ))
      else 0) * (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) := by
  have ha1 : (1:ℝ) < a := by exact_mod_cast (by omega : 1 < a)
  have hb1 : (1:ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have ha0 : (0:ℝ) < a := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  have hla : Real.log (a : ℝ) ≠ 0 := ne_of_gt (Real.log_pos ha1)
  have hlb : Real.log (b : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hb1)
  by_cases h : lowerTwoDiscarded ε (expo ε x a) (expo ε x b)
  · simp only [h, if_true]
    field_simp
  · simp only [h, if_false]
    ring

/-- The support bound: a nonzero summand of `leaf_two_pair_riemann_first` forces
`b ≥ Z ^ (c₁ - ε)`, and `Decomp514a.scaleZ_rpow_ge` turns that into `b ≥ x ^ (11/200)`. This is
what makes the Riemann sum against the integral converge: the lowest admissible integer `b`, and
with it every admissible `a`, is at least `x ^ (11/200)`. -/
theorem support_ge {ε x : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hx : 1 ≤ x) {a b : ℕ}
    (h : lowerTwoDiscarded ε (expo ε x a) (expo ε x b)) :
    scaleZ ε x ^ ((1+7*(2*(1/16-1/10^5)))/15 - ε) ≤ (b : ℝ) := by
  obtain ⟨hZx, hZ1⟩ := scaleZ_rpow_ge hε hε8 hx
  have hZ0 : 0 < scaleZ ε x := by linarith
  have hlogZ : 0 < Real.log (scaleZ ε x) := Real.log_pos hZ1
  obtain ⟨hc, -, -, -, -⟩ := h
  have hexp : expo ε x b = Real.log (b : ℝ) / Real.log (scaleZ ε x) := rfl
  rw [hexp] at hc
  have h1 : ((1+7*(2*(1/16-1/10^5)))/15 - ε) * Real.log (scaleZ ε x) ≤ Real.log (b : ℝ) := by
    have h2 := mul_le_mul_of_nonneg_right hc hlogZ.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hlogZ)] at h2
  have hlogb : 0 < Real.log (b : ℝ) := by
    have h3 : 0 < ((1+7*(2*(1/16-1/10^5)))/15 - ε) * Real.log (scaleZ ε x) := by
      have : (0:ℝ) < (1+7*(2*(1/16-1/10^5)))/15 - ε := by linarith
      positivity
    linarith
  have hbpos : (0:ℝ) < b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · rw [h0] at hlogb; simp at hlogb
    · exact_mod_cast h0
  have hZc : 0 < scaleZ ε x ^ ((1+7*(2*(1/16-1/10^5)))/15 - ε) :=
    Real.rpow_pos_of_pos hZ0 _
  rw [← Real.log_rpow (x := scaleZ ε x)
    (y := (1+7*(2*(1/16-1/10^5)))/15 - ε) hZ0] at h1
  exact (Real.log_le_log_iff hZc hbpos).mp h1


/-! ### Stage 6: the leaf's integral over `α` is the integral of the density over `a` -/

/-- For a fixed `b`, the integral over `α ∈ [1/10, 1/2]` of the leaf's E2 integrand is the integral
over `a ∈ [Z^(1/10), Z^(1/2)]` of the density `Φ_b` at `a = Z^α`. Both the indicator and the
Buchstab argument agree: `(s - α - β)/β = log (m/(a b)) / log b` (`two_pair_arg_eq`) and
`dα / α = da / (a log a)`. -/
theorem per_b_integral_eq {ω : ℝ → ℝ} {ε x : ℝ} (hZ1 : 1 < scaleZ ε x) {m b : ℕ}
    (hm : 0 < m) (hb2 : 2 ≤ b) :
    (∫ α in (1/10:ℝ)..(1/2:ℝ),
        if lowerTwoDiscarded ε α (expo ε x b) then
          ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
        else 0) =
      ∫ a in (scaleZ ε x) ^ (1/10:ℝ)..(scaleZ ε x) ^ (1/2:ℝ),
        if lowerTwoDiscarded ε (Real.log a / Real.log (scaleZ ε x)) (expo ε x b) then
          ω (Real.log ((m : ℝ) / (a * (b : ℝ))) / Real.log (b : ℝ)) /
            (a * Real.log a)
        else 0 := by
  have hZ0 : 0 < scaleZ ε x := by linarith
  have hL : Real.log (scaleZ ε x) ≠ 0 := ne_of_gt (Real.log_pos hZ1)
  have hb1 : (2:ℝ) ≤ b := by exact_mod_cast hb2
  have hlb : Real.log (b : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by linarith : (1:ℝ) < b))
  have h := integral_log_subst hZ1
    (fun α : ℝ => if lowerTwoDiscarded ε α (expo ε x b) then
        ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
      else 0)
  rw [← h]
  refine intervalIntegral.integral_congr fun a ha => ?_
  have hmin : min ((scaleZ ε x) ^ (1/10:ℝ)) ((scaleZ ε x) ^ (1/2:ℝ)) = (scaleZ ε x) ^ (1/10:ℝ) :=
    min_eq_left (Real.rpow_le_rpow_of_exponent_le hZ1.le (by norm_num))
  have ha_ge : (scaleZ ε x) ^ (1/10:ℝ) ≤ a := by
    rw [Set.uIcc, hmin] at ha
    exact ha.1
  have hZt : (1:ℝ) < (scaleZ ε x) ^ (1/10:ℝ) := Real.one_lt_rpow hZ1 (by norm_num)
  have ha1 : (0:ℝ) < a := by linarith
  have ha_gt : (1:ℝ) < a := by linarith
  have hla : Real.log a ≠ 0 := ne_of_gt (Real.log_pos ha_gt)
  have hane : a ≠ 0 := ne_of_gt ha1
  simp only [expo]
  by_cases hind : lowerTwoDiscarded ε (Real.log a / Real.log (scaleZ ε x))
      (Real.log (b : ℝ) / Real.log (scaleZ ε x))
  · simp only [hind, if_true]
    have harg : (Real.log (m : ℝ) / Real.log (scaleZ ε x) - Real.log a / Real.log (scaleZ ε x) -
          Real.log (b : ℝ) / Real.log (scaleZ ε x)) / (Real.log (b : ℝ) / Real.log (scaleZ ε x)) =
        Real.log ((m : ℝ) / (a * (b : ℝ))) / Real.log (b : ℝ) := by
      refine two_pair_arg_eq (Z := scaleZ ε x) ?_ ?_ ?_ ?_
      · exact Real.log_pos hZ1
      · exact_mod_cast hm
      · exact ha1
      · linarith
    rw [harg]
    have hsplit : Real.log a = (Real.log a / Real.log (scaleZ ε x)) * Real.log (scaleZ ε x) := by
      field_simp
    rw [hsplit] at *
    field_simp
  · simp only [hind, if_false]
    ring

/-! ### Stage 7: which cells can carry a jump -/

/-- If a switch point `t` of the exponent lies in the cell `[log a / log Z, log (a+1) / log Z]`,
then `Z ^ t` lies between `a` and `a + 1`. -/
theorem switch_cell {Z t : ℝ} (hZ : 1 < Z) {a : ℕ} (ha : 1 ≤ a)
    (h1 : Real.log (a : ℝ) / Real.log Z ≤ t)
    (h2 : t ≤ Real.log ((a : ℝ) + 1) / Real.log Z) :
    (a : ℝ) ≤ Z ^ t ∧ Z ^ t ≤ (a : ℝ) + 1 := by
  have hL : 0 < Real.log Z := Real.log_pos hZ
  have hZ0 : 0 < Z := by linarith
  have ha0 : (0:ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have e1 : Real.log (a : ℝ) ≤ t * Real.log Z := by
    have h := mul_le_mul_of_nonneg_right h1 hL.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hL)] at h
  have e2 : Real.log (a : ℝ) ≤ Real.log (Z ^ t) := by
    rw [Real.log_rpow hZ0]
    exact e1
  have e3 : (a : ℝ) ≤ Z ^ t :=
    (Real.log_le_log_iff ha0 (Real.rpow_pos_of_pos hZ0 t)).mp e2
  have f1 : t * Real.log Z ≤ Real.log ((a : ℝ) + 1) := by
    have h := mul_le_mul_of_nonneg_right h2 hL.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hL)] at h
  have f2 : Real.log (Z ^ t) ≤ Real.log ((a : ℝ) + 1) := by
    rw [Real.log_rpow hZ0]
    exact f1
  have f3 : Z ^ t ≤ (a : ℝ) + 1 :=
    (Real.log_le_log_iff (Real.rpow_pos_of_pos hZ0 t) (by positivity)).mp f2
  exact ⟨e3, f3⟩

/-- The converse form: the index of a cell containing a switch point is the floor of `Z ^ t` or
the floor minus one. At most two integers per switch point, so at most `2 * 14` cells of the sum
carry a jump. -/
theorem switch_cell_floor {Z t : ℝ} (hZ : 1 < Z) {a : ℕ} (ha : 1 ≤ a)
    (h1 : Real.log (a : ℝ) / Real.log Z ≤ t)
    (h2 : t ≤ Real.log ((a : ℝ) + 1) / Real.log Z) :
    Nat.floor (Z ^ t) = a ∨ Nat.floor (Z ^ t) = a + 1 := by
  obtain ⟨hb1, hb2⟩ := switch_cell hZ ha h1 h2
  have hle : a ≤ Nat.floor (Z ^ t) := Nat.le_floor hb1
  have hlt : Nat.floor (Z ^ t) < a + 2 := by
    have hltR : ((Nat.floor (Z ^ t) : ℕ) : ℝ) < ((a + 2 : ℕ) : ℝ) := by
      have h := Nat.floor_le (show (0:ℝ) ≤ Z ^ t by positivity)
      push_cast
      linarith
    exact_mod_cast hltR
  omega


/-- Only finitely many cells of the sum carry a jump. If each index in `P` has a switch point `t`
of `T` in its cell, then those indices are the floor of `Z ^ t` or one less (`switch_cell_floor`),
so there are at most `2 * T.card` of them: with the fourteen switch points of `sect_same`, at
most `28`. The predicate is a variable so that its argument stays a natural number. -/
theorem bad_cell_count {Z : ℝ} (hZ : 1 < Z) (T : Finset ℝ) (P : ℕ → Prop)
    (hP : ∀ a : ℕ, P a → ∃ t : ℝ, t ∈ T ∧
      Real.log (a : ℝ) / Real.log Z ≤ t ∧ t ≤ Real.log ((a : ℝ) + 1) / Real.log Z)
    {A B : ℕ} (hA : 1 ≤ A) :
    ((Finset.Ioc A B).filter P).card ≤ 2 * T.card := by
  set S : Finset ℕ := (T.image (fun t => Nat.floor (Z ^ t))) ∪
    (T.image (fun t => Nat.floor (Z ^ t) - 1)) with hS
  have hsub : (Finset.Ioc A B).filter P ⊆ S := by
    intro a ha
    obtain ⟨hain, hPa⟩ := Finset.mem_filter.mp ha
    obtain ⟨t, htT, h1, h2⟩ := hP a hPa
    have haA : 1 ≤ a := le_trans hA (le_of_lt (Finset.mem_Ioc.mp hain).1)
    have hfl := switch_cell_floor hZ haA h1 h2
    rw [hS]
    simp only [Finset.mem_union, Finset.mem_image]
    rcases hfl with h | h
    · exact Or.inl ⟨t, htT, h⟩
    · exact Or.inr ⟨t, htT, by omega⟩
  calc ((Finset.Ioc A B).filter P).card ≤ S.card := Finset.card_le_card hsub
    _ ≤ (T.image (fun t => Nat.floor (Z ^ t))).card +
          (T.image (fun t => Nat.floor (Z ^ t) - 1)).card := Finset.card_union_le _ _
    _ ≤ T.card + T.card := by
        have h1 := Finset.card_image_le (s := T) (f := fun t => Nat.floor (Z ^ t))
        have h2 := Finset.card_image_le (s := T) (f := fun t => Nat.floor (Z ^ t) - 1)
        omega
    _ = 2 * T.card := by ring


/-! ### Stage 8: the density vanishes outside the support -/

/-- The density is zero to the left of `b`: `E₂` needs `β ≤ α`, i.e. `b ≤ a`. This is what lets
the sum over `Ioc b M` be replaced by a sum over the aligned integer range, since `support_ge`
puts every admissible `b` above `Z ^ (c₁ - ε) > Z ^ (1/10)`. -/
theorem density_zero_of_lt {ε Z : ℝ} (hZ : 1 < Z) (ω : ℝ → ℝ) {m a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    (if lowerTwoDiscarded ε (Real.log a / Real.log Z) (Real.log b / Real.log Z) then
        ω (Real.log (m / (a * b)) / Real.log b) / (a * Real.log a) else 0) = 0 := by
  rw [if_neg]
  intro h
  obtain ⟨-, hba, -, -, -⟩ := h
  have hL : 0 < Real.log Z := Real.log_pos hZ
  have h1 : Real.log b ≤ Real.log a := by
    have h2 := mul_le_mul_of_nonneg_right hba hL.le
    have h3 : Real.log a / Real.log Z * Real.log Z = Real.log a :=
      div_mul_cancel₀ _ (ne_of_gt hL)
    have h4 : Real.log b / Real.log Z * Real.log Z = Real.log b :=
      div_mul_cancel₀ _ (ne_of_gt hL)
    linarith
  have h3 : b ≤ a := (Real.log_le_log_iff hb ha).mp h1
  linarith

/-- The density is zero to the right of `α = 1/2`: `E₂` needs `α ≤ 1/2`. So a summand with
`a > Z ^ (1/2)` vanishes, and the sum can stop at `⌊Z ^ (1/2)⌋`. -/
theorem density_zero_of_half_lt {ε Z : ℝ} (hZ : 1 < Z) (ω : ℝ → ℝ) {m a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hα : 1/2 < Real.log a / Real.log Z) :
    (if lowerTwoDiscarded ε (Real.log a / Real.log Z) (Real.log b / Real.log Z) then
        ω (Real.log (m / (a * b)) / Real.log b) / (a * Real.log a) else 0) = 0 := by
  rw [if_neg]
  intro h
  obtain ⟨-, -, hle, -, -⟩ := h
  linarith




/-! ### Stage 9: per cell oscillation of the density in the integer variable -/

/-- The density `Φ_b` of `leaf_two_pair_riemann_first` in the integer variable `t`:
`[E₂] ω (log (m/(t b)) / log b) / (t log t)`. -/
private theorem density_abs_le {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z β : ℝ} {m t : ℝ} {b : ℕ} (ht : 2 ≤ t) (hb : 2 ≤ b) :
    abs (if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
        ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0) ≤
      1 / (t * Real.log t) := by
  have ht0 : (0:ℝ) < t := by linarith
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hpos : (0:ℝ) < t * Real.log t := by positivity
  have hw1 : ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) ≤ 1 :=
    LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz _
  have hw0 : 0 ≤ ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) :=
    Decomp514a.two_density_buchstab_nonneg hω hz _
  by_cases h : lowerTwoDiscarded ε (Real.log t / Real.log Z) β
  · rw [if_pos h, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith, hw1⟩) hpos.le
  · rw [if_neg h, abs_zero]
    positivity

/-- The crude cell oscillation: on the cell `[a, a+1]` the density moves by at most
`2 / (a log a)`, with no condition on the discarded region or on the Buchstab argument. -/
private theorem cell_osc_crude {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z β : ℝ} {m t : ℝ} {b : ℕ} (hb : 2 ≤ b) {a : ℕ} (ha : 2 ≤ a)
    (ht1 : (a : ℝ) ≤ t) (ht2 : t ≤ (a : ℝ) + 1) :
    abs ((if lowerTwoDiscarded ε (Real.log ((a : ℝ) + 1) / Real.log Z) β then
        ω (Real.log (m / (((a : ℝ) + 1) * (b : ℝ))) / Real.log (b : ℝ)) /
          (((a : ℝ) + 1) * Real.log ((a : ℝ) + 1)) else 0) -
      (if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
        ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0)) ≤
      2 / ((a : ℝ) * Real.log a) := by
  have ha2 : (2:ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0:ℝ) < a := by linarith
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  have ht2 : (2:ℝ) ≤ t := le_trans ha2 ht1
  have ha1 : (2:ℝ) ≤ (a:ℝ) + 1 := by linarith
  have h1 := density_abs_le hω hz (ε := ε) (Z := Z) (β := β) (m := m) (b := b) ha1 hb
  have h2 := density_abs_le hω hz (ε := ε) (Z := Z) (β := β) (m := m) (b := b) ht2 hb
  -- monotonicity of `x log x` on `[2, ∞)`
  have hmono : ∀ x y : ℝ, 2 ≤ x → x ≤ y → x * Real.log x ≤ y * Real.log y := by
    intro x y hx hxy
    have hx0 : (0:ℝ) < x := by linarith
    have hl : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hlxy : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
    have hy0 : (0:ℝ) ≤ y := by linarith
    calc x * Real.log x ≤ y * Real.log x := by
          exact mul_le_mul_of_nonneg_right hxy hl
      _ ≤ y * Real.log y := by
          exact mul_le_mul_of_nonneg_left hlxy hy0
  have hbase : (0:ℝ) < a * Real.log a := by positivity
  have hle1 : 1 / (((a:ℝ) + 1) * Real.log ((a:ℝ) + 1)) ≤ 1 / (a * Real.log a) :=
    one_div_le_one_div_of_le hbase (hmono a ((a:ℝ)+1) ha2 (by linarith))
  have hle2 : 1 / (t * Real.log t) ≤ 1 / (a * Real.log a) :=
    one_div_le_one_div_of_le hbase (hmono a t ha2 ht1)
  have htri : abs ((if lowerTwoDiscarded ε (Real.log ((a : ℝ) + 1) / Real.log Z) β then
        ω (Real.log (m / (((a : ℝ) + 1) * (b : ℝ))) / Real.log (b : ℝ)) /
          (((a : ℝ) + 1) * Real.log ((a : ℝ) + 1)) else 0) -
      (if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
        ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0)) ≤
      1 / (((a:ℝ) + 1) * Real.log ((a:ℝ) + 1)) + 1 / (t * Real.log t) := by
    refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
    · have h1' := abs_le.mp h1
      have h2' := abs_le.mp h2
      linarith [h1'.2, h2'.1]
    · have h1' := abs_le.mp h1
      have h2' := abs_le.mp h2
      linarith [h1'.1, h2'.2]
  have hfin : 1 / (((a:ℝ) + 1) * Real.log ((a:ℝ) + 1)) + 1 / (t * Real.log t) ≤
      2 / ((a:ℝ) * Real.log a) := by
    have e : 1 / ((a:ℝ) * Real.log a) + 1 / ((a:ℝ) * Real.log a) = 2 / ((a:ℝ) * Real.log a) := by ring
    linarith
  linarith [htri, hfin]



/-! ### Stage 10: the discarded region is constant on a cell with no switch point -/

/-- P0069 page 51: if none of the fourteen switch points of the discarded region `E₂` lies in
`[α, α']`, then the region takes the same value at `α` and at `α'`. This is `sect_same` with its
twelve atom-wise transfers read off from the absence of the corresponding switch point. -/
private theorem cell_region_const {ε β α α' : ℝ} (hα : α ≤ α')
    (h1 : ¬(α ≤ β ∧ β ≤ α'))
    (h2 : ¬(α ≤ 1/2 ∧ (1/2 : ℝ) ≤ α'))
    (h3 : ¬(α ≤ 1 - 2*β ∧ 1 - 2*β ≤ α'))
    (h4 : ¬(α ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β ∧
            1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β ≤ α'))
    (h5 : ¬(α ≤ (2 + 2*(1/16-1/10^5) - ε - 7*β)/4 ∧
            (2 + 2*(1/16-1/10^5) - ε - 7*β)/4 ≤ α'))
    (h6 : ¬(α ≤ 1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β ∧
            1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β ≤ α'))
    (h7 : ¬(α ≤ (2 + 2*(1/16-1/10^5) - ε - 5*β)/4 ∧
            (2 + 2*(1/16-1/10^5) - ε - 5*β)/4 ≤ α'))
    (h8 : ¬(α ≤ 1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β ∧
            1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β ≤ α'))
    (h10 : ¬(α ≤ 2*β - 2*(1/16-1/10^5) + ε ∧ 2*β - 2*(1/16-1/10^5) + ε ≤ α'))
    (h11 : ¬(α ≤ (36*(2*(1/16-1/10^5)) - 2)/11 - ε ∧ (36*(2*(1/16-1/10^5)) - 2)/11 - ε ≤ α'))
    (h12a : ¬(α ≤ (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4 ∧
              (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4 ≤ α'))
    (h12b : ¬(α ≤ (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4 ∧
              (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4 ≤ α'))
    (h13a : ¬(α ≤ (2 - (2*(1/16-1/10^5) - ε) - β)/4 ∧
              (2 - (2*(1/16-1/10^5) - ε) - β)/4 ≤ α'))
    (h13b : ¬(α ≤ (2 + (2*(1/16-1/10^5) - ε) - β)/4 ∧
              (2 + (2*(1/16-1/10^5) - ε) - β)/4 ≤ α')) :
    (lowerTwoDiscarded ε α β ↔ lowerTwoDiscarded ε α' β) := by
  -- the atom-wise transfers
  have e1 : β ≤ α ↔ β ≤ α' := le_iff_of_not_switch' hα h1
  have e2 : α ≤ 1/2 ↔ α' ≤ 1/2 := le_iff_of_not_switch hα h2
  have e3 : α + 2*β ≤ 1 ↔ α' + 2*β ≤ 1 := by
    have a1 : (α + 2*β ≤ 1) ↔ (α ≤ 1 - 2*β) := by constructor <;> intro h <;> linarith
    have a2 : (α' + 2*β ≤ 1) ↔ (α' ≤ 1 - 2*β) := by constructor <;> intro h <;> linarith
    exact a1.trans ((le_iff_of_not_switch hα h3).trans a2.symm)
  have e4 : α + 2*β ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε ↔
      α' + 2*β ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε := by
    have a1 : (α + 2*β ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε) ↔
        (α ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β) := by
      constructor <;> intro h <;> linarith
    have a2 : (α' + 2*β ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε) ↔
        (α' ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β) := by
      constructor <;> intro h <;> linarith
    exact a1.trans ((le_iff_of_not_switch hα h4).trans a2.symm)
  have e5 : 4*α + 7*β ≤ 2+2*(1/16-1/10^5)-ε ↔ 4*α' + 7*β ≤ 2+2*(1/16-1/10^5)-ε := by
    have a1 : (4*α + 7*β ≤ 2+2*(1/16-1/10^5)-ε) ↔
        (α ≤ (2 + 2*(1/16-1/10^5) - ε - 7*β)/4) := by
      constructor <;> intro h <;> linarith
    have a2 : (4*α' + 7*β ≤ 2+2*(1/16-1/10^5)-ε) ↔
        (α' ≤ (2 + 2*(1/16-1/10^5) - ε - 7*β)/4) := by
      constructor <;> intro h <;> linarith
    exact a1.trans ((le_iff_of_not_switch hα h5).trans a2.symm)
  have e6 : 1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β ↔
      1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α' + β := by
    have a1 : (1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β) ↔
        (1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β ≤ α) := by
      constructor <;> intro h <;> linarith
    have a2 : (1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α' + β) ↔
        (1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β ≤ α') := by
      constructor <;> intro h <;> linarith
    exact a1.trans ((le_iff_of_not_switch' hα h6).trans a2.symm)
  have e7 : 4*α + 5*β ≤ 2+2*(1/16-1/10^5)-ε ↔ 4*α' + 5*β ≤ 2+2*(1/16-1/10^5)-ε := by
    have a1 : (4*α + 5*β ≤ 2+2*(1/16-1/10^5)-ε) ↔
        (α ≤ (2 + 2*(1/16-1/10^5) - ε - 5*β)/4) := by
      constructor <;> intro h <;> linarith
    have a2 : (4*α' + 5*β ≤ 2+2*(1/16-1/10^5)-ε) ↔
        (α' ≤ (2 + 2*(1/16-1/10^5) - ε - 5*β)/4) := by
      constructor <;> intro h <;> linarith
    exact a1.trans ((le_iff_of_not_switch hα h7).trans a2.symm)
  have e8 : 1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β ↔
      1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α' + β := by
    have a1 : (1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β) ↔
        (1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β ≤ α) := by
      constructor <;> intro h <;> linarith
    have a2 : (1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α' + β) ↔
        (1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β ≤ α') := by
      constructor <;> intro h <;> linarith
    exact a1.trans ((le_iff_of_not_switch' hα h8).trans a2.symm)
  have e11 : 2*β - (2*(1/16-1/10^5)) + ε ≤ α ↔ 2*β - (2*(1/16-1/10^5)) + ε ≤ α' :=
    le_iff_of_not_switch' hα h10
  have e12 : α ≤ (36*(2*(1/16-1/10^5))-2)/11-ε ↔ α' ≤ (36*(2*(1/16-1/10^5))-2)/11-ε :=
    le_iff_of_not_switch hα h11
  have e13 : |4*α + 3*β - 2| ≤ 2*(1/16-1/10^5)-ε ↔ |4*α' + 3*β - 2| ≤ 2*(1/16-1/10^5)-ε := by
    have a1 : |4*α + 3*β - 2| ≤ 2*(1/16-1/10^5)-ε ↔
        (α ≤ (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4 ∧
          (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4 ≤ α) := by
      rw [abs_le]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    have a2 : |4*α' + 3*β - 2| ≤ 2*(1/16-1/10^5)-ε ↔
        (α' ≤ (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4 ∧
          (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4 ≤ α') := by
      rw [abs_le]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [a1, a2]
    exact and_congr (le_iff_of_not_switch hα h12b) (le_iff_of_not_switch' hα h12a)
  have e14 : |4*α + β - 2| ≤ 2*(1/16-1/10^5)-ε ↔ |4*α' + β - 2| ≤ 2*(1/16-1/10^5)-ε := by
    have a1 : |4*α + β - 2| ≤ 2*(1/16-1/10^5)-ε ↔
        (α ≤ (2 + (2*(1/16-1/10^5) - ε) - β)/4 ∧
          (2 - (2*(1/16-1/10^5) - ε) - β)/4 ≤ α) := by
      rw [abs_le]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    have a2 : |4*α' + β - 2| ≤ 2*(1/16-1/10^5)-ε ↔
        (α' ≤ (2 + (2*(1/16-1/10^5) - ε) - β)/4 ∧
          (2 - (2*(1/16-1/10^5) - ε) - β)/4 ≤ α') := by
      rw [abs_le]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [a1, a2]
    exact and_congr (le_iff_of_not_switch hα h13b) (le_iff_of_not_switch' hα h13a)
  exact sect_same hα e1 e2 e3 e4 e5 e6 e7 e8 e11 e12 e13 e14



/-- The Buchstab argument `log (m/(t b)) / log b` is nonincreasing in `t > 0`. -/
private theorem two_pair_arg_anti {m b t t' : ℝ} (hm : 0 < m) (hb : 1 < b)
    (ht : 0 < t) (htt : t ≤ t') :
    Real.log (m / (t' * b)) / Real.log b ≤ Real.log (m / (t * b)) / Real.log b := by
  have hb0 : 0 < b := by linarith
  have hlb : 0 < Real.log b := Real.log_pos hb
  have ht'0 : 0 < t' := lt_of_lt_of_le ht htt
  have htbh : 0 < t * b := by positivity
  have htb'h : 0 < t' * b := by positivity
  have hle : m / (t' * b) ≤ m / (t * b) := by
    apply div_le_div_of_nonneg_left hm.le htbh
    exact mul_le_mul_of_nonneg_right htt hb0.le
  have hlt : Real.log (m / (t' * b)) ≤ Real.log (m / (t * b)) :=
    Real.log_le_log (by positivity) hle
  exact div_le_div_of_nonneg_right hlt hlb.le

/-- The good cell: on a cell on which the discarded region does not change and the Buchstab
argument stays at least one, the density moves by at most `16 / (a^2 log a)`. This is
`two_pair_cell_osc` applied at the two endpoints of the cell. -/
private theorem cell_osc_good {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z β : ℝ} {m t : ℝ} {b : ℕ} (hb : 2 ≤ b) (hm : 0 < m) {a : ℕ} (ha : 4 ≤ a)
    (ht1 : (a : ℝ) ≤ t) (ht2 : t ≤ (a : ℝ) + 1)
    (hreg : lowerTwoDiscarded ε (Real.log ((a : ℝ) + 1) / Real.log Z) β ↔
            lowerTwoDiscarded ε (Real.log t / Real.log Z) β)
    (hu : 1 ≤ Real.log (m / (((a : ℝ) + 1) * (b : ℝ))) / Real.log (b : ℝ)) :
    abs ((if lowerTwoDiscarded ε (Real.log ((a : ℝ) + 1) / Real.log Z) β then
        ω (Real.log (m / (((a : ℝ) + 1) * (b : ℝ))) / Real.log (b : ℝ)) /
          (((a : ℝ) + 1) * Real.log ((a : ℝ) + 1)) else 0) -
      (if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
        ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0)) ≤
      16 / ((a : ℝ) ^ 2 * Real.log a) := by
  have haR : (4:ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (2:ℝ) ≤ b := by exact_mod_cast hb
  have ha0 : (0:ℝ) < a := by linarith
  have ha1pos : (0:ℝ) < (a:ℝ) + 1 := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by linarith : (0:ℝ) < a) ht1
  by_cases hD : lowerTwoDiscarded ε (Real.log ((a : ℝ) + 1) / Real.log Z) β
  · have hDt : lowerTwoDiscarded ε (Real.log t / Real.log Z) β := hreg.mp hD
    simp only [hD, hDt, if_true]
    have hu2 : 1 ≤ Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ) :=
      le_trans hu (two_pair_arg_anti hm (by linarith : (1:ℝ) < b) ht0 ht2)
    have h1 := two_pair_cell_osc hω hz (m := m) (b := (b:ℝ)) (a := (a:ℝ))
      (t := (a:ℝ) + 1) hbR hm haR (by linarith) le_rfl hu
    have h2 := two_pair_cell_osc hω hz (m := m) (b := (b:ℝ)) (a := (a:ℝ))
      (t := t) hbR hm haR ht1 ht2 hu2
    have hpos : (0:ℝ) < (a:ℝ) ^ 2 * Real.log a := by
      have : (0:ℝ) < Real.log a := Real.log_pos (by linarith)
      positivity
    have e : ω (Real.log (m / (((a : ℝ) + 1) * (b : ℝ))) / Real.log (b : ℝ)) /
          (((a : ℝ) + 1) * Real.log ((a : ℝ) + 1)) -
        ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) =
        (ω (Real.log (m / (((a : ℝ) + 1) * (b : ℝ))) / Real.log (b : ℝ)) /
          (((a : ℝ) + 1) * Real.log ((a : ℝ) + 1)) -
          ω (Real.log (m / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            ((a : ℝ) * Real.log a)) +
        (ω (Real.log (m / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) / ((a : ℝ) * Real.log a) -
          ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)) := by
      ring
    rw [e]
    have h3 : abs (ω (Real.log (m / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
        ((a : ℝ) * Real.log a) -
          ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)) =
        abs (ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) -
          ω (Real.log (m / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            ((a : ℝ) * Real.log a)) := abs_sub_comm _ _
    have h4 := abs_add_le (ω (Real.log (m / (((a : ℝ) + 1) * (b : ℝ))) / Real.log (b : ℝ)) /
          (((a : ℝ) + 1) * Real.log ((a : ℝ) + 1)) -
          ω (Real.log (m / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            ((a : ℝ) * Real.log a))
      (ω (Real.log (m / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) / ((a : ℝ) * Real.log a) -
        ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t))
    rw [h3] at h4
    have hfin : 8 / ((a : ℝ) ^ 2 * Real.log a) + 8 / ((a : ℝ) ^ 2 * Real.log a) =
        16 / ((a : ℝ) ^ 2 * Real.log a) := by ring
    linarith [h1, h2, h4]
  · have hDt : ¬ lowerTwoDiscarded ε (Real.log t / Real.log Z) β :=
      fun h => hD (hreg.mpr h)
    simp only [hD, hDt, if_false, sub_zero, abs_zero]
    have : (0:ℝ) < Real.log a := Real.log_pos (by linarith)
    positivity



/-! ### Stage 11: measurability, integrability and two summation bounds -/

/-- Buchstab's function is measurable: continuous off the single point `1`. -/
private theorem measurable_buchstab {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω) : Measurable ω := by
  refine measurable_of_continuousOn_compl_singleton (1 : ℝ) ?_
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  rcases lt_or_gt_of_ne hx with h | h
  · have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhds x] ω := by
      filter_upwards [isOpen_Iio.mem_nhds h] with y hy
      exact (hz y hy).symm
    exact (continuousAt_const.congr hev).continuousWithinAt
  · exact (hω.1.continuousAt (Ici_mem_nhds h)).continuousWithinAt

/-- The density is measurable. -/
private theorem measurable_density {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    (ε Z β : ℝ) (m : ℝ) (b : ℕ) :
    Measurable (fun t : ℝ => if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
        ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0) := by
  have hωm : Measurable ω := measurable_buchstab hω hz
  have hs : MeasurableSet {t : ℝ | lowerTwoDiscarded ε (Real.log t / Real.log Z) β} := by
    unfold lowerTwoDiscarded upperPairRegion
    measurability
  have hf : Measurable (fun t : ℝ =>
      ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)) := by
    measurability
  exact Measurable.ite hs hf measurable_const

/-- The density is interval integrable on `[u, v]` for `u ≥ 2`. -/
private theorem intervalIntegrable_density {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z β : ℝ} {m : ℝ} {b : ℕ} (hb : 2 ≤ b) {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    IntervalIntegrable (fun t : ℝ => if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
        ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0)
      volume u v := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le huv]
  have hmeas := (measurable_density hω hz ε Z β m b).aestronglyMeasurable (μ := volume)
  refine MeasureTheory.Integrable.of_bound hmeas.restrict 1 ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
  have hx2 : 2 ≤ x := le_trans hu (le_of_lt hx.1)
  have hb1 := density_abs_le hω hz (ε := ε) (Z := Z) (β := β) (m := m) (b := b) hx2 hb
  have hx0 : (0:ℝ) < x := by linarith
  have hl : (1/2:ℝ) ≤ Real.log x := by
    have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx2
    have h2' : (1/2:ℝ) ≤ Real.log 2 := by
      have h := Real.log_two_gt_d9
      linarith
    linarith
  have hden : (1:ℝ) ≤ x * Real.log x := by nlinarith [hx2, hl]
  have hpos : (0:ℝ) < x * Real.log x := by nlinarith [hx0, hl]
  have hle : 1 / (x * Real.log x) ≤ 1 := by
    rw [div_le_one hpos]
    exact hden
  rw [Real.norm_eq_abs]
  exact hb1.trans hle

/-- An interval integral of a function that vanishes on the open interval is zero: the end points
carry no mass. -/
private theorem integral_eq_zero_of_open {f : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (h : ∀ x, u < x → x < v → f x = 0) : (∫ x in u..v, f x) = 0 := by
  rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_,
    intervalIntegral.integral_zero]
  rw [MeasureTheory.ae_iff]
  have hsub : {x : ℝ | ¬(x ∈ Set.uIoc u v → f x = 0)} ⊆ {v} := by
    intro x hx
    simp only [Set.mem_setOf_eq, not_imp] at hx
    obtain ⟨hxin, hfx⟩ := hx
    have hxv : x = v := by
      by_contra hne
      rw [Set.uIoc_of_le huv] at hxin
      exact hfx (h x hxin.1 (lt_of_le_of_ne hxin.2 hne))
    simp [hxv]
  exact measure_mono_null hsub (measure_singleton v)

/-- `∑_{A < a ≤ B} 1 / a^2 ≤ 1 / A` for `A ≥ 1`. -/
private theorem sum_inv_sq_le {A B : ℕ} (hA : 1 ≤ A) :
    (∑ a ∈ Finset.Ioc A B, 1 / ((a : ℝ) ^ 2)) ≤ 1 / (A : ℝ) := by
  have hA0 : (0:ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  rcases le_or_gt A B with h | h
  · have := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := A) (n := B) (by omega) h
    have he : (∑ a ∈ Finset.Ioc A B, 1 / ((a : ℝ) ^ 2)) =
        ∑ a ∈ Finset.Ioc A B, (((a : ℝ)) ^ 2)⁻¹ := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [one_div]
    rw [he]
    refine this.trans ?_
    have hB0 : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
    have hle : 0 ≤ ((B:ℝ))⁻¹ := by positivity
    rw [← one_div]
    linarith
  · have hempty : Finset.Ioc A B = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    positivity

/-- `∑_{A < a ≤ B} 1 / (a^2 log a) ≤ 2 / (A log A)` for `A ≥ 2`. -/
private theorem inv_sq_log_sum_le {A B : ℕ} (hA : 2 ≤ A) :
    (∑ a ∈ Finset.Ioc A B, 1 / ((a : ℝ) ^ 2 * Real.log (a : ℝ))) ≤
      2 / ((A : ℝ) * Real.log (A : ℝ)) := by
  have hA0 : (0:ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hA2 : (2:ℝ) ≤ A := by exact_mod_cast hA
  have hlogA : 0 < Real.log (A:ℝ) := by
    have h2 : Real.log 2 ≤ Real.log (A:ℝ) := Real.log_le_log (by norm_num) hA2
    have h2' : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have step : ∀ a ∈ Finset.Ioc A B, 1 / ((a : ℝ) ^ 2 * Real.log (a : ℝ)) ≤
      (1 / Real.log (A:ℝ)) * (1 / ((a : ℝ) ^ 2)) := by
    intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp ha
    have haA : (2:ℝ) ≤ a := by
      have : (A:ℝ) ≤ a := by exact_mod_cast le_of_lt h1
      linarith
    have ha0 : (0:ℝ) < a := by linarith
    have hla : 0 < Real.log (a:ℝ) := by
      have := Real.log_le_log (by norm_num : (0:ℝ) < 2) haA
      have h2' : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    have hlogle : Real.log (A:ℝ) ≤ Real.log (a:ℝ) := by
      apply Real.log_le_log hA0
      exact_mod_cast le_of_lt h1
    have h1' : 1 / ((a : ℝ) ^ 2 * Real.log (a : ℝ)) ≤ 1 / ((a : ℝ) ^ 2 * Real.log (A:ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (0:ℝ) < (a:ℝ)^2 := by positivity
      exact mul_le_mul_of_nonneg_left hlogle this.le
    have h2' : 1 / ((a : ℝ) ^ 2 * Real.log (A:ℝ)) = (1 / Real.log (A:ℝ)) * (1 / ((a : ℝ) ^ 2)) := by
      field_simp
    linarith [h1', h2'.le, h2'.ge]
  calc (∑ a ∈ Finset.Ioc A B, 1 / ((a : ℝ) ^ 2 * Real.log (a : ℝ)))
      ≤ ∑ a ∈ Finset.Ioc A B, (1 / Real.log (A:ℝ)) * (1 / ((a : ℝ) ^ 2)) :=
        Finset.sum_le_sum step
    _ = (1 / Real.log (A:ℝ)) * (∑ a ∈ Finset.Ioc A B, 1 / ((a : ℝ) ^ 2)) := by
        rw [Finset.mul_sum]
    _ ≤ (1 / Real.log (A:ℝ)) * (1 / (A:ℝ)) := by
        apply mul_le_mul_of_nonneg_left (sum_inv_sq_le (by omega)) (by positivity)
    _ ≤ 2 / ((A:ℝ) * Real.log (A:ℝ)) := by
        rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos hA0 hlogA]



/-! ### Stage 12: the switch points as one finset -/

/-- The fourteen switch points of the discarded region `E₂` as a finset. -/
private theorem cell_region_const_auto {ε β α α' : ℝ} (hα : α ≤ α')
    (hno : ∀ τ ∈ ([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset,
        ¬(α ≤ τ ∧ τ ≤ α')) :
    (lowerTwoDiscarded ε α β ↔ lowerTwoDiscarded ε α' β) :=
  cell_region_const hα
    (hno _ (by simp)) (hno _ (by simp)) (hno _ (by simp)) (hno _ (by simp))
    (hno _ (by simp)) (hno _ (by simp)) (hno _ (by simp)) (hno _ (by simp))
    (hno _ (by simp)) (hno _ (by simp)) (hno _ (by simp)) (hno _ (by simp))
    (hno _ (by simp)) (hno _ (by simp))

/-- The good cell oscillation of the density: the discarded region does not change across the cell
and the Buchstab argument does not cross `1`. -/
private theorem cell_osc_density {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z β : ℝ} {m : ℝ} {b : ℕ} (hb : 2 ≤ b) (hm : 0 < m) {a : ℕ} (ha : 4 ≤ a) {t : ℝ}
    (ht1 : (a : ℝ) ≤ t) (ht2 : t ≤ (a : ℝ) + 1)
    (hreg : lowerTwoDiscarded ε (Real.log ((a : ℝ) + 1) / Real.log Z) β ↔
            lowerTwoDiscarded ε (Real.log t / Real.log Z) β)
    (hcase : 1 ≤ Real.log (m / (((a : ℝ) + 1) * (b : ℝ))) / Real.log (b : ℝ) ∨
             Real.log (m / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ) < 1) :
    abs ((if lowerTwoDiscarded ε (Real.log ((a : ℝ) + 1) / Real.log Z) β then
        ω (Real.log (m / (((a : ℝ) + 1) * (b : ℝ))) / Real.log (b : ℝ)) /
          (((a : ℝ) + 1) * Real.log ((a : ℝ) + 1)) else 0) -
      (if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
        ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0)) ≤
      16 / ((a : ℝ) ^ 2 * Real.log a) := by
  have ha0 : (0:ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have haR : (4:ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (1:ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  have hpos : (0:ℝ) < (a:ℝ)^2 * Real.log a := by positivity
  rcases hcase with hu | hlt
  · exact cell_osc_good hω hz hb hm ha ht1 ht2 hreg hu
  · -- the Buchstab argument is below one on the whole cell, so both values vanish
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht1
    have h1 : Real.log (m / (((a:ℝ)+1) * (b:ℝ))) / Real.log (b:ℝ) < 1 :=
      lt_of_le_of_lt (two_pair_arg_anti hm hbR (by linarith) (by linarith)) hlt
    have h2 : Real.log (m / (t * (b:ℝ))) / Real.log (b:ℝ) < 1 :=
      lt_of_le_of_lt (two_pair_arg_anti hm hbR ha0 ht1) hlt
    have e1 : (if lowerTwoDiscarded ε (Real.log ((a:ℝ)+1) / Real.log Z) β then
        ω (Real.log (m / (((a:ℝ)+1) * (b:ℝ))) / Real.log (b:ℝ)) /
          (((a:ℝ)+1) * Real.log ((a:ℝ)+1)) else 0) = 0 := by
      by_cases hD : lowerTwoDiscarded ε (Real.log ((a:ℝ)+1) / Real.log Z) β
      · rw [if_pos hD, hz _ h1]
        ring
      · rw [if_neg hD]
    have e2 : (if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
        ω (Real.log (m / (t * (b:ℝ))) / Real.log (b:ℝ)) / (t * Real.log t) else 0) = 0 := by
      by_cases hD : lowerTwoDiscarded ε (Real.log t / Real.log Z) β
      · rw [if_pos hD, hz _ h2]
        ring
      · rw [if_neg hD]
    rw [e1, e2, sub_zero, abs_zero]
    positivity

/-- Reindexing a sum over `Ioc A B` by `n ↦ n - 1`. -/
private theorem sum_Ioc_shift {A B : ℕ} (hA : 1 ≤ A) (g : ℕ → ℝ) :
    (∑ n ∈ Finset.Ioc A B, g (n - 1)) = ∑ a ∈ Finset.Ioc (A - 1) (B - 1), g a := by
  refine Finset.sum_bij (fun n _ => n - 1) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  · intro n1 hn1 n2 hn2 he
    obtain ⟨h1, _⟩ := Finset.mem_Ioc.mp hn1
    obtain ⟨h3, _⟩ := Finset.mem_Ioc.mp hn2
    omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp ha
    refine ⟨a + 1, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro n hn
    rfl

/-- Reindexing a filtered cardinality over `Ioc A B` by `n ↦ n - 1`. -/
private theorem card_filter_Ioc_shift {A B : ℕ} (hA : 1 ≤ A) (P : ℕ → Prop) :
    ((Finset.Ioc A B).filter (fun n => P (n - 1))).card =
      ((Finset.Ioc (A - 1) (B - 1)).filter P).card := by
  refine Finset.card_bij (fun n _ => n - 1) ?_ ?_ ?_
  · intro n hn
    obtain ⟨hin, hP⟩ := Finset.mem_filter.mp hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hin
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, hP⟩
  · intro n1 hn1 n2 hn2 he
    obtain ⟨hin, _⟩ := Finset.mem_filter.mp hn1
    obtain ⟨h1, _⟩ := Finset.mem_Ioc.mp hin
    omega
  · intro a ha
    obtain ⟨hin, hP⟩ := Finset.mem_filter.mp ha
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hin
    exact ⟨a + 1, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩,
      by simpa using hP⟩, by omega⟩



/-! ### Stage 13: the per-`b` Riemann comparison, sum against integral -/

/-- P0069 page 51 display 5.17, the passage from the sum over the first outer variable to the
integral, for one fixed second variable `b`: the sum over the integers `a` of the E2 density is
the integral over the exponent range, up to `200 / (b log b)`. The sum is taken over the integers
as they stand, cell by cell; on each cell the density moves by `16 / (a^2 log a)`, except on the
at most `28` cells that carry a switch point of the discarded region and the at most `2` cells
that carry the point at which the Buchstab argument crosses one, where the crude bound
`2 / (a log a)` is used. -/
private theorem per_b_riemann {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z β : ℝ} (hZ : 1 < Z) (hZ4 : 4 ≤ Z) (hZ10 : (2:ℝ) ≤ Z ^ (1/10:ℝ)) (hβ : 0 < β)
    {m : ℝ} (hm : 0 < m) {b M : ℕ} (hb : 4 ≤ b) (hbM : b ≤ M)
    (hbZ : Z ^ (1/10:ℝ) ≤ (b:ℝ)) (hbZ2 : (b:ℝ) ≤ Z ^ (1/2:ℝ)) (hM : Z ^ (1/2:ℝ) ≤ (M:ℝ))
    (hβb : β = Real.log (b:ℝ) / Real.log Z) :
    abs ((∑ a ∈ Finset.Ioc b M,
        (if lowerTwoDiscarded ε (Real.log (a:ℝ) / Real.log Z) β then
          ω (Real.log (m / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            ((a : ℝ) * Real.log (a : ℝ)) else 0))
      - (∫ t in (Z ^ (1/10:ℝ))..(Z ^ (1/2:ℝ)),
        (if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
          ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0)))
      ≤ 100 / ((b : ℝ) * Real.log (b : ℝ)) := by
  have hb2 : 2 ≤ b := by omega
  have hbR : (2:ℝ) ≤ b := by exact_mod_cast hb2
  have hb0 : (0:ℝ) < (b:ℝ) := by linarith
  have hb1 : (1:ℝ) < b := by linarith
  have hlb : 0 < Real.log (b:ℝ) := Real.log_pos hb1
  have hZ0 : (0:ℝ) < Z := by linarith
  have hLZ : 0 < Real.log Z := Real.log_pos hZ
  set φ : ℝ → ℝ := fun t => if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
      ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0 with hφ
  -- the switch points and the two kinds of bad cell
  set bad1 : ℕ → Prop := fun a => ∃ τ ∈ ([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset,
      Real.log (a:ℝ) / Real.log Z ≤ τ ∧ τ ≤ Real.log ((a:ℝ)+1) / Real.log Z with hbad1
  set bad2 : ℕ → Prop := fun a =>
      Real.log (a:ℝ) / Real.log Z ≤ Real.log m / Real.log Z - 2*β ∧
      Real.log m / Real.log Z - 2*β ≤ Real.log ((a:ℝ)+1) / Real.log Z with hbad2
  set bad : ℕ → Prop := fun a => bad1 a ∨ bad2 a with hbad
  set δ : ℕ → ℝ := fun n => 16 / (((n:ℝ)-1)^2 * Real.log ((n:ℝ)-1)) +
      (if bad (n-1) then 2 / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)) else 0) with hδ
  -- integrability of the density on the cells
  have hcell : ∀ n : ℕ, b < n → IntervalIntegrable φ volume ((n:ℝ)-1) (n:ℝ) := by
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hnb : (b:ℝ) ≤ (n:ℝ) - 1 := by
      have h1 : b + 1 ≤ n := by omega
      have h2 : (b:ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast h1
      linarith
    have hu2 : 2 ≤ (n:ℝ) - 1 := le_trans hbR hnb
    have hle : (n:ℝ) - 1 ≤ (n:ℝ) := by linarith
    rw [hφ]
    exact intervalIntegrable_density hω hz hb2 hu2 hle
  -- the per cell oscillation
  have hosc : ∀ n : ℕ, b < n → ∀ t ∈ Set.Icc ((n:ℝ)-1) (n:ℝ), abs (φ (n:ℝ) - φ t) ≤ δ n := by
    intro n hn t ht
    have hn1 : 1 ≤ n := by omega
    have hcast : (((n - 1 : ℕ)) : ℝ) = (n:ℝ) - 1 := by
      push_cast [Nat.cast_sub hn1]; ring
    have hcast1 : (((n - 1 : ℕ)) : ℝ) + 1 = (n:ℝ) := by rw [hcast]; ring
    have ha4 : 4 ≤ n - 1 := by omega
    have ha2 : 2 ≤ n - 1 := by omega
    have haR : (4:ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast ha4
    have ha0 : (0:ℝ) < ((n - 1 : ℕ) : ℝ) := by linarith
    have hla : 0 < Real.log (((n - 1 : ℕ)) : ℝ) := Real.log_pos (by linarith)
    have ht1 : (((n - 1 : ℕ)) : ℝ) ≤ t := by rw [hcast]; linarith [ht.1]
    have ht2 : t ≤ (((n - 1 : ℕ)) : ℝ) + 1 := by rw [hcast1]; exact ht.2
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht1
    have hk4 : 1 ≤ n - 1 := by omega
    have hcrude : abs (φ (n:ℝ) - φ t) ≤ 2 / ((((n - 1 : ℕ)) : ℝ) * Real.log (((n - 1 : ℕ)) : ℝ)) := by
      have h := cell_osc_crude hω hz (ε := ε) (Z := Z) (β := β) (m := m) (b := b) hb2
        (a := n - 1) ha2 ht1 ht2
      rw [hcast1] at h
      simpa only [hφ] using h
    rw [hδ]
    beta_reduce
    rw [← hcast]
    by_cases hbc : bad (n-1)
    · rw [if_pos hbc]
      have h2 : (0:ℝ) ≤ 16 / ((((n - 1 : ℕ)) : ℝ) ^ 2 * Real.log (((n - 1 : ℕ)) : ℝ)) :=
        div_nonneg (by norm_num) (by positivity)
      linarith [hcrude]
    · rw [if_neg hbc, add_zero]
      obtain ⟨hb1', hb2'⟩ := not_or.mp hbc
      -- the discarded region does not change across the cell
      have hno : ∀ τ ∈ ([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset,
          ¬(Real.log t / Real.log Z ≤ τ ∧ τ ≤ Real.log ((((n - 1 : ℕ)) : ℝ) + 1) / Real.log Z) := by
        intro τ hτ hτin
        apply hb1'
        exact ⟨τ, hτ, by
          have := div_le_div_of_nonneg_right (Real.log_le_log ha0 ht1) hLZ.le
          linarith [hτin.1], hτin.2⟩
      have hαn : Real.log t / Real.log Z ≤ Real.log ((((n - 1 : ℕ)) : ℝ) + 1) / Real.log Z := by
        rw [hcast1]
        exact div_le_div_of_nonneg_right (Real.log_le_log ht0 ht.2) hLZ.le
      have hreg : lowerTwoDiscarded ε (Real.log ((((n - 1 : ℕ)) : ℝ) + 1) / Real.log Z) β ↔
          lowerTwoDiscarded ε (Real.log t / Real.log Z) β :=
        (cell_region_const_auto (ε := ε) (β := β) hαn hno).symm
      -- the Buchstab argument does not cross one
      have hcase : 1 ≤ Real.log (m / (((((n - 1 : ℕ)) : ℝ) + 1) * (b:ℝ))) / Real.log (b:ℝ) ∨
          Real.log (m / ((((n - 1 : ℕ)) : ℝ) * (b:ℝ))) / Real.log (b:ℝ) < 1 := by
        by_cases hle : Real.log m / Real.log Z - 2*β < Real.log (((n - 1 : ℕ)) : ℝ) / Real.log Z
        · right
          have harg : Real.log (m / ((((n - 1 : ℕ)) : ℝ) * (b:ℝ))) / Real.log (b:ℝ) =
              (Real.log m / Real.log Z - Real.log (((n - 1 : ℕ)) : ℝ) / Real.log Z - β) / β := by
            rw [hβb]
            exact (two_pair_arg_eq hLZ hm ha0 hb1).symm
          rw [harg, div_lt_one hβ]
          linarith
        · left
          have hstep : Real.log (((n - 1 : ℕ)) : ℝ) / Real.log Z ≤
              Real.log m / Real.log Z - 2*β := not_lt.mp hle
          have hle' : Real.log ((((n - 1 : ℕ)) : ℝ) + 1) / Real.log Z <
              Real.log m / Real.log Z - 2*β := by
            by_contra hcon
            exact hb2' ⟨hstep, not_lt.mp hcon⟩
          have harg : Real.log (m / (((((n - 1 : ℕ)) : ℝ) + 1) * (b:ℝ))) / Real.log (b:ℝ) =
              (Real.log m / Real.log Z - Real.log ((((n - 1 : ℕ)) : ℝ) + 1) / Real.log Z - β) / β := by
            rw [hβb]
            exact (two_pair_arg_eq hLZ hm (by linarith : (0:ℝ) < (((n - 1 : ℕ)) : ℝ) + 1) hb1).symm
          rw [harg, le_div_iff₀ hβ]
          linarith
      have hgood := cell_osc_density hω hz hb2 hm ha4 ht1 ht2 hreg hcase
      rw [hcast1] at hgood
      simpa only [hφ] using hgood
  -- the per cell bounds are nonnegative
  have hδ0 : ∀ n : ℕ, b < n → 0 ≤ δ n := by
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hcast : (((n - 1 : ℕ)) : ℝ) = (n:ℝ) - 1 := by
      push_cast [Nat.cast_sub hn1]; ring
    have ha2 : (2:ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      have : (2:ℕ) ≤ n - 1 := by omega
      exact_mod_cast this
    have ha0 : (0:ℝ) < ((n - 1 : ℕ) : ℝ) := by linarith
    have hla : 0 < Real.log (((n - 1 : ℕ)) : ℝ) := Real.log_pos (by linarith)
    rw [hδ]
    beta_reduce
    rw [← hcast]
    have h1 : (0:ℝ) ≤ 16 / ((((n - 1 : ℕ)) : ℝ) ^ 2 * Real.log (((n - 1 : ℕ)) : ℝ)) :=
      div_nonneg (by norm_num) (by positivity)
    have h2 : (0:ℝ) ≤ if bad (n-1) then 2 / ((((n - 1 : ℕ)) : ℝ) * Real.log (((n - 1 : ℕ)) : ℝ)) else 0 := by
      split_ifs with h
      · exact div_nonneg (by norm_num) (by positivity)
      · norm_num
    linarith
  -- the sum of the per cell bounds
  have hsum1 : (∑ n ∈ Finset.Ioc b M, 16 / (((n:ℝ)-1)^2 * Real.log ((n:ℝ)-1)))
      ≤ 32 / ((b:ℝ) * Real.log (b:ℝ)) := by
    have hshift : (∑ n ∈ Finset.Ioc b M, 16 / (((n:ℝ)-1)^2 * Real.log ((n:ℝ)-1))) =
        ∑ a ∈ Finset.Ioc (b-1) (M-1), 16 / ((a:ℝ)^2 * Real.log (a:ℝ)) := by
      rw [← sum_Ioc_shift (A := b) (B := M) (by omega : 1 ≤ b)
        (fun a => 16 / ((a:ℝ)^2 * Real.log (a:ℝ)))]
      refine Finset.sum_congr rfl fun n hmem => ?_
      obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp hmem
      have hn1 : 1 ≤ n := by omega
      rw [Nat.cast_sub hn1, Nat.cast_one]
    rw [hshift]
    have hstep : (∑ a ∈ Finset.Ioc (b-1) (M-1), 16 / ((a:ℝ)^2 * Real.log (a:ℝ)))
        ≤ (16 / Real.log (b:ℝ)) * (∑ a ∈ Finset.Ioc (b-1) (M-1), 1 / ((a:ℝ)^2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a ha => ?_
      obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp ha
      have haB : b ≤ a := by omega
      have haA : (b:ℝ) ≤ (a:ℝ) := by exact_mod_cast haB
      have ha0 : (0:ℝ) < (a:ℝ) := by linarith
      have ha2 : (2:ℝ) ≤ (a:ℝ) := le_trans hbR haA
      have hlogle : Real.log (b:ℝ) ≤ Real.log (a:ℝ) := Real.log_le_log hb0 haA
      have hla : 0 < Real.log (a:ℝ) := Real.log_pos (by linarith)
      have hden1 : (0:ℝ) < (a:ℝ)^2 * Real.log (a:ℝ) := by positivity
      have hden2 : (0:ℝ) < (a:ℝ)^2 * Real.log (b:ℝ) := by
        have : (0:ℝ) < Real.log (b:ℝ) := hlb
        positivity
      have hmono : (a:ℝ)^2 * Real.log (b:ℝ) ≤ (a:ℝ)^2 * Real.log (a:ℝ) :=
        mul_le_mul_of_nonneg_left hlogle (by positivity)
      have hle : 1 / ((a:ℝ)^2 * Real.log (a:ℝ)) ≤ 1 / ((a:ℝ)^2 * Real.log (b:ℝ)) :=
        one_div_le_one_div_of_le hden2 hmono
      have he : 16 / ((a:ℝ)^2 * Real.log (a:ℝ)) ≤
          16 * (1 / ((a:ℝ)^2 * Real.log (b:ℝ))) := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_left (by norm_num) hden2 hmono
      have he2 : (16 / Real.log (b:ℝ)) * (1 / ((a:ℝ)^2)) =
          16 * (1 / ((a:ℝ)^2 * Real.log (b:ℝ))) := by
        field_simp
      linarith [he, he2.le, he2.ge]
    refine hstep.trans ?_
    have hsq := sum_inv_sq_le (A := b-1) (B := M-1) (by omega : 1 ≤ b - 1)
    have hsq' : (∑ a ∈ Finset.Ioc (b-1) (M-1), 1 / ((a:ℝ)^2)) ≤ 2 / (b:ℝ) := by
      refine hsq.trans ?_
      rw [Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one]
      have hhalf : (b:ℝ) / 2 ≤ (b:ℝ) - 1 := by linarith
      have hmono : 1 / ((b:ℝ) - 1) ≤ 1 / ((b:ℝ) / 2) :=
        one_div_le_one_div_of_le (by linarith) hhalf
      have heq : 1 / ((b:ℝ) / 2) = 2 / (b:ℝ) := by field_simp
      linarith [hmono, heq.le, heq.ge]
    calc (16 / Real.log (b:ℝ)) * (∑ a ∈ Finset.Ioc (b-1) (M-1), 1 / ((a:ℝ)^2))
        ≤ (16 / Real.log (b:ℝ)) * (2 / (b:ℝ)) := by
          apply mul_le_mul_of_nonneg_left hsq' (by positivity)
      _ = 32 / ((b:ℝ) * Real.log (b:ℝ)) := by field_simp; ring
  -- the bad cells
  have hcard1 : ((Finset.Ioc (b-1) (M-1)).filter bad1).card ≤ 28 := by
    have hsub : (Finset.Ioc (b-1) (M-1)).filter bad1 ⊆
        (([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset.image (fun τ : ℝ => Nat.floor (Z ^ τ))) ∪
        (([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset.image (fun τ : ℝ => Nat.floor (Z ^ τ) - 1)) := by
      intro a ha
      obtain ⟨hain, hb⟩ := Finset.mem_filter.mp ha
      obtain ⟨τ, hτ, h1, h2⟩ := hb
      have haA : 1 ≤ a := by
        obtain ⟨hx, -⟩ := Finset.mem_Ioc.mp hain
        omega
      have hfl := switch_cell_floor hZ haA h1 h2
      rcases hfl with h | h
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨τ, hτ, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨τ, hτ, by omega⟩)
    have hcL : (([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset).card ≤ 14 :=
      (List.toFinset_card_le _).trans (le_of_eq rfl)
    calc ((Finset.Ioc (b-1) (M-1)).filter bad1).card
        ≤ ((([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset.image (fun τ : ℝ => Nat.floor (Z ^ τ))) ∪
            (([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset.image (fun τ : ℝ => Nat.floor (Z ^ τ) - 1))).card :=
          Finset.card_le_card hsub
      _ ≤ ((([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset.image (fun τ : ℝ => Nat.floor (Z ^ τ)))).card +
            ((([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset.image (fun τ : ℝ => Nat.floor (Z ^ τ) - 1))).card :=
          Finset.card_union_le _ _
      _ ≤ 14 + 14 := by
          refine Nat.add_le_add ?_ ?_
          · exact Finset.card_image_le.trans hcL
          · exact Finset.card_image_le.trans hcL
      _ = 28 := rfl
  have hcard2 : ((Finset.Ioc (b-1) (M-1)).filter bad2).card ≤ 2 := by
    have hsub : (Finset.Ioc (b-1) (M-1)).filter bad2 ⊆
        ({Nat.floor (Z ^ (Real.log m / Real.log Z - 2*β)),
          Nat.floor (Z ^ (Real.log m / Real.log Z - 2*β)) - 1} : Finset ℕ) := by
      intro a ha
      obtain ⟨hain, hb⟩ := Finset.mem_filter.mp ha
      obtain ⟨hb1, hb2⟩ := hb
      have haA : 1 ≤ a := by
        obtain ⟨hx, -⟩ := Finset.mem_Ioc.mp hain
        omega
      have hfl := switch_cell_floor hZ haA hb1 hb2
      rcases hfl with h | h
      · rw [h]
        exact Finset.mem_insert_self _ _
      · rw [h]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  have hsum2 : (∑ n ∈ Finset.Ioc b M, (if bad (n-1) then
      2 / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)) else 0))
      ≤ 60 / ((b:ℝ) * Real.log (b:ℝ)) := by
    have hshift : (∑ n ∈ Finset.Ioc b M, (if bad (n-1) then
        2 / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)) else 0)) =
        ∑ a ∈ Finset.Ioc (b-1) (M-1), (if bad a then
          2 / ((a:ℝ) * Real.log (a:ℝ)) else 0) := by
      rw [← sum_Ioc_shift (A := b) (B := M) (by omega : 1 ≤ b)
        (fun a => if bad a then 2 / ((a:ℝ) * Real.log (a:ℝ)) else 0)]
      refine Finset.sum_congr rfl fun n hmem => ?_
      obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp hmem
      have hn1 : 1 ≤ n := by omega
      have hcastn : (((n - 1 : ℕ)) : ℝ) = (n:ℝ) - 1 := by
        push_cast [Nat.cast_sub hn1]; ring
      beta_reduce
      by_cases hb' : bad (n - 1)
      · rw [if_pos hb', if_pos hb', hcastn]
      · rw [if_neg hb', if_neg hb']
    rw [hshift]
    rw [← Finset.sum_filter]
    have hterm : ∀ a ∈ (Finset.Ioc (b-1) (M-1)).filter bad,
        2 / ((a:ℝ) * Real.log (a:ℝ)) ≤ 2 / ((b:ℝ) * Real.log (b:ℝ)) := by
      intro a ha
      obtain ⟨hain, hba⟩ := Finset.mem_filter.mp ha
      obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp hain
      have haB : b ≤ a := by omega
      have haA : (b:ℝ) ≤ (a:ℝ) := by exact_mod_cast haB
      have ha0 : (0:ℝ) < (a:ℝ) := by linarith
      have hlogle : Real.log (b:ℝ) ≤ Real.log (a:ℝ) := Real.log_le_log hb0 haA
      have hden : (0:ℝ) < (b:ℝ) * Real.log (b:ℝ) := by positivity
      have hden2 : (b:ℝ) * Real.log (b:ℝ) ≤ (a:ℝ) * Real.log (a:ℝ) :=
        mul_le_mul haA hlogle (le_of_lt hlb) (le_of_lt ha0)
      exact div_le_div_of_nonneg_left (by norm_num) hden hden2
    have hsumle := Finset.sum_le_card_nsmul ((Finset.Ioc (b-1) (M-1)).filter bad)
      (fun a => 2 / ((a:ℝ) * Real.log (a:ℝ))) (2 / ((b:ℝ) * Real.log (b:ℝ))) hterm
    rw [nsmul_eq_mul] at hsumle
    have hcardle : ((Finset.Ioc (b-1) (M-1)).filter bad).card ≤ 30 := by
      have hsub : (Finset.Ioc (b-1) (M-1)).filter bad ⊆
          (Finset.Ioc (b-1) (M-1)).filter bad1 ∪ (Finset.Ioc (b-1) (M-1)).filter bad2 := by
        intro a ha
        obtain ⟨hins, hb⟩ := Finset.mem_filter.mp ha
        rcases hb with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hins, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hins, h⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le ((Finset.Ioc (b-1) (M-1)).filter bad1)
        ((Finset.Ioc (b-1) (M-1)).filter bad2)
      omega
    refine hsumle.trans ?_
    have hstep : ((Finset.Ioc (b-1) (M-1)).filter bad).card * (2 / ((b:ℝ) * Real.log (b:ℝ)))
        ≤ 30 * (2 / ((b:ℝ) * Real.log (b:ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcardle
    have hlast : 30 * (2 / ((b:ℝ) * Real.log (b:ℝ))) =
        60 / ((b:ℝ) * Real.log (b:ℝ)) := by ring
    linarith [hstep, hlast.le, hlast.ge]
  -- the integral identity: the density vanishes outside the exponent range
  have hint_eq : (∫ t in (b:ℝ)..(M:ℝ), φ t) =
      ∫ t in (Z ^ (1/10:ℝ))..(Z ^ (1/2:ℝ)), φ t := by
    have hZ2 : (2:ℝ) ≤ Z ^ (1/2:ℝ) := by
      have h := Real.sqrt_le_sqrt (by linarith : (4:ℝ) ≤ Z)
      have h4 : Real.sqrt 4 = (2:ℝ) := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [h4, Real.sqrt_eq_rpow] at h
      exact h
    have hi1 : IntervalIntegrable φ volume (b:ℝ) (Z ^ (1/2:ℝ)) := by
      rw [hφ]; exact intervalIntegrable_density hω hz hb2 hbR hbZ2
    have hi2 : IntervalIntegrable φ volume (Z ^ (1/2:ℝ)) (M:ℝ) := by
      rw [hφ]; exact intervalIntegrable_density hω hz hb2 hZ2 hM
    have hi3 : IntervalIntegrable φ volume (Z ^ (1/10:ℝ)) (b:ℝ) := by
      rw [hφ]; exact intervalIntegrable_density hω hz hb2 hZ10 hbZ
    have e1 : (∫ t in (Z ^ (1/2:ℝ))..(M:ℝ), φ t) = 0 := by
      refine integral_eq_zero_of_open hM ?_
      intro x hx1 hx2
      have hx0 : 0 < x := lt_trans (Real.rpow_pos_of_pos hZ0 _) hx1
      have hl : Real.log (Z ^ (1/2:ℝ)) < Real.log x := Real.log_lt_log (Real.rpow_pos_of_pos hZ0 _) hx1
      rw [Real.log_rpow hZ0] at hl
      have hα : 1/2 < Real.log x / Real.log Z := by
        rw [lt_div_iff₀ hLZ]; linarith
      rw [hφ]
      simp only
      rw [hβb]
      exact density_zero_of_half_lt hZ ω hx0 hb0 hα
    have e2 : (∫ t in (Z ^ (1/10:ℝ))..(b:ℝ), φ t) = 0 := by
      refine integral_eq_zero_of_open hbZ ?_
      intro x hx1 hx2
      have hx0 : 0 < x := lt_trans (Real.rpow_pos_of_pos hZ0 _) hx1
      rw [hφ]
      simp only
      rw [hβb]
      exact density_zero_of_lt hZ ω hx0 hb0 hx2
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, e1, add_zero]
    rw [← intervalIntegral.integral_add_adjacent_intervals hi3 hi1, e2, zero_add]
  -- assemble
  have hcells := sum_sub_integral_le_of_cell φ δ b hδ0 hcell hosc M hbM
  have hsumδ : (∑ n ∈ Finset.Ioc b M, δ n) ≤ 100 / ((b:ℝ) * Real.log (b:ℝ)) := by
    have hsplit : (∑ n ∈ Finset.Ioc b M, δ n) =
        (∑ n ∈ Finset.Ioc b M, 16 / (((n:ℝ)-1)^2 * Real.log ((n:ℝ)-1))) +
        (∑ n ∈ Finset.Ioc b M, (if bad (n-1) then
          2 / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)) else 0)) := by
      rw [hδ, Finset.sum_add_distrib]
    rw [hsplit]
    have hden : (0:ℝ) < (b:ℝ) * Real.log (b:ℝ) := by positivity
    refine (add_le_add hsum1 hsum2).trans ?_
    have e : 32 / ((b:ℝ) * Real.log (b:ℝ)) + 60 / ((b:ℝ) * Real.log (b:ℝ)) =
        92 / ((b:ℝ) * Real.log (b:ℝ)) := by ring
    rw [e]
    exact div_le_div_of_nonneg_right (by norm_num) hden.le
  calc abs ((∑ a ∈ Finset.Ioc b M,
        (if lowerTwoDiscarded ε (Real.log (a:ℝ) / Real.log Z) β then
          ω (Real.log (m / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            ((a : ℝ) * Real.log (a : ℝ)) else 0))
      - (∫ t in (Z ^ (1/10:ℝ))..(Z ^ (1/2:ℝ)),
        (if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
          ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0)))
      = abs ((∑ a ∈ Finset.Ioc b M, φ a) - (∫ t in (Z ^ (1/10:ℝ))..(Z ^ (1/2:ℝ)), φ t)) := by
        simp only [hφ]
    _ = abs ((∑ a ∈ Finset.Ioc b M, φ a) - (∫ t in (b:ℝ)..(M:ℝ), φ t)) := by rw [hint_eq]
    _ ≤ 100 / ((b:ℝ) * Real.log (b:ℝ)) := hcells.trans hsumδ




/-! ### Stage 14: the leaf's inner sum and inner integral in the `φ_b` form -/

/-- The leaf's inner sum at a fixed `b ≥ 2` is the density sum of `per_b_riemann` times the
outer weight `1 / (b log^2 b)`. -/
private theorem two_pair_inner_sum {ω : ℝ → ℝ} {ε x : ℝ} {m B b : ℕ} (hb : 2 ≤ b) :
    (∑ a ∈ Finset.Ioc b B,
      (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
          ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
        else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log (b : ℝ))))
      = (∑ a ∈ Finset.Ioc b B,
          (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
            ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
              ((a : ℝ) * Real.log (a : ℝ)) else 0)) *
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha2 : 2 ≤ a := by
    obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp ha
    omega
  exact summand_eq_density_weight ω ha2 hb

/-- The leaf's inner integral at a fixed `b ≥ 2` is the integral over the exponent range of
`per_b_riemann`, divided by the outer weight. -/
private theorem two_pair_inner_int {ω : ℝ → ℝ} {ε x : ℝ} {m b : ℕ}
    (hZ : 1 < scaleZ ε x) (hm : 0 < m) (hb : 2 ≤ b) :
    (∫ α in (1/10:ℝ)..(1/2:ℝ),
        if lowerTwoDiscarded ε α (expo ε x b) then
          ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
        else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2)
      = (∫ t in (scaleZ ε x) ^ (1/10:ℝ)..(scaleZ ε x) ^ (1/2:ℝ),
          (if lowerTwoDiscarded ε (Real.log t / Real.log (scaleZ ε x)) (expo ε x b) then
            ω (Real.log ((m : ℝ) / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)
          else 0)) / ((b : ℝ) * Real.log (b : ℝ) ^ 2) := by
  rw [per_b_integral_eq hZ hm hb]



/-! ### Stage 15: the discarded region is empty off the exponent range -/

/-- On `E₂` the second exponent is above `12499/100000`. Hence below that level the region is
empty and the density vanishes identically. -/
private theorem lowerTwo_beta_gt {ε α β : ℝ} (hε8 : ε ≤ 1/10^8)
    (h : lowerTwoDiscarded ε α β) : (12499:ℝ)/100000 < β := by
  obtain ⟨hc, -, -, -, -⟩ := h
  linarith [hε8]

/-- On `E₂` the second exponent is at most `1/2`: above that level the region is empty. -/
private theorem lowerTwo_beta_le_half {ε α β : ℝ} (h : lowerTwoDiscarded ε α β) : β ≤ 1/2 := by
  obtain ⟨-, hba, ha, -, -⟩ := h
  linarith

/-- Below the level `12499/100000` both the density sum and the density integral vanish. -/
private theorem two_pair_per_b_small {ω : ℝ → ℝ} {ε : ℝ} (hε8 : ε ≤ 1/10^8)
    {x : ℝ} (hZ : 0 < Real.log (scaleZ ε x)) {m B b : ℕ}
    (hsmall : Real.log (b:ℝ) / Real.log (scaleZ ε x) ≤ 12499/100000) :
    (∑ a ∈ Finset.Ioc b B,
        (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
          ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            ((a : ℝ) * Real.log (a : ℝ)) else 0)) = 0 ∧
      (∫ α in (1/10:ℝ)..(1/2:ℝ),
        (if lowerTwoDiscarded ε α (expo ε x b) then
          ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
        else 0)) = 0 := by
  have hb0 : expo ε x b = Real.log (b:ℝ) / Real.log (scaleZ ε x) := rfl
  have hnd : ∀ α : ℝ, ¬ lowerTwoDiscarded ε α (expo ε x b) := by
    intro α h
    have := lowerTwo_beta_gt hε8 h
    rw [hb0] at this
    linarith
  constructor
  · refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg (hnd _)]
  · have h0 : (∫ α in (1/10:ℝ)..(1/2:ℝ),
        (if lowerTwoDiscarded ε α (expo ε x b) then
          ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
        else 0)) = ∫ α in (1/10:ℝ)..(1/2:ℝ), (0:ℝ) :=
      intervalIntegral.integral_congr fun α _ => by rw [if_neg (hnd α)]
    rw [h0, intervalIntegral.integral_zero]

/-- Above the level `1/2` both the density sum and the density integral vanish. -/
private theorem two_pair_per_b_large {ω : ℝ → ℝ} {ε : ℝ}
    {x : ℝ} (hZ : 1 < scaleZ ε x) {m B b : ℕ}
    (hlarge : (1/2:ℝ) < Real.log (b:ℝ) / Real.log (scaleZ ε x)) :
    (∑ a ∈ Finset.Ioc b B,
        (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
          ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            ((a : ℝ) * Real.log (a : ℝ)) else 0)) = 0 ∧
      (∫ α in (1/10:ℝ)..(1/2:ℝ),
        (if lowerTwoDiscarded ε α (expo ε x b) then
          ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
        else 0)) = 0 := by
  have hb0 : expo ε x b = Real.log (b:ℝ) / Real.log (scaleZ ε x) := rfl
  have hnd : ∀ α : ℝ, ¬ lowerTwoDiscarded ε α (expo ε x b) := by
    intro α h
    have := lowerTwo_beta_le_half h
    rw [hb0] at this
    linarith
  constructor
  · refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg (hnd _)]
  · have h0 : (∫ α in (1/10:ℝ)..(1/2:ℝ),
        (if lowerTwoDiscarded ε α (expo ε x b) then
          ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
        else 0)) = ∫ α in (1/10:ℝ)..(1/2:ℝ), (0:ℝ) :=
      intervalIntegral.integral_congr fun α _ => by rw [if_neg (hnd α)]
    rw [h0, intervalIntegral.integral_zero]

/-- `4 ≤ Z ^ (12499/100000)` for `Z ≥ 2^20`: the lowest level of `E₂` is above `4`.
Proved through `log`, since `Real.rpow` rewrites on numerals do not elaborate here. -/
private theorem rpow_level_ge_four {Z : ℝ} (hZ : (1048576:ℝ) ≤ Z) :
    (4:ℝ) ≤ Z ^ (12499/100000:ℝ) := by
  have hZ0 : (0:ℝ) < Z := by linarith
  rw [Real.le_rpow_iff_log_le (by norm_num : (0:ℝ) < 4) hZ0]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : Real.log (1048576:ℝ) ≤ Real.log Z := Real.log_le_log (by norm_num) hZ
  have h2 : Real.log (1048576:ℝ) = 20 * Real.log 2 := by
    rw [show (1048576:ℝ) = 2 ^ (20:ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have h3 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h3]
  nlinarith [h1, h2, hl2]

/-- `2 ≤ Z ^ (1/10)` for `Z ≥ 1024`. -/
private theorem rpow_tenth_ge_two {Z : ℝ} (hZ : (1024:ℝ) ≤ Z) :
    (2:ℝ) ≤ Z ^ (1/10:ℝ) := by
  have hZ0 : (0:ℝ) < Z := by linarith
  rw [Real.le_rpow_iff_log_le (by norm_num : (0:ℝ) < 2) hZ0]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : Real.log (1024:ℝ) ≤ Real.log Z := Real.log_le_log (by norm_num) hZ
  have h2 : Real.log (1024:ℝ) = 10 * Real.log 2 := by
    rw [show (1024:ℝ) = 2 ^ (10:ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h2] at h1
  linarith [h1]




/-- Below the level `12499/100000` the density integral in the variable `t` vanishes. -/
private theorem two_pair_int_zero_small {ω : ℝ → ℝ} {ε : ℝ} (hε8 : ε ≤ 1/10^8)
    {x : ℝ} (hZ : 0 < Real.log (scaleZ ε x)) {m b : ℕ}
    (hsmall : Real.log (b:ℝ) / Real.log (scaleZ ε x) ≤ 12499/100000) :
    (∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)),
        (if lowerTwoDiscarded ε (Real.log t / Real.log (scaleZ ε x)) (expo ε x b) then
          ω (Real.log ((m : ℝ) / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)
        else 0)) = 0 := by
  have hb0 : expo ε x b = Real.log (b:ℝ) / Real.log (scaleZ ε x) := rfl
  have hnd : ∀ α : ℝ, ¬ lowerTwoDiscarded ε α (expo ε x b) := by
    intro α h
    have hgt := lowerTwo_beta_gt hε8 h
    rw [hb0] at hgt
    linarith
  have h0 : (∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)),
        (if lowerTwoDiscarded ε (Real.log t / Real.log (scaleZ ε x)) (expo ε x b) then
          ω (Real.log ((m : ℝ) / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)
        else 0)) =
      ∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)), (0:ℝ) :=
    intervalIntegral.integral_congr fun t _ => by rw [if_neg (hnd _)]
  rw [h0, intervalIntegral.integral_zero]

/-- Above the level `1/2` the density integral in the variable `t` vanishes. -/
private theorem two_pair_int_zero_large {ω : ℝ → ℝ} {ε : ℝ}
    {x : ℝ} (hZ : 1 < scaleZ ε x) {m b : ℕ}
    (hlarge : (1/2:ℝ) < Real.log (b:ℝ) / Real.log (scaleZ ε x)) :
    (∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)),
        (if lowerTwoDiscarded ε (Real.log t / Real.log (scaleZ ε x)) (expo ε x b) then
          ω (Real.log ((m : ℝ) / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)
        else 0)) = 0 := by
  have hb0 : expo ε x b = Real.log (b:ℝ) / Real.log (scaleZ ε x) := rfl
  have hnd : ∀ α : ℝ, ¬ lowerTwoDiscarded ε α (expo ε x b) := by
    intro α h
    have hle := lowerTwo_beta_le_half h
    rw [hb0] at hle
    linarith
  have h0 : (∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)),
        (if lowerTwoDiscarded ε (Real.log t / Real.log (scaleZ ε x)) (expo ε x b) then
          ω (Real.log ((m : ℝ) / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)
        else 0)) =
      ∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)), (0:ℝ) :=
    intervalIntegral.integral_congr fun t _ => by rw [if_neg (hnd _)]
  rw [h0, intervalIntegral.integral_zero]

set_option maxHeartbeats 1000000 in
/-- The per `b` comparison of the density sum with the density integral over the exponent range:
`100 / (b log b)` on the support of `E₂`, `0` where the region is empty. -/
private theorem two_pair_per_b {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) {x : ℝ}
    (hZbig : (1048576:ℝ) ≤ scaleZ ε x)
    {m B b : ℕ} (hm : 0 < m) (hbB : b ≤ B)
    (hZB : (scaleZ ε x) ^ (1/2:ℝ) ≤ (B:ℝ)) :
    abs ((∑ a ∈ Finset.Ioc b B,
        (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
          ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            ((a : ℝ) * Real.log (a : ℝ)) else 0))
      - (∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)),
        (if lowerTwoDiscarded ε (Real.log t / Real.log (scaleZ ε x)) (expo ε x b) then
          ω (Real.log ((m : ℝ) / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0)))
      ≤ if (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (b:ℝ) then
          100 / ((b:ℝ) * Real.log (b:ℝ)) else 0 := by
  have hZ1 : 1 < scaleZ ε x := by linarith
  have hZ0 : (0:ℝ) < scaleZ ε x := by linarith
  have hLZ : 0 < Real.log (scaleZ ε x) := Real.log_pos hZ1
  by_cases hcase : (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (b:ℝ)
  · rw [if_pos hcase]
    have hb0 : (0:ℝ) < (b:ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hZ0 _) hcase
    by_cases hhalf : (1/2:ℝ) < Real.log (b:ℝ) / Real.log (scaleZ ε x)
    · obtain ⟨h1, -⟩ := two_pair_per_b_large (ω := ω) (ε := ε) hZ1 (m := m) (B := B) (b := b) hhalf
      have h2 := two_pair_int_zero_large (ω := ω) (ε := ε) hZ1 (m := m) (b := b) hhalf
      rw [h1, h2, sub_zero, abs_zero]
      positivity
    · have hβle : Real.log (b:ℝ) / Real.log (scaleZ ε x) ≤ 1/2 := not_lt.mp hhalf
      have hβpos : (0:ℝ) < expo ε x b := by
        have hmono : (12499:ℝ)/100000 * Real.log (scaleZ ε x) ≤ Real.log (b:ℝ) := by
          have hlog : Real.log ((scaleZ ε x) ^ (12499/100000:ℝ)) ≤ Real.log (b:ℝ) :=
            Real.log_le_log (Real.rpow_pos_of_pos hZ0 _) hcase
          rw [Real.log_rpow hZ0] at hlog
          linarith
        have hpos : (0:ℝ) < 12499/100000 * Real.log (scaleZ ε x) := by positivity
        show (0:ℝ) < Real.log (b:ℝ) / Real.log (scaleZ ε x)
        exact div_pos (lt_of_lt_of_le hpos hmono) hLZ
      have hb4 : 4 ≤ b := by
        have h4 := rpow_level_ge_four (by linarith : (1048576:ℝ) ≤ scaleZ ε x)
        have h45 : (4:ℝ) ≤ (b:ℝ) := le_trans h4 hcase
        exact_mod_cast h45
      have hbZ2 : (b:ℝ) ≤ (scaleZ ε x) ^ (1/2:ℝ) := by
        rw [← Real.log_le_log_iff hb0 (Real.rpow_pos_of_pos hZ0 _), Real.log_rpow hZ0]
        rw [div_le_iff₀ hLZ] at hβle
        linarith
      have hbZ1 : (scaleZ ε x) ^ (1/10:ℝ) ≤ (b:ℝ) :=
        le_trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by norm_num)) hcase
      have hZ10 : (2:ℝ) ≤ (scaleZ ε x) ^ (1/10:ℝ) :=
        rpow_tenth_ge_two (by linarith : (1024:ℝ) ≤ scaleZ ε x)
      exact per_b_riemann (ω := ω) (ε := ε) (Z := scaleZ ε x) (β := expo ε x b)
        (m := (m : ℝ)) (b := b) (M := B) hω hz hZ1
        (by linarith : (4:ℝ) ≤ scaleZ ε x) hZ10 hβpos (by exact_mod_cast hm) hb4 hbB
        hbZ1 hbZ2 hZB rfl
  · rw [if_neg hcase]
    have hsmall : Real.log (b:ℝ) / Real.log (scaleZ ε x) ≤ 12499/100000 := by
      rcases Nat.eq_zero_or_pos b with hbzero | hbpos
      · subst hbzero
        simp only [Nat.cast_zero, Real.log_zero, zero_div]
        norm_num
      · have hb0' : (0:ℝ) < (b:ℝ) := by exact_mod_cast hbpos
        by_contra hcon
        have hlt : (12499:ℝ)/100000 < Real.log (b:ℝ) / Real.log (scaleZ ε x) := not_le.mp hcon
        have hprod : (12499:ℝ)/100000 * Real.log (scaleZ ε x) < Real.log (b:ℝ) := by
          rw [lt_div_iff₀ hLZ] at hlt
          linarith
        have hZb : (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (b:ℝ) := by
          have e1 : (scaleZ ε x) ^ (12499/100000:ℝ) =
              Real.exp (Real.log (scaleZ ε x) * (12499/100000)) := Real.rpow_def_of_pos hZ0 _
          rw [e1]
          have e2 : Real.exp (Real.log (b:ℝ)) = (b:ℝ) := Real.exp_log hb0'
          rw [← e2]
          exact Real.exp_le_exp.mpr (by linarith)
        exact hcase hZb
    obtain ⟨h1, -⟩ := two_pair_per_b_small (ω := ω) hε8 hLZ (m := m) (B := B) (b := b) hsmall
    have h2 := two_pair_int_zero_small (ω := ω) hε8 hLZ (m := m) (b := b) hsmall
    rw [h1, h2, sub_zero, abs_zero]

set_option maxHeartbeats 800000 in
/-- P0069 page 51: the outer sum of the per `b` weights, cut at the level `z0 ≥ x^(11/200)`.
`Σ_b (1/(b log^2 b)) · (100/(b log b))` above `z0` is `O(x^(-11/200) / log^3 x)`. -/
private theorem two_pair_weight_sum {x z0 : ℝ} (hx2 : 2 ≤ x) (hz0 : 4 ≤ z0)
    (hz0x : x ^ (11/200:ℝ) ≤ z0) {B : ℕ} :
    (∑ b ∈ Finset.Ioc 1 B, (1 / ((b:ℝ) * Real.log (b:ℝ) ^ 2)) *
        (if z0 ≤ (b:ℝ) then 100 / ((b:ℝ) * Real.log (b:ℝ)) else 0))
      ≤ 20000000 * x ^ (-(11/200:ℝ)) / Real.log x ^ 3 := by
  have hx0 : (0:ℝ) < x := by linarith
  have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hz00 : (0:ℝ) < z0 := by linarith
  have hlz0 : Real.log x / 20 ≤ Real.log z0 := by
    have h1 : Real.log (x ^ (11/200:ℝ)) ≤ Real.log z0 :=
      Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hz0x
    rw [Real.log_rpow hx0] at h1
    nlinarith [h1, hl0]
  have hlz00 : (0:ℝ) < Real.log z0 := by linarith
  -- the summand is `100 / (b^2 log^3 b)` on the support and `0` off it
  have hstep : ∀ b ∈ Finset.Ioc 1 B, (1 / ((b:ℝ) * Real.log (b:ℝ) ^ 2)) *
        (if z0 ≤ (b:ℝ) then 100 / ((b:ℝ) * Real.log (b:ℝ)) else 0)
      ≤ (if z0 ≤ (b:ℝ) then 100 / ((b:ℝ) ^ 2 * Real.log (b:ℝ) ^ 3) else 0) := by
    intro b hb
    by_cases h : z0 ≤ (b:ℝ)
    · rw [if_pos h, if_pos h]
      have hb3 : 2 ≤ b := by
        obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp hb
        omega
      have hb2 : (2:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb3
      have hb0 : (0:ℝ) < (b:ℝ) := by linarith
      have hL : Real.log (b:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
      have hbne : (b:ℝ) ≠ 0 := ne_of_gt hb0
      field_simp
      norm_num
    · rw [if_neg h, if_neg h, mul_zero]
  refine (Finset.sum_le_sum hstep).trans ?_
  -- cut the range at `⌊z0⌋ - 1`
  have hdrop : (∑ b ∈ Finset.Ioc 1 B,
        (if z0 ≤ (b:ℝ) then 100 / ((b:ℝ) ^ 2 * Real.log (b:ℝ) ^ 3) else 0))
      ≤ ∑ b ∈ Finset.Ioc (Nat.floor z0 - 1) B, 100 / ((b:ℝ) ^ 2 * Real.log (b:ℝ) ^ 3) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
    intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hb1
    have h3 : Nat.floor z0 ≤ b := by
      exact_mod_cast le_trans (Nat.floor_le (le_of_lt hz00)) hb2
    exact Finset.mem_Ioc.mpr ⟨by omega, h2⟩
  refine hdrop.trans ?_
  have hA1 : 1 ≤ Nat.floor z0 - 1 := by
    have h2 : 2 ≤ Nat.floor z0 := Nat.le_floor (a := z0) (n := 2) (by push_cast; linarith)
    omega
  have hAeq : ((Nat.floor z0 - 1 : ℕ) : ℝ) = ((Nat.floor z0 : ℕ) : ℝ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ Nat.floor z0)]
    ring
  have hAge : (z0 : ℝ) / 2 ≤ ((Nat.floor z0 - 1 : ℕ) : ℝ) := by
    have h1 : ((Nat.floor z0 : ℕ) : ℝ) ≤ z0 := Nat.floor_le (by linarith)
    have h2 : z0 - 1 ≤ ((Nat.floor z0 : ℕ) : ℝ) := by
      have h3 := Nat.lt_floor_add_one z0
      linarith
    rw [hAeq]; linarith
  -- each term is at most `(800 / log^3 z0) * (1/b^2)`
  have hstep3 : (∑ b ∈ Finset.Ioc (Nat.floor z0 - 1) B,
        100 / ((b:ℝ) ^ 2 * Real.log (b:ℝ) ^ 3))
      ≤ (800 / Real.log z0 ^ 3) *
          (∑ b ∈ Finset.Ioc (Nat.floor z0 - 1) B, 1 / ((b:ℝ) ^ 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp hb
    have hbA : ((Nat.floor z0 - 1 : ℕ) : ℝ) ≤ (b:ℝ) := by
      have h2 : (Nat.floor z0 - 1) ≤ b := by omega
      exact_mod_cast h2
    have hb2 : (2:ℝ) ≤ (b:ℝ) := by linarith
    have hb0 : (0:ℝ) < (b:ℝ) := by linarith
    have hlogb : Real.log z0 / 2 ≤ Real.log (b:ℝ) := by
      have h2 : Real.log (z0 / 2) ≤ Real.log (b:ℝ) :=
        Real.log_le_log (by linarith) (le_trans hAge hbA)
      have h3 : Real.log (z0 / 2) = Real.log z0 - Real.log 2 :=
        Real.log_div (ne_of_gt hz00) (by norm_num)
      have h4 : Real.log 2 ≤ Real.log z0 / 2 := by
        have h5 : Real.log 4 ≤ Real.log z0 := Real.log_le_log (by norm_num) hz0
        have h6 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
          push_cast
          ring
        linarith
      linarith
    have hlogb0 : 0 < Real.log (b:ℝ) := by linarith
    have hcube : Real.log z0 ^ 3 / 8 ≤ Real.log (b:ℝ) ^ 3 := by
      have h8 : (Real.log z0 / 2) ^ 3 ≤ Real.log (b:ℝ) ^ 3 :=
        pow_le_pow_left₀ (by linarith) hlogb 3
      have h9 : (Real.log z0 / 2) ^ 3 = Real.log z0 ^ 3 / 8 := by ring
      linarith [h8, h9.le, h9.ge]
    have hden : 0 < (b:ℝ) ^ 2 * Real.log (b:ℝ) ^ 3 :=
      mul_pos (pow_pos hb0 2) (pow_pos hlogb0 3)
    have hden2 : 0 < (b:ℝ) ^ 2 * (Real.log z0 ^ 3 / 8) := by
      have hlz3 : (0:ℝ) < Real.log z0 ^ 3 / 8 := div_pos (pow_pos (by linarith : (0:ℝ) < Real.log z0) 3) (by norm_num)
      exact mul_pos (pow_pos hb0 2) hlz3
    have hmono : (b:ℝ) ^ 2 * (Real.log z0 ^ 3 / 8) ≤ (b:ℝ) ^ 2 * Real.log (b:ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    have hle : 1 / ((b:ℝ) ^ 2 * Real.log (b:ℝ) ^ 3) ≤
        1 / ((b:ℝ) ^ 2 * (Real.log z0 ^ 3 / 8)) :=
      one_div_le_one_div_of_le hden2 hmono
    have he : (800 / Real.log z0 ^ 3) * (1 / ((b:ℝ) ^ 2)) =
        100 * (1 / ((b:ℝ) ^ 2 * (Real.log z0 ^ 3 / 8))) := by
      field_simp
      ring
    calc 100 / ((b:ℝ) ^ 2 * Real.log (b:ℝ) ^ 3)
        = 100 * (1 / ((b:ℝ) ^ 2 * Real.log (b:ℝ) ^ 3)) := by rw [mul_one_div]
      _ ≤ 100 * (1 / ((b:ℝ) ^ 2 * (Real.log z0 ^ 3 / 8))) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
      _ = (800 / Real.log z0 ^ 3) * (1 / ((b:ℝ) ^ 2)) := he.symm
  refine hstep3.trans ?_
  have hsq := sum_inv_sq_le (A := Nat.floor z0 - 1) (B := B) hA1
  have hsq' : (∑ b ∈ Finset.Ioc (Nat.floor z0 - 1) B, 1 / ((b:ℝ) ^ 2)) ≤ 2 / z0 := by
    refine hsq.trans ?_
    have h2 : 1 / ((Nat.floor z0 - 1 : ℕ) : ℝ) ≤ 1 / (z0 / 2) :=
      one_div_le_one_div_of_le (by linarith) hAge
    have h3 : 1 / (z0 / 2) = 2 / z0 := by field_simp
    linarith [h2, h3.le, h3.ge]

  have hfin : (800 / Real.log z0 ^ 3) * (2 / z0) ≤
      20000000 * x ^ (-(11/200:ℝ)) / Real.log x ^ 3 := by
    have h1 : 1 / z0 ≤ x ^ (-(11/200:ℝ)) := by
      rw [Real.rpow_neg hx0.le, ← one_div]
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx0 _) hz0x
    have h2 : 1 / Real.log z0 ^ 3 ≤ 8000 / Real.log x ^ 3 := by
      have hl3 : (Real.log x / 20) ^ 3 ≤ Real.log z0 ^ 3 :=
        pow_le_pow_left₀ (by linarith) hlz0 3
      have e : (Real.log x / 20) ^ 3 = Real.log x ^ 3 / 8000 := by ring
      rw [show (8000:ℝ) / Real.log x ^ 3 = 1 / (Real.log x ^ 3 / 8000) by field_simp]
      have hx3 : (0:ℝ) < Real.log x ^ 3 / 8000 :=
        div_pos (a := Real.log x ^ 3) (b := 8000) (pow_pos hl0 3) (by norm_num)
      exact one_div_le_one_div_of_le hx3 (by linarith [hl3, e.le, e.ge])
    have hpos1 : (0:ℝ) ≤ 1 / Real.log z0 ^ 3 :=
      div_nonneg (by norm_num) (pow_pos hlz00 3).le
    have hpos2 : (0:ℝ) ≤ x ^ (-(11/200:ℝ)) := by positivity
    have hmul : (1 / Real.log z0 ^ 3) * (1 / z0) ≤
        (8000 / Real.log x ^ 3) * x ^ (-(11/200:ℝ)) :=
      mul_le_mul h2 h1 (by positivity)
        (le_of_lt (div_pos (a := (8000:ℝ)) (b := Real.log x ^ 3) (by norm_num) (pow_pos hl0 3)))
    have he : (800 / Real.log z0 ^ 3) * (2 / z0) =
        1600 * (1 / Real.log z0 ^ 3) * (1 / z0) := by
      field_simp
      ring
    have he2 : 1600 * (8000 / Real.log x ^ 3) * x ^ (-(11/200:ℝ)) =
        12800000 * x ^ (-(11/200:ℝ)) / Real.log x ^ 3 := by
      field_simp
      ring
    have hle2 : 1600 * ((1 / Real.log z0 ^ 3) * (1 / z0)) ≤
        1600 * ((8000 / Real.log x ^ 3) * x ^ (-(11/200:ℝ))) :=
      mul_le_mul_of_nonneg_left hmul (by norm_num)
    have hsmall : (12800000:ℝ) * x ^ (-(11/200:ℝ)) / Real.log x ^ 3 ≤
        20000000 * x ^ (-(11/200:ℝ)) / Real.log x ^ 3 := by
      have hp : (0:ℝ) < x ^ (-(11/200:ℝ)) / Real.log x ^ 3 := by positivity
      have : (12800000:ℝ) * (x ^ (-(11/200:ℝ)) / Real.log x ^ 3) ≤
          20000000 * (x ^ (-(11/200:ℝ)) / Real.log x ^ 3) := by
        apply mul_le_mul_of_nonneg_right (by norm_num) hp.le
      calc (12800000:ℝ) * x ^ (-(11/200:ℝ)) / Real.log x ^ 3
          = 12800000 * (x ^ (-(11/200:ℝ)) / Real.log x ^ 3) := by ring
        _ ≤ 20000000 * (x ^ (-(11/200:ℝ)) / Real.log x ^ 3) := this
        _ = 20000000 * x ^ (-(11/200:ℝ)) / Real.log x ^ 3 := by ring
    calc (800 / Real.log z0 ^ 3) * (2 / z0)
        = 1600 * (1 / Real.log z0 ^ 3) * (1 / z0) := he
      _ = 1600 * ((1 / Real.log z0 ^ 3) * (1 / z0)) := by ring
      _ ≤ 1600 * ((8000 / Real.log x ^ 3) * x ^ (-(11/200:ℝ))) := hle2
      _ = 1600 * (8000 / Real.log x ^ 3) * x ^ (-(11/200:ℝ)) := by ring
      _ = 12800000 * x ^ (-(11/200:ℝ)) / Real.log x ^ 3 := he2
      _ ≤ 20000000 * x ^ (-(11/200:ℝ)) / Real.log x ^ 3 := hsmall
  have hcoef2 : (0:ℝ) ≤ 800 / Real.log z0 ^ 3 := by
    have hlz00 : (0:ℝ) < Real.log z0 := by linarith
    exact div_nonneg (by norm_num) (pow_pos hlz00 3).le
  exact mul_le_mul_of_nonneg_left hsq' hcoef2
    |>.trans hfin


/-! ### Stage 16: `leaf_two_pair_riemann_first` -/

set_option maxHeartbeats 1000000 in
/-- P0069 page 51: the per `b` term of `leaf_two_pair_riemann_first`, bounded by the weight
`1/(b log^2 b)` times the per `b` comparison of `two_pair_per_b`. -/
private theorem two_pair_term_bound {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) {x : ℝ}
    (hZ1 : 1 < scaleZ ε x) (hZbig : (1048576:ℝ) ≤ scaleZ ε x)
    {m B b : ℕ} (hm : 0 < m) (hbB : b ≤ B)
    (hZB : (scaleZ ε x) ^ (1/2:ℝ) ≤ (B:ℝ)) :
    abs ((∑ a ∈ Finset.Ioc b B,
        (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
            ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
              Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
          else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log (b : ℝ))))
      - (∫ α in (1/10:ℝ)..(1/2:ℝ),
          if lowerTwoDiscarded ε α (expo ε x b) then
            ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
          else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2))
      ≤ (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (b:ℝ) then
            100 / ((b:ℝ) * Real.log (b:ℝ)) else 0) := by
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · -- `b = 0`: an empty sum and a zero weight
    subst hb0
    have h1 : (∑ a ∈ Finset.Ioc 0 B,
        (if lowerTwoDiscarded ε (expo ε x a) (expo ε x 0) then
            ω (Real.log ((m : ℝ) / ((a : ℝ) * ((0:ℕ) : ℝ))) / Real.log ((0:ℕ) : ℝ)) /
              Real.log ((0:ℕ) : ℝ) / ((a : ℝ) * ((0:ℕ) : ℝ))
          else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log ((0:ℕ) : ℝ)))) = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      simp
    have h2 : (∫ α in (1/10:ℝ)..(1/2:ℝ),
          if lowerTwoDiscarded ε α (expo ε x 0) then
            ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x 0) / expo ε x 0) / α
          else 0) / (((0:ℕ) : ℝ) * Real.log ((0:ℕ) : ℝ) ^ 2) = 0 := by
      simp
    rw [h1, h2, sub_zero, abs_zero]
    simp
  · -- `b ≥ 1`
    have hw : (0:ℝ) ≤ 1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2) := by positivity
    have hw2 : (0:ℝ) ≤ ((b : ℝ) * Real.log (b : ℝ) ^ 2)⁻¹ := by positivity
    rcases Nat.eq_or_lt_of_le hbpos with hb1 | hb2
    · -- `b = 1`: both sides vanish
      subst hb1
      have h1 : (∑ a ∈ Finset.Ioc 1 B,
          (if lowerTwoDiscarded ε (expo ε x a) (expo ε x 1) then
              ω (Real.log ((m : ℝ) / ((a : ℝ) * ((1:ℕ) : ℝ))) / Real.log ((1:ℕ) : ℝ)) /
                Real.log ((1:ℕ) : ℝ) / ((a : ℝ) * ((1:ℕ) : ℝ))
            else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log ((1:ℕ) : ℝ)))) = 0 := by
        refine Finset.sum_eq_zero fun a _ => ?_
        simp
      have h2 : (∫ α in (1/10:ℝ)..(1/2:ℝ),
            if lowerTwoDiscarded ε α (expo ε x 1) then
              ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x 1) / expo ε x 1) / α
            else 0) / (((1:ℕ) : ℝ) * Real.log ((1:ℕ) : ℝ) ^ 2) = 0 := by
        simp
      rw [h1, h2, sub_zero, abs_zero]
      simp
    · -- `b ≥ 2`: the per `b` comparison
      have hA : (∫ α in (1/10:ℝ)..(1/2:ℝ),
            if lowerTwoDiscarded ε α (expo ε x b) then
              ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
            else 0) =
          ∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)),
            (if lowerTwoDiscarded ε (Real.log t / Real.log (scaleZ ε x)) (expo ε x b) then
              ω (Real.log ((m : ℝ) / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)
            else 0) :=
        per_b_integral_eq (ω := ω) (ε := ε) (x := x) (m := m) (b := b) hZ1
          (by exact_mod_cast hm) hb2
      have hsum_eq := two_pair_inner_sum (ω := ω) (ε := ε) (x := x) (m := m) (B := B) (b := b) hb2
      rw [hsum_eq]
      rw [hA]
      have hcore := two_pair_per_b (ω := ω) (ε := ε) (x := x) (m := m) (B := B) (b := b)
        hω hz hε hε8 hZbig hm hbB hZB
      calc abs ((∑ a ∈ Finset.Ioc b B,
              (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  ((a : ℝ) * Real.log (a : ℝ)) else 0)) *
            (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) -
          (∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)),
              (if lowerTwoDiscarded ε (Real.log t / Real.log (scaleZ ε x)) (expo ε x b) then
                ω (Real.log ((m : ℝ) / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)
              else 0)) / ((b : ℝ) * Real.log (b : ℝ) ^ 2))
          = abs ((∑ a ∈ Finset.Ioc b B,
              (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  ((a : ℝ) * Real.log (a : ℝ)) else 0)) -
              (∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)),
                (if lowerTwoDiscarded ε (Real.log t / Real.log (scaleZ ε x)) (expo ε x b) then
                  ω (Real.log ((m : ℝ) / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)
                else 0))) * ((b : ℝ) * Real.log (b : ℝ) ^ 2)⁻¹ := by
            rw [div_eq_mul_inv, one_mul, div_eq_mul_inv, ← sub_mul, abs_mul, abs_of_nonneg hw2]
        _ ≤ ((b : ℝ) * Real.log (b : ℝ) ^ 2)⁻¹ *
              (if (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (b:ℝ) then
                100 / ((b:ℝ) * Real.log (b:ℝ)) else 0) := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_left hcore hw2
        _ = (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
              (if (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (b:ℝ) then
                100 / ((b:ℝ) * Real.log (b:ℝ)) else 0) := by
            rw [one_div]




/-- P0069 page 51 display 5.17, the outer primes of the E2 sum of display 5.15. Interchange of
the two outer variables over the triangle `1 ≤ b < a ≤ N`. -/
theorem two_pair_triangle_swap (N : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ b ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Ioc b N, g a b =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Ico 1 a, g a b := by
  refine Finset.sum_comm' fun b a => ?_
  simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_Ico]
  omega

/-- P0069 page 51 display 5.17, the outer primes of the E2 sum of display 5.15. Exact algebra
of the two applications of the prime number theorem: with `w` the indicator of the primes and
`l` the density `1 / log`, the sum over `w b w a` is the sum over `l a l b` plus an error with
the factor `w a - l a` for each fixed `b` and an error with the factor `w b - l b` for each
fixed `a`. -/
theorem two_pair_sum_split (N : ℕ) (w l : ℕ → ℝ) (F : ℕ → ℕ → ℝ) :
    ∑ b ∈ Finset.Icc 1 N, w b * ∑ a ∈ Finset.Ioc b N, w a * F a b =
      (∑ b ∈ Finset.Icc 1 N, w b * ∑ a ∈ Finset.Ioc b N, (w a - l a) * F a b) +
      (∑ a ∈ Finset.Icc 1 N, l a * ∑ b ∈ Finset.Ico 1 a, (w b - l b) * F a b) +
      ∑ b ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Ioc b N, F a b * (l a * l b) := by
  have e1 : ∑ b ∈ Finset.Icc 1 N, w b * ∑ a ∈ Finset.Ioc b N, w a * F a b =
      (∑ b ∈ Finset.Icc 1 N, w b * ∑ a ∈ Finset.Ioc b N, (w a - l a) * F a b) +
      ∑ b ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Ioc b N, w b * (l a * F a b) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have e2 := two_pair_triangle_swap N (fun a b => w b * (l a * F a b))
  have e3 : ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Ico 1 a, w b * (l a * F a b) =
      (∑ a ∈ Finset.Icc 1 N, l a * ∑ b ∈ Finset.Ico 1 a, (w b - l b) * F a b) +
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Ico 1 a, F a b * (l a * l b) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have e4 := two_pair_triangle_swap N (fun a b => F a b * (l a * l b))
  beta_reduce at e2 e4
  rw [e1, e2, e3, ← e4]
  ring

/-- P0069 page 51 display 5.17, the outer primes of the E2 sum of display 5.15. The sum over
the prime pairs `p2 < p1` up to `N` with a condition `E` is the iterated sum over `b` and then
`a > b` weighted by the indicator of the primes. -/
theorem two_pair_sum_iterated (N : ℕ) (E : ℕ → ℕ → Prop) (t : ℕ → ℕ → ℝ) :
    ∑ i ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun i : ℕ × ℕ =>
        i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧ E i.1 i.2), t i.1 i.2 =
      ∑ b ∈ Finset.Icc 1 N, primeWeight b *
        ∑ a ∈ Finset.Ioc b N, primeWeight a * (if E a b then t a b else 0) := by
  rw [Finset.sum_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb1 := (Finset.mem_Icc.mp hb).1
  have hIoc : Finset.Ioc b N = (Finset.Icc 1 N).filter (fun a => b < a) := by
    ext a
    simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hIoc, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h1 : a.Prime <;> by_cases h2 : b.Prime <;> by_cases h3 : b < a <;>
    by_cases h4 : E a b <;> simp [primeWeight, h1, h2, h3, h4]

/-- LEAF: P0069 page 51, display 5.17, the E2 sum of display 5.15 at one point `m` of J, the
passage from the sum over the first outer variable to the integral of page 51. For each fixed
integer `b` the sum over the integers `a > b` with exponents in E2 of
`ω(log (m / (a b)) / log b) / (a log a)` is the integral over the first exponent `β1` of
`ω((s - β1 - β2) / β2) / β1` on the section of E2 at `β2 = log b / log Z`, where `m = Z^s`:
the change of variables `a = Z^β1` has `da / (a log a) = dβ1 / β1`, and on `a > b ≥
(2 Y) ^ (1 / 10)` the sum of a function of bounded variation is its integral up to a power
saving. The statement is summed over `b` with the remaining weight `1 / (b log^2 b)`. No
prime number theorem is used. -/
theorem leaf_two_pair_riemann_first (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          ∑ a ∈ Finset.Ioc b ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log (b : ℝ)))) -
        ∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          (∫ α in (1/10:ℝ)..(1/2:ℝ),
            if lowerTwoDiscarded ε α (expo ε x b) then
              ω ((Real.log m / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
            else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2)| ≤ C * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨Cabs, hCabs0, hCabs⟩ := rpow_neg_mul_log_rpow_le (c := 11/200) (by norm_num) (j := -3) A
  refine ⟨max (max (20000000 * Cabs) ((2:ℝ)^40)) (Real.exp ((2:ℝ)^(A+1))),
    fun x hx m hm1 hm2 => ?_⟩
  have h40 : (2:ℝ) ^ 40 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hexp : Real.exp ((2:ℝ) ^ (A+1)) ≤ x := (le_max_right _ _).trans hx
  have hCabsx : Cabs ≤ x := by
    have h1 : 20000000 * Cabs ≤ max (20000000 * Cabs) ((2:ℝ)^40) := le_max_left _ _
    have h2 : max (20000000 * Cabs) ((2:ℝ)^40) ≤ max (max (20000000 * Cabs) ((2:ℝ)^40))
        (Real.exp ((2:ℝ)^(A+1))) := le_max_left _ _
    have h3 : Cabs ≤ 20000000 * Cabs := by nlinarith [hCabs0]
    linarith [h1, h2, h3, hx]
  obtain ⟨hY49, -, -, -, hl, hlX1, hlX2⟩ :=
    two_pair_scale_facts hε hε8 hA h40 hexp (by nlinarith : (1:ℝ) ^ 2 ≤ x)
  have hx1 : (1:ℝ) ≤ x := le_trans (by norm_num) h40
  have hx0 : (0:ℝ) < x := by linarith
  have hy4 : (4:ℝ) ≤ x ^ (11/20 + ε) := le_trans (by norm_num) hY49
  have hy0 : (0:ℝ) < x ^ (11/20 + ε) := by linarith
  have hZ1 : 1 < scaleZ ε x := (scaleZ_rpow_ge hε hε8 hx1).2
  have hZ0 : (0:ℝ) < scaleZ ε x := by linarith
  have hZD : 0 < Real.log (scaleZ ε x) := Real.log_pos hZ1
  have hY20 : (2:ℝ) ^ 20 ≤ x ^ (11/20 + ε) := by
    refine shortY_ge_of_sq_le hε hx1 ?_
    rw [show ((2:ℝ) ^ 20) ^ 2 = (2:ℝ) ^ 40 by norm_num]
    exact h40
  have hZbig : (1048576:ℝ) ≤ scaleZ ε x := by
    unfold scaleZ shortY
    nlinarith [hY20]
  have hZlevel : (4:ℝ) ≤ (scaleZ ε x) ^ (12499/100000:ℝ) := rpow_level_ge_four hZbig
  -- `x^(11/200) ≤ z0 = Z^(12499/100000)`, because `12499/100000` is below `c1 - eps` and
  -- `Z = 4 Y` carries the factor `4`
  have hz0x : x ^ (11/200:ℝ) ≤ (scaleZ ε x) ^ (12499/100000:ℝ) := by
    have hp : (11/200:ℝ) ≤ (11:ℝ)/20 * (12499/100000) := by norm_num
    have h1 : x ^ (11/200:ℝ) ≤ x ^ ((11:ℝ)/20 * (12499/100000)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 hp
    have h2 : x ^ ((11:ℝ)/20 * (12499/100000)) =
        (x ^ ((11:ℝ)/20)) ^ (12499/100000:ℝ) := by
      rw [Real.rpow_mul (le_of_lt hx0)]
    have hbase : x ^ ((11:ℝ)/20) ≤ scaleZ ε x := by
      have hshort : x ^ ((11:ℝ)/20) ≤ x ^ (11/20 + ε) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      unfold scaleZ shortY
      nlinarith [hshort]
    have h3 : (x ^ ((11:ℝ)/20)) ^ (12499/100000:ℝ) ≤ (scaleZ ε x) ^ (12499/100000:ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hx0) _) hbase (by norm_num)
    rw [h2] at h1
    exact h1.trans h3
  -- `Z^(1/2) ≤ ⌊2 Y⌋`
  have hYsq : (2:ℝ) ≤ (x ^ (11/20 + ε)) ^ (1/2:ℝ) := by
    have h := Real.sqrt_le_sqrt hy4
    have h4 : Real.sqrt 4 = (2:ℝ) := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4, Real.sqrt_eq_rpow] at h
    exact h
  have hYsq0 : (0:ℝ) ≤ (x ^ (11/20 + ε)) ^ (1/2:ℝ) := by positivity
  have hYsqsq : ((x ^ (11/20 + ε)) ^ (1/2:ℝ)) ^ 2 = x ^ (11/20 + ε) := by
    rw [pow_two, ← Real.rpow_add (by linarith)]
    norm_num
  have hZs : (scaleZ ε x) ^ (1/2:ℝ) = 2 * (x ^ (11/20 + ε)) ^ (1/2:ℝ) := by
    unfold scaleZ shortY
    rw [Real.mul_rpow (x := (4:ℝ)) (y := x ^ (11/20 + ε)) (z := (1/2:ℝ)) (by norm_num) (le_of_lt hy0)]
    have h4 : (4:ℝ) ^ (1/2:ℝ) = 2 := by
      rw [← Real.sqrt_eq_rpow, show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4]
  have hZB : (scaleZ ε x) ^ (1/2:ℝ) ≤ ((⌊2 * x ^ (11/20 + ε)⌋₊ : ℕ) : ℝ) := by
    rw [hZs]
    have hmain : 2 * (x ^ (11/20 + ε)) ^ (1/2:ℝ) ≤ 2 * x ^ (11/20 + ε) - 1 := by
      nlinarith [hYsq, hYsq0, hYsqsq, hy4]
    have hfloor : 2 * x ^ (11/20 + ε) - 1 ≤ ((⌊2 * x ^ (11/20 + ε)⌋₊ : ℕ) : ℝ) := by
      have h := Nat.lt_floor_add_one (2 * x ^ (11/20 + ε))
      linarith
    linarith
  -- the sum bound
  have hB1 : 1 ≤ ⌊2 * x ^ (11/20 + ε)⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_one]
    nlinarith [hy4]
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hpt : ∀ b ∈ Finset.Icc 1 ⌊2 * x ^ (11/20 + ε)⌋₊,
      |(∑ a ∈ Finset.Ioc b ⌊2 * x ^ (11/20 + ε)⌋₊,
          (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
              ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
            else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log (b : ℝ)))) -
        (∫ α in (1/10:ℝ)..(1/2:ℝ),
          if lowerTwoDiscarded ε α (expo ε x b) then
            ω ((Real.log m / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
          else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2)|
      ≤ (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (b:ℝ) then
            100 / ((b:ℝ) * Real.log (b:ℝ)) else 0) := by
    intro b hb
    exact two_pair_term_bound (ω := ω) hω hz hε hε8 hZ1 hZbig (by omega : 0 < m)
      (Finset.mem_Icc.mp hb).2 hZB
  refine (Finset.sum_le_sum hpt).trans ?_
  have hIcc : (∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11/20 + ε)⌋₊,
      (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
        (if (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (b:ℝ) then
          100 / ((b:ℝ) * Real.log (b:ℝ)) else 0))
      = ∑ b ∈ Finset.Ioc 1 ⌊2 * x ^ (11/20 + ε)⌋₊,
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (b:ℝ) then
            100 / ((b:ℝ) * Real.log (b:ℝ)) else 0) := by
    rw [Finset.Icc_eq_cons_Ioc hB1, Finset.sum_cons]
    have h1 : (1 / (((1:ℕ) : ℝ) * Real.log (((1:ℕ) : ℝ)) ^ 2)) *
        (if (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (((1:ℕ) : ℝ)) then
          100 / ((((1:ℕ) : ℝ)) * Real.log (((1:ℕ) : ℝ))) else 0) = 0 := by
      simp
    rw [h1, zero_add]
  rw [hIcc]
  have hW := two_pair_weight_sum (x := x) (z0 := (scaleZ ε x) ^ (12499/100000:ℝ))
      (by linarith) hZlevel hz0x (B := ⌊2 * x ^ (11/20 + ε)⌋₊)
  have hlog0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (le_of_lt hlog0) _
  have hcabs := hCabs x (by linarith)
  have hlog3 : Real.log x ^ (-3:ℝ) = (Real.log x ^ 3)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hlog0)]
    norm_num [Real.rpow_natCast]
  have hlab : 20000000 * x ^ (-(11/200:ℝ)) / Real.log x ^ 3
      = 20000000 * (x ^ (-(11/200:ℝ)) * Real.log x ^ (-3:ℝ)) := by
    rw [hlog3, div_eq_mul_inv]
    ring
  have hstep : 20000000 * (x ^ (-(11/200:ℝ)) * Real.log x ^ (-3:ℝ))
      ≤ max (max (20000000 * Cabs) ((2:ℝ)^40)) (Real.exp ((2:ℝ) ^ (A+1))) *
        Real.log x ^ (-A) := by
    have h1 : 20000000 * (x ^ (-(11/200:ℝ)) * Real.log x ^ (-3:ℝ))
        ≤ 20000000 * (Cabs * Real.log x ^ (-A)) :=
      mul_le_mul_of_nonneg_left hcabs (by norm_num)
    have h3 : (20000000 * Cabs) * Real.log x ^ (-A)
        ≤ max (max (20000000 * Cabs) ((2:ℝ)^40)) (Real.exp ((2:ℝ) ^ (A+1))) *
          Real.log x ^ (-A) :=
      mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_left _ _)) hL
    refine h1.trans ?_
    calc 20000000 * (Cabs * Real.log x ^ (-A))
        = (20000000 * Cabs) * Real.log x ^ (-A) := by ring
      _ ≤ _ := h3
  exact hW.trans (hlab ▸ hstep)

/-! ### NEW: the discarded region as a function of the second exponent `β` -/

/-- `lowerTwoDiscarded` in `β` at fixed `α`: every atom is `β ≤ L` or `L ≤ β` with `L` affine in
`α`, so between consecutive switch points the truth value does not change. -/
theorem sect_same_beta {ε α β β' : ℝ}
    (h0 : (1+7*(2*(1/16-1/10^5)))/15-ε ≤ β ↔ (1+7*(2*(1/16-1/10^5)))/15-ε ≤ β')
    (h1 : β ≤ α ↔ β' ≤ α)
    (h3 : α + 2*β ≤ 1 ↔ α + 2*β' ≤ 1)
    (h4 : α + 2*β ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε ↔
          α + 2*β' ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε)
    (h5 : 4*α + 7*β ≤ 2+2*(1/16-1/10^5)-ε ↔ 4*α + 7*β' ≤ 2+2*(1/16-1/10^5)-ε)
    (h6 : 1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β ↔
          1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β')
    (h7 : 4*α + 5*β ≤ 2+2*(1/16-1/10^5)-ε ↔ 4*α + 5*β' ≤ 2+2*(1/16-1/10^5)-ε)
    (h8 : 1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β ↔
          1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β')
    (h12 : β ≤ (36*(2*(1/16-1/10^5))-2)/11-ε ↔ β' ≤ (36*(2*(1/16-1/10^5))-2)/11-ε)
    (h11 : 2*β - (2*(1/16-1/10^5)) + ε ≤ α ↔ 2*β' - (2*(1/16-1/10^5)) + ε ≤ α)
    (h13 : |4*α + 3*β - 2| ≤ 2*(1/16-1/10^5)-ε ↔ |4*α + 3*β' - 2| ≤ 2*(1/16-1/10^5)-ε)
    (h14 : |4*α + β - 2| ≤ 2*(1/16-1/10^5)-ε ↔ |4*α + β' - 2| ≤ 2*(1/16-1/10^5)-ε) :
    (lowerTwoDiscarded ε α β ↔ lowerTwoDiscarded ε α β') := by
  unfold lowerTwoDiscarded upperPairRegion
  rw [h0, h1, h3, h4, h5, h6, h7, h8, h12, h11, h13, h14]

/-- The discarded region at fixed `α` is a measurable set in the integer variable `t` with
`β = log t / log Z`. -/
private theorem measurableSet_lowerTwo_beta {ε α Z : ℝ} :
    MeasurableSet {t : ℝ | lowerTwoDiscarded ε α (Real.log t / Real.log Z)} := by
  unfold lowerTwoDiscarded upperPairRegion
  measurability

/-- Buchstab's function is measurable: continuous off the single point `1`. -/
private theorem measurable_buchstab_new {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω) : Measurable ω := by
  refine measurable_of_continuousOn_compl_singleton (1 : ℝ) ?_
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  rcases lt_or_gt_of_ne hx with h | h
  · have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhds x] ω := by
      filter_upwards [isOpen_Iio.mem_nhds h] with y hy
      exact (hz y hy).symm
    exact (continuousAt_const.congr hev).continuousWithinAt
  · exact (hω.1.continuousAt (Ici_mem_nhds h)).continuousWithinAt

/-- The `α`-integrand of the second passage is measurable in the integer variable `t`. -/
private theorem phi_measurable {ω : ℝ → ℝ} (hωm : Measurable ω) {ε Z s α : ℝ} :
    Measurable (fun t : ℝ => if lowerTwoDiscarded ε α (Real.log t / Real.log Z) then
      ω ((s - α - Real.log t / Real.log Z) / (Real.log t / Real.log Z)) / α else 0) := by
  have hs : MeasurableSet {t : ℝ | lowerTwoDiscarded ε α (Real.log t / Real.log Z)} :=
    measurableSet_lowerTwo_beta
  have hf : Measurable (fun t : ℝ =>
      ω ((s - α - Real.log t / Real.log Z) / (Real.log t / Real.log Z)) / α) := by
    measurability
  exact Measurable.ite hs hf measurable_const



/-! ### NEW: elementary sum estimates -/

/-- `log v - log u ≤ (v - u)/u` for `0 < u ≤ v` (copy of the target's `log_sub_log_le_div`,
restated here so that the WIP compiles on its own). -/
theorem log_sub_log_le_div_new {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    Real.log t - Real.log a ≤ (t - a) / a := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  rw [← Real.log_div ht.ne' ha.ne']
  have h1 : Real.log (t / a) ≤ t / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2 : t / a - 1 = (t - a) / a := by rw [div_sub_one ha.ne']
  linarith

/-- `1/n ≤ log (n/(n-1))` for `n ≥ 2`. -/
private theorem inv_le_log_ratio {n : ℕ} (hn : 2 ≤ n) :
    1/(n:ℝ) ≤ Real.log ((n:ℝ)/((n:ℝ)-1)) := by
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have h1 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hx : (0:ℝ) < (n:ℝ)/((n:ℝ)-1) := by positivity
  have h := Real.one_sub_inv_le_log_of_pos (x := (n:ℝ)/((n:ℝ)-1)) hx
  have e : 1 - ((n:ℝ)/((n:ℝ)-1))⁻¹ = 1/(n:ℝ) := by
    rw [inv_div]
    field_simp
    ring
  rwa [e] at h

/-- `∑_{N < n ≤ B} 1/(n log^2 n) ≤ 1/log N` for `N ≥ 4`, by telescoping
`1/(n log^2 n) ≤ 1/log (n-1) - 1/log n`. -/
private theorem sum_inv_log_sq_le {N B : ℕ} (hN : 4 ≤ N) :
    (∑ n ∈ Finset.Ioc N B, 1 / ((n:ℝ) * Real.log (n:ℝ)^2)) ≤ 1 / Real.log (N:ℝ) := by
  have hN2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
  have hlogN : 0 < Real.log (N:ℝ) := by
    have h : Real.log 2 ≤ Real.log (N:ℝ) := Real.log_le_log (by norm_num) hN2
    have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hstep : ∀ n ∈ Finset.Ioc N B,
      1 / ((n:ℝ) * Real.log (n:ℝ)^2) ≤
        1 / Real.log ((n:ℝ) - 1) - 1 / Real.log (n:ℝ) := by
    intro n hn
    obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp hn
    have hn2 : 2 ≤ n := by omega
    have hn5 : 5 ≤ n := by omega
    have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
    have hn5R : (5:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn5
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    have hln : 0 < Real.log (n:ℝ) := by
      have h : Real.log 2 ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) hnR
      have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    have hlm : 0 < Real.log ((n:ℝ) - 1) := Real.log_pos (by linarith)
    have hlm_le : Real.log ((n:ℝ) - 1) ≤ Real.log (n:ℝ) :=
      Real.log_le_log (by linarith) (by linarith)
    have e1 : 1 / Real.log ((n:ℝ) - 1) - 1 / Real.log (n:ℝ) =
        Real.log ((n:ℝ)/((n:ℝ)-1)) / (Real.log ((n:ℝ)-1) * Real.log (n:ℝ)) := by
      rw [Real.log_div hn0.ne' (by linarith : ((n:ℝ)-1) ≠ 0)]
      field_simp
    have hinv : 1/(n:ℝ) ≤ Real.log ((n:ℝ)/((n:ℝ)-1)) := inv_le_log_ratio hn2
    have hA : (1/(n:ℝ)) / (Real.log ((n:ℝ)-1) * Real.log (n:ℝ)) ≤
        Real.log ((n:ℝ)/((n:ℝ)-1)) / (Real.log ((n:ℝ)-1) * Real.log (n:ℝ)) :=
      div_le_div_of_nonneg_right hinv (by positivity)
    have e2 : (1/(n:ℝ)) / (Real.log ((n:ℝ)-1) * Real.log (n:ℝ)) =
        1/((n:ℝ) * (Real.log ((n:ℝ)-1) * Real.log (n:ℝ))) := by
      field_simp
    have hmul : Real.log ((n:ℝ)-1) * Real.log (n:ℝ) ≤ Real.log (n:ℝ)^2 := by
      have h1 : Real.log ((n:ℝ)-1) * Real.log (n:ℝ) ≤ Real.log (n:ℝ) * Real.log (n:ℝ) :=
        mul_le_mul_of_nonneg_right hlm_le hln.le
      calc Real.log ((n:ℝ)-1) * Real.log (n:ℝ) ≤ Real.log (n:ℝ) * Real.log (n:ℝ) := h1
        _ = Real.log (n:ℝ)^2 := by ring
    have hB : 1/((n:ℝ) * Real.log (n:ℝ)^2) ≤
        (1/(n:ℝ)) / (Real.log ((n:ℝ)-1) * Real.log (n:ℝ)) := by
      rw [e2]
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left hmul hn0.le
    rw [e1]
    exact hB.trans hA
  refine (Finset.sum_le_sum hstep).trans ?_
  have htel : ∀ B' : ℕ, N ≤ B' →
      (∑ n ∈ Finset.Ioc N B', (1 / Real.log ((n:ℝ) - 1) - 1 / Real.log (n:ℝ)))
        = 1 / Real.log (N:ℝ) - 1 / Real.log (B':ℝ) := by
    intro B' hB'
    induction B', hB' using Nat.le_induction with
    | base => simp
    | succ b hb ih =>
      rw [Finset.sum_Ioc_succ_top hb, ih]
      have hcast : ((b + 1 : ℕ) : ℝ) = (b:ℝ) + 1 := by push_cast; ring
      have hsub : (b:ℝ) + 1 - 1 = (b:ℝ) := by ring
      rw [hcast, hsub]
      ring
  rcases le_or_gt N B with h | h
  · rw [htel B h]
    have hB0 : (0:ℝ) ≤ 1 / Real.log (B:ℝ) := by
      rcases Nat.eq_zero_or_pos B with hB | hB
      · rw [hB]; simp
      · have hB1 : (2:ℝ) ≤ (B:ℝ) := by
          have : 2 ≤ B := by omega
          exact_mod_cast this
        have h2 : 0 < Real.log (B:ℝ) := by
          have h3 : Real.log 2 ≤ Real.log (B:ℝ) := Real.log_le_log (by norm_num) hB1
          have h4 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
          linarith
        exact le_of_lt (one_div_pos.mpr h2)
    linarith
  · have hempty : Finset.Ioc N B = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    positivity

/-- `∑_{A < n ≤ B} 1/(n^2 log^k n) ≤ 1/(A log^k A)` for `A ≥ 4`, `1 ≤ k`. -/
private theorem sum_inv_sq_log_pow_le {A B : ℕ} (hA : 2 ≤ A) {k : ℕ} (hk : 1 ≤ k) :
    (∑ n ∈ Finset.Ioc A B, 1 / ((n:ℝ)^2 * Real.log (n:ℝ)^k)) ≤
      1 / ((A:ℝ) * Real.log (A:ℝ)^k) := by
  have hA2 : (2:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA
  have hA0 : (0:ℝ) < (A:ℝ) := by linarith
  have hlogA : 0 < Real.log (A:ℝ) := by
    have h : Real.log 2 ≤ Real.log (A:ℝ) := Real.log_le_log (by norm_num) hA2
    have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hstep : ∀ n ∈ Finset.Ioc A B, 1 / ((n:ℝ)^2 * Real.log (n:ℝ)^k) ≤
      (1 / Real.log (A:ℝ)^k) * (1 / ((n:ℝ)^2)) := by
    intro n hn
    obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp hn
    have hnA : (A:ℝ) ≤ (n:ℝ) := by exact_mod_cast le_of_lt h1
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    have hln : 0 < Real.log (n:ℝ) := lt_of_lt_of_le hlogA (Real.log_le_log hA0 hnA)
    have hle : Real.log (A:ℝ)^k ≤ Real.log (n:ℝ)^k :=
      pow_le_pow_left₀ hlogA.le (Real.log_le_log hA0 hnA) k
    have hb : 1 / ((n:ℝ)^2 * Real.log (n:ℝ)^k) ≤ 1 / ((n:ℝ)^2 * Real.log (A:ℝ)^k) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    have e : 1 / ((n:ℝ)^2 * Real.log (A:ℝ)^k) = (1 / Real.log (A:ℝ)^k) * (1 / ((n:ℝ)^2)) := by
      field_simp
    linarith [hb, e.le, e.ge]
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum]
  have hsq : (∑ n ∈ Finset.Ioc A B, 1 / ((n:ℝ)^2)) ≤ 1 / (A:ℝ) := sum_inv_sq_le (by omega)
  have hfin : (1 / Real.log (A:ℝ)^k) * (1 / (A:ℝ)) = 1 / ((A:ℝ) * Real.log (A:ℝ)^k) := by
    field_simp
  calc (1 / Real.log (A:ℝ)^k) * (∑ n ∈ Finset.Ioc A B, 1 / ((n:ℝ)^2))
      ≤ (1 / Real.log (A:ℝ)^k) * (1 / (A:ℝ)) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 1 / ((A:ℝ) * Real.log (A:ℝ)^k) := hfin



/-! ### NEW: the discarded region is constant on a `b`-cell with no switch point -/

set_option maxHeartbeats 4000000 in
/-- The switch points of `E₂` as a function of the second exponent `β` at fixed `α`, `s`: if none
of them lies in `[β, β']` then the region takes the same value at `β` and `β'`. -/
private theorem cell_region_const_beta {ε α s β β' : ℝ} (hββ' : β ≤ β')
    (hno : ∀ τ ∈ (([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
        (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
        (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        (α + 2*(1/16-1/10^5) - ε)/2,
        (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
        (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
        2 - (2*(1/16-1/10^5) - ε) - 4*α,
        2 + (2*(1/16-1/10^5) - ε) - 4*α,
        (s - α)/2] : List ℝ).toFinset), ¬(β ≤ τ ∧ τ ≤ β')) :
    (lowerTwoDiscarded ε α β ↔ lowerTwoDiscarded ε α β') := by
  refine sect_same_beta (h0 := ?_) (h1 := ?_) (h3 := ?_) (h4 := ?_) (h5 := ?_) (h6 := ?_)
    (h7 := ?_) (h8 := ?_) (h12 := ?_) (h11 := ?_) (h13 := ?_) (h14 := ?_)
  · -- `c₁ - ε ≤ β`
    have hz := hno ((1+7*(2*(1/16-1/10^5)))/15-ε) (by simp)
    constructor
    · intro h; linarith
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
  · -- `β ≤ α`
    have hz := hno (α) (by simp)
    constructor
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
    · intro h; linarith
  · -- `α + 2β ≤ 1`
    have hz := hno ((1-α)/2) (by simp)
    constructor
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
    · intro h; linarith
  · -- `α + 2β ≤ c₃ - 2ε`
    have hz := hno ((1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2) (by simp)
    constructor
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
    · intro h; linarith
  · -- `4α + 7β ≤ 2 + θ - ε`
    have hz := hno ((2 + 2*(1/16-1/10^5) - ε - 4*α)/7) (by simp)
    constructor
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
    · intro h; linarith
  · -- `c₅ ≤ α + β`
    have hz := hno (1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α) (by simp)
    constructor
    · intro h; linarith
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
  · -- `4α + 5β ≤ 2 + θ - ε`
    have hz := hno ((2 + 2*(1/16-1/10^5) - ε - 4*α)/5) (by simp)
    constructor
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
    · intro h; linarith
  · -- `c₇ ≤ α + β`
    have hz := hno (1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α) (by simp)
    constructor
    · intro h; linarith
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
  · -- `β ≤ (36θ - 2)/11 - ε`
    have hz := hno ((36*(2*(1/16-1/10^5))-2)/11-ε) (by simp)
    constructor
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
    · intro h; linarith
  · -- `2β - θ + ε ≤ α`
    have hz := hno ((α + 2*(1/16-1/10^5) - ε)/2) (by simp)
    constructor
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
    · intro h; linarith
  · -- `|4α + 3β - 2| ≤ θ - ε`
    have hzu := hno ((2 + (2*(1/16-1/10^5) - ε) - 4*α)/3) (by simp : ((2 + (2*(1/16-1/10^5) - ε) - 4*α)/3) ∈ ([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
        (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
        (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        (α + 2*(1/16-1/10^5) - ε)/2,
        (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
        (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
        2 - (2*(1/16-1/10^5) - ε) - 4*α,
        2 + (2*(1/16-1/10^5) - ε) - 4*α,
        (s - α)/2] : List ℝ).toFinset)
    have hzl := hno ((2 - (2*(1/16-1/10^5) - ε) - 4*α)/3) (by simp : ((2 - (2*(1/16-1/10^5) - ε) - 4*α)/3) ∈ ([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
        (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
        (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        (α + 2*(1/16-1/10^5) - ε)/2,
        (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
        (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
        2 - (2*(1/16-1/10^5) - ε) - 4*α,
        2 + (2*(1/16-1/10^5) - ε) - 4*α,
        (s - α)/2] : List ℝ).toFinset)
    rw [abs_le, abs_le]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := h
      constructor
      · linarith
      · by_contra hc
        refine hzu ⟨?_, ?_⟩ <;> linarith
    · intro h
      obtain ⟨h1, h2⟩ := h
      constructor
      · by_contra hc
        refine hzl ⟨?_, ?_⟩ <;> linarith
      · linarith
  · -- `|4α + β - 2| ≤ θ - ε`
    have hzu := hno (2 + (2*(1/16-1/10^5) - ε) - 4*α) (by simp : (2 + (2*(1/16-1/10^5) - ε) - 4*α) ∈ ([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
        (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
        (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        (α + 2*(1/16-1/10^5) - ε)/2,
        (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
        (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
        2 - (2*(1/16-1/10^5) - ε) - 4*α,
        2 + (2*(1/16-1/10^5) - ε) - 4*α,
        (s - α)/2] : List ℝ).toFinset)
    have hzl := hno (2 - (2*(1/16-1/10^5) - ε) - 4*α) (by simp : (2 - (2*(1/16-1/10^5) - ε) - 4*α) ∈ ([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
        (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
        (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        (α + 2*(1/16-1/10^5) - ε)/2,
        (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
        (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
        2 - (2*(1/16-1/10^5) - ε) - 4*α,
        2 + (2*(1/16-1/10^5) - ε) - 4*α,
        (s - α)/2] : List ℝ).toFinset)
    rw [abs_le, abs_le]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := h
      constructor
      · linarith
      · by_contra hc
        refine hzu ⟨?_, ?_⟩ <;> linarith
    · intro h
      obtain ⟨h1, h2⟩ := h
      constructor
      · by_contra hc
        refine hzl ⟨?_, ?_⟩ <;> linarith
      · linarith


/-! ### NEW: the good cell oscillation in the `b` variable -/

/-- `(s - α - β)/β` is antitone in `β > 0`. -/
private theorem arg_beta_anti {s α β β' : ℝ} (hβ : 0 < β) (hβ' : 0 < β') (h : β ≤ β')
    (hsa : α ≤ s) :
    (s - α - β')/β' ≤ (s - α - β)/β := by
  have e1 : (s - α - β')/β' = (s - α)/β' - 1 := by
    rw [sub_div, div_self (ne_of_gt hβ')]
  have e2 : (s - α - β)/β = (s - α)/β - 1 := by
    rw [sub_div, div_self (ne_of_gt hβ)]
  rw [e1, e2]
  have h1 : (s - α)/β' ≤ (s - α)/β := by
    have hsa0 : 0 ≤ s - α := by linarith
    exact div_le_div_of_nonneg_left hsa0 hβ h
  linarith

set_option maxHeartbeats 1000000 in
/-- One good `b`-cell: if the region does not change across the cell and the Buchstab argument
stays on one side of one, the `α`-integrand of the second passage moves by at most
`200 log Z / ((n-1) log^2 (n-1))` over the cell. -/
private theorem phi_cell_osc {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z s α : ℝ} (hZ : 1 < Z) {n : ℕ} (hn : 4 ≤ n) {t : ℝ}
    (ht1 : (n:ℝ) - 1 ≤ t) (ht2 : t ≤ (n:ℝ))
    (hα1 : 1/10 ≤ α) (hα2 : α ≤ 1/2) (hs0 : 1/2 ≤ s) (hs : s ≤ 1)
    (hreg : lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) ↔
            lowerTwoDiscarded ε α (Real.log t/Real.log Z))
    (hcase : 1 ≤ (s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z) ∨
             (s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z) < 1) :
    |(if lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) then
        ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z))/α else 0) -
      (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
        ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)| ≤
      200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := by
  have hZ0 : (0:ℝ) < Z := by linarith
  have hLZ : 0 < Real.log Z := Real.log_pos hZ
  have hn4 : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : (0:ℝ) < (n:ℝ) := by linarith
  have hnm : (3:ℝ) ≤ (n:ℝ) - 1 := by linarith
  have hnm0 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have ht0 : (0:ℝ) < t := by linarith
  have hα0 : (0:ℝ) < α := by linarith
  have hlogn : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlogm : 0 < Real.log ((n:ℝ)-1) := Real.log_pos (by linarith)
  have hβn : 0 < Real.log (n:ℝ)/Real.log Z := div_pos hlogn hLZ
  have hβt : 0 < Real.log t/Real.log Z := div_pos hlogt hLZ
  have hlogn_le : Real.log ((n:ℝ)-1) ≤ Real.log (n:ℝ) := Real.log_le_log hnm0 (by linarith)
  have hβle : Real.log t/Real.log Z ≤ Real.log (n:ℝ)/Real.log Z :=
    div_le_div_of_nonneg_right (Real.log_le_log ht0 ht2) hLZ.le
  have harganti : (s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z) ≤
      (s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z) :=
    arg_beta_anti hβt hβn hβle (by linarith)
  have hβdiff : Real.log (n:ℝ)/Real.log Z - Real.log t/Real.log Z ≤
      1/(((n:ℝ)-1)*Real.log Z) := by
    rw [← sub_div]
    have e : 1/(((n:ℝ)-1)*Real.log Z) = (1/((n:ℝ)-1))/Real.log Z := by field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ hLZ.le
    have h1 : Real.log (n:ℝ) - Real.log t ≤ ((n:ℝ) - t)/t := log_sub_log_le_div_new ht0 ht2
    have h2 : ((n:ℝ) - t)/t ≤ ((n:ℝ) - t)/((n:ℝ) - 1) :=
      div_le_div_of_nonneg_left (by linarith) hnm0 (by linarith)
    have h3 : ((n:ℝ) - t)/((n:ℝ) - 1) ≤ 1/((n:ℝ) - 1) := by
      rw [div_le_div_iff₀ hnm0 hnm0]
      nlinarith
    linarith
  rcases hcase with hu | hlt
  · -- the Buchstab argument is at least one at both points
    have hut : 1 ≤ (s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z) := le_trans hu harganti
    have hlip := buchstab_lipschitz_abs hω hz hu hut
    by_cases hD : lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z)
    · have hDt : lowerTwoDiscarded ε α (Real.log t/Real.log Z) := hreg.mp hD
      rw [if_pos hD, if_pos hDt, ← sub_div, abs_div, abs_of_pos hα0]
      -- the argument difference
      have e1 : (s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z) =
          (s - α)/(Real.log (n:ℝ)/Real.log Z) - 1 := by
        rw [sub_div, div_self (ne_of_gt hβn)]
      have e2 : (s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z) =
          (s - α)/(Real.log t/Real.log Z) - 1 := by
        rw [sub_div, div_self (ne_of_gt hβt)]
      have hargdiff : |(s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z) -
          (s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z)| ≤
          Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := by
        rw [e1, e2]
        have hmul : ((s - α)/(Real.log (n:ℝ)/Real.log Z) - 1) -
            ((s - α)/(Real.log t/Real.log Z) - 1) =
            (s - α) * (1/(Real.log (n:ℝ)/Real.log Z) - 1/(Real.log t/Real.log Z)) := by ring
        rw [hmul, abs_mul]
        have habs1 : |s - α| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith
        have hb2 : |1/(Real.log (n:ℝ)/Real.log Z) - 1/(Real.log t/Real.log Z)| ≤
            Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := by
          have hnum0 : 0 ≤ Real.log (n:ℝ)/Real.log Z - Real.log t/Real.log Z := by linarith
          have hβl : 0 < Real.log ((n:ℝ)-1)/Real.log Z := div_pos hlogm hLZ
          have ht_ge : Real.log ((n:ℝ)-1)/Real.log Z ≤ Real.log t/Real.log Z :=
            div_le_div_of_nonneg_right (Real.log_le_log hnm0 ht1) hLZ.le
          have hn_ge : Real.log ((n:ℝ)-1)/Real.log Z ≤ Real.log (n:ℝ)/Real.log Z :=
            div_le_div_of_nonneg_right (Real.log_le_log hnm0 (by linarith)) hLZ.le
          have hden : Real.log ((n:ℝ)-1)/Real.log Z * (Real.log ((n:ℝ)-1)/Real.log Z) ≤
              Real.log (n:ℝ)/Real.log Z * (Real.log t/Real.log Z) :=
            mul_le_mul hn_ge ht_ge (le_of_lt hβl) (le_trans (le_of_lt hβl) hn_ge)
          have e3 : 1/(Real.log (n:ℝ)/Real.log Z) - 1/(Real.log t/Real.log Z) =
              (Real.log t/Real.log Z - Real.log (n:ℝ)/Real.log Z) /
                ((Real.log (n:ℝ)/Real.log Z)*(Real.log t/Real.log Z)) := by
            field_simp
          have habs : |1/(Real.log (n:ℝ)/Real.log Z) - 1/(Real.log t/Real.log Z)| =
              (Real.log (n:ℝ)/Real.log Z - Real.log t/Real.log Z) /
                ((Real.log (n:ℝ)/Real.log Z)*(Real.log t/Real.log Z)) := by
            have hsig : |Real.log t/Real.log Z - Real.log (n:ℝ)/Real.log Z| =
                (Real.log (n:ℝ)/Real.log Z - Real.log t/Real.log Z) := by
              rw [abs_sub_comm, abs_of_nonneg hnum0]
            rw [e3, abs_div, abs_of_pos (mul_pos hβn hβt), hsig]
          have h3a : (Real.log (n:ℝ)/Real.log Z - Real.log t/Real.log Z) /
              (Real.log (n:ℝ)/Real.log Z * (Real.log t/Real.log Z)) ≤
              (1/(((n:ℝ)-1)*Real.log Z)) /
                (Real.log (n:ℝ)/Real.log Z * (Real.log t/Real.log Z)) :=
            div_le_div_of_nonneg_right hβdiff (by positivity)
          have h3b : (1/(((n:ℝ)-1)*Real.log Z)) /
                (Real.log (n:ℝ)/Real.log Z * (Real.log t/Real.log Z)) ≤
              (1/(((n:ℝ)-1)*Real.log Z)) /
                (Real.log ((n:ℝ)-1)/Real.log Z * (Real.log ((n:ℝ)-1)/Real.log Z)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden
          have hfin : (1/(((n:ℝ)-1)*Real.log Z)) /
              (Real.log ((n:ℝ)-1)/Real.log Z * (Real.log ((n:ℝ)-1)/Real.log Z)) =
              Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := by
            field_simp
          rw [habs]
          linarith [h3a, h3b, hfin]
        calc |s - α| * |1/(Real.log (n:ℝ)/Real.log Z) - 1/(Real.log t/Real.log Z)|
            ≤ 1 * (Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) :=
              mul_le_mul habs1 hb2 (abs_nonneg _) (by norm_num)
          _ = Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := by ring
      have h1 : |ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z)) -
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))| ≤
          Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := hlip.trans hargdiff
      have hb : |ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z)) -
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))| / α ≤
          (Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) / (1/10) := by
        have hb1 : |ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z)) -
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))| / α ≤
            (Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) / α :=
          div_le_div_of_nonneg_right h1 hα0.le
        have hb2 : (Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) / α ≤
            (Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) / (1/10) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hα1
        linarith
      have h2 : (Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) / (1/10) ≤
          200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := by
        have ee1 : (Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) / (1/10) =
            10 * (Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) := by field_simp
        have ee2 : 200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) =
            200 * (Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) := by ring
        rw [ee1, ee2]
        apply mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      linarith [hb, h2]
    · have hDt : ¬ lowerTwoDiscarded ε α (Real.log t/Real.log Z) := fun h => hD (hreg.mpr h)
      rw [if_neg hD, if_neg hDt, sub_zero, abs_zero]
      positivity
  · -- the Buchstab argument is below one at both points, so both values vanish
    have hnt : (s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z) < 1 :=
      lt_of_le_of_lt harganti hlt
    have e1 : (if lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) then
        ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z))/α else 0) = 0 := by
      by_cases hD : lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z)
      · rw [if_pos hD, hz _ hnt, zero_div]
      · rw [if_neg hD]
    have e2 : (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
        ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0) = 0 := by
      by_cases hD : lowerTwoDiscarded ε α (Real.log t/Real.log Z)
      · rw [if_pos hD, hz _ hlt, zero_div]
      · rw [if_neg hD]
    rw [e1, e2, sub_zero, abs_zero]
    positivity


/-! ### NEW: weight monotonicity, cell oscillation and the integrand bound -/

/-- `u log^2 u` is monotone on `[1, ∞)`, so `1/(u log^2 u)` is antitone there. -/
private theorem weight_mono {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    1/(b * Real.log b^2) ≤ 1/(a * Real.log a^2) := by
  have ha0 : (0:ℝ) < a := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  have hla0 : 0 < Real.log a := Real.log_pos ha
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha.le
  have hlab : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  have hlb : 0 ≤ Real.log b := le_trans hla hlab
  have h1 : a * Real.log a^2 ≤ b * Real.log b^2 := by
    have h2 : Real.log a^2 ≤ Real.log b^2 := by
      apply pow_le_pow_left₀ hla hlab
    exact mul_le_mul hab h2 (by positivity) (by linarith)
  exact one_div_le_one_div_of_le (by positivity) h1

/-- On the cell `[n-1, n]` the weight moves by at most its drop `1/((n-1)log^2(n-1)) -
1/(n log^2 n)`. -/
private theorem weight_cell_osc {n : ℕ} (hn : 4 ≤ n) {t : ℝ}
    (ht1 : (n:ℝ) - 1 ≤ t) (ht2 : t ≤ (n:ℝ)) :
    |1/((n:ℝ) * Real.log (n:ℝ)^2) - 1/(t * Real.log t^2)| ≤
      1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2) := by
  have hn4 : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have ht2' : t ≤ (n:ℝ) := ht2
  have hle1 : (1:ℝ) < t := by linarith
  have hle2 : (1:ℝ) < (n:ℝ) - 1 := by linarith
  have hWt : 1/((n:ℝ) * Real.log (n:ℝ)^2) ≤ 1/(t * Real.log t^2) :=
    weight_mono hle1 ht2'
  have hWm : 1/(t * Real.log t^2) ≤ 1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) :=
    weight_mono hle2 ht1
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- Telescoping weight drop: `∑_{N < n ≤ B} (w(n-1) - w(n)) = w(N) - w(B) ≤ w(N)`. -/
private theorem tel_weight {N B : ℕ} (hN : 4 ≤ N) :
    (∑ n ∈ Finset.Ioc N B,
        (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2))) ≤
      1/((N:ℝ) * Real.log (N:ℝ)^2) := by
  have htel : ∀ B' : ℕ, N ≤ B' →
      (∑ n ∈ Finset.Ioc N B',
          (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2)))
        = 1/((N:ℝ) * Real.log (N:ℝ)^2) - 1/((B':ℝ) * Real.log (B':ℝ)^2) := by
    intro B' hB'
    induction B', hB' using Nat.le_induction with
    | base => simp
    | succ b hb ih =>
      rw [Finset.sum_Ioc_succ_top hb, ih]
      have hcast : ((b + 1 : ℕ) : ℝ) = (b:ℝ) + 1 := by push_cast; ring
      have hsub : (b:ℝ) + 1 - 1 = (b:ℝ) := by ring
      rw [hcast, hsub]
      ring
  rcases le_or_gt N B with h | h
  · rw [htel B h]
    have hN4 : (4:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hpos : (0:ℝ) < 1/((B:ℝ) * Real.log (B:ℝ)^2) := by
      have hB4 : (4:ℝ) ≤ (B:ℝ) := by
        have : 4 ≤ B := by omega
        exact_mod_cast this
      have hlog : 0 < Real.log (B:ℝ) := Real.log_pos (by linarith)
      positivity
    linarith
  · have hempty : Finset.Ioc N B = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    have hN4 : (4:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hlog : 0 < Real.log (N:ℝ) := Real.log_pos (by linarith)
    positivity

/-- `|Φ| ≤ 10` for the `α`-integrand of the second passage, for `α, β ≥ 1/10`. -/
private theorem phi_abs_le {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z s α β : ℝ} (hα1 : 1/10 ≤ α) :
    |(if lowerTwoDiscarded ε α β then ω ((s - α - β)/β)/α else 0)| ≤ 10 := by
  have hα0 : (0:ℝ) < α := by linarith
  have hw1 : ω ((s - α - β)/β) ≤ 1 :=
    LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz _
  have hw0 : 0 ≤ ω ((s - α - β)/β) :=
    Decomp514a.two_density_buchstab_nonneg hω hz _
  have hinv : 1/α ≤ 10 := by
    rw [div_le_iff₀ hα0]
    linarith
  by_cases h : lowerTwoDiscarded ε α β
  · rw [if_pos h, abs_div, abs_of_pos hα0]
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ ω ((s - α - β)/β))]
    rw [div_le_iff₀ hα0]
    calc ω ((s - α - β)/β) ≤ 1 := hw1
      _ ≤ 10 * α := by nlinarith
  · rw [if_neg h, abs_zero]
    norm_num



/-- `1/(t log^2 t)` times the `α`-integrand is at most `10/(t log^2 t)`. -/
private theorem phi_weight_abs_le {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z s α : ℝ} (hα1 : 1/10 ≤ α) (t : ℝ) (ht : 1 < t) :
    |(1/(t * Real.log t^2)) *
      (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
        ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)| ≤
      10 * (1/(t * Real.log t^2)) := by
  have hw : 0 < 1/(t * Real.log t^2) := by
    have : 0 < Real.log t := Real.log_pos ht
    positivity
  have h1 : |if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
      ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0| ≤ 10 :=
    phi_abs_le hω hz (ε := ε) (Z := Z) (s := s) (α := α) (β := Real.log t/Real.log Z) hα1
  calc |(1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)|
      = (1/(t * Real.log t^2)) *
        |if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0| := by
        rw [abs_mul, abs_of_pos hw]
    _ ≤ (1/(t * Real.log t^2)) * 10 := mul_le_mul_of_nonneg_left h1 (le_of_lt hw)
    _ = 10 * (1/(t * Real.log t^2)) := by ring

/-! ### NEW: the second passage at one point `α` -/

set_option maxHeartbeats 150000000 in
/-- The sum over the integer variable against the integral, cell by cell: the first half of the
second passage, with the weight telescoping. -/
private theorem second_passage_cell {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z s : ℝ} (hε8 : ε ≤ 1/10^8) (hZ : 1 < Z) (hZbig : (2:ℝ)^20 ≤ Z)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) {α : ℝ} (hα1 : 1/10 ≤ α) (hα2 : α ≤ 1/2) :
    |(∑ b ∈ Finset.Ioc ⌊Z^(1/10:ℝ)⌋₊ ⌊Z^(1/2:ℝ)⌋₊,
        (1/((b:ℝ) * Real.log (b:ℝ)^2)) *
          (if lowerTwoDiscarded ε α (Real.log (b:ℝ)/Real.log Z) then
            ω ((s - α - Real.log (b:ℝ)/Real.log Z)/(Real.log (b:ℝ)/Real.log Z))/α else 0)) -
      (∫ t in ((⌊Z^(1/10:ℝ)⌋₊ : ℝ))..((⌊Z^(1/2:ℝ)⌋₊ : ℝ)), (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0))| ≤
      500000 * (1 + Real.log Z) /
        (((⌊Z^(1/10:ℝ)⌋₊ : ℝ) - 1) * Real.log ((⌊Z^(1/10:ℝ)⌋₊ : ℝ) - 1)^2) := by
  classical
  have hZ0 : (0:ℝ) < Z := by linarith
  have hLZ : (0:ℝ) < Real.log Z := Real.log_pos hZ
  set u : ℝ := Z^(1/10:ℝ) with hu
  set v : ℝ := Z^(1/2:ℝ) with hv
  set B0 : ℕ := ⌊u⌋₊ with hB0
  set B1 : ℕ := ⌊v⌋₊ with hB1
  have hu4 : (4:ℝ) ≤ u := by
    have h1 : ((2:ℝ)^20)^(1/10:ℝ) ≤ Z^(1/10:ℝ) :=
      Real.rpow_le_rpow (by positivity) hZbig (by norm_num)
    have h2 : ((2:ℝ)^20)^(1/10:ℝ) = 4 := by
      rw [← Real.rpow_natCast (2:ℝ) 20, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [hu]
    linarith
  have hu0 : (0:ℝ) < u := by linarith
  have huv : u ≤ v := by
    rw [hu, hv]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)
  have hB0ge : 4 ≤ B0 := by
    rw [hB0]
    exact Nat.le_floor (by push_cast; exact hu4)
  have hB0le : ((B0:ℝ)) ≤ u := by
    rw [hB0]; exact Nat.floor_le (by positivity)
  have hB1le : ((B1:ℝ)) ≤ v := by
    rw [hB1]; exact Nat.floor_le (by positivity)
  have hB0B1 : B0 ≤ B1 := by
    have h1 : (B0:ℝ) ≤ v := le_trans hB0le huv
    rw [hB1]
    exact Nat.le_floor h1
  have hB0w : (1:ℝ) ≤ (B0:ℝ) := by
    have : 1 ≤ B0 := by omega
    exact_mod_cast this
  have hB0R4 : (4:ℝ) ≤ (B0:ℝ) := by exact_mod_cast hB0ge
  have huB1 : u ≤ (B1:ℝ) := by
    -- `u + 1 ≤ v` and `v - 1 ≤ B1`
    have hvpow : v = u^5 := by
      rw [hu, hv, ← Real.rpow_natCast]
      rw [show (1/2:ℝ) = (1/10:ℝ) * 5 by norm_num, Real.rpow_mul (le_of_lt hZ0)]
      norm_num
    have huv1 : u + 1 ≤ v := by
      rw [hvpow]
      have hpow : (4:ℝ)^4 ≤ u^4 := pow_le_pow_left₀ (by norm_num) hu4 4
      have hmul : u * 4^4 ≤ u^5 := by
        rw [show u^5 = u * u^4 by ring]
        exact mul_le_mul_of_nonneg_left hpow (by linarith)
      nlinarith [hmul, hu4]
    have hfl : v - 1 ≤ (B1:ℝ) := by
      rw [hB1]
      have := Nat.lt_floor_add_one v
      linarith
    linarith
  have hε8' : ε ≤ 1/8 := by linarith
  -- the switch points and the bad cells
  set T : Finset ℝ := ([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
        (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
        (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        (α + 2*(1/16-1/10^5) - ε)/2,
        (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
        (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
        2 - (2*(1/16-1/10^5) - ε) - 4*α,
        2 + (2*(1/16-1/10^5) - ε) - 4*α,
        (s - α)/2] : List ℝ).toFinset with hT
  set P : ℕ → Prop := fun n => ∃ τ ∈ T, Real.log ((n:ℝ)-1)/Real.log Z ≤ τ ∧
    τ ≤ Real.log (n:ℝ)/Real.log Z with hP
  -- the per cell allowance
  -- the `α`-integrand is measurable and bounded by `10 / (t log^2 t)`
  have hΦmeas : Measurable (fun t : ℝ => if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
      ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0) :=
    phi_measurable (measurable_buchstab_new hω hz) (Z := Z) (s := s) (α := α) (ε := ε)
  have hWmeas : Measurable (fun t : ℝ => 1/(t * Real.log t^2)) := by measurability
  have hphimeas : Measurable (fun t : ℝ => (1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) := hWmeas.mul hΦmeas
  have hphib : ∀ t : ℝ, 1 < t → |(fun t : ℝ => (1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t| ≤
        10 * (1/(t * Real.log t^2)) := by
    intro t ht
    have hw : 0 < 1/(t * Real.log t^2) := by
      have : 0 < Real.log t := Real.log_pos ht
      positivity
    have h1 : |if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
        ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0| ≤ 10 :=
      phi_abs_le hω hz (ε := ε) (Z := Z) (s := s) (α := α) (β := Real.log t/Real.log Z) hα1
    calc |(1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)|
        = (1/(t * Real.log t^2)) *
          |if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0| := by
          rw [abs_mul, abs_of_pos hw]
      _ ≤ (1/(t * Real.log t^2)) * 10 := mul_le_mul_of_nonneg_left h1 (le_of_lt hw)
      _ = 10 * (1/(t * Real.log t^2)) := by ring
  -- `phi_cell_osc`'s constant, shifted: `200 log Z / ((n-1) log^2 (n-1))`, the weight drop, and
  -- the allowance of a cell carrying a jump
  have hint : ∀ n : ℕ, B0 < n →
      IntervalIntegrable (fun t : ℝ => (1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) volume ((n:ℝ) - 1) (n:ℝ) := by
    intro n hn
    have hn5 : (5:ℝ) ≤ (n:ℝ) := by
      have : 5 ≤ n := by omega
      exact_mod_cast this
    rw [intervalIntegrable_iff]
    have hle : ((n:ℝ) - 1) ≤ (n:ℝ) := by linarith
    rw [Set.uIoc_of_le hle]
    refine MeasureTheory.Integrable.of_bound hphimeas.aestronglyMeasurable.restrict
      (10 * (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2))) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    have hx1 : (1:ℝ) < x := by linarith [hx.1]
    have hbx := hphib x hx1
    have hmono : 1/(x * Real.log x^2) ≤ 1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) :=
      weight_mono (by linarith : (1:ℝ) < (n:ℝ) - 1) (le_of_lt hx.1)
    have hpos : (0:ℝ) < 1/(x * Real.log x^2) := by
      have : 0 < Real.log x := Real.log_pos hx1
      positivity
    rw [Real.norm_eq_abs]
    exact hbx.trans (mul_le_mul_of_nonneg_left hmono (by norm_num))
  have hδ0 : ∀ n : ℕ, B0 < n → 0 ≤
      ((1/((n:ℝ) * Real.log (n:ℝ)^2)) *
          (200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2))
        + 10 * (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2))
        + (if P n then 20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) else 0)) := by
    intro n hn
    have hnR : (B0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hn2 : (2:ℝ) ≤ (n:ℝ) := by linarith
    have hnm1 : (1:ℝ) < (n:ℝ) - 1 := by linarith
    have hdrop : 0 ≤ 1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2) := by
      have h := weight_mono hnm1 (by linarith : ((n:ℝ)-1) ≤ (n:ℝ))
      linarith
    have hWn : 0 ≤ 1/((n:ℝ) * Real.log (n:ℝ)^2) := by
      have : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
      positivity
    have hcoef : 0 ≤ 200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := by
      have h1 : 0 < Real.log ((n:ℝ)-1) := Real.log_pos hnm1
      positivity
    have hthird : 0 ≤ (if P n then 20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) else 0) := by
      split_ifs
      · have : 0 < Real.log (B0:ℝ) := Real.log_pos (by linarith)
        positivity
      · norm_num
    have := mul_nonneg hWn hcoef
    linarith
  -- the per cell oscillation
  have hosc : ∀ n : ℕ, B0 < n → ∀ t ∈ Set.Icc ((n:ℝ) - 1) (n:ℝ),
      |(fun t : ℝ => (1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) (n:ℝ) -
       (fun t : ℝ => (1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t| ≤
      ((1/((n:ℝ) * Real.log (n:ℝ)^2)) *
          (200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2))
        + 10 * (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2))
        + (if P n then 20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) else 0)) := by
    intro n hn t ht
    obtain ⟨ht1, ht2⟩ := ht
    have hn4n : 4 ≤ n := by omega
    have hn5n : 5 ≤ n := by omega
    have hnR : (B0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hn5 : (5:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn5n
    have hn4 : (4:ℝ) ≤ (n:ℝ) := by linarith
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    have hnm0 : (0:ℝ) < (n:ℝ) - 1 := by linarith
    have hnm1 : (1:ℝ) < (n:ℝ) - 1 := by linarith
    have ht1' : (4:ℝ) ≤ t := by linarith
    have ht0 : (0:ℝ) < t := by linarith
    have ht1'' : (1:ℝ) < t := by linarith
    have htn : t ≤ (n:ℝ) := ht2
    have hWosc : |1/((n:ℝ) * Real.log (n:ℝ)^2) - 1/(t * Real.log t^2)| ≤
        1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2) :=
      weight_cell_osc hn4n ht1 ht2
    have hWn0 : (0:ℝ) < 1/((n:ℝ) * Real.log (n:ℝ)^2) := by
      have : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
      positivity
    have hWB0 : (0:ℝ) ≤ 1/((B0:ℝ) * Real.log (B0:ℝ)^2) := by
      have : 0 < Real.log (B0:ℝ) := Real.log_pos (by linarith)
      positivity
    have hB0t : (B0:ℝ) ≤ t := by
      have h1 : (B0:ℝ) + 1 ≤ (n:ℝ) := by
        have h2 : B0 + 1 ≤ n := by omega
        exact_mod_cast h2
      linarith
    have hB0n : (B0:ℝ) ≤ (n:ℝ) := by
      have h2 : B0 ≤ n := by omega
      exact_mod_cast h2
    by_cases hPn : P n
    · -- a cell carrying a jump: the crude bound
      have hthird : (if P n then 20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) else 0) =
          20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) := by rw [if_pos hPn]
      have hWB0t : 1/(t * Real.log t^2) ≤ 1/((B0:ℝ) * Real.log (B0:ℝ)^2) :=
        weight_mono (by linarith : (1:ℝ) < (B0:ℝ)) hB0t
      have hWB0n : 1/((n:ℝ) * Real.log (n:ℝ)^2) ≤ 1/((B0:ℝ) * Real.log (B0:ℝ)^2) :=
        weight_mono (by linarith : (1:ℝ) < (B0:ℝ)) hB0n
      have h1 : |(1/((n:ℝ) * Real.log (n:ℝ)^2)) *
          (if lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) then
            ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z))/α else 0)| ≤
          10 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) := by
        have h2 := hphib _ (by linarith : (1:ℝ) < (n:ℝ))
        exact h2.trans (mul_le_mul_of_nonneg_left hWB0n (by norm_num))
      have h2 : |(1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)| ≤
          10 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) := by
        have h3 := hphib t ht1''
        exact h3.trans (mul_le_mul_of_nonneg_left hWB0t (by norm_num))
      have htri : |(1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            (if lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) then
              ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z))/α else 0) -
          (1/(t * Real.log t^2)) *
            (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)| ≤
          20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) := by
        refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
        · linarith [abs_le.mp h2, abs_le.mp h1]
        · linarith [abs_le.mp h1, abs_le.mp h2]
      have hcoef : (0:ℝ) ≤ 200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := by
        have : 0 < Real.log ((n:ℝ)-1) := Real.log_pos hnm1
        positivity
      have hdrop : 0 ≤ 1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2) := by
        have hm := weight_mono hnm1 (by linarith : ((n:ℝ)-1) ≤ (n:ℝ))
        linarith
      have := mul_nonneg hWn0.le hcoef
      rw [hthird]
      linarith
    · -- a good cell
      have hthird : (if P n then 20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) else 0) = 0 := by
        rw [if_neg hPn]
      -- no switch point in the cell
      have hnoCell : ∀ τ ∈ ([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
          (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
          (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
          (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
          (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
          1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
          1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
          (α + 2*(1/16-1/10^5) - ε)/2,
          (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
          (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
          2 - (2*(1/16-1/10^5) - ε) - 4*α,
          2 + (2*(1/16-1/10^5) - ε) - 4*α,
          (s - α)/2] : List ℝ).toFinset,
          ¬(Real.log ((n:ℝ)-1)/Real.log Z ≤ τ ∧ τ ≤ Real.log (n:ℝ)/Real.log Z) := by
        intro τ hτ hc
        have hτT : τ ∈ T := by
          rw [hT]
          simpa using hτ
        exact hPn ⟨τ, hτT, hc⟩
      have hβt0 : (0:ℝ) < Real.log t/Real.log Z :=
        div_pos (Real.log_pos ht1'') hLZ
      have hβn0 : (0:ℝ) < Real.log (n:ℝ)/Real.log Z :=
        div_pos (Real.log_pos (by linarith)) hLZ
      have hβtn : Real.log t/Real.log Z ≤ Real.log (n:ℝ)/Real.log Z :=
        div_le_div_of_nonneg_right (Real.log_le_log ht0 htn) hLZ.le
      have hβm_t : Real.log ((n:ℝ)-1)/Real.log Z ≤ Real.log t/Real.log Z :=
        div_le_div_of_nonneg_right (Real.log_le_log hnm0 ht1) hLZ.le
      -- restrict the switch points to the sub-cell `[β_t, β_n]`
      have hnoSub : ∀ τ ∈ ([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
          (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
          (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
          (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
          (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
          1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
          1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
          (α + 2*(1/16-1/10^5) - ε)/2,
          (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
          (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
          2 - (2*(1/16-1/10^5) - ε) - 4*α,
          2 + (2*(1/16-1/10^5) - ε) - 4*α,
          (s - α)/2] : List ℝ).toFinset,
          ¬(Real.log t/Real.log Z ≤ τ ∧ τ ≤ Real.log (n:ℝ)/Real.log Z) := by
        intro τ hτ hc
        exact hnoCell τ hτ ⟨le_trans hβm_t hc.1, hc.2⟩
      have hreg0 := cell_region_const_beta (ε := ε) (α := α) (s := s) hβtn hnoSub
      -- the Buchstab argument case
      have hargTh := hnoCell _ (by simp : (s - α)/2 ∈ ([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
          (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
          (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
          (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
          (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
          1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
          1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
          (α + 2*(1/16-1/10^5) - ε)/2,
          (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
          (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
          2 - (2*(1/16-1/10^5) - ε) - 4*α,
          2 + (2*(1/16-1/10^5) - ε) - 4*α,
          (s - α)/2] : List ℝ).toFinset)
      have hcase : 1 ≤ (s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z) ∨
          (s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z) < 1 := by
        by_contra hc
        push_neg at hc
        obtain ⟨h1, h2⟩ := hc
        have e1 : (s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z) =
            (s - α)/(Real.log (n:ℝ)/Real.log Z) - 1 := by
          rw [sub_div, div_self (ne_of_gt hβn0)]
        have e2 : (s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z) =
            (s - α)/(Real.log t/Real.log Z) - 1 := by
          rw [sub_div, div_self (ne_of_gt hβt0)]
        rw [e1] at h1
        rw [e2] at h2
        -- `2 β_t ≤ s - α < 2 β_n`, so `(s - α)/2` sits strictly between the two switch points
        have h2a : (2:ℝ) ≤ (s - α)/(Real.log t/Real.log Z) := by linarith
        have h1a : (s - α)/(Real.log (n:ℝ)/Real.log Z) < 2 := by linarith
        have h2ge : 2 * (Real.log t/Real.log Z) ≤ s - α := by
          have := (le_div_iff₀ hβt0).mp h2a
          linarith
        have h1lt : s - α < 2 * (Real.log (n:ℝ)/Real.log Z) := by
          have := (div_lt_iff₀ hβn0).mp h1a
          linarith
        refine hargTh ⟨?_, ?_⟩
        · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
          linarith
        · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
          linarith
      -- the cell oscillation of `Φ`
      have hΦosc : |(if lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) then
            ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z))/α else 0) -
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)| ≤
          200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) :=
        phi_cell_osc hω hz (ε := ε) (Z := Z) (s := s) (α := α) (n := n) hZ
          hn4n ht1 ht2 hα1 hα2 hs0 hs1 hreg0.symm hcase
      have hΦt : |(if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)| ≤ 10 :=
        phi_abs_le hω hz (ε := ε) (Z := Z) (s := s) (α := α) (β := Real.log t/Real.log Z) hα1
      -- split the difference of the two products
      have hsplit : (1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            (if lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) then
              ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z))/α else 0) -
          (1/(t * Real.log t^2)) *
            (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0) =
          (1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            ((if lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) then
              ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z))/α else 0) -
             (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) +
          ((1/((n:ℝ) * Real.log (n:ℝ)^2)) - 1/(t * Real.log t^2)) *
            (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0) := by
        ring
      have h1 : |(1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            ((if lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) then
              ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z))/α else 0) -
             (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0))| ≤
          (1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            (200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) := by
        rw [abs_mul, abs_of_pos hWn0]
        exact mul_le_mul_of_nonneg_left hΦosc hWn0.le
      have hdrop0 : (0:ℝ) ≤ 1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) -
          1/((n:ℝ) * Real.log (n:ℝ)^2) := by
        have hm := weight_mono hnm1 (by linarith : ((n:ℝ)-1) ≤ (n:ℝ))
        linarith
      have h2 : |((1/((n:ℝ) * Real.log (n:ℝ)^2)) - 1/(t * Real.log t^2)) *
            (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)| ≤
          10 * (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2)) := by
        rw [abs_mul]
        calc |1/((n:ℝ) * Real.log (n:ℝ)^2) - 1/(t * Real.log t^2)| *
              |(if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
                ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)|
            ≤ (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2)) * 10 :=
              mul_le_mul hWosc hΦt (abs_nonneg _) hdrop0
          _ = 10 * (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) -
                1/((n:ℝ) * Real.log (n:ℝ)^2)) := by ring
      have htri := abs_add_le ((1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            ((if lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) then
              ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z))/α else 0) -
             (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)))
          (((1/((n:ℝ) * Real.log (n:ℝ)^2)) - 1/(t * Real.log t^2)) *
            (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0))
      rw [hsplit, hthird, add_zero]
      linarith [h1, h2, htri]
  -- the cell by cell comparison of the sum and the integral over `(B0, B1]`
  have hcell : |(∑ n ∈ Finset.Ioc B0 B1,
        (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) (n:ℝ)) -
      (∫ t in (B0:ℝ)..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t)| ≤
      (∑ n ∈ Finset.Ioc B0 B1,
        ((1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            (200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2))
          + 10 * (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2))
          + (if P n then 20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) else 0))) :=
    sum_sub_integral_le_of_cell _ _ B0 hδ0 hint hosc B1 hB0B1
  -- the number of cells carrying a jump
  have hTcard : T.card ≤ 15 := by
    rw [hT]
    have h := List.toFinset_card_le (l := ([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
      (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
      (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
      (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
      (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
      1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
      1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
      (α + 2*(1/16-1/10^5) - ε)/2,
      (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
      (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
      2 - (2*(1/16-1/10^5) - ε) - 4*α,
      2 + (2*(1/16-1/10^5) - ε) - 4*α,
      (s - α)/2] : List ℝ))
    simpa using h
  have hbadcard : ((Finset.Ioc B0 B1).filter P).card ≤ 30 := by
    have h2T : ((Finset.Ioc B0 B1).filter P).card ≤ 2 * T.card := by
      set S : Finset ℕ := (T.image (fun τ => Nat.floor (Z ^ τ) + 1)) ∪
        (T.image (fun τ => Nat.floor (Z ^ τ))) with hS
      have hsub : (Finset.Ioc B0 B1).filter P ⊆ S := by
        intro n hn
        obtain ⟨hn1, hnP⟩ := Finset.mem_filter.mp hn
        obtain ⟨τ, hτT, hP1, hP2⟩ := hnP
        have hn2 : 2 ≤ n := by
          have := (Finset.mem_Ioc.mp hn1).1
          omega
        have hcast : (((n - 1 : ℕ) : ℝ)) = (n:ℝ) - 1 := by
          have h1n : 1 ≤ n := by omega
          rw [Nat.cast_sub h1n]
          simp
        have hn1' : 1 ≤ n - 1 := by omega
        have hlog1 : Real.log (((n - 1 : ℕ) : ℝ)) / Real.log Z ≤ τ := by
          rw [hcast]; exact hP1
        have hlog2 : τ ≤ Real.log ((((n - 1 : ℕ) : ℝ)) + 1) / Real.log Z := by
          rw [hcast]
          have e : ((n:ℝ) - 1) + 1 = (n:ℝ) := by ring
          rw [e]; exact hP2
        have hfl := switch_cell_floor hZ (a := n - 1) hn1' hlog1 hlog2
        rw [hS]
        simp only [Finset.mem_union, Finset.mem_image]
        have hpred : (n - 1) + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
        rcases hfl with h | h
        · refine Or.inl ⟨τ, hτT, ?_⟩
          rw [h, hpred]
        · refine Or.inr ⟨τ, hτT, ?_⟩
          rw [h, hpred]
      calc ((Finset.Ioc B0 B1).filter P).card ≤ S.card := Finset.card_le_card hsub
        _ ≤ (T.image (fun τ => Nat.floor (Z ^ τ) + 1)).card +
              (T.image (fun τ => Nat.floor (Z ^ τ))).card := Finset.card_union_le _ _
        _ ≤ T.card + T.card := by
            have h1 := Finset.card_image_le (s := T) (f := fun τ => Nat.floor (Z ^ τ) + 1)
            have h2 := Finset.card_image_le (s := T) (f := fun τ => Nat.floor (Z ^ τ))
            omega
        _ = 2 * T.card := by ring
    exact le_trans h2T (by omega)
  -- the sum of the allowances
  have hsumδ : (∑ n ∈ Finset.Ioc B0 B1,
        ((1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            (200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2))
          + 10 * (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2))
          + (if P n then 20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) else 0))) ≤
      500000 * (1 + Real.log Z) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) := by
    have hB0_4 : 4 ≤ B0 := hB0ge
    have hB0R4'' : (4:ℝ) ≤ (B0:ℝ) := by exact_mod_cast hB0_4
    have hlogB0 : 0 < Real.log ((B0:ℝ) - 1) := Real.log_pos (by linarith)
    have hlogle1 : (1:ℝ) ≤ Real.log ((B0:ℝ) - 1) := by
      have h : Real.log 3 ≤ Real.log ((B0:ℝ) - 1) := by
        apply Real.log_le_log (by norm_num)
        linarith
      have h4 : (1:ℝ) ≤ Real.log 3 := by
        rw [Real.le_log_iff_exp_le (by norm_num)]
        linarith [Real.exp_one_lt_d9]
      linarith
    have hden : 0 < ((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2 :=
      mul_pos (by linarith) (pow_pos hlogB0 2)
    have hden4 : 0 < ((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^4 :=
      mul_pos (by linarith) (pow_pos hlogB0 4)
    have hWB0 : 0 ≤ 1/((B0:ℝ) * Real.log (B0:ℝ)^2) := by
      have hlogB : 0 < Real.log (B0:ℝ) := Real.log_pos (by linarith)
      positivity
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    -- the first piece: `∑ w(n) A(n) ≤ 200 log Z / ((B0-1) log^4 (B0-1))`
    have hshift : (∑ n ∈ Finset.Ioc B0 B1,
          1/(((n:ℝ)-1)^2 * Real.log ((n:ℝ)-1)^4)) =
        ∑ m ∈ Finset.Ioc (B0 - 1) (B1 - 1), 1/((m:ℝ)^2 * Real.log (m:ℝ)^4) := by
      refine Finset.sum_bij (fun n _ => n - 1) ?_ ?_ ?_ ?_
      · intro n hn
        obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
        exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
      · intro n1 hn1 n2 hn2 he
        obtain ⟨h1, _⟩ := Finset.mem_Ioc.mp hn1
        obtain ⟨h3, _⟩ := Finset.mem_Ioc.mp hn2
        omega
      · intro m hm
        obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hm
        refine ⟨m + 1, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro n hn
        obtain ⟨h1, _⟩ := Finset.mem_Ioc.mp hn
        have e : (((n - 1 : ℕ)) : ℝ) = (n:ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]
          simp
        rw [e]
    have hpiece1 : (∑ n ∈ Finset.Ioc B0 B1,
          (1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            (200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2))) ≤
        200 * Real.log Z / (((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^4) := by
      have hstep : ∀ n ∈ Finset.Ioc B0 B1,
          (1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            (200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) ≤
          200 * Real.log Z * (1/(((n:ℝ)-1)^2 * Real.log ((n:ℝ)-1)^4)) := by
        intro n hn
        have hn2 : 2 ≤ n := by
          have := (Finset.mem_Ioc.mp hn).1
          omega
        have hnR2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
        have hB0_5 : 4 ≤ B0 := hB0ge
        have hn5 : (5:ℝ) ≤ (n:ℝ) := by
          have h1 : (B0:ℝ) + 1 ≤ (n:ℝ) := by
            have h3 : B0 + 1 ≤ n := by
              have := (Finset.mem_Ioc.mp hn).1
              omega
            exact_mod_cast h3
          have h2 : (4:ℝ) ≤ (B0:ℝ) := by exact_mod_cast hB0_4
          linarith
        have hnm1 : (1:ℝ) < (n:ℝ) - 1 := by linarith
        have hlogm : 0 < Real.log ((n:ℝ)-1) := Real.log_pos hnm1
        have hW : 1/((n:ℝ) * Real.log (n:ℝ)^2) ≤ 1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) :=
          weight_mono hnm1 (by linarith : ((n:ℝ)-1) ≤ (n:ℝ))
        have hpos : 0 < 1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := by positivity
        calc (1/((n:ℝ) * Real.log (n:ℝ)^2)) *
              (200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2))
            = 200 * Real.log Z * ((1/((n:ℝ) * Real.log (n:ℝ)^2)) *
                (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2))) := by ring
          _ ≤ 200 * Real.log Z * ((1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) *
                (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2))) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_right hW (le_of_lt hpos)
          _ = 200 * Real.log Z * (1/(((n:ℝ)-1)^2 * Real.log ((n:ℝ)-1)^4)) := by
              congr 1
              field_simp
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [← Finset.mul_sum, hshift]
      have hsum := sum_inv_sq_log_pow_le (A := B0 - 1) (B := B1 - 1)
        (by omega : 2 ≤ B0 - 1) (k := 4) (by norm_num)
      have hcast1 : (((B0 - 1 : ℕ)) : ℝ) = (B0:ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ B0)]
        simp
      rw [hcast1, one_div] at hsum
      have hfin : (0:ℝ) ≤ 200 * Real.log Z := by positivity
      exact mul_le_mul_of_nonneg_left hsum hfin
    -- the second piece: the telescoping weight drop
    have hpiece2 : (∑ n ∈ Finset.Ioc B0 B1,
          10 * (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2))) ≤
        10 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) := by
      rw [← Finset.mul_sum]
      have htel := tel_weight (N := B0) (B := B1) (by omega : 4 ≤ B0)
      linarith
    -- the third piece: the cells carrying a jump
    have hpiece3 : (∑ n ∈ Finset.Ioc B0 B1,
          (if P n then 20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) else 0)) ≤
        600 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
      have hc : ((Finset.Ioc B0 B1).filter P).card ≤ 30 := hbadcard
      have hcR : (((Finset.Ioc B0 B1).filter P).card : ℝ) ≤ 30 := by exact_mod_cast hc
      calc (((Finset.Ioc B0 B1).filter P).card : ℝ) *
            (20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)))
          ≤ 30 * (20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2))) := by
            apply mul_le_mul_of_nonneg_right hcR
            positivity
        _ = 600 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) := by ring
    -- the bookkeeping: `W(B0) ≤ 2/den` and `1/log^4 ≤ 1/log^2`
    have hWB0le : 1/((B0:ℝ) * Real.log (B0:ℝ)^2) ≤ 2/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := by
      have hW1 : 1/((B0:ℝ) * Real.log (B0:ℝ)^2) ≤ 1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) :=
        weight_mono (by linarith : (1:ℝ) < (B0:ℝ) - 1) (by linarith : ((B0:ℝ)-1) ≤ (B0:ℝ))
      have h2 : 1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) ≤
          2 * (1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)) := by
        have hpos : (0:ℝ) < 1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := by positivity
        linarith
      calc 1/((B0:ℝ) * Real.log (B0:ℝ)^2)
          ≤ 1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := hW1
        _ ≤ 2 * (1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)) := h2
        _ = 2/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := by rw [mul_one_div]
    have hlogle : ((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2 ≤ ((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^4 := by
      have h2 : Real.log ((B0:ℝ)-1)^2 ≤ Real.log ((B0:ℝ)-1)^4 :=
        pow_le_pow_right₀ hlogle1 (by norm_num : 2 ≤ 4)
      exact mul_le_mul_of_nonneg_left h2 (by linarith)
    have hpiece1' : 200 * Real.log Z / (((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^4) ≤
        200 * Real.log Z / (((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) :=
      div_le_div_of_nonneg_left (by positivity) hden hlogle
    have htot : 200 * Real.log Z / (((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)
        + 20/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)
        + 1200/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) ≤
        500000 * (1 + Real.log Z) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) := by
      have hlogZ0 : 0 ≤ Real.log Z := le_of_lt hLZ
      have hden0 : ((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2 ≠ 0 := ne_of_gt hden
      have e : 200 * Real.log Z / (((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)
          + 20/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)
          + 1200/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)
          = (200 * Real.log Z + 1220)/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := by
        field_simp
        ring
      rw [e, div_le_div_iff₀ hden hden]
      have h1 : 200 * Real.log Z + 1220 ≤ 500000 * (1 + Real.log Z) := by linarith
      exact mul_le_mul_of_nonneg_right h1 hden.le
    have h10 : 10 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) ≤
        20/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := by
      have h := mul_le_mul_of_nonneg_left hWB0le (by norm_num : (0:ℝ) ≤ 10)
      calc 10 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2))
          ≤ 10 * (2/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)) := h
        _ = 20/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := by ring
    have h600 : 600 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) ≤
        1200/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := by
      have h := mul_le_mul_of_nonneg_left hWB0le (by norm_num : (0:ℝ) ≤ 600)
      calc 600 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2))
          ≤ 600 * (2/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)) := h
        _ = 1200/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := by ring
    linarith [hpiece1, hpiece1', hpiece2, hpiece3, h10, h600, htot]
  exact hcell.trans hsumδ



set_option maxHeartbeats 20000000 in
/-- The second passage of display 5.17 at one point `α`. -/
private theorem second_passage_pointwise {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z s : ℝ} (hε8 : ε ≤ 1/10^8)
    (hZ : 1 < Z) (hZbig : (2:ℝ)^20 ≤ Z)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1)
    {α : ℝ} (hα1 : 1/10 ≤ α) (hα2 : α ≤ 1/2) :
    |(∑ b ∈ Finset.Ioc ⌊Z^(1/10:ℝ)⌋₊ ⌊Z^(1/2:ℝ)⌋₊,
        (1/((b:ℝ) * Real.log (b:ℝ)^2)) *
          (if lowerTwoDiscarded ε α (Real.log (b:ℝ)/Real.log Z) then
            ω ((s - α - Real.log (b:ℝ)/Real.log Z)/(Real.log (b:ℝ)/Real.log Z))/α else 0)) -
      (1/Real.log Z) * (∫ β in (1/10:ℝ)..(1/2:ℝ),
        (if lowerTwoDiscarded ε α β then ω ((s - α - β)/β)/(α*β^2) else 0))| ≤
      1000000 * (1 + Real.log Z) / (((⌊Z^(1/10:ℝ)⌋₊ : ℝ) - 1) * Real.log ((⌊Z^(1/10:ℝ)⌋₊ : ℝ) - 1)^2) := by
  classical
  have hZ0 : (0:ℝ) < Z := by linarith
  have hLZ : (0:ℝ) < Real.log Z := Real.log_pos hZ
  set u : ℝ := Z^(1/10:ℝ) with hu
  set v : ℝ := Z^(1/2:ℝ) with hv
  set B0 : ℕ := ⌊u⌋₊ with hB0
  set B1 : ℕ := ⌊v⌋₊ with hB1
  have hu4 : (4:ℝ) ≤ u := by
    have h1 : ((2:ℝ)^20)^(1/10:ℝ) ≤ Z^(1/10:ℝ) :=
      Real.rpow_le_rpow (by positivity) hZbig (by norm_num)
    have h2 : ((2:ℝ)^20)^(1/10:ℝ) = 4 := by
      rw [← Real.rpow_natCast (2:ℝ) 20, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [hu]
    linarith
  have hu0 : (0:ℝ) < u := by linarith
  have huv : u ≤ v := by
    rw [hu, hv]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)
  have hB0ge : 4 ≤ B0 := by
    rw [hB0]
    exact Nat.le_floor (by push_cast; exact hu4)
  have hB0le : ((B0:ℝ)) ≤ u := by
    rw [hB0]; exact Nat.floor_le (by positivity)
  have hB1le : ((B1:ℝ)) ≤ v := by
    rw [hB1]; exact Nat.floor_le (by positivity)
  have hB0B1 : B0 ≤ B1 := by
    have h1 : (B0:ℝ) ≤ v := le_trans hB0le huv
    rw [hB1]
    exact Nat.le_floor h1
  have hB0w : (1:ℝ) ≤ (B0:ℝ) := by
    have : 1 ≤ B0 := by omega
    exact_mod_cast this
  have hB0R4 : (4:ℝ) ≤ (B0:ℝ) := by exact_mod_cast hB0ge
  have huB1 : u ≤ (B1:ℝ) := by
    -- `u + 1 ≤ v` and `v - 1 ≤ B1`
    have hvpow : v = u^5 := by
      rw [hu, hv, ← Real.rpow_natCast]
      rw [show (1/2:ℝ) = (1/10:ℝ) * 5 by norm_num, Real.rpow_mul (le_of_lt hZ0)]
      norm_num
    have huv1 : u + 1 ≤ v := by
      rw [hvpow]
      have hpow : (4:ℝ)^4 ≤ u^4 := pow_le_pow_left₀ (by norm_num) hu4 4
      have hmul : u * 4^4 ≤ u^5 := by
        rw [show u^5 = u * u^4 by ring]
        exact mul_le_mul_of_nonneg_left hpow (by linarith)
      nlinarith [hmul, hu4]
    have hfl : v - 1 ≤ (B1:ℝ) := by
      rw [hB1]
      have := Nat.lt_floor_add_one v
      linarith
    linarith
  have hε8' : ε ≤ 1/8 := by linarith  -- the `α`-integrand is measurable, and bounded by `10 / (t log^2 t)`
  have hΦmeas : Measurable (fun t : ℝ => if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
      ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0) :=
    phi_measurable (measurable_buchstab_new hω hz) (Z := Z) (s := s) (α := α) (ε := ε)
  have hWmeas : Measurable (fun t : ℝ => 1/(t * Real.log t^2)) := by measurability
  have hphimeas : Measurable (fun t : ℝ => (1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) :=
    hWmeas.mul hΦmeas
  have hphib : ∀ t : ℝ, 1 < t → |(1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)| ≤
        10 * (1/(t * Real.log t^2)) :=
    fun t ht => phi_weight_abs_le hω hz hα1 t ht
  -- the sum against the integral, from the extracted cell comparison
  have hcell0 : |(∑ b ∈ Finset.Ioc B0 B1,
        (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) (b:ℝ)) -
      (∫ t in (B0:ℝ)..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t)| ≤
      500000 * (1 + Real.log Z) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) := by
    have h := second_passage_cell (ω := ω) hω hz hε8 hZ hZbig hs0 hs1 hα1 hα2
    have e1 : (⌊Z^(1/10:ℝ)⌋₊ : ℕ) = B0 := by rw [hB0, hu]
    have e2 : (⌊Z^(1/2:ℝ)⌋₊ : ℕ) = B1 := by rw [hB1, hv]
    rw [e1, e2] at h
    exact h
  -- the change of variables `t = Z^β`
  have hsub : (1/Real.log Z) * (∫ β in (1/10:ℝ)..(1/2:ℝ),
        (if lowerTwoDiscarded ε α β then ω ((s - α - β)/β)/(α*β^2) else 0)) =
      ∫ t in u..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t := by
    have h := integral_log_subst (Z := Z) hZ
      (g := fun β : ℝ => if lowerTwoDiscarded ε α β then ω ((s - α - β)/β)/(α*β^2) else 0)
    rw [hu, hv, ← h, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht0 : (0:ℝ) < t := by
      rw [Set.uIcc_of_le huv] at ht
      linarith [ht.1, hu0]
    have hlt : 0 < Real.log t := Real.log_pos (by
      rw [Set.uIcc_of_le huv] at ht
      linarith [ht.1, hu4])
    have hβ0 : (0:ℝ) < Real.log t / Real.log Z := div_pos hlt hLZ
    by_cases hD : lowerTwoDiscarded ε α (Real.log t/Real.log Z)
    · rw [if_pos hD, if_pos hD]
      field_simp
    · rw [if_neg hD, if_neg hD]
      ring
  -- the two slivers
  have hsliver : |(∫ t in u..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) -
      (∫ t in (B0:ℝ)..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t)| ≤
      500000 * (1 + Real.log Z) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) := by
    have hB0_1 : ((B0:ℝ)) ≤ u := hB0le
    have huB1' : u ≤ (B1:ℝ) := huB1
    have hB1v : ((B1:ℝ)) ≤ v := hB1le
    -- integrability of the pieces
    have hInt : ∀ p q : ℝ, (1:ℝ) < p → p ≤ q → IntervalIntegrable
        (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) volume p q := by
      intro p q hp hpq
      · rw [intervalIntegrable_iff]
        rw [Set.uIoc_of_le hpq]
        refine MeasureTheory.Integrable.of_bound hphimeas.aestronglyMeasurable.restrict
          (10 * (1/(p * Real.log p^2))) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        have hx1 : (1:ℝ) < x := lt_of_lt_of_le hp (le_of_lt hx.1)
        have hbx := hphib x hx1
        have hmono : 1/(x * Real.log x^2) ≤ 1/(p * Real.log p^2) :=
          weight_mono hp (le_of_lt hx.1)
        have hposx : (0:ℝ) < 1/(x * Real.log x^2) := by
          have : 0 < Real.log x := Real.log_pos hx1
          positivity
        rw [Real.norm_eq_abs]
        exact hbx.trans (mul_le_mul_of_nonneg_left hmono (by norm_num))
    have hsplit1 : (∫ t in u..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) =
        (∫ t in u..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) +
        (∫ t in (B1:ℝ)..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) :=
      (intervalIntegral.integral_add_adjacent_intervals (hInt u _ (by linarith) huB1')
        (hInt _ v (by linarith) hB1v)).symm
    have hsplit2 : (∫ t in (B0:ℝ)..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) =
        (∫ t in (B0:ℝ)..u, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) +
        (∫ t in u..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) :=
      (intervalIntegral.integral_add_adjacent_intervals (hInt _ _ (by linarith) hB0_1)
        (hInt _ _ (by linarith) huB1')).symm
    -- the lower sliver vanishes
    have hzero : (∫ t in (B0:ℝ)..u, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) = 0 := by
      apply integral_eq_zero_of_open hB0_1
      intro x hx1 hx2
      have hx0 : (0:ℝ) < x := by linarith
      have hxlog : 0 < Real.log x := Real.log_pos (by linarith)
      have hxle : Real.log x / Real.log Z ≤ 1/10 := by
        rw [div_le_iff₀ hLZ]
        have h2 : Real.log x ≤ Real.log u := Real.log_le_log hx0 (le_of_lt hx2)
        rw [hu, Real.log_rpow hZ0] at h2
        nlinarith [h2, hLZ]
      by_cases hD : lowerTwoDiscarded ε α (Real.log x / Real.log Z)
      · rw [if_pos hD]
        obtain ⟨hc, -⟩ := hD
        have hc' : (1+7*(2*(1/16-1/10^5)))/15 - 1/8 ≤ 1/10 := by norm_num
        linarith
      · rw [if_neg hD, mul_zero]
    -- the upper sliver is short
    have hupper : |(∫ t in (B1:ℝ)..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t)| ≤
        10 * (1/((B1:ℝ) * Real.log (B1:ℝ)^2)) := by
      have hb1 : (1:ℝ) < (B1:ℝ) := by
        have : (4:ℝ) ≤ (B1:ℝ) := le_trans hB0R4 (by exact_mod_cast hB0B1)
        linarith
      have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (B1:ℝ)) (b := v) (C := 10 * (1/((B1:ℝ) * Real.log (B1:ℝ)^2)))
        (f := fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0))
        (by
          intro x hx
          rw [Set.uIoc_of_le hB1v] at hx
          have hx1 : (1:ℝ) < x := lt_of_lt_of_le hb1 (le_of_lt hx.1)
          have hbx := hphib x hx1
          have hmono : 1/(x * Real.log x^2) ≤ 1/((B1:ℝ) * Real.log (B1:ℝ)^2) :=
            weight_mono hb1 (le_of_lt hx.1)
          exact hbx.trans (mul_le_mul_of_nonneg_left hmono (by norm_num)))
      rw [Real.norm_eq_abs] at hbnd
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ v - (B1:ℝ))] at hbnd
      refine hbnd.trans ?_
      have hlen : v - (B1:ℝ) ≤ 1 := by
        rw [hB1]
        linarith [Nat.lt_floor_add_one v]
      have hpos : (0:ℝ) ≤ 10 * (1/((B1:ℝ) * Real.log (B1:ℝ)^2)) := by
        have : (0:ℝ) < Real.log (B1:ℝ) := Real.log_pos hb1
        positivity
      calc 10 * (1/((B1:ℝ) * Real.log (B1:ℝ)^2)) * (v - (B1:ℝ))
          ≤ 10 * (1/((B1:ℝ) * Real.log (B1:ℝ)^2)) * 1 := by
            apply mul_le_mul_of_nonneg_left hlen
            positivity
        _ = 10 * (1/((B1:ℝ) * Real.log (B1:ℝ)^2)) := by ring
    -- assemble
    rw [hsplit1, hsplit2, hzero, zero_add]
    have htri : |(∫ t in u..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) +
        (∫ t in (B1:ℝ)..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) -
      (∫ t in u..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t)| ≤
        10 * (1/((B1:ℝ) * Real.log (B1:ℝ)^2)) := by
      have e : (∫ t in u..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
            (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) +
          (∫ t in (B1:ℝ)..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
            (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) -
        (∫ t in u..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
            (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) =
        (∫ t in (B1:ℝ)..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) := by
        ring
      rw [e]
      exact hupper
    have hB1le' : (1/((B1:ℝ) * Real.log (B1:ℝ)^2)) ≤
        2 * (1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)) := by
      have hB1_4 : (4:ℝ) ≤ (B1:ℝ) := le_trans hB0R4 (by exact_mod_cast hB0B1)
      have hlogB1 : (1:ℝ) < Real.log (B1:ℝ) := by
        have h : Real.log 3 < Real.log (B1:ℝ) := by
          apply Real.log_lt_log (by norm_num)
          linarith
        have h3 : (1:ℝ) ≤ Real.log 3 := by
          rw [Real.le_log_iff_exp_le (by norm_num)]
          linarith [Real.exp_one_lt_d9]
        linarith
      have hlogB0 : 0 < Real.log ((B0:ℝ)-1) := Real.log_pos (by
        have : (4:ℝ) ≤ (B0:ℝ) := by exact_mod_cast (by omega : 4 ≤ B0)
        linarith)
      have hden0 : 0 < ((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2 :=
        mul_pos (by linarith) (pow_pos hlogB0 2)
      have hcomp : ((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2 ≤ (B1:ℝ) * Real.log (B1:ℝ)^2 := by
        have h1 : ((B0:ℝ)-1) ≤ (B1:ℝ) := by linarith
        have h2 : Real.log ((B0:ℝ)-1) ≤ Real.log (B1:ℝ) := by
          apply Real.log_le_log (by linarith); linarith
        have h3 : Real.log ((B0:ℝ)-1)^2 ≤ Real.log (B1:ℝ)^2 :=
          pow_le_pow_left₀ (le_of_lt hlogB0) h2 2
        exact mul_le_mul h1 h3 (by positivity) (by linarith)
      have h0 := one_div_le_one_div_of_le hden0 hcomp
      have hpos : (0:ℝ) < 1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := by positivity
      linarith
    have hfin2 : 10 * (1/((B1:ℝ) * Real.log (B1:ℝ)^2)) ≤
        500000 * (1 + Real.log Z) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) := by
      have hlogB0' : 0 < Real.log ((B0:ℝ)-1) := Real.log_pos (by
        have : (4:ℝ) ≤ (B0:ℝ) := by exact_mod_cast (by omega : 4 ≤ B0)
        linarith)
      have hden0 : 0 < ((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2 :=
        mul_pos (by linarith) (pow_pos hlogB0' 2)
      have hlogle1 : (1:ℝ) ≤ Real.log ((B0:ℝ)-1) := by
        have h : Real.log 3 ≤ Real.log ((B0:ℝ)-1) := by
          apply Real.log_le_log (by norm_num)
          have : (4:ℝ) ≤ (B0:ℝ) := by exact_mod_cast (by omega : 4 ≤ B0)
          linarith
        have h3 : (1:ℝ) ≤ Real.log 3 := by
          rw [Real.le_log_iff_exp_le (by norm_num)]
          linarith [Real.exp_one_lt_d9]
        linarith
      have hlogZ0 : 0 ≤ Real.log Z := le_of_lt hLZ
      rw [le_div_iff₀ hden0]
      have h10 := mul_le_mul_of_nonneg_left hB1le' (by norm_num : (0:ℝ) ≤ 10)
      have h20 : (10:ℝ) * (2 * (1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2))) *
          (((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) = 20 := by
        have hB0m1 : ((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2 ≠ 0 := by
          have h1 : (0:ℝ) < (B0:ℝ) - 1 := by linarith
          have h2 : 0 < Real.log ((B0:ℝ)-1) := Real.log_pos (by linarith)
          exact ne_of_gt (mul_pos h1 (pow_pos h2 2))
        have hB0nz : (B0:ℝ) - 1 ≠ 0 := by linarith
        field_simp [hB0m1, hB0nz]
        ring
      calc 10 * (1/((B1:ℝ) * Real.log (B1:ℝ)^2)) * (((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)
          ≤ (10 * (2 * (1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)))) *
              (((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) :=
            mul_le_mul_of_nonneg_right h10 hden0.le
        _ = 20 := h20
        _ ≤ 500000 * (1 + Real.log Z) := by nlinarith [hlogZ0]
    exact htri.trans hfin2
  -- the final assembly
  have hassemble : |(∑ n ∈ Finset.Ioc B0 B1,
        (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) (n:ℝ)) -
      (1/Real.log Z) * (∫ β in (1/10:ℝ)..(1/2:ℝ),
        (if lowerTwoDiscarded ε α β then ω ((s - α - β)/β)/(α*β^2) else 0))| ≤
      1000000 * (1 + Real.log Z) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) := by
    rw [hsub]
    have h1 := abs_sub_le ((∑ n ∈ Finset.Ioc B0 B1,
        (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) (n:ℝ)))
      (∫ t in (B0:ℝ)..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t)
      (∫ t in u..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t)
    have h2 : |(∫ t in (B0:ℝ)..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) -
        (∫ t in u..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t)| =
        |(∫ t in u..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) -
        (∫ t in (B0:ℝ)..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t)| :=
      abs_sub_comm _ _
    rw [h2] at h1
    have hdbl : 500000 * (1 + Real.log Z) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2)
        + 500000 * (1 + Real.log Z) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2)
        = 1000000 * (1 + Real.log Z) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) := by
        have hB0m1 : ((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2 ≠ 0 := by
          have h1 : (0:ℝ) < (B0:ℝ) - 1 := by linarith
          have h2 : 0 < Real.log ((B0:ℝ)-1) := Real.log_pos (by linarith)
          exact ne_of_gt (mul_pos h1 (pow_pos h2 2))
        have hB0nz : (B0:ℝ) - 1 ≠ 0 := by linarith
        field_simp [hB0m1, hB0nz]
        ring
    linarith [h1, hcell0, hsliver, hdbl]
  -- rewrite the range and the constant
  rw [hB0, hB1, hu]
  exact hassemble


/-! ### NEW: the tail of the sum vanishes, and the leaf -/

/-- The summand of the second passage vanishes outside `(Z^(1/10), Z^(1/2)]`. -/
private theorem second_passage_summand_zero {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    {ε x s : ℝ} (hZ1 : 1 < scaleZ ε x) (hε8 : ε ≤ 1/10^8)
    {α : ℝ} (hα1 : 1/10 ≤ α) (hα2 : α ≤ 1/2) {b : ℕ}
    (hb : expo ε x b ≤ 1/10 ∨ 1/2 < expo ε x b) :
    (1/((b:ℝ) * Real.log (b:ℝ)^2)) *
      (if lowerTwoDiscarded ε α (expo ε x b) then
        ω ((s - α - expo ε x b) / expo ε x b) / α else 0) = 0 := by
  rw [expo] at hb ⊢
  have hzero : (if lowerTwoDiscarded ε α (Real.log (b:ℝ)/Real.log (scaleZ ε x)) then
      ω ((s - α - Real.log (b:ℝ)/Real.log (scaleZ ε x))/(Real.log (b:ℝ)/Real.log (scaleZ ε x)))/α
      else 0) = 0 := by
    rw [if_neg]
    intro hLT
    obtain ⟨hc, hba, ha, -⟩ := hLT
    rcases hb with hb | hb
    · have hcut : (1/10:ℝ) < (1+7*(2*(1/16-1/10^5)))/15 - 1/10^8 := by norm_num
      have hcut' : (1/10:ℝ) < (1+7*(2*(1/16-1/10^5)))/15 - ε := by linarith
      linarith
    · linarith
  rw [hzero, mul_zero]

/-- A negative power of `x` is at most a negative power of `log x`, times a constant. -/
private theorem rpow_neg_le_log_rpow {A c x : ℝ} (hA : 0 < A) (hc : 0 < c) (hx : 1 < x) :
    x ^ (-c) ≤ (A/c)^A * Real.log x ^ (-A) := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hr : 0 < c/A := div_pos hc hA
  have hAc : 0 < A/c := div_pos hA hc
  have h1 : Real.log x ≤ x^(c/A)/(c/A) := log_le_rpow_div hx0 hr
  have h2 : Real.log x ^ A ≤ (x^(c/A)/(c/A))^A := Real.rpow_le_rpow hlog.le h1 hA.le
  have h3 : (x^(c/A)/(c/A))^A = x^c / (c/A)^A := by
    rw [Real.div_rpow (le_of_lt (Real.rpow_pos_of_pos hx0 _)) hr.le]
    congr 1
    rw [← Real.rpow_mul (le_of_lt hx0)]
    have e : c / A * A = c := by field_simp
    rw [e]
  have hmul : (A/c)^A * (c/A)^A = 1 := by
    have hm : (A/c) * (c/A) = 1 := by field_simp
    calc (A/c)^A * (c/A)^A = ((A/c) * (c/A))^A := (Real.mul_rpow hAc.le hr.le).symm
      _ = 1 := by rw [hm, Real.one_rpow]
  have h4 : ((c/A)^A)⁻¹ = (A/c)^A := inv_eq_of_mul_eq_one_left hmul
  have h5 : (x^(c/A)/(c/A))^A = x^c * (A/c)^A := by
    rw [h3, div_eq_mul_inv, h4]
  rw [h5] at h2
  rw [Real.rpow_neg (le_of_lt hx0), Real.rpow_neg hlog.le, inv_eq_one_div, inv_eq_one_div]
  have eR : (A/c)^A * (1 / Real.log x ^ A) = (A/c)^A / Real.log x ^ A := mul_one_div _ _
  rw [eR, div_le_div_iff₀ (Real.rpow_pos_of_pos hx0 c) (Real.rpow_pos_of_pos hlog A)]
  linarith [h2]


set_option maxHeartbeats 8000000 in
/-- P0069 page 51, display 5.17: the leaf's statement, from `second_passage_pointwise`. -/
theorem leaf_two_pair_riemann_second_new (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          (∫ α in (1/10:ℝ)..(1/2:ℝ),
            if lowerTwoDiscarded ε α (expo ε x b) then
              ω ((Real.log m / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
            else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) -
        lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x)| ≤ C * Real.log x ^ (-A) := by
  intro A hA
  refine ⟨max (max (Real.exp ((2:ℝ)^(A+1))) ((2:ℝ)^40))
      (10^7 * (400*(A+1)/11)^(A+1)), fun x hx m hm1 hm2 => ?_⟩
  have hx40 : (2:ℝ)^40 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hxexp : Real.exp ((2:ℝ)^(A+1)) ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxC : (10^7 : ℝ) * (400*(A+1)/11)^(A+1) ≤ x := (le_max_right _ _).trans hx
  have hx1 : (1:ℝ) ≤ x := le_trans (by norm_num) hx40
  have hx0 : (0:ℝ) < x := by linarith
  obtain ⟨hY49, -, -, -, hl, hlX1, hlX2⟩ :=
    two_pair_scale_facts hε hε8 hA hx40 hxexp (by nlinarith [hx40] : (0:ℝ) ^ 2 ≤ x)
  have hY4 : (4:ℝ) ≤ x ^ (11 / 20 + ε) := le_trans (by norm_num) hY49
  have hY0 : (0:ℝ) < x ^ (11 / 20 + ε) := by linarith
  have hZval : scaleZ ε x = 4 * x ^ (11 / 20 + ε) := rfl
  have hZ4 : (4:ℝ) ≤ scaleZ ε x := by rw [hZval]; linarith
  have hZbig : (2:ℝ)^20 ≤ scaleZ ε x := by
    rw [hZval]; nlinarith [hY49]
  have hZ1 : 1 < scaleZ ε x := by linarith
  have hZ0 : (0:ℝ) < scaleZ ε x := by linarith
  have hLZ : 0 < Real.log (scaleZ ε x) := Real.log_pos hZ1
  have hmR : (0:ℝ) < (m:ℝ) := by
    have h : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) hm1
    exact_mod_cast h
  have hmGt : x ^ (11 / 20 + ε) < (m:ℝ) := by
    have h3 : x ^ (11 / 20 + ε) < (⌊x ^ (11 / 20 + ε)⌋₊ : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (x ^ (11 / 20 + ε))
      exact_mod_cast this
    have h4 : (⌊x ^ (11 / 20 + ε)⌋₊ : ℝ) + 1 ≤ (m:ℝ) := by
      have h5 : ⌊x ^ (11 / 20 + ε)⌋₊ + 1 ≤ m := hm1
      exact_mod_cast h5
    linarith
  have hmLe : (m:ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by
    have h2 : (m:ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by exact_mod_cast hm2
    have h3 : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
      Nat.floor_le (by positivity)
    linarith
  -- the exponent `s = log m / log Z`
  have hs0 : (1/2:ℝ) ≤ Real.log (m:ℝ) / Real.log (scaleZ ε x) := by
    rw [le_div_iff₀ hLZ]
    have h1 : Real.log (x ^ (11 / 20 + ε)) ≤ Real.log (m:ℝ) :=
      Real.log_le_log hY0 (le_of_lt hmGt)
    have h2 : Real.log (scaleZ ε x) = Real.log 4 + Real.log (x ^ (11 / 20 + ε)) := by
      rw [hZval, Real.log_mul (by norm_num) (ne_of_gt hY0)]
    have h4 : Real.log 4 ≤ Real.log (x ^ (11 / 20 + ε)) :=
      Real.log_le_log (by norm_num) hY4
    rw [h2]
    linarith
  have hs1 : Real.log (m:ℝ) / Real.log (scaleZ ε x) ≤ 1 := by
    rw [div_le_iff₀ hLZ]
    have h1 : Real.log (m:ℝ) ≤ Real.log (2 * x ^ (11 / 20 + ε)) :=
      Real.log_le_log (by linarith) hmLe
    have h2 : Real.log (2 * x ^ (11 / 20 + ε)) ≤ Real.log (scaleZ ε x) := by
      apply Real.log_le_log (by linarith)
      rw [hZval]; linarith
    linarith
  -- the inner `α`-integrals are integrable
  have hαInt : ∀ b : ℕ, IntervalIntegrable
      (fun α : ℝ => if lowerTwoDiscarded ε α (expo ε x b) then
        ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
        else 0) volume (1/10) (1/2) := by
    intro b
    have hmeas : Measurable (fun α : ℝ => if lowerTwoDiscarded ε α (expo ε x b) then
        ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
        else 0) := by
      have hωm : Measurable ω := measurable_buchstab_new hω hz
      have hs1' : MeasurableSet {α : ℝ | lowerTwoDiscarded ε α (expo ε x b)} := by
        unfold lowerTwoDiscarded upperPairRegion
        measurability
      have hf : Measurable (fun α : ℝ =>
          ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α) := by
        measurability
      exact Measurable.ite hs1' hf measurable_const
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (1/10:ℝ) ≤ 1/2)]
    refine MeasureTheory.Integrable.of_bound hmeas.aestronglyMeasurable.restrict 10 ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with a ha
    have ha1 : (1/10:ℝ) ≤ a := le_of_lt ha.1
    rw [Real.norm_eq_abs]
    exact phi_abs_le hω hz (ε := ε) (Z := scaleZ ε x) (s := Real.log (m:ℝ) / Real.log (scaleZ ε x))
      (α := a) (β := expo ε x b) ha1
  -- the sum over `b` and the `α`-integral commute
  have hexch : (∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        (∫ α in (1/10:ℝ)..(1/2:ℝ),
          if lowerTwoDiscarded ε α (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
          else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) =
      ∫ α in (1/10:ℝ)..(1/2:ℝ), ∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if lowerTwoDiscarded ε α (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
          else 0) := by
    have hpt : ∀ b : ℕ, (∫ α in (1/10:ℝ)..(1/2:ℝ),
          (if lowerTwoDiscarded ε α (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
          else 0)) / ((b : ℝ) * Real.log (b : ℝ) ^ 2) =
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) * (∫ α in (1/10:ℝ)..(1/2:ℝ),
          (if lowerTwoDiscarded ε α (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
          else 0)) := fun b => by ring
    simp_rw [hpt, ← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_finset_sum (fun b _ => (hαInt b).const_mul _)]
  -- the truncation of the `b`-sum to `(B0, B1]`
  set B0 : ℕ := ⌊(scaleZ ε x)^(1/10:ℝ)⌋₊ with hB0
  set B1 : ℕ := ⌊(scaleZ ε x)^(1/2:ℝ)⌋₊ with hB1
  have hZpow20 : (2:ℝ) ≤ (scaleZ ε x)^(1/20:ℝ) := by
    have h1 : ((2:ℝ)^20)^(1/20:ℝ) ≤ (scaleZ ε x)^(1/20:ℝ) :=
      Real.rpow_le_rpow (by positivity) hZbig (by norm_num)
    have h2 : ((2:ℝ)^20)^(1/20:ℝ) = 2 := by
      rw [← Real.rpow_natCast (2:ℝ) 20, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    linarith
  have hpow4 : (4:ℝ) ≤ (scaleZ ε x)^(1/10:ℝ) := by
    have h1 : ((2:ℝ)^20)^(1/10:ℝ) ≤ (scaleZ ε x)^(1/10:ℝ) :=
      Real.rpow_le_rpow (by positivity) hZbig (by norm_num)
    have h2 : ((2:ℝ)^20)^(1/10:ℝ) = 4 := by
      rw [← Real.rpow_natCast (2:ℝ) 20, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    linarith
  have hB0ge : 4 ≤ B0 := by
    rw [hB0]; exact Nat.le_floor (by push_cast; linarith)
  have hB0R4 : (4:ℝ) ≤ (B0:ℝ) := by exact_mod_cast hB0ge
  have hB0le : ((B0:ℝ)) ≤ (scaleZ ε x)^(1/10:ℝ) := Nat.floor_le (by positivity)
  have hB1le : ((B1:ℝ)) ≤ (scaleZ ε x)^(1/2:ℝ) := Nat.floor_le (by positivity)
  have hB0B1 : B0 ≤ B1 := by
    have h1 : (B0:ℝ) ≤ (scaleZ ε x)^(1/10:ℝ) := hB0le
    have h2 : (scaleZ ε x)^(1/10:ℝ) ≤ (scaleZ ε x)^(1/2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hZ1.le (by norm_num)
    rw [hB1]
    exact Nat.le_floor (le_trans h1 h2)
  have hB1N : B1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ := by
    apply Nat.le_floor
    push_cast
    have hB1z : (B1:ℝ) ≤ (scaleZ ε x)^(1/2:ℝ) := hB1le
    have h4 : (4:ℝ)^(1/2:ℝ) = 2 := by
      rw [← Real.sqrt_eq_rpow, show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hZval, Real.mul_rpow (by norm_num) (le_of_lt hY0), h4] at hB1z
    have hYh : (x ^ (11/20 + ε))^(1/2:ℝ) ≤ x ^ (11/20 + ε) := by
      have h1 : (x ^ (11/20 + ε))^(1/2:ℝ) ≤ (x ^ (11/20 + ε))^(1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      rwa [Real.rpow_one] at h1
    linarith
  -- each summand outside `(B0, B1]` vanishes
  have htrunc : ∀ a : ℝ, 1/10 ≤ a → a ≤ 1/2 →
      (∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if lowerTwoDiscarded ε a (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
          else 0)) =
      ∑ b ∈ Finset.Ioc B0 B1,
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if lowerTwoDiscarded ε a (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
          else 0) := by
    intro a ha1 ha2
    refine (Finset.sum_subset ?_ ?_).symm
    · intro b hb
      obtain ⟨hb1, hb2⟩ := Finset.mem_Ioc.mp hb
      exact Finset.mem_Icc.mpr ⟨by omega, le_trans hb2 hB1N⟩
    · intro b hb hnb
      simp only [Finset.mem_Icc] at hb
      simp only [Finset.mem_Ioc, not_and, not_lt] at hnb
      have hb1 : 1 ≤ b := hb.1
      have hbR1 : (1:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb1
      have hlogb : 0 ≤ Real.log (b:ℝ) := Real.log_nonneg hbR1
      have hcase : b ≤ B0 ∨ B1 < b := by
        by_contra hc
        push_neg at hc
        exact hnb hc.1 hc.2
      rcases hcase with hble | hbgt
      · have hβ : Real.log (b:ℝ) / Real.log (scaleZ ε x) ≤ 1/10 := by
          rw [div_le_iff₀ hLZ]
          have h1 : Real.log (b:ℝ) ≤ Real.log (B0:ℝ) := by
            rcases Nat.eq_zero_or_pos b with h0 | hpos
            · omega
            · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hble)
          have h2 : Real.log (B0:ℝ) ≤ Real.log ((scaleZ ε x)^(1/10:ℝ)) :=
            Real.log_le_log (by linarith) hB0le
          rw [Real.log_rpow hZ0] at h2
          linarith
        have := second_passage_summand_zero (ω := ω) hω
          (x := x) (s := Real.log (m:ℝ) / Real.log (scaleZ ε x)) (ε := ε) hZ1 hε8
          (α := a) ha1 ha2 (b := b) (Or.inl hβ)
        exact this
      · have hβ : 1/2 < Real.log (b:ℝ) / Real.log (scaleZ ε x) := by
          rw [lt_div_iff₀ hLZ]
          have h1 : Real.log ((scaleZ ε x)^(1/2:ℝ)) < Real.log (b:ℝ) := by
            apply Real.log_lt_log (Real.rpow_pos_of_pos hZ0 _)
            have h3 : (B1:ℝ) + 1 ≤ (b:ℝ) := by
              have : B1 + 1 ≤ b := by omega
              exact_mod_cast this
            have hZlt : (scaleZ ε x)^(1/2:ℝ) < (B1:ℝ) + 1 := by
              rw [hB1]
              exact Nat.lt_floor_add_one _
            linarith
          rw [Real.log_rpow hZ0] at h1
          linarith
        have := second_passage_summand_zero (ω := ω) hω
          (x := x) (s := Real.log (m:ℝ) / Real.log (scaleZ ε x)) (ε := ε) hZ1 hε8
          (α := a) ha1 ha2 (b := b) (Or.inr hβ)
        exact this
  -- integrability of the two functions of `α`
  have hGbound : ∀ a : ℝ, 1/10 ≤ a → |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if lowerTwoDiscarded ε a (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
          else 0))| ≤
      10 * (∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, 1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) := by
    intro a ha
    have hstep : ∀ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        |(1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if lowerTwoDiscarded ε a (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
          else 0)| ≤ 10 * (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) := by
      intro b hb
      have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      have hlogb : 0 ≤ Real.log (b:ℝ) := Real.log_nonneg (by exact_mod_cast hb1)
      have hw : 0 ≤ 1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2) := by
        rcases eq_or_lt_of_le hb1 with h | h
        · simp [← h]
        · have h1 : (1:ℝ) < (b:ℝ) := by exact_mod_cast h
          have h2 : 0 < Real.log (b:ℝ) := Real.log_pos h1
          positivity
      have hone : |(if lowerTwoDiscarded ε a (expo ε x b) then
          ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
          else 0)| ≤ 10 :=
        phi_abs_le hω hz (ε := ε) (Z := scaleZ ε x)
          (s := Real.log (m:ℝ) / Real.log (scaleZ ε x)) (α := a) (β := expo ε x b) ha
      calc |(1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
            (if lowerTwoDiscarded ε a (expo ε x b) then
              ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
            else 0)|
          = (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
            |(if lowerTwoDiscarded ε a (expo ε x b) then
              ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
            else 0)| := by rw [abs_mul, abs_of_nonneg hw]
        _ ≤ (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) * 10 := mul_le_mul_of_nonneg_left hone hw
        _ = 10 * (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) := by ring
    calc |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
            (if lowerTwoDiscarded ε a (expo ε x b) then
              ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
            else 0))|
        ≤ ∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          |(1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
            (if lowerTwoDiscarded ε a (expo ε x b) then
              ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
            else 0)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, 10 * (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) :=
          Finset.sum_le_sum hstep
      _ = 10 * (∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, 1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) := by
          rw [Finset.mul_sum]
  have hGmeas : Measurable (fun a : ℝ => ∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if lowerTwoDiscarded ε a (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
          else 0)) := by
    have hωm : Measurable ω := measurable_buchstab_new hω hz
    apply Finset.measurable_sum
    intro b hb
    apply Measurable.mul measurable_const
    have hs1' : MeasurableSet {α : ℝ | lowerTwoDiscarded ε α (expo ε x b)} := by
      unfold lowerTwoDiscarded upperPairRegion
      measurability
    have hf : Measurable (fun α : ℝ =>
        ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α) := by
      measurability
    exact Measurable.ite hs1' hf measurable_const
  have hGint : IntervalIntegrable (fun a : ℝ => ∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if lowerTwoDiscarded ε a (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
          else 0)) volume (1/10) (1/2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (1/10:ℝ) ≤ 1/2)]
    refine MeasureTheory.Integrable.of_bound hGmeas.aestronglyMeasurable.restrict
      (10 * (∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, 1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2))) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with aa haa
    rw [Real.norm_eq_abs]
    exact hGbound aa (le_of_lt haa.1)
  have hdens : lowerTwoDensityAt ω ε (Real.log (m:ℝ) / Real.log (scaleZ ε x)) / Real.log (scaleZ ε x) =
      ∫ a in (1/10:ℝ)..(1/2:ℝ), (1 / Real.log (scaleZ ε x)) *
        (∫ β in (1/10:ℝ)..(1/2:ℝ),
          (if lowerTwoDiscarded ε a β then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0)) := by
    unfold lowerTwoDensityAt
    rw [div_eq_inv_mul, ← intervalIntegral.integral_const_mul]
    simp only [one_div]
  -- the inner `β`-integral is integrable and bounded by `400`
  have hβb : ∀ a : ℝ, 1/10 ≤ a → |∫ β in (1/10:ℝ)..(1/2:ℝ),
      (if lowerTwoDiscarded ε a β then
        ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0)| ≤ 400 := by
    intro a ha
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (1/10:ℝ)) (b := (1/2:ℝ)) (C := 1000)
      (f := fun β : ℝ => if lowerTwoDiscarded ε a β then
        ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0)
      (by
        intro b hb
        rw [Set.uIoc_of_le (by norm_num : (1/10:ℝ) ≤ 1/2)] at hb
        rw [Real.norm_eq_abs]
        by_cases hD : lowerTwoDiscarded ε a b
        · rw [if_pos hD, abs_div]
          have ha0 : (0:ℝ) < a := by linarith
          have hb0 : (0:ℝ) < b := by linarith [hb.1]
          have hnum : |ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - b) / b)| ≤ 1 := by
            rw [abs_le]
            exact ⟨by linarith [Decomp514a.two_density_buchstab_nonneg hω hz ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - b) / b)],
              LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz _⟩
          have hden : (1/1000:ℝ) ≤ a * b^2 := by nlinarith [ha, hb.1, ha0, hb0]
          rw [abs_of_pos (by positivity : (0:ℝ) < a * b^2)]
          rw [div_le_iff₀ (by positivity : (0:ℝ) < a * b^2)]
          nlinarith [hnum]
        · rw [if_neg hD, abs_zero]; norm_num)
    rw [Real.norm_eq_abs] at hbnd
    refine hbnd.trans ?_
    norm_num
  have hDint : IntervalIntegrable (fun a : ℝ => (1 / Real.log (scaleZ ε x)) *
      (∫ β in (1/10:ℝ)..(1/2:ℝ),
        (if lowerTwoDiscarded ε a β then
          ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0)))
      volume (1/10) (1/2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (1/10:ℝ) ≤ 1/2)]
    refine MeasureTheory.Integrable.of_bound ?_ 400 ?_
    ·
      -- measurability of the inner integral as a function of `α`
      have h2m : Measurable (fun p : ℝ × ℝ =>
            if lowerTwoDiscarded ε p.1 p.2 then
              ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - p.1 - p.2) / p.2) / (p.1 * p.2 ^ 2)
            else 0) := by
        have hωm : Measurable ω := measurable_buchstab_new hω hz
        have hs1' : MeasurableSet {p : ℝ × ℝ | lowerTwoDiscarded ε p.1 p.2} := by
          unfold lowerTwoDiscarded upperPairRegion
          measurability
        have hf : Measurable (fun p : ℝ × ℝ =>
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - p.1 - p.2) / p.2) / (p.1 * p.2 ^ 2)) := by
          measurability
        exact Measurable.ite hs1' hf measurable_const
      have hraw : StronglyMeasurable (fun p : ℝ × ℝ =>
          (Set.Ioc (1/10:ℝ) (1/2)).indicator
            (fun q : ℝ => if lowerTwoDiscarded ε p.1 q then
              ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - p.1 - q) / q) / (p.1 * q ^ 2)
            else 0) p.2) := by
        refine h2m.stronglyMeasurable.indicator ?_
        exact measurableSet_Ioc.preimage measurable_snd
      have hind : StronglyMeasurable (Function.uncurry (fun a q : ℝ =>
          (Set.Ioc (1/10:ℝ) (1/2)).indicator
            (fun q' : ℝ => if lowerTwoDiscarded ε a q' then
              ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - q') / q') / (a * q' ^ 2)
            else 0) q)) := hraw
      have hsm := StronglyMeasurable.integral_prod_right (ν := volume) hind
      have e : (fun a : ℝ => ∫ β in (1/10:ℝ)..(1/2:ℝ),
          (if lowerTwoDiscarded ε a β then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0)) =
          (fun a : ℝ => ∫ β, (Set.Ioc (1/10:ℝ) (1/2)).indicator
            (fun q : ℝ => if lowerTwoDiscarded ε a q then
              ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - q) / q) / (a * q ^ 2)
            else 0) β) := by
        funext a
        rw [intervalIntegral.integral_of_le (by norm_num : (1/10:ℝ) ≤ 1/2),
          ← MeasureTheory.integral_indicator measurableSet_Ioc]
      have hfin : AEStronglyMeasurable (fun a : ℝ => ∫ β in (1/10:ℝ)..(1/2:ℝ),
          (if lowerTwoDiscarded ε a β then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0))
          (volume.restrict (Set.Ioc (1/10:ℝ) (1/2))) := by
        rw [e]
        exact hsm.measurable.aestronglyMeasurable.restrict
      exact hfin.const_mul _
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with a ha
      rw [Real.norm_eq_abs]
      have hlogZ1 : (1:ℝ) ≤ Real.log (scaleZ ε x) := by
        have h : Real.log 4 ≤ Real.log (scaleZ ε x) := Real.log_le_log (by norm_num) hZ4
        have h2 : (1:ℝ) ≤ Real.log 4 := by
          have h4 : (0.5:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
          have h5 : Real.log 4 = 2 * Real.log 2 := by
            rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
            push_cast
            ring
          linarith
        linarith
      calc |(1 / Real.log (scaleZ ε x)) *
            (∫ β in (1/10:ℝ)..(1/2:ℝ),
              (if lowerTwoDiscarded ε a β then
                ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0))|
          = |1 / Real.log (scaleZ ε x)| *
            |∫ β in (1/10:ℝ)..(1/2:ℝ),
              (if lowerTwoDiscarded ε a β then
                ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0)| :=
            abs_mul _ _
        _ ≤ 1 * 400 := by
            apply mul_le_mul
            · rw [abs_of_pos (by positivity : (0:ℝ) < 1 / Real.log (scaleZ ε x))]
              rw [div_le_one (by linarith)]
              exact hlogZ1
            · exact hβb a (le_of_lt ha.1)
            · exact abs_nonneg _
            · norm_num
        _ = 400 := by norm_num
  -- the pointwise comparison
  have hpt : ∀ a : ℝ, 1/10 ≤ a → a ≤ 1/2 →
      |(∑ b ∈ Finset.Ioc B0 B1, (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if lowerTwoDiscarded ε a (Real.log (b : ℝ) / Real.log (scaleZ ε x)) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - Real.log (b : ℝ) / Real.log (scaleZ ε x)) /
              (Real.log (b : ℝ) / Real.log (scaleZ ε x))) / a else 0)) -
        (1 / Real.log (scaleZ ε x)) *
          (∫ β in (1/10:ℝ)..(1/2:ℝ),
            (if lowerTwoDiscarded ε a β then
              ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0))| ≤
        1000000 * (1 + Real.log (scaleZ ε x)) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) := by
    intro a ha1 ha2
    have h := second_passage_pointwise (ω := ω) hω hz (ε := ε) (Z := scaleZ ε x)
      (s := Real.log (m:ℝ) / Real.log (scaleZ ε x)) hε8 hZ1 hZbig hs0 hs1 ha1 ha2
    rw [← hB0, ← hB1] at h
    simpa [expo] using h
  -- the integral of the difference
  rw [hexch, hdens]
  rw [← intervalIntegral.integral_sub hGint hDint]
  refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num : (1/10:ℝ) ≤ 1/2)).trans ?_
  have hpt' : ∀ a ∈ Set.Icc (1/10:ℝ) (1/2),
      |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if lowerTwoDiscarded ε a (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
          else 0)) -
        (1 / Real.log (scaleZ ε x)) *
        (∫ β in (1/10:ℝ)..(1/2:ℝ),
          (if lowerTwoDiscarded ε a β then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0))| ≤
        1000000 * (1 + Real.log (scaleZ ε x)) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) := by
    intro a ha
    rw [htrunc a ha.1 ha.2]
    exact hpt a ha.1 ha.2
  refine (intervalIntegral.integral_mono_on (by norm_num : (1/10:ℝ) ≤ 1/2) (hGint.sub hDint).abs
    intervalIntegrable_const hpt').trans ?_
  rw [intervalIntegral.integral_const, smul_eq_mul]
  -- the final numerical comparison
  have hx27 : (27:ℝ) ≤ Real.log x := by
    have h2 : Real.log ((2:ℝ)^40) ≤ Real.log x := Real.log_le_log (by norm_num) hx40
    have h3 : Real.log ((2:ℝ)^40) = 40 * Real.log 2 := by
      rw [Real.log_pow]; push_cast; ring
    have h4 : (0.693:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    rw [h3] at h2
    linarith
  have hlogZ_le : (1 + Real.log (scaleZ ε x)) ≤ 4 * Real.log x := by
    have h1 : Real.log (scaleZ ε x) = Real.log 4 + Real.log (x ^ (11 / 20 + ε)) := by
      rw [hZval, Real.log_mul (by norm_num) (ne_of_gt hY0)]
    have h5 : Real.log (x ^ (11 / 20 + ε)) = (11/20 + ε) * Real.log x := Real.log_rpow hx0 _
    have h6 : (11/20 + ε) * Real.log x ≤ Real.log x := by
      have h7 : (11/20 + ε) ≤ 1 := by linarith
      nlinarith [Real.log_nonneg hx1]
    have h8 : Real.log 4 ≤ 4 := by
      have h9 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
      linarith
    have h10 : (1:ℝ) ≤ Real.log x := by linarith
    linarith
  -- `log^2 (B0-1) ≥ 1/4` and `(B0-1) ≥ Z^(1/20)`
  have hB0m1 : (scaleZ ε x)^(1/20:ℝ) ≤ (B0:ℝ) - 1 := by
    have h2 := hZpow20
    have h3 : (scaleZ ε x)^(1/10:ℝ) = (scaleZ ε x)^(1/20:ℝ) * (scaleZ ε x)^(1/20:ℝ) := by
      rw [← Real.rpow_add hZ0]; norm_num
    have h4 : ((B0:ℝ)) ≥ (scaleZ ε x)^(1/10:ℝ) - 1 := by
      have h5 := Nat.floor_le (show (0:ℝ) ≤ (scaleZ ε x)^(1/10:ℝ) by positivity)
      push_cast at h5
      have h6 := Nat.sub_one_lt_floor ((scaleZ ε x)^(1/10:ℝ))
      linarith
    rw [h3] at h4
    nlinarith [h2, h4]
  have hlogB0 : (1/2:ℝ) ≤ Real.log ((B0:ℝ) - 1) := by
    have h2 : (2:ℝ) ≤ (B0:ℝ) - 1 := by linarith [hB0R4]
    have h3 : Real.log 2 ≤ Real.log ((B0:ℝ) - 1) := Real.log_le_log (by norm_num) h2
    have h4 : (0.5:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    linarith
  have hden : (scaleZ ε x)^(1/20:ℝ) / 4 ≤ ((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2 := by
    have h2 : (1/4:ℝ) ≤ Real.log ((B0:ℝ) - 1)^2 := by nlinarith
    have h3 : (0:ℝ) < (scaleZ ε x)^(1/20:ℝ) := Real.rpow_pos_of_pos hZ0 _
    nlinarith [hB0m1, h2, h3]
  have hERR : 1000000 * (1 + Real.log (scaleZ ε x)) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) ≤
      4000000 * (1 + Real.log (scaleZ ε x)) * (scaleZ ε x)^(-(1/20:ℝ)) := by
    have hpos : (0:ℝ) < ((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2 := by
      have h1 : (0:ℝ) < (B0:ℝ) - 1 := by linarith
      have h2 : (0:ℝ) < Real.log ((B0:ℝ) - 1) := by linarith
      positivity
    have hz0 : (0:ℝ) < (scaleZ ε x)^(1/20:ℝ) := Real.rpow_pos_of_pos hZ0 _
    have hstep : 1000000 * (1 + Real.log (scaleZ ε x)) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) ≤
        1000000 * (1 + Real.log (scaleZ ε x)) / ((scaleZ ε x)^(1/20:ℝ) / 4) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    have heq : 1000000 * (1 + Real.log (scaleZ ε x)) / ((scaleZ ε x)^(1/20:ℝ) / 4) =
        4000000 * (1 + Real.log (scaleZ ε x)) * ((scaleZ ε x)^(1/20:ℝ))⁻¹ := by
      field_simp
      norm_num
    rw [Real.rpow_neg (le_of_lt hZ0)]
    linarith [hstep, heq.le, heq.ge]
  have hZpow_le : (scaleZ ε x)^(-(1/20:ℝ)) ≤ x ^ (-(11/400:ℝ)) := by
    have h1 : x ^ (11/400:ℝ) ≤ (scaleZ ε x)^(1/20:ℝ) := by
      rw [hZval]
      have h2 : (4 * x ^ (11/20 + ε))^(1/20:ℝ) =
          4^(1/20:ℝ) * (x ^ (11/20 + ε))^(1/20:ℝ) := Real.mul_rpow (by norm_num) (le_of_lt hY0)
      rw [h2, ← Real.rpow_mul (le_of_lt hx0)]
      have h3 : x ^ (11/400:ℝ) ≤ x ^ ((11/20 + ε) * (1/20)) := by
        apply Real.rpow_le_rpow_of_exponent_le hx1
        nlinarith
      have h4 : (1:ℝ) ≤ 4^(1/20:ℝ) := by
        calc (1:ℝ) = 1^(1/20:ℝ) := by rw [Real.one_rpow]
          _ ≤ 4^(1/20:ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      have h5 : (0:ℝ) < x ^ ((11/20 + ε) * (1/20)) := Real.rpow_pos_of_pos hx0 _
      nlinarith [h3, h4, h5, Real.rpow_pos_of_pos hx0 (11/400:ℝ)]
    rw [Real.rpow_neg (le_of_lt hZ0), Real.rpow_neg (le_of_lt hx0)]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hx0 _)).mpr h1
  -- assemble the constant
  have hA1 : (0:ℝ) < A + 1 := by linarith
  have hcpos : (0:ℝ) < 11/400 := by norm_num
  have hlogA : x ^ (-(11/400:ℝ)) ≤ ((A+1)/(11/400))^(A+1) * Real.log x ^ (-(A+1)) :=
    rpow_neg_le_log_rpow hA1 hcpos (by linarith)
  have hlognonneg : (0:ℝ) ≤ Real.log x := Real.log_nonneg hx1
  have hstep1 : (2/5:ℝ) * (1000000 * (1 + Real.log (scaleZ ε x)) /
      (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2)) ≤
      (2/5:ℝ) * (4000000 * (1 + Real.log (scaleZ ε x)) * (scaleZ ε x)^(-(1/20:ℝ))) :=
    mul_le_mul_of_nonneg_left hERR (by norm_num)
  have hstep2 : (2/5:ℝ) * (4000000 * (1 + Real.log (scaleZ ε x)) * (scaleZ ε x)^(-(1/20:ℝ))) ≤
      (2/5:ℝ) * (4000000 * (4 * Real.log x) * x ^ (-(11/400:ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2/5)
    have h3 : (0:ℝ) ≤ (1 + Real.log (scaleZ ε x)) := by
      have h5 : 0 ≤ Real.log (scaleZ ε x) := Real.log_nonneg hZ1.le
      linarith
    have hz : (0:ℝ) ≤ (scaleZ ε x)^(-(1/20:ℝ)) := Real.rpow_nonneg hZ0.le _
    calc 4000000 * (1 + Real.log (scaleZ ε x)) * (scaleZ ε x)^(-(1/20:ℝ))
        = 4000000 * ((1 + Real.log (scaleZ ε x)) * (scaleZ ε x)^(-(1/20:ℝ))) := by ring
      _ ≤ 4000000 * ((4 * Real.log x) * (scaleZ ε x)^(-(1/20:ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hlogZ_le hz
      _ ≤ 4000000 * ((4 * Real.log x) * x ^ (-(11/400:ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hZpow_le (by linarith)
      _ = 4000000 * (4 * Real.log x) * x ^ (-(11/400:ℝ)) := by ring
  have hstep3 : (2/5:ℝ) * (4000000 * (4 * Real.log x) * x ^ (-(11/400:ℝ))) ≤
      (2/5:ℝ) * (4000000 * (4 * ((A+1)/(11/400))^(A+1) * Real.log x ^ (-(A+1))) * Real.log x) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2/5)
    have h1 : Real.log x * x ^ (-(11/400:ℝ)) ≤
        Real.log x * (((A+1)/(11/400))^(A+1) * Real.log x ^ (-(A+1:ℝ))) :=
      mul_le_mul_of_nonneg_left hlogA hlognonneg
    calc 4000000 * (4 * Real.log x) * x ^ (-(11/400:ℝ))
        = 16000000 * (Real.log x * x ^ (-(11/400:ℝ))) := by ring
      _ ≤ 16000000 * (Real.log x * (((A+1)/(11/400))^(A+1) * Real.log x ^ (-(A+1:ℝ)))) := by
          apply mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 4000000 * (4 * ((A+1)/(11/400))^(A+1) * Real.log x ^ (-(A+1:ℝ))) * Real.log x := by ring
  have hstep4 : (2/5:ℝ) * (4000000 * (4 * ((A+1)/(11/400))^(A+1) * Real.log x ^ (-(A+1))) * Real.log x) =
      (2/5:ℝ) * (4000000 * (4 * ((A+1)/(11/400))^(A+1))) * Real.log x ^ (-A) := by
    have hlogpos : (0:ℝ) < Real.log x := by linarith
    have e : Real.log x ^ (-A:ℝ) = Real.log x ^ (-(A+1:ℝ)) * Real.log x := by
      have h1 : (-A:ℝ) = -(A+1) + 1 := by ring
      rw [h1, Real.rpow_add hlogpos, Real.rpow_one]
    rw [e]
    ring
  have hconst : (2/5:ℝ) * (4000000 * (4 * ((A+1)/(11/400))^(A+1))) ≤
      10^7 * (400*(A+1)/11)^(A+1) := by
    have he : ((A+1)/(11/400)) = (400*(A+1)/11) := by field_simp
    rw [he]
    have hpos : (0:ℝ) < (400*(A+1)/11)^(A+1) := by positivity
    nlinarith [hpos]
  have hlognn : (0:ℝ) ≤ Real.log x ^ (-A) := Real.rpow_nonneg hlognonneg _
  have hfinal : (2/5:ℝ) * (1000000 * (1 + Real.log (scaleZ ε x)) /
      (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2)) ≤
      (10^7 * (400*(A+1)/11)^(A+1)) * Real.log x ^ (-A) := by
    calc (2/5:ℝ) * (1000000 * (1 + Real.log (scaleZ ε x)) /
          (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2))
        ≤ (2/5:ℝ) * (4000000 * (1 + Real.log (scaleZ ε x)) * (scaleZ ε x)^(-(1/20:ℝ))) := hstep1
      _ ≤ (2/5:ℝ) * (4000000 * (4 * Real.log x) * x ^ (-(11/400:ℝ))) := hstep2
      _ ≤ (2/5:ℝ) * (4000000 * (4 * ((A+1)/(11/400))^(A+1) * Real.log x ^ (-(A+1))) * Real.log x) := hstep3
      _ = (2/5:ℝ) * (4000000 * (4 * ((A+1)/(11/400))^(A+1))) * Real.log x ^ (-A) := hstep4
      _ ≤ (10^7 * (400*(A+1)/11)^(A+1)) * Real.log x ^ (-A) :=
          mul_le_mul_of_nonneg_right hconst hlognn
  have hfac : (1/2:ℝ) - 1/10 = 2/5 := by norm_num
  have hCle : (10^7 : ℝ) * (400*(A+1)/11)^(A+1) ≤
      max (max (Real.exp ((2:ℝ)^(A+1))) ((2:ℝ)^40)) (10^7 * (400*(A+1)/11)^(A+1)) :=
    le_max_right _ _
  refine (le_trans ?_ (mul_le_mul_of_nonneg_right hCle hlognn))
  rw [hfac]
  exact hfinal

/-- LEAF: P0069 page 51, display 5.17, the E2 sum of display 5.15 at one point `m` of J, the
passage from the sum over the second outer variable to the integral of page 51. The sum over
the integers `b` of `M(log b / log Z) / (b log^2 b)`, where `M(β2)` is the integral over the
first exponent of `ω((s - β1 - β2) / β2) / β1` on the section of E2 at `β2`, is
`(1 / log Z) ∫∫_{E2} ω((s - β1 - β2) / β2) / (β1 β2^2)`: the change of variables `b = Z^β2`
has `db / (b log^2 b) = dβ2 / (β2^2 log Z)`, the function `M` has bounded variation and
vanishes below `β2 = 1 / 10`, so the sum is the integral up to a power saving, and the order
of the two integrals is exchanged by Fubini. No prime number theorem is used. -/
theorem leaf_two_pair_riemann_second (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          (∫ α in (1/10:ℝ)..(1/2:ℝ),
            if lowerTwoDiscarded ε α (expo ε x b) then
              ω ((Real.log m / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
            else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) -
        lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x)| ≤ C * Real.log x ^ (-A) :=
  leaf_two_pair_riemann_second_new ω hω hz hε hε8

/-- P0069 page 51, display 5.17, the E2 sum of display 5.15 at one point `m` of J, the passage
from sums to the integral of page 51. The sum over the integer pairs `b < a` with exponents in
E2 of `ω(log (m / (a b)) / log b) / (a b log a log^2 b)` is
`(1 / log Z) ∫∫_{E2} ω((s - β1 - β2) / β2) / (β1 β2^2)` at `m = Z^s`. No prime number theorem
is used. CONDITIONAL ON `leaf_two_pair_riemann_first` and `leaf_two_pair_riemann_second`. -/
theorem two_pair_riemann (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          ∑ a ∈ Finset.Ioc b ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log (b : ℝ)))) -
        lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x)| ≤ C * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, hC1⟩ := leaf_two_pair_riemann_first ω hω hz hε hε8 A hA
  obtain ⟨C2, hC2⟩ := leaf_two_pair_riemann_second ω hω hz hε hε8 A hA
  refine ⟨max (max C1 C2) (|C1| + |C2| + 1), fun x hx m hm1 hm2 => ?_⟩
  have hx1 : C1 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx2 : C2 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hC : |C1| + |C2| + 1 ≤ max (max C1 C2) (|C1| + |C2| + 1) := le_max_right _ _
  have hxone : (1 : ℝ) ≤ x := by
    have h1 := abs_nonneg C1
    have h2 := abs_nonneg C2
    linarith
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hxone) _
  have a1 := abs_le.mp (hC1 x hx1 m hm1 hm2)
  have a2 := abs_le.mp (hC2 x hx2 m hm1 hm2)
  have k1 := mul_le_mul_of_nonneg_right (le_abs_self C1) hL
  have k2 := mul_le_mul_of_nonneg_right (le_abs_self C2) hL
  have k4 := mul_le_mul_of_nonneg_right hC hL
  have k5 : (|C1| + |C2| + 1) * Real.log x ^ (-A) =
      |C1| * Real.log x ^ (-A) + |C2| * Real.log x ^ (-A) + Real.log x ^ (-A) := by ring
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]

/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number
theorem", the outer primes `p1`, `p2` of the E2 sum of display 5.15 at one point `m` of J. The
sum over the prime pairs with exponents in E2 of `ω(log (m / (p1 p2)) / log p2) / log p2`
weighted by `1 / (p1 p2)` is `(1 / log Z) ∫∫_{E2} ω((s - β1 - β2) / β2) / (β1 β2^2)` at
`m = Z^s`, with every log power saved. CONDITIONAL ON `leaf_two_pair_riemann_first` and
`leaf_two_pair_riemann_second`. -/
theorem two_pair_density_pointwise (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
            i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
              lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
          ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ))) / Real.log (i.2 : ℝ)) /
            Real.log (i.2 : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ))) -
        lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x)| ≤ C * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, hC1⟩ := two_pair_first_prime ω hω hz hε hε8 A hA
  obtain ⟨C2, hC2⟩ := two_pair_second_prime ω hω hz hε hε8 A hA
  obtain ⟨C3, hC3⟩ := two_pair_riemann ω hω hz hε hε8 A hA
  refine ⟨max (max C1 C2) (max C3 (|C1| + |C2| + |C3| + 1)), fun x hx m hm1 hm2 => ?_⟩
  have hx1 : C1 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx2 : C2 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx3 : C3 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hC : |C1| + |C2| + |C3| + 1 ≤ max (max C1 C2) (max C3 (|C1| + |C2| + |C3| + 1)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hxone : (1 : ℝ) ≤ x := by
    have h1 := abs_nonneg C1
    have h2 := abs_nonneg C2
    have h3 := abs_nonneg C3
    linarith
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hxone) _
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
  have k5 : (|C1| + |C2| + |C3| + 1) * Real.log x ^ (-A) =
      |C1| * Real.log x ^ (-A) + |C2| * Real.log x ^ (-A) + |C3| * Real.log x ^ (-A) +
        Real.log x ^ (-A) := by ring
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]

end LeanLab.BHP1997.LowerShortC165
