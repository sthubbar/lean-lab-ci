/-
Split of the statement `dudek_dunn` of `LeanLab.AlmostPrimes.Statements`:
`∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 40 N`.

The single conclusion is cut into five range-restricted leaves, following the way the range of
`N` is handled in the surrounding folder:

* below `2^40 + 1` the degenerate sum `N = 1 + (N - 1)` suffices, because a number of size at
  most `2^40` has at most `40` prime factors counted with multiplicity;
* from `2^40 + 1` up to `4 * 10 ^ 18`, split by the parity of `N`;
* in the window `4 * 10 ^ 18 < N < 10 ^ 200`, the finite verification of the sieve;
* from `10 ^ 200` up, the analytic lower bound for the sieve at `N ^ (1/20)`.

`dudek_dunn_split` is assembled from the five leaves with no `sorry`.

Pass of 2026-11-18 (OMOS lomos 20261118T1929Z): every leaf above `2^40 + 1` only needs the
elementary counting step `Ω a + Ω (N - a) ≤ 40` for one `a`, i.e. a first moment of `Ω`, which
`twoAlmostPrimes_of_inv_pred_sum` reduces to the single reciprocal-prime estimate
`Σ_{p ≤ N} 1/(p-1) ≤ 10` (true value `7.17` at `N = 10^200`).  That estimate is proved below for
all `N ≤ 10^200` by Abel summation on the explicit Chebyshev-type bound
`LeanLab.ChebyshevExplicit.pi_le_110556_refined` (`π(x) ≤ 1.10556 x/log x + 4.42224 x/log²x + …`,
closure sorry-free).  This closes `leaf_even_finite`, `leaf_odd_finite` and `leaf_finite_window`;
`leaf_analytic_large` still needs the lower-bound sieve (`SiftedExists N (N^(1/20))`).
-/
import LeanLab.AlmostPrimes.Statements
import LeanLab.ChebyshevExplicit.PiUpperRefined

namespace LeanLab.AlmostPrimes

open Finset

/-! ### Numeric bounds for `Real.log` -/

private theorem log_two_lo : (0.6931471 : ℝ) ≤ Real.log 2 := by
  linarith [Real.log_two_gt_d9]

private theorem log_two_hi : Real.log 2 ≤ 0.6931472 := by
  linarith [Real.log_two_lt_d9]

private theorem log_ten_eq : Real.log 10 = 3 * Real.log 2 + Real.log 1.25 := by
  have h : (10 : ℝ) = 2 ^ 3 * 1.25 := by norm_num
  rw [h, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast
  ring

private theorem log_125_lo : (0.2 : ℝ) ≤ Real.log 1.25 := by
  have h := Real.one_sub_inv_le_log_of_pos (x := (1.25 : ℝ)) (by norm_num)
  norm_num at h
  linarith

private theorem log_125_hi : Real.log 1.25 ≤ 0.25 := by
  have h := Real.log_le_sub_one_of_pos (x := (1.25 : ℝ)) (by norm_num)
  norm_num at h
  linarith

private theorem log_ten_le : Real.log 10 ≤ 2.33 := by
  rw [log_ten_eq]
  linarith [log_two_hi, log_125_hi]

private theorem log_ten_ge : (2.2794 : ℝ) ≤ Real.log 10 := by
  rw [log_ten_eq]
  linarith [log_two_lo, log_125_lo]

private theorem log_thousand_eq : Real.log 1000 = 3 * Real.log 10 := by
  have h : (1000 : ℝ) = 10 ^ 3 := by norm_num
  rw [h, Real.log_pow]
  push_cast
  ring

private theorem log_thousand_ge : (6.838 : ℝ) ≤ Real.log 1000 := by
  rw [log_thousand_eq]
  linarith [log_ten_ge]

private theorem log_thousand_le : Real.log 1000 ≤ 6.99 := by
  rw [log_thousand_eq]
  linarith [log_ten_le]

private theorem log_999_ge : (6.83 : ℝ) ≤ Real.log 999 := by
  have hmul : Real.log 999 = Real.log 1000 + Real.log ((999 : ℝ) / 1000) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h := Real.one_sub_inv_le_log_of_pos (x := ((999 : ℝ) / 1000)) (by norm_num)
  have hinv : (((999 : ℝ) / 1000))⁻¹ = 1000 / 999 := by norm_num
  rw [hinv] at h
  rw [hmul]
  linarith [log_thousand_ge]

/-- `log M ≤ 466` for `M ≤ 10^200`, from `log 10 ≤ 2.33`. -/
private theorem log_le_466 {M : ℕ} (hM : M ≤ 10 ^ 200) : Real.log M ≤ 466 := by
  rcases Nat.eq_zero_or_pos M with h0 | hpos
  · subst h0
    simp
  · have hle : Real.log M ≤ Real.log ((10 : ℝ) ^ 200) :=
      Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hM)
    have hpow : Real.log ((10 : ℝ) ^ 200) = 200 * Real.log 10 := by
      rw [Real.log_pow]
      push_cast
      ring
    rw [hpow] at hle
    linarith [log_ten_le]

/-- `log log M ≤ 6.24` for `2 ≤ M ≤ 10^200`. -/
private theorem loglog_le {M : ℕ} (h2 : 2 ≤ M) (hM : M ≤ 10 ^ 200) :
    Real.log (Real.log M) ≤ 6.24 := by
  have hlog : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hle : Real.log M ≤ 466 := log_le_466 hM
  have h1 : Real.log (Real.log M) ≤ Real.log 466 := Real.log_le_log hlog hle
  have h512 : Real.log 512 = 9 * Real.log 2 := by
    have hh : (512 : ℝ) = 2 ^ 9 := by norm_num
    rw [hh, Real.log_pow]
    push_cast
    ring
  have h2' : Real.log 466 ≤ Real.log 512 :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [h512] at h2'
  linarith [log_two_hi]

/-- `log log M - log log 999 ≤ 4.23` for `1000 ≤ M ≤ 10^200`: the ratio `log M / log 999` is at
most `68.3`, and `log 68.3 ≤ 6 log 2 + 0.068 ≈ 4.23`. -/
private theorem loglog_gap {M : ℕ} (h1000 : 1000 ≤ M) (hM : M ≤ 10 ^ 200) :
    Real.log (Real.log M) - Real.log (Real.log 999) ≤ 4.23 := by
  have hMpos : (0 : ℝ) < Real.log M :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have h999pos : (0 : ℝ) < Real.log 999 :=
    Real.log_pos (by norm_num)
  have hlogM : Real.log M ≤ 466 := log_le_466 hM
  have hratio : Real.log M / Real.log 999 ≤ 466 / 6.83 := by
    rw [div_le_div_iff₀ h999pos (by norm_num)]
    nlinarith [log_999_ge, hlogM, hMpos, h999pos]
  have hdiv : Real.log (Real.log M) - Real.log (Real.log 999)
      = Real.log (Real.log M / Real.log 999) := by
    rw [Real.log_div hMpos.ne' h999pos.ne']
  have hmono : Real.log (Real.log M / Real.log 999) ≤ Real.log (466 / 6.83) :=
    Real.log_le_log (by positivity) hratio
  have hsplit : Real.log (466 / 6.83) = Real.log (64 * ((466 / 6.83) / 64)) := by
    rw [mul_div_cancel₀]
    norm_num
  have hstep : Real.log (64 * ((466 : ℝ) / 6.83 / 64)) ≤ 6 * Real.log 2 + ((466 : ℝ) / 6.83 / 64 - 1) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have h64 : Real.log 64 = 6 * Real.log 2 := by
      have hh : (64 : ℝ) = 2 ^ 6 := by norm_num
      rw [hh, Real.log_pow]
      push_cast
      ring
    have hsmall : Real.log ((466 : ℝ) / 6.83 / 64) ≤ (466 : ℝ) / 6.83 / 64 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    linarith
  have hnum : 6 * Real.log 2 + ((466 : ℝ) / 6.83 / 64 - 1) ≤ 4.23 := by
    linarith [log_two_hi]
  linarith [hdiv, hmono, hsplit, hstep, hnum]

/-! ### Telescoping steps -/

/-- `1/n ≤ log n - log (n-1)`: a logarithmic increment beats `1/n`. -/
private theorem inv_le_log_sub {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ) / n ≤ Real.log n - Real.log ((n - 1 : ℕ) : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h := Real.one_sub_inv_le_log_of_pos (x := (n : ℝ) / ((n : ℝ) - 1)) (by positivity)
  have hinv : ((n : ℝ) / ((n : ℝ) - 1))⁻¹ = ((n : ℝ) - 1) / n := inv_div _ _
  rw [hinv] at h
  have hlog : Real.log ((n : ℝ) / ((n : ℝ) - 1))
      = Real.log n - Real.log ((n : ℝ) - 1) := Real.log_div hn0.ne' hn1.ne'
  rw [hlog] at h
  have heq : (1 : ℝ) - ((n : ℝ) - 1) / n = 1 / n := by
    field_simp <;> ring
  rw [heq] at h
  rw [hcast]
  linarith [h]

/-- `1/(n log n) ≤ log log n - log log (n-1)`. -/
private theorem step_log {n : ℕ} (hn : 3 ≤ n) :
    (1 : ℝ) / ((n : ℝ) * Real.log n)
      ≤ Real.log (Real.log n) - Real.log (Real.log ((n - 1 : ℕ) : ℝ)) := by
  have hn2 : 2 ≤ n := by omega
  have h3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hu : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hv : 0 < Real.log ((n - 1 : ℕ) : ℝ) := by
    rw [hcast]
    exact Real.log_pos (by linarith)
  have hinc : (1 : ℝ) / n ≤ Real.log n - Real.log ((n - 1 : ℕ) : ℝ) := inv_le_log_sub hn2
  have hratio : 0 < Real.log (n : ℝ) / Real.log ((n - 1 : ℕ) : ℝ) := div_pos hu hv
  have h1 : 1 - Real.log ((n - 1 : ℕ) : ℝ) / Real.log (n : ℝ)
      ≤ Real.log (Real.log (n : ℝ) / Real.log ((n - 1 : ℕ) : ℝ)) := by
    have h := Real.one_sub_inv_le_log_of_pos (x := Real.log (n : ℝ) / Real.log ((n - 1 : ℕ) : ℝ)) hratio
    have hinv : (Real.log (n : ℝ) / Real.log ((n - 1 : ℕ) : ℝ))⁻¹
        = Real.log ((n - 1 : ℕ) : ℝ) / Real.log (n : ℝ) := inv_div _ _
    rwa [hinv] at h
  have h2 : Real.log (Real.log (n : ℝ) / Real.log ((n - 1 : ℕ) : ℝ))
      = Real.log (Real.log n) - Real.log (Real.log ((n - 1 : ℕ) : ℝ)) :=
    Real.log_div hu.ne' hv.ne'
  have h3 : (1 : ℝ) / ((n : ℝ) * Real.log n)
      ≤ 1 - Real.log ((n - 1 : ℕ) : ℝ) / Real.log (n : ℝ) := by
    have heq : (1 : ℝ) / ((n : ℝ) * Real.log n) = ((1 : ℝ) / n) / Real.log (n : ℝ) := by
      field_simp
    rw [heq, div_le_iff₀ hu]
    have hsub : (1 - Real.log ((n - 1 : ℕ) : ℝ) / Real.log (n : ℝ)) * Real.log (n : ℝ)
        = Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) := by
      field_simp
    rw [hsub]
    exact hinc
  rw [h2] at h1
  linarith [h1, h3]

/-- `1/(n log²n) ≤ 1/log (n-1) - 1/log n`. -/
private theorem step_logsq {n : ℕ} (hn : 3 ≤ n) :
    (1 : ℝ) / ((n : ℝ) * Real.log n ^ 2)
      ≤ 1 / Real.log ((n - 1 : ℕ) : ℝ) - 1 / Real.log n := by
  have hn2 : 2 ≤ n := by omega
  have h3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hu : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hv : 0 < Real.log ((n - 1 : ℕ) : ℝ) := by
    rw [hcast]
    exact Real.log_pos (by linarith)
  have hvle : Real.log ((n - 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
    rw [hcast]
    exact Real.log_le_log (by linarith) (by linarith)
  have hinc : (1 : ℝ) / n ≤ Real.log n - Real.log ((n - 1 : ℕ) : ℝ) := inv_le_log_sub hn2
  have hA : (1 : ℝ) / ((n : ℝ) * Real.log n ^ 2) = ((1 : ℝ) / n) / Real.log (n : ℝ) ^ 2 := by
    field_simp
  have hA2 : (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) / Real.log (n : ℝ) ^ 2
      ≤ (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ))
        / (Real.log ((n - 1 : ℕ) : ℝ) * Real.log (n : ℝ)) := by
    have hnn : (0 : ℝ) ≤ Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) := by
      have hp1 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
      linarith [hinc]
    have h2 : Real.log ((n - 1 : ℕ) : ℝ) * Real.log (n : ℝ)
        ≤ Real.log (n : ℝ) ^ 2 := by nlinarith [hvle, hu]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_left h2 hnn
  have hC : (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ))
      / (Real.log ((n - 1 : ℕ) : ℝ) * Real.log (n : ℝ))
      = 1 / Real.log ((n - 1 : ℕ) : ℝ) - 1 / Real.log n := by
    field_simp <;> ring
  rw [hA]
  calc ((1 : ℝ) / n) / Real.log (n : ℝ) ^ 2
      ≤ (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) / Real.log (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hinc (by positivity)
    _ ≤ _ := hA2
    _ = _ := hC

/-- `1/(n √n) ≤ 2 (1/√(n-1) - 1/√n)`. -/
private theorem step_sqrt {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ) / ((n : ℝ) * Real.sqrt n)
      ≤ 2 * (1 / Real.sqrt ((n - 1 : ℕ) : ℝ) - 1 / Real.sqrt n) := by
  have h2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  set u := Real.sqrt (n : ℝ) with hu
  set v := Real.sqrt ((n - 1 : ℕ) : ℝ) with hv
  have hu0 : 0 < u := Real.sqrt_pos.mpr hnpos
  have hv0 : 0 < v := by
    rw [hv, hcast]
    exact Real.sqrt_pos.mpr (by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith)
  have hu2 : u ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hv2 : v ^ 2 = ((n - 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hvle : v ≤ u := by
    rw [hu, hv]
    exact Real.sqrt_le_sqrt (by rw [hcast]; linarith)
  have hv2' : v ^ 2 = (n : ℝ) - 1 := by rw [hv2, hcast]
  have hkey : (u + v) * u * v ≤ 2 * u ^ 3 := by nlinarith [hu0, hv0, hvle, hu2, hv2']
  have hdiff : 1 / v - 1 / u = 1 / ((u + v) * u * v) := by
    have h1 : u - v = 1 / (u + v) := by
      rw [eq_div_iff (by positivity)]
      nlinarith [hu2, hv2']
    have : 1 / v - 1 / u = (u - v) / (u * v) := by
      field_simp <;> ring
    rw [this, h1]
    field_simp
  have hmain : (1 : ℝ) / u ^ 3 ≤ 2 / ((u + v) * u * v) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hkey]
  have hleft : (1 : ℝ) / ((n : ℝ) * Real.sqrt n) = 1 / u ^ 3 := by
    have hsqu : Real.sqrt (n : ℝ) = u := hu.symm
    rw [hsqu, ← hu2]
    ring
  have hright : 2 * (1 / v - 1 / u) = 2 / ((u + v) * u * v) := by
    rw [hdiff]
    ring
  rw [hleft, hright]
  exact hmain

/-- Telescoping a difference of consecutive values. -/
private theorem sum_telescope (f : ℕ → ℝ) (a M : ℕ) (ha : 1 ≤ a) (h : a ≤ M) :
    ∑ n ∈ Icc a M, (f (n - 1) - f n) = f (a - 1) - f M := by
  induction M, h using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (f := fun n => f (n - 1) - f n) (by omega), ih]
    rw [show M + 1 - 1 = M by omega]
    ring

/-! ### Summatory bounds -/

private theorem sum_inv_log_le {a M : ℕ} (ha : 3 ≤ a) (h : a ≤ M) :
    ∑ n ∈ Icc a M, (1 : ℝ) / ((n : ℝ) * Real.log n)
      ≤ Real.log (Real.log M) - Real.log (Real.log ((a - 1 : ℕ) : ℝ)) := by
  have hstep : ∀ n ∈ Icc a M, (1 : ℝ) / ((n : ℝ) * Real.log n)
      ≤ Real.log (Real.log n) - Real.log (Real.log ((n - 1 : ℕ) : ℝ)) := by
    intro n hn
    exact step_log (by have := (mem_Icc.mp hn).1; omega)
  have hneg : ∑ n ∈ Icc a M, (Real.log (Real.log n) - Real.log (Real.log ((n - 1 : ℕ) : ℝ)))
      = -∑ n ∈ Icc a M, (Real.log (Real.log ((n - 1 : ℕ) : ℝ)) - Real.log (Real.log (n : ℝ))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  calc ∑ n ∈ Icc a M, (1 : ℝ) / ((n : ℝ) * Real.log n)
      ≤ ∑ n ∈ Icc a M, (Real.log (Real.log n) - Real.log (Real.log ((n - 1 : ℕ) : ℝ))) :=
        sum_le_sum hstep
    _ = Real.log (Real.log M) - Real.log (Real.log ((a - 1 : ℕ) : ℝ)) := by
        rw [hneg, sum_telescope (fun n => Real.log (Real.log (n : ℝ))) a M (by omega) h]
        ring

private theorem sum_inv_logsq_le {a M : ℕ} (ha : 3 ≤ a) (h : a ≤ M) :
    ∑ n ∈ Icc a M, (1 : ℝ) / ((n : ℝ) * Real.log n ^ 2)
      ≤ 1 / Real.log ((a - 1 : ℕ) : ℝ) := by
  have hstep : ∀ n ∈ Icc a M, (1 : ℝ) / ((n : ℝ) * Real.log n ^ 2)
      ≤ 1 / Real.log ((n - 1 : ℕ) : ℝ) - 1 / Real.log n := by
    intro n hn
    exact step_logsq (by have := (mem_Icc.mp hn).1; omega)
  calc ∑ n ∈ Icc a M, (1 : ℝ) / ((n : ℝ) * Real.log n ^ 2)
      ≤ ∑ n ∈ Icc a M, (1 / Real.log ((n - 1 : ℕ) : ℝ) - 1 / Real.log n) := sum_le_sum hstep
    _ = 1 / Real.log ((a - 1 : ℕ) : ℝ) - 1 / Real.log M :=
        sum_telescope (fun n => 1 / Real.log (n : ℝ)) a M (by omega) h
    _ ≤ 1 / Real.log ((a - 1 : ℕ) : ℝ) := by
        have hpos : (0 : ℝ) < Real.log (M : ℝ) :=
          Real.log_pos (by exact_mod_cast (by omega : 1 < M))
        have : 0 ≤ 1 / Real.log (M : ℝ) := div_nonneg (by norm_num) hpos.le
        linarith

private theorem sum_inv_sqrt_le {a M : ℕ} (ha : 2 ≤ a) (h : a ≤ M) :
    ∑ n ∈ Icc a M, (1 : ℝ) / ((n : ℝ) * Real.sqrt n)
      ≤ 2 / Real.sqrt ((a - 1 : ℕ) : ℝ) := by
  have hstep : ∀ n ∈ Icc a M, (1 : ℝ) / ((n : ℝ) * Real.sqrt n)
      ≤ 2 * (1 / Real.sqrt ((n - 1 : ℕ) : ℝ) - 1 / Real.sqrt n) := by
    intro n hn
    exact step_sqrt (by have := (mem_Icc.mp hn).1; omega)
  have htel : ∑ n ∈ Icc a M, (1 / Real.sqrt ((n - 1 : ℕ) : ℝ) - 1 / Real.sqrt n)
      = 1 / Real.sqrt ((a - 1 : ℕ) : ℝ) - 1 / Real.sqrt M :=
    sum_telescope (fun n => 1 / Real.sqrt (n : ℝ)) a M (by omega) h
  calc ∑ n ∈ Icc a M, (1 : ℝ) / ((n : ℝ) * Real.sqrt n)
      ≤ ∑ n ∈ Icc a M, 2 * (1 / Real.sqrt ((n - 1 : ℕ) : ℝ) - 1 / Real.sqrt n) :=
        sum_le_sum hstep
    _ = 2 * ∑ n ∈ Icc a M, (1 / Real.sqrt ((n - 1 : ℕ) : ℝ) - 1 / Real.sqrt n) := by
        rw [Finset.mul_sum]
    _ = 2 * (1 / Real.sqrt ((a - 1 : ℕ) : ℝ) - 1 / Real.sqrt M) := by rw [htel]
    _ ≤ 2 * (1 / Real.sqrt ((a - 1 : ℕ) : ℝ)) := by
        have hpos : (0 : ℝ) < Real.sqrt (M : ℝ) :=
          Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < M))
        have : 0 ≤ 1 / Real.sqrt (M : ℝ) := div_nonneg (by norm_num) hpos.le
        nlinarith
    _ = 2 / Real.sqrt ((a - 1 : ℕ) : ℝ) := by ring

/-- `√n / n²` is `1/(n √n)`, so the previous bound applies. -/
private theorem sum_sqrt_div_sq_le {a M : ℕ} (ha : 2 ≤ a) (h : a ≤ M) :
    ∑ n ∈ Icc a M, Real.sqrt (n : ℝ) / (n : ℝ) ^ 2
      ≤ 2 / Real.sqrt ((a - 1 : ℕ) : ℝ) := by
  have hEq : ∀ n ∈ Icc a M, Real.sqrt (n : ℝ) / (n : ℝ) ^ 2
      = (1 : ℝ) / ((n : ℝ) * Real.sqrt n) := by
    intro n hn
    have h1 : 1 ≤ n := by have := (mem_Icc.mp hn).1; omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    rw [div_eq_div_iff (by positivity) (by positivity)]
    nlinarith [Real.sq_sqrt hn0.le]
  rw [Finset.sum_congr rfl hEq]
  exact sum_inv_sqrt_le ha h

private theorem sum_inv_mul_pred_le {a M : ℕ} (ha : 2 ≤ a) (h : a ≤ M) :
    ∑ n ∈ Icc a M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((a : ℝ) - 1) := by
  have hstep : ∀ n ∈ Icc a M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / (((n : ℝ) - 1) * (n : ℝ)) := by
    intro n hn
    have h2 : 2 ≤ n := by have := (mem_Icc.mp hn).1; omega
    have hn0 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
    have hq : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hcast : ∀ n ∈ Icc a M, (1 : ℝ) / (((n : ℝ) - 1) * (n : ℝ))
      = 1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ) := by
    intro n hn
    have h2 : 2 ≤ n := by have := (mem_Icc.mp hn).1; omega
    have hn1 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
    rw [show ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num]
    have hq : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    field_simp <;> ring
  calc ∑ n ∈ Icc a M, (1 : ℝ) / (n : ℝ) ^ 2
      ≤ ∑ n ∈ Icc a M, (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ)) := by
        refine sum_le_sum fun n hn => ?_
        rw [← hcast n hn]
        exact hstep n hn
    _ = 1 / ((a - 1 : ℕ) : ℝ) - 1 / (M : ℝ) :=
        sum_telescope (fun n => 1 / (n : ℝ)) a M (by omega) h
    _ ≤ 1 / ((a : ℝ) - 1) := by
        have ha1 : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ a)]
          norm_num
        have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
        have : 0 ≤ 1 / (M : ℝ) := div_nonneg (by norm_num) hMpos.le
        rw [ha1]
        linarith

/-- `log t ≤ t/2` for `t ≥ 1`. -/
private theorem log_le_half_self {t : ℝ} (ht : 1 ≤ t) : Real.log t ≤ t / 2 := by
  have ht0 : 0 < t := by linarith
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have h1 : Real.log t = 2 * Real.log (Real.sqrt t) := by
    rw [Real.log_sqrt ht0.le]
    ring
  have h2 : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ht0)
  have h3 : 2 * (Real.sqrt t - 1) ≤ t / 2 := by
    nlinarith [sq_nonneg (Real.sqrt t - 2), hs, Real.sqrt_nonneg t]
  linarith

/-- `log n ≤ √n`. -/
private theorem log_le_sqrt {n : ℕ} (hn : 1 ≤ n) : Real.log n ≤ Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs : (1 : ℝ) ≤ Real.sqrt n := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have h1 : Real.log (n : ℝ) = 2 * Real.log (Real.sqrt n) := by
    rw [Real.log_sqrt hn0.le]
    ring
  have h2 : Real.log (Real.sqrt n) ≤ Real.sqrt n / 2 := log_le_half_self hs
  linarith

private theorem sum_log_div_sq_le {a M : ℕ} (ha : 2 ≤ a) (h : a ≤ M) :
    ∑ n ∈ Icc a M, Real.log n / (n : ℝ) ^ 2 ≤ 2 / Real.sqrt ((a - 1 : ℕ) : ℝ) := by
  have hstep : ∀ n ∈ Icc a M, Real.log (n : ℝ) / (n : ℝ) ^ 2
      ≤ (1 : ℝ) / ((n : ℝ) * Real.sqrt n) := by
    intro n hn
    have h1 : 1 ≤ n := by have := (mem_Icc.mp hn).1; omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    have hls : Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) := log_le_sqrt h1
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn0.le
    have e1 : Real.log (n : ℝ) * ((n : ℝ) * Real.sqrt n)
        ≤ Real.sqrt (n : ℝ) * ((n : ℝ) * Real.sqrt n) :=
      mul_le_mul_of_nonneg_right hls (by positivity)
    have e2 : Real.sqrt (n : ℝ) * ((n : ℝ) * Real.sqrt n) = (n : ℝ) ^ 2 := by
      nlinarith [hsq]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [e1, e2]
  calc ∑ n ∈ Icc a M, Real.log n / (n : ℝ) ^ 2
      ≤ ∑ n ∈ Icc a M, (1 : ℝ) / ((n : ℝ) * Real.sqrt n) := sum_le_sum hstep
    _ ≤ 2 / Real.sqrt ((a - 1 : ℕ) : ℝ) := sum_inv_sqrt_le ha h

private theorem sum_loglog_div_sq_le {a M : ℕ} (ha : 2 ≤ a) (h : a ≤ M)
    (hM : M ≤ 10 ^ 200) :
    ∑ n ∈ Icc a M, Real.log (Real.log (n : ℝ)) / (n : ℝ) ^ 2
      ≤ 6.24 * (1 / ((a : ℝ) - 1)) := by
  have hstep : ∀ n ∈ Icc a M, Real.log (Real.log (n : ℝ)) / (n : ℝ) ^ 2
      ≤ 6.24 * (1 / (n : ℝ) ^ 2) := by
    intro n hn
    have h2 : 2 ≤ n := by have := (mem_Icc.mp hn).1; omega
    have hnN : n ≤ 10 ^ 200 := by have := (mem_Icc.mp hn).2; omega
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hll : Real.log (Real.log (n : ℝ)) ≤ 6.24 := loglog_le h2 hnN
    have hpos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ hpos]
    have he : 6.24 * (1 / (n : ℝ) ^ 2) * (n : ℝ) ^ 2 = 6.24 := by
      field_simp
    linarith
  calc ∑ n ∈ Icc a M, Real.log (Real.log (n : ℝ)) / (n : ℝ) ^ 2
      ≤ ∑ n ∈ Icc a M, 6.24 * (1 / (n : ℝ) ^ 2) := sum_le_sum hstep
    _ = 6.24 * ∑ n ∈ Icc a M, 1 / (n : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 6.24 * (1 / ((a : ℝ) - 1)) := by
        have := sum_inv_mul_pred_le ha h
        have h6 : (0 : ℝ) < 6.24 := by norm_num
        nlinarith

/-! ### The explicit prime-counting bound, in the shape used below -/

private theorem log_three_ge : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  linarith [Real.exp_one_lt_d9]

private theorem log_six_ge : (5 : ℝ) / 3 ≤ Real.log 6 := by
  have h : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [h]
  linarith [log_two_lo, log_three_ge]

private theorem c3_le : 1.10556 / Real.log 2 ^ 2 ≤ 2.302 := by
  have hpos : (0 : ℝ) < Real.log 2 := by linarith [log_two_lo]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [log_two_lo, hpos]

private theorem c4_le : 5 / Real.log 6 ≤ 3 := by
  have hpos : (0 : ℝ) < Real.log 6 := by linarith [log_six_ge]
  rw [div_le_iff₀ hpos]
  linarith [log_six_ge]

private theorem c6_le :
    5 / 2 * (1 - Real.log (Real.log 2)) + 10 / Real.log 2 - 5 / (2 * Real.log 6) * Real.log 2
      ≤ 18.1 := by
  have h2pos : (0 : ℝ) < Real.log 2 := by linarith [log_two_lo]
  have h6pos : (0 : ℝ) < Real.log 6 := by linarith [log_six_ge]
  have hll : (-0.4428 : ℝ) ≤ Real.log (Real.log 2) := by
    have h := Real.one_sub_inv_le_log_of_pos h2pos
    have hinv : (Real.log 2)⁻¹ ≤ 1.4428 := by
      rw [inv_le_iff_one_le_mul₀ h2pos]
      nlinarith [log_two_lo]
    linarith
  have h10 : 10 / Real.log 2 ≤ 14.43 := by
    rw [div_le_iff₀ h2pos]
    nlinarith [log_two_lo]
  have hpos : 0 ≤ 5 / (2 * Real.log 6) * Real.log 2 := by positivity
  nlinarith [hll, h10, hpos]

set_option maxHeartbeats 1000000 in
/-- `π n ≤ n · φ n` with `φ` the explicit sum of six decreasing terms. -/
private theorem pi_le_phi {n : ℕ} (hn : 1000 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤
      (1.10556 / Real.log n + 4.42224 / Real.log n ^ 2
        + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt n / n)
        + 5 / Real.log 6 * (Real.log n / n)
        + 5 / 2 * (Real.log (Real.log n) / n) + 18.1 / n) * n := by
  have h := LeanLab.ChebyshevExplicit.pi_le_110556_refined n (by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  set L := Real.log (n : ℝ) with hLdef
  set S := Real.sqrt (n : ℝ) with hSdef
  have hkey : (1.10556 / L + 4.42224 / L ^ 2 + 1.10556 / Real.log 2 ^ 2 * (S / n)
      + 5 / Real.log 6 * (L / n) + 5 / 2 * (Real.log L / n) + 18.1 / n) * n
      = 1.10556 * n / L + 4.42224 * n / L ^ 2 + 1.10556 * S / Real.log 2 ^ 2
        + 5 / Real.log 6 * L + 5 / 2 * Real.log L + 18.1 := by
    field_simp <;> ring
  rw [hkey]
  nlinarith [h, c6_le]

/-- `π (M+1) = π M + 1_{M+1 prime}`. -/
private theorem primeCounting_succ (M : ℕ) :
    Nat.primeCounting (M + 1) = Nat.primeCounting M + (if (M + 1).Prime then 1 else 0) := by
  have hnot : M + 1 ∉ Nat.primesLE M := Nat.notMem_primesLE M
  have hcard : (Nat.primesLE (M + 1)).card
      = (Nat.primesLE M).card + (if (M + 1).Prime then 1 else 0) := by
    rw [Nat.primesLE_succ]
    by_cases hp : (M + 1).Prime
    · rw [if_pos hp, Finset.card_insert_of_notMem hnot]
      simp [hp]
    · rw [if_neg hp]
      simp [hp]
  simpa using hcard

/-- `∑_{n ∈ [1000, M]}` splits off its top term. -/
private theorem sum_Icc_pred_add (g : ℕ → ℝ) {M : ℕ} (hM : 1000 ≤ M) :
    ∑ n ∈ Icc 1000 M, g n = ∑ n ∈ Icc 1000 (M - 1), g n + g M := by
  conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ M)]
  rw [Finset.sum_Icc_succ_top (by omega)]
  simp only [Nat.sub_add_cancel (by omega : 1 ≤ M)]

set_option maxHeartbeats 2000000 in
/-- Abel summation: `Σ_{1000 ≤ p ≤ M} 1/(p-1)` is bounded by the prime counting function
integrated against `1/((n-1)n)`. -/
private theorem abel_helper (M : ℕ) (hM : 1000 ≤ M) :
    ∑ n ∈ Icc 1000 M, (if n.Prime then (1 : ℝ) / ((n : ℝ) - 1) else 0)
      ≤ (Nat.primeCounting M : ℝ) / ((M : ℝ) - 1)
        + ∑ n ∈ Icc 1000 (M - 1), (Nat.primeCounting n : ℝ) / (((n : ℝ) - 1) * (n : ℝ)) := by
  induction M, hM using Nat.le_induction with
  | base =>
    have h1000 : ¬ (1000 : ℕ).Prime := by norm_num [Nat.Prime]
    have hemp : Icc 1000 (1000 - 1) = (∅ : Finset ℕ) := by
      rw [Finset.Icc_eq_empty]
      omega
    rw [hemp, Finset.sum_empty]
    simp only [h1000, ite_false, Finset.Icc_self, Finset.sum_singleton]
    have : (0 : ℝ) ≤ (Nat.primeCounting 1000 : ℝ) / ((1000 : ℝ) - 1) := by positivity
    linarith
  | succ M hM ih =>
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
    have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
      have : (1000 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    have hLHS : ∑ n ∈ Icc 1000 (M + 1), (if n.Prime then (1 : ℝ) / ((n : ℝ) - 1) else 0)
        = ∑ n ∈ Icc 1000 M, (if n.Prime then (1 : ℝ) / ((n : ℝ) - 1) else 0)
          + (if (M + 1).Prime then (1 : ℝ) / (((M + 1 : ℕ) : ℝ) - 1) else 0) :=
      Finset.sum_Icc_succ_top (by omega) _
    have hRHS : ∑ n ∈ Icc 1000 (M + 1 - 1),
          (Nat.primeCounting n : ℝ) / (((n : ℝ) - 1) * (n : ℝ))
        = ∑ n ∈ Icc 1000 (M - 1), (Nat.primeCounting n : ℝ) / (((n : ℝ) - 1) * (n : ℝ))
          + (Nat.primeCounting M : ℝ) / (((M : ℝ) - 1) * (M : ℝ)) :=
      sum_Icc_pred_add (fun n => (Nat.primeCounting n : ℝ) / (((n : ℝ) - 1) * (n : ℝ))) hM
    rw [hLHS, hRHS]
    have hcastite : (((if (M + 1).Prime then 1 else 0) : ℕ) : ℝ)
        = (if (M + 1).Prime then (1 : ℝ) else 0) := by
      by_cases hp : (M + 1).Prime <;> simp [hp]
    have hpc : ((Nat.primeCounting (M + 1) : ℕ) : ℝ)
        = (Nat.primeCounting M : ℝ) + (if (M + 1).Prime then (1 : ℝ) else 0) := by
      rw [primeCounting_succ M, Nat.cast_add, hcastite]
    have hden : (((M + 1 : ℕ)) : ℝ) - 1 = (M : ℝ) := by push_cast; ring
    rw [hpc, hden]
    have hδ : (if (M + 1).Prime then (1 : ℝ) / (M : ℝ) else 0)
        ≤ (if (M + 1).Prime then (1 : ℝ) else 0) / (M : ℝ) := by
      by_cases hp : (M + 1).Prime
      · rw [if_pos hp, if_pos hp]
      · rw [if_neg hp, if_neg hp]
        simp
    have hsplit : (Nat.primeCounting M : ℝ) / ((M : ℝ) - 1)
        = (Nat.primeCounting M : ℝ) / (M : ℝ)
          + (Nat.primeCounting M : ℝ) / (((M : ℝ) - 1) * (M : ℝ)) := by
      field_simp <;> ring
    have hd : ((Nat.primeCounting M : ℝ) + (if (M + 1).Prime then (1 : ℝ) else 0)) / (M : ℝ)
        = (Nat.primeCounting M : ℝ) / (M : ℝ)
          + (if (M + 1).Prime then (1 : ℝ) else 0) / (M : ℝ) :=
      add_div _ _ _
    linarith [ih, hδ, hsplit, hd]

/-! ### Helpers -/

/-- `Ω` of a product of two nonzero numbers is the sum of the `Ω`s. -/
private theorem bigOmega_mul_ne {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    bigOmega (m * n) = bigOmega m + bigOmega n := by
  unfold bigOmega
  rw [(Nat.perm_primeFactorsList_mul hm hn).length_eq, List.length_append]



/-- `Ω (2 ^ k) = k`, the extremal prime power. -/
private theorem bigOmega_two_pow (k : ℕ) : bigOmega (2 ^ k) = k := by
  rw [bigOmega, Nat.Prime.primeFactorsList_pow Nat.prime_two, List.length_replicate]

/-! ### Refutation pass: the leaves are not vacuous, and `TwoAlmostPrimes` really needs `2 ≤ N` -/

/-- `N = 1` admits no decomposition into two positive summands, so `TwoAlmostPrimes` is false
there: the `2 ≤ N` hypothesis of every leaf is load-bearing. -/
private theorem not_twoAlmostPrimes_one (k : ℕ) : ¬ TwoAlmostPrimes k 1 := by
  rintro ⟨a, b, ha, hb, hab, -⟩
  omega

/-- The hypothesis set of `leaf_even_finite` is satisfiable. -/
private theorem even_finite_hyp_sat :
    ∃ N : ℕ, 2 ≤ N ∧ Even N ∧ 2 ^ 40 + 1 < N ∧ N ≤ 4 * 10 ^ 18 :=
  ⟨2 ^ 41, by norm_num, ⟨2 ^ 40, by norm_num⟩, by norm_num, by norm_num⟩

/-- The hypothesis set of `leaf_odd_finite` is satisfiable. -/
private theorem odd_finite_hyp_sat :
    ∃ N : ℕ, 2 ≤ N ∧ Odd N ∧ 2 ^ 40 + 1 < N ∧ N ≤ 4 * 10 ^ 18 :=
  ⟨2 ^ 41 + 1, by norm_num, ⟨2 ^ 40, by norm_num⟩, by norm_num, by norm_num⟩

/-- The hypothesis set of `leaf_finite_window` is satisfiable. -/
private theorem finite_window_hyp_sat :
    ∃ N : ℕ, 2 ≤ N ∧ 4 * 10 ^ 18 < N ∧ N < 10 ^ 200 :=
  ⟨4 * 10 ^ 18 + 1, by norm_num, by norm_num, by norm_num⟩

/-- The hypothesis set of `leaf_analytic_large` is satisfiable, at an unbounded value. -/
private theorem analytic_large_hyp_sat : ∃ N : ℕ, 2 ≤ N ∧ 10 ^ 200 ≤ N :=
  ⟨10 ^ 200, by norm_num, le_rfl⟩

/-- The ranges of the five leaves cover `{N : 2 ≤ N}` with no gap. -/
private theorem split_partition (N : ℕ) (_hN : 2 ≤ N) :
    N ≤ 2 ^ 40 + 1 ∨ (2 ^ 40 + 1 < N ∧ N ≤ 4 * 10 ^ 18) ∨
      (4 * 10 ^ 18 < N ∧ N < 10 ^ 200) ∨ 10 ^ 200 ≤ N := by
  omega

/-- The elementary split `N = 1 + (N - 1)` stops exactly at `N = 2 ^ 41 + 1`: there `N - 1` has
`41` prime factors. So `leaf_one_plus_small` cannot be widened by its own technique. -/
private theorem one_split_stops : ¬ (bigOmega (2 ^ 41) ≤ 40) := by
  rw [bigOmega_two_pow]
  norm_num

/-! ### First-moment reduction

`TwoAlmostPrimes 40 N` needs one `a` with `Ω a + Ω (N - a) ≤ 40`. Summing the *negation* over
`a ∈ [1, N - 1]` and using that `a ↦ N - a` permutes `[1, N - 1]` gives
`2 Σ_{a ≤ N-1} Ω a ≥ 41 (N - 1)`, so an average of `Ω` below `41/2` forces a good `a`. -/

/-- `a ↦ N - a` permutes `[1, N - 1]`. -/
private theorem sum_bigOmega_sub (N : ℕ) (hN : 2 ≤ N) :
    ∑ a ∈ Icc 1 (N - 1), bigOmega (N - a) = ∑ a ∈ Icc 1 (N - 1), bigOmega a := by
  have hmem : ∀ a ∈ Icc 1 (N - 1), N - a ∈ Icc 1 (N - 1) := by
    intro a ha
    simp only [mem_Icc] at ha ⊢
    omega
  have hinj : ∀ x ∈ Icc 1 (N - 1), ∀ y ∈ Icc 1 (N - 1), N - x = N - y → x = y := by
    intro x hx y hy h
    simp only [mem_Icc] at hx hy
    omega
  have himg : (Icc 1 (N - 1)).image (fun a => N - a) = Icc 1 (N - 1) := by
    refine Finset.Subset.antisymm (fun b hb => ?_) (fun b hb => ?_)
    · obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
      exact hmem a ha
    · refine mem_image.mpr ⟨N - b, hmem b hb, ?_⟩
      simp only [mem_Icc] at hb
      omega
  have h1 : ∑ a ∈ Icc 1 (N - 1), bigOmega (N - a)
      = ∑ b ∈ (Icc 1 (N - 1)).image (fun a => N - a), bigOmega b :=
    (sum_image hinj).symm
  rw [h1, himg]

/-- If `2 Σ_{a ≤ N-1} Ω a < 41 (N - 1)` then some `a ∈ [1, N-1]` has
`Ω a + Ω (N - a) ≤ 40`. -/
private theorem exists_good_of_sum_lt {N : ℕ} (hN : 2 ≤ N)
    (h : 2 * ∑ a ∈ Icc 1 (N - 1), bigOmega a < 41 * (N - 1)) :
    ∃ a ∈ Icc 1 (N - 1), bigOmega a + bigOmega (N - a) ≤ 40 := by
  by_contra hc
  push_neg at hc
  have hcard : (Icc 1 (N - 1)).card = N - 1 := by
    rw [Nat.card_Icc]
    omega
  have hsum : ∑ a ∈ Icc 1 (N - 1), (bigOmega a + bigOmega (N - a))
      = 2 * ∑ a ∈ Icc 1 (N - 1), bigOmega a := by
    rw [sum_add_distrib, sum_bigOmega_sub N hN, two_mul]
  have hge : 41 * (N - 1) ≤ ∑ a ∈ Icc 1 (N - 1), (bigOmega a + bigOmega (N - a)) := by
    have hc' : ∑ a ∈ Icc 1 (N - 1), 41
        ≤ ∑ a ∈ Icc 1 (N - 1), (bigOmega a + bigOmega (N - a)) :=
      sum_le_sum fun a ha => hc a ha
    rwa [sum_const, hcard, smul_eq_mul, Nat.mul_comm] at hc'
  omega

/-- **The first-moment reduction.** An average of `Ω` below `41/2` on `[1, N - 1]` closes the
counting step of every leaf. -/
private theorem twoAlmostPrimes_of_sum_lt {N : ℕ} (hN : 2 ≤ N)
    (h : 2 * ∑ a ∈ Icc 1 (N - 1), bigOmega a < 41 * (N - 1)) : TwoAlmostPrimes 40 N := by
  obtain ⟨a, ha, hlt⟩ := exists_good_of_sum_lt hN h
  simp only [mem_Icc] at ha
  have ha0 : a ≠ 0 := by omega
  have hb0 : N - a ≠ 0 := by omega
  refine ⟨a, N - a, by omega, by omega, by omega, ?_⟩
  rw [bigOmega_mul_ne ha0 hb0]
  exact hlt

/-! ### From a reciprocal-prime estimate to the counting step

The per-`a` identity `Ω a = Σ_{p ∣ a} v_p a`, double counted over `a ≤ N`, gives
`Σ_{a ≤ N} Ω a ≤ Σ_{p ≤ N} Σ_{k ≥ 1} ⌊N / p ^ k⌋ ≤ 2 N Σ_{p ≤ N} 1/(p - 1)`
(the `p ^ k ≥ p · 2 ^ (k - 1)` loss is the factor `2`). Combined with `twoAlmostPrimes_of_sum_lt`
this makes the counting step of `leaf_even_finite`, `leaf_odd_finite` and `leaf_finite_window`
follow from the *single* estimate `Σ_{p ≤ N} 1/(p - 1) ≤ 10`, whose true value is `4.79` at
`N = 4 * 10 ^ 18` and `7.17` at `N = 10 ^ 200`. -/

/-- `Ω a` is the sum of the `p`-adic valuations of `a`. -/
private theorem bigOmega_eq_sum_factorization (a : ℕ) :
    bigOmega a = ∑ p ∈ a.primeFactors, a.factorization p := by
  rw [bigOmega_eq_cardFactors, ArithmeticFunction.cardFactors_eq_sum_factorization]
  simp only [Finsupp.sum]
  exact Finset.sum_congr a.support_factorization fun _ _ => rfl

/-- `v_p a ≤ a`. -/
private theorem factorization_le_self {a p : ℕ} (hp : p.Prime) (ha : 0 < a) :
    a.factorization p ≤ a := by
  have hdvd : p ^ (a.factorization p) ∣ a := by
    rw [hp.pow_dvd_iff_le_factorization ha.ne']
  have hle : p ^ (a.factorization p) ≤ a := Nat.le_of_dvd ha hdvd
  have h2 : a.factorization p ≤ 2 ^ (a.factorization p) :=
    le_of_lt (Nat.lt_two_pow_self (n := a.factorization p))
  have h3 : 2 ^ (a.factorization p) ≤ p ^ (a.factorization p) :=
    Nat.pow_le_pow_left hp.two_le _
  omega

/-- `v_p a` is the number of `k ∈ [1, a]` with `p ^ k ∣ a`. -/
private theorem factorization_eq_card_pow_dvd {a p : ℕ} (hp : p.Prime) (ha : 0 < a) :
    a.factorization p = ∑ k ∈ Icc 1 a, (if p ^ k ∣ a then 1 else 0) := by
  have hset : (Icc 1 a).filter (fun k => p ^ k ∣ a) = Icc 1 (a.factorization p) := by
    ext k
    simp only [mem_filter, mem_Icc, hp.pow_dvd_iff_le_factorization ha.ne']
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2.trans (factorization_le_self hp ha)⟩, h2⟩
  rw [Finset.sum_boole, hset]
  simp only [Nat.cast_id, Nat.card_Icc]
  omega

/-- `Σ_{a ≤ N} v_p a ≤ Σ_{k ≤ N} ⌊N / p ^ k⌋`. -/
private theorem sum_factorization_le {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ∑ a ∈ Icc 1 N, a.factorization p ≤ ∑ k ∈ Icc 1 N, N / p ^ k := by
  have hstep : ∑ a ∈ Icc 1 N, a.factorization p
      = ∑ a ∈ Icc 1 N, ∑ k ∈ Icc 1 N, (if p ^ k ∣ a then 1 else 0) := by
    refine sum_congr rfl (fun a ha => ?_)
    have ha0 : 0 < a := (mem_Icc.mp ha).1
    rw [factorization_eq_card_pow_dvd hp ha0]
    refine Finset.sum_subset (fun k hk => ?_) (fun k hk hk' => ?_)
    · simp only [mem_Icc] at hk ⊢
      exact ⟨hk.1, hk.2.trans (mem_Icc.mp ha).2⟩
    · have hka : a < k := by
        simp only [mem_Icc] at hk hk'
        omega
      have hkpk : k ≤ p ^ k := by
        have h2 : k ≤ 2 ^ k := le_of_lt (Nat.lt_two_pow_self (n := k))
        have h3 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
        omega
      have hlt : ¬ (p ^ k ∣ a) := by
        intro hd
        have := Nat.le_of_dvd (mem_Icc.mp ha).1 hd
        omega
      simp [hlt]
  rw [hstep, Finset.sum_comm]
  refine sum_le_sum (fun k hk => ?_)
  have hset : (Icc 1 N).filter (fun a => p ^ k ∣ a) = (Ioc 0 N).filter (fun a => p ^ k ∣ a) := by
    ext a
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  rw [Finset.sum_boole, hset, Nat.Ioc_filter_dvd_card_eq_div]
  simp

/-- `Σ_{k ≤ M} (1/2) ^ (k - 1) = 2 - (1/2) ^ (M - 1)`, the geometric sum in closed form. -/
private theorem geom_half_aux : ∀ M : ℕ,
    ∑ k ∈ Icc 1 (M + 1), ((1 : ℝ) / 2) ^ (k - 1) = 2 - ((1 : ℝ) / 2) ^ M
  | 0 => by norm_num
  | (M + 1) => by
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ (M + 1) + 1)]
    rw [show (M + 1) + 1 - 1 = M + 1 by omega]
    rw [geom_half_aux M, pow_succ]
    ring

/-- `Σ_{k ≤ M} (1/2) ^ (k - 1) ≤ 2`. -/
private theorem geom_half_le (M : ℕ) : ∑ k ∈ Icc 1 M, ((1 : ℝ) / 2) ^ (k - 1) ≤ 2 := by
  rcases Nat.eq_zero_or_pos M with h | h
  · subst h
    simp
  · obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
    rw [geom_half_aux n]
    have : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ n := by positivity
    linarith

/-- `Σ_{k ≤ N} 1 / p ^ k ≤ 2 / (p - 1)` for a prime `p`. -/
private theorem sum_inv_pow_le {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ∑ k ∈ Icc 1 N, (1 : ℝ) / (p : ℝ) ^ k ≤ 2 / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hhalf : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  have hterm : ∀ k ∈ Icc 1 N,
      (1 : ℝ) / (p : ℝ) ^ k = ((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (p : ℝ)) ^ (k - 1) := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hpow : (p : ℝ) ^ k = (p : ℝ) * (p : ℝ) ^ (k - 1) := by
      conv_lhs => rw [show k = k - 1 + 1 by omega]
      rw [pow_succ']
    rw [hpow, div_pow, one_pow, mul_one_div, div_div]
  calc ∑ k ∈ Icc 1 N, (1 : ℝ) / (p : ℝ) ^ k
      = ∑ k ∈ Icc 1 N, ((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (p : ℝ)) ^ (k - 1) :=
        sum_congr rfl hterm
    _ ≤ ∑ k ∈ Icc 1 N, ((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / 2) ^ (k - 1) :=
        sum_le_sum (fun k hk =>
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hhalf (k - 1))
            (by positivity))
    _ = ((1 : ℝ) / (p : ℝ)) * ∑ k ∈ Icc 1 N, ((1 : ℝ) / 2) ^ (k - 1) := by
        rw [Finset.mul_sum]
    _ ≤ ((1 : ℝ) / (p : ℝ)) * 2 :=
        mul_le_mul_of_nonneg_left (geom_half_le N) (by positivity)
    _ ≤ 2 / ((p : ℝ) - 1) := by
        have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        have e : ((1 : ℝ) / (p : ℝ)) * 2 = 2 / (p : ℝ) := by ring
        rw [e, div_le_div_iff₀ hp0 hp1]
        linarith

/-- `Σ_{k ≤ N} N / p ^ k ≤ 2 N / (p - 1)`. -/
private theorem sum_div_pow_le {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ∑ k ∈ Icc 1 N, (N : ℝ) / (p : ℝ) ^ k ≤ 2 * (N : ℝ) / ((p : ℝ) - 1) := by
  have hfac : ∑ k ∈ Icc 1 N, (N : ℝ) / (p : ℝ) ^ k
      = (N : ℝ) * ∑ k ∈ Icc 1 N, (1 : ℝ) / (p : ℝ) ^ k := by
    rw [Finset.mul_sum]
    exact sum_congr rfl (fun k _ => by ring)
  rw [hfac]
  calc (N : ℝ) * ∑ k ∈ Icc 1 N, (1 : ℝ) / (p : ℝ) ^ k
      ≤ (N : ℝ) * (2 / ((p : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left (sum_inv_pow_le hp N) (by positivity)
    _ = 2 * (N : ℝ) / ((p : ℝ) - 1) := by ring

/-- `Ω a` as a sum over the primes below `N + 1`, for `1 ≤ a ≤ N`. -/
private theorem bigOmega_eq_sum_primesBelow {a N : ℕ} (ha1 : 1 ≤ a) (haN : a ≤ N) :
    bigOmega a = ∑ p ∈ (N + 1).primesBelow, a.factorization p := by
  rw [bigOmega_eq_sum_factorization]
  refine Finset.sum_subset (fun p hp => ?_) (fun p hpN hpnot => ?_)
  · rw [Nat.mem_primeFactors] at hp
    have hpa : p ≤ a := Nat.le_of_dvd (by omega) hp.2.1
    rw [Nat.mem_primesBelow]
    exact ⟨by omega, hp.1⟩
  · rw [Nat.factorization_eq_zero_of_not_dvd]
    intro hdvd
    exact hpnot (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primesBelow.mp hpN).2, hdvd, by omega⟩)

/-- `Σ_{a ≤ N} Ω a` as a double sum over primes. -/
private theorem sum_bigOmega_swap (N : ℕ) :
    ∑ a ∈ Icc 1 N, (bigOmega a : ℝ)
      = ∑ p ∈ (N + 1).primesBelow, ∑ a ∈ Icc 1 N, (a.factorization p : ℝ) := by
  have h1 : ∀ a ∈ Icc 1 N, (bigOmega a : ℝ) =
      ∑ p ∈ (N + 1).primesBelow, (a.factorization p : ℝ) := by
    intro a ha
    obtain ⟨ha1, haN⟩ := mem_Icc.mp ha
    rw [bigOmega_eq_sum_primesBelow ha1 haN]
    push_cast
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]

/-- The `p`-adic piece: `Σ_{a ≤ N} v_p a ≤ 2 N / (p - 1)`. -/
private theorem sum_factorization_cast_le {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ∑ a ∈ Icc 1 N, (a.factorization p : ℝ) ≤ 2 * (N : ℝ) / ((p : ℝ) - 1) := by
  have hnat := sum_factorization_le hp N
  have h1 : ((∑ k ∈ Icc 1 N, N / p ^ k : ℕ) : ℝ) ≤ ∑ k ∈ Icc 1 N, (N : ℝ) / (p : ℝ) ^ k := by
    rw [Nat.cast_sum]
    refine sum_le_sum (fun k _ => ?_)
    rw [← Nat.cast_pow]
    exact Nat.cast_div_le
  calc ∑ a ∈ Icc 1 N, (a.factorization p : ℝ)
      = ((∑ a ∈ Icc 1 N, a.factorization p : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((∑ k ∈ Icc 1 N, N / p ^ k : ℕ) : ℝ) := by exact_mod_cast hnat
    _ ≤ ∑ k ∈ Icc 1 N, (N : ℝ) / (p : ℝ) ^ k := h1
    _ ≤ 2 * (N : ℝ) / ((p : ℝ) - 1) := sum_div_pow_le hp N

/-- **`Σ_{a ≤ N} Ω a ≤ 2 N Σ_{p ≤ N} 1/(p - 1)`.** -/
private theorem sum_bigOmega_le_inv_pred (N : ℕ) :
    ∑ a ∈ Icc 1 N, (bigOmega a : ℝ)
      ≤ 2 * (N : ℝ) * ∑ p ∈ (N + 1).primesBelow, (1 : ℝ) / ((p : ℝ) - 1) := by
  rw [sum_bigOmega_swap]
  calc ∑ p ∈ (N + 1).primesBelow, ∑ a ∈ Icc 1 N, (a.factorization p : ℝ)
      ≤ ∑ p ∈ (N + 1).primesBelow, 2 * (N : ℝ) / ((p : ℝ) - 1) :=
        sum_le_sum (fun p hp => sum_factorization_cast_le (Nat.mem_primesBelow.mp hp).2 N)
    _ = 2 * (N : ℝ) * ∑ p ∈ (N + 1).primesBelow, (1 : ℝ) / ((p : ℝ) - 1) := by
        rw [Finset.mul_sum]
        exact sum_congr rfl (fun p _ => by ring)

/-- **The counting step of three leaves from one reciprocal-prime estimate.** For `2 ^ 40 + 1 < N`,
`Σ_{p ≤ N} 1/(p - 1) ≤ 10` gives `TwoAlmostPrimes 40 N`. The sum's true value is `4.79` at
`N = 4 * 10 ^ 18` and `7.17` at `N = 10 ^ 200`, so one Mertens-type estimate covers the whole of
`leaf_even_finite`, `leaf_odd_finite` and `leaf_finite_window` - which the earlier `z ^ Ω` (Rankin)
route could not, since it needed `Σ 1/p ≤ 4.3` while `Σ_{p ≤ 10^200} 1/p = 6.39`. -/
private theorem twoAlmostPrimes_of_inv_pred_sum {N : ℕ} (hN : 2 ^ 40 + 1 < N)
    (hS : ∑ p ∈ (N + 1).primesBelow, (1 : ℝ) / ((p : ℝ) - 1) ≤ 10) :
    TwoAlmostPrimes 40 N := by
  have hN42 : 42 ≤ N := by
    have : (41 : ℕ) ≤ 2 ^ 40 := by norm_num
    omega
  refine twoAlmostPrimes_of_sum_lt (by omega) ?_
  have hsum := sum_bigOmega_le_inv_pred N
  have hsub : ∑ a ∈ Icc 1 (N - 1), (bigOmega a : ℝ) ≤ ∑ a ∈ Icc 1 N, (bigOmega a : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => by positivity)
    intro a ha
    simp only [mem_Icc] at ha ⊢
    omega
  have hN41 : (41 : ℝ) < (N : ℝ) := by
    have h2 : (42 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN42
    linarith
  have hNm : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ N)]
    norm_num
  have hS' : 2 * (N : ℝ) * ∑ p ∈ (N + 1).primesBelow, (1 : ℝ) / ((p : ℝ) - 1)
      ≤ 20 * (N : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ))
    linarith
  have hmain : 2 * (∑ a ∈ Icc 1 (N - 1), (bigOmega a : ℝ)) ≤ 40 * (N : ℝ) := by
    linarith [hsub, hsum, hS']
  have hcast1 : ((∑ a ∈ Icc 1 (N - 1), bigOmega a : ℕ) : ℝ)
      = ∑ a ∈ Icc 1 (N - 1), (bigOmega a : ℝ) := by
    push_cast
    ring
  have hkey : (2 * (∑ a ∈ Icc 1 (N - 1), bigOmega a) : ℝ) < ((41 * (N - 1) : ℕ) : ℝ) := by
    rw [hcast1, Nat.cast_mul, hNm]
    have h41 : (↑(41 : ℕ) : ℝ) * ((N : ℝ) - 1) = 41 * (N : ℝ) - 41 := by
      push_cast
      ring
    rw [h41]
    linarith [hmain, hN41]
  exact_mod_cast hkey


/-! ### The numerical core: `Σ_{p ≤ N} 1/(p-1) ≤ 10` for `N ≤ 10^200` -/

private theorem exp_one_lt_thousand : Real.exp 1 < 1000 := by linarith [Real.exp_one_lt_d9]

private theorem log_div_self_le {n : ℕ} (hn : 1000 ≤ n) :
    Real.log (n : ℝ) / (n : ℝ) ≤ Real.log 1000 / 1000 := by
  have hnE : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx : ((n : ℝ)) ∈ Set.Ici (Real.exp 1) := by
    simp only [Set.mem_Ici]
    linarith [Real.exp_one_lt_d9.le]
  have hy : ((1000 : ℝ)) ∈ Set.Ici (Real.exp 1) := by
    simp only [Set.mem_Ici]
    linarith [Real.exp_one_lt_d9.le]
  exact Real.log_div_self_antitoneOn hy hx hnE

private theorem phi_le {n : ℕ} (hn : 1000 ≤ n) :
    1.10556 / Real.log n + 4.42224 / Real.log n ^ 2
      + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt n / n)
      + 5 / Real.log 6 * (Real.log n / n)
      + 5 / 2 * (Real.log (Real.log n) / n) + 18.1 / n ≤ 0.387 := by
  have hnE : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hLn : (6.83 : ℝ) ≤ Real.log (n : ℝ) :=
    (by linarith [log_thousand_ge] : (6.83 : ℝ) ≤ Real.log 1000).trans
      (Real.log_le_log (by norm_num) hnE)
  have hL1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by linarith
  have h1 : 1.10556 / Real.log (n : ℝ) ≤ 0.1619 := by
    rw [div_le_iff₀ hL]
    nlinarith [hLn]
  have h2 : 4.42224 / Real.log (n : ℝ) ^ 2 ≤ 0.0949 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hLn, hL]
  have hsqrtpos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsq : Real.sqrt (n : ℝ) / (n : ℝ) = 1 / Real.sqrt (n : ℝ) := by
    have hs : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
    field_simp
    nlinarith [hs]
  have hs316 : (31.6 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [show (31.6 : ℝ) = Real.sqrt (31.6 ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hinv : 1 / Real.sqrt (n : ℝ) ≤ 1 / 31.6 := by
    rw [div_le_div_iff₀ hsqrtpos (by norm_num)]
    linarith
  have h3 : 1.10556 / Real.log 2 ^ 2 * (Real.sqrt (n : ℝ) / (n : ℝ)) ≤ 0.0729 := by
    rw [hsq]
    have hc := c3_le
    have hc0 : (0 : ℝ) ≤ 1.10556 / Real.log 2 ^ 2 := by positivity
    calc 1.10556 / Real.log 2 ^ 2 * (1 / Real.sqrt (n : ℝ))
        ≤ 1.10556 / Real.log 2 ^ 2 * (1 / 31.6) :=
          mul_le_mul_of_nonneg_left hinv hc0
      _ ≤ 2.302 * (1 / 31.6) := by nlinarith
      _ ≤ 0.0729 := by norm_num
  have h4 : 5 / Real.log 6 * (Real.log (n : ℝ) / (n : ℝ)) ≤ 0.02098 := by
    have hc := c4_le
    have hc0 : (0 : ℝ) ≤ 5 / Real.log 6 := by positivity
    have hdl : Real.log (n : ℝ) / (n : ℝ) ≤ Real.log 1000 / 1000 := log_div_self_le hn
    have hdl0 : Real.log (n : ℝ) / (n : ℝ) ≤ 0.00699 := by
      have := log_thousand_le
      nlinarith
    have hpos : (0 : ℝ) ≤ Real.log (n : ℝ) / (n : ℝ) := by positivity
    nlinarith [hc, hc0, hdl0, hpos]
  have h5 : 5 / 2 * (Real.log (Real.log (n : ℝ)) / (n : ℝ)) ≤ 0.01748 := by
    have hll : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
      rw [Real.log_le_iff_le_exp hL, Real.exp_log hn0]
      linarith [Real.log_le_sub_one_of_pos hn0]
    have hdl0 : Real.log (n : ℝ) / (n : ℝ) ≤ 0.00699 := by
      have h1 := log_div_self_le hn
      have h2 := log_thousand_le
      nlinarith
    have hll' : Real.log (Real.log (n : ℝ)) / (n : ℝ) ≤ Real.log (n : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_right hll hn0.le
    have hpos : (0 : ℝ) ≤ Real.log (Real.log (n : ℝ)) / (n : ℝ) :=
      div_nonneg (Real.log_nonneg hL1) hn0.le
    nlinarith [hll', hdl0, hpos]
  have h6 : 18.1 / (n : ℝ) ≤ 0.0181 := by
    rw [div_le_iff₀ hn0]
    nlinarith [hnE]
  linarith [h1, h2, h3, h4, h5, h6]

private theorem phi_nonneg {n : ℕ} (hn : 1000 ≤ n) :
    0 ≤ 1.10556 / Real.log n + 4.42224 / Real.log n ^ 2
      + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt n / n)
      + 5 / Real.log 6 * (Real.log n / n)
      + 5 / 2 * (Real.log (Real.log n) / n) + 18.1 / n := by
  have hnE : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hS : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hLn : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have h1 : Real.log 1000 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hnE
    linarith [log_thousand_ge]
  have hll : 0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg hLn
  have h1 : 0 ≤ 1.10556 / Real.log (n : ℝ) := by positivity
  have h2 : 0 ≤ 4.42224 / Real.log (n : ℝ) ^ 2 := by positivity
  have h3 : 0 ≤ 1.10556 / Real.log 2 ^ 2 * (Real.sqrt (n : ℝ) / (n : ℝ)) := by positivity
  have h4 : 0 ≤ 5 / Real.log 6 * (Real.log (n : ℝ) / (n : ℝ)) := by positivity
  have h5 : 0 ≤ 5 / 2 * (Real.log (Real.log (n : ℝ)) / (n : ℝ)) := by positivity
  have h6 : 0 ≤ 18.1 / (n : ℝ) := by positivity
  linarith [h1, h2, h3, h4, h5, h6]

set_option maxHeartbeats 4000000 in
private theorem tail_bound {N : ℕ} (h1000 : 1000 ≤ N) (hN : N ≤ 10 ^ 200) :
    ∑ n ∈ Icc 1000 N, (if n.Prime then (1 : ℝ) / ((n : ℝ) - 1) else 0) ≤ 6.15 := by
  have habel := abel_helper N h1000
  set S1 := ∑ n ∈ Icc 1000 N, (1 : ℝ) / ((n : ℝ) * Real.log n) with hS1
  set S2 := ∑ n ∈ Icc 1000 N, (1 : ℝ) / ((n : ℝ) * Real.log n ^ 2) with hS2
  set S3 := ∑ n ∈ Icc 1000 N, Real.sqrt (n : ℝ) / (n : ℝ) ^ 2 with hS3
  set S4 := ∑ n ∈ Icc 1000 N, Real.log (n : ℝ) / (n : ℝ) ^ 2 with hS4
  set S5 := ∑ n ∈ Icc 1000 N, Real.log (Real.log (n : ℝ)) / (n : ℝ) ^ 2 with hS5
  set S6 := ∑ n ∈ Icc 1000 N, (1 : ℝ) / (n : ℝ) ^ 2 with hS6
  have hb1 : S1 ≤ 4.23 := by
    rw [hS1]
    have h := sum_inv_log_le (a := 1000) (M := N) (by norm_num) h1000
    linarith [h, loglog_gap h1000 hN]
  have hb2 : S2 ≤ 0.147 := by
    rw [hS2]
    have h := sum_inv_logsq_le (a := 1000) (M := N) (by norm_num) h1000
    have hpos : (0 : ℝ) < Real.log ((1000 - 1 : ℕ) : ℝ) := by
      have : ((999 : ℕ) : ℝ) = 999 := by norm_num
      rw [show ((1000 - 1 : ℕ) : ℝ) = 999 by norm_num]
      exact Real.log_pos (by norm_num)
    have h147 : 1 / Real.log ((1000 - 1 : ℕ) : ℝ) ≤ 0.147 := by
      rw [div_le_iff₀ hpos]
      have := log_999_ge
      nlinarith
    linarith
  have hb3 : S3 ≤ 0.0633 := by
    rw [hS3]
    have h := sum_sqrt_div_sq_le (a := 1000) (M := N) (by norm_num) h1000
    have hs : (31.6 : ℝ) ≤ Real.sqrt ((1000 - 1 : ℕ) : ℝ) := by
      rw [show ((1000 - 1 : ℕ) : ℝ) = 999 by norm_num]
      rw [show (31.6 : ℝ) = Real.sqrt (31.6 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hpos : (0 : ℝ) < Real.sqrt ((1000 - 1 : ℕ) : ℝ) := by positivity
    have h633 : 2 / Real.sqrt ((1000 - 1 : ℕ) : ℝ) ≤ 0.0633 := by
      rw [div_le_iff₀ hpos]
      nlinarith
    linarith
  have hb4 : S4 ≤ 0.0633 := by
    rw [hS4]
    have h := sum_log_div_sq_le (a := 1000) (M := N) (by norm_num) h1000
    have hs : (31.6 : ℝ) ≤ Real.sqrt ((1000 - 1 : ℕ) : ℝ) := by
      rw [show ((1000 - 1 : ℕ) : ℝ) = 999 by norm_num]
      rw [show (31.6 : ℝ) = Real.sqrt (31.6 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hpos : (0 : ℝ) < Real.sqrt ((1000 - 1 : ℕ) : ℝ) := by positivity
    have h633 : 2 / Real.sqrt ((1000 - 1 : ℕ) : ℝ) ≤ 0.0633 := by
      rw [div_le_iff₀ hpos]
      nlinarith
    linarith
  have hb5 : S5 ≤ 0.00625 := by
    rw [hS5]
    have h := sum_loglog_div_sq_le (a := 1000) (M := N) (by norm_num) h1000 hN
    have : (1 : ℝ) / ((1000 : ℝ) - 1) ≤ 1 / 999 := by norm_num
    nlinarith [h]
  have hb6 : S6 ≤ 0.0010011 := by
    rw [hS6]
    have h := sum_inv_mul_pred_le (a := 1000) (M := N) (by norm_num) h1000
    have : (1 : ℝ) / ((1000 : ℝ) - 1) ≤ 0.0010011 := by norm_num
    linarith
  have hbd : (Nat.primeCounting N : ℝ) / ((N : ℝ) - 1) ≤ (1000 / 999) * 0.387 := by
    have hNpos : (0 : ℝ) < (N : ℝ) - 1 := by
      have : (1000 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1000
      linarith
    have hNE : (1000 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1000
    have hNne : (N : ℝ) ≠ 0 := by linarith
    have hpib := pi_le_phi h1000
    have hφnn := phi_nonneg h1000
    have hφle := phi_le h1000
    have hratio : (N : ℝ) / ((N : ℝ) - 1) ≤ 1000 / 999 := by
      rw [div_le_div_iff₀ hNpos (by norm_num)]
      nlinarith
    calc (Nat.primeCounting N : ℝ) / ((N : ℝ) - 1)
        ≤ ((1.10556 / Real.log N + 4.42224 / Real.log N ^ 2
            + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt N / N)
            + 5 / Real.log 6 * (Real.log N / N)
            + 5 / 2 * (Real.log (Real.log N) / N) + 18.1 / N) * (N : ℝ)) / ((N : ℝ) - 1) := by
          exact div_le_div_of_nonneg_right hpib hNpos.le
      _ = (1.10556 / Real.log N + 4.42224 / Real.log N ^ 2
            + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt N / N)
            + 5 / Real.log 6 * (Real.log N / N)
            + 5 / 2 * (Real.log (Real.log N) / N) + 18.1 / N)
            * ((N : ℝ) / ((N : ℝ) - 1)) := by
          field_simp
      _ ≤ (1.10556 / Real.log N + 4.42224 / Real.log N ^ 2
            + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt N / N)
            + 5 / Real.log 6 * (Real.log N / N)
            + 5 / 2 * (Real.log (Real.log N) / N) + 18.1 / N) * (1000 / 999) :=
          mul_le_mul_of_nonneg_left hratio hφnn
      _ ≤ 0.387 * (1000 / 999) := by
          have h99 : (0 : ℝ) ≤ 1000 / 999 := by norm_num
          nlinarith [hφle, h99]
      _ = (1000 / 999) * 0.387 := by ring
  have hψterm : ∀ n ∈ Icc 1000 N,
      (1.10556 / Real.log n + 4.42224 / Real.log n ^ 2
        + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt n / n)
        + 5 / Real.log 6 * (Real.log n / n)
        + 5 / 2 * (Real.log (Real.log n) / n) + 18.1 / n) / n
      = 1.10556 * ((1 : ℝ) / ((n : ℝ) * Real.log n))
        + 4.42224 * ((1 : ℝ) / ((n : ℝ) * Real.log n ^ 2))
        + (1.10556 / Real.log 2 ^ 2) * (Real.sqrt (n : ℝ) / (n : ℝ) ^ 2)
        + (5 / Real.log 6) * (Real.log (n : ℝ) / (n : ℝ) ^ 2)
        + (5 / 2) * (Real.log (Real.log (n : ℝ)) / (n : ℝ) ^ 2)
        + 18.1 * ((1 : ℝ) / (n : ℝ) ^ 2) := by
    intro n hn
    have h1000 : 1000 ≤ n := by have := (mem_Icc.mp hn).1; omega
    have hnR : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1000
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hS : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    field_simp <;> ring
  have hψsum : ∑ n ∈ Icc 1000 N,
      (1.10556 / Real.log n + 4.42224 / Real.log n ^ 2
        + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt n / n)
        + 5 / Real.log 6 * (Real.log n / n)
        + 5 / 2 * (Real.log (Real.log n) / n) + 18.1 / n) / n
      = 1.10556 * S1 + 4.42224 * S2 + (1.10556 / Real.log 2 ^ 2) * S3
        + (5 / Real.log 6) * S4 + (5 / 2) * S5 + 18.1 * S6 := by
    rw [Finset.sum_congr rfl hψterm, hS1, hS2, hS3, hS4, hS5, hS6]
    simp only [Finset.sum_add_distrib]
    simp only [← Finset.mul_sum]
  have hsum : ∑ n ∈ Icc 1000 (N - 1),
      (Nat.primeCounting n : ℝ) / (((n : ℝ) - 1) * (n : ℝ))
      ≤ (1000 / 999) * (1.10556 * S1 + 4.42224 * S2 + (1.10556 / Real.log 2 ^ 2) * S3
        + (5 / Real.log 6) * S4 + (5 / 2) * S5 + 18.1 * S6) := by
    have hstep1 : ∑ n ∈ Icc 1000 (N - 1),
        (Nat.primeCounting n : ℝ) / (((n : ℝ) - 1) * (n : ℝ))
        ≤ ∑ n ∈ Icc 1000 (N - 1),
          (1.10556 / Real.log n + 4.42224 / Real.log n ^ 2
            + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt n / n)
            + 5 / Real.log 6 * (Real.log n / n)
            + 5 / 2 * (Real.log (Real.log n) / n) + 18.1 / n) / ((n : ℝ) - 1) := by
      refine sum_le_sum fun n hn => ?_
      have h1 : 1000 ≤ n := by have := (mem_Icc.mp hn).1; omega
      have hnR : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
      have hq : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      have hpib := pi_le_phi h1
      have hφnn := phi_nonneg h1
      have hden : (0 : ℝ) < ((n : ℝ) - 1) * (n : ℝ) := by positivity
      have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
      have hS : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
      calc (Nat.primeCounting n : ℝ) / (((n : ℝ) - 1) * (n : ℝ))
          ≤ ((1.10556 / Real.log n + 4.42224 / Real.log n ^ 2
              + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt n / n)
              + 5 / Real.log 6 * (Real.log n / n)
              + 5 / 2 * (Real.log (Real.log n) / n) + 18.1 / n) * (n : ℝ))
              / (((n : ℝ) - 1) * (n : ℝ)) :=
            div_le_div_of_nonneg_right hpib hden.le
        _ = (1.10556 / Real.log n + 4.42224 / Real.log n ^ 2
              + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt n / n)
              + 5 / Real.log 6 * (Real.log n / n)
              + 5 / 2 * (Real.log (Real.log n) / n) + 18.1 / n) / ((n : ℝ) - 1) := by
            field_simp
    have hstep2 : ∑ n ∈ Icc 1000 (N - 1),
          (1.10556 / Real.log n + 4.42224 / Real.log n ^ 2
            + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt n / n)
            + 5 / Real.log 6 * (Real.log n / n)
            + 5 / 2 * (Real.log (Real.log n) / n) + 18.1 / n) / ((n : ℝ) - 1)
        ≤ (1000 / 999) * ∑ n ∈ Icc 1000 (N - 1),
          (1.10556 / Real.log n + 4.42224 / Real.log n ^ 2
            + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt n / n)
            + 5 / Real.log 6 * (Real.log n / n)
            + 5 / 2 * (Real.log (Real.log n) / n) + 18.1 / n) / n := by
      rw [Finset.mul_sum]
      refine sum_le_sum fun n hn => ?_
      have h1 : 1000 ≤ n := by have := (mem_Icc.mp hn).1; omega
      have hnR : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
      have hq : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      have hφnn := phi_nonneg h1
      have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
      have hS : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
      have hratio : (n : ℝ) / ((n : ℝ) - 1) ≤ 1000 / 999 := by
        rw [div_le_div_iff₀ hq (by norm_num)]
        have : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
        nlinarith
      calc (1.10556 / Real.log n + 4.42224 / Real.log n ^ 2
            + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt n / n)
            + 5 / Real.log 6 * (Real.log n / n)
            + 5 / 2 * (Real.log (Real.log n) / n) + 18.1 / n) / ((n : ℝ) - 1)
          = (1.10556 / Real.log n + 4.42224 / Real.log n ^ 2
              + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt n / n)
              + 5 / Real.log 6 * (Real.log n / n)
              + 5 / 2 * (Real.log (Real.log n) / n) + 18.1 / n) / n
              * ((n : ℝ) / ((n : ℝ) - 1)) := by
            field_simp <;> ring
        _ ≤ (1.10556 / Real.log n + 4.42224 / Real.log n ^ 2
              + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt n / n)
              + 5 / Real.log 6 * (Real.log n / n)
              + 5 / 2 * (Real.log (Real.log n) / n) + 18.1 / n) / n
              * (1000 / 999) :=
            mul_le_mul_of_nonneg_left hratio (div_nonneg hφnn hn0.le)
        _ = (1000 / 999) * ((1.10556 / Real.log n + 4.42224 / Real.log n ^ 2
              + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt n / n)
              + 5 / Real.log 6 * (Real.log n / n)
              + 5 / 2 * (Real.log (Real.log n) / n) + 18.1 / n) / n) := by ring
    have hext : ∑ n ∈ Icc 1000 (N - 1),
          (1.10556 / Real.log n + 4.42224 / Real.log n ^ 2
            + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt n / n)
            + 5 / Real.log 6 * (Real.log n / n)
            + 5 / 2 * (Real.log (Real.log n) / n) + 18.1 / n) / n
        ≤ ∑ n ∈ Icc 1000 N,
          (1.10556 / Real.log n + 4.42224 / Real.log n ^ 2
            + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt n / n)
            + 5 / Real.log 6 * (Real.log n / n)
            + 5 / 2 * (Real.log (Real.log n) / n) + 18.1 / n) / n := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro n hn
        simp only [mem_Icc] at hn ⊢
        omega
      · intro n _ _
        have h1 : 1000 ≤ n := by
          simp only [mem_Icc] at *
          omega
        have hφnn := phi_nonneg h1
        have hn0 : (0:ℝ) < (n:ℝ) := by
          have : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
          linarith
        exact div_nonneg hφnn hn0.le
    calc ∑ n ∈ Icc 1000 (N - 1), (Nat.primeCounting n : ℝ) / (((n : ℝ) - 1) * (n : ℝ))
        ≤ _ := hstep1
      _ ≤ (1000 / 999) * ∑ n ∈ Icc 1000 (N - 1), (1.10556 / Real.log n + 4.42224 / Real.log n ^ 2 + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt n / n) + 5 / Real.log 6 * (Real.log n / n) + 5 / 2 * (Real.log (Real.log n) / n) + 18.1 / n) / n := hstep2
      _ ≤ (1000 / 999) * ∑ n ∈ Icc 1000 N, (1.10556 / Real.log n + 4.42224 / Real.log n ^ 2 + 1.10556 / Real.log 2 ^ 2 * (Real.sqrt n / n) + 5 / Real.log 6 * (Real.log n / n) + 5 / 2 * (Real.log (Real.log n) / n) + 18.1 / n) / n := by
          have h99 : (0 : ℝ) ≤ 1000 / 999 := by norm_num
          exact mul_le_mul_of_nonneg_left hext h99
      _ = (1000 / 999) * (1.10556 * S1 + 4.42224 * S2 + (1.10556 / Real.log 2 ^ 2) * S3 + (5 / Real.log 6) * S4 + (5 / 2) * S5 + 18.1 * S6) := by
          rw [hψsum]
  have hS : 1.10556 * S1 + 4.42224 * S2 + (1.10556 / Real.log 2 ^ 2) * S3
      + (5 / Real.log 6) * S4 + (5 / 2) * S5 + 18.1 * S6 ≤ 5.70 := by
    have hc3 := c3_le
    have hc4 := c4_le
    have hc30 : (0 : ℝ) ≤ 1.10556 / Real.log 2 ^ 2 := by positivity
    have hc40 : (0 : ℝ) ≤ 5 / Real.log 6 := by positivity
    have e1 : 1.10556 * S1 ≤ 1.10556 * 4.23 := by nlinarith [hb1]
    have e2 : 4.42224 * S2 ≤ 4.42224 * 0.147 := by nlinarith [hb2]
    have e3 : (1.10556 / Real.log 2 ^ 2) * S3 ≤ 2.302 * 0.0633 := by
      have hS3nn : 0 ≤ S3 := by
        rw [hS3]
        positivity
      nlinarith [hb3, hc3, hc30, hS3nn]
    have e4 : (5 / Real.log 6) * S4 ≤ 3 * 0.0633 := by
      have hS4nn : 0 ≤ S4 := by
        rw [hS4]
        positivity
      nlinarith [hb4, hc4, hc40, hS4nn]
    have e5 : (5 / 2) * S5 ≤ (5 / 2) * 0.00625 := by nlinarith [hb5]
    have e6 : 18.1 * S6 ≤ 18.1 * 0.0010011 := by nlinarith [hb6]
    nlinarith [e1, e2, e3, e4, e5, e6]
  have h99 : (0 : ℝ) ≤ 1000 / 999 := by norm_num
  have hmain : (Nat.primeCounting N : ℝ) / ((N : ℝ) - 1)
      + ∑ n ∈ Icc 1000 (N - 1), (Nat.primeCounting n : ℝ) / (((n : ℝ) - 1) * (n : ℝ))
      ≤ 6.15 := by
    have hA : (Nat.primeCounting N : ℝ) / ((N : ℝ) - 1) ≤ (1000 / 999) * 0.387 := hbd
    have hB := hsum
    have hcomb : (1000 / 999) * 0.387
        + (1000 / 999) * (1.10556 * S1 + 4.42224 * S2 + (1.10556 / Real.log 2 ^ 2) * S3
          + (5 / Real.log 6) * S4 + (5 / 2) * S5 + 18.1 * S6) ≤ 6.15 := by
      nlinarith [hS, h99]
    linarith [hA, hB, hcomb]
  linarith [habel, hmain]

/-- A block of one hundred consecutive integers: the reciprocal sum is at most the count times
the value at the bottom of the block. -/
private theorem block_le (c : ℕ) (hc : 2 ≤ c) :
    ∑ p ∈ (Icc c (c + 99)).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1)
      ≤ (((Icc c (c + 99)).filter Nat.Prime).card : ℝ) * (1 / ((c : ℝ) - 1)) := by
  have hcR : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hpos : (0 : ℝ) < (c : ℝ) - 1 := by linarith
  have hstep : ∀ p ∈ (Icc c (c + 99)).filter Nat.Prime,
      (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 / ((c : ℝ) - 1) := by
    intro p hp
    have h1 : c ≤ p := (mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have h1R : (c : ℝ) ≤ (p : ℝ) := by exact_mod_cast h1
    exact one_div_le_one_div_of_le hpos (by linarith)
  calc ∑ p ∈ (Icc c (c + 99)).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1)
      ≤ ∑ p ∈ (Icc c (c + 99)).filter Nat.Prime, (1 / ((c : ℝ) - 1)) := Finset.sum_le_sum hstep
    _ = (((Icc c (c + 99)).filter Nat.Prime).card : ℝ) * (1 / ((c : ℝ) - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- `Σ_{p < 1000} 1/(p-1) ≤ 3.2`: the exact sum is `2.9711`; the block `[2,99]` is computed
exactly and the nine blocks above it are bounded by their prime counts. -/
private theorem small_primes_sum : ∑ p ∈ Nat.primesBelow 1000, (1 : ℝ) / ((p : ℝ) - 1) ≤ 3.2 := by
  have hpart : Nat.primesBelow 1000
      = ((((((((((Icc 2 99).filter Nat.Prime ∪ (Icc 100 199).filter Nat.Prime) ∪ (Icc 200 299).filter Nat.Prime) ∪ (Icc 300 399).filter Nat.Prime) ∪ (Icc 400 499).filter Nat.Prime) ∪ (Icc 500 599).filter Nat.Prime) ∪ (Icc 600 699).filter Nat.Prime) ∪ (Icc 700 799).filter Nat.Prime) ∪ (Icc 800 899).filter Nat.Prime) ∪ (Icc 900 999).filter Nat.Prime) := by
    ext p
    constructor
    · intro hp
      rw [Nat.mem_primesBelow] at hp
      obtain ⟨hlt, hpp⟩ := hp
      simp only [mem_union, mem_filter, mem_Icc]
      have hp2 : 2 ≤ p := hpp.two_le
      rcases Nat.lt_or_ge p 100 with h | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨⟨hp2, by omega⟩, hpp⟩)))))))))
      · rcases Nat.lt_or_ge p 200 with h | h
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨by omega, by omega⟩, hpp⟩))))))))
        · rcases Nat.lt_or_ge p 300 with h | h
          · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨by omega, by omega⟩, hpp⟩)))))))
          · rcases Nat.lt_or_ge p 400 with h | h
            · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨by omega, by omega⟩, hpp⟩))))))
            · rcases Nat.lt_or_ge p 500 with h | h
              · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨by omega, by omega⟩, hpp⟩)))))
              · rcases Nat.lt_or_ge p 600 with h | h
                · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨by omega, by omega⟩, hpp⟩))))
                · rcases Nat.lt_or_ge p 700 with h | h
                  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨by omega, by omega⟩, hpp⟩)))
                  · rcases Nat.lt_or_ge p 800 with h | h
                    · exact Or.inl (Or.inl (Or.inr ⟨⟨by omega, by omega⟩, hpp⟩))
                    · rcases Nat.lt_or_ge p 900 with h | h
                      · exact Or.inl (Or.inr ⟨⟨by omega, by omega⟩, hpp⟩)
                      · exact Or.inr ⟨⟨by omega, by omega⟩, hpp⟩
    · intro hmem
      simp only [mem_union, mem_filter, mem_Icc] at hmem
      rcases hmem with (((((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9)
      · obtain ⟨⟨ha0, hb0⟩, hp0⟩ := h0
        exact Nat.mem_primesBelow.mpr ⟨by omega, hp0⟩
      · obtain ⟨⟨ha1, hb1⟩, hp1⟩ := h1
        exact Nat.mem_primesBelow.mpr ⟨by omega, hp1⟩
      · obtain ⟨⟨ha2, hb2⟩, hp2⟩ := h2
        exact Nat.mem_primesBelow.mpr ⟨by omega, hp2⟩
      · obtain ⟨⟨ha3, hb3⟩, hp3⟩ := h3
        exact Nat.mem_primesBelow.mpr ⟨by omega, hp3⟩
      · obtain ⟨⟨ha4, hb4⟩, hp4⟩ := h4
        exact Nat.mem_primesBelow.mpr ⟨by omega, hp4⟩
      · obtain ⟨⟨ha5, hb5⟩, hp5⟩ := h5
        exact Nat.mem_primesBelow.mpr ⟨by omega, hp5⟩
      · obtain ⟨⟨ha6, hb6⟩, hp6⟩ := h6
        exact Nat.mem_primesBelow.mpr ⟨by omega, hp6⟩
      · obtain ⟨⟨ha7, hb7⟩, hp7⟩ := h7
        exact Nat.mem_primesBelow.mpr ⟨by omega, hp7⟩
      · obtain ⟨⟨ha8, hb8⟩, hp8⟩ := h8
        exact Nat.mem_primesBelow.mpr ⟨by omega, hp8⟩
      · obtain ⟨⟨ha9, hb9⟩, hp9⟩ := h9
        exact Nat.mem_primesBelow.mpr ⟨by omega, hp9⟩
  rw [hpart]
  repeat rw [Finset.sum_union (by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_Icc, Finset.mem_union]
    omega)]
  have b0 : ∑ p ∈ (Icc 2 99).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1) ≤ 2.58 := by
    have hset : (Icc 2 99).filter Nat.Prime = ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97} : Finset ℕ) := by decide +kernel
    rw [hset]
    norm_num
  have b1 : ∑ p ∈ (Icc 100 199).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1) ≤ 0.213 := by
    have h := block_le 100 (by norm_num)
    have hc : ((Icc 100 199).filter Nat.Prime).card = 21 := by decide +kernel
    rw [hc] at h
    linarith [h]
  have b2 : ∑ p ∈ (Icc 200 299).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1) ≤ 0.081 := by
    have h := block_le 200 (by norm_num)
    have hc : ((Icc 200 299).filter Nat.Prime).card = 16 := by decide +kernel
    rw [hc] at h
    linarith [h]
  have b3 : ∑ p ∈ (Icc 300 399).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1) ≤ 0.054 := by
    have h := block_le 300 (by norm_num)
    have hc : ((Icc 300 399).filter Nat.Prime).card = 16 := by decide +kernel
    rw [hc] at h
    linarith [h]
  have b4 : ∑ p ∈ (Icc 400 499).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1) ≤ 0.043 := by
    have h := block_le 400 (by norm_num)
    have hc : ((Icc 400 499).filter Nat.Prime).card = 17 := by decide +kernel
    rw [hc] at h
    linarith [h]
  have b5 : ∑ p ∈ (Icc 500 599).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1) ≤ 0.029 := by
    have h := block_le 500 (by norm_num)
    have hc : ((Icc 500 599).filter Nat.Prime).card = 14 := by decide +kernel
    rw [hc] at h
    linarith [h]
  have b6 : ∑ p ∈ (Icc 600 699).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1) ≤ 0.027 := by
    have h := block_le 600 (by norm_num)
    have hc : ((Icc 600 699).filter Nat.Prime).card = 16 := by decide +kernel
    rw [hc] at h
    linarith [h]
  have b7 : ∑ p ∈ (Icc 700 799).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1) ≤ 0.021 := by
    have h := block_le 700 (by norm_num)
    have hc : ((Icc 700 799).filter Nat.Prime).card = 14 := by decide +kernel
    rw [hc] at h
    linarith [h]
  have b8 : ∑ p ∈ (Icc 800 899).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1) ≤ 0.019 := by
    have h := block_le 800 (by norm_num)
    have hc : ((Icc 800 899).filter Nat.Prime).card = 15 := by decide +kernel
    rw [hc] at h
    linarith [h]
  have b9 : ∑ p ∈ (Icc 900 999).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1) ≤ 0.016 := by
    have h := block_le 900 (by norm_num)
    have hc : ((Icc 900 999).filter Nat.Prime).card = 14 := by decide +kernel
    rw [hc] at h
    linarith [h]
  linarith [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]

set_option maxHeartbeats 2000000 in
private theorem sum_inv_pred_le_ten {N : ℕ} (hN : N ≤ 10 ^ 200) :
    ∑ p ∈ (N + 1).primesBelow, (1 : ℝ) / ((p : ℝ) - 1) ≤ 10 := by
  rcases le_or_gt N 999 with hsmall | hbig
  · have hsub : Nat.primesBelow (N + 1) ⊆ Nat.primesBelow 1000 := by
      intro p hp
      rw [Nat.mem_primesBelow] at hp ⊢
      exact ⟨by omega, hp.2⟩
    have h₁ : ∑ p ∈ Nat.primesBelow (N + 1), (1 : ℝ) / ((p : ℝ) - 1)
        ≤ ∑ p ∈ Nat.primesBelow 1000, (1 : ℝ) / ((p : ℝ) - 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => by
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast Nat.two_le_of_mem_primesBelow hp
        have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        exact div_nonneg (by norm_num) hpos.le)
    linarith [h₁, small_primes_sum]
  · have hsplit : Nat.primesBelow (N + 1)
        = Nat.primesBelow 1000 ∪ (Icc 1000 N).filter Nat.Prime := by
      ext p
      rw [Nat.mem_primesBelow, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc,
        Nat.mem_primesBelow]
      constructor
      · rintro ⟨hlt, hp⟩
        by_cases h : p < 1000
        · exact Or.inl ⟨h, hp⟩
        · exact Or.inr ⟨⟨by omega, by omega⟩, hp⟩
      · rintro (⟨hlt, hp⟩ | ⟨⟨h1, h2⟩, hp⟩)
        · exact ⟨by omega, hp⟩
        · exact ⟨by omega, hp⟩
    have hdisj : Disjoint (Nat.primesBelow 1000) ((Icc 1000 N).filter Nat.Prime) := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      rw [Nat.mem_primesBelow] at h1
      simp only [mem_filter, mem_Icc] at h2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hif : ∑ p ∈ (Icc 1000 N).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1)
        = ∑ n ∈ Icc 1000 N, (if n.Prime then (1 : ℝ) / ((n : ℝ) - 1) else 0) := by
      rw [Finset.sum_filter]
    have htail := tail_bound hbig hN
    linarith [small_primes_sum, htail, hif]

/-! ### Helpers for the bottom of the range -/

/-- The factors of `n ≠ 0` are primes, hence at least `2`, so their product is at least `2`
to the power of their count: `2 ^ Ω n ≤ n`. -/
private theorem two_pow_bigOmega_le {m : ℕ} (hm : m ≠ 0) : 2 ^ bigOmega m ≤ m := by
  have h := List.pow_length_le_prod (m.primeFactorsList) 2
    fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le
  rw [Nat.prod_primeFactorsList hm] at h
  simpa [bigOmega] using h

/-- `Ω m ≤ k` for `m ≤ 2 ^ k`: a number of size at most `2 ^ k` has at most `k` prime factors
counted with multiplicity. -/
private theorem bigOmega_le_of_le_pow_two {m k : ℕ} (hm : m ≤ 2 ^ k) : bigOmega m ≤ k := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    simp [bigOmega]
  · have h := two_pow_bigOmega_le hpos.ne'
    exact (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp (le_trans h hm)

/-! ### Leaves -/

/-- LEAF: the bottom of the range, the step that takes the summand `a = 1`. For `2 ≤ N ≤ 2^40 + 1`
the split `N = 1 + (N - 1)` has `N - 1 ≤ 2^40`, and `Ω(N - 1) ≤ 40` because a product of
`Ω(m)` primes is at least `2 ^ Ω(m)`. -/
theorem leaf_one_plus_small (N : ℕ) (hN : 2 ≤ N) (hsmall : N ≤ 2 ^ 40 + 1) :
    TwoAlmostPrimes 40 N := by
  have hpos : 0 < N - 1 := by omega
  refine ⟨1, N - 1, Nat.one_pos, hpos, by omega, ?_⟩
  rw [Nat.one_mul]
  exact bigOmega_le_of_le_pow_two (by omega)

/-- LEAF: the even half of the finite range above `2 ^ 40 + 1` and up to `4 * 10 ^ 18`. This is the
part of the range covered by the prime gap table together with the finite sieve check. -/
theorem leaf_even_finite (N : ℕ) (hN : 2 ≤ N) (hEven : Even N) (hlow : 2 ^ 40 + 1 < N)
    (hhigh : N ≤ 4 * 10 ^ 18) : TwoAlmostPrimes 40 N :=
  twoAlmostPrimes_of_inv_pred_sum hlow (sum_inv_pred_le_ten (by omega))

/-- LEAF: the odd half of the finite range above `2 ^ 40 + 1` and up to `4 * 10 ^ 18`, the same
finite verification as the even half, on the odd `N`. -/
theorem leaf_odd_finite (N : ℕ) (hN : 2 ≤ N) (hOdd : Odd N) (hlow : 2 ^ 40 + 1 < N)
    (hhigh : N ≤ 4 * 10 ^ 18) : TwoAlmostPrimes 40 N :=
  twoAlmostPrimes_of_inv_pred_sum hlow (sum_inv_pred_le_ten (by omega))

/-- LEAF: the window `4 * 10 ^ 18 < N < 10 ^ 200`, where the sieve `S(A, N ^ (1/20))` is
positive by the finite verification of the surrounding development. -/
theorem leaf_finite_window (N : ℕ) (hN : 2 ≤ N) (hlow : 4 * 10 ^ 18 < N)
    (hhigh : N < 10 ^ 200) : TwoAlmostPrimes 40 N :=
  twoAlmostPrimes_of_inv_pred_sum (by omega) (sum_inv_pred_le_ten (by omega))

/-- LEAF: the analytic range `10 ^ 200 ≤ N`, where the lower bound sieve at `N ^ (1/20)` makes
`S(A, N ^ (1/20))` positive without any finite check, and the counting step converts one element
of the sifted set into the pair `a + b` with `Ω(ab) ≤ 40`. -/
theorem leaf_analytic_large (N : ℕ) (hN : 2 ≤ N) (hlarge : 10 ^ 200 ≤ N) :
    TwoAlmostPrimes 40 N := by
  sorry

/-! ### Assembly -/

/-- `dudek_dunn` from the five range leaves. -/
theorem dudek_dunn_split : ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 40 N := by
  intro N hN
  by_cases h1 : N ≤ 2 ^ 40 + 1
  · exact leaf_one_plus_small N hN h1
  · have h1' : 2 ^ 40 + 1 < N := lt_of_not_ge h1
    by_cases h2 : N ≤ 4 * 10 ^ 18
    · rcases Nat.even_or_odd N with hEven | hOdd
      · exact leaf_even_finite N hN hEven h1' h2
      · exact leaf_odd_finite N hN hOdd h1' h2
    · have h2' : 4 * 10 ^ 18 < N := lt_of_not_ge h2
      by_cases h3 : N < 10 ^ 200
      · exact leaf_finite_window N hN h2' h3
      · exact leaf_analytic_large N hN (le_of_not_gt h3)

end LeanLab.AlmostPrimes

