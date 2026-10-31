/-
# R-0050 T2 salvage: rough weighted shift Chowla at shift N, as a named Prop

Unit U-1499, PC run 20261022T2003Z-18. AI wrote this Lean code.
Binary Goldbach is OPEN. Nothing here is progress on it; this is a ROUTE, and every
Goldbach conclusion below is CONDITIONAL ON a named, unproved Prop.

Setup, plain math. Fix `N`. Call `n` rough when `1 < n` and every prime factor `p` of `n`
has `p^3 > N`, the `R0007.Rough` predicate. Put
* `w(n) = 1` if `n` is rough, else `0`; `λ(n) = (-1)^Ω(n)`;
* `g = w λ`, the rough weighted Liouville function, `g 0 = 0`;
* `ρ = w (1 - λ)/2`, which on `n ≤ N` is the indicator of primes `p > N^{1/3}`;
* `σ = w (1 + λ)/2`, which on `n ≤ N` is the indicator of `pq` with `p, q > N^{1/3}`;
* `W2 = Σ_{a ≤ N} w(a) w(N-a)`, `X = Σ_{a ≤ N} g(a) w(N-a)`, `T = Σ_{a ≤ N} g(a) g(N-a)`,
  `r = Σ_{a ≤ N} ρ(a) ρ(N-a)`, `s = Σ_{a ≤ N} σ(a) σ(N-a)`.

PROVED here, unconditional:
* `four_refl_rho`: `4 r = W2 - 2 X + T`, the R-0007 rough identity, for any weights.
* `refl_rho_sub_sigma`: `r - s = -X`; so `X < 0` alone forces `r > 0`.
* `lb_iff`: the named Prop `ReflChowlaLB N x` holds iff `r > 0`; so it is the weakest
  correlation hypothesis that works through `sym_corr_split`, and it is exactly as hard as
  Goldbach for `N` with both primes above `N^{1/3}`.
* `shift_of_cross_neg`: `X < 0` implies the strict two-sided form `ShiftChowla N x`.
CONDITIONAL:
* `goldbach_of_reflChowla`, CONDITIONAL ON `ReflChowlaLB N x`.
* `goldbach_of_shiftChowla`, CONDITIONAL ON `ShiftChowla N x`.
* `goldbach_large_of_unif`, CONDITIONAL ON `UnifShiftChowla`.
Vacuity: `ReflChowlaLB 10 x` holds for every `x`, and `ShiftChowla 10 x` holds, via `X = -3`.
-/
import Mathlib
import LeanLab.Routes.U1491SymShift
import LeanLab.Routes.R0007RoughParity

namespace LeanLab.Routes.U1499

open Finset
open LeanLab.Routes.U1491

/-- Liouville `λ(n) = (-1)^Ω(n)`, with `λ 0 = λ 1 = 1`. -/
noncomputable def liou (n : ℕ) : ℝ := (-1 : ℝ) ^ n.primeFactorsList.length

open Classical in
/-- rough weight: `1 < n` and every prime factor `p` of `n` has `N < p^3`. -/
noncomputable def wt (N n : ℕ) : ℝ := if 1 < n ∧ R0007.Rough N n then 1 else 0

/-- rough weighted Liouville `g = w λ`. -/
noncomputable def gw (N n : ℕ) : ℝ := wt N n * liou n
/-- rough prime indicator `ρ = w (1 - λ) / 2`. -/
noncomputable def rho (N n : ℕ) : ℝ := wt N n * (1 - liou n) / 2
/-- rough semiprime indicator `σ = w (1 + λ) / 2`. -/
noncomputable def sigma (N n : ℕ) : ℝ := wt N n * (1 + liou n) / 2

/-- the one-point cross term `X(N) = Σ_{a ≤ N} g(a) w(N - a)`. -/
noncomputable def cross (N : ℕ) : ℝ := ∑ a ∈ range (N + 1), gw N a * wt N (N - a)

lemma liou_cases (n : ℕ) : liou n = 1 ∨ liou n = -1 := by
  unfold liou
  rcases Nat.even_or_odd n.primeFactorsList.length with h | h
  · left; exact h.neg_one_pow
  · right; exact h.neg_one_pow

lemma wt_cases (N n : ℕ) : wt N n = 0 ∨ wt N n = 1 := by
  unfold wt; split_ifs <;> simp

lemma wt_zero (N : ℕ) : wt N 0 = 0 := by simp [wt]

lemma gw_zero (N : ℕ) : gw N 0 = 0 := by simp [gw, wt_zero]

lemma rho_nonneg (N n : ℕ) : 0 ≤ rho N n := by
  unfold rho
  rcases wt_cases N n with h | h <;> rcases liou_cases n with h' | h' <;> rw [h, h'] <;> norm_num

lemma sigma_nonneg (N n : ℕ) : 0 ≤ sigma N n := by
  unfold sigma
  rcases wt_cases N n with h | h <;> rcases liou_cases n with h' | h' <;> rw [h, h'] <;> norm_num

lemma abs_gw (N n : ℕ) : |gw N n| = wt N n := by
  unfold gw
  rcases wt_cases N n with h | h <;> rcases liou_cases n with h' | h' <;> rw [h, h'] <;> norm_num

lemma cross_symm (N : ℕ) : cross N = ∑ a ∈ range (N + 1), wt N a * gw N (N - a) := by
  unfold cross
  rw [← sum_range_reflect (fun a => wt N a * gw N (N - a)) (N + 1)]
  refine sum_congr rfl (fun a ha => ?_)
  rw [mem_range] at ha
  have e1 : N + 1 - 1 - a = N - a := by omega
  have e2 : N - (N - a) = a := by omega
  simp only [e1, e2]
  ring

/-- **R-0007 rough identity**: `4 r = W2 - 2 X + T`. PROVED. -/
theorem four_refl_rho (N : ℕ) :
    4 * refl (rho N) N = refl (wt N) N - 2 * cross N + refl (gw N) N := by
  have h : ∀ a ∈ range (N + 1), 4 * (rho N a * rho N (N - a))
      = wt N a * wt N (N - a) - gw N a * wt N (N - a) - wt N a * gw N (N - a)
        + gw N a * gw N (N - a) := by
    intro a _; simp only [rho, gw]; ring
  have hc := cross_symm N
  unfold U1491.refl
  rw [mul_sum, sum_congr rfl h, sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← hc]
  unfold cross
  ring

/-- the semiprime twin: `4 s = W2 + 2 X + T`. PROVED. -/
theorem four_refl_sigma (N : ℕ) :
    4 * refl (sigma N) N = refl (wt N) N + 2 * cross N + refl (gw N) N := by
  have h : ∀ a ∈ range (N + 1), 4 * (sigma N a * sigma N (N - a))
      = wt N a * wt N (N - a) + gw N a * wt N (N - a) + wt N a * gw N (N - a)
        + gw N a * gw N (N - a) := by
    intro a _; simp only [sigma, gw]; ring
  have hc := cross_symm N
  unfold U1491.refl
  rw [mul_sum, sum_congr rfl h, sum_add_distrib, sum_add_distrib, sum_add_distrib, ← hc]
  unfold cross
  ring

/-- `r - s = -X`: prime pairs minus rough semiprime pairs is minus the one-point term. PROVED. -/
theorem refl_rho_sub_sigma (N : ℕ) : refl (rho N) N - refl (sigma N) N = -cross N := by
  have h1 := four_refl_rho N
  have h2 := four_refl_sigma N
  linarith

theorem refl_sigma_nonneg (N : ℕ) : 0 ≤ refl (sigma N) N :=
  sum_nonneg (fun a _ => mul_nonneg (sigma_nonneg N a) (sigma_nonneg N _))

/-- on `a ≤ N`, `ρ(a) ≠ 0` forces `a` prime, via `R0007.prime_iff_odd_card`. PROVED. -/
theorem prime_of_rho_ne {N a : ℕ} (haN : a ≤ N) (h : rho N a ≠ 0) : a.Prime := by
  unfold rho wt at h
  split_ifs at h with hw
  · have hl : liou a ≠ 1 := by intro e; rw [e] at h; simp at h
    have hodd : Odd a.primeFactorsList.length := by
      rcases Nat.even_or_odd a.primeFactorsList.length with he | ho
      · exact absurd he.neg_one_pow hl
      · exact ho
    exact (R0007.prime_iff_odd_card hw.1 haN hw.2).mpr hodd
  · simp at h

/-- `r > 0` gives a Goldbach representation of `N`. PROVED. -/
theorem goldbach_of_refl_pos {N : ℕ} (h : 0 < refl (rho N) N) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N := by
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt h)
  rw [mem_range] at ha
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hne
  exact ⟨a, N - a, prime_of_rho_ne (by omega) h1, prime_of_rho_ne (by omega) h2, by omega⟩

/-! ## The named hypotheses -/

/-- **Weakest form.** The shift-`N` correlation of the even extension of `g` over the window
`-N - x < n < x` beats twice the forward correlation by more than `2 X - W2`:
`S_x(N) > 2 D_x(N) + 2 X - W2`. -/
def ReflChowlaLB (N x : ℕ) : Prop :=
  2 * fwd (gw N) N x + (2 * cross N - refl (wt N) N) < symCorr (gw N) N x

/-- **Two-sided Chowla form at a single shift.** `|S_x(N) - 2 D_x(N)| < W2 - 2 X`. -/
def ShiftChowla (N x : ℕ) : Prop :=
  |symCorr (gw N) N x - 2 * fwd (gw N) N x| < refl (wt N) N - 2 * cross N

/-- **Uniform form**, window `x = N`, every large even `N`. -/
def UnifShiftChowla : Prop := ∃ N₀ : ℕ, ∀ N ≥ N₀, Even N → ShiftChowla N N

/-- `ReflChowlaLB N x ↔ r > 0`: the weakest form is exactly the positive rough count.
PROVED, through `sym_corr_split` and `four_refl_rho`. -/
theorem lb_iff (N x : ℕ) : ReflChowlaLB N x ↔ 0 < refl (rho N) N := by
  unfold ReflChowlaLB
  rw [sym_corr_split _ (gw_zero N)]
  have h4 := four_refl_rho N
  constructor <;> intro h <;> linarith

theorem lb_of_shift {N x : ℕ} (h : ShiftChowla N x) : ReflChowlaLB N x := by
  unfold ShiftChowla at h; unfold ReflChowlaLB
  have := (abs_lt.mp h).1
  linarith

/-- CONDITIONAL ON `ReflChowlaLB N x`. -/
theorem goldbach_of_reflChowla {N x : ℕ} (h : ReflChowlaLB N x) :
    0 < refl (rho N) N ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N :=
  ⟨(lb_iff N x).mp h, goldbach_of_refl_pos ((lb_iff N x).mp h)⟩

/-- CONDITIONAL ON `ShiftChowla N x`. -/
theorem goldbach_of_shiftChowla {N x : ℕ} (h : ShiftChowla N x) :
    0 < refl (rho N) N ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N :=
  goldbach_of_reflChowla (lb_of_shift h)

/-- CONDITIONAL ON `UnifShiftChowla`: every large even `N` is a sum of two primes. -/
theorem goldbach_large_of_unif (h : UnifShiftChowla) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, Even N → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N := by
  obtain ⟨N₀, hN⟩ := h
  exact ⟨N₀, fun N hN0 he => (goldbach_of_shiftChowla (hN N hN0 he)).2⟩

/-! ## The one-point input implies the correlation input -/

/-- trivial bound `|T| ≤ W2`. PROVED. -/
theorem abs_refl_gw_le (N : ℕ) : |refl (gw N) N| ≤ refl (wt N) N := by
  unfold U1491.refl
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl (fun a _ => ?_)))
  rw [abs_mul, abs_gw, abs_gw]

/-- `X < 0` implies `ShiftChowla N x` for every window `x`. PROVED. -/
theorem shift_of_cross_neg {N : ℕ} (hX : cross N < 0) (x : ℕ) : ShiftChowla N x := by
  unfold ShiftChowla
  rw [sym_corr_split _ (gw_zero N), add_sub_cancel_right]
  have := abs_refl_gw_le N
  linarith

/-- `r ≥ -X`. PROVED. -/
theorem neg_cross_le_refl_rho (N : ℕ) : -cross N ≤ refl (rho N) N := by
  have h1 := refl_rho_sub_sigma N
  have h2 := refl_sigma_nonneg N
  linarith

/-! ## Vacuity at `N = 10` -/

lemma liou_prime {p : ℕ} (hp : p.Prime) : liou p = -1 := by
  simp [liou, Nat.primeFactorsList_prime hp]

lemma wt_prime {N p : ℕ} (hp : p.Prime) (h : N < p ^ 3) : wt N p = 1 := by
  unfold wt; rw [if_pos ⟨hp.one_lt, R0007.rough_of_prime hp h⟩]

lemma wt_even {N n : ℕ} (hn : 2 ∣ n) (hN : 8 ≤ N) : wt N n = 0 := by
  unfold wt
  rw [if_neg]
  rintro ⟨h1, hr⟩
  have hm : 2 ∈ n.primeFactorsList :=
    (Nat.mem_primeFactorsList_iff_dvd (by omega) Nat.prime_two).mpr hn
  have := hr 2 hm
  norm_num at this; omega

lemma wt_one (N : ℕ) : wt N 1 = 0 := by simp [wt]

example (x : ℕ) : ReflChowlaLB 10 x := by
  rw [lb_iff]
  have h3 : rho 10 3 = 1 := by
    simp only [rho, wt_prime (N := 10) Nat.prime_three (by norm_num), liou_prime Nat.prime_three]; norm_num
  have h7 : rho 10 7 = 1 := by
    simp only [rho, wt_prime (N := 10) (by norm_num : Nat.Prime 7) (by norm_num),
      liou_prime (by norm_num : Nat.Prime 7)]; norm_num
  have hle : rho 10 3 * rho 10 (10 - 3) ≤ refl (rho 10) 10 :=
    single_le_sum (f := fun a => rho 10 a * rho 10 (10 - a))
      (fun a _ => mul_nonneg (rho_nonneg _ _) (rho_nonneg _ _)) (by simp)
  have e : (10 : ℕ) - 3 = 7 := rfl
  rw [e, h3, h7] at hle
  linarith

/-- `X(10) = -3`: the pairs `(3,7), (5,5), (7,3)`; `9 + 1` drops since `w 1 = 0`. -/
theorem cross_ten : cross 10 = -3 := by
  have w2 := wt_even (N := 10) (n := 2) (by norm_num) (by norm_num)
  have w4 := wt_even (N := 10) (n := 4) (by norm_num) (by norm_num)
  have w6 := wt_even (N := 10) (n := 6) (by norm_num) (by norm_num)
  have w8 := wt_even (N := 10) (n := 8) (by norm_num) (by norm_num)
  have w10 := wt_even (N := 10) (n := 10) (by norm_num) (by norm_num)
  have w3 := wt_prime (N := 10) Nat.prime_three (by norm_num)
  have w5 := wt_prime (N := 10) Nat.prime_five (by norm_num)
  have w7 := wt_prime (N := 10) (p := 7) (by norm_num) (by norm_num)
  have l3 := liou_prime Nat.prime_three
  have l5 := liou_prime Nat.prime_five
  have l7 := liou_prime (p := 7) (by norm_num)
  simp only [cross, gw, sum_range_succ, sum_range_zero]
  norm_num [w2, w4, w6, w8, w10, w3, w5, w7, l3, l5, l7, wt_zero, wt_one]

example (x : ℕ) : ShiftChowla 10 x := shift_of_cross_neg (by rw [cross_ten]; norm_num) x

end LeanLab.Routes.U1499
