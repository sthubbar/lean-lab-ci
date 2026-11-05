import LeanLab.BakerHarmanPintz1997.Decomp90

namespace LeanLab.BakerHarmanPintz1997.DecompJ883
open Finset Real Decomp90
attribute [local instance] Classical.propDecidable

open MeasureTheory intervalIntegral

/-! ============================================================================
## Second session (`W883b`, OMOS lomos 20261104T1214Z): verified reduction of
## `fgm_discretization_error` to a Bernoulli--Fourier estimate

This is spliced into the lab file: `fgm_discretization_error` is closed below with the explicit
constant `500` (`disc_bound`), from purely Mathlib material. Everything in this block compiles
with no `sorry`, including under the lab's `autoImplicit = false`.

* `em1_interval` — first-order Euler–Maclaurin on one unit interval (trapezoid form);
* `em2_interval` — one further integration by parts: centred sawtooth against `f'` becomes
  the polynomial `u²-u+1/6` against `f''`;
* `B2_fract_eq_poly`, `intervalIntegrable_B2_fract` — the periodic `B₂ = bernoulliFun 2 (fract ·)`
  agrees with that polynomial a.e. on each unit interval;
* `sum_Ico_endpoint`, `sum_Ico_shift_r`, `sum_Ico_telescope`, `sum_integral_units`;
* **`em2_block`** — second-order Euler–Maclaurin over a block of unit intervals:
  `∑_{Ioc K K1} f = ∫_K^{K1} f + ½(f K1 - f K) + (1/12)(f' K1 - f' K) - ½∫_K^{K1} B₂({y}) f''(y) dy`;
* **`osc_integral_bound`** — the first-derivative (oscillation) test
  `‖∫_a^b y^{-5/2} e^{i(μy + t log y)}‖ ≤ 10 a^{-5/2}` for `5 ≤ |μ|`, `|t| ≤ 2a`, `b ≤ 4a`
  (one integration by parts with `1/(iφ')`, `φ' = μ + t/y ≥ 3`);
* **`B2_fourier_tsum`** — Mathlib's absolutely convergent Bernoulli–Fourier series
  (`hasSum_one_div_pow_mul_fourier_mul_bernoulliFun`, `k = 2`) restated at an arbitrary real point:
  `∑' n, n^{-2} e^{2πiny} = 2π² B₂({y})`;
* **`integral_B2_fourier`** — term-by-term integration against `f''` (via
  `intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm`, with the family cut off below `a` so
  that it is continuous on all of `ℝ`).

Third session (`W883c`, OMOS lomos 20261105T0944Z) — the numerical assembly that closes the
leaf: `mode_bound` (per-mode bound from `osc_integral_bound`),
`int_tsum_inv_sq_le_four` (`∑'_{n:ℤ} n^{-2} ≤ 4` from `hasSum_zeta_two`), `bern_integral_bound`,
the boundary difference from closed forms (`integral_cpow` + fundamental theorem, so no
interval-additivity rewriting is needed), and `disc_bound`, which is the leaf itself with
`C_disc = 500`. Each of the four carries `t` as an explicit binder: the lab lakefile sets
`autoImplicit = false`, so an auto-bound `t` in `c.im = -t` is an error under `lake build`
though not under `lake env lean`.
-/

open Finset Real MeasureTheory intervalIntegral


/-! ## 1. The power `y ↦ (y:ℂ)^c` on the positive axis -/

private lemma hasDerivAt_cpow_c (c : ℂ) (hc : c ≠ 0) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ c) (c * (y : ℂ) ^ (c - 1)) y :=
  hasDerivAt_ofReal_cpow_const hy.ne' hc

private lemma continuousOn_cpow (c : ℂ) (hc : c ≠ 0) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun y : ℝ => (y : ℂ) ^ c) (Set.uIcc a b) := by
  intro y hy
  rw [Set.uIcc_of_le hab] at hy
  exact (hasDerivAt_cpow_c c hc (lt_of_lt_of_le ha hy.1)).continuousAt.continuousWithinAt

private lemma intervalIntegrable_cpow (c : ℂ) (hc : c ≠ 0) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun y : ℝ => (y : ℂ) ^ c) volume a b :=
  (continuousOn_cpow c hc ha hab).intervalIntegrable

private lemma norm_cpow_eq {c : ℂ} {y : ℝ} (hy : 0 < y) : ‖(y : ℂ) ^ c‖ = y ^ c.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hy c

/-! ## 2. Combinatorics of `Ico` versus `Ioc` sums -/

private lemma sum_Ico_endpoint (f : ℕ → ℂ) (a : ℕ) :
    ∀ b, a ≤ b → ∑ n ∈ Finset.Ico a b, f n + f b = ∑ n ∈ Finset.Ioc a b, f n + f a := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ico_succ_top hb, Finset.sum_Ioc_succ_top hb]
    linear_combination ih

private lemma sum_Ico_shift (f : ℕ → ℂ) (a : ℕ) :
    ∀ b, a ≤ b → ∑ n ∈ Finset.Ico a b, f (n + 1) = ∑ n ∈ Finset.Ioc a b, f n := by
  intro b hab
  rw [Finset.sum_Ico_add' f a b 1]
  congr 1
  ext k
  simp only [Finset.mem_Ico, Finset.mem_Ioc]
  omega

private lemma sum_Ico_telescope (g : ℕ → ℂ) (a : ℕ) :
    ∀ b, a ≤ b → ∑ n ∈ Finset.Ico a b, (g (n + 1) - g n) = g b - g a := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ico_succ_top hb, ih]
    ring

/-! ## 3. Per-interval Euler–Maclaurin (symmetric form) -/

private lemma hasDerivAt_local_weight (n : ℕ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => ((y - n - 1 / 2 : ℝ) : ℂ)) 1 y := by
  have h1 : HasDerivAt (fun y : ℝ => y - n - 1 / 2 : ℝ → ℝ) 1 y := by
    simpa using ((hasDerivAt_id y).sub_const (n : ℝ)).sub_const (1 / 2)
  simpa using h1.ofReal_comp

/-- First-order Euler–Maclaurin on one unit interval, in trapezoid form. -/
private lemma em1_interval (f f' : ℝ → ℂ) (n : ℕ)
    (hderiv : ∀ y ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1), HasDerivAt f (f' y) y)
    (hint : IntervalIntegrable f' volume (n : ℝ) ((n : ℝ) + 1)) :
    ∫ y in (n : ℝ)..((n : ℝ) + 1), ((y - n - 1 / 2 : ℝ) : ℂ) * f' y =
      (f (n : ℝ) + f ((n : ℝ) + 1)) / 2 - ∫ y in (n : ℝ)..((n : ℝ) + 1), f y := by
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun y : ℝ => ((y - n - 1 / 2 : ℝ) : ℂ)) (v := f) (u' := fun _ => (1 : ℂ)) (v' := f')
    (fun y _ => hasDerivAt_local_weight n y) hderiv intervalIntegrable_const hint
  have h1 : ((n : ℝ) + 1 - n - 1 / 2 : ℝ) = 1 / 2 := by ring
  have h2 : ((n : ℝ) - n - 1 / 2 : ℝ) = -(1 / 2) := by ring
  simp only [h1, h2, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_neg, one_mul] at hb
  rw [hb]
  simp only [one_div]
  push_cast
  ring

/-! ## 4. The Bernoulli function `B₂` -/

private lemma bernoulliFun_two_eq (x : ℝ) :
    bernoulliFun 2 x = x ^ 2 - x + 1 / 6 := by
  rw [bernoulliFun_two]
  norm_num

private lemma hasDerivAt_bernoulliFun_two (y : ℝ) :
    HasDerivAt (fun y : ℝ => bernoulliFun 2 y) (2 * y - 1) y := by
  have h := hasDerivAt_bernoulliFun 2 y
  have h2 : ((2 : ℕ) : ℝ) * bernoulliFun (2 - 1) y = 2 * y - 1 := by
    rw [show (2 - 1 : ℕ) = 1 from rfl, bernoulliFun_one]
    push_cast
    ring
  rw [h2] at h
  exact h



/-! ## The `saw`-to-`B₂` step on one unit interval, with the explicit polynomial weight -/

private lemma hasDerivAt_B2_poly (n : ℕ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => ((y - n) ^ 2 - (y - n) + 1 / 6 : ℝ)) (((2 : ℝ) * (y - n) - 1 : ℝ)) y := by
  have h1 : HasDerivAt (fun y : ℝ => y - (n : ℝ)) 1 y := by
    simpa using (hasDerivAt_id y).sub_const (n : ℝ)
  have h2 : HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 2 - (y - (n : ℝ)) + 1 / 6)
      (2 * (y - (n : ℝ)) ^ (2 - 1) * 1 - 1) y :=
    ((h1.pow 2).sub h1).add_const (1 / 6)
  have h3 : (2 * (y - (n : ℝ)) ^ (2 - 1) * 1 - 1 : ℝ) = 2 * (y - (n : ℝ)) - 1 := by
    norm_num
  rw [h3] at h2
  exact h2

/-- One integration by parts turning the centred sawtooth against `f'` into the polynomial
`B₂`-weight against `f''`. -/
private lemma em2_interval (f' f'' : ℝ → ℂ) (n : ℕ)
    (hf' : ∀ y ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1), HasDerivAt f' (f'' y) y)
    (hint : IntervalIntegrable f'' volume (n : ℝ) ((n : ℝ) + 1)) :
    ∫ y in (n : ℝ)..((n : ℝ) + 1), ((y - n - 1 / 2 : ℝ) : ℂ) * f' y =
      (f' ((n : ℝ) + 1) - f' (n : ℝ)) / 12 -
        (1 / 2) * ∫ y in (n : ℝ)..((n : ℝ) + 1),
          (((y - n) ^ 2 - (y - n) + 1 / 6 : ℝ) : ℂ) * f'' y := by
  have hB := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun y : ℝ => (((y - n) ^ 2 - (y - n) + 1 / 6 : ℝ) : ℂ))
    (v := f')
    (u' := fun y : ℝ => (((2 : ℝ) * (y - n) - 1 : ℝ) : ℂ))
    (v' := f'')
    (fun y _ => (hasDerivAt_B2_poly n y).ofReal_comp) hf'
    (by
      have hc : Continuous fun y : ℝ => (((2 : ℝ) * (y - n) - 1 : ℝ) : ℂ) := by fun_prop
      exact hc.intervalIntegrable _ _) hint
  have h1 : ((((n : ℝ) + 1 - n) ^ 2 - ((n : ℝ) + 1 - n) + 1 / 6 : ℝ) : ℂ) = 1 / 6 := by
    norm_num
  have h0 : ((((n : ℝ) - n) ^ 2 - ((n : ℝ) - n) + 1 / 6 : ℝ) : ℂ) = 1 / 6 := by
    norm_num
  rw [h1, h0] at hB
  have hJ : ∫ y in (n : ℝ)..((n : ℝ) + 1), (((2 : ℝ) * (y - n) - 1 : ℝ) : ℂ) * f' y
      = 2 * ∫ y in (n : ℝ)..((n : ℝ) + 1), ((y - n - 1 / 2 : ℝ) : ℂ) * f' y := by
    rw [show (∫ y in (n : ℝ)..((n : ℝ) + 1), (((2 : ℝ) * (y - n) - 1 : ℝ) : ℂ) * f' y)
        = ∫ y in (n : ℝ)..((n : ℝ) + 1),
            (2 : ℂ) * (((y - n - 1 / 2 : ℝ) : ℂ) * f' y) from by
      refine intervalIntegral.integral_congr fun y _ => ?_
      push_cast
      ring]
    exact intervalIntegral.integral_const_mul 2 _
  rw [hJ] at hB
  linear_combination (1 / 2 : ℂ) * hB

/-- On a unit interval the periodic `B₂` agrees with the explicit polynomial a.e. -/
private lemma B2_fract_eq_poly (f'' : ℝ → ℂ) (n : ℕ) :
    ∫ y in (n : ℝ)..((n : ℝ) + 1), ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ) * f'' y =
      ∫ y in (n : ℝ)..((n : ℝ) + 1),
        (((y - n) ^ 2 - (y - n) + 1 / 6 : ℝ) : ℂ) * f'' y := by
  refine intervalIntegral.integral_congr_ae (μ := volume) ?_
  have hae : ∀ᵐ y : ℝ ∂volume, y ≠ (n : ℝ) + 1 := by
    rw [MeasureTheory.ae_iff]; simp
  filter_upwards [hae] with y hy hyin
  rw [Set.uIoc_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)] at hyin
  obtain ⟨hy1, hy2⟩ := hyin
  have hfl : ⌊y⌋ = (n : ℤ) :=
    Int.floor_eq_iff.2 ⟨by push_cast; linarith,
      by have h2 : y < (n : ℝ) + 1 := lt_of_le_of_ne hy2 hy; push_cast; linarith⟩
  have hfr : Int.fract y = y - n := by
    rw [← Int.self_sub_floor y, hfl]
    push_cast
    ring
  rw [hfr, bernoulliFun_two_eq]

private lemma intervalIntegrable_B2_fract (c : ℂ) (hc2 : c - 2 ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    IntervalIntegrable
      (fun y : ℝ => ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ) * (c * (c - 1) * (y : ℂ) ^ (c - 2)))
      volume (n : ℝ) ((n : ℝ) + 1) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hle : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hcont : ContinuousOn
      (fun y : ℝ => (((y - n) ^ 2 - (y - n) + 1 / 6 : ℝ) : ℂ) *
        (c * (c - 1) * (y : ℂ) ^ (c - 2)))
      (Set.uIcc (n : ℝ) ((n : ℝ) + 1)) := by
    apply ContinuousOn.mul
    · have : Continuous fun y : ℝ => (((y - n) ^ 2 - (y - n) + 1 / 6 : ℝ) : ℂ) := by fun_prop
      exact this.continuousOn
    · intro y hy
      rw [Set.uIcc_of_le hle] at hy
      have hy0 : 0 < y := lt_of_lt_of_le (by linarith : (0:ℝ) < (n:ℝ)) hy.1
      exact (((hasDerivAt_cpow_c (c - 2) hc2 hy0).const_mul (c * (c - 1))).continuousAt).continuousWithinAt
  refine hcont.intervalIntegrable.congr_uIoo ?_
  intro y hy
  rw [Set.uIoo_of_le hle] at hy
  have hfl : ⌊y⌋ = (n : ℤ) :=
    Int.floor_eq_iff.2 ⟨by push_cast; linarith [hy.1.le],
      by push_cast; linarith [hy.2]⟩
  have hfr : Int.fract y = y - n := by
    rw [← Int.self_sub_floor y, hfl]
    push_cast
    ring
  simp only []
  rw [hfr, bernoulliFun_two_eq]

/-! ## Summation plumbing -/

private lemma sum_Ico_shift_r (f : ℝ → ℂ) (a : ℕ) :
    ∀ b, a ≤ b → ∑ n ∈ Finset.Ico a b, f ((n : ℝ) + 1) = ∑ n ∈ Finset.Ioc a b, f (n : ℝ) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ico_succ_top hb, Finset.sum_Ioc_succ_top hb, ih]
    norm_num

private lemma sum_integral_units (g : ℝ → ℂ) (K K1 : ℕ) (hKK1 : K ≤ K1)
    (hg : ∀ n ∈ Finset.Ico K K1, IntervalIntegrable g volume (n : ℝ) ((n : ℝ) + 1)) :
    ∑ n ∈ Finset.Ico K K1, ∫ y in (n : ℝ)..((n : ℝ) + 1), g y
      = ∫ y in (K : ℝ)..(K1 : ℝ), g y := by
  have h := intervalIntegral.sum_integral_adjacent_intervals_Ico (μ := volume) (f := g)
    (a := fun k : ℕ => (k : ℝ)) hKK1
    (fun k hk => by
      have hk' : k ∈ Finset.Ico K K1 := by
        rw [Finset.mem_Ico]; exact ⟨hk.1, hk.2⟩
      simpa only [Nat.cast_add, Nat.cast_one] using hg k hk')
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-! ## The block form of second-order Euler–Maclaurin -/

private lemma em2_block (f f' f'' : ℝ → ℂ) (K K1 : ℕ) (hK1 : 1 ≤ K) (hKK1 : K ≤ K1)
    (hf : ∀ y ∈ Set.Ici (1 : ℝ), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Ici (1 : ℝ), HasDerivAt f' (f'' y) y)
    (hf_int : ∀ n ∈ Finset.Ico K K1, IntervalIntegrable f volume (n : ℝ) ((n : ℝ) + 1))
    (hf'_int : ∀ n ∈ Finset.Ico K K1, IntervalIntegrable f' volume (n : ℝ) ((n : ℝ) + 1))
    (hf''_int : ∀ n ∈ Finset.Ico K K1, IntervalIntegrable f'' volume (n : ℝ) ((n : ℝ) + 1))
    (hQ_int : ∀ n ∈ Finset.Ico K K1,
      IntervalIntegrable (fun y => ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ) * f'' y)
        volume (n : ℝ) ((n : ℝ) + 1)) :
    ∑ n ∈ Finset.Ioc K K1, f (n : ℝ) - ∫ y in (K : ℝ)..(K1 : ℝ), f y =
      (f (K1 : ℝ) - f (K : ℝ)) / 2 + (f' (K1 : ℝ) - f' (K : ℝ)) / 12
        - (1 / 2) * ∫ y in (K : ℝ)..(K1 : ℝ),
            ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ) * f'' y := by
  have hK1R : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
  have hstep : ∀ n ∈ Finset.Ico K K1,
      (f (n : ℝ) + f ((n : ℝ) + 1)) / 2 - ∫ y in (n : ℝ)..((n : ℝ) + 1), f y =
      (f' ((n : ℝ) + 1) - f' (n : ℝ)) / 12 -
        (1 / 2) * ∫ y in (n : ℝ)..((n : ℝ) + 1),
          ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ) * f'' y := by
    intro n hn
    have hnK : K ≤ n := (Finset.mem_Ico.1 hn).1
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have h1 : 1 ≤ n := le_trans hK1 hnK
      exact_mod_cast h1
    have hle : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hdf : ∀ y ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1), HasDerivAt f (f' y) y := by
      intro y hy
      rw [Set.uIcc_of_le hle] at hy
      exact hf y (le_trans hn1 hy.1)
    have hdf' : ∀ y ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1), HasDerivAt f' (f'' y) y := by
      intro y hy
      rw [Set.uIcc_of_le hle] at hy
      exact hf' y (le_trans hn1 hy.1)
    rw [← em1_interval f f' n hdf (hf'_int n hn)]
    rw [em2_interval f' f'' n hdf' (hf''_int n hn)]
    rw [B2_fract_eq_poly f'' n]
  have hsum := Finset.sum_congr rfl hstep
  -- evaluate the four sums
  have hS1 : ∑ n ∈ Finset.Ico K K1, (f (n : ℝ) + f ((n : ℝ) + 1)) / 2
      = ∑ n ∈ Finset.Ioc K K1, f (n : ℝ) + (f (K : ℝ) - f (K1 : ℝ)) / 2 := by
    have hs : ∑ n ∈ Finset.Ico K K1, (f (n : ℝ) + f ((n : ℝ) + 1)) / 2
        = (1 / 2) * ((∑ n ∈ Finset.Ico K K1, f (n : ℝ))
            + ∑ n ∈ Finset.Ico K K1, f ((n : ℝ) + 1)) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      ring
    have hIco : ∑ n ∈ Finset.Ico K K1, f (n : ℝ)
        = ∑ n ∈ Finset.Ioc K K1, f (n : ℝ) + f (K : ℝ) - f (K1 : ℝ) := by
      linear_combination sum_Ico_endpoint (fun k : ℕ => f (k : ℝ)) K K1 hKK1
    rw [hs, sum_Ico_shift_r f K K1 hKK1, hIco]
    ring
  have hS2 : ∑ n ∈ Finset.Ico K K1, ∫ y in (n : ℝ)..((n : ℝ) + 1), f y
      = ∫ y in (K : ℝ)..(K1 : ℝ), f y := sum_integral_units f K K1 hKK1 hf_int
  have hS3 : ∑ n ∈ Finset.Ico K K1, (f' ((n : ℝ) + 1) - f' (n : ℝ)) / 12
      = (f' (K1 : ℝ) - f' (K : ℝ)) / 12 := by
    have hs : ∑ n ∈ Finset.Ico K K1, (f' ((n : ℝ) + 1) - f' (n : ℝ)) / 12
        = (1 / 12) * ∑ n ∈ Finset.Ico K K1, (f' ((n : ℝ) + 1) - f' (n : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      ring
    have ht : ∑ n ∈ Finset.Ico K K1, (f' ((n : ℝ) + 1) - f' (n : ℝ))
        = f' (K1 : ℝ) - f' (K : ℝ) := by
      have h := sum_Ico_telescope (fun k : ℕ => f' (k : ℝ)) K K1 hKK1
      simpa only [Nat.cast_add, Nat.cast_one] using h
    rw [hs, ht]
    ring
  have hS4 : ∑ n ∈ Finset.Ico K K1, (1 / 2) * ∫ y in (n : ℝ)..((n : ℝ) + 1),
        ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ) * f'' y
      = (1 / 2) * ∫ y in (K : ℝ)..(K1 : ℝ),
          ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ) * f'' y := by
    rw [← Finset.mul_sum,
      sum_integral_units (fun y => ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ) * f'' y) K K1 hKK1 hQ_int]
  simp only [Finset.sum_sub_distrib, hS1, hS2, hS3, hS4] at hsum
  linear_combination hsum

/-! ## Oscillation: the first derivative test for `∫ A(y) e^{i(μy + t log y)}` -/

private lemma hasDerivAt_phase_gen {μ t : ℝ} {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => μ * y + t * Real.log y) (μ + t / y) y := by
  have h1 : HasDerivAt (fun y : ℝ => μ * y) μ y := by
    simpa using (hasDerivAt_id y).const_mul μ
  have h2 : HasDerivAt (fun y : ℝ => t * Real.log y) (t * y⁻¹) y :=
    (Real.hasDerivAt_log hy.ne').const_mul t
  have h := h1.add h2
  rw [show μ + t * y⁻¹ = μ + t / y from by rw [div_eq_mul_inv]] at h
  exact h

private lemma hasDerivAt_phase'_gen {μ t : ℝ} {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => μ + t / y) (-(t / y ^ 2)) y := by
  have h : HasDerivAt (fun y : ℝ => t / y) (-(t / y ^ 2)) y := by
    have h' := ((hasDerivAt_id y).inv hy.ne').const_mul t
    simpa [div_eq_mul_inv, mul_neg, mul_comm, mul_left_comm, mul_assoc] using h'
  have h2 : HasDerivAt (fun y : ℝ => μ) (0:ℝ) y := hasDerivAt_const y μ
  have h3 := h2.add h
  have h4 : ((fun y : ℝ => μ) + fun y : ℝ => t / y) = fun y : ℝ => μ + t / y := rfl
  rw [h4] at h3
  simpa using h3

private lemma hasDerivAt_v_gen {μ t : ℝ} {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ)))
      (Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ))
        * (Complex.I * ((μ + t / y : ℝ) : ℂ))) y := by
  have hφ := hasDerivAt_phase_gen (μ := μ) (t := t) hy
  have h1 : HasDerivAt (fun y : ℝ => Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ))
      (Complex.I * ((μ + t / y : ℝ) : ℂ)) y := hφ.ofReal_comp.const_mul Complex.I
  exact h1.cexp

private lemma hasDerivAt_psi_gen {μ t : ℝ} {y : ℝ} (hy : 0 < y) (hq : μ + t / y ≠ 0) :
    HasDerivAt (fun y : ℝ => y ^ (-5/2 : ℝ) / (μ + t / y))
      (((-(5/2) * y ^ (-7/2 : ℝ)) * (μ + t / y) - y ^ (-5/2 : ℝ) * (-(t / y ^ 2)))
        / (μ + t / y) ^ 2) y := by
  have hA : HasDerivAt (fun y : ℝ => y ^ (-5/2 : ℝ)) ((-(5/2)) * y ^ (-7/2 : ℝ)) y := by
    have h := Real.hasDerivAt_rpow_const (x := y) (p := (-5/2 : ℝ)) (Or.inl hy.ne')
    have hexp : (-5/2 - 1 : ℝ) = -7/2 := by norm_num
    rw [hexp] at h
    simpa only [neg_div] using h
  have hq' := hasDerivAt_phase'_gen (μ := μ) (t := t) hy
  exact hA.div hq' hq

private lemma psi'_val {μ t y : ℝ} (hy : 0 < y) (hq : μ + t / y ≠ 0) :
    (((-(5/2) * y ^ (-7/2 : ℝ)) * (μ + t / y) - y ^ (-5/2 : ℝ) * (-(t / y ^ 2)))
        / (μ + t / y) ^ 2)
      = -(5/2) * y ^ (-7/2 : ℝ) / (μ + t / y)
        - y ^ (-5/2 : ℝ) * (-(t / y ^ 2)) / (μ + t / y) ^ 2 := by
  field_simp

private lemma rpow_neg52_mul_inv {a : ℝ} (ha : 0 < a) :
    a ^ (-5/2 : ℝ) * a⁻¹ = a ^ (-7/2 : ℝ) := by
  have h : a ^ (-5/2 : ℝ) * a ^ (-1 : ℝ) = a ^ (-7/2 : ℝ) := by
    rw [← Real.rpow_add ha]
    norm_num
  rwa [Real.rpow_neg_one] at h

private lemma rpow_inv_mul_neg52 {a : ℝ} (ha : 0 < a) :
    a⁻¹ * a ^ (-5/2 : ℝ) = a ^ (-7/2 : ℝ) := by
  rw [mul_comm]
  exact rpow_neg52_mul_inv ha

private lemma rpow_neg72_mul {a : ℝ} (ha : 0 < a) :
    a ^ (-7/2 : ℝ) * a = a ^ (-5/2 : ℝ) := by
  have h : a ^ (-7/2 : ℝ) * a ^ (1 : ℝ) = a ^ (-5/2 : ℝ) := by
    rw [← Real.rpow_add ha]
    norm_num
  rwa [Real.rpow_one] at h

private lemma continuousOn_log_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun y : ℝ => Real.log y) (Set.uIcc a b) := by
  refine Real.continuousOn_log.mono ?_
  intro y hy
  rw [Set.uIcc_of_le hab] at hy
  exact ne_of_gt (lt_of_lt_of_le ha hy.1)

private lemma continuousOn_phase_cont {μ t a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun y : ℝ => μ * y + t * Real.log y) (Set.uIcc a b) :=
  ((continuous_const.mul continuous_id).continuousOn).add
    (continuousOn_const.mul (continuousOn_log_Icc ha hab))

private lemma continuousOn_phase'_cont {μ t a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun y : ℝ => μ + t / y) (Set.uIcc a b) := by
  intro y hy
  rw [Set.uIcc_of_le hab] at hy
  exact (hasDerivAt_phase'_gen (μ := μ) (t := t)
    (lt_of_lt_of_le ha hy.1)).continuousAt.continuousWithinAt

private lemma continuousOn_rpow_neg {p a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun y : ℝ => y ^ p) (Set.uIcc a b) := by
  intro y hy
  rw [Set.uIcc_of_le hab] at hy
  exact (Real.continuousAt_rpow_const y p
    (Or.inl (ne_of_gt (lt_of_lt_of_le ha hy.1)))).continuousWithinAt

/-- First derivative (oscillation) test with amplitude `y ↦ y^{-5/2}` and phase `μy + t log y`,
whose derivative is bounded below by `3` on `[a,b]` when `5 ≤ |μ|` and `|t| ≤ 2a`. -/
private lemma osc_integral_bound {a b μ t : ℝ} (ha : 0 < a) (hab : a ≤ b) (hba : b ≤ 4 * a)
    (hμ : 5 ≤ |μ|) (ht : |t| ≤ 2 * a) :
    ‖∫ y in a..b, ((y ^ (-5/2 : ℝ) : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ))‖
      ≤ 10 * a ^ (-5/2 : ℝ) := by
  have hφ3 : ∀ y ∈ Set.uIcc a b, (3:ℝ) ≤ |μ + t / y| := by
    intro y hy
    rw [Set.uIcc_of_le hab] at hy
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    have h1 : |t / y| ≤ 2 := by
      rw [abs_div, abs_of_pos hy0, div_le_iff₀ hy0]
      calc |t| ≤ 2 * a := ht
        _ ≤ 2 * y := by linarith [hy.1]
    have h2 : |μ| ≤ |μ + t / y| + |t / y| := by
      have h3 := abs_add_le (μ + t / y) (-(t / y))
      rwa [add_neg_cancel_right, abs_neg] at h3
    linarith
  have hφne : ∀ y ∈ Set.uIcc a b, μ + t / y ≠ 0 := by
    intro y hy h0
    have h := hφ3 y hy
    rw [h0, abs_zero] at h
    linarith
  have hypos : ∀ y ∈ Set.uIcc a b, 0 < y := by
    intro y hy
    rw [Set.uIcc_of_le hab] at hy
    exact lt_of_lt_of_le ha hy.1
  have hnorm_exp : ∀ y : ℝ,
      ‖Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ))‖ = 1 := by
    intro y
    rw [Complex.norm_exp]
    simp
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun y : ℝ => -(Complex.I) * (((y ^ (-5/2 : ℝ) / (μ + t / y) : ℝ)) : ℂ))
    (v := fun y : ℝ => Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ)))
    (u' := fun y : ℝ => -(Complex.I) * (((-(5/2) * y ^ (-7/2 : ℝ) / (μ + t / y)
        - y ^ (-5/2 : ℝ) * (-(t / y ^ 2)) / (μ + t / y) ^ 2 : ℝ)) : ℂ))
    (v' := fun y : ℝ => Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ))
        * (Complex.I * ((μ + t / y : ℝ) : ℂ)))
    (fun y hy => by
      have hp := hasDerivAt_psi_gen (μ := μ) (t := t) (hypos y hy) (hφne y hy)
      rw [psi'_val (hypos y hy) (hφne y hy)] at hp
      exact hp.ofReal_comp.const_mul (-Complex.I))
    (fun y hy => hasDerivAt_v_gen (μ := μ) (t := t) (hypos y hy))
    (by
      -- continuity of u' on the interval
      have h1 : ContinuousOn (fun y : ℝ => -(5/2) * y ^ (-7/2 : ℝ) / (μ + t / y)
          - y ^ (-5/2 : ℝ) * (-(t / y ^ 2)) / (μ + t / y) ^ 2) (Set.uIcc a b) := by
        have h7 := continuousOn_rpow_neg (p := (-7/2 : ℝ)) ha hab
        have h5 := continuousOn_rpow_neg (p := (-5/2 : ℝ)) ha hab
        have hq := continuousOn_phase'_cont (μ := μ) (t := t) ha hab
        have hqne : ∀ y ∈ Set.uIcc a b, μ + t / y ≠ 0 := hφne
        have hsq : ContinuousOn (fun y : ℝ => (μ + t / y) ^ 2) (Set.uIcc a b) := hq.pow 2
        have hsqq : ∀ y ∈ Set.uIcc a b, (μ + t / y) ^ 2 ≠ 0 := by
          intro y hy h
          exact hqne y hy (pow_eq_zero_iff'.1 h |>.1)
        have hA : ContinuousOn (fun y : ℝ => -(5/2) * y ^ (-7/2 : ℝ)) (Set.uIcc a b) :=
          continuousOn_const.mul h7
        have hB : ContinuousOn (fun y : ℝ => y ^ (-5/2 : ℝ) * (-(t / y ^ 2))) (Set.uIcc a b) := by
          apply h5.mul
          have hdiv : ContinuousOn (fun y : ℝ => (-t) / y ^ 2) (Set.uIcc a b) :=
            continuousOn_const.div (s := Set.uIcc a b)
              ((continuous_id (X := ℝ)).continuousOn.pow 2) (fun y hy => by
                rw [Set.uIcc_of_le hab] at hy
                exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha hy.1)))
          simpa only [neg_div] using hdiv
        exact (hA.div hq hqne).sub (hB.div hsq hsqq)
      exact (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn h1)).intervalIntegrable)
    (by
      have hq := continuousOn_phase'_cont (μ := μ) (t := t) ha hab
      have h1 : ContinuousOn (fun y : ℝ => Complex.I * ((μ + t / y : ℝ) : ℂ)) (Set.uIcc a b) :=
        continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hq)
      have h2 : ContinuousOn (fun y : ℝ =>
          Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ))) (Set.uIcc a b) :=
        Complex.continuous_exp.comp_continuousOn
          (continuousOn_const.mul
            (Complex.continuous_ofReal.comp_continuousOn
              (continuousOn_phase_cont (μ := μ) (t := t) ha hab)))
      exact (h2.mul h1).intervalIntegrable)
  have hprod : ∀ y ∈ Set.uIcc a b,
      ((y ^ (-5/2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ))
      = (-(Complex.I) * (((y ^ (-5/2 : ℝ) / (μ + t / y) : ℝ)) : ℂ)) *
        (Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ))
          * (Complex.I * ((μ + t / y : ℝ) : ℂ))) := by
    intro y hy
    have hne := hφne y hy
    have hcast : ((μ + t / y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
    have hdivR : y ^ (-5/2 : ℝ) / (μ + t / y) * (μ + t / y) = y ^ (-5/2 : ℝ) :=
      div_mul_cancel₀ _ hne
    have hdiv : ((y ^ (-5/2 : ℝ) / (μ + t / y) : ℝ) : ℂ) * ((μ + t / y : ℝ) : ℂ)
        = ((y ^ (-5/2 : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, hdivR]
    have hI : (-(Complex.I)) * Complex.I = (1 : ℂ) := by
      rw [neg_mul, Complex.I_mul_I]; ring
    calc ((y ^ (-5/2 : ℝ) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ))
        = ((-(Complex.I)) * Complex.I) *
            (((y ^ (-5/2 : ℝ) : ℝ) : ℂ)
              * Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ))) := by
          rw [hI]; ring
      _ = ((-(Complex.I)) * Complex.I) *
            ((((y ^ (-5/2 : ℝ) / (μ + t / y) : ℝ)) : ℂ) * ((μ + t / y : ℝ) : ℂ)
              * Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ))) := by
          rw [hdiv]
      _ = (-(Complex.I) * (((y ^ (-5/2 : ℝ) / (μ + t / y) : ℝ)) : ℂ)) *
          (Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ))
            * (Complex.I * ((μ + t / y : ℝ) : ℂ))) := by
          ring
  have hmain : ∫ y in a..b, ((y ^ (-5/2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ))
      = (-(Complex.I) * (((b ^ (-5/2 : ℝ) / (μ + t / b) : ℝ)) : ℂ)) *
          Complex.exp (Complex.I * ((μ * b + t * Real.log b : ℝ) : ℂ))
        - (-(Complex.I) * (((a ^ (-5/2 : ℝ) / (μ + t / a) : ℝ)) : ℂ)) *
          Complex.exp (Complex.I * ((μ * a + t * Real.log a : ℝ) : ℂ))
        - ∫ y in a..b, (-(Complex.I) * (((-(5/2) * y ^ (-7/2 : ℝ) / (μ + t / y)
            - y ^ (-5/2 : ℝ) * (-(t / y ^ 2)) / (μ + t / y) ^ 2 : ℝ)) : ℂ)) *
          Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ)) := by
    rw [← hIBP]
    exact intervalIntegral.integral_congr hprod
  have hbnd1 : ∀ y ∈ Set.uIcc a b,
      ‖(-(Complex.I) * (((y ^ (-5/2 : ℝ) / (μ + t / y) : ℝ)) : ℂ)) *
        Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ))‖ ≤ a ^ (-5/2 : ℝ) := by
    intro y hy
    have h3 := hφ3 y hy
    have hψ : ‖(-(Complex.I) * (((y ^ (-5/2 : ℝ) / (μ + t / y) : ℝ)) : ℂ))‖
        = y ^ (-5/2 : ℝ) / |μ + t / y| := by
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_div, abs_of_pos (Real.rpow_pos_of_pos (hypos y hy) _)]
    rw [norm_mul, hnorm_exp, mul_one, hψ]
    have hle : y ^ (-5/2 : ℝ) ≤ a ^ (-5/2 : ℝ) := by
      refine Real.rpow_le_rpow_of_nonpos ha ?_ (by norm_num)
      rw [Set.uIcc_of_le hab] at hy
      exact hy.1
    have hpos : (0:ℝ) < y ^ (-5/2 : ℝ) := Real.rpow_pos_of_pos (hypos y hy) _
    have hA : (0:ℝ) < a ^ (-5/2 : ℝ) := Real.rpow_pos_of_pos ha _
    calc y ^ (-5/2 : ℝ) / |μ + t / y| ≤ y ^ (-5/2 : ℝ) / 3 :=
          div_le_div_of_nonneg_left (le_of_lt hpos) (by norm_num) h3
      _ ≤ a ^ (-5/2 : ℝ) / 3 := div_le_div_of_nonneg_right hle (by norm_num)
      _ ≤ a ^ (-5/2 : ℝ) := by linarith
  have hbound2 : ∀ y ∈ Set.uIoc a b,
      ‖(-(Complex.I) * (((-(5/2) * y ^ (-7/2 : ℝ) / (μ + t / y)
          - y ^ (-5/2 : ℝ) * (-(t / y ^ 2)) / (μ + t / y) ^ 2 : ℝ)) : ℂ)) *
        Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ))‖
        ≤ (2 : ℝ) * a ^ (-7/2 : ℝ) := by
    intro y hy
    rw [Set.uIoc_of_le hab] at hy
    have hy1 : a ≤ y := hy.1.le
    have hy0 : 0 < y := lt_of_lt_of_le ha hy1
    have hyu : y ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact ⟨hy1, hy.2⟩
    have h3 := hφ3 y hyu
    have h3pos : (0:ℝ) < |μ + t / y| := by linarith
    have hnorm : ‖(-(Complex.I) * (((-(5/2) * y ^ (-7/2 : ℝ) / (μ + t / y)
          - y ^ (-5/2 : ℝ) * (-(t / y ^ 2)) / (μ + t / y) ^ 2 : ℝ)) : ℂ))‖
        = |-(5/2) * y ^ (-7/2 : ℝ) / (μ + t / y)
          - y ^ (-5/2 : ℝ) * (-(t / y ^ 2)) / (μ + t / y) ^ 2| := by
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_mul, hnorm_exp, mul_one, hnorm]
    have hsplit : |-(5/2) * y ^ (-7/2 : ℝ) / (μ + t / y)
          - y ^ (-5/2 : ℝ) * (-(t / y ^ 2)) / (μ + t / y) ^ 2|
        ≤ |(5/2) * y ^ (-7/2 : ℝ) / (μ + t / y)|
          + |y ^ (-5/2 : ℝ) * (t / y ^ 2) / (μ + t / y) ^ 2| := by
      have h1 : (-(5/2) * y ^ (-7/2 : ℝ) / (μ + t / y)
          - y ^ (-5/2 : ℝ) * (-(t / y ^ 2)) / (μ + t / y) ^ 2)
          = (-((5/2) * y ^ (-7/2 : ℝ) / (μ + t / y)))
            - (-(y ^ (-5/2 : ℝ) * (t / y ^ 2) / (μ + t / y) ^ 2)) := by ring
      rw [h1, sub_neg_eq_add]
      have hab := abs_add_le (-((5/2) * y ^ (-7/2 : ℝ) / (μ + t / y)))
        (y ^ (-5/2 : ℝ) * (t / y ^ 2) / (μ + t / y) ^ 2)
      simpa using hab
    have hP : |(5/2) * y ^ (-7/2 : ℝ) / (μ + t / y)| ≤ a ^ (-7/2 : ℝ) := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (5/2) * y ^ (-7/2 : ℝ))]
      have hA : y ^ (-7/2 : ℝ) ≤ a ^ (-7/2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos ha hy1 (by norm_num)
      have hp : (0:ℝ) < a ^ (-7/2 : ℝ) := Real.rpow_pos_of_pos ha _
      have h1 : (5/2) * y ^ (-7/2 : ℝ) ≤ (5/2) * a ^ (-7/2 : ℝ) := by linarith
      have h2 : (5/2) * a ^ (-7/2 : ℝ) ≤ a ^ (-7/2 : ℝ) * 3 := by nlinarith
      have h3' : a ^ (-7/2 : ℝ) * 3 ≤ a ^ (-7/2 : ℝ) * |μ + t / y| :=
        mul_le_mul_of_nonneg_left h3 (le_of_lt hp)
      rw [div_le_iff₀ h3pos]
      linarith
    have hQ : |y ^ (-5/2 : ℝ) * (t / y ^ 2) / (μ + t / y) ^ 2| ≤ a ^ (-7/2 : ℝ) := by
      have hA : y ^ (-5/2 : ℝ) ≤ a ^ (-5/2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos ha hy1 (by norm_num)
      have hApos : (0:ℝ) < y ^ (-5/2 : ℝ) := Real.rpow_pos_of_pos hy0 _
      have hsq : (9:ℝ) ≤ (μ + t / y) ^ 2 := by
        have hnn : (0:ℝ) ≤ |μ + t / y| := abs_nonneg _
        have h9 : (9:ℝ) ≤ |μ + t / y| ^ 2 := by nlinarith
        rwa [sq_abs] at h9
      have ht2 : |t| / y ^ 2 ≤ 2 * a / a ^ 2 := by
        have hy2 : (0:ℝ) < y ^ 2 := by positivity
        have ha2 : (0:ℝ) < a ^ 2 := by positivity
        have h1 : |t| / y ^ 2 ≤ 2 * a / y ^ 2 :=
          div_le_div_of_nonneg_right (by linarith) (le_of_lt hy2)
        have h2 : 2 * a / y ^ 2 ≤ 2 * a / a ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) ha2 (by nlinarith)
        linarith
      have hQeq : |y ^ (-5/2 : ℝ) * (t / y ^ 2) / (μ + t / y) ^ 2|
          = y ^ (-5/2 : ℝ) * (|t| / y ^ 2) / (μ + t / y) ^ 2 := by
        rw [abs_div, abs_mul, abs_of_pos hApos, abs_div,
          abs_of_pos (by positivity : (0:ℝ) < y ^ 2),
          abs_of_pos (by positivity : (0:ℝ) < (μ + t / y) ^ 2)]
      rw [hQeq]
      have hstep : a ^ (-5/2 : ℝ) * (2 * a / a ^ 2) = 2 * a ^ (-7/2 : ℝ) := by
        have h1 : 2 * a / a ^ 2 = 2 * a⁻¹ := by field_simp
        have key : a ^ (-5/2 : ℝ) * (2 * a⁻¹) = 2 * (a⁻¹ * a ^ (-5/2 : ℝ)) := by ring
        have h3 : a⁻¹ * a ^ (-5/2 : ℝ) = a ^ (-7/2 : ℝ) := rpow_inv_mul_neg52 ha
        calc a ^ (-5/2 : ℝ) * (2 * a / a ^ 2) = a ^ (-5/2 : ℝ) * (2 * a⁻¹) := by rw [h1]
          _ = 2 * (a⁻¹ * a ^ (-5/2 : ℝ)) := key
          _ = 2 * a ^ (-7/2 : ℝ) := by rw [h3]
      have hlt : y ^ (-5/2 : ℝ) * (|t| / y ^ 2) ≤ a ^ (-5/2 : ℝ) * (2 * a / a ^ 2) :=
        mul_le_mul hA ht2 (by positivity) (by positivity)
      have hnum : y ^ (-5/2 : ℝ) * (|t| / y ^ 2) ≤ 2 * a ^ (-7/2 : ℝ) := by
        rw [← hstep]; exact hlt
      have hp : (0:ℝ) < a ^ (-7/2 : ℝ) := Real.rpow_pos_of_pos ha _
      have hpos2 : (0:ℝ) < 2 * a ^ (-7/2 : ℝ) := by positivity
      calc y ^ (-5/2 : ℝ) * (|t| / y ^ 2) / (μ + t / y) ^ 2
          ≤ (2 * a ^ (-7/2 : ℝ)) / (μ + t / y) ^ 2 :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ (2 * a ^ (-7/2 : ℝ)) / 9 :=
            div_le_div_of_nonneg_left (le_of_lt hpos2) (by norm_num) hsq
        _ ≤ a ^ (-7/2 : ℝ) := by
            rw [div_le_iff₀ (by norm_num : (0:ℝ) < 9)]
            linarith
    linarith
  rw [hmain]
  have ht1 : ‖(-(Complex.I) * (((b ^ (-5/2 : ℝ) / (μ + t / b) : ℝ)) : ℂ)) *
        Complex.exp (Complex.I * ((μ * b + t * Real.log b : ℝ) : ℂ))‖ ≤ a ^ (-5/2 : ℝ) :=
    hbnd1 b (by rw [Set.uIcc_of_le hab]; exact ⟨hab, le_rfl⟩)
  have ht2 : ‖(-(Complex.I) * (((a ^ (-5/2 : ℝ) / (μ + t / a) : ℝ)) : ℂ)) *
        Complex.exp (Complex.I * ((μ * a + t * Real.log a : ℝ) : ℂ))‖ ≤ a ^ (-5/2 : ℝ) :=
    hbnd1 a (by rw [Set.uIcc_of_le hab]; exact ⟨le_rfl, hab⟩)
  have ht3 := intervalIntegral.norm_integral_le_of_norm_le_const hbound2
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)] at ht3
  have hA7 : (0:ℝ) < a ^ (-7/2 : ℝ) := Real.rpow_pos_of_pos ha _
  have step : ‖∫ y in a..b, (-(Complex.I) * (((-(5/2) * y ^ (-7/2 : ℝ) / (μ + t / y)
        - y ^ (-5/2 : ℝ) * (-(t / y ^ 2)) / (μ + t / y) ^ 2 : ℝ)) : ℂ)) *
        Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ))‖
      ≤ 6 * a ^ (-5/2 : ℝ) := by
    refine le_trans ht3 ?_
    have h1 : (2:ℝ) * a ^ (-7/2 : ℝ) * (b - a) ≤ 2 * a ^ (-7/2 : ℝ) * (3 * a) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have h2 : 2 * a ^ (-7/2 : ℝ) * (3 * a) = 6 * a ^ (-5/2 : ℝ) := by
      have h3 : a ^ (-7/2 : ℝ) * a = a ^ (-5/2 : ℝ) := rpow_neg72_mul ha
      calc 2 * a ^ (-7/2 : ℝ) * (3 * a) = 6 * (a ^ (-7/2 : ℝ) * a) := by ring
        _ = 6 * a ^ (-5/2 : ℝ) := by rw [h3]
    linarith [h1, h2]
  calc ‖(-(Complex.I) * (((b ^ (-5/2 : ℝ) / (μ + t / b) : ℝ)) : ℂ)) *
          Complex.exp (Complex.I * ((μ * b + t * Real.log b : ℝ) : ℂ))
        - (-(Complex.I) * (((a ^ (-5/2 : ℝ) / (μ + t / a) : ℝ)) : ℂ)) *
          Complex.exp (Complex.I * ((μ * a + t * Real.log a : ℝ) : ℂ))
        - ∫ y in a..b, (-(Complex.I) * (((-(5/2) * y ^ (-7/2 : ℝ) / (μ + t / y)
            - y ^ (-5/2 : ℝ) * (-(t / y ^ 2)) / (μ + t / y) ^ 2 : ℝ)) : ℂ)) *
          Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ))‖
      ≤ ‖(-(Complex.I) * (((b ^ (-5/2 : ℝ) / (μ + t / b) : ℝ)) : ℂ)) *
            Complex.exp (Complex.I * ((μ * b + t * Real.log b : ℝ) : ℂ))‖
        + ‖(-(Complex.I) * (((a ^ (-5/2 : ℝ) / (μ + t / a) : ℝ)) : ℂ)) *
            Complex.exp (Complex.I * ((μ * a + t * Real.log a : ℝ) : ℂ))‖
        + ‖∫ y in a..b, (-(Complex.I) * (((-(5/2) * y ^ (-7/2 : ℝ) / (μ + t / y)
            - y ^ (-5/2 : ℝ) * (-(t / y ^ 2)) / (μ + t / y) ^ 2 : ℝ)) : ℂ)) *
          Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ))‖ := by
        have h1 := norm_sub_le
          ((-(Complex.I) * (((b ^ (-5/2 : ℝ) / (μ + t / b) : ℝ)) : ℂ)) *
            Complex.exp (Complex.I * ((μ * b + t * Real.log b : ℝ) : ℂ)))
          ((-(Complex.I) * (((a ^ (-5/2 : ℝ) / (μ + t / a) : ℝ)) : ℂ)) *
            Complex.exp (Complex.I * ((μ * a + t * Real.log a : ℝ) : ℂ)))
        have h2 := norm_sub_le
          ((-(Complex.I) * (((b ^ (-5/2 : ℝ) / (μ + t / b) : ℝ)) : ℂ)) *
              Complex.exp (Complex.I * ((μ * b + t * Real.log b : ℝ) : ℂ))
            - (-(Complex.I) * (((a ^ (-5/2 : ℝ) / (μ + t / a) : ℝ)) : ℂ)) *
              Complex.exp (Complex.I * ((μ * a + t * Real.log a : ℝ) : ℂ)))
          (∫ y in a..b, (-(Complex.I) * (((-(5/2) * y ^ (-7/2 : ℝ) / (μ + t / y)
            - y ^ (-5/2 : ℝ) * (-(t / y ^ 2)) / (μ + t / y) ^ 2 : ℝ)) : ℂ)) *
            Complex.exp (Complex.I * ((μ * y + t * Real.log y : ℝ) : ℂ)))
        linarith
    _ ≤ a ^ (-5/2 : ℝ) + a ^ (-5/2 : ℝ) + 6 * a ^ (-5/2 : ℝ) := by linarith
    _ ≤ 10 * a ^ (-5/2 : ℝ) := by
        have hA5 : (0:ℝ) < a ^ (-5/2 : ℝ) := Real.rpow_pos_of_pos ha _
        linarith

/-! ## The Fourier series of `B₂` -/

private lemma exp_two_pi_I_fract (n : ℤ) (y : ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((Int.fract y : ℝ) : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) := by
  have hfloor : ((Int.fract y : ℝ) + ((⌊y⌋ : ℤ) : ℝ)) = y := Int.fract_add_floor y
  have hy : (y : ℂ) = ((Int.fract y : ℝ) : ℂ) + ((⌊y⌋ : ℤ) : ℂ) := by
    calc (y : ℂ) = (((Int.fract y : ℝ) + ((⌊y⌋ : ℤ) : ℝ) : ℝ) : ℂ) := by rw [hfloor]
      _ = ((Int.fract y : ℝ) : ℂ) + ((⌊y⌋ : ℤ) : ℂ) := by push_cast; ring
  rw [hy]
  have hsplit : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)
        * (((Int.fract y : ℝ) : ℂ) + ((⌊y⌋ : ℤ) : ℂ))
      = 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((Int.fract y : ℝ) : ℂ)
        + ((n * ⌊y⌋ : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private lemma B2_fourier_tsum (y : ℝ) :
    (∑' n : ℤ, (1 / (n : ℂ) ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)))
      = 2 * (Real.pi : ℂ) ^ 2 * ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ) := by
  have hx : Int.fract y ∈ Set.Icc (0:ℝ) 1 :=
    ⟨Int.fract_nonneg y, le_of_lt (Int.fract_lt_one y)⟩
  have h := hasSum_one_div_pow_mul_fourier_mul_bernoulliFun (k := 2) (by norm_num) hx
  have hval : (-(2 * (Real.pi : ℂ) * Complex.I) ^ 2 / ((Nat.factorial 2 : ℕ) : ℂ))
        * ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ)
      = 2 * (Real.pi : ℂ) ^ 2 * ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ) := by
    have h2 : ((Nat.factorial 2 : ℕ) : ℂ) = 2 := by norm_num
    have hsq : (2 * (Real.pi : ℂ) * Complex.I) ^ 2 = -(4 * (Real.pi : ℂ) ^ 2) := by
      linear_combination (4 * (Real.pi : ℂ) ^ 2) * Complex.I_mul_I
    rw [h2, hsq]
    ring
  rw [← hval, ← h.tsum_eq]
  refine tsum_congr (fun n => ?_)
  have hf : fourier n ((Int.fract y : ℝ) : UnitAddCircle)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((Int.fract y : ℝ) : ℂ)) := by
    rw [fourier_coe_apply]
    norm_num
  rw [hf, exp_two_pi_I_fract]

/-! ## Term-by-term integration of the `B₂` Fourier series against `f''` -/

private lemma norm_one_div_sq_intCast (n : ℤ) :
    ‖(1 / (n : ℂ) ^ 2)‖ = (1 / (n : ℝ) ^ 2) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [norm_div, norm_one, norm_pow, Complex.norm_intCast]
    norm_num

private lemma summable_one_div_sq_int : Summable fun n : ℤ => (1 / (n : ℝ) ^ 2) := by
  simpa using (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)

set_option maxHeartbeats 1000000 in
private lemma integral_B2_fourier {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {c : ℂ}
    (hre : c.re = -1 / 2) (hc2 : c - 2 ≠ 0) :
    ∫ y in a..b, ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ) * (c * (c - 1) * (y : ℂ) ^ (c - 2))
      = (1 / (2 * (Real.pi : ℂ) ^ 2)) * ∑' n : ℤ,
          ∫ y in a..b, (1 / (n : ℂ) ^ 2) *
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
            (c * (c - 1) * (y : ℂ) ^ (c - 2)) := by
  have key : ∀ {y : ℝ}, y ∈ Set.uIcc a b → a ≤ y := by
    intro y hy
    rcases Set.mem_uIcc.mp hy with h | h
    · exact h.1
    · exact le_of_eq (le_antisymm h.2 (le_trans hab h.1)).symm
  have hcut : ∀ y : ℝ, (0:ℝ) < max y a := fun y => lt_of_lt_of_le ha (le_max_right y a)
  have hcontpow : Continuous fun y : ℝ => (((max y a : ℝ)) : ℂ) ^ (c - 2) := by
    refine continuous_iff_continuousAt.2 (fun y => ?_)
    have hsp : (((max y a : ℝ)) : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.ofReal_mem_slitPlane]; exact hcut y
    have hmaxc : ContinuousAt (fun y : ℝ => (((max y a : ℝ)) : ℂ)) y :=
      Complex.continuous_ofReal.continuousAt.comp
        ((continuous_id.max continuous_const).continuousAt)
    exact ContinuousAt.comp (g := fun z : ℂ => z ^ (c - 2))
      (f := fun y : ℝ => (((max y a : ℝ)) : ℂ)) (continuousAt_cpow_const hsp) hmaxc
  have hexp : ∀ n : ℤ, Continuous fun y : ℝ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) := by
    intro n
    refine Complex.continuous_exp.comp ?_
    exact (Complex.continuous_ofReal.const_mul (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)))
  have hcont : ∀ n : ℤ, Continuous fun y : ℝ =>
      (1 / (n : ℂ) ^ 2) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
        (c * (c - 1) * (((max y a : ℝ)) : ℂ) ^ (c - 2)) := by
    intro n
    have h1 : Continuous fun y : ℝ => (1 / (n : ℂ) ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) :=
      continuous_const.mul (hexp n)
    have h2 : Continuous fun y : ℝ => c * (c - 1) * (((max y a : ℝ)) : ℂ) ^ (c - 2) :=
      (continuous_const.mul continuous_const).mul hcontpow
    exact h1.mul h2
  set M : ℝ := ‖c‖ * ‖c - 1‖ * a ^ (-5/2 : ℝ) with hM
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  -- the pointwise bound on `[a,b]`
  have hpt : ∀ (n : ℤ) (y : ℝ), y ∈ Set.uIcc a b →
      ‖(1 / (n : ℂ) ^ 2) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
        (c * (c - 1) * (y : ℂ) ^ (c - 2))‖ ≤ (1 / (n : ℝ) ^ 2) * M := by
    intro n y hy
    have hy1 : a ≤ y := key hy
    rw [hM, norm_mul, norm_mul]
    have hexp1 : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [hexp1, mul_one, norm_mul, norm_mul, norm_one_div_sq_intCast]
    have hnormc : ‖(y : ℂ) ^ (c - 2)‖ = y ^ (-5/2 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le ha hy1)]
      rw [show (c - 2).re = -5/2 by rw [Complex.sub_re, hre]; norm_num]
    rw [hnormc]
    have hle : y ^ (-5/2 : ℝ) ≤ a ^ (-5/2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos ha hy1 (by norm_num)
    have hstep : ‖c‖ * ‖c - 1‖ * (y ^ (-5/2 : ℝ)) ≤ ‖c‖ * ‖c - 1‖ * (a ^ (-5/2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    calc (1 / (n : ℝ) ^ 2) * (‖c‖ * ‖c - 1‖ * y ^ (-5/2 : ℝ))
        ≤ (1 / (n : ℝ) ^ 2) * (‖c‖ * ‖c - 1‖ * a ^ (-5/2 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hstep
          positivity
      _ = (1 / (n : ℝ) ^ 2) * (‖c‖ * ‖c - 1‖ * a ^ (-5/2 : ℝ)) := rfl
  -- the continuous family, cut off at `a` so that it is continuous on all of `ℝ`
  let G : ℤ → C(ℝ, ℂ) := fun n => ⟨fun y : ℝ => (1 / (n : ℂ) ^ 2) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
      (c * (c - 1) * (((max y a : ℝ)) : ℂ) ^ (c - 2)), hcont n⟩
  have hGapply : ∀ (n : ℤ) (y : ℝ), G n y = (1 / (n : ℂ) ^ 2) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
      (c * (c - 1) * (((max y a : ℝ)) : ℂ) ^ (c - 2)) := fun n y => rfl
  have hsumm : Summable fun n : ℤ =>
      ‖(G n).restrict ((⟨Set.uIcc a b, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ) : Set ℝ)‖ := by
    have hmaj : ∀ n : ℤ,
        ‖(G n).restrict ((⟨Set.uIcc a b, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ) : Set ℝ)‖
          ≤ (1 / (n : ℝ) ^ 2) * M := by
      intro n
      refine (ContinuousMap.norm_le (f := (G n).restrict
        ((⟨Set.uIcc a b, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ) : Set ℝ))
        (mul_nonneg (by positivity) hMnn)).2 (fun y => ?_)
      have hy : (y : ℝ) ∈ Set.uIcc a b := y.2
      have hmax : max (y : ℝ) a = (y : ℝ) := max_eq_left (key hy)
      show ‖(G n) ((y : ℝ))‖ ≤ (1 / (n : ℝ) ^ 2) * M
      rw [hGapply n (y : ℝ), hmax]
      exact hpt n (y : ℝ) hy
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hmaj
      (summable_one_div_sq_int.mul_right M)
  have htsum := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
    (a := a) (b := b) (E := ℂ) (f := G) hsumm
  -- the pointwise sum on `[a,b]`
  have hident : ∀ y ∈ Set.uIcc a b, (∑' n : ℤ, G n y)
      = 2 * (Real.pi : ℂ) ^ 2 * (((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ)
          * (c * (c - 1) * (y : ℂ) ^ (c - 2))) := by
    intro y hy
    have hy1 : a ≤ y := key hy
    have hmax : max y a = y := max_eq_left hy1
    have hstep : ∀ n : ℤ, G n y = (1 / (n : ℂ) ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
        (c * (c - 1) * (y : ℂ) ^ (c - 2)) := by
      intro n
      rw [hGapply n y, hmax]
    simp only [hstep]
    rw [show (∑' n : ℤ, (1 / (n : ℂ) ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
        (c * (c - 1) * (y : ℂ) ^ (c - 2)))
      = (∑' n : ℤ, (1 / (n : ℂ) ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ))) *
        (c * (c - 1) * (y : ℂ) ^ (c - 2)) from tsum_mul_right]
    rw [B2_fourier_tsum]
    ring
  have h1 : ∫ y in a..b, (∑' n : ℤ, G n y)
      = 2 * (Real.pi : ℂ) ^ 2 * ∫ y in a..b,
          ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ) * (c * (c - 1) * (y : ℂ) ^ (c - 2)) := by
    rw [intervalIntegral.integral_congr hident, intervalIntegral.integral_const_mul]
  have h2 : ∫ y in a..b, ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ)
        * (c * (c - 1) * (y : ℂ) ^ (c - 2))
      = (1 / (2 * (Real.pi : ℂ) ^ 2)) * ∫ y in a..b, (∑' n : ℤ, G n y) := by
    have hpi : (2 * (Real.pi : ℂ) ^ 2) ≠ 0 := by
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero two_ne_zero (pow_ne_zero 2 this)
    rw [h1, one_div, inv_mul_cancel_left₀ hpi]
  have hunf : ∀ (n : ℤ) (y : ℝ), y ∈ Set.uIcc a b → G n y
      = (1 / (n : ℂ) ^ 2) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ))
        * (c * (c - 1) * (y : ℂ) ^ (c - 2)) := by
    intro n y hy
    rw [hGapply n y, max_eq_left (key hy)]
  have hsum_eq : (∑' n : ℤ, ∫ y in a..b, (1 / (n : ℂ) ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
        (c * (c - 1) * (y : ℂ) ^ (c - 2)))
      = ∑' n : ℤ, ∫ y in a..b, G n y := by
    refine tsum_congr (fun n => ?_)
    exact intervalIntegral.integral_congr (fun y hy => (hunf n y hy).symm)
  rw [h2, hsum_eq]
  congr 1
  exact htsum.symm


/-! ============================================================================
## Third session (`W883c`, OMOS lomos 20261105T0944Z): the numerical assembly

Nothing here changes the lab file. `disc_bound` is the whole leaf
`fgm_discretization_error` with the explicit constant `500`.
-/

open Finset Real MeasureTheory intervalIntegral

/-! ### 1. The exponent, split into modulus and phase -/

private lemma cpow_sub_two_eq_exp (c : ℂ) (t : ℝ) (hre : c.re = -1 / 2) (him : c.im = -t)
    {y : ℝ} (hy : 0 < y) :
    (y : ℂ) ^ (c - 2) =
      ((y ^ (-5 / 2 : ℝ) : ℝ) : ℂ) * Complex.exp (Complex.I * (((-t) * Real.log y : ℝ) : ℂ)) := by
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hsplit : c - 2 = ((-5 / 2 : ℝ) : ℂ) + (((-t : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext
    · rw [Complex.sub_re, hre]; norm_num
    · rw [Complex.sub_im, him]; norm_num
  have hlog : Complex.log (y : ℂ) = ((Real.log y : ℝ) : ℂ) :=
    (Complex.ofReal_log hy.le).symm
  have him' : (y : ℂ) ^ (((-t : ℝ) : ℂ) * Complex.I)
      = Complex.exp (Complex.I * (((-t) * Real.log y : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hy0, hlog]
    congr 1
    push_cast
    ring
  rw [hsplit, Complex.cpow_add _ _ hy0,
    show (y : ℂ) ^ ((-5 / 2 : ℝ) : ℂ) = ((y ^ (-5 / 2 : ℝ) : ℝ) : ℂ) from
      (Complex.ofReal_cpow hy.le (-5 / 2)).symm, him']

private lemma mode_integrand_eq (c : ℂ) (t : ℝ) (hre : c.re = -1 / 2) (him : c.im = -t)
    {y : ℝ} (hy : 0 < y) (n : ℤ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) * (y : ℂ) ^ (c - 2)
      = ((y ^ (-5 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (((2 * Real.pi * (n : ℝ)) * y + (-t) * Real.log y : ℝ) : ℂ)) := by
  rw [cpow_sub_two_eq_exp c t hre him hy]
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ))
      = Complex.exp (Complex.I * (((2 * Real.pi * (n : ℝ)) * y : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [hexp,
    show Complex.I * (((2 * Real.pi * (n : ℝ)) * y + (-t) * Real.log y : ℝ) : ℂ)
        = Complex.I * (((2 * Real.pi * (n : ℝ)) * y : ℝ) : ℂ)
          + Complex.I * (((-t) * Real.log y : ℝ) : ℂ) from by
      push_cast
      ring,
    Complex.exp_add]
  ring

/-! ### 2. The per-mode bound -/

private lemma norm_exp_phase (μ t y : ℝ) :
    ‖Complex.exp (Complex.I * (((μ * y + t * Real.log y : ℝ)) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

private lemma mode_bound (c : ℂ) (t : ℝ) (hre : c.re = -1 / 2) (him : c.im = -t)
    (K K1 : ℕ) (hK : 1 ≤ K) (hKK1 : K ≤ K1) (hb4 : (K1 : ℝ) ≤ 4 * (K : ℝ))
    (ht2 : |t| ≤ 2 * (K : ℝ)) (n : ℤ) :
    ‖∫ y in (K : ℝ)..(K1 : ℝ), (1 / (n : ℂ) ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
        (c * (c - 1) * (y : ℂ) ^ (c - 2))‖
      ≤ (1 / (n : ℝ) ^ 2) * (‖c‖ * ‖c - 1‖ * (10 * (K : ℝ) ^ (-5 / 2 : ℝ))) := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hK1R : (K : ℝ) ≤ (K1 : ℝ) := by exact_mod_cast hKK1
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  -- pull the constants out
  have hpull : ∫ y in (K : ℝ)..(K1 : ℝ), (1 / (n : ℂ) ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
        (c * (c - 1) * (y : ℂ) ^ (c - 2))
      = ((1 / (n : ℂ) ^ 2) * (c * (c - 1))) *
        ∫ y in (K : ℝ)..(K1 : ℝ),
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
            (y : ℂ) ^ (c - 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun y _ => by ring)
  -- the oscillation bound on the pure exponential-power integral
  have hcore : ‖∫ y in (K : ℝ)..(K1 : ℝ),
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
        (y : ℂ) ^ (c - 2))‖ ≤ 10 * (K : ℝ) ^ (-5 / 2 : ℝ) := by
    have hcongr : ∫ y in (K : ℝ)..(K1 : ℝ),
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
          (y : ℂ) ^ (c - 2))
        = ∫ y in (K : ℝ)..(K1 : ℝ), (((y ^ (-5 / 2 : ℝ) : ℝ)) : ℂ) *
          Complex.exp (Complex.I * (((2 * Real.pi * (n : ℝ)) * y + (-t) * Real.log y : ℝ) : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le hK1R] at hy
      exact mode_integrand_eq c t hre him (by linarith [hy.1]) n
    rw [hcongr]
    refine osc_integral_bound hK0 hK1R hb4 ?_ ?_
    · have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hn
      have hpi3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
      have habs : |2 * Real.pi * (n : ℝ)| = 2 * Real.pi * |(n : ℝ)| := by
        rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
        norm_num
      rw [habs]
      nlinarith [Real.pi_pos, abs_nonneg (n : ℝ)]
    · simpa using ht2
  rw [hpull, norm_mul]
  have hcoef : ‖(1 / (n : ℂ) ^ 2) * (c * (c - 1))‖ = (1 / (n : ℝ) ^ 2) * (‖c‖ * ‖c - 1‖) := by
    rw [norm_mul, norm_mul, norm_one_div_sq_intCast]
  rw [hcoef]
  have hnn : (0 : ℝ) ≤ (1 / (n : ℝ) ^ 2) * (‖c‖ * ‖c - 1‖) := by
    have h1 : (0 : ℝ) < (n : ℝ) ^ 2 := by
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      positivity
    have := norm_nonneg c
    have := norm_nonneg (c - 1)
    positivity
  exact (mul_le_mul_of_nonneg_left hcore hnn).trans (le_of_eq (by ring))

/-! ### 3. The `ℤ`-sum bound `∑' n, 1/n² ≤ 4` -/

private lemma int_tsum_inv_sq_le_four : (∑' n : ℤ, (1 / (n : ℝ) ^ 2)) ≤ 4 := by
  have hsumm : Summable fun n : ℤ => (1 / (n : ℝ) ^ 2) := summable_one_div_sq_int
  have heven : Function.Even fun n : ℤ => (1 / (n : ℝ) ^ 2) := by
    intro n
    simp
  have hmain := tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsumm
  have hsucc : HasSum (fun k : ℕ => (1 / ((k + 1 : ℕ) : ℝ) ^ 2)) (Real.pi ^ 2 / 6) := by
    refine (hasSum_nat_add_iff (f := fun k : ℕ => (1 / (k : ℝ) ^ 2)) 1).2 ?_
    simpa using hasSum_zeta_two
  have hpnat : (∑' n : ℕ+, (1 / (((n : ℕ)) : ℝ) ^ 2)) = Real.pi ^ 2 / 6 := by
    rw [tsum_pnat_eq_tsum_succ (f := fun k : ℕ => (1 / (k : ℝ) ^ 2))]
    exact hsucc.tsum_eq
  have hcast : (∑' n : ℕ+, (1 / ((((n : ℤ)) : ℝ)) ^ 2))
      = (∑' n : ℕ+, (1 / (((n : ℕ)) : ℝ) ^ 2)) :=
    tsum_congr (fun n => by push_cast; ring)
  rw [hmain, hcast, hpnat, nsmul_eq_mul]
  have h0 : (1 / (((0 : ℤ)) : ℝ) ^ 2) = 0 := by norm_num
  rw [h0, zero_add]
  have hp2 : Real.pi ^ 2 < 10 := by
    have h := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  nlinarith

/-! ### 4. The complex constants -/

private lemma norm_two_pi_sq_complex : ‖(2 : ℂ) * (Real.pi : ℂ) ^ 2‖ = 2 * Real.pi ^ 2 := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  norm_num

private lemma norm_one_div_two_pi_sq :
    ‖(1 : ℂ) / (2 * (Real.pi : ℂ) ^ 2)‖ = 1 / (2 * Real.pi ^ 2) := by
  rw [norm_div, norm_one, norm_two_pi_sq_complex]

/-! ### 5. The Bernoulli-weighted integral, bounded by `4 * M` -/

set_option maxHeartbeats 1000000 in
private lemma bern_integral_bound (c : ℂ) (t : ℝ) (hre : c.re = -1 / 2) (him : c.im = -t)
    (hc2 : c - 2 ≠ 0) (K K1 : ℕ) (hK : 1 ≤ K) (hKK1 : K ≤ K1)
    (hb4 : (K1 : ℝ) ≤ 4 * (K : ℝ)) (ht2 : |t| ≤ 2 * (K : ℝ)) :
    ‖∫ y in (K : ℝ)..(K1 : ℝ), ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ) *
        (c * (c - 1) * (y : ℂ) ^ (c - 2))‖
      ≤ 4 * (‖c‖ * ‖c - 1‖ * (10 * (K : ℝ) ^ (-5 / 2 : ℝ))) := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hK1R : (K : ℝ) ≤ (K1 : ℝ) := by exact_mod_cast hKK1
  set M : ℝ := ‖c‖ * ‖c - 1‖ * (10 * (K : ℝ) ^ (-5 / 2 : ℝ)) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hMsum : Summable fun n : ℤ => (1 / (n : ℝ) ^ 2) * M :=
    summable_one_div_sq_int.mul_right M
  have hper : ∀ n : ℤ,
      ‖∫ y in (K : ℝ)..(K1 : ℝ), (1 / (n : ℂ) ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
        (c * (c - 1) * (y : ℂ) ^ (c - 2))‖ ≤ (1 / (n : ℝ) ^ 2) * M := by
    intro n
    rw [hM]
    exact mode_bound c t hre him K K1 hK hKK1 hb4 ht2 n
  have hsummF : Summable fun n : ℤ =>
      ‖∫ y in (K : ℝ)..(K1 : ℝ), (1 / (n : ℂ) ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
        (c * (c - 1) * (y : ℂ) ^ (c - 2))‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hper hMsum
  have htsum : (∑' n : ℤ, ‖∫ y in (K : ℝ)..(K1 : ℝ), (1 / (n : ℂ) ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
        (c * (c - 1) * (y : ℂ) ^ (c - 2))‖) ≤ 4 * M := by
    have h1 : (∑' n : ℤ, ‖∫ y in (K : ℝ)..(K1 : ℝ), (1 / (n : ℂ) ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
        (c * (c - 1) * (y : ℂ) ^ (c - 2))‖) ≤ ∑' n : ℤ, (1 / (n : ℝ) ^ 2) * M :=
      Summable.tsum_le_tsum hper hsummF hMsum
    have h2 : (∑' n : ℤ, (1 / (n : ℝ) ^ 2) * M) = (∑' n : ℤ, (1 / (n : ℝ) ^ 2)) * M :=
      tsum_mul_right
    have h3 : (∑' n : ℤ, (1 / (n : ℝ) ^ 2)) ≤ 4 := int_tsum_inv_sq_le_four
    calc (∑' n : ℤ, ‖∫ y in (K : ℝ)..(K1 : ℝ), (1 / (n : ℂ) ^ 2) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
          (c * (c - 1) * (y : ℂ) ^ (c - 2))‖)
        ≤ ∑' n : ℤ, (1 / (n : ℝ) ^ 2) * M := h1
      _ = (∑' n : ℤ, (1 / (n : ℝ) ^ 2)) * M := h2
      _ ≤ 4 * M := mul_le_mul_of_nonneg_right h3 hM0
  have hid := integral_B2_fourier (c := c) (a := (K : ℝ)) (b := (K1 : ℝ)) hK0 hK1R hre hc2
  rw [hid, norm_mul, norm_one_div_two_pi_sq]
  have hnorm : ‖∑' n : ℤ, ∫ y in (K : ℝ)..(K1 : ℝ), (1 / (n : ℂ) ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
        (c * (c - 1) * (y : ℂ) ^ (c - 2))‖ ≤ 4 * M :=
    (norm_tsum_le_tsum_norm hsummF).trans htsum
  have hcoef : 1 / (2 * Real.pi ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hstep : 1 / (2 * Real.pi ^ 2) * ‖∑' n : ℤ, ∫ y in (K : ℝ)..(K1 : ℝ), (1 / (n : ℂ) ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (y : ℂ)) *
        (c * (c - 1) * (y : ℂ) ^ (c - 2))‖ ≤ 1 * (4 * M) :=
    mul_le_mul hcoef hnorm (norm_nonneg _) (by norm_num)
  rw [hM] at hstep ⊢
  linarith

/-! ### 6. Scaling `K^{-q}` against `N^{-q}` when `N ≤ 2K` -/

private lemma rpow_neg_le_of_le_two_mul {N K : ℝ} (hN : 0 < N) (hK : 0 < K) (h : N ≤ 2 * K)
    {q : ℝ} (hq : 0 ≤ q) {m : ℝ} (hm : (2 : ℝ) ^ q ≤ m) :
    K ^ (-q) ≤ m * N ^ (-q) := by
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) q
  have hm0 : 0 ≤ m := le_trans h2pos.le hm
  have h1 : (2 * K) ^ (-q) ≤ N ^ (-q) := Real.rpow_le_rpow_of_nonpos hN h (by linarith)
  have h3 : (2 * K) ^ (-q) = (2 : ℝ) ^ (-q) * K ^ (-q) := Real.mul_rpow (by norm_num) hK.le
  have h4 : (2 : ℝ) ^ q * (2 : ℝ) ^ (-q) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hqeq : K ^ (-q) = (2 : ℝ) ^ q * ((2 * K) ^ (-q)) := by
    rw [h3, show (2 : ℝ) ^ q * ((2 : ℝ) ^ (-q) * K ^ (-q))
        = ((2 : ℝ) ^ q * (2 : ℝ) ^ (-q)) * K ^ (-q) by ring, h4, one_mul]
  rw [hqeq]
  calc (2 : ℝ) ^ q * (2 * K) ^ (-q) ≤ m * ((2 * K) ^ (-q)) :=
        mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (by positivity) (-q))
    _ ≤ m * N ^ (-q) := mul_le_mul_of_nonneg_left h1 hm0

private lemma sqrt_two_le_three_halves : Real.sqrt 2 ≤ 3 / 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

private lemma two_rpow_half_le : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
  rw [← Real.sqrt_eq_rpow]
  linarith [sqrt_two_le_three_halves]

private lemma two_rpow_three_halves_le : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 3 := by
  have h : (2 : ℝ) ^ (3 / 2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) * 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one]
  rw [h, ← Real.sqrt_eq_rpow]
  nlinarith [sqrt_two_le_three_halves]

private lemma two_rpow_five_halves_le : (2 : ℝ) ^ (5 / 2 : ℝ) ≤ 6 := by
  have h : (2 : ℝ) ^ (5 / 2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) * 4 := by
    rw [show (5 / 2 : ℝ) = 1 / 2 + 2 by norm_num, Real.rpow_add (by norm_num)]
    norm_num
  rw [h, ← Real.sqrt_eq_rpow]
  nlinarith [sqrt_two_le_three_halves]

private lemma intervalIntegrable_cpow_any (c : ℂ) (hc : c ≠ 0) {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    IntervalIntegrable (fun y : ℝ => (y : ℂ) ^ c) volume a b := by
  rcases le_total a b with h | h
  · exact intervalIntegrable_cpow c hc (by linarith) h
  · exact (intervalIntegrable_cpow c hc (by linarith) h).symm

private lemma norm_three_le (a b c : ℂ) : ‖a + b + (-c)‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have h := norm_add_le (a + b) (-c)
  have h5 : ‖(-c : ℂ)‖ = ‖c‖ := norm_neg c
  rw [h5] at h
  have h4 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  linarith

private lemma norm_five_le (a b c d e : ℂ) :
    ‖a + b + (-c) + d + (-e)‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  have h5 : ‖(-c : ℂ)‖ = ‖c‖ := norm_neg c
  have h6 : ‖(-e : ℂ)‖ = ‖e‖ := norm_neg e
  have h1 : ‖a + b + (-c) + d + (-e)‖ ≤ ‖a + b + (-c) + d‖ + ‖e‖ := by
    have := norm_add_le (a + b + (-c) + d) (-e)
    simpa [h6] using this
  have h2 : ‖a + b + (-c) + d‖ ≤ ‖a + b + (-c)‖ + ‖d‖ := norm_add_le _ _
  have h3 : ‖a + b + (-c)‖ ≤ ‖a + b‖ + ‖c‖ := by
    have := norm_add_le (a + b) (-c)
    simpa [h5] using this
  have h4 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
  linarith

/-! ### 7. The leaf -/

set_option maxHeartbeats 1000000 in
private theorem disc_bound (N N1 t : ℝ) (hN : 1 ≤ N) (hNN1 : N ≤ N1) (hN1le : N1 ≤ 2 * N)
    (ht : |t| ≤ N) :
    ‖(∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, (n : ℂ) ^ (-(t : ℂ) * Complex.I) * (n : ℂ) ^ (-1 / 2 : ℂ)) -
      ∫ y in N..N1, (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I)‖
      ≤ 500 * N ^ (-1 / 2 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hR : (0 : ℝ) ≤ N ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hN0.le _
  let c : ℂ := (-1 / 2 : ℂ) + (-(t : ℂ) * Complex.I)
  have hcre : c.re = -1 / 2 := by simp [c]
  have hcim : c.im = -t := by simp [c]
  have hcne : c ≠ 0 := by
    intro h
    have h1 : c.re = 0 := by rw [h]; simp
    rw [hcre] at h1; norm_num at h1
  have hc1ne : c - 1 ≠ 0 := by
    intro h
    have h1 : (c - 1).re = 0 := by rw [h]; simp
    have h2 : (c - 1).re = c.re - 1 := by simp
    rw [h2, hcre] at h1; norm_num at h1
  have hc2ne : c - 2 ≠ 0 := by
    intro h
    have h1 : (c - 2).re = 0 := by rw [h]; simp
    have h2 : (c - 2).re = c.re - 2 := by simp
    rw [h2, hcre] at h1; norm_num at h1
  set f : ℝ → ℂ := fun y => (y : ℂ) ^ c with hfdef
  set f' : ℝ → ℂ := fun y => c * (y : ℂ) ^ (c - 1) with hfdef'
  set f'' : ℝ → ℂ := fun y => c * (c - 1) * (y : ℂ) ^ (c - 2) with hfdef''
  -- floor data
  have hK : 1 ≤ ⌊N⌋₊ := Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ N by exact_mod_cast hN)
  have hKK1 : ⌊N⌋₊ ≤ ⌊N1⌋₊ := Nat.floor_mono hNN1
  have hKR : ((⌊N⌋₊ : ℕ) : ℝ) ≤ N := Nat.floor_le (by linarith)
  have hKN : N < ((⌊N⌋₊ : ℕ) : ℝ) + 1 := by
    have := Nat.lt_floor_add_one N; simpa using this
  have hK1R : ((⌊N1⌋₊ : ℕ) : ℝ) ≤ N1 := Nat.floor_le (by linarith)
  have hK1N : N1 < ((⌊N1⌋₊ : ℕ) : ℝ) + 1 := by
    have := Nat.lt_floor_add_one N1; simpa using this
  have hK0 : (0 : ℝ) < ((⌊N⌋₊ : ℕ) : ℝ) := by exact_mod_cast hK
  have hKnat : (1 : ℝ) ≤ ((⌊N⌋₊ : ℕ) : ℝ) := by exact_mod_cast hK
  have hK1pos : (1 : ℝ) ≤ ((⌊N1⌋₊ : ℕ) : ℝ) := by
    have h : 1 ≤ ⌊N1⌋₊ := le_trans hK hKK1
    exact_mod_cast h
  have hN2K : N ≤ 2 * ((⌊N⌋₊ : ℕ) : ℝ) := by linarith
  have ht2 : |t| ≤ 2 * ((⌊N⌋₊ : ℕ) : ℝ) := by nlinarith [abs_nonneg t]
  have hb4 : ((⌊N1⌋₊ : ℕ) : ℝ) ≤ 4 * ((⌊N⌋₊ : ℕ) : ℝ) := by
    have h1 : ((⌊N1⌋₊ : ℕ) : ℝ) ≤ 2 * N := by linarith
    linarith
  have hKK1R : ((⌊N⌋₊ : ℕ) : ℝ) ≤ ((⌊N1⌋₊ : ℕ) : ℝ) := by exact_mod_cast hKK1
  -- summand and integrand
  have hsummand : ∀ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊,
      (n : ℂ) ^ (-(t : ℂ) * Complex.I) * (n : ℂ) ^ (-1 / 2 : ℂ) = f n := by
    intro n hn
    have hn1 : 1 ≤ n := by
      have h2 := (mem_Ioc.mp hn).1
      omega
    have hn0 : (n : ℂ) ≠ 0 := by
      have h : (0 : ℝ) < n := by exact_mod_cast hn1
      exact Complex.ofReal_ne_zero.mpr h.ne'
    show _ = (n : ℂ) ^ c
    rw [mul_comm, ← Complex.cpow_add _ _ hn0]
  have hintmand : ∫ y in N..N1, (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I)
      = ∫ y in N..N1, f y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hNN1] at hy
    have hy0 : 0 < y := by linarith [hy.1]
    have hy0c : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy0.ne'
    show _ = (y : ℂ) ^ c
    dsimp only
    rw [← Complex.cpow_add _ _ hy0c]
  -- smoothness for Euler–Maclaurin
  have hf : ∀ y ∈ Set.Ici (1 : ℝ), HasDerivAt f (f' y) y := by
    intro y hy
    have hy0 : y ≠ 0 := by
      have h : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
      exact h.ne'
    exact hasDerivAt_ofReal_cpow_const hy0 hcne
  have hf' : ∀ y ∈ Set.Ici (1 : ℝ), HasDerivAt f' (f'' y) y := by
    intro y hy
    have hy0 : y ≠ 0 := by
      have h : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
      exact h.ne'
    have h := (hasDerivAt_ofReal_cpow_const (r := c - 1) hy0 hc1ne).const_mul c
    have hsub : (c - 1) - 1 = c - 2 := by ring
    rw [hsub] at h
    simpa [hfdef', hfdef'', mul_assoc] using h
  have hfint : ∀ n ∈ Ico ⌊N⌋₊ ⌊N1⌋₊, IntervalIntegrable f volume (n : ℝ) ((n : ℝ) + 1) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have h : 1 ≤ n := le_trans hK (mem_Ico.mp hn).1
      exact_mod_cast h
    exact intervalIntegrable_cpow c hcne (by linarith) (by linarith)
  have hf'int : ∀ n ∈ Ico ⌊N⌋₊ ⌊N1⌋₊, IntervalIntegrable f' volume (n : ℝ) ((n : ℝ) + 1) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have h : 1 ≤ n := le_trans hK (mem_Ico.mp hn).1
      exact_mod_cast h
    have h := intervalIntegrable_cpow (c - 1) hc1ne (a := (n : ℝ)) (b := (n : ℝ) + 1)
      (by linarith) (by linarith)
    simpa [hfdef'] using h.const_mul c
  have hf''int : ∀ n ∈ Ico ⌊N⌋₊ ⌊N1⌋₊, IntervalIntegrable f'' volume (n : ℝ) ((n : ℝ) + 1) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have h : 1 ≤ n := le_trans hK (mem_Ico.mp hn).1
      exact_mod_cast h
    have h := intervalIntegrable_cpow (c - 2) hc2ne (a := (n : ℝ)) (b := (n : ℝ) + 1)
      (by linarith) (by linarith)
    simpa [hfdef''] using h.const_mul (c * (c - 1))
  have hQint : ∀ n ∈ Ico ⌊N⌋₊ ⌊N1⌋₊,
      IntervalIntegrable (fun y => ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ) * f'' y)
        volume (n : ℝ) ((n : ℝ) + 1) := by
    intro n hn
    have hn1 : 1 ≤ n := le_trans hK (mem_Ico.mp hn).1
    simpa [hfdef''] using intervalIntegrable_B2_fract c hc2ne n hn1
  have hEL := em2_block f f' f'' ⌊N⌋₊ ⌊N1⌋₊ hK hKK1 hf hf' hfint hf'int hf''int hQint
  -- the signed split of the integral
  have hint_any : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → IntervalIntegrable f volume a b :=
    fun a b ha hb => intervalIntegrable_cpow_any c hcne ha hb
  -- norms of the pieces
  have hnormK : ‖f ((⌊N⌋₊ : ℕ) : ℝ)‖ = ((⌊N⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) := by
    show ‖((((⌊N⌋₊ : ℕ) : ℝ)) : ℂ) ^ c‖ = _
    rw [norm_cpow_eq (by linarith), hcre]
  have hnormK1 : ‖f ((⌊N1⌋₊ : ℕ) : ℝ)‖ = ((⌊N1⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) := by
    show ‖((((⌊N1⌋₊ : ℕ) : ℝ)) : ℂ) ^ c‖ = _
    rw [norm_cpow_eq (by linarith), hcre]
  have hnormK' : ‖f' ((⌊N⌋₊ : ℕ) : ℝ)‖ = ‖c‖ * ((⌊N⌋₊ : ℕ) : ℝ) ^ (-3 / 2 : ℝ) := by
    show ‖c * ((((⌊N⌋₊ : ℕ) : ℝ)) : ℂ) ^ (c - 1)‖ = _
    rw [norm_mul, norm_cpow_eq (by linarith)]
    congr 1
    rw [show (c - 1).re = -3 / 2 by rw [Complex.sub_re, hcre]; norm_num]
  have hnormK1' : ‖f' ((⌊N1⌋₊ : ℕ) : ℝ)‖ = ‖c‖ * ((⌊N1⌋₊ : ℕ) : ℝ) ^ (-3 / 2 : ℝ) := by
    show ‖c * ((((⌊N1⌋₊ : ℕ) : ℝ)) : ℂ) ^ (c - 1)‖ = _
    rw [norm_mul, norm_cpow_eq (by linarith)]
    congr 1
    rw [show (c - 1).re = -3 / 2 by rw [Complex.sub_re, hcre]; norm_num]
  -- scaling
  have hscale1 : ((⌊N⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) ≤ 2 * N ^ (-1 / 2 : ℝ) := by
    have h := rpow_neg_le_of_le_two_mul (q := (1 / 2 : ℝ)) hN0 hK0 hN2K (by norm_num)
      two_rpow_half_le
    simpa [neg_div] using h
  have hscale3 : ((⌊N⌋₊ : ℕ) : ℝ) ^ (-3 / 2 : ℝ) ≤ 3 * N ^ (-3 / 2 : ℝ) := by
    have h := rpow_neg_le_of_le_two_mul (q := (3 / 2 : ℝ)) hN0 hK0 hN2K (by norm_num)
      two_rpow_three_halves_le
    simpa [neg_div] using h
  have hscale5 : ((⌊N⌋₊ : ℕ) : ℝ) ^ (-5 / 2 : ℝ) ≤ 6 * N ^ (-5 / 2 : ℝ) := by
    have h := rpow_neg_le_of_le_two_mul (q := (5 / 2 : ℝ)) hN0 hK0 hN2K (by norm_num)
      two_rpow_five_halves_le
    simpa [neg_div] using h
  -- bounds on `c`
  have hc_bound : ‖c‖ ≤ N + 1 / 2 := by
    have h1 : ‖c‖ ≤ |c.re| + |c.im| := Complex.norm_le_abs_re_add_abs_im c
    rw [hcre, hcim, abs_neg] at h1
    have h2 : |(-1 / 2 : ℝ)| = 1 / 2 := by norm_num
    rw [h2] at h1
    linarith
  have hc1_bound : ‖c - 1‖ ≤ N + 3 / 2 := by
    have h1 : ‖c - 1‖ ≤ |(c - 1).re| + |(c - 1).im| := Complex.norm_le_abs_re_add_abs_im (c - 1)
    have hre1 : (c - 1).re = -3 / 2 := by rw [Complex.sub_re, hcre]; norm_num
    have him1 : (c - 1).im = -t := by rw [Complex.sub_im, hcim]; simp
    rw [hre1, him1, abs_neg] at h1
    have h2 : |(-3 / 2 : ℝ)| = 3 / 2 := by norm_num
    rw [h2] at h1
    linarith
  -- P1
  have hP1 : ‖(f ((⌊N1⌋₊ : ℕ) : ℝ) - f ((⌊N⌋₊ : ℕ) : ℝ)) / 2‖ ≤ 2 * N ^ (-1 / 2 : ℝ) := by
    have h1 : ‖f ((⌊N1⌋₊ : ℕ) : ℝ) - f ((⌊N⌋₊ : ℕ) : ℝ)‖ ≤
        ((⌊N1⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) + ((⌊N⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) := by
      refine (norm_sub_le _ _).trans ?_
      rw [hnormK1, hnormK]
    have h2 : ((⌊N1⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) ≤ ((⌊N⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hK0 hKK1R (by norm_num)
    have hsum : ‖f ((⌊N1⌋₊ : ℕ) : ℝ) - f ((⌊N⌋₊ : ℕ) : ℝ)‖
        ≤ 2 * ((⌊N⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) := by linarith
    have hfin : 2 * ((⌊N⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) ≤ 2 * (2 * N ^ (-1 / 2 : ℝ)) := by
      linarith
    rw [norm_div]
    have h3 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h3]
    linarith
  -- P2
  have hP2 : ‖(f' ((⌊N1⌋₊ : ℕ) : ℝ) - f' ((⌊N⌋₊ : ℕ) : ℝ)) / 12‖ ≤ 1 * N ^ (-1 / 2 : ℝ) := by
    have h1 : ‖f' ((⌊N1⌋₊ : ℕ) : ℝ) - f' ((⌊N⌋₊ : ℕ) : ℝ)‖ ≤
        ‖c‖ * ((⌊N1⌋₊ : ℕ) : ℝ) ^ (-3 / 2 : ℝ) + ‖c‖ * ((⌊N⌋₊ : ℕ) : ℝ) ^ (-3 / 2 : ℝ) := by
      refine (norm_sub_le _ _).trans ?_
      rw [hnormK1', hnormK']
    have h2 : ((⌊N1⌋₊ : ℕ) : ℝ) ^ (-3 / 2 : ℝ) ≤ ((⌊N⌋₊ : ℕ) : ℝ) ^ (-3 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hK0 hKK1R (by norm_num)
    have hK3 : (0 : ℝ) ≤ ((⌊N⌋₊ : ℕ) : ℝ) ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hK0.le _
    have hN3 : (0 : ℝ) ≤ N ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hN0.le _
    rw [norm_div]
    have h3 : ‖(12 : ℂ)‖ = 12 := by norm_num
    rw [h3]
    have hc0 : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
    have h4 : ‖c‖ * ((⌊N⌋₊ : ℕ) : ℝ) ^ (-3 / 2 : ℝ) ≤ (N + 1 / 2) * (3 * N ^ (-3 / 2 : ℝ)) :=
      mul_le_mul hc_bound hscale3 hK3 (by linarith)
    have h5 : (N + 1 / 2) * (3 * N ^ (-3 / 2 : ℝ)) ≤ (9 / 2) * N ^ (-1 / 2 : ℝ) := by
      have h6 : N * N ^ (-3 / 2 : ℝ) = N ^ (-1 / 2 : ℝ) := by
        have h7 : N ^ (((1 : ℕ) : ℝ)) * N ^ (-3 / 2 : ℝ)
            = N ^ ((((1 : ℕ) : ℝ)) + (-3 / 2) : ℝ) :=
          (Real.rpow_add hN0 (((1 : ℕ) : ℝ)) (-3 / 2)).symm
        have h8 : N * N ^ (-3 / 2 : ℝ) = N ^ (((1 : ℕ) : ℝ)) * N ^ (-3 / 2 : ℝ) := by
          rw [Real.rpow_natCast, pow_one]
        rw [h8, h7]
        norm_num
      have hNle : N + 1 / 2 ≤ (3 / 2) * N := by linarith
      calc (N + 1 / 2) * (3 * N ^ (-3 / 2 : ℝ)) ≤ ((3 / 2) * N) * (3 * N ^ (-3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right hNle (by positivity)
        _ = (9 / 2) * (N * N ^ (-3 / 2 : ℝ)) := by ring
        _ = (9 / 2) * N ^ (-1 / 2 : ℝ) := by rw [h6]
    have hAa : ‖c‖ * ((⌊N1⌋₊ : ℕ) : ℝ) ^ (-3 / 2 : ℝ)
        ≤ ‖c‖ * ((⌊N⌋₊ : ℕ) : ℝ) ^ (-3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left h2 hc0
    have hsum : ‖f' ((⌊N1⌋₊ : ℕ) : ℝ) - f' ((⌊N⌋₊ : ℕ) : ℝ)‖
        ≤ 2 * (‖c‖ * ((⌊N⌋₊ : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) := by linarith
    have hfour : ‖c‖ * ((⌊N⌋₊ : ℕ) : ℝ) ^ (-3 / 2 : ℝ) ≤ (9 / 2) * N ^ (-1 / 2 : ℝ) :=
      h4.trans h5
    linarith
  -- P3
  have hP3 : ‖(1 / 2) * ∫ y in ((⌊N⌋₊ : ℕ) : ℝ)..((⌊N1⌋₊ : ℕ) : ℝ),
      ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ) * f'' y‖ ≤ 450 * N ^ (-1 / 2 : ℝ) := by
    have hb := bern_integral_bound c t hcre hcim hc2ne ⌊N⌋₊ ⌊N1⌋₊ hK hKK1 hb4 ht2
    have hMle : ‖c‖ * ‖c - 1‖ * (10 * ((⌊N⌋₊ : ℕ) : ℝ) ^ (-5 / 2 : ℝ))
        ≤ 225 * N ^ (-1 / 2 : ℝ) := by
      have hK5 : (0 : ℝ) ≤ ((⌊N⌋₊ : ℕ) : ℝ) ^ (-5 / 2 : ℝ) := Real.rpow_nonneg hK0.le _
      have hN5 : (0 : ℝ) ≤ N ^ (-5 / 2 : ℝ) := Real.rpow_nonneg hN0.le _
      have hcc : ‖c‖ * ‖c - 1‖ ≤ (N + 1 / 2) * (N + 3 / 2) :=
        mul_le_mul hc_bound hc1_bound (norm_nonneg _) (by linarith)
      have hcc2 : (N + 1 / 2) * (N + 3 / 2) ≤ (15 / 4) * N ^ 2 := by nlinarith [hR]
      have hcc3 : ‖c‖ * ‖c - 1‖ ≤ (15 / 4) * N ^ 2 := hcc.trans hcc2
      have h5b : (10 : ℝ) * ((⌊N⌋₊ : ℕ) : ℝ) ^ (-5 / 2 : ℝ) ≤ 10 * (6 * N ^ (-5 / 2 : ℝ)) := by
        linarith
      have hcomb : ‖c‖ * ‖c - 1‖ * (10 * ((⌊N⌋₊ : ℕ) : ℝ) ^ (-5 / 2 : ℝ))
          ≤ ((15 / 4) * N ^ 2) * (10 * (6 * N ^ (-5 / 2 : ℝ))) :=
        mul_le_mul hcc3 h5b (by positivity) (by positivity)
      have hEq : ((15 / 4) * N ^ 2) * (10 * (6 * N ^ (-5 / 2 : ℝ))) = 225 * N ^ (-1 / 2 : ℝ) := by
        have h6 : (N : ℝ) ^ 2 * N ^ (-5 / 2 : ℝ) = N ^ (-1 / 2 : ℝ) := by
          have h7 : N ^ (((2 : ℕ) : ℝ)) * N ^ (-5 / 2 : ℝ)
              = N ^ ((((2 : ℕ) : ℝ)) + (-5 / 2) : ℝ) :=
            (Real.rpow_add hN0 (((2 : ℕ) : ℝ)) (-5 / 2)).symm
          have h8 : (N : ℝ) ^ 2 * N ^ (-5 / 2 : ℝ)
              = N ^ (((2 : ℕ) : ℝ)) * N ^ (-5 / 2 : ℝ) := by
            rw [Real.rpow_natCast]
          rw [h8, h7]
          norm_num
        calc ((15 / 4) * N ^ 2) * (10 * (6 * N ^ (-5 / 2 : ℝ)))
            = 225 * ((N : ℝ) ^ 2 * N ^ (-5 / 2 : ℝ)) := by ring
          _ = 225 * N ^ (-1 / 2 : ℝ) := by rw [h6]
      linarith [hcomb, hEq]
    rw [norm_mul]
    have h3 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h3]
    nlinarith [hb, hMle]
  -- P4, P5
  have hP4 : ‖∫ y in ((⌊N⌋₊ : ℕ) : ℝ)..N, f y‖ ≤ 2 * N ^ (-1 / 2 : ℝ) := by
    have hpt : ∀ᵐ y ∂(volume : MeasureTheory.Measure ℝ),
        y ∈ Set.uIoc ((⌊N⌋₊ : ℕ) : ℝ) N → ‖f y‖ ≤ ((⌊N⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) := by
      filter_upwards with y hy
      rw [Set.uIoc_of_le hKR] at hy
      have hy0 : 0 < y := by linarith [hy.1]
      show ‖(y : ℂ) ^ c‖ ≤ _
      rw [norm_cpow_eq hy0, hcre]
      exact Real.rpow_le_rpow_of_nonpos hK0 hy.1.le (by norm_num)
    have hmain := intervalIntegral.norm_integral_le_of_norm_le_const_ae hpt
    have hlen : |N - ((⌊N⌋₊ : ℕ) : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hKv : (0 : ℝ) ≤ ((⌊N⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hK0.le _
    calc ‖∫ y in ((⌊N⌋₊ : ℕ) : ℝ)..N, f y‖
        ≤ ((⌊N⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) * |N - ((⌊N⌋₊ : ℕ) : ℝ)| := hmain
      _ ≤ ((⌊N⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hlen hKv
      _ ≤ 2 * N ^ (-1 / 2 : ℝ) := by rw [mul_one]; exact hscale1
  have hP5 : ‖∫ y in ((⌊N1⌋₊ : ℕ) : ℝ)..N1, f y‖ ≤ 2 * N ^ (-1 / 2 : ℝ) := by
    have hK10 : (0 : ℝ) < ((⌊N1⌋₊ : ℕ) : ℝ) := by linarith
    have hpt : ∀ᵐ y ∂(volume : MeasureTheory.Measure ℝ),
        y ∈ Set.uIoc ((⌊N1⌋₊ : ℕ) : ℝ) N1 →
          ‖f y‖ ≤ ((⌊N1⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) := by
      filter_upwards with y hy
      rw [Set.uIoc_of_le hK1R] at hy
      have hy0 : 0 < y := by linarith [hy.1]
      show ‖(y : ℂ) ^ c‖ ≤ _
      rw [norm_cpow_eq hy0, hcre]
      exact Real.rpow_le_rpow_of_nonpos hK10 hy.1.le (by norm_num)
    have hmain := intervalIntegral.norm_integral_le_of_norm_le_const_ae hpt
    have hlen : |N1 - ((⌊N1⌋₊ : ℕ) : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hK1v : (0 : ℝ) ≤ ((⌊N1⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hK10.le _
    have hmono : ((⌊N1⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) ≤ ((⌊N⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hK0 hKK1R (by norm_num)
    calc ‖∫ y in ((⌊N1⌋₊ : ℕ) : ℝ)..N1, f y‖
        ≤ ((⌊N1⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) * |N1 - ((⌊N1⌋₊ : ℕ) : ℝ)| := hmain
      _ ≤ ((⌊N1⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hlen hK1v
      _ ≤ 2 * N ^ (-1 / 2 : ℝ) := by
          rw [mul_one]
          exact hmono.trans hscale1
  -- the Euler–Maclaurin part
  have hEL' : (∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, f n)
        - ∫ y in ((⌊N⌋₊ : ℕ) : ℝ)..((⌊N1⌋₊ : ℕ) : ℝ), f y
      = (f ((⌊N1⌋₊ : ℕ) : ℝ) - f ((⌊N⌋₊ : ℕ) : ℝ)) / 2
        + (f' ((⌊N1⌋₊ : ℕ) : ℝ) - f' ((⌊N⌋₊ : ℕ) : ℝ)) / 12
        + (-((1 / 2) * ∫ y in ((⌊N⌋₊ : ℕ) : ℝ)..((⌊N1⌋₊ : ℕ) : ℝ),
            ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ) * f'' y)) := by
    rw [hEL]
    abel
  have hbEL : ‖(∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, f n)
        - ∫ y in ((⌊N⌋₊ : ℕ) : ℝ)..((⌊N1⌋₊ : ℕ) : ℝ), f y‖
      ≤ 2 * N ^ (-1 / 2 : ℝ) + 1 * N ^ (-1 / 2 : ℝ) + 450 * N ^ (-1 / 2 : ℝ) := by
    rw [hEL']
    have htri := norm_three_le ((f ((⌊N1⌋₊ : ℕ) : ℝ) - f ((⌊N⌋₊ : ℕ) : ℝ)) / 2)
      ((f' ((⌊N1⌋₊ : ℕ) : ℝ) - f' ((⌊N⌋₊ : ℕ) : ℝ)) / 12)
      ((1 / 2) * ∫ y in ((⌊N⌋₊ : ℕ) : ℝ)..((⌊N1⌋₊ : ℕ) : ℝ),
        ((bernoulliFun 2 (Int.fract y) : ℝ) : ℂ) * f'' y)
    have h1 := hP1
    have h2 := hP2
    have h3 := hP3
    linarith
  -- assemble
  have hc1' : c + 1 ≠ 0 := by
    intro h
    have h1 : (c + 1).re = 0 := by rw [h]; simp
    have h2 : (c + 1).re = c.re + 1 := by simp
    rw [h2, hcre] at h1; norm_num at h1
  -- fundamental-theorem bound: `‖q^(c+1) - p^(c+1)‖ ≤ ‖c+1‖ p^(-1/2)` on a unit interval
  have hFTC : ∀ p q : ℝ, 1 ≤ p → p ≤ q → q ≤ p + 1 →
      ‖(q : ℂ) ^ (c + 1) - (p : ℂ) ^ (c + 1)‖ ≤ ‖c + 1‖ * p ^ (-1 / 2 : ℝ) := by
    intro p q hp hpq hq
    have hp0 : (0 : ℝ) < p := by linarith
    have hderiv : ∀ x ∈ Set.uIcc p q,
        HasDerivAt (fun y : ℝ => (y : ℂ) ^ (c + 1)) ((c + 1) * (x : ℂ) ^ c) x := by
      intro x hx
      rw [Set.uIcc_of_le hpq] at hx
      have hx0 : x ≠ 0 := by
        have : (0 : ℝ) < x := by linarith [hx.1]
        exact this.ne'
      simpa using hasDerivAt_ofReal_cpow_const hx0 hc1'
    have hint : IntervalIntegrable (fun x : ℝ => (c + 1) * (x : ℂ) ^ c) volume p q :=
      (intervalIntegrable_cpow c hcne (by linarith) hpq).const_mul ((c + 1))
    have hftc := integral_eq_sub_of_hasDerivAt hderiv hint
    rw [← hftc]
    have hpt : ∀ᵐ x ∂(volume : MeasureTheory.Measure ℝ), x ∈ Set.uIoc p q →
        ‖((c + 1) * (x : ℂ) ^ c)‖ ≤ ‖c + 1‖ * p ^ (-1 / 2 : ℝ) := by
      filter_upwards with x hx
      rw [Set.uIoc_of_le hpq] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      rw [norm_mul, norm_cpow_eq hx0, hcre]
      have hle : x ^ (-1 / 2 : ℝ) ≤ p ^ (-1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hp0 hx.1.le (by norm_num)
      exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    have hmain := intervalIntegral.norm_integral_le_of_norm_le_const_ae hpt
    have hlen : |q - p| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hC : (0 : ℝ) ≤ ‖c + 1‖ * p ^ (-1 / 2 : ℝ) := by positivity
    calc ‖∫ x in p..q, (c + 1) * (x : ℂ) ^ c‖
        ≤ ‖c + 1‖ * p ^ (-1 / 2 : ℝ) * |q - p| := hmain
      _ ≤ ‖c + 1‖ * p ^ (-1 / 2 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hlen hC
      _ = ‖c + 1‖ * p ^ (-1 / 2 : ℝ) := by ring
  -- closed forms
  have hIKK1 : ∫ y in ((⌊N⌋₊ : ℕ) : ℝ)..((⌊N1⌋₊ : ℕ) : ℝ), f y
      = ((((⌊N1⌋₊ : ℕ) : ℝ) : ℂ) ^ (c + 1) - (((⌊N⌋₊ : ℕ) : ℝ) : ℂ) ^ (c + 1)) / (c + 1) := by
    simp only [hfdef]
    exact integral_cpow (Or.inl (by rw [hcre]; norm_num))
  have hINN1 : ∫ y in N..N1, f y
      = ((N1 : ℂ) ^ (c + 1) - (N : ℂ) ^ (c + 1)) / (c + 1) := by
    simp only [hfdef]
    exact integral_cpow (Or.inl (by rw [hcre]; norm_num))
  -- the boundary difference, via closed forms
  have hB : ‖(∫ y in ((⌊N⌋₊ : ℕ) : ℝ)..((⌊N1⌋₊ : ℕ) : ℝ), f y) - ∫ y in N..N1, f y‖
      ≤ 4 * N ^ (-1 / 2 : ℝ) := by
    have hb1 : ‖(N1 : ℂ) ^ (c + 1) - (((⌊N1⌋₊ : ℕ) : ℝ) : ℂ) ^ (c + 1)‖
        ≤ ‖c + 1‖ * ((⌊N1⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) :=
      hFTC _ _ hK1pos hK1R (by linarith [hK1N])
    have hb2 : ‖(N : ℂ) ^ (c + 1) - (((⌊N⌋₊ : ℕ) : ℝ) : ℂ) ^ (c + 1)‖
        ≤ ‖c + 1‖ * ((⌊N⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) :=
      hFTC _ _ hKnat hKR (by linarith [hKN])
    have hcn : (0 : ℝ) < ‖c + 1‖ := by
      rw [norm_pos_iff]
      exact hc1'
    rw [hIKK1, hINN1, ← sub_div, norm_div]
    have hsplitA : ((((⌊N1⌋₊ : ℕ) : ℝ) : ℂ) ^ (c + 1) - (((⌊N⌋₊ : ℕ) : ℝ) : ℂ) ^ (c + 1))
        - ((N1 : ℂ) ^ (c + 1) - (N : ℂ) ^ (c + 1))
        = (-((N1 : ℂ) ^ (c + 1) - (((⌊N1⌋₊ : ℕ) : ℝ) : ℂ) ^ (c + 1)))
          + ((N : ℂ) ^ (c + 1) - (((⌊N⌋₊ : ℕ) : ℝ) : ℂ) ^ (c + 1)) := by ring
    rw [hsplitA]
    have htri := norm_add_le (-((N1 : ℂ) ^ (c + 1) - (((⌊N1⌋₊ : ℕ) : ℝ) : ℂ) ^ (c + 1)))
      ((N : ℂ) ^ (c + 1) - (((⌊N⌋₊ : ℕ) : ℝ) : ℂ) ^ (c + 1))
    rw [norm_neg] at htri
    have hsum : ‖(-((N1 : ℂ) ^ (c + 1) - (((⌊N1⌋₊ : ℕ) : ℝ) : ℂ) ^ (c + 1)))
          + ((N : ℂ) ^ (c + 1) - (((⌊N⌋₊ : ℕ) : ℝ) : ℂ) ^ (c + 1))‖
        ≤ ‖c + 1‖ * (((⌊N1⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) + ((⌊N⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) := by
      have h1 := hb1
      have h2 := hb2
      nlinarith [htri]
    have hmono : ((⌊N1⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) ≤ ((⌊N⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hK0 hKK1R (by norm_num)
    have hdiv := div_le_div_of_nonneg_right hsum hcn.le
    have hsimp : (‖c + 1‖ * (((⌊N1⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) + ((⌊N⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) / ‖c + 1‖
        = ((⌊N1⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) + ((⌊N⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) :=
      mul_div_cancel_left₀ _ (ne_of_gt hcn)
    rw [hsimp] at hdiv
    have hK1' : (0 : ℝ) ≤ ((⌊N1⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
    have hKv : (0 : ℝ) ≤ ((⌊N⌋₊ : ℕ) : ℝ) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hK0.le _
    linarith [hdiv, hmono, hscale1, hR]
  rw [Finset.sum_congr rfl hsummand, hintmand]
  have hdec : (∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, f n) - ∫ y in N..N1, f y
      = ((∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, f n)
          - ∫ y in ((⌊N⌋₊ : ℕ) : ℝ)..((⌊N1⌋₊ : ℕ) : ℝ), f y)
        + ((∫ y in ((⌊N⌋₊ : ℕ) : ℝ)..((⌊N1⌋₊ : ℕ) : ℝ), f y) - ∫ y in N..N1, f y) := by
    abel
  rw [hdec]
  have htri2 := norm_add_le ((∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, f n)
      - ∫ y in ((⌊N⌋₊ : ℕ) : ℝ)..((⌊N1⌋₊ : ℕ) : ℝ), f y)
    ((∫ y in ((⌊N⌋₊ : ℕ) : ℝ)..((⌊N1⌋₊ : ℕ) : ℝ), f y) - ∫ y in N..N1, f y)
  have h1 := hbEL
  have h2 := hB
  have h3 := htri2
  linarith [hR]

/-- LEAF. Page 21. Explicit Saving Parameter η. -/
theorem fgm_eta (ε : ℝ) (hε : 0 < ε) : 0 < min (ε / 8) (1 / 4) :=
  lt_min (by positivity) (by norm_num)

/-- LEAF, CITED. Page 21, Fujii-Gallagher-Montgomery bound, reference 6 Theorem 1, cited not proved
in the lab. Statement unchanged by U-1609: not refuted, blocked on the citation. -/
theorem fgm_bound :
  ∃ C_FGM : ℝ, 0 < C_FGM ∧
  ∀ q : ℕ, q ≥ 1 → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
  ∀ N u : ℝ, 1 ≤ N → N ≤ u → u ≤ 2 * N →
  ‖∑ n ∈ Ioc ⌊N⌋₊ ⌊u⌋₊, χ (n : ZMod q) * (n : ℂ) ^ (-(t : ℂ) * Complex.I) -
    (if χ = 1 then 1 else 0 : ℂ) * (Nat.totient q : ℂ) / (q : ℂ) *
    ∫ y in N..u, (y : ℂ) ^ (-(t : ℂ) * Complex.I)‖
  ≤ C_FGM * (q : ℝ) ^ (1 / 2 : ℝ) * (|t| + 1) ^ (1 / 2 : ℝ) * log ((q : ℝ) * (|t| + 2)) := by sorry

/-- LEAF, OPEN. Outline step for page 21, the paper prints no such display. Discretization error
between discrete sum and integral, in the nonresonant range `|t| ≤ N` only. U-1609 added that
hypothesis: at `t = 2πN` the old form fails, `Audit1609.old_fgm_discretization_error_false`. -/
theorem fgm_discretization_error :
  ∃ C_disc : ℝ, 0 ≤ C_disc ∧ ∀ N N1 : ℝ, 1 ≤ N → N ≤ N1 → N1 ≤ 2 * N → ∀ t : ℝ, |t| ≤ N →
  ‖∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, (n : ℂ) ^ (-(t : ℂ) * Complex.I) * (n : ℂ) ^ (-1 / 2 : ℂ) -
    ∫ y in N..N1, (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I)‖
  ≤ C_disc * (N : ℝ) ^ (-1 / 2 : ℝ) := by
  exact ⟨500, by norm_num, fun N N1 hN hNN1 hN1 t ht => disc_bound N N1 t hN hNN1 hN1 ht⟩

/-- LEAF. Page 21. Main integral evaluation bound. -/
theorem fgm_integral_bound :
  ∀ N N1 : ℝ, 1 ≤ N → N ≤ N1 → N1 ≤ 2 * N → ∀ t : ℝ,
  ‖∫ y in N..N1, (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I)‖
  ≤ 5 * (N : ℝ) ^ (1 / 2 : ℝ) / (1 + |t|) := by
  intro N N1 hN hNN1 hN1 t
  have hN0 : 0 < N := by linarith
  have hN10 : 0 < N1 := by linarith
  let s : ℂ := (-1 / 2 : ℂ) + (-(t : ℂ) * Complex.I)
  let d : ℂ := s + 1
  have hfun : Set.EqOn
      (fun y : ℝ => (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I))
      (fun y => (y : ℂ) ^ s) (Set.uIcc N N1) := by
    intro y hy
    have hypos : 0 < y := by
      rw [Set.uIcc_of_le hNN1] at hy
      linarith [hy.1]
    dsimp [s]
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hypos.ne')]
  have hint : ∫ y in N..N1,
      (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I) =
      ∫ y in N..N1, (y : ℂ) ^ s :=
    intervalIntegral.integral_congr hfun
  have hvalue : ∫ y in N..N1,
      (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I) =
      ((N1 : ℂ) ^ d - (N : ℂ) ^ d) / d := by
    calc
      _ = ∫ y in N..N1, (y : ℂ) ^ s := hint
      _ = _ := by
        change (∫ y in N..N1, (y : ℂ) ^ s) =
          ((N1 : ℂ) ^ (s + 1) - (N : ℂ) ^ (s + 1)) / (s + 1)
        exact integral_cpow (a := N) (b := N1) (r := s)
          (Or.inl (by dsimp [s]; norm_num))
  have hdre : d.re = 1 / 2 := by simp [d, s]; ring
  have hdim : d.im = -t := by simp [d, s]
  have hden1 : 1 / 2 ≤ ‖d‖ := by
    have hh := Complex.abs_re_le_norm d
    rw [hdre] at hh
    norm_num at hh
    exact hh
  have hden2 : |t| ≤ ‖d‖ := by
    have hh := Complex.abs_im_le_norm d
    rw [hdim] at hh
    simpa using hh
  have hdenpos : 0 < ‖d‖ := by linarith
  have hnormN1 : ‖(N1 : ℂ) ^ d‖ = N1 ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN10 d, hdre]
  have hnormN : ‖(N : ℂ) ^ d‖ = N ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN0 d, hdre]
  have hroot2 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 3 / 2 := by
    rw [← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
  have hNroot : 0 ≤ N ^ (1 / 2 : ℝ) := Real.rpow_nonneg hN0.le _
  have hN1root : N1 ^ (1 / 2 : ℝ) ≤ (2 * N) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hN1 (by norm_num)
  have hmulroot : (2 * N) ^ (1 / 2 : ℝ) =
      (2 : ℝ) ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hN0.le]
  have hnum : ‖(N1 : ℂ) ^ d - (N : ℂ) ^ d‖ ≤
      (5 / 2 : ℝ) * N ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ ‖(N1 : ℂ) ^ d‖ + ‖(N : ℂ) ^ d‖ := norm_sub_le _ _
      _ = N1 ^ (1 / 2 : ℝ) + N ^ (1 / 2 : ℝ) := by rw [hnormN1, hnormN]
      _ ≤ (2 * N) ^ (1 / 2 : ℝ) + N ^ (1 / 2 : ℝ) :=
        add_le_add hN1root le_rfl
      _ = (2 : ℝ) ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) +
          N ^ (1 / 2 : ℝ) := by rw [hmulroot]
      _ ≤ (5 / 2 : ℝ) * N ^ (1 / 2 : ℝ) := by nlinarith [hroot2, hNroot]
  by_cases ht : |t| ≤ 1
  · have hpoint : ∀ y ∈ Set.uIoc N N1, ‖(y : ℂ) ^ s‖ ≤ N ^ (-1 / 2 : ℝ) := by
      intro y hy
      have hyN : N ≤ y := by
        rw [Set.uIoc_of_le hNN1] at hy
        exact hy.1.le
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hyN]) s]
      have hsre : s.re = -1 / 2 := by simp [s]
      rw [hsre]
      exact Real.rpow_le_rpow_of_nonpos hN0 hyN (by norm_num)
    have hsmall : ‖∫ y in N..N1, (y : ℂ) ^ s‖ ≤
        N ^ (-1 / 2 : ℝ) * |N1 - N| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
      filter_upwards with y hy
      exact hpoint y hy
    have hlength : |N1 - N| ≤ N := by
      rw [abs_of_nonneg (by linarith : 0 ≤ N1 - N)]
      linarith
    have hpow : N ^ (-1 / 2 : ℝ) * N = N ^ (1 / 2 : ℝ) := by
      calc
        N ^ (-1 / 2 : ℝ) * N =
            N ^ (-1 / 2 : ℝ) * N ^ (1 : ℝ) := by simp
        _ = N ^ ((-1 / 2 : ℝ) + 1) := (Real.rpow_add hN0 _ _).symm
        _ = N ^ (1 / 2 : ℝ) := by congr 1; norm_num
    calc
      _ = ‖∫ y in N..N1, (y : ℂ) ^ s‖ := by rw [hint]
      _ ≤ N ^ (-1 / 2 : ℝ) * |N1 - N| := hsmall
      _ ≤ N ^ (-1 / 2 : ℝ) * N :=
        mul_le_mul_of_nonneg_left hlength (Real.rpow_nonneg hN0.le _)
      _ = N ^ (1 / 2 : ℝ) := hpow
      _ ≤ 5 * N ^ (1 / 2 : ℝ) / (1 + |t|) := by
        rw [le_div_iff₀ (by positivity : 0 < 1 + |t|)]
        nlinarith [Real.rpow_nonneg hN0.le (1 / 2 : ℝ)]
  · have htlarge : 1 < |t| := lt_of_not_ge ht
    have htpos : 0 < |t| := by linarith
    have hformula : ‖∫ y in N..N1,
        (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I)‖ =
        ‖(N1 : ℂ) ^ d - (N : ℂ) ^ d‖ / ‖d‖ := by
      rw [hvalue, Complex.norm_div]
    have hfirst : ‖(N1 : ℂ) ^ d - (N : ℂ) ^ d‖ / ‖d‖ ≤
        ((5 / 2 : ℝ) * N ^ (1 / 2 : ℝ)) / |t| := by
      apply (div_le_div_iff₀ hdenpos htpos).2
      exact mul_le_mul hnum hden2 (abs_nonneg t) (by positivity)
    have hlast : ((5 / 2 : ℝ) * N ^ (1 / 2 : ℝ)) / |t| ≤
        5 * N ^ (1 / 2 : ℝ) / (1 + |t|) := by
      apply (div_le_div_iff₀ htpos (by positivity : 0 < 1 + |t|)).2
      have hratio : 1 + |t| ≤ 2 * |t| := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hratio (by positivity :
        0 ≤ (5 / 2 : ℝ) * N ^ (1 / 2 : ℝ))]
    exact hformula ▸ hfirst.trans hlast

/-- LEAF. Page 21. Frequency inequality conversion. -/
theorem fgm_frequency_conversion :
  ∀ x N t : ℝ, 2 ≤ x → x ^ (1/4 : ℝ) ≤ N → N ≤ x →
  |t| ^ (1 / 2 : ℝ) * x ^ (1 / 16 : ℝ) < N →
  (|t| + 1) ^ (1 / 2 : ℝ) ≤ 2 * N ^ (1 - 1 / 16 : ℝ) := by
  intro x N t hx hroot hNx hsplit
  have hx0 : 0 < x := by linarith
  have hN1 : 1 ≤ N :=
    (Real.one_le_rpow (by linarith : 1 ≤ x) (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans hroot
  have hN0 : 0 < N := by linarith
  have hpow : N ^ (1 / 16 : ℝ) ≤ x ^ (1 / 16 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hNx (by norm_num)
  have hprod : |t| ^ (1 / 2 : ℝ) * N ^ (1 / 16 : ℝ) < N :=
    (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (abs_nonneg t) _)).trans_lt hsplit
  have hsqrt : |t| ^ (1 / 2 : ℝ) < N ^ (15 / 16 : ℝ) := by
    have hden : 0 < N ^ (1 / 16 : ℝ) := Real.rpow_pos_of_pos hN0 _
    have hdiv := (lt_div_iff₀ hden).2 hprod
    have hid : N / N ^ (1 / 16 : ℝ) = N ^ (15 / 16 : ℝ) := by
      calc
        N / N ^ (1 / 16 : ℝ) = N ^ (1 : ℝ) / N ^ (1 / 16 : ℝ) := by rw [Real.rpow_one]
        _ = N ^ (1 - 1 / 16 : ℝ) := (Real.rpow_sub hN0 1 (1 / 16 : ℝ)).symm
        _ = N ^ (15 / 16 : ℝ) := by congr 1; norm_num
    rwa [hid] at hdiv
  have htsquare : |t| ≤ N ^ (15 / 8 : ℝ) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg t) _)
      hsqrt.le (by norm_num : (0 : ℝ) ≤ 2)
    have hleft : (|t| ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = |t| := by
      rw [← Real.rpow_mul (abs_nonneg t)]
      norm_num
    have hright : (N ^ (15 / 16 : ℝ)) ^ (2 : ℝ) = N ^ (15 / 8 : ℝ) := by
      rw [← Real.rpow_mul hN0.le]
      norm_num
    calc
      |t| = (|t| ^ (1 / 2 : ℝ)) ^ 2 := hleft.symm
      _ ≤ (N ^ (15 / 16 : ℝ)) ^ 2 := hh
      _ = N ^ (15 / 8 : ℝ) := hright
  have hNpow1 : 1 ≤ N ^ (15 / 8 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hpower : (N ^ (15 / 16 : ℝ)) ^ 2 = N ^ (15 / 8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hbase : |t| + 1 ≤ (2 * N ^ (15 / 16 : ℝ)) ^ 2 := by
    rw [mul_pow, hpower]
    nlinarith
  have hB : 0 ≤ 2 * N ^ (15 / 16 : ℝ) := by positivity
  calc
    (|t| + 1) ^ (1 / 2 : ℝ) = Real.sqrt (|t| + 1) := by rw [Real.sqrt_eq_rpow]
    _ ≤ Real.sqrt ((2 * N ^ (15 / 16 : ℝ)) ^ 2) := Real.sqrt_le_sqrt hbase
    _ = 2 * N ^ (15 / 16 : ℝ) := Real.sqrt_sq hB
    _ = 2 * N ^ (1 - 1 / 16 : ℝ) := by congr 2; norm_num

/-- Page 21. Combination of remainder bounds. U-1609 added `0 ≤ C_FGM` and `0 ≤ K_2`: the old form
fails at `C_FGM = -1`, `Audit1609.old_fgm_combine_remainders_false`. -/
theorem fgm_combine_remainders :
  ∀ C_FGM K_2 N ε : ℝ, 0 ≤ C_FGM → 0 ≤ K_2 → 1 ≤ N → 0 < ε →
  C_FGM * N ^ (-1 / 2 : ℝ) * (K_2 * N ^ (ε / 8)) * (2 * N ^ (1 - ε / 4))
  ≤ 2 * C_FGM * K_2 * N ^ (1 / 2 - min (ε / 8) (1 / 4)) := by
  intro C K N ε hC hK hN hε
  have hN0 : 0 < N := by linarith
  have hprod : N ^ (-1 / 2 : ℝ) * N ^ (ε / 8) * N ^ (1 - ε / 4) = N ^ (1 / 2 - ε / 8) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    congr 1
    ring
  have hmono : N ^ (1 / 2 - ε / 8) ≤ N ^ (1 / 2 - min (ε / 8) (1 / 4)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith [min_le_left (ε / 8) (1 / 4 : ℝ)])
  calc
    C * N ^ (-1 / 2 : ℝ) * (K * N ^ (ε / 8)) * (2 * N ^ (1 - ε / 4))
        = 2 * C * K * (N ^ (-1 / 2 : ℝ) * N ^ (ε / 8) * N ^ (1 - ε / 4)) := by ring
    _ = 2 * C * K * N ^ (1 / 2 - ε / 8) := by rw [hprod]
    _ ≤ 2 * C * K * N ^ (1 / 2 - min (ε / 8) (1 / 4)) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)

/-- LEAF. Page 21. Main decomposition branch -/
theorem fgm_branch :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 2 ≤ x → ∀ N N1 : ℝ, x ^ ε ≤ N → N ≤ x → N ≤ N1 → N1 ≤ 2 * N →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A → ∀ χ : DirichletCharacter ℂ q,
    ∀ t : ℝ, |t| ≤ x → |t| ^ (1 / 2 : ℝ) * x ^ (ε / 4) < N →
      ‖∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, χ (n : ZMod q) * (n : ℂ) ^ (-(half t))‖ ≤
        C * (N ^ (1 / 2 - η) + N ^ (1 / 2 : ℝ) / (1 + |t|)) := by
  exact Decomp90.fgm_branch
