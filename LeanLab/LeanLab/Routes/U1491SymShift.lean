/-
# R-0050, T3 MOONSHOT: two-point correlation at shift N of the even extension

Unit U-1491, PC run 20261022T1603Z-23862. AI wrote this Lean code.

Route. Extend `f : ℕ → R` with `f 0 = 0` to `ℤ` evenly, `F n = f |n|`. The two-point
correlation of `F` at shift `N` over the window `-N - x < n < x` splits exactly as
  `S_x(N) = r_f(N) + 2 D_x(N)`,
where `r_f(N) = Σ_{a ≤ N} f(a) f(N - a)` is the binary Goldbach type convolution and
`D_x(N) = Σ_{k < x} f(k) f(k + N)` is the forward, de Polignac type, correlation at shift `N`.
So a two-point Chowla or Hardy-Littlewood statement at shift `N` for the even extension
contains the reflection at `N` as the part of the window that straddles `0`.

PROVED here, unconditional:
* `sym_corr_split`: the identity above.
* `refl_pos_iff`: for `f ≥ 0` over an ordered ring, `r_f(N) > 0 ↔ S_x(N) > 2 D_x(N)`.
* `sym_corr_window`: for `|f| ≤ 1`, `|S_x(N) - 2 D_x(N)| ≤ N + 1` for every `x`; at fixed
  `N` the reflection part is bounded while the window grows, so any statement about
  `S_x(N)` as `x → ∞` with `N` fixed, Tao's regime, is blind to `r_f(N)`.

KNOWN mathematics, elementary. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import Mathlib

namespace LeanLab.Routes.U1491

open Finset

/-- Symmetric-window shift correlation of the even extension. -/
def symCorr {R : Type*} [CommRing R] (f : ℕ → R) (N x : ℕ) : R :=
  ∑ n ∈ Ioo (-(N : ℤ) - x) x, f n.natAbs * f (n + N).natAbs

/-- The reflection, binary Goldbach type, convolution at `N`. -/
def refl {R : Type*} [CommRing R] (f : ℕ → R) (N : ℕ) : R :=
  ∑ a ∈ range (N + 1), f a * f (N - a)

/-- The forward shift correlation at shift `N` over `0 ≤ k < x`. -/
def fwd {R : Type*} [CommRing R] (f : ℕ → R) (N x : ℕ) : R :=
  ∑ k ∈ range x, f k * f (k + N)

theorem symCorr_zero {R : Type*} [CommRing R] (f : ℕ → R) (hf : f 0 = 0) (N : ℕ) :
    symCorr f N 0 = refl f N := by
  unfold symCorr refl
  simp only [Nat.cast_zero, sub_zero]
  have h1 : ∑ n ∈ Ioo (-(N : ℤ)) 0, f n.natAbs * f (n + N).natAbs
      = ∑ m ∈ Ioo 0 N, f m * f (N - m) := by
    refine Finset.sum_nbij' (fun n => n.natAbs) (fun m => -(m : ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro n hn; simp only [mem_Ioo] at hn ⊢; omega
    · intro m hm; simp only [mem_Ioo] at hm ⊢; omega
    · intro n hn; simp only [mem_Ioo] at hn; omega
    · intro m hm; simp
    · intro n hn
      simp only [mem_Ioo] at hn
      congr 2; omega
  rw [h1]
  refine Finset.sum_subset (fun m hm => ?_) (fun m hm hm' => ?_)
  · simp only [mem_Ioo, mem_range] at hm ⊢; omega
  · simp only [mem_Ioo, mem_range, not_and_or, not_lt] at hm hm'
    rcases hm' with h | h
    · have : m = 0 := by omega
      subst this; simp [hf]
    · have : N - m = 0 := by omega
      rw [this, hf, mul_zero]

theorem symCorr_succ {R : Type*} [CommRing R] (f : ℕ → R) (hf : f 0 = 0) (N x : ℕ) :
    symCorr f N (x + 1) = symCorr f N x + 2 * (f x * f (x + N)) := by
  unfold symCorr
  by_cases h0 : N = 0 ∧ x = 0
  · obtain ⟨rfl, rfl⟩ := h0
    have h01 : Ioo (-1 : ℤ) 1 = {0} := by ext n; simp only [mem_Ioo, mem_singleton]; omega
    simp [h01, hf]
  have hset : Ioo (-(N : ℤ) - ↑(x + 1)) ↑(x + 1)
      = insert (-(N : ℤ) - x) (insert (x : ℤ) (Ioo (-(N : ℤ) - x) x)) := by
    ext n; simp only [mem_Ioo, mem_insert]; push_cast; omega
  have hA : (-(N : ℤ) - x) ∉ insert (x : ℤ) (Ioo (-(N : ℤ) - x) x) := by
    simp only [mem_insert, mem_Ioo, not_or]; omega
  have hB : (x : ℤ) ∉ Ioo (-(N : ℤ) - x) x := by simp
  rw [hset, sum_insert hA, sum_insert hB]
  have e1 : (-(N : ℤ) - x).natAbs = x + N := by omega
  have e2 : (-(N : ℤ) - x + N).natAbs = x := by omega
  have e3 : (x : ℤ).natAbs = x := by omega
  have e4 : ((x : ℤ) + N).natAbs = x + N := by omega
  rw [e1, e2, e3, e4]
  ring

/-- Headline: `S_x(N) = r_f(N) + 2 D_x(N)` for the even extension of `f` with `f 0 = 0`. -/
theorem sym_corr_split {R : Type*} [CommRing R] (f : ℕ → R) (hf : f 0 = 0) (N x : ℕ) :
    symCorr f N x = refl f N + 2 * fwd f N x := by
  induction x with
  | zero => simp [symCorr_zero f hf, fwd]
  | succ x ih =>
    rw [symCorr_succ f hf, ih, fwd, fwd, sum_range_succ]
    ring

/-- For nonnegative `f`, the reflection count is positive iff the shift correlation of the
even extension beats twice the forward correlation. -/
theorem refl_pos_iff {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (f : ℕ → R) (hf : f 0 = 0) (N x : ℕ) :
    0 < refl f N ↔ 2 * fwd f N x < symCorr f N x := by
  rw [sym_corr_split f hf]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- The window barrier: for `|f| ≤ 1` the reflection part of `S_x(N)` is at most `N + 1`
in size for every window `x`. -/
theorem sym_corr_window (f : ℕ → ℝ) (hf : f 0 = 0) (hb : ∀ n, |f n| ≤ 1) (N x : ℕ) :
    |symCorr f N x - 2 * fwd f N x| ≤ N + 1 := by
  rw [sym_corr_split f hf, add_sub_cancel_right, refl]
  calc |∑ a ∈ range (N + 1), f a * f (N - a)|
      ≤ ∑ a ∈ range (N + 1), |f a * f (N - a)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ range (N + 1), (1 : ℝ) := by
        refine sum_le_sum (fun a _ => ?_)
        rw [abs_mul]
        calc |f a| * |f (N - a)| ≤ 1 * 1 :=
              mul_le_mul (hb a) (hb _) (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = N + 1 := by simp

/-- Vacuity: the prime indicator satisfies `f 0 = 0` and `|f| ≤ 1`, and at `N = 10`,
`x = 0`, the reflection count is positive. -/
noncomputable def primeInd (n : ℕ) : ℝ := if n.Prime then 1 else 0

theorem primeInd_zero : primeInd 0 = 0 := by simp [primeInd, Nat.not_prime_zero]

theorem primeInd_le (n : ℕ) : |primeInd n| ≤ 1 := by
  unfold primeInd; split_ifs <;> simp

example : 0 < refl primeInd 10 := by
  have h : refl primeInd 10 = 3 := by
    simp only [refl, primeInd, sum_range_succ, sum_range_zero]
    norm_num
  rw [h]; norm_num

end LeanLab.Routes.U1491
