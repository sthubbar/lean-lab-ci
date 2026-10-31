/-
# R-0053 MOONSHOT: two sided Maynard weights and a window of Goldbach targets

Unit U-1541, run 20261026T0403Z-9802, track T3 MOONSHOT.
AI wrote this Lean code, Claude, checked only by the Lean kernel. Binary Goldbach is OPEN.
Nothing here is progress on Goldbach. This file is a ROUTE: it states the counting step
of the route and the arithmetic that shows where it meets Selberg's parity barrier.

Setup, plain math. Fix even targets `M + D j`, `j < k`. For `n` in a finite set `s` with
nonnegative weights `w`, let `a n = 1` if `n` is prime and `B n` the number of `j` with
`M + D j - n` prime. Write `W = Σ w`, `A = Σ w a`, `S1 = Σ w B`, `S2 = Σ w B²`,
`Pos = Σ w 1[B ≥ 1]`.

PROVED here, unconditional, no sorry:
* `bonferroni_pointwise`: `2 a B ≥ 2 a - (B-1)(B-2)` for `a ∈ {0,1}`, `B : ℕ`.
* `union_step`: `W < A + Pos` gives an `n` with `a n = 1` and `B n ≥ 1`.
* `second_moment`: `S1² ≤ Pos * S2`, weighted Cauchy-Schwarz.
* `window_of_moments`: `W < A + S1²/S2` gives such an `n`.
* `parity_line`: if `2A ≤ W`, a single form at most half prime under `w`, and
  `2 S1² ≤ W S2`, pair constant at least 2, then `W < A + S1²/S2` FAILS.
* `goldbach_window`: the Goldbach form of `window_of_moments`: some `M + D j` is a sum of
  two primes. It is unconditional as an implication; its hypothesis is the route's open
  input and is NOT claimed for any infinite family of `M`.
* `goldbach_window_vacuity`: the hypothesis of `goldbach_window` holds at `M = 10`.
No new `def ... : Prop`, no LEAF, no CITED sorry.
-/
import Mathlib

namespace U1541

open Finset

/-- Pointwise Bonferroni form of the product: for `a ∈ {0,1}` and `B : ℕ`,
`2 a B ≥ 2 a - (B - 1)(B - 2)` in `ℤ`. -/
theorem bonferroni_pointwise (a : ℤ) (ha : a = 0 ∨ a = 1) (B : ℕ) :
    2 * a - ((B : ℤ) - 1) * ((B : ℤ) - 2) ≤ 2 * a * B := by
  have key : 0 ≤ ((B : ℤ) - 1) * ((B : ℤ) - 2) := by
    rcases Nat.lt_or_ge B 2 with h | h
    · interval_cases B <;> norm_num
    · have h1 : (2 : ℤ) ≤ B := by exact_mod_cast h
      nlinarith
  rcases ha with rfl | rfl
  · simpa using key
  · rcases Nat.lt_or_ge B 1 with h | h
    · interval_cases B; norm_num
    · have h1 : (1 : ℤ) ≤ B := by exact_mod_cast h
      nlinarith

/-- Union step: if the weighted mass of `{a = 1}` plus that of `{B ≥ 1}` exceeds the total
mass, some point has both. -/
theorem union_step {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (P : ι → Prop) [DecidablePred P] (B : ι → ℕ)
    (h : ∑ i ∈ s, w i < ∑ i ∈ s, w i * (if P i then 1 else 0)
        + ∑ i ∈ s, w i * (if 1 ≤ B i then 1 else 0)) :
    ∃ i ∈ s, P i ∧ 1 ≤ B i := by
  by_contra hne
  push_neg at hne
  have : ∑ i ∈ s, w i * (if P i then 1 else 0) + ∑ i ∈ s, w i * (if 1 ≤ B i then 1 else 0)
      ≤ ∑ i ∈ s, w i := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro i hi
    by_cases hp : P i
    · have hb : ¬ 1 ≤ B i := fun hb => (Nat.lt_irrefl 0) (by have := hne i hi hp; omega)
      simp [hp, hb]
    · by_cases hb : 1 ≤ B i
      · simp [hp, hb]
      · simp [hp, hb, hw i hi]
  linarith

/-- Second moment: `(Σ w B)² ≤ (Σ w 1[B ≥ 1]) (Σ w B²)`, weighted Cauchy-Schwarz. -/
theorem second_moment {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (B : ι → ℕ) :
    (∑ i ∈ s, w i * (B i : ℝ)) ^ 2
      ≤ (∑ i ∈ s, w i * (if 1 ≤ B i then 1 else 0)) * ∑ i ∈ s, w i * (B i : ℝ) ^ 2 := by
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i hi
    have := hw i hi
    split_ifs <;> simp [this]
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  · intro i hi
    by_cases hb : 1 ≤ B i
    · simp only [hb, if_true, mul_one]
      apply le_of_eq; ring
    · have : B i = 0 := by omega
      simp [this]

/-- Window step: `W < A + S1²/S2` with `S2 > 0` gives a point with `a = 1` and `B ≥ 1`. -/
theorem window_of_moments {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (P : ι → Prop) [DecidablePred P] (B : ι → ℕ)
    (hS2 : 0 < ∑ i ∈ s, w i * (B i : ℝ) ^ 2)
    (h : ∑ i ∈ s, w i < ∑ i ∈ s, w i * (if P i then 1 else 0)
        + (∑ i ∈ s, w i * (B i : ℝ)) ^ 2 / ∑ i ∈ s, w i * (B i : ℝ) ^ 2) :
    ∃ i ∈ s, P i ∧ 1 ≤ B i := by
  apply union_step s w hw P B
  have hcs := second_moment s w hw B
  have : (∑ i ∈ s, w i * (B i : ℝ)) ^ 2 / ∑ i ∈ s, w i * (B i : ℝ) ^ 2
      ≤ ∑ i ∈ s, w i * (if 1 ≤ B i then 1 else 0) := by
    rw [div_le_iff₀ hS2]; exact hcs
  linarith

/-- The parity line. If at most half the weight sits on `a = 1` and the second moment is
at least twice the squared first moment over the mass, pair constant `c ≥ 2`, then the
window test `W < A + S1²/S2` fails. Under Selberg's parity principle both hypotheses are
what a sieve-only input can deliver at best. -/
theorem parity_line (W A S1 S2 : ℝ) (hS2 : 0 < S2) (hA : 2 * A ≤ W)
    (hc : 2 * S1 ^ 2 ≤ W * S2) : ¬ (W < A + S1 ^ 2 / S2) := by
  intro h
  have : S1 ^ 2 / S2 ≤ W / 2 := by
    rw [div_le_iff₀ hS2]; linarith
  linarith

/-- Goldbach form of the window step. `s` is any set of `n ≤ M`; `B n` counts `j < k` with
`M + D j - n` prime. If `W < A + S1²/S2` then some target `M + D j`, `j < k`, is a sum of
two primes. -/
theorem goldbach_window (M k : ℕ) (D : ℕ → ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ≤ M)
    (w : ℕ → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hS2 : 0 < ∑ n ∈ s, w n *
      (((range k).filter (fun j => (M + D j - n).Prime)).card : ℝ) ^ 2)
    (h : ∑ n ∈ s, w n < ∑ n ∈ s, w n * (if n.Prime then 1 else 0)
        + (∑ n ∈ s, w n * (((range k).filter (fun j => (M + D j - n).Prime)).card : ℝ)) ^ 2
          / ∑ n ∈ s, w n *
            (((range k).filter (fun j => (M + D j - n).Prime)).card : ℝ) ^ 2) :
    ∃ j < k, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = M + D j := by
  obtain ⟨n, hn, hp, hB⟩ := window_of_moments s w hw (fun n => n.Prime)
    (fun n => ((range k).filter (fun j => (M + D j - n).Prime)).card) hS2 h
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hB
  rw [mem_filter, mem_range] at hj
  refine ⟨j, hj.1, n, M + D j - n, hp, hj.2, ?_⟩
  have := hs n hn
  omega

/-- Vacuity: the hypothesis of `goldbach_window` can hold. `M = 10`, `k = 1`, `D = 0`,
`s = {3}`, `w = 1`: `W = 1`, `A = 1`, `S1 = S2 = 1`, and `1 < 1 + 1`. -/
theorem goldbach_window_vacuity :
    ∃ j < 1, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 10 + (fun _ => 0) j := by
  have hB : ((range 1).filter (fun j => (10 + (fun _ : ℕ => 0) j - 3).Prime)).card = 1 := by
    decide
  apply goldbach_window 10 1 (fun _ => 0) {3} (by simp) (fun _ => 1) (by simp)
  · simp only [sum_singleton, hB]; norm_num
  · simp only [sum_singleton, hB]; norm_num [Nat.prime_three]

end U1541
