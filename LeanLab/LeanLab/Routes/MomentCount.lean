/-
T3 route R-5002, unit U-5040. The moment counting lemma behind the variance barrier.
If `M n ≥ m > 0` on a finite block `S`, every `n ∈ S` with `R n = 0` contributes `M n ^ (2k) ≥ m ^ (2k)`
to `∑ (R n - M n) ^ (2k)`, so the number of zeros is at most that moment over `m ^ (2k)`
(`card_zero_le_moment`), and a moment below `m ^ (2k)` leaves no zero (`no_zero_of_moment_lt`).
With `R` the weighted Goldbach count `goldbachR` this gives `goldbach_of_moment_lt`: every `n` in the
block is a sum of two primes. The hypothesis is NOT known for any `k`; gen/variance_barrier.py shows
that for `k = 1` it is false numerically, the variance is about `0.17 (N log N)²` against `m² ≈ (0.33 N)²`,
while for `k = 2` it holds numerically from `N = 2^14` to `2^23`. A map entry, not progress on Goldbach,
which is open.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.Routes
open Finset

/-- Plain math: `#{n ∈ S : R n = 0} · m^(2k) ≤ ∑_{n ∈ S} (R n - M n)^(2k)` when `0 ≤ m ≤ M n` on `S`. -/
theorem card_zero_le_moment (S : Finset ℕ) (R M : ℕ → ℝ) {m : ℝ} (k : ℕ)
    (hm : 0 ≤ m) (hM : ∀ n ∈ S, m ≤ M n) :
    ((S.filter (fun n => R n = 0)).card : ℝ) * m ^ (2 * k) ≤ ∑ n ∈ S, (R n - M n) ^ (2 * k) := by
  have hnn : ∀ n ∈ S, 0 ≤ (R n - M n) ^ (2 * k) := fun n _ => by
    rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
  calc ((S.filter (fun n => R n = 0)).card : ℝ) * m ^ (2 * k)
      = ∑ n ∈ S.filter (fun n => R n = 0), m ^ (2 * k) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ S.filter (fun n => R n = 0), (R n - M n) ^ (2 * k) := by
        apply sum_le_sum
        intro n hn
        rw [mem_filter] at hn
        rw [hn.2, zero_sub, pow_mul, pow_mul, neg_sq]
        exact pow_le_pow_left₀ (sq_nonneg _)
          (pow_le_pow_left₀ hm (hM n hn.1) 2) k
    _ ≤ ∑ n ∈ S, (R n - M n) ^ (2 * k) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n hn _ => hnn n hn)

/-- Plain math: if `∑_{n ∈ S} (R n - M n)^(2k) < m^(2k)` and `0 ≤ m ≤ M n` on `S`, then `R n ≠ 0` on `S`. -/
theorem no_zero_of_moment_lt (S : Finset ℕ) (R M : ℕ → ℝ) {m : ℝ} (k : ℕ)
    (hm : 0 ≤ m) (hM : ∀ n ∈ S, m ≤ M n)
    (hlt : ∑ n ∈ S, (R n - M n) ^ (2 * k) < m ^ (2 * k)) : ∀ n ∈ S, R n ≠ 0 := by
  intro n hn h0
  have hc := card_zero_le_moment S R M k hm hM
  have h1 : (1 : ℝ) ≤ (S.filter (fun n => R n = 0)).card := by
    exact_mod_cast card_pos.mpr ⟨n, mem_filter.mpr ⟨hn, h0⟩⟩
  have hp : 0 ≤ m ^ (2 * k) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
  nlinarith

/-- The weighted Goldbach count `R(n) = ∑_{p + q = n} log p log q`, over primes `p, q`. -/
noncomputable def goldbachR (n : ℕ) : ℝ :=
  ∑ a ∈ range (n + 1), if a.Prime ∧ (n - a).Prime then Real.log a * Real.log (n - a : ℕ) else 0

/-- `R(n) ≠ 0` gives a representation `n = p + q`. -/
theorem goldbach_of_R_ne_zero {n : ℕ} (h : goldbachR n ≠ 0) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  by_contra hno
  apply h
  unfold goldbachR
  apply sum_eq_zero
  intro a ha
  rw [mem_range] at ha
  split_ifs with hpq
  · exact absurd ⟨a, n - a, hpq.1, hpq.2, by omega⟩ hno
  · rfl

/-- The route's conclusion: a `2k`-th moment of `R - M` below `m^(2k)` on a block `S`, with `M ≥ m ≥ 0`
there, makes every `n ∈ S` a sum of two primes. CONDITIONAL in use: the moment bound is the open input. -/
theorem goldbach_of_moment_lt (S : Finset ℕ) (M : ℕ → ℝ) {m : ℝ} (k : ℕ)
    (hm : 0 ≤ m) (hM : ∀ n ∈ S, m ≤ M n)
    (hlt : ∑ n ∈ S, (goldbachR n - M n) ^ (2 * k) < m ^ (2 * k)) :
    ∀ n ∈ S, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n :=
  fun n hn => goldbach_of_R_ne_zero (no_zero_of_moment_lt S goldbachR M k hm hM hlt n hn)

/-- Vacuity test: the hypotheses can hold. On `S = {4}` with `M = R`, the moment is `0 < 1 = m^(2k)`
for `m = 1`, provided `R 4 ≥ 1`; here `R 4 = (log 2)²`, so we take `m = (log 2)²` and `k = 1`. -/
theorem vacuity_example : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 4 := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine goldbach_of_moment_lt {4} goldbachR (m := (Real.log 2) ^ 2 / 2) 1 (by positivity)
    ?_ ?_ 4 (mem_singleton_self 4)
  · intro n hn
    rw [mem_singleton] at hn
    subst hn
    have hR : goldbachR 4 = Real.log 2 * Real.log 2 := by
      unfold goldbachR
      simp [sum_range_succ, Nat.prime_two]
    rw [hR]; nlinarith
  · simp only [sum_singleton, sub_self]
    rw [zero_pow (by norm_num)]
    positivity

end LeanLab.Routes
