import Mathlib

/-!
# R-5062, the sieve as a linear program on `A = {N - p}`

Lab proof, unit U-5600, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. Known mathematics:
LP duality for sieves goes back to Selberg's extremal formulation of the sieve problem, and the
parity barrier to Selberg 1949. Binary Goldbach is OPEN; this is a T3 route, never progress on
Goldbach.

A sieve that sees only the congruence data `A_d = ∑_{d ∣ n} x n`, `d ∈ D`, of a sequence
`x : ℕ → [0, 1]` proves a lower bound for the prime mass `∑ P n * x n` through a dual certificate:
weights `lam d` on `D` and box multipliers `u n ≥ 0` with
`∑_{d ∈ D, d ∣ n} lam d - u n ≤ P n` for every `n`. Weak duality says the bound
`∑ lam d * A_d - ∑ u n` holds, and, the point of the route, it holds for every other `y` with the
same data. So if one `y` with the data of the Goldbach sequence carries no prime mass, no sieve on
that data proves `r(N) > 0`. numerics/r5062_*.py computes the least prime mass by LP.

* `sum_data_eq`: the swap `∑_d lam d * A_d(x) = ∑_n x n * ∑_{d ∣ n} lam d`, PROVED.
* `weak_duality`: the sieve lower bound from a dual certificate, PROVED.
* `same_data_bound`: the certificate bound for `x` is a lower bound for every `y` with the data
  of `x`, PROVED.
* `no_certificate_of_zero`: if some `y` in the box with the data of `x` has prime mass zero,
  every certificate bound is `≤ 0`, PROVED.
* `weak_duality_example`: vacuity test, a certificate with positive bound on a two element `S`.
-/

namespace LeanLab.Routes.R5062

open Finset

/-- The congruence datum `A_d(x) = ∑_{n ∈ S, d ∣ n} x n`. -/
def data (S : Finset ℕ) (x : ℕ → ℝ) (d : ℕ) : ℝ := ∑ n ∈ S.filter (d ∣ ·), x n

/-- The sum swap behind every sieve: `∑_{d ∈ D} lam d A_d(x) = ∑_{n ∈ S} x n ∑_{d ∈ D, d ∣ n} lam d`. -/
theorem sum_data_eq (S D : Finset ℕ) (x lam : ℕ → ℝ) :
    ∑ d ∈ D, lam d * data S x d = ∑ n ∈ S, x n * ∑ d ∈ D.filter (· ∣ n), lam d := by
  unfold data
  simp_rw [mul_sum, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun n _ => ?_
  refine sum_congr rfl fun d _ => ?_
  split_ifs <;> ring

/-- Weak LP duality for the sieve with the box `0 ≤ x ≤ 1`. -/
theorem weak_duality (S D : Finset ℕ) (x P lam u : ℕ → ℝ)
    (hx0 : ∀ n ∈ S, 0 ≤ x n) (hx1 : ∀ n ∈ S, x n ≤ 1) (hu : ∀ n ∈ S, 0 ≤ u n)
    (hdual : ∀ n ∈ S, ∑ d ∈ D.filter (· ∣ n), lam d - u n ≤ P n) :
    ∑ d ∈ D, lam d * data S x d - ∑ n ∈ S, u n ≤ ∑ n ∈ S, P n * x n := by
  rw [sum_data_eq, ← sum_sub_distrib]
  refine sum_le_sum fun n hn => ?_
  have h1 := hdual n hn
  have h2 := hx0 n hn
  have h3 := hx1 n hn
  have h4 := hu n hn
  nlinarith

/-- A certificate bound computed from the data of `x` is a lower bound for the prime mass of every
`y` in the box with the same data on `D`: the sieve cannot tell `x` from `y`. -/
theorem same_data_bound (S D : Finset ℕ) (x y P lam u : ℕ → ℝ)
    (hy0 : ∀ n ∈ S, 0 ≤ y n) (hy1 : ∀ n ∈ S, y n ≤ 1) (hu : ∀ n ∈ S, 0 ≤ u n)
    (hdual : ∀ n ∈ S, ∑ d ∈ D.filter (· ∣ n), lam d - u n ≤ P n)
    (hdata : ∀ d ∈ D, data S x d = data S y d) :
    ∑ d ∈ D, lam d * data S x d - ∑ n ∈ S, u n ≤ ∑ n ∈ S, P n * y n := by
  rw [sum_congr rfl fun d hd => by rw [hdata d hd]]
  exact weak_duality S D y P lam u hy0 hy1 hu hdual

/-- The parity form: one `y` in the box with the data of `x` and no prime mass kills every
certificate. -/
theorem no_certificate_of_zero (S D : Finset ℕ) (x y P lam u : ℕ → ℝ)
    (hy0 : ∀ n ∈ S, 0 ≤ y n) (hy1 : ∀ n ∈ S, y n ≤ 1) (hu : ∀ n ∈ S, 0 ≤ u n)
    (hdual : ∀ n ∈ S, ∑ d ∈ D.filter (· ∣ n), lam d - u n ≤ P n)
    (hdata : ∀ d ∈ D, data S x d = data S y d) (hzero : ∑ n ∈ S, P n * y n = 0) :
    ∑ d ∈ D, lam d * data S x d - ∑ n ∈ S, u n ≤ 0 :=
  hzero ▸ same_data_bound S D x y P lam u hy0 hy1 hu hdual hdata

/-- Vacuity test: `S = {2, 4}`, `D = {1, 4}`, `P = 1_{n = 2}`, `x = 1` on `S`. The certificate
`lam 1 = 1`, `lam 4 = -1`, `u = 0` is dual feasible and gives the bound `A_1 - A_4 = 2 - 1 = 1`,
the exact prime mass. -/
theorem weak_duality_example :
    ∑ d ∈ ({1, 4} : Finset ℕ), (fun d => if d = 1 then (1 : ℝ) else -1) d *
        data {2, 4} (fun _ => 1) d - ∑ n ∈ ({2, 4} : Finset ℕ), (fun _ => (0 : ℝ)) n
      ≤ ∑ n ∈ ({2, 4} : Finset ℕ), (fun n => if n = 2 then (1 : ℝ) else 0) n * (fun _ => 1) n ∧
    ∑ d ∈ ({1, 4} : Finset ℕ), (fun d => if d = 1 then (1 : ℝ) else -1) d *
        data {2, 4} (fun _ => 1) d - ∑ n ∈ ({2, 4} : Finset ℕ), (fun _ => (0 : ℝ)) n = 1 := by
  refine ⟨weak_duality _ _ _ _ _ _ (by simp) (by simp) (by simp) ?_, ?_⟩
  · intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl <;> simp [filter_insert, filter_singleton]
  · simp [data, filter_insert, filter_singleton]
    norm_num

end LeanLab.Routes.R5062
