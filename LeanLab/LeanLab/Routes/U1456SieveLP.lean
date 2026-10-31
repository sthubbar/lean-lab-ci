import Mathlib

/-!
# R-0048, T3 MOONSHOT: the sieve linear program on A = {N - p}

Unit U-1456, PC run 20261022T0003Z-15508. AI wrote this Lean code, Claude. Checked only by
the Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it.

Route. Treat a sieve lower bound for the Goldbach count as a linear programming certificate:
a vector `c` with `Σ_{n ∈ P} z n ≥ Σ_i c i * ⟪L i, z⟫` for every nonnegative `z`, where the
`L i` are the data functionals, such as the divisor counts `Σ_{d ∣ n} z n`. Weak duality then
says the certificate is worthless as soon as one nonnegative decoy `y` matches the data of the
true sequence `x` and puts no mass on the target set `P`: `sieve_lp_blind`.

The parity breaking functional is a Liouville moment: `odd_mass_eq` shows that the total
mass and the Liouville moment together fix the mass on `λ = -1`, which contains the primes.
-/

namespace LeanLab.Routes.U1456

open Finset

/-- Weak duality blindness. If a decoy `y ≥ 0` has the same data as `x` for every functional
`L i` and no mass on `P`, then every valid LP lower bound certificate `c` gives a bound at
most `0` for `x`. -/
theorem sieve_lp_blind {α ι : Type*} [DecidableEq α] (S : Finset α) (I : Finset ι) (P : Finset α)
    (L : ι → α → ℝ) (c : ι → ℝ) (x y : α → ℝ)
    (hcert : ∀ z : α → ℝ, (∀ n ∈ S, 0 ≤ z n) →
      ∑ i ∈ I, c i * ∑ n ∈ S, L i n * z n ≤ ∑ n ∈ S ∩ P, z n)
    (hy : ∀ n ∈ S, 0 ≤ y n)
    (hdata : ∀ i ∈ I, ∑ n ∈ S, L i n * y n = ∑ n ∈ S, L i n * x n)
    (hzero : ∑ n ∈ S ∩ P, y n = 0) :
    ∑ i ∈ I, c i * ∑ n ∈ S, L i n * x n ≤ 0 := by
  have h := hcert y hy
  rw [hzero] at h
  calc ∑ i ∈ I, c i * ∑ n ∈ S, L i n * x n
      = ∑ i ∈ I, c i * ∑ n ∈ S, L i n * y n := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hdata i hi]
    _ ≤ 0 := h

/-- The mass on `λ = -1` is fixed by the total mass and the Liouville moment, for any
weights `y` and any `±1` valued `lam`. -/
theorem odd_mass_eq {α : Type*} [DecidableEq α] (S : Finset α) (lam y : α → ℝ)
    (hlam : ∀ n ∈ S, lam n = 1 ∨ lam n = -1) :
    2 * ∑ n ∈ S.filter (fun n => lam n = -1), y n
      = ∑ n ∈ S, y n - ∑ n ∈ S, lam n * y n := by
  classical
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  rcases hlam n hn with h | h
  · rw [if_neg (by rw [h]; norm_num), h]; ring
  · rw [if_pos h, h]; ring

/-- Vacuity: the certificate, data and decoy hypotheses of `sieve_lp_blind` can all hold.
Support `{3, 4}`, target `P = {3}`, one functional, the total count, with `x = 1_{3}` and
decoy `y = 1_{4}`; the certificate `c = 0` is valid. -/
example : ∑ i ∈ ({0} : Finset ℕ), (0 : ℝ) *
      ∑ n ∈ ({3, 4} : Finset ℕ), (fun _ _ => (1 : ℝ)) i n * (if n = 3 then 1 else 0) ≤ 0 := by
  refine sieve_lp_blind ({3, 4} : Finset ℕ) {0} {3} (fun _ _ => (1 : ℝ)) (fun _ => 0)
    (fun n => if n = 3 then 1 else 0) (fun n => if n = 4 then 1 else 0) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [zero_mul, Finset.sum_const_zero]
    exact Finset.sum_nonneg fun n hn => hz n (Finset.mem_inter.mp hn).1
  · intro n _; split_ifs <;> norm_num
  · intro i _; simp
  · simp

/-- Vacuity for `odd_mass_eq`: `S = {2, 4}` with `λ 2 = -1`, `λ 4 = 1`, unit weights. -/
example : 2 * ∑ n ∈ ({2, 4} : Finset ℕ).filter
      (fun n => (if n = 2 then (-1 : ℝ) else 1) = -1), (1 : ℝ)
    = ∑ n ∈ ({2, 4} : Finset ℕ), (1 : ℝ)
      - ∑ n ∈ ({2, 4} : Finset ℕ), (if n = 2 then (-1 : ℝ) else 1) * 1 :=
  odd_mass_eq _ (fun n => if n = 2 then (-1 : ℝ) else 1) (fun _ => 1)
    (fun _ _ => by split_ifs <;> simp)

end LeanLab.Routes.U1456

#print axioms LeanLab.Routes.U1456.sieve_lp_blind
#print axioms LeanLab.Routes.U1456.odd_mass_eq
