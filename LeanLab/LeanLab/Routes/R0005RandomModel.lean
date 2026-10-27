import Mathlib

/-!
# R-0005, the Hardy-Littlewood local densities for one N

T3 MOONSHOT route, unit U-1026. AI wrote this Lean code. KNOWN mathematics.

`localCount p N` counts residues `a mod p` with `a ≠ 0` and `N - a ≠ 0`: the residue classes
mod `p` in which both summands of `N = a + (N - a)` can be prime, once `a, N - a > p`.
It is `p - 1` when `p ∣ N` and `p - 2` otherwise. The local density
`σ p N = p * localCount p N / (p - 1)^2` is the Euler factor of the singular series:
`1 - 1/(p-1)^2` when `p ∤ N`, the twin prime factor, and `p/(p-1)` when `p ∣ N`,
which is that factor times `(p-1)/(p-2)`. At `p = 2` and odd `N` the count is `0`, the only
local obstruction. These facts are what the Cramér-Granville random model feeds the main term;
they say nothing about whether a single `N` is a sum of two primes.
-/

namespace LeanLab.Routes.R0005

open Finset

/-- residues `a mod p` with `a` and `N - a` both nonzero -/
def localCount (p : ℕ) [NeZero p] (N : ZMod p) : ℕ :=
  (univ.filter (fun a : ZMod p => a ≠ 0 ∧ N - a ≠ 0)).card

theorem filter_eq (p : ℕ) [NeZero p] (N : ZMod p) :
    univ.filter (fun a : ZMod p => a ≠ 0 ∧ N - a ≠ 0) = univ \ {0, N} := by
  ext a
  simp [sub_eq_zero, eq_comm]

theorem localCount_eq (p : ℕ) [NeZero p] (N : ZMod p) :
    localCount p N = if N = 0 then p - 1 else p - 2 := by
  unfold localCount
  rw [filter_eq, card_sdiff_of_subset (subset_univ _), card_univ, ZMod.card]
  split_ifs with h
  · subst h; simp
  · rw [card_pair (Ne.symm h)]

/-- the parity obstruction at 2: odd `N` has no local solution mod 2 -/
theorem localCount_two_odd (N : ZMod 2) (h : N ≠ 0) : localCount 2 N = 0 := by
  rw [localCount_eq]; simp [h]

/-- even `N`: one local solution mod 2 -/
theorem localCount_two_even : localCount 2 0 = 1 := by
  rw [localCount_eq]; simp

/-- the local density, the Euler factor of the singular series -/
noncomputable def sigma (p : ℕ) [NeZero p] (N : ZMod p) : ℝ :=
  (p : ℝ) * localCount p N / ((p : ℝ) - 1) ^ 2

theorem sigma_ndvd (p : ℕ) [NeZero p] (hp : 3 ≤ p) (N : ZMod p) (hN : N ≠ 0) :
    sigma p N = 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  unfold sigma
  rw [localCount_eq]; simp only [hN, ite_false]
  have h1 : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [h1]
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h3 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hne : ((p : ℝ) - 1) ^ 2 ≠ 0 := pow_ne_zero 2 h3
  rw [div_eq_iff hne]
  field_simp
  ring

theorem sigma_dvd (p : ℕ) [NeZero p] (hp : 3 ≤ p) :
    sigma p 0 = (1 - 1 / ((p : ℝ) - 1) ^ 2) * (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  unfold sigma
  rw [localCount_eq]; simp only [ite_true]
  have h1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [h1]
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
  have h3 : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- the extra factor at primes dividing `N` is at least one, so the singular series of an
even `N` is at least `2 C₂` -/
theorem localFactor_ge_one (p : ℕ) (hp : 3 ≤ p) :
    1 ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem sigma_pos (p : ℕ) [NeZero p] (hp : 3 ≤ p) (N : ZMod p) : 0 < sigma p N := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  by_cases hN : N = 0
  · subst hN; rw [sigma_dvd p hp]
    have : 1 / ((p : ℝ) - 1) ^ 2 < 1 := by
      rw [div_lt_one (by nlinarith)]; nlinarith
    have : 0 < ((p : ℝ) - 1) / ((p : ℝ) - 2) := div_pos (by linarith) (by linarith)
    nlinarith
  · rw [sigma_ndvd p hp N hN]
    have : 1 / ((p : ℝ) - 1) ^ 2 < 1 := by
      rw [div_lt_one (by nlinarith)]; nlinarith
    linarith

/-- vacuity check: at `p = 3`, `N = 1` the hypotheses hold and the count is `1`;
at `p = 3`, `N = 0` it is `2` -/
example : localCount 3 1 = 1 := by rw [localCount_eq]; decide
example : localCount 3 0 = 2 := by rw [localCount_eq]; rfl

end LeanLab.Routes.R0005
