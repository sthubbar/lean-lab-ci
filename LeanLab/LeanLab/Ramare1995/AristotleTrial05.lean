/-
Aristotle trial 5, lean-aristotle 2026-10-27. Target from MOUNTAIN.md, folder Ramare1995,
file Decomp1526b.lean, OPEN leaf `sum_Icc_sum_divisors_le`: sum over m <= n of sum over d | m
of g(d) is at most n times sum over d <= n of g(d)/d.
Statement and the definitions `oddFac` and `gfun` copied character for character from
Decomp1526b.lean on main, inlined here in their own namespace, unchanged. Proof written by
Aristotle, Harmonic, project 730a02db-001f-4aea-8c45-57a6e5645d08, on Lean 4.28; checked by
lean-aristotle on Lean and Mathlib 4.35 standalone: builds, axioms propext, Classical.choice,
Quot.sound only, no banned token. This repo file itself is NOT yet built in the lane: the
lean-refresh merge rebuild is the trusted check; linking it to Decomp1526b's defs is
lean-refresh's call. AI wrote the Lean code.
-/
import Mathlib

open Finset Real
open scoped Classical

noncomputable section
namespace LeanLab.Ramare1995.AristotleTrial05

def oddFac (N : ℕ) : ℝ :=
  ∏ p ∈ N.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))

def gfun (d : ℕ) : ℝ :=
  if Squarefree d ∧ ¬ Even d then
    ∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 3) / ((p : ℝ) - 2) ^ 2) else 0

lemma gfun_nonneg (d : ℕ) : 0 ≤ gfun d := by
  unfold gfun
  split_ifs with h
  · apply Finset.prod_nonneg
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact h.2 (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
    have : 3 ≤ p := by
      have := hpp.two_le
      omega
    have : (3 : ℝ) ≤ p := by exact_mod_cast this
    apply div_nonneg <;> nlinarith
  · exact le_refl 0

lemma sum_divisors_swap (n : ℕ) (f : ℕ → ℝ) :
    ∑ m ∈ Icc 1 n, ∑ d ∈ m.divisors, f d =
      ∑ d ∈ Icc 1 n, ∑ _m ∈ (Ioc 0 n).filter (d ∣ ·), f d := by
  apply Finset.sum_comm'
  intro m d
  simp only [Finset.mem_Icc, Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hd, hm⟩
    have := Nat.le_of_dvd (by omega) hd
    have := Nat.pos_of_dvd_of_pos hd (by omega)
    omega
  · intro h
    obtain ⟨⟨⟨h1, h2⟩, hd⟩, h3, h4⟩ := h
    exact ⟨⟨by omega, h2⟩, hd, by omega⟩

theorem sum_Icc_sum_divisors_le (n : ℕ) :
    ∑ m ∈ Icc 1 n, ∑ d ∈ m.divisors, gfun d ≤ n * ∑ d ∈ Icc 1 n, gfun d / d := by
  rw [sum_divisors_swap, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]
  have hd1 : (1 : ℝ) ≤ d := by
    have := (Finset.mem_Icc.mp hd).1
    exact_mod_cast this
  have key : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := Nat.cast_div_le
  have hg := gfun_nonneg d
  calc ((n / d : ℕ) : ℝ) * gfun d ≤ ((n : ℝ) / d) * gfun d :=
        mul_le_mul_of_nonneg_right key hg
    _ = n * (gfun d / d) := by ring

end LeanLab.Ramare1995.AristotleTrial05

end
