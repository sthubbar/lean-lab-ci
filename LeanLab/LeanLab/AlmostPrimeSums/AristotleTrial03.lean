/-
Aristotle trial 3, lean-aristotle 2026-10-27. Target from MOUNTAIN.md, folder AlmostPrimeSums,
file Decomp1544c.lean, OPEN leaf `two_pow_omega_le`: for every delta > 0 there is C > 0 with
2^omega(N) <= C N^delta for all N >= 1.
Statement copied character for character from Decomp1544c.lean on main, unchanged; own namespace
only. Proof written by Aristotle, Harmonic, project 0a15b114-8817-4382-b176-d15831f19978, on
Lean 4.28; checked by lean-aristotle on Lean and Mathlib 4.35 standalone: builds, axioms
propext, Classical.choice, Quot.sound only, no banned token. This repo file itself is NOT yet
built in the lane: the lean-refresh merge rebuild is the trusted check. Wiring it into
Decomp1544c is lean-refresh's call. AI wrote the Lean code.
-/
import Mathlib

open Finset Real Filter Topology
open scoped ArithmeticFunction.omega

namespace LeanLab.AlmostPrimeSums.AristotleTrial03

/-- A natural number `p` with `(p : ℝ) ^ δ < 2` is smaller than `⌈2 ^ (1/δ)⌉₊`. -/
lemma lt_ceil_of_rpow_lt_two {δ : ℝ} (hδ : 0 < δ) {p : ℕ} (hp : (p : ℝ) ^ δ < 2) :
    p < ⌈(2 : ℝ) ^ (1 / δ)⌉₊ := by
  by_contra h
  push Not at h
  have h1 : (2 : ℝ) ^ (1 / δ) ≤ p := (Nat.ceil_le).1 h
  have h2 : ((2 : ℝ) ^ (1 / δ)) ^ δ ≤ (p : ℝ) ^ δ :=
    Real.rpow_le_rpow (by positivity) h1 hδ.le
  rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδ.ne', Real.rpow_one] at h2
  linarith

theorem two_pow_omega_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → (2 : ℝ) ^ ω N ≤ C * (N : ℝ) ^ δ := by
  set M := ⌈(2 : ℝ) ^ (1 / δ)⌉₊
  refine ⟨2 ^ M, by positivity, fun N hN => ?_⟩
  classical
  set S : Finset ℕ := N.primeFactors
  set A := S.filter (fun p : ℕ => (p : ℝ) ^ δ < 2)
  set B := S.filter (fun p : ℕ => ¬ (p : ℝ) ^ δ < 2)
  have hω : ω N = A.card + B.card := by
    have : ω N = S.card := by
      rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]; rfl
    rw [this]
    exact (Finset.card_filter_add_card_filter_not _).symm
  have hA : A.card ≤ M := by
    have : A ⊆ Finset.range M := by
      intro p hp
      simp only [A, Finset.mem_filter] at hp
      exact Finset.mem_range.2 (lt_ceil_of_rpow_lt_two hδ hp.2)
    simpa using Finset.card_le_card this
  have hB : (2 : ℝ) ^ B.card ≤ (N : ℝ) ^ δ := by
    calc (2 : ℝ) ^ B.card = ∏ p ∈ B, (2 : ℝ) := by simp
      _ ≤ ∏ p ∈ B, ((p : ℝ) ^ δ) := by
          refine Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun p hp => ?_)
          simp only [B, Finset.mem_filter] at hp
          linarith [hp.2]
      _ = (∏ p ∈ B, (p : ℝ)) ^ δ := by
          rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
      _ ≤ (N : ℝ) ^ δ := by
          apply Real.rpow_le_rpow (by positivity) _ hδ.le
          have hdvd : ∏ p ∈ B, p ∣ N :=
            (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans
              (Nat.prod_primeFactors_dvd N)
          have : ∏ p ∈ B, p ≤ N := Nat.le_of_dvd (by omega) hdvd
          rw [← Nat.cast_prod]
          exact_mod_cast this
  rw [hω, pow_add]
  have hA' : (2 : ℝ) ^ A.card ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hA
  exact mul_le_mul hA' hB (by positivity) (by positivity)

end LeanLab.AlmostPrimeSums.AristotleTrial03
