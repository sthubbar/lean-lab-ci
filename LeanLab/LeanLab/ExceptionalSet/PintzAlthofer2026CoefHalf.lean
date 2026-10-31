/-
# Pintz and Althöfer 2026, (4.18) with the Euler product bounded below by 1/2

Unit U-1146, T2 FRONTIER, idea I-0080, run 20261020T0103Z-16649.

`prod_ge_half`: ∏_{2<p≤P} (1 − 1/(p−1)²) ≥ 1/2 for every P, since p − 1 runs over distinct
integers m ≥ 2 and ∏_{2≤m≤M} (1 − 1/m²) = (M+1)/(2M), `prod_sq_eq`. Hence, from `coef418`:

  ‖vTrunc X P P w n‖ ≥ n e^{−n/X} (1 − 12 τ(n)²/√P) − X/(2π²P) · C e (1 + log P/log 2) τ(n)² (1 + log P)

for every even n ≥ 2, P ≥ 2, X > 0, `coef418_half`. The bracket is now free of P except
through τ(n)²/√P. The true constant is 2C₂ ≈ 1.3203; 1 is enough for the lower half of
BesselInput. AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.PintzAlthofer2026Coef

namespace LeanLab.ExceptionalSet.PintzAlthofer2026CoefHalf

open Finset Real LeanLab.Routes.R5060

/-- ∏_{m=2}^{M} (1 − 1/m²) = (M+1)/(2M) for M ≥ 2. -/
theorem prod_sq_eq : ∀ M : ℕ, 2 ≤ M →
    ∏ m ∈ Icc 2 M, (1 - 1 / ((m : ℝ)) ^ 2) = ((M : ℝ) + 1) / (2 * M) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    rw [prod_Icc_succ_top (by omega), ih]
    have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
    push_cast
    field_simp
    ring

/-- The product over primes 2 < p ≤ P of (1 − 1/(p−1)²) is at least 1/2. -/
theorem prod_ge_half (P : ℕ) :
    (1 / 2 : ℝ) ≤ ∏ p ∈ (Nat.primesLE P).filter (2 < ·), (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  set S := (Nat.primesLE P).filter (2 < ·)
  have hS : ∀ p ∈ S, 3 ≤ p := fun p hp => by
    simp only [S, mem_filter] at hp; omega
  -- reindex by m = p - 1
  have hinj : Set.InjOn (fun p : ℕ => p - 1) (S : Set ℕ) := by
    intro a ha b hb hab
    have := hS a ha; have := hS b hb
    simp only at hab; omega
  have hre : ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1) ^ 2) =
      ∏ m ∈ S.image (fun p : ℕ => (p - 1 : ℕ)), (1 - 1 / ((m : ℕ) : ℝ) ^ 2) := by
    rw [prod_image hinj]
    refine prod_congr rfl fun p hp => ?_
    have := hS p hp
    rw [Nat.cast_sub (by omega)]; simp
  rw [hre]
  set T := S.image (fun p : ℕ => (p - 1 : ℕ))
  set M := max P 2
  have hsub : T ⊆ Icc 2 M := by
    intro m hm
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hm
    have h3 := hS p hp
    have hpP : p ≤ P := by
      simp only [S, mem_filter, Nat.primesLE, Nat.mem_primesBelow] at hp; omega
    exact mem_Icc.2 ⟨by omega, by omega⟩
  have hf0 : ∀ m ∈ Icc 2 M, 0 ≤ 1 - 1 / ((m : ℝ)) ^ 2 := by
    intro m hm
    have : (2 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.1 hm).1
    have : 1 / ((m : ℝ)) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    linarith
  have hf1 : ∀ m ∈ Icc 2 M, 1 - 1 / ((m : ℝ)) ^ 2 ≤ 1 := by
    intro m hm
    have : 0 ≤ 1 / ((m : ℝ)) ^ 2 := by positivity
    linarith
  have hsplit := prod_sdiff hsub (f := fun m : ℕ => 1 - 1 / ((m : ℝ)) ^ 2)
  have hrest : ∏ m ∈ Icc 2 M \ T, (1 - 1 / ((m : ℝ)) ^ 2) ≤ 1 :=
    prod_le_one₀ (fun m hm => hf0 m (sdiff_subset hm)) (fun m hm => hf1 m (sdiff_subset hm))
  have hT0 : 0 ≤ ∏ m ∈ T, (1 - 1 / ((m : ℝ)) ^ 2) :=
    prod_nonneg fun m hm => hf0 m (hsub hm)
  have hfull : ∏ m ∈ Icc 2 M, (1 - 1 / ((m : ℝ)) ^ 2) = ((M : ℝ) + 1) / (2 * M) :=
    prod_sq_eq M (le_max_right _ _)
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast (le_max_right P 2)
  have hhalf : (1 / 2 : ℝ) ≤ ((M : ℝ) + 1) / (2 * M) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  have : ∏ m ∈ Icc 2 M, (1 - 1 / ((m : ℝ)) ^ 2) ≤ ∏ m ∈ T, (1 - 1 / ((m : ℝ)) ^ 2) := by
    rw [← hsplit]
    calc (∏ m ∈ Icc 2 M \ T, (1 - 1 / ((m : ℝ)) ^ 2)) * ∏ m ∈ T, (1 - 1 / ((m : ℝ)) ^ 2)
        ≤ 1 * ∏ m ∈ T, (1 - 1 / ((m : ℝ)) ^ 2) := mul_le_mul_of_nonneg_right hrest hT0
      _ = _ := one_mul _
  linarith

/-- **(4.18) with bracket 1 − 12τ²/√P**. -/
theorem coef418_half : ∃ C : ℝ, 0 < C ∧ ∀ (n P : ℕ) (X : ℝ), Even n → 2 ≤ n → 2 ≤ P → 0 < X →
    (n * Real.exp (-n / X)) * (1 - 12 * (n.divisors.card : ℝ) ^ 2 / Real.sqrt P)
      - X / (2 * π ^ 2 * P) * (C * (Real.exp 1 * (1 + Real.log P / Real.log 2)) *
          (n.divisors.card : ℝ) ^ 2 * (1 + Real.log P))
      ≤ ‖LeanLab.ExceptionalSet.PintzAlthofer2026Beta.vTrunc X P P
          (fun q => ((bS n q : ℝ) : ℂ)) n‖ := by
  obtain ⟨C, hC, h⟩ := LeanLab.ExceptionalSet.PintzAlthofer2026Coef.coef418
  refine ⟨C, hC, fun n P X hn hn2 hP hX => ?_⟩
  have h1 := h n P X hn hn2 hP hX
  have hA : 0 ≤ (n : ℝ) * Real.exp (-n / X) := by positivity
  have hp := prod_ge_half P
  have : (n * Real.exp (-n / X)) * (1 - 12 * (n.divisors.card : ℝ) ^ 2 / Real.sqrt P) ≤
      (n * Real.exp (-n / X)) * (2 * ∏ p ∈ (Nat.primesLE P).filter (2 < ·),
        (1 - 1 / ((p : ℝ) - 1) ^ 2) - 12 * (n.divisors.card : ℝ) ^ 2 / Real.sqrt P) :=
    mul_le_mul_of_nonneg_left (by linarith) hA
  linarith

end LeanLab.ExceptionalSet.PintzAlthofer2026CoefHalf

