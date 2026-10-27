/-
P0083, page 489, equation 37. Euler product for the convergent coefficient series.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.WeightedConvergence

namespace LeanLab.Perelli1996.Section3
open Finset Real Polynomial

/-- The coefficient series equals its Euler product; the factor at two is one. -/
theorem weighted_roots_eulerProduct (F : ℤ[X]) (hF : Admissible F) :
    (∑' d : ℕ, arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ) / d) =
      ∏' p : Nat.Primes, (1 + arithmeticFactor p.1 * ((Roots.rootResidues F p.1).card : ℝ) / p.1) := by
  let g (d : ℕ) : ℝ := arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ) / d
  have hg0 : g 0 = 0 := by simp [g]
  have hg1 : g 1 = 1 := by simp [g, arithmeticFactor_one, Roots.rootResidues]
  have hgmul {m n : ℕ} (hcop : Nat.Coprime m n) : g (m * n) = g m * g n := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hg0]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hg0]
    dsimp [g]
    rw [arithmeticFactor_mul hcop, Roots.root_count_mul F m n hm hn hcop]
    push_cast
    field_simp
  have hgnonneg (d : ℕ) : 0 ≤ g d :=
    div_nonneg (mul_nonneg (arithmeticFactor_nonneg d) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hsum : Summable (fun d => ‖g d‖) := by
    have hs := summable_weighted_roots F hF
    change Summable g at hs
    convert hs using 1
    funext d
    rw [Real.norm_eq_abs, abs_of_nonneg (hgnonneg d)]
  have heuler := EulerProduct.eulerProduct_tprod (f := g) hg1 (fun {_ _} h => hgmul h) hsum hg0
  have hfac (p : Nat.Primes) : (∑' e : ℕ, g (p.1 ^ e)) = 1 + g p.1 := by
    have htail (e : ℕ) (he : e ∉ ({0, 1} : Finset ℕ)) : g (p.1 ^ e) = 0 := by
      have he2 : 2 ≤ e := by simp only [Finset.mem_insert, Finset.mem_singleton] at he; omega
      have hns : ¬ Squarefree (p.1 ^ e) := by
        rw [Nat.squarefree_pow_iff p.2.ne_one (by omega)]
        simp only [not_and]
        intro _
        omega
      simp [g, arithmeticFactor_nonsquarefree hns]
    calc (∑' e : ℕ, g (p.1 ^ e)) = ∑ e ∈ ({0, 1} : Finset ℕ), g (p.1 ^ e) := tsum_eq_sum htail
      _ = 1 + g p.1 := by
        rw [Finset.sum_pair (by decide : (0 : ℕ) ≠ 1), pow_zero, pow_one, hg1]
  calc (∑' d : ℕ, g d) = ∏' p : Nat.Primes, ∑' e : ℕ, g (p.1 ^ e) := heuler.symm
    _ = ∏' p : Nat.Primes, (1 + g p.1) := tprod_congr hfac

/-- Equation 37 with the odd prime product exactly as printed. -/
theorem weighted_roots_eulerProduct_odd (F : ℤ[X]) (hF : Admissible F) :
    (∑' d : ℕ, arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ) / d) =
      ∏' p : {p : ℕ // p.Prime ∧ 2 < p},
        (1 + ((Roots.rootResidues F p.1).card : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 2))) := by
  classical
  rw [weighted_roots_eulerProduct F hF]
  let g (p : Nat.Primes) : ℝ := 1 + arithmeticFactor p.1 * ((Roots.rootResidues F p.1).card : ℝ) / p.1
  let embed (p : {p : ℕ // p.Prime ∧ 2 < p}) : Nat.Primes := ⟨p.1, p.2.1⟩
  have hinj : Function.Injective embed := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun p : Nat.Primes => p.1) h
  have hs : Function.mulSupport g ⊆ Set.range embed := by
    intro p hp
    change g p ≠ 1 at hp
    have hcases : p.1 = 2 ∨ 2 < p.1 := by have := p.2.two_le; omega
    rcases hcases with hp2 | hpgt
    · exfalso
      apply hp
      dsimp [g]
      rw [hp2, arithmeticFactor_even (by norm_num : 2 ∣ 2)]
      norm_num
    · exact ⟨⟨p.1, p.2, hpgt⟩, rfl⟩
  have heq := hinj.tprod_eq hs
  change (∏' p : Nat.Primes, g p) = _
  rw [← heq]
  apply tprod_congr
  intro p
  dsimp [g, embed]
  rw [arithmeticFactor_prime p.2.1 p.2.2]
  have hpR : (2 : ℝ) < p.1 := by exact_mod_cast p.2.2
  have hp0 : (p.1 : ℝ) ≠ 0 := by linarith
  have hp2 : (p.1 : ℝ) - 2 ≠ 0 := by linarith
  field_simp <;> ring

end LeanLab.Perelli1996.Section3
