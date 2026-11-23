import LeanLab.Halupczok2012.Statements
import LeanLab.Halupczok2012.Decomp329f
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Leaves for `leaf_wu_theorem` in `DecompJ219`, Halupczok journal page 345, proof of
Corollary 1.3, which cites Wu's result on Chen primes in short intervals.
https://doi.org/10.5802/jtnb.839

The cited result is Wu 2004, Acta Arith. 114, Theorem 5, with exponent 0.971, in the sifted
form produced by its Chen sieve. The proved packing step
`Decomp329f.wu_of_fixed_power_count` passes from fixed length windows `x^θ` to every `Y`
with `X^θ ≤ Y ≤ X`. The assembly `leaf_wu_theorem_of_leaves` is proved here sorry free.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.DecompJ219LeavesWu

open Finset
open scoped Classical

/-- LEAF: P0077 page 345, proof of Corollary 1.3, Wu's result on Chen primes in short
intervals. Class HARD. CITED-LEFT: pure citation of Wu 2004 Theorem 5, P0036 page 5, at
θ = 0.971, in the sifted form its Chen sieve proves, p + 2 = P2 with all prime factors at
least x^δ. The page image of P0036 page 5 prints θ ⩾ 0.971. -/
theorem leaf_wu2004_thm5_sifted :
    ∃ δ > (0 : ℝ), ∃ c > (0 : ℝ), ∃ x0 > (0 : ℝ), ∀ x : ℝ, x0 ≤ x →
      c * x ^ (0.971 : ℝ) / Real.log x ^ 2 ≤
        ((kRange x (x ^ (0.971 : ℝ))).filter (fun p : ℕ => p.Prime ∧ IsP 2 (p + 2) ∧
          ∀ r : ℕ, r.Prime → r ∣ p + 2 → x ^ δ ≤ r)).card := by
  sorry

/-- Sifting by primes at least `x^δ > 3` removes the residue `p + 2 ≡ 0 (mod 3)`. -/
theorem sifted_not_three {x δ : ℝ} (h3 : (3 : ℝ) < x ^ δ) {p : ℕ}
    (hp : ∀ r : ℕ, r.Prime → r ∣ p + 2 → x ^ δ ≤ r) : ¬ 3 ∣ p + 2 := by
  intro h
  have := hp 3 Nat.prime_three h
  push_cast at this
  linarith

/-- The fixed window count with `3 ∤ p + 2`, the exact statement of
`Decomp329g.fixed_wu_rough_count_leaf`, from the sifted Wu leaf. -/
theorem fixed_wu_count_of_sifted :
    ∃ c > 0, ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → 2 ≤ X →
      c * X ^ (0.971 : ℝ) / (Real.log X) ^ 2 ≤
        (((kRange X (X ^ (0.971 : ℝ))).filter
          (fun p => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2))).card : ℝ) := by
  obtain ⟨δ, hδ, c, hc, x0, _, hw⟩ := leaf_wu2004_thm5_sifted
  set x1 : ℝ := (4 : ℝ) ^ (1 / δ) with hx1
  have hx1pos : 0 < x1 := by positivity
  refine ⟨c, hc, max x0 x1, fun x hx _ => ?_⟩
  have hxx0 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have hxx1 : x1 ≤ x := le_trans (le_max_right _ _) hx
  have h3 : (3 : ℝ) < x ^ δ := by
    have h4 : x1 ^ δ = 4 := by
      rw [hx1, ← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hδ.ne', Real.rpow_one]
    have : x1 ^ δ ≤ x ^ δ := Real.rpow_le_rpow hx1pos.le hxx1 hδ.le
    linarith
  refine le_trans (hw x hxx0) ?_
  exact_mod_cast card_le_card fun p hp => by
    rw [mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.1, sifted_not_three h3 hp.2.2.2⟩

/-- Assembly: the exact statement of `DecompJ219.leaf_wu_theorem` from the cited Wu leaf
and the proved packing step `Decomp329f.wu_of_fixed_power_count`. -/
theorem leaf_wu_theorem_of_leaves :
  ∃ c > 0, ∃ Y0 > 0, ∀ (X Y : ℝ), Y0 ≤ Y → X ^ (0.971 : ℝ) ≤ Y → Y ≤ X →
    c * Y / (Real.log Y) ^ 2 ≤ (@Finset.filter ℕ (fun (p : ℕ) => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2)) (Classical.decPred _) (kRange X Y)).card :=
  Decomp329f.wu_of_fixed_power_count fixed_wu_count_of_sifted

end LeanLab.Halupczok2012.DecompJ219LeavesWu
