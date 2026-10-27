/-
P0045, journal page 779, display 30.
The prime factors of a product of at most L positive integers at most X give a small weight.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LPZ2007.D4Tail

namespace LeanLab.LPZ2007.D4Product

open Finset Real
open LeanLab.LPZ2007

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The Euler product error is at most delta times L when L is sufficiently large. -/
theorem product_weight_small (V : Finset ℕ) (n : ℕ → ℕ) {X L δ : ℝ}
    (_hX : 0 < X) (hδ : 0 < δ) (hlog : log X = L * log 2)
    (hn : ∀ v ∈ V, n v ≠ 0) (hnX : ∀ v ∈ V, (n v : ℝ) ≤ X)
    (hcard : (V.card : ℝ) ≤ L)
    (hL : (6 * exp 27 / δ) ^ 2 + 1 ≤ L) :
    ∑ s ∈ (LeanLab.LPZ2007B.opf (∏ v ∈ V, n v)).powerset,
      LeanLab.LPZ2007B.W s ≤ δ * L := by
  let P := ∏ v ∈ V, n v
  have hP0 : P ≠ 0 := prod_ne_zero_iff.2 hn
  have hL1 : 1 ≤ L := by nlinarith [sq_nonneg (6 * exp 27 / δ)]
  have hPX : (P : ℝ) ≤ X ^ V.card := by
    dsimp [P]
    rw [Nat.cast_prod, ← prod_const]
    exact prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) hnX
  have hω : (P.primeFactors.card : ℝ) ≤ L ^ 2 := by
    have h2 : (2 : ℝ) ^ P.primeFactors.card ≤ X ^ V.card :=
      (show (2 : ℝ) ^ P.primeFactors.card ≤ (P : ℝ) by
        exact_mod_cast LeanLab.Romanov.two_pow_card_le P hP0).trans hPX
    have h4 := log_le_log (by positivity) h2
    rw [log_pow, log_pow, hlog] at h4
    have hωL : (P.primeFactors.card : ℝ) ≤ V.card * L := by
      have hl2 := log_pos (by norm_num : (1 : ℝ) < 2)
      nlinarith
    nlinarith
  let Y := ⌈L ^ 2⌉₊ + 4
  have hY : 4 ≤ Y := by omega
  have hωY : P.primeFactors.card ≤ Y := by
    have : (P.primeFactors.card : ℝ) ≤ (⌈L ^ 2⌉₊ : ℕ) := hω.trans (Nat.le_ceil _)
    have : P.primeFactors.card ≤ ⌈L ^ 2⌉₊ := by exact_mod_cast this
    omega
  have hlogY : log (Y : ℝ) ≤ 2 + 4 * √L := by
    apply le_trans _ (LeanLab.LPZ2007B.log_sq_add_le L hL1)
    apply log_le_log (by positivity)
    dsimp [Y]
    push_cast
    linarith [Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ L ^ 2)]
  exact (LeanLab.LPZ2007B.sum_W_opf_le P Y hY hωY).trans
    (LeanLab.LPZ2007B.aux_third (exp 27) δ L (log Y) (exp_pos _) hδ hL hlogY)

end
end LeanLab.LPZ2007.D4Product

#print axioms LeanLab.LPZ2007.D4Product.product_weight_small
