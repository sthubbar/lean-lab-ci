/-
P0045, journal page 779, display 30.
The product remainder has the printed logarithmic size.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LPZ2007.D4Product

namespace LeanLab.LPZ2007.D4ProductLog

open Finset Real

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The Euler weight is at most five times exp 27 times log L. -/
theorem product_weight_log (V : Finset ℕ) (n : ℕ → ℕ) {X L : ℝ}
    (_hX : 0 < X) (hL : 2 ≤ L) (hlog : log X = L * log 2)
    (hn : ∀ v ∈ V, n v ≠ 0) (hnX : ∀ v ∈ V, (n v : ℝ) ≤ X)
    (hcard : (V.card : ℝ) ≤ L) :
    ∑ s ∈ (LeanLab.LPZ2007B.opf (∏ v ∈ V, n v)).powerset,
      LeanLab.LPZ2007B.W s ≤ 5 * exp 27 * log L := by
  let P := ∏ v ∈ V, n v
  have hP0 : P ≠ 0 := prod_ne_zero_iff.2 hn
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
  have hYle : (Y : ℝ) ≤ L ^ 2 + 5 := by
    dsimp [Y]
    push_cast
    linarith [Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ L ^ 2)]
  have hL3 : 8 ≤ L ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL 3
    norm_num at this
    exact this
  have hL5 : L ^ 2 + 5 ≤ L ^ 5 := by
    calc L ^ 2 + 5 ≤ L ^ 2 * 8 := by nlinarith
      _ ≤ L ^ 2 * L ^ 3 := mul_le_mul_of_nonneg_left hL3 (sq_nonneg _)
      _ = L ^ 5 := by ring
  have hlogY : log (Y : ℝ) ≤ 5 * log L := by
    have := log_le_log (by positivity : (0 : ℝ) < Y) (hYle.trans hL5)
    simpa only [log_pow, Nat.cast_ofNat] using this
  calc ∑ s ∈ (LeanLab.LPZ2007B.opf P).powerset, LeanLab.LPZ2007B.W s
      ≤ exp 27 * log Y := LeanLab.LPZ2007B.sum_W_opf_le P Y hY hωY
    _ ≤ exp 27 * (5 * log L) := mul_le_mul_of_nonneg_left hlogY (exp_pos _).le
    _ = 5 * exp 27 * log L := by ring

end
end LeanLab.LPZ2007.D4ProductLog

#print axioms LeanLab.LPZ2007.D4ProductLog.product_weight_log
