/- AI-written Lean code by OpenAI Codex, task362, 2026-11-05. Binary Goldbach is open. -/
import LeanLab.Tchudakov1938.Decomp362a

namespace LeanLab.Tchudakov1938.Decomp362i
open Real Filter MeasureTheory
set_option maxHeartbeats 400000

/-- LEAF. P0064, page 34, last display in the Lemma 13 proof. The quartic tail above a positive integer has cubic decay with an explicit constant. -/
theorem quartic_tail_nat (N : ℕ) (hN : 1 ≤ N) :
    (∑' k : ℕ, 1 / ((k + N : ℕ) : ℝ)^4) ≤ (4 / 3 : ℝ) / (N : ℝ)^3 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-4 : ℝ)) (Set.Ici (N : ℝ)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (hN0.trans_le hx) hxy (by norm_num)
  have hint : IntegrableOn (fun t : ℝ => t ^ (-4 : ℝ)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hN0
  have ht := hanti.tsum_comp_add_le_integral N hint (fun t ht => Real.rpow_nonneg (le_of_lt (hN0.trans (show (N : ℝ) < t from ht))) _)
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) hN0] at ht
  have hs : Summable (fun k : ℕ => 1 / (k : ℝ)^4) := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff N).mpr hs
  have heq := hshift.tsum_eq_zero_add
  simp only [zero_add, Nat.add_assoc, Nat.add_comm 1 N] at heq
  rw [heq]
  have ht' : (∑' k : ℕ, 1 / ((k + (N + 1) : ℕ) : ℝ)^4) ≤ (1 / 3 : ℝ) / (N : ℝ)^3 := by
    convert ht using 1
    · apply tsum_congr
      intro k
      rw [show (-4 : ℝ) = -(4 : ℕ) by norm_num, Real.rpow_neg_natCast]
      simp [Nat.add_assoc]
    · norm_num [Real.rpow_neg_natCast]
      ring
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : (N : ℝ)^3 ≤ (N : ℝ)^4 := pow_le_pow_right₀ hNR (by norm_num)
  have hinv : 1 / (N : ℝ)^4 ≤ 1 / (N : ℝ)^3 :=
    one_div_le_one_div_of_le (by positivity) hpow
  calc
    1 / (N : ℝ)^4 + (∑' k : ℕ, 1 / ((k + (N + 1) : ℕ) : ℝ)^4) ≤
      1 / (N : ℝ)^4 + (1 / 3 : ℝ) / (N : ℝ)^3 := add_le_add le_rfl ht'
    _ ≤ 1 / (N : ℝ)^3 + (1 / 3 : ℝ) / (N : ℝ)^3 := add_le_add hinv le_rfl
    _ = (4 / 3 : ℝ) / (N : ℝ)^3 := by ring

/-- P0064, page 34, last display in the Lemma 13 proof. The tail beginning at floor Q has the required cubic decay for Q at least two. -/
theorem quartic_tail_real (Q : ℝ) (hQ : 2 ≤ Q) :
    (∑' k : ℕ, 1 / ((k + ⌊Q⌋₊ : ℕ) : ℝ)^4) ≤ (32 / 3 : ℝ) / Q^3 := by
  have hQ0 : 0 < Q := by linarith
  have hN : 1 ≤ ⌊Q⌋₊ := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hNR : (1 : ℝ) ≤ (⌊Q⌋₊ : ℝ) := by exact_mod_cast hN
  have hfloor : Q < (⌊Q⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hhalf : Q / 2 ≤ (⌊Q⌋₊ : ℝ) := by linarith
  have hpow : (Q / 2)^3 ≤ (⌊Q⌋₊ : ℝ)^3 := pow_le_pow_left₀ (by positivity) hhalf 3
  calc
    _ ≤ (4 / 3 : ℝ) / (⌊Q⌋₊ : ℝ)^3 := quartic_tail_nat ⌊Q⌋₊ hN
    _ ≤ (4 / 3 : ℝ) / (Q / 2)^3 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
    _ = (32 / 3 : ℝ) / Q^3 := by ring

end LeanLab.Tchudakov1938.Decomp362i
