import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_arc_energy_offwindow

/-!
Split of `leaf_ofw_high_tail` in `SPLIT_feed1122_leaf_arc_energy_offwindow.lean`, P0029
Bhowmik and Grimmelt 2026 with the arc model of P0083 Pintz 2026.

Beyond the truncation point `X ^ 2` the coefficient of the difference is the coefficient of
`F_{X,X²}²` minus the model coefficient `v_X(n)`, and `|a - b|² ≤ 2|a|² + 2|b|²` gives the leaves

* `leaf_oht_FX_sq_tail`, MEDIUM: the energy of the coefficients of `F_{X,X²}²` beyond `X ^ 2`,
  a partial convolution damped by `e^{-n/X} ≤ e^{-X}`;
* `leaf_oht_model_tail`, MEDIUM: the energy of the model coefficients beyond `X ^ 2`, the damped
  main part and the arc truncation tail of size about `q² X / n`.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.BG2026.Decomp522a

open Finset Real MeasureTheory AddCircle
open LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
open LeanLab.ExceptionalSet.PintzAlthofer2026Model
open LeanLab.ExceptionalSet.BG2026.Supply385

noncomputable section

/-- LEAF: the coefficients of the squared generating function beyond its truncation point,
P0029 section 3: the sum over `n > X ^ 2` of `|ĝ(n)|²`, `g = F_{X,X²}²`, is eventually at most
`C · X^(3/2 + 2Θ + ε)`.  MEDIUM: each such coefficient is a partial convolution of
`Λ(m) e^{-m/X}` with total damping `e^{-n/X} ≤ e^{-X}`, and there are at most `2 X ^ 2` of them. -/
theorem leaf_oht_FX_sq_tail (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if ((X ^ 2 : ℕ) : ℤ) < n then
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2) n‖ ^ 2 else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- LEAF: the model coefficients beyond `X ^ 2`, P0083 display 4.14: the sum over `n > X ^ 2` of
`|v_X(n)|²` is eventually at most `C · X^(3/2 + 2Θ + ε)`.  MEDIUM: the main part
`e^{-n/X} n 𝔖_Q(n)` is damped by `e^{-X}`, and the arc truncation part decays like `q² X / n`,
an `L²` tail of the cut arcs; no primes and no zero free input. -/
theorem leaf_oht_model_tail (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if ((X ^ 2 : ℕ) : ℤ) < n then
        ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2 else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- The coefficient of the difference is the difference of the coefficients. -/
private lemma oht_coeff_sub (X : ℕ) (hX : 0 < X) (n : ℤ) :
    fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n =
      fourierCoeff (fun t => FX X (X ^ 2) t ^ 2) n -
        fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  set W : AddCircle (1 : ℝ) → ℂ := Vfun X (Nat.sqrt X) (Nat.sqrt X) with hWdef
  have hW : MemLp W 2 haarAddCircle := memLp_Vfun hX0 _ _
  have hFX : MemLp (fun t => FX (X : ℝ) (X ^ 2) t ^ 2) 2 haarAddCircle :=
    memLp_FX_sq (X : ℝ) (X ^ 2)
  have hneg : fourierCoeff (-W) = -fourierCoeff W := by
    ext m
    have h := fourierCoeff.const_smul (T := (1 : ℝ)) W (-1) m
    simpa [neg_smul, one_smul] using h
  have hadd := fourierCoeff.add (T := (1 : ℝ))
    (f := fun t => FX X (X ^ 2) t ^ 2) (g := -W)
    (hFX.integrable one_le_two) (hW.integrable one_le_two).neg
  have heq : (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) =
      (fun t => FX X (X ^ 2) t ^ 2) + (-W) := by
    ext t
    simp [hWdef, sub_eq_add_neg]
  rw [heq, hadd, hneg, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]

/-- Pointwise: `|a - b|² ≤ 2 |a|² + 2 |b|²`. -/
private lemma oht_pointwise (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have htri := norm_sub_le a b
  have h0 : 0 ≤ ‖a - b‖ := norm_nonneg _
  have hab : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ h0 htri 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- A family dominated by a summable family supported on `n > X ^ 2`: summability of each tail
from the summable full energies. -/
private lemma summable_oht (X : ℕ) (f : ℤ → ℝ) (hf : Summable f) :
    Summable (fun n : ℤ => if ((X ^ 2 : ℕ) : ℤ) < n then f n else 0) := by
  classical
  have : (fun n : ℤ => if ((X ^ 2 : ℕ) : ℤ) < n then f n else 0) =
      Set.indicator {n : ℤ | ((X ^ 2 : ℕ) : ℤ) < n} f := by
    funext n; simp [Set.indicator]
  rw [this]
  exact hf.indicator _

/-- `leaf_ofw_high_tail` from the two tail leaves. -/
theorem leaf_ofw_high_tail_of_leaves (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if ((X ^ 2 : ℕ) : ℤ) < n then
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  classical
  obtain ⟨C1, hC1, X1, h1⟩ := leaf_oht_FX_sq_tail Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C2, hC2, X2, h2⟩ := leaf_oht_model_tail Θ hΘ1 hΘ2 hZF ε hε hsublinear
  refine ⟨2 * C1 + 2 * C2, by positivity, max (max X1 X2) 1, ?_⟩
  intro X hX
  have hXpos : 0 < X := by omega
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hGs : Summable (fun n : ℤ => ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2) n‖ ^ 2) := by
    have hG : MemLp (fun t => FX X (X ^ 2) t ^ 2) 2 haarAddCircle :=
      memLp_FX_sq (X : ℝ) (X ^ 2)
    have hh := hasSum_sq_fourierCoeff (hG.toLp (fun t => FX X (X ^ 2) t ^ 2))
    rw [fourierCoeff_congr_ae (MemLp.coeFn_toLp hG)] at hh
    exact hh.summable
  have hWs : Summable (fun n : ℤ =>
      ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2) := by
    have hW : MemLp (Vfun X (Nat.sqrt X) (Nat.sqrt X)) 2 haarAddCircle := memLp_Vfun hX0 _ _
    have hh := hasSum_sq_fourierCoeff (hW.toLp (Vfun X (Nat.sqrt X) (Nat.sqrt X)))
    rw [fourierCoeff_congr_ae (MemLp.coeFn_toLp hW)] at hh
    exact hh.summable
  set A : ℤ → ℝ := fun n => if ((X ^ 2 : ℕ) : ℤ) < n then
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2) n‖ ^ 2 else 0 with hA
  set B : ℤ → ℝ := fun n => if ((X ^ 2 : ℕ) : ℤ) < n then
        ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2 else 0 with hB
  have hAs : Summable A := summable_oht X _ hGs
  have hBs : Summable B := summable_oht X _ hWs
  have hle : ∀ n : ℤ, (if ((X ^ 2 : ℕ) : ℤ) < n then
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
        else 0) ≤ 2 * A n + 2 * B n := by
    intro n
    by_cases hn : ((X ^ 2 : ℕ) : ℤ) < n
    · simp only [hA, hB]
      rw [if_pos hn, if_pos hn, if_pos hn, oht_coeff_sub X hXpos n]
      exact oht_pointwise _ _
    · simp only [hA, hB]
      rw [if_neg hn, if_neg hn, if_neg hn]
      norm_num
  have hLs : Summable (fun n : ℤ => if ((X ^ 2 : ℕ) : ℤ) < n then
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
        else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hle
      ((hAs.mul_left 2).add (hBs.mul_left 2))
  have hsum := Summable.tsum_le_tsum hle hLs ((hAs.mul_left 2).add (hBs.mul_left 2))
  rw [Summable.tsum_add (hAs.mul_left 2) (hBs.mul_left 2), tsum_mul_left, tsum_mul_left] at hsum
  have hA' := h1 X (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX)
  have hB' := h2 X (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX)
  calc _ ≤ 2 * (∑' n, A n) + 2 * (∑' n, B n) := hsum
    _ ≤ 2 * (C1 * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε)) + 2 * (C2 * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε)) := by
        gcongr
    _ = (2 * C1 + 2 * C2) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by ring

end

end LeanLab.ExceptionalSet.BG2026.Decomp522a
