import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_arc_energy_offwindow

/-!
Split of `leaf_ofw_high_middle` in `SPLIT_feed1122_leaf_arc_energy_offwindow.lean`, P0029
Bhowmik and Grimmelt 2026 with the arc model of P0083 Pintz 2026.

On the damped middle frequencies `X < n ≤ X ^ 2` the coefficient `R_Λ(n) e^{-n/X} - v_X(n)` is
cut at the Hardy-Littlewood main term `M(n) = n 𝔖(n)` for even `n` and `M(n) = 0` for odd `n`:

  `R_Λ(n) e^{-n/X} - v_X(n) = e^{-n/X} (R_Λ(n) - M(n)) + (e^{-n/X} M(n) - v_X(n))`,

and `|a + b|² ≤ 2|a|² + 2|b|²` gives the two leaves

* `leaf_ohm_error_energy`, HARD: the damped mean square of the error `R_Λ(n) - M(n)`, the only
  place the zero free hypothesis enters; on even `n` this is the paper's `error n`;
* `leaf_ohm_model_energy`, HARD: the arc model reconstructs the damped main term, a statement
  with no primes in it.

The odd `n` are put on the error side because `Sing` is the even Euler product for all `n`, so
`n · Sing n` at odd `n` is of size `n` and its damped energy would be of order `X³`, more than
the target `X^(3/2 + 2Θ + ε)`.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.BG2026.Decomp522a

open Finset Real MeasureTheory AddCircle
open LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
open LeanLab.ExceptionalSet.PintzAlthofer2026Model
open LeanLab.ExceptionalSet.BG2026.Supply385

noncomputable section

/-- LEAF: the damped mean square of the Goldbach error on the middle frequencies, P0029 section 3,
the mean square of `error n` weighted by `e^{-2n/X}`: the sum over `X < n ≤ X ^ 2` of
`(e^{-n/X} (R_Λ(n) - M(n)))²`, with `M(n) = n 𝔖(n)` at even `n` and `0` at odd `n`, is
eventually at most `C · X^(3/2 + 2Θ + ε)`.  HARD: the zero free hypothesis `ZeroFreeBeyond Θ`
gives the even part of size `X^(1 + 2Θ + ε)` through the explicit formula; the odd part counts
representations with a power of `2` and is `X` up to logarithms. -/
theorem leaf_ohm_error_energy (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if (X : ℤ) < n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ) then
        (Real.exp (-(n.toNat : ℝ) / X) *
          (LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat -
            (if Even n.toNat then (n.toNat : ℝ) * Sing n.toNat else 0))) ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- LEAF: the arc model reconstructs the damped main term on the middle frequencies, P0083
display 4.14 for `v_X(n)` against `e^{-n/X} n 𝔖(n)`: the sum over `X < n ≤ X ^ 2` of
`|e^{-n/X} M(n) - v_X(n)|²`, with `M(n) = n 𝔖(n)` at even `n` and `0` at odd `n`, is eventually
at most `C · X^(3/2 + 2Θ + ε)`.  HARD: the tail `𝔖 - 𝔖_Q` of the singular series beyond
`Q = √X` in mean square, size `X^(5/2)` up to logarithms, the cancellation between `q` and `2q`
at odd `n`, and the arc truncation; no primes and no zero free input. -/
theorem leaf_ohm_model_energy (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if (X : ℤ) < n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ) then
        ‖((Real.exp (-(n.toNat : ℝ) / X) *
            (if Even n.toNat then (n.toNat : ℝ) * Sing n.toNat else 0) : ℝ) : ℂ) -
          fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- Pointwise: `|r e - v|² ≤ 2 (e (r - M))² + 2 |e M - v|²`. -/
private lemma ohm_pointwise (r e M : ℝ) (v : ℂ) :
    ‖((r * e : ℝ) : ℂ) - v‖ ^ 2 ≤
      2 * (e * (r - M)) ^ 2 + 2 * ‖((e * M : ℝ) : ℂ) - v‖ ^ 2 := by
  have hsplit : ((r * e : ℝ) : ℂ) - v = ((e * (r - M) : ℝ) : ℂ) + (((e * M : ℝ) : ℂ) - v) := by
    push_cast; ring
  have htri := norm_add_le ((e * (r - M) : ℝ) : ℂ) (((e * M : ℝ) : ℂ) - v)
  rw [← hsplit, Complex.norm_real, Real.norm_eq_abs] at htri
  have h0 : 0 ≤ ‖((r * e : ℝ) : ℂ) - v‖ := norm_nonneg _
  have h1 : 0 ≤ ‖((e * M : ℝ) : ℂ) - v‖ := norm_nonneg _
  have hab : ‖((r * e : ℝ) : ℂ) - v‖ ^ 2 ≤
      (|e * (r - M)| + ‖((e * M : ℝ) : ℂ) - v‖) ^ 2 := pow_le_pow_left₀ h0 htri 2
  have hsq : |e * (r - M)| ^ 2 = (e * (r - M)) ^ 2 := sq_abs _
  nlinarith [sq_nonneg (|e * (r - M)| - ‖((e * M : ℝ) : ℂ) - v‖)]

/-- A family supported on `X < n ≤ X ^ 2` is summable. -/
private lemma summable_ohm (X : ℕ) (f : ℤ → ℝ) :
    Summable (fun n : ℤ => if (X : ℤ) < n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ) then f n else 0) := by
  classical
  apply summable_of_ne_finset_zero (s := Finset.Ioc (X : ℤ) ((X ^ 2 : ℕ) : ℤ))
  intro n hn
  rw [Finset.mem_Ioc] at hn
  rw [if_neg hn]

/-- `leaf_ofw_high_middle` from the error leaf and the model leaf. -/
theorem leaf_ofw_high_middle_of_leaves (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if (X : ℤ) < n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ) then
        ‖((LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat *
            Real.exp (-(n.toNat : ℝ) / X) : ℝ) : ℂ) -
          fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  classical
  obtain ⟨C1, hC1, X1, h1⟩ := leaf_ohm_error_energy Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C2, hC2, X2, h2⟩ := leaf_ohm_model_energy Θ hΘ1 hΘ2 hZF ε hε hsublinear
  refine ⟨2 * C1 + 2 * C2, by positivity, max X1 X2, ?_⟩
  intro X hX
  set A : ℤ → ℝ := fun n => if (X : ℤ) < n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ) then
        (Real.exp (-(n.toNat : ℝ) / X) *
          (LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat -
            (if Even n.toNat then (n.toNat : ℝ) * Sing n.toNat else 0))) ^ 2
        else 0 with hA
  set B : ℤ → ℝ := fun n => if (X : ℤ) < n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ) then
        ‖((Real.exp (-(n.toNat : ℝ) / X) *
            (if Even n.toNat then (n.toNat : ℝ) * Sing n.toNat else 0) : ℝ) : ℂ) -
          fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2
        else 0 with hB
  have hAs : Summable A := summable_ohm X _
  have hBs : Summable B := summable_ohm X _
  have hle : ∀ n : ℤ, (if (X : ℤ) < n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ) then
        ‖((LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat *
            Real.exp (-(n.toNat : ℝ) / X) : ℝ) : ℂ) -
          fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2
        else 0) ≤ 2 * A n + 2 * B n := by
    intro n
    by_cases hn : (X : ℤ) < n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ)
    · simp only [hA, hB]
      rw [if_pos hn, if_pos hn, if_pos hn]
      exact ohm_pointwise _ _ _ _
    · simp only [hA, hB]
      rw [if_neg hn, if_neg hn, if_neg hn]
      norm_num
  have hsum := Summable.tsum_le_tsum hle (summable_ohm X _)
    ((hAs.mul_left 2).add (hBs.mul_left 2))
  rw [Summable.tsum_add (hAs.mul_left 2) (hBs.mul_left 2), tsum_mul_left, tsum_mul_left] at hsum
  have hA' := h1 X (le_trans (le_max_left _ _) hX)
  have hB' := h2 X (le_trans (le_max_right _ _) hX)
  calc _ ≤ 2 * (∑' n, A n) + 2 * (∑' n, B n) := hsum
    _ ≤ 2 * (C1 * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε)) + 2 * (C2 * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε)) := by
        gcongr
    _ = (2 * C1 + 2 * C2) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by ring

end

end LeanLab.ExceptionalSet.BG2026.Decomp522a
