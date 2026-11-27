import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_arc_energy_offwindow

/-!
Split of `LeanLab.ExceptionalSet.BG2026.Decomp522a.leaf_ofw_high_middle`, the damped middle
frequencies `X < n ≤ X ^ 2` of the off window energy of P0029 Bhowmik and Grimmelt 2026 with the
arc model of P0083 Pintz 2026.

On this range the coefficient of the squared generating function is `R_Λ(n) e^{-n/X}`.  The parent
leaf names two ingredients, and the split separates them through the intermediate value
`𝔖(n) n e^{-n/X}`, with `𝔖(n)` the Hardy-Littlewood singular series `Sing n` for even `n` and `0`
for odd `n`, using `‖a - b‖² ≤ 2‖a - c‖² + 2‖c - b‖²`:

* `leaf_ofw_middle_error`: the mean square of the Hardy-Littlewood error `R_Λ(n) - 𝔖(n) n`,
  weighted by `e^{-2n/X}`, over `X < n ≤ X²`; this is where `ZeroFreeBeyond Θ` enters, the
  Hardy-Littlewood mean square `Σ_{n ≤ N} |R_Λ(n) - 𝔖(n) n|² ≪ N^{3/2 + 2Θ + ε}` summed against the
  damping.
* `leaf_ofw_middle_model`: the arc model's reconstruction of `𝔖(n) n e^{-n/X}`, the energy of
  `𝔖(n) n e^{-n/X} - v_X(n)` over the same range; no primes, no zero free input.

`leaf_ofw_high_middle_of_leaves` proves the statement of `leaf_ofw_high_middle` from them.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.BG2026.Decomp522a.OfwHighMiddle

open Finset Real MeasureTheory AddCircle
open LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
open LeanLab.ExceptionalSet.PintzAlthofer2026Model
open LeanLab.ExceptionalSet.BG2026.Supply385

noncomputable section

/-- LEAF: the weighted Hardy-Littlewood mean square on the damped middle range.  Under
`ZeroFreeBeyond Θ`, the error `R_Λ(n) - 𝔖(n) n` of the Hardy-Littlewood asymptotic, with
`𝔖(n) = Sing n` for even `n` and `0` for odd `n`, has mean square `≪ N^{3/2 + 2Θ + ε}` up to `N`;
summed against `e^{-2n/X}` over `X < n ≤ X²` it is `≪ X^{3/2 + 2Θ + ε}`.  This is the zero free
input of the parent leaf, the mean square of `error n` weighted by `e^{-2n/X}` over `n > X`.  HARD:
the explicit formula for `R_Λ` under a zero free region, the Hardy-Littlewood mean square. -/
theorem leaf_ofw_middle_error (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if (X : ℤ) < n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ) then
        ((LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat -
            (if Even n.toNat then Sing n.toNat else 0) * (n.toNat : ℝ)) *
          Real.exp (-(n.toNat : ℝ) / X)) ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- LEAF: the arc model reconstructs `𝔖(n) n e^{-n/X}` on the damped middle range.  The model
coefficient is `v_X(n) = Σ_{q ≤ √X} μ(q)² c_q(n)/φ(q)² ∫_{|β| ≤ √X/(qX)} e(-nβ)(X⁻¹ − 2πiβ)⁻² dβ`;
the full line integral is `n e^{-n/X}`, the cut tails are `O(min(q√X, q²X/n))`, and the singular
series truncated at `q ≤ √X` differs from `𝔖(n)` by a tail of mean square `≪ X^{-1/2 + ε}` on
average.  The energy of `𝔖(n) n e^{-n/X} - v_X(n)` over `X < n ≤ X²` is `≪ X^{5/2 + ε}`.  This is
the arc model's reconstruction the parent leaf names.  MEDIUM: Ramanujan sum mean squares and an
integration by parts on each arc, no primes and no zero free input. -/
theorem leaf_ofw_middle_model (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if (X : ℤ) < n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ) then
        ‖(((if Even n.toNat then Sing n.toNat else 0) * (n.toNat : ℝ) *
            Real.exp (-(n.toNat : ℝ) / X) : ℝ) : ℂ) -
          fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (5 / 2 + ε) := by
  sorry

/-- `‖a - b‖² ≤ 2‖a - c‖² + 2‖c - b‖²`, summed over the indices with `P n`. -/
private lemma tsum_sq_split (P : ℤ → Prop) [DecidablePred P] (a b c : ℤ → ℂ)
    (h1 : Summable (fun n => if P n then ‖a n - c n‖ ^ 2 else 0))
    (h2 : Summable (fun n => if P n then ‖c n - b n‖ ^ 2 else 0)) :
    (∑' n, if P n then ‖a n - b n‖ ^ 2 else 0) ≤
      2 * (∑' n, if P n then ‖a n - c n‖ ^ 2 else 0) +
        2 * (∑' n, if P n then ‖c n - b n‖ ^ 2 else 0) := by
  have hpt : ∀ n, (if P n then ‖a n - b n‖ ^ 2 else 0) ≤
      2 * (if P n then ‖a n - c n‖ ^ 2 else 0) + 2 * (if P n then ‖c n - b n‖ ^ 2 else 0) := by
    intro n
    split_ifs
    · have htri : ‖a n - b n‖ ≤ ‖a n - c n‖ + ‖c n - b n‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      have h0 : 0 ≤ ‖a n - b n‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖a n - c n‖ - ‖c n - b n‖), norm_nonneg (a n - c n),
        norm_nonneg (c n - b n)]
    · simp
  have hs : Summable (fun n => 2 * (if P n then ‖a n - c n‖ ^ 2 else 0) +
      2 * (if P n then ‖c n - b n‖ ^ 2 else 0)) := (h1.mul_left 2).add (h2.mul_left 2)
  have hl : Summable (fun n => if P n then ‖a n - b n‖ ^ 2 else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hpt hs
  calc _ ≤ ∑' n, (2 * (if P n then ‖a n - c n‖ ^ 2 else 0) +
        2 * (if P n then ‖c n - b n‖ ^ 2 else 0)) := hl.tsum_le_tsum hpt hs
    _ = _ := by rw [(h1.mul_left 2).tsum_add (h2.mul_left 2), tsum_mul_left, tsum_mul_left]

/-- A family supported on a finite set of integers is summable. -/
private lemma summable_of_support_Icc (f : ℤ → ℝ) (lo hi : ℤ)
    (hf : ∀ n, ¬ (lo ≤ n ∧ n ≤ hi) → f n = 0) : Summable f :=
  summable_of_ne_finset_zero (s := Finset.Icc lo hi) (fun n hn => hf n (by
    simpa [Finset.mem_Icc] using hn))

/-- Assembly: the statement of `leaf_ofw_high_middle` from the two middle leaves. -/
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
  obtain ⟨C1, hC1, X1, h1⟩ := leaf_ofw_middle_error Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C2, hC2, X2, h2⟩ := leaf_ofw_middle_model ε hε
  refine ⟨2 * C1 + 2 * C2, by positivity, X1 + X2 + 1, ?_⟩
  intro X hX
  have hXpos : 0 < X := by omega
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hXpos
  let P : ℤ → Prop := fun n => (X : ℤ) < n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ)
  let a : ℤ → ℂ := fun n => ((LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat *
      Real.exp (-(n.toNat : ℝ) / X) : ℝ) : ℂ)
  let b : ℤ → ℂ := fun n => fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n
  let c : ℤ → ℂ := fun n => (((if Even n.toNat then Sing n.toNat else 0) * (n.toNat : ℝ) *
      Real.exp (-(n.toNat : ℝ) / X) : ℝ) : ℂ)
  have hsupp : ∀ (g : ℤ → ℝ) (n : ℤ), ¬ ((X : ℤ) ≤ n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ)) →
      (if P n then g n else 0) = 0 := by
    intro g n hn
    exact if_neg (fun h => hn ⟨h.1.le, h.2⟩)
  have hs1 : Summable (fun n => if P n then ‖a n - c n‖ ^ 2 else 0) :=
    summable_of_support_Icc _ _ _ (hsupp _)
  have hs2 : Summable (fun n => if P n then ‖c n - b n‖ ^ 2 else 0) :=
    summable_of_support_Icc _ _ _ (hsupp _)
  have hmain := tsum_sq_split P a b c hs1 hs2
  have hac : (∑' n, if P n then ‖a n - c n‖ ^ 2 else 0) =
      ∑' n : ℤ, if (X : ℤ) < n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ) then
        ((LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat -
            (if Even n.toNat then Sing n.toNat else 0) * (n.toNat : ℝ)) *
          Real.exp (-(n.toNat : ℝ) / X)) ^ 2
        else 0 := by
    refine tsum_congr fun n => ?_
    by_cases hn : P n
    · rw [if_pos hn, if_pos hn]
      simp only [a, c]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring
    · rw [if_neg hn, if_neg hn]
  have e1 := h1 X (by omega)
  have e2 := h2 X (by omega)
  rw [← hac] at e1
  have hpow : (X : ℝ) ^ (5 / 2 + ε) ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hpos : 0 ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by positivity
  calc _ ≤ 2 * (∑' n, if P n then ‖a n - c n‖ ^ 2 else 0) +
        2 * (∑' n, if P n then ‖c n - b n‖ ^ 2 else 0) := hmain
    _ ≤ 2 * (C1 * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε)) + 2 * (C2 * (X : ℝ) ^ (5 / 2 + ε)) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 (by norm_num))
          (mul_le_mul_of_nonneg_left e2 (by norm_num))
    _ ≤ (2 * C1 + 2 * C2) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
        nlinarith [mul_le_mul_of_nonneg_left hpow hC2]

end

end LeanLab.ExceptionalSet.BG2026.Decomp522a.OfwHighMiddle
