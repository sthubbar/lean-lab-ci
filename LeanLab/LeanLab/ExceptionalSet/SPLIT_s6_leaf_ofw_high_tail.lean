import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_arc_energy_offwindow

/-!
Split of `LeanLab.ExceptionalSet.BG2026.Decomp522a.leaf_ofw_high_tail`, the frequencies beyond the
truncation point `X ^ 2` of `F_X` in the off window energy of P0029 Bhowmik and Grimmelt 2026 with
the arc model of P0083 Pintz 2026.

At a frequency `n > X ^ 2` the coefficient of `F_{X,X²}² - V_X` is the coefficient of `F_{X,X²}²`
minus the model coefficient `v_X(n)`, and `‖a - b‖² ≤ 2‖a‖² + 2‖b‖²`.  The two pieces are the two
ingredients the leaf names:

* `leaf_ofw_tail_FX`: the partial convolution `Σ_{u+v=n, u,v ≤ X²} Λ(u)Λ(v) e^{-n/X}` at
  `n > X²`, damped by `e^{-X}`, has energy `O(X^{5/2})`; no zero free input.
* `leaf_ofw_tail_model`: the model coefficient `v_X(n)` at `n > X²`, whose arc truncation part
  decays like `q² X / n`, has energy `O(X^{5/2})`; no primes, no zero free input.

`leaf_ofw_high_tail_of_leaves` proves the statement of `leaf_ofw_high_tail` from them, since
`X^{5/2} ≤ X^{3/2 + 2Θ + ε}` for `X ≥ 1`, `Θ ≥ 1/2`, `ε > 0`.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.BG2026.Decomp522a.OfwHighTail

open Finset Real MeasureTheory AddCircle
open LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
open LeanLab.ExceptionalSet.PintzAlthofer2026Model
open LeanLab.ExceptionalSet.BG2026.Supply385

noncomputable section

/-- LEAF: the squared generating function beyond its truncation point.  For `n > X ^ 2` the
coefficient of `F_{X,X²}²` is the partial convolution `Σ_{u+v=n, u,v ≤ X²} Λ(u)Λ(v) e^{-n/X}`,
zero for `n > 2X²` and at most `n log² n · e^{-X}` otherwise, so its energy over `n > X²` is
`O(X^6 log⁴ X e^{-2X})`, far below `X^{5/2}`.  This is the damped tail the parent leaf names as a
trivial bound.  EASY: a bound on a finite convolution with exponential damping, no zero free input. -/
theorem leaf_ofw_tail_FX :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if ((X ^ 2 : ℕ) : ℤ) < n then
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2) n‖ ^ 2 else 0)
        ≤ C * (X : ℝ) ^ (5 / 2 : ℝ) := by
  sorry

/-- LEAF: the arc model beyond the truncation point of `F_X`.  For `n > X ^ 2` the model
coefficient is `v_X(n) = Σ_{q ≤ √X} μ(q)² c_q(n)/φ(q)² ∫_{|β| ≤ √X/(qX)} e(-nβ)(X⁻¹ − 2πiβ)⁻² dβ`;
the full line integral is `n e^{-n/X}`, negligible, and the cut tails are `O(q² X / n)` by one
integration by parts, so the energy over `n > X²` is `O(X²)`, below `X^{5/2}`.  This is the
`L²` tail of the cut arcs the parent leaf names.  MEDIUM: an integration by parts on each arc and a
crude sum over `q`, no primes and no zero free input. -/
theorem leaf_ofw_tail_model :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if ((X ^ 2 : ℕ) : ℤ) < n then
        ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2 else 0)
        ≤ C * (X : ℝ) ^ (5 / 2 : ℝ) := by
  sorry

/-- The coefficient of the difference is the difference of the coefficients. -/
private lemma coeff_diff (X : ℕ) (hX : 0 < X) (n : ℤ) :
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
  rw [heq, hadd, hneg, Pi.add_apply, Pi.neg_apply, ← sub_eq_add_neg]

/-- Squared coefficients of an `L²` function on the circle are summable. -/
private lemma summable_coeff_sq (f : AddCircle (1 : ℝ) → ℂ) (hf : MemLp f 2 haarAddCircle) :
    Summable (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2) := by
  have hh := hasSum_sq_fourierCoeff (hf.toLp f)
  have hcoef : fourierCoeff ((hf.toLp f : Lp ℂ 2 haarAddCircle) : AddCircle (1 : ℝ) → ℂ) =
      fourierCoeff f := fourierCoeff_congr_ae (MemLp.coeFn_toLp hf)
  rw [hcoef] at hh
  exact hh.summable

/-- Assembly: the statement of `leaf_ofw_high_tail` from the two tail leaves. -/
theorem leaf_ofw_high_tail_of_leaves (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if ((X ^ 2 : ℕ) : ℤ) < n then
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  classical
  obtain ⟨C1, hC1, X1, h1⟩ := leaf_ofw_tail_FX
  obtain ⟨C2, hC2, X2, h2⟩ := leaf_ofw_tail_model
  refine ⟨2 * C1 + 2 * C2, by positivity, X1 + X2 + 1, ?_⟩
  intro X hX
  have hXpos : 0 < X := by omega
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hXpos
  set a : ℤ → ℂ := fun n => fourierCoeff (fun t => FX X (X ^ 2) t ^ 2) n with ha
  set b : ℤ → ℂ := fun n => fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n with hb
  have hsa : Summable (fun n : ℤ => if ((X ^ 2 : ℕ) : ℤ) < n then ‖a n‖ ^ 2 else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> first | exact le_rfl | positivity)
      (summable_coeff_sq _ (memLp_FX_sq (X : ℝ) (X ^ 2)))
  have hsb : Summable (fun n : ℤ => if ((X ^ 2 : ℕ) : ℤ) < n then ‖b n‖ ^ 2 else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> first | exact le_rfl | positivity)
      (summable_coeff_sq _ (memLp_Vfun (by exact_mod_cast hXpos) _ _))
  have hpt : ∀ n : ℤ, (if ((X ^ 2 : ℕ) : ℤ) < n then
      ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
      else 0) ≤
      2 * (if ((X ^ 2 : ℕ) : ℤ) < n then ‖a n‖ ^ 2 else 0) +
        2 * (if ((X ^ 2 : ℕ) : ℤ) < n then ‖b n‖ ^ 2 else 0) := by
    intro n
    split_ifs
    · rw [coeff_diff X hXpos n]
      have htri : ‖a n - b n‖ ≤ ‖a n‖ + ‖b n‖ := norm_sub_le _ _
      have h0 : 0 ≤ ‖a n - b n‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖a n‖ - ‖b n‖), norm_nonneg (a n), norm_nonneg (b n)]
    · simp
  have hs : Summable (fun n : ℤ => 2 * (if ((X ^ 2 : ℕ) : ℤ) < n then ‖a n‖ ^ 2 else 0) +
      2 * (if ((X ^ 2 : ℕ) : ℤ) < n then ‖b n‖ ^ 2 else 0)) :=
    (hsa.mul_left 2).add (hsb.mul_left 2)
  have hl := Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hpt hs
  have hpow : (X : ℝ) ^ (5 / 2 : ℝ) ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have e1 := h1 X (by omega)
  have e2 := h2 X (by omega)
  calc _ ≤ ∑' n : ℤ, (2 * (if ((X ^ 2 : ℕ) : ℤ) < n then ‖a n‖ ^ 2 else 0) +
        2 * (if ((X ^ 2 : ℕ) : ℤ) < n then ‖b n‖ ^ 2 else 0)) :=
        hl.tsum_le_tsum hpt hs
    _ = 2 * (∑' n : ℤ, if ((X ^ 2 : ℕ) : ℤ) < n then ‖a n‖ ^ 2 else 0) +
        2 * (∑' n : ℤ, if ((X ^ 2 : ℕ) : ℤ) < n then ‖b n‖ ^ 2 else 0) := by
        rw [(hsa.mul_left 2).tsum_add (hsb.mul_left 2), tsum_mul_left, tsum_mul_left]
    _ ≤ 2 * (C1 * (X : ℝ) ^ (5 / 2 : ℝ)) + 2 * (C2 * (X : ℝ) ^ (5 / 2 : ℝ)) := by
        gcongr
    _ ≤ (2 * C1 + 2 * C2) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
        have : 0 ≤ 2 * C1 + 2 * C2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hpow this]

end

end LeanLab.ExceptionalSet.BG2026.Decomp522a.OfwHighTail
