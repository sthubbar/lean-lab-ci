import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_arc_energy_offwindow

/-!
Split of `LeanLab.ExceptionalSet.BG2026.Decomp522a.leaf_ofw_short`, the odd frequencies
`0 ≤ n ≤ X` outside the even window, in the off window energy of P0029 Bhowmik and Grimmelt 2026
with the arc model of P0083 Pintz 2026.

The parent leaf names two ingredients, and `‖a - b‖² ≤ 2‖a‖² + 2‖b‖²` separates them:

* `leaf_ofw_short_primes`: a count of `R_Λ(n)` at odd `n`.  One of the two summands of an odd `n`
  is even, so a power of `2`, and `R_Λ(n) ≤ 2 log 2 · log n · log₂ n`; the energy of
  `R_Λ(n) e^{-n/X}` over odd `n ≤ X` is `O(X log⁴ X)`, below `X²`.
* `leaf_ofw_short_model`: Ramanujan sum bookkeeping at odd `n`.  The model coefficient `v_X(n)`
  at odd `n` nearly cancels between `q` and `2q`, since `c_{2q}(n) = -c_q(n)` and
  `φ(2q) = φ(q)` for odd `q` and odd `n`; only the pairs `q ≤ √X < 2q` and the difference of the
  arc widths survive, of energy `≪ X^{5/2 + ε}`.

`leaf_ofw_short_of_leaves` proves the statement of `leaf_ofw_short` from them.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.BG2026.Decomp522a.OfwShort

open Finset Real MeasureTheory AddCircle
open LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
open LeanLab.ExceptionalSet.PintzAlthofer2026Model
open LeanLab.ExceptionalSet.BG2026.Supply385

noncomputable section

/-- LEAF: a count of `R_Λ(n)` at odd `n`.  For odd `n` one of `u`, `n - u` is even, so a power of
`2` when `Λ` is nonzero there, and `R_Λ(n) ≤ 2 log 2 · log n · (log₂ n + 1)`; hence the energy of
`R_Λ(n) e^{-n/X}` over the odd `0 ≤ n ≤ X`, the integers of `[0, X]` outside the even window, is
`O(X log⁴ X)`, at most `C X²`.  This is the count of `R_Λ(n)` at odd `n` the parent leaf names.
EASY: elementary, no zero free input. -/
theorem leaf_ofw_short_primes :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
          n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
        (LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat *
            Real.exp (-(n.toNat : ℝ) / X)) ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (2 : ℝ) := by
  sorry

/-- LEAF: the arc model at odd frequencies.  For odd `n ≤ X` the model coefficient is
`v_X(n) = Σ_{q ≤ √X} μ(q)² c_q(n)/φ(q)² ∫_{|β| ≤ √X/(qX)} e(-nβ)(X⁻¹ − 2πiβ)⁻² dβ`; for odd `q` the
terms `q` and `2q` have `c_{2q}(n) = -c_q(n)` and `φ(2q) = φ(q)`, so they cancel up to the
difference of the cut integrals at widths `1/(q√X)` and `1/(2q√X)`, of size `O(q√X)`, and the
unpaired odd `q ∈ (√X/2, √X]` contribute `n e^{-n/X} Σ μ(q)² c_q(n)/φ(q)²`.  The energy over the
odd `0 ≤ n ≤ X` is `≪ X^{5/2 + ε}`.  This is the Ramanujan sum bookkeeping at odd `n` the parent
leaf names.  MEDIUM: Ramanujan sum mean squares over `n ≤ X` and the cut arc integrals. -/
theorem leaf_ofw_short_model (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
          n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
        ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2
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

/-- Assembly: the statement of `leaf_ofw_short` from the two short leaves. -/
theorem leaf_ofw_short_of_leaves (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
          n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
        ‖((LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat *
            Real.exp (-(n.toNat : ℝ) / X) : ℝ) : ℂ) -
          fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  classical
  obtain ⟨C1, hC1, X1, h1⟩ := leaf_ofw_short_primes
  obtain ⟨C2, hC2, X2, h2⟩ := leaf_ofw_short_model ε hε
  refine ⟨2 * C1 + 2 * C2, by positivity, X1 + X2 + 1, ?_⟩
  intro X hX
  have hXpos : 0 < X := by omega
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hXpos
  let P : ℤ → Prop := fun n => 0 ≤ n ∧ n ≤ (X : ℤ) ∧
    n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ))
  let a : ℤ → ℂ := fun n => ((LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat *
      Real.exp (-(n.toNat : ℝ) / X) : ℝ) : ℂ)
  let b : ℤ → ℂ := fun n => fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n
  let c : ℤ → ℂ := fun _ => 0
  have hsupp : ∀ (g : ℤ → ℝ) (n : ℤ), ¬ ((0 : ℤ) ≤ n ∧ n ≤ (X : ℤ)) →
      (if P n then g n else 0) = 0 := by
    intro g n hn
    exact if_neg (fun h => hn ⟨h.1, h.2.1⟩)
  have hs1 : Summable (fun n => if P n then ‖a n - c n‖ ^ 2 else 0) :=
    summable_of_support_Icc _ _ _ (hsupp _)
  have hs2 : Summable (fun n => if P n then ‖c n - b n‖ ^ 2 else 0) :=
    summable_of_support_Icc _ _ _ (hsupp _)
  have hmain := tsum_sq_split P a b c hs1 hs2
  have hac : (∑' n, if P n then ‖a n - c n‖ ^ 2 else 0) =
      ∑' n : ℤ, if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
          n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
        (LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat *
            Real.exp (-(n.toNat : ℝ) / X)) ^ 2
        else 0 := by
    refine tsum_congr fun n => ?_
    by_cases hn : P n
    · rw [if_pos hn, if_pos hn]
      simp only [a, c, sub_zero]
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    · rw [if_neg hn, if_neg hn]
  have hcb : (∑' n, if P n then ‖c n - b n‖ ^ 2 else 0) =
      ∑' n : ℤ, if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
          n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
        ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2
        else 0 := by
    refine tsum_congr fun n => ?_
    by_cases hn : P n
    · rw [if_pos hn, if_pos hn]
      simp only [b, c, zero_sub, norm_neg]
    · rw [if_neg hn, if_neg hn]
  have e1 := h1 X (by omega)
  have e2 := h2 X (by omega)
  rw [← hac] at e1
  rw [← hcb] at e2
  have hpow1 : (X : ℝ) ^ (2 : ℝ) ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hpow2 : (X : ℝ) ^ (5 / 2 + ε) ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  calc _ ≤ 2 * (∑' n, if P n then ‖a n - c n‖ ^ 2 else 0) +
        2 * (∑' n, if P n then ‖c n - b n‖ ^ 2 else 0) := hmain
    _ ≤ 2 * (C1 * (X : ℝ) ^ (2 : ℝ)) + 2 * (C2 * (X : ℝ) ^ (5 / 2 + ε)) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 (by norm_num))
          (mul_le_mul_of_nonneg_left e2 (by norm_num))
    _ ≤ (2 * C1 + 2 * C2) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
        nlinarith [mul_le_mul_of_nonneg_left hpow1 hC1, mul_le_mul_of_nonneg_left hpow2 hC2]

end

end LeanLab.ExceptionalSet.BG2026.Decomp522a.OfwShort
