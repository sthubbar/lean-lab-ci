import LeanLab.ExceptionalSet.SPLIT_leaf_arc_energy

/-!
Split, burst-20261122 p2 by CLOUD S149, of the leaf `leaf_ofw_short` of
`SPLIT_feed1122_leaf_arc_energy_offwindow.lean`, the odd frequencies `0 ≤ n ≤ X`, P0029
Bhowmik and Grimmelt 2026 with the arc model of P0083 Pintz 2026.  The same branch already splits
`leaf_ofw_high_tail` the same way in `SPLIT_feed1122_leaf_ofw_high_tail.lean`, CLOUD S132.

It is split by `‖a - b‖² ≤ 2‖a‖² + 2‖b‖²` into the energy of the prime side alone and the energy of
the arc model alone.  The split is faithful: at odd `n` the paper bounds the two sides
separately, there is no main term cancellation between `R_Λ(n) e^{-n/X}` and `v_X(n)` there.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.BG2026.Decomp522a

open Finset Real MeasureTheory AddCircle
open LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
open LeanLab.ExceptionalSet.PintzAlthofer2026Model
open LeanLab.ExceptionalSet.BG2026.Supply385

noncomputable section

/-- Pointwise `‖a - b‖² ≤ 2‖a‖² + 2‖b‖²`, summed over an index set. -/
theorem p2_tsum_ind_norm_sub_sq_le (P : ℤ → Prop) [DecidablePred P] (a b : ℤ → ℂ)
    (ha : Summable (fun n => if P n then ‖a n‖ ^ 2 else 0))
    (hb : Summable (fun n => if P n then ‖b n‖ ^ 2 else 0)) :
    (∑' n, if P n then ‖a n - b n‖ ^ 2 else 0) ≤
      2 * (∑' n, if P n then ‖a n‖ ^ 2 else 0) + 2 * (∑' n, if P n then ‖b n‖ ^ 2 else 0) := by
  have hpt : ∀ n, (if P n then ‖a n - b n‖ ^ 2 else 0) ≤
      2 * (if P n then ‖a n‖ ^ 2 else 0) + 2 * (if P n then ‖b n‖ ^ 2 else 0) := by
    intro n
    split_ifs
    · have h1 := norm_sub_le (a n) (b n)
      have h2 : 0 ≤ ‖a n - b n‖ := norm_nonneg _
      have h3 : 0 ≤ ‖a n‖ := norm_nonneg _
      have h4 : 0 ≤ ‖b n‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖a n‖ - ‖b n‖)]
    · simp
  have hs : Summable (fun n => 2 * (if P n then ‖a n‖ ^ 2 else 0) +
      2 * (if P n then ‖b n‖ ^ 2 else 0)) := (ha.mul_left 2).add (hb.mul_left 2)
  have hl : Summable (fun n => if P n then ‖a n - b n‖ ^ 2 else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hpt hs
  calc (∑' n, if P n then ‖a n - b n‖ ^ 2 else 0)
      ≤ ∑' n, (2 * (if P n then ‖a n‖ ^ 2 else 0) + 2 * (if P n then ‖b n‖ ^ 2 else 0)) :=
        hl.tsum_le_tsum hpt hs
    _ = _ := by rw [(ha.mul_left 2).tsum_add (hb.mul_left 2), tsum_mul_left, tsum_mul_left]

/-- Parseval summability of the squared coefficients of an `L²` function on the circle. -/
theorem p2_summable_coeff_sq {f : AddCircle (1 : ℝ) → ℂ} (hf : MemLp f 2 haarAddCircle) :
    Summable (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2) := by
  have hh := hasSum_sq_fourierCoeff (hf.toLp f)
  have hcoef : fourierCoeff ((hf.toLp f : Lp ℂ 2 haarAddCircle) : AddCircle (1 : ℝ) → ℂ) =
      fourierCoeff f := fourierCoeff_congr_ae (MemLp.coeFn_toLp hf)
  rw [hcoef] at hh
  exact hh.summable

theorem p2_summable_ind {P : ℤ → Prop} [DecidablePred P] {c : ℤ → ℝ} (hc : Summable c)
    (h0 : ∀ n, 0 ≤ c n) : Summable (fun n => if P n then c n else 0) :=
  Summable.of_nonneg_of_le (fun n => by split_ifs <;> simp [h0])
    (fun n => by split_ifs <;> simp [h0]) hc

/-- The coefficient of the difference is the difference of the coefficients. -/
theorem p2_coeff_diff (X : ℕ) (hX : 0 < X) (n : ℤ) :
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

/-- LEAF: P0029, the prime side at odd frequencies `0 ≤ n ≤ X`.  An odd `n` is a sum of two prime
powers only with a power of `2`, so `R_Λ(n) ≪ log³ n` and the energy of `R_Λ(n) e^{-n/X}` over
odd `n ≤ X` is `O(X log⁶ X)`.  EASY: a divisibility count, no zero free input. -/
theorem leaf_ofw_short_count (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
          n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
        ‖((LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat *
            Real.exp (-(n.toNat : ℝ) / X) : ℝ) : ℂ)‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- LEAF: P0083 Pintz 2026 (4.14), the arc model at odd frequencies `0 ≤ n ≤ X`.  At odd `n` the
terms `q` and `2q`, `q` odd, cancel in the truncated singular series since `c_{2q}(n) = -c_q(n)`
and `φ(2q) = φ(q)`; only odd `q` with `Q/2 < q ≤ Q`, `Q = √X`, survive, giving `|v_X(n)| ≪ X^{1/2+ε}`
up to the arc truncation error, and energy `O(X^{2+2ε})` over odd `n ≤ X`.  MEDIUM: Ramanujan sum
bookkeeping in `fourierCoeff_Vfun` plus a bound on the cut arc integrals, no zero free input. -/
theorem leaf_ofw_short_model (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
          n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
        ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- Reduction of `leaf_ofw_short` to `leaf_ofw_short_count` and `leaf_ofw_short_model`. -/
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
  obtain ⟨C1, hC1, X1, h1⟩ := leaf_ofw_short_count Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C2, hC2, X2, h2⟩ := leaf_ofw_short_model Θ hΘ1 hΘ2 hZF ε hε hsublinear
  refine ⟨2 * C1 + 2 * C2, by positivity, X1 + X2 + 1, ?_⟩
  intro X hX
  have hXpos : 0 < X := by omega
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hXpos
  set P : ℤ → Prop := fun n => 0 ≤ n ∧ n ≤ (X : ℤ) ∧
    n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) with hP
  have hA : Summable (fun n : ℤ => if P n then
      ‖((LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat *
          Real.exp (-(n.toNat : ℝ) / X) : ℝ) : ℂ)‖ ^ 2 else 0) := by
    apply summable_of_ne_finset_zero (s := Finset.Icc (0 : ℤ) X)
    intro n hn
    have : ¬ P n := by
      rintro ⟨h0, hle, _⟩
      exact hn (Finset.mem_Icc.mpr ⟨h0, hle⟩)
    simp [this]
  have hB := p2_summable_ind (P := P)
    (p2_summable_coeff_sq (memLp_Vfun hX0 (Nat.sqrt X : ℝ) (Nat.sqrt X)))
    (fun n => by positivity)
  have hle := p2_tsum_ind_norm_sub_sq_le P _ _ hA hB
  have e1 := h1 X (by omega)
  have e2 := h2 X (by omega)
  have hp : 0 ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by positivity
  nlinarith

end

end LeanLab.ExceptionalSet.BG2026.Decomp522a
