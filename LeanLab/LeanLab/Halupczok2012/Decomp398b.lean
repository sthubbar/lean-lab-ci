import LeanLab.Halupczok2012.Decomp398a

/-!
Supply decomposition for the fixed residue part of Halupczok Theorem 7.
Source: journal pages 336 to 337, Lemma 2.1 and display 2.2,
and page 343, display 4.1.
The prime free overlap moment is separate from the Perelli Pintz arc estimates.
https://doi.org/10.5802/jtnb.839
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp398b

open Finset
open scoped Classical

/-- LEAF. Halupczok page 337, display 2.2 and its Voronoi estimate.
Sum the overlap counts before Cauchy Schwarz.
The window is doubled because the progression condition concerns 2k.
The bound X at most K Y squared lets log Y replace log X.
This arithmetic statement has no prime weights or singular series. -/
theorem fixed_residue_moment (c K : ℝ) (hc : 0 < c) (hK : 0 < K) (a : ℤ) :
    ∃ C Y0 : ℝ, 0 < C ∧ ∀ X R Y Q : ℝ,
      Y0 ≤ Y → 1 ≤ R → R ≤ Y → Y ≤ X → X ≤ K * Y ^ 2 → (a : ℝ) ≤ X →
      1 ≤ Q → Q ≤ c * R ^ (3 / 2 : ℝ) * X ^ (-(1 / 2) : ℝ) →
      ∑ k ∈ kRange X R,
        (((Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => ((2 * k : ℕ) : ℤ) ≡ a [ZMOD q])).card : ℝ) ^ 2 ≤
        C * R * Real.log Y ^ 3 := by
  sorry

/-- Display 4.1 on page 343, conditional on Theorem5 and the prime free moment leaf. -/
theorem theorem7_of_theorem5 (h5 : Theorem5) : Theorem7 := by
  intro A ε1 ε2 hA hε1 hε2 c1 c2 c3 c4 c5 hc1 hc2 hc3 hc4 hc5 a ha
  let K := (1 / c1) ^ 2 + c5 + 2
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨CM, YM, hCM, hM⟩ := fixed_residue_moment c3 K hc3 hK (a : ℤ)
  obtain ⟨C5, Y5, h5b⟩ := h5 (2 * A + 3) ε2 ε1 (by linarith) hε2 hε1
    c1 c2 1 c4 c5 hc1 hc2 (by norm_num) hc4 hc5
  let D := max C5 0 * CM
  have hD : 0 ≤ D := mul_nonneg (le_max_right _ _) hCM.le
  refine ⟨Real.sqrt D, max (Real.exp 1) (max YM Y5), ?_⟩
  intro X1 X2 Y R Q hR0 hYX2 hlow hRlow hRY hQ1 hQ hgap0 hgaplo hgaphi haX
  have hRe : Real.exp 1 ≤ R := (le_max_left _ _).trans hR0
  have hR1 : 1 ≤ R := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hRe
  have hRpos : 0 < R := by linarith
  have hYe : Real.exp 1 ≤ Y := hRe.trans hRY
  have hY1 : 1 ≤ Y := hR1.trans hRY
  have hL : 0 < Real.log Y := by
    have h := Real.log_le_log (Real.exp_pos 1) hYe
    rw [Real.log_exp] at h
    linarith
  have hYX1 : Y ≤ X1 := by linarith
  have hX2sq : X2 ≤ (Y / c1) ^ 2 := le_sq_of_rpow hc1 (hY1.trans hYX2) (by linarith) hlow
  have hX1sq : X1 ≤ K * Y ^ 2 := by
    have hYY : Y ≤ Y ^ 2 := by nlinarith
    have hsq : (Y / c1) ^ 2 = (1 / c1) ^ 2 * Y ^ 2 := by ring
    dsimp [K]
    rw [hsq] at hX2sq
    have hcy : c5 * Y ≤ c5 * Y ^ 2 := mul_le_mul_of_nonneg_left hYY hc5.le
    nlinarith [sq_nonneg (Y / c1)]
  have hMom : (∑ k ∈ kRange X1 R,
      (((Icc 1 ⌊Q⌋₊).filter (fun q => 2 * k ≡ a [MOD q])).card : ℝ) ^ 2) ≤
      CM * R * Real.log Y ^ 3 := by
    simpa only [Int.natCast_modEq_iff, Int.cast_natCast] using hM X1 R Y Q
      ((le_max_left _ _).trans ((le_max_right _ _).trans (hR0.trans hRY)))
      hR1 hRY hYX1 hX1sq (by exact_mod_cast haX) hQ1 hQ
  have hE := h5b X1 X2 Y R
    ((le_max_right _ _).trans ((le_max_right _ _).trans (hR0.trans hRY)))
    hlow hYX2 hRlow (by simpa using hRY) (hRY.trans hYX1) hgap0 hgaplo hgaphi
  have hE' : (∑ k ∈ kRange X1 R, (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2) ≤
      max C5 0 * R * Y ^ 2 * Real.log Y ^ (-(2 * A + 3)) := by
    refine hE.trans ?_
    gcongr
    exact le_max_left _ _
  have hCS := Progression398.even_cauchy (kRange X1 R)
    (fun k => binSum X2 Y (2 * k) - S (2 * k) * Y) ⌊Q⌋₊ (fun _ => a)
  change (∑ q ∈ Icc 1 ⌊Q⌋₊, |thm7Inner X1 X2 Y R q a|) ^ 2 ≤ _ at hCS
  have hM0 : 0 ≤ ∑ k ∈ kRange X1 R,
      (((Icc 1 ⌊Q⌋₊).filter (fun q => 2 * k ≡ a [MOD q])).card : ℝ) ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hb := hCS.trans (mul_le_mul hE' hMom hM0 (by positivity))
  have heq : (max C5 0 * R * Y ^ 2 * Real.log Y ^ (-(2 * A + 3))) *
      (CM * R * Real.log Y ^ 3) = (Real.sqrt D * R * Y * Real.log Y ^ (-A)) ^ 2 := by
    calc
      _ = D * R ^ 2 * Y ^ 2 * (Real.log Y ^ 3 * Real.log Y ^ (-(2 * A + 3))) := by
        dsimp [D]
        ring
      _ = _ := by
        rw [Max398.log_cancel hL]
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hD]
  rw [heq] at hb
  have hrhs : 0 ≤ Real.sqrt D * R * Y * Real.log Y ^ (-A) := by positivity
  nlinarith [sq_nonneg ((∑ q ∈ Icc 1 ⌊Q⌋₊, |thm7Inner X1 X2 Y R q a|) +
    Real.sqrt D * R * Y * Real.log Y ^ (-A))]

/-- Exact statement of the sealed theorem_7, from the overlap leaf and the two arc leaves. -/
theorem theorem7 : Theorem7 :=
  theorem7_of_theorem5 (theorem5_of_PP Decomp398a.pp1993_goldbach)

end LeanLab.Halupczok2012.Decomp398b
