import LeanLab.Halupczok2012.Progression398
import LeanLab.Halupczok2012.U1496PP

/-!
Halupczok journal page 343, the maximum supplement of Theorem 4.1.
The progression estimate is elementary.
The binary mean square remains conditional on Theorem5.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Max398

open Finset
open scoped Classical

/-- The logarithmic cancellation in display 4.1 on page 343.
The mean square is used with exponent 2A + 3. -/
theorem log_cancel {L A : ℝ} (hL : 0 < L) :
    L ^ 3 * L ^ (-(2 * A + 3)) = (L ^ (-A)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hL,
    ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  congr 1
  norm_num
  ring

/-- Lemma 2.2 on page 338 in the range Q at most c times the square root of R.
The logarithm in the full range bound is absorbed into log Y. -/
theorem progression_factor {c R Y Q : ℝ} (hc : 0 < c)
    (hY : Real.exp 1 ≤ Y) (hR : 0 ≤ R) (hRY : R ≤ Y)
    (hQ1 : 1 ≤ Q) (hQ : Q ≤ c * R ^ (1 / 2 : ℝ)) :
    2 * R * (1 + Real.log (⌊Q⌋₊ : ℝ)) ^ 3 + (⌊Q⌋₊ : ℝ) ^ 2 ≤
      R * (2 * (|Real.log (c ^ 2)| + 2) ^ 3 + c ^ 2) * Real.log Y ^ 3 := by
  have hYpos : 0 < Y := (Real.exp_pos 1).trans_le hY
  have hL1 : 1 ≤ Real.log Y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hY
  have hNQ : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hN1 : (1 : ℝ) ≤ (⌊Q⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ Q by simpa using hQ1)
  have hN0 : (0 : ℝ) ≤ (⌊Q⌋₊ : ℝ) := Nat.cast_nonneg _
  have hNsq : (⌊Q⌋₊ : ℝ) ^ 2 ≤ c ^ 2 * R := by
    have h0 : 0 ≤ c * R ^ (1 / 2 : ℝ) := by positivity
    have h := pow_le_pow_left₀ hN0 (hNQ.trans hQ) 2
    have hs : (R ^ (1 / 2 : ℝ)) ^ 2 = R := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hR]
      norm_num
    rwa [mul_pow, hs] at h
  have hNb : (⌊Q⌋₊ : ℝ) ≤ c ^ 2 * Y := by
    have hNN : (⌊Q⌋₊ : ℝ) ≤ (⌊Q⌋₊ : ℝ) ^ 2 := by nlinarith
    exact hNN.trans (hNsq.trans (mul_le_mul_of_nonneg_left hRY (sq_nonneg _)))
  have hlog : 1 + Real.log (⌊Q⌋₊ : ℝ) ≤ (|Real.log (c ^ 2)| + 2) * Real.log Y := by
    have h := Real.log_le_log (by linarith) hNb
    rw [Real.log_mul (by positivity) hYpos.ne'] at h
    have ha := le_abs_self (Real.log (c ^ 2))
    have hb : |Real.log (c ^ 2)| ≤ |Real.log (c ^ 2)| * Real.log Y :=
      le_mul_of_one_le_right (abs_nonneg _) hL1
    nlinarith
  have hH := one_add_log_nonneg ⌊Q⌋₊
  have hp := pow_le_pow_left₀ hH hlog 3
  have hL3 : 1 ≤ Real.log Y ^ 3 := one_le_pow₀ hL1
  have hn : c ^ 2 * R ≤ c ^ 2 * R * Real.log Y ^ 3 :=
    le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) hR) hL3
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * R)
  rw [mul_pow] at hm
  nlinarith

/-- The maximum supplement on page 343 follows from Theorem 2.3 on page 339.
This is conditional on the binary mean square only. -/
theorem theorem7Max_of_theorem5 (h5 : Theorem5) : Theorem7Max := by
  intro A ε1 ε2 hA hε1 hε2 c1 c2 c3 c4 c5 hc1 hc2 hc3 hc4 hc5
  obtain ⟨C5, Y05, h5b⟩ := h5 (2 * A + 3) ε2 ε1 (by linarith) hε2 hε1
    c1 c2 1 c4 c5 hc1 hc2 (by norm_num) hc4 hc5
  let D := 2 * (|Real.log (c3 ^ 2)| + 2) ^ 3 + c3 ^ 2
  let K := max C5 0 * D
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hK : 0 ≤ K := mul_nonneg (le_max_right _ _) hD
  refine ⟨Real.sqrt K, max Y05 (Real.exp 1), ?_⟩
  intro X1 X2 Y R Q hR0 hYX2 hlow hRlow hRY hQ1 hQ hgap0 hgaplo hgaphi a
  have hRe : Real.exp 1 ≤ R := (le_max_right _ _).trans hR0
  have hRpos : 0 < R := (Real.exp_pos 1).trans_le hRe
  have hYe : Real.exp 1 ≤ Y := hRe.trans hRY
  have hYpos : 0 < Y := hRpos.trans_le hRY
  have hL : 0 < Real.log Y := by
    have h := Real.log_le_log (Real.exp_pos 1) hYe
    rw [Real.log_exp] at h
    linarith
  have hYX1 : Y ≤ X1 := by linarith
  have hE := h5b X1 X2 Y R ((le_max_left _ _).trans (hR0.trans hRY))
    hlow hYX2 hRlow (by simpa using hRY) (hRY.trans hYX1) hgap0 hgaplo hgaphi
  have hE' : (∑ k ∈ kRange X1 R, (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2) ≤
      max C5 0 * R * Y ^ 2 * Real.log Y ^ (-(2 * A + 3)) := by
    refine hE.trans ?_
    gcongr
    exact le_max_left _ _
  have hP := progression_factor hc3 hYe hRpos.le hRY hQ1 hQ
  have hCS := Progression398.even_large_sieve X1 R hRpos.le
    (fun k => binSum X2 Y (2 * k) - S (2 * k) * Y) ⌊Q⌋₊ a
  change (∑ q ∈ Icc 1 ⌊Q⌋₊, |thm7Inner X1 X2 Y R q (a q)|) ^ 2 ≤ _ at hCS
  have hE0 : 0 ≤ ∑ k ∈ kRange X1 R, (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hF0 : 0 ≤ 2 * R * (1 + Real.log (⌊Q⌋₊ : ℝ)) ^ 3 + (⌊Q⌋₊ : ℝ) ^ 2 := by
    have := one_add_log_nonneg ⌊Q⌋₊
    positivity
  have hb := hCS.trans (mul_le_mul hE' hP hF0 (by positivity))
  have heq : (max C5 0 * R * Y ^ 2 * Real.log Y ^ (-(2 * A + 3))) *
      (R * D * Real.log Y ^ 3) = (Real.sqrt K * R * Y * Real.log Y ^ (-A)) ^ 2 := by
    calc
      _ = K * R ^ 2 * Y ^ 2 * (Real.log Y ^ 3 * Real.log Y ^ (-(2 * A + 3))) := by
        dsimp [K]
        ring
      _ = _ := by rw [log_cancel hL]; rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hK]
  change _ ≤ (max C5 0 * R * Y ^ 2 * Real.log Y ^ (-(2 * A + 3))) *
    (R * D * Real.log Y ^ 3) at hb
  rw [heq] at hb
  have hrhs : 0 ≤ Real.sqrt K * R * Y * Real.log Y ^ (-A) := by positivity
  nlinarith [sq_nonneg ((∑ q ∈ Icc 1 ⌊Q⌋₊, |thm7Inner X1 X2 Y R q (a q)|) +
    Real.sqrt K * R * Y * Real.log Y ^ (-A))]

/-- Perelli Pintz pages 44 to 46 supply the sole analytic input of the maximum supplement. -/
theorem theorem7Max_of_PP1993 (hPP : PP1993Goldbach) : Theorem7Max :=
  theorem7Max_of_theorem5 (theorem5_of_PP hPP)

end LeanLab.Halupczok2012.Max398
