/-
# Pintz and Althöfer 2026, (4.18) in the paper's form: |v(n)| ≥ x/(8e) on the window

Unit U-1148, T2 FRONTIER, idea I-0080, run 20261020T0103Z-16649.

`coef_lower`: there is X₀ such that for every natural x ≥ X₀ and every even n with
x/2 < n ≤ x, the major arc model coefficient with P = ⌊√x⌋ and weights w_q = μ(q)² c_q(n)/φ(q)²
satisfies ‖vTrunc x P P w n‖ ≥ x/(8e). From `coef418_half`, τ(n) ≤ C n^{1/16},
HeathBrown1985/DivisorEps, and t = x^{1/16}: the main term is at least t^16/(4e), the τ term
24C²/t² ≤ 1/2, the error at most K t^{12}.

This is the lower half of `BesselInput`'s coefficient condition for these coefficients, with
c = 1/(8e). The L² upper half, Section 4.4's Lemma 4 zero sum, stays cited, so `BesselInput`
itself is NOT discharged. AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.PintzAlthofer2026CoefHalf
import LeanLab.HeathBrown1985.DivisorEps

namespace LeanLab.ExceptionalSet.PintzAlthofer2026CoefLower

open Finset Real LeanLab.Routes.R5060

/-- From `x ≥ A^m` and `t^(m·j) = x`... the elementary step: if `t ≥ 0`, `s = t^j`,
`s^m = x` and `A^m ≤ x` with `A ≥ 0`, then `A ≤ s`. -/
lemma le_of_pow_le {s A x : ℝ} {m : ℕ} (hm : m ≠ 0) (hs : 0 ≤ s) (hA : 0 ≤ A)
    (hx : s ^ m = x) (h : A ^ m ≤ x) : A ≤ s := by
  by_contra hlt; push_neg at hlt
  have := pow_lt_pow_left₀ hlt hs hm
  linarith

set_option maxHeartbeats 1000000 in
theorem coef_lower : ∃ X0 : ℝ, ∀ x : ℕ, X0 ≤ x → ∀ n : ℕ, Even n → x / 2 < n → n ≤ x →
    (x : ℝ) / (8 * Real.exp 1) ≤ ‖LeanLab.ExceptionalSet.PintzAlthofer2026Beta.vTrunc x
      (Nat.sqrt x) (Nat.sqrt x) (fun q => ((bS n q : ℝ) : ℂ)) n‖ := by
  obtain ⟨C0, hC0, hcoef⟩ := LeanLab.ExceptionalSet.PintzAlthofer2026CoefHalf.coef418_half
  obtain ⟨C, hC, hτ⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow 16 (by norm_num)
  set e := Real.exp 1
  have he : 0 < e := Real.exp_pos 1
  set K := 425 * e * C0 * C ^ 2
  have hK : 0 < K := by positivity
  refine ⟨max 65536 (max ((48 * C ^ 2) ^ 8) ((8 * e * K) ^ 4)), fun x hx n hn hxn hnx => ?_⟩
  have hx1 : (65536 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have hxA : (48 * C ^ 2) ^ 8 ≤ (x : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxB : (8 * e * K) ^ 4 ≤ (x : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : (0 : ℝ) < x := by linarith
  -- t = x^{1/16}
  set t := (x : ℝ) ^ ((1 : ℝ) / 16) with ht_def
  have ht0 : 0 ≤ t := by positivity
  have ht16 : t ^ 16 = (x : ℝ) := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have ht2 : 2 ≤ t := le_of_pow_le (m := 16) (by norm_num) ht0 (by norm_num) ht16
    (by norm_num at hx1 ⊢; linarith)
  have hCt2 : 48 * C ^ 2 ≤ t ^ 2 := le_of_pow_le (m := 8) (by norm_num) (by positivity)
    (by positivity) (by rw [← pow_mul]; exact ht16) hxA
  have hKt4 : 8 * e * K ≤ t ^ 4 := le_of_pow_le (m := 4) (by norm_num) (by positivity)
    (by positivity) (by rw [← pow_mul]; exact ht16) hxB
  -- n and τ(n)
  have hx65 : (65536 : ℕ) ≤ x := by exact_mod_cast hx1
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnr : (n : ℝ) ≤ x := by exact_mod_cast hnx
  have hτn := hτ n hn1
  have hn16 : (n : ℝ) ^ ((16 : ℕ) : ℝ)⁻¹ ≤ t := by
    rw [ht_def]; norm_num
    exact Real.rpow_le_rpow (Nat.cast_nonneg n) hnr (by norm_num)
  have hτt : (n.divisors.card : ℝ) ≤ C * t := hτn.trans (mul_le_mul_of_nonneg_left hn16 hC.le)
  have hτ0 : (0 : ℝ) ≤ n.divisors.card := Nat.cast_nonneg _
  have hτ2 : (n.divisors.card : ℝ) ^ 2 ≤ C ^ 2 * t ^ 2 := by
    have := pow_le_pow_left₀ hτ0 hτt 2; nlinarith
  -- P = Nat.sqrt x
  set P := Nat.sqrt x
  have hPx : x < (P + 1) * (P + 1) := Nat.lt_succ_sqrt x
  have hP8 : t ^ 8 / 2 ≤ (P : ℝ) := by
    have h : (x : ℝ) < ((P : ℝ) + 1) ^ 2 := by
      have : ((x : ℕ) : ℝ) < (((P + 1) * (P + 1) : ℕ) : ℝ) := by exact_mod_cast hPx
      push_cast at this; nlinarith
    have h2 : t ^ 8 < (P : ℝ) + 1 := by
      by_contra hc; push_neg at hc
      have hsq := pow_le_pow_left₀ (by positivity) hc 2
      have h16 : (t ^ 8) ^ 2 = (x : ℝ) := by rw [← pow_mul]; exact ht16
      linarith
    have : 2 ≤ t ^ 8 := by nlinarith [pow_le_pow_left₀ (by norm_num) ht2 8]
    linarith
  have hP2 : 2 ≤ P := by
    have : (2 : ℝ) ≤ P := by nlinarith [pow_le_pow_left₀ (by norm_num) ht2 8]
    exact_mod_cast this
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hPle : (P : ℝ) ≤ x := by exact_mod_cast Nat.sqrt_le_self x
  have hsqP : t ^ 4 / 2 ≤ Real.sqrt P := by
    apply Real.le_sqrt_of_sq_le
    have : (t ^ 4 / 2) ^ 2 = t ^ 8 / 4 := by ring
    rw [this]; have : 0 ≤ t ^ 8 := by positivity
    linarith
  -- log bounds
  have hlogt : Real.log t ≤ t := by
    have := Real.log_le_sub_one_of_pos (show 0 < t by linarith); linarith
  have hlogx : Real.log x = 16 * Real.log t := by
    rw [← ht16, Real.log_pow]; norm_num
  have hlogP : Real.log P ≤ 16 * t := by
    have := Real.log_le_log hPr hPle; rw [hlogx] at this; linarith
  have hlogP0 : 0 ≤ Real.log P := Real.log_nonneg (by exact_mod_cast (show 1 ≤ P by omega))
  have hl2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hb1 : 1 + Real.log P / Real.log 2 ≤ 25 * t := by
    have : Real.log P / Real.log 2 ≤ 16 * t / 0.69 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    have : 16 * t / 0.69 ≤ 24 * t := by rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  have hb2 : 1 + Real.log P ≤ 17 * t := by linarith
  -- apply coef418_half
  have hmain := hcoef n P x hn hn2 hP2 hx0
  -- main term
  have hexp : Real.exp (-1) ≤ Real.exp (-(n : ℝ) / x) := by
    apply Real.exp_le_exp.2
    rw [neg_div, neg_le_neg_iff, div_le_one hx0]; exact hnr
  have hnhalf : (x : ℝ) / 2 ≤ n := by
    have : ((x / 2 : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hxn
    have h2 : (x : ℝ) / 2 ≤ ((x / 2 : ℕ) : ℝ) + 1 := by
      have := Nat.lt_div_mul_add (a := x) (show 0 < 2 by norm_num)
      have : ((x : ℕ) : ℝ) < ((x / 2 * 2 + 2 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    linarith
  have hemi : Real.exp (-1) = 1 / e := by rw [Real.exp_neg]; simp [e]
  have hA : (x : ℝ) / (2 * e) ≤ n * Real.exp (-(n : ℝ) / x) := by
    calc (x : ℝ) / (2 * e) = (x / 2) * Real.exp (-1) := by rw [hemi]; field_simp
      _ ≤ n * Real.exp (-(n : ℝ) / x) :=
          mul_le_mul hnhalf hexp (by positivity) (Nat.cast_nonneg n)
  -- bracket
  have hbr : (1 / 2 : ℝ) ≤ 1 - 12 * (n.divisors.card : ℝ) ^ 2 / Real.sqrt P := by
    have hs : 0 < Real.sqrt P := Real.sqrt_pos.2 hPr
    have : 12 * (n.divisors.card : ℝ) ^ 2 / Real.sqrt P ≤ 1 / 2 := by
      rw [div_le_iff₀ hs]
      have ht2' : 0 ≤ t ^ 2 := by positivity
      have h48 : 48 * C ^ 2 * t ^ 2 ≤ t ^ 2 * t ^ 2 := mul_le_mul_of_nonneg_right hCt2 ht2'
      have h44 : t ^ 2 * t ^ 2 = t ^ 4 := by ring
      have hτ12 : 12 * (n.divisors.card : ℝ) ^ 2 ≤ 12 * (C ^ 2 * t ^ 2) := by linarith
      linarith
    linarith
  -- error
  have hpi : 1 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  have hXP : (x : ℝ) / (2 * π ^ 2 * P) ≤ t ^ 8 := by
    rw [div_le_iff₀ (by positivity)]
    have : (x : ℝ) = t ^ 8 * t ^ 8 := by rw [← pow_add]; exact ht16.symm
    rw [this]
    have h8 : 0 ≤ t ^ 8 := by positivity
    have hPP : (P : ℝ) ≤ π ^ 2 * P := by
      have := mul_le_mul_of_nonneg_right hpi hPr.le; linarith
    have h2P : t ^ 8 ≤ 2 * π ^ 2 * P := by linarith
    exact mul_le_mul_of_nonneg_left h2P h8
  have herr : (x : ℝ) / (2 * π ^ 2 * P) * (C0 * (e * (1 + Real.log P / Real.log 2)) *
      (n.divisors.card : ℝ) ^ 2 * (1 + Real.log P)) ≤ K * t ^ 12 := by
    have h1 : 0 ≤ 1 + Real.log P / Real.log 2 := by positivity
    have h2 : 0 ≤ 1 + Real.log P := by linarith
    have hX0' : 0 ≤ (x : ℝ) / (2 * π ^ 2 * P) := by positivity
    calc (x : ℝ) / (2 * π ^ 2 * P) * (C0 * (e * (1 + Real.log P / Real.log 2)) *
          (n.divisors.card : ℝ) ^ 2 * (1 + Real.log P))
        ≤ t ^ 8 * (C0 * (e * (25 * t)) * (C ^ 2 * t ^ 2) * (17 * t)) := by
          apply mul_le_mul hXP _ (by positivity) (by positivity)
          apply mul_le_mul _ hb2 h2 (by positivity)
          apply mul_le_mul _ hτ2 (by positivity) (by positivity)
          apply mul_le_mul_of_nonneg_left _ hC0.le
          exact mul_le_mul_of_nonneg_left hb1 he.le
      _ = K * t ^ 12 := by simp only [K]; ring
  have hKt : K * t ^ 12 ≤ (x : ℝ) / (8 * e) := by
    rw [le_div_iff₀ (by positivity), ← ht16]
    have h12 : 0 ≤ t ^ 12 := by positivity
    have : K * t ^ 12 * (8 * e) = (8 * e * K) * t ^ 12 := by ring
    rw [this]
    calc (8 * e * K) * t ^ 12 ≤ t ^ 4 * t ^ 12 := mul_le_mul_of_nonneg_right hKt4 h12
      _ = t ^ 16 := by ring
  -- combine
  have hA0 : 0 ≤ (x : ℝ) / (2 * e) := by positivity
  have hmt : (x : ℝ) / (2 * e) * (1 / 2) ≤
      (n * Real.exp (-(n : ℝ) / x)) * (1 - 12 * (n.divisors.card : ℝ) ^ 2 / Real.sqrt P) :=
    mul_le_mul hA hbr (by norm_num) (by positivity)
  have hfin : (x : ℝ) / (2 * e) * (1 / 2) - (x : ℝ) / (8 * e) = (x : ℝ) / (8 * e) := by
    field_simp; ring
  linarith

end LeanLab.ExceptionalSet.PintzAlthofer2026CoefLower
