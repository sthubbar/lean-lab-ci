/-
P0045 Languasco, Pintz, Zaccagnini 2007, Section 3 p.4: the minor arc bound
`S(α) ≪ X^{4/5} L⁴` on `𝔪`, PROVED from the lab's Vinogradov bound.

Unit U-1228, T1 PROVE, PC run 20261020T1203Z-6833.

Route:
* `minor_dirichlet`: every `α ∈ 𝔪` has a reduced `a/q` with `P < q ≤ X/P` and `|α − a/q| ≤ 1/q²`,
  by Dirichlet with `Q = ⌊X/P⌋`; a `q ≤ P` would put `α` on a major arc, since `P(P+1) ≤ X`.
* The lab's `PNTPort.Vinogradov.vinogradov_minor`, PROVED, gives
  `|S(α)| ≤ 300 (N/√q + N^{4/5} + √(Nq)) (1 + log N)⁴` with `N = ⌊X⌋`.
* `minorBound_proved : MinorBound`: with `P ≥ X^{0.4}`, `N/√q ≤ X/√P ≤ X^{4/5}` and
  `√(Nq) ≤ X/√P ≤ X^{4/5}`, so `|S(α)| ≤ 14400 X^{4/5} L⁴`. The paper cites its Lemma 6.3 for this.
* `eq7_proved`, `minorL2_proved`: the paper's (7) and its L² bound, PROVED unconditional.
* `mainJ_twoC0_of_eq25`: the repaired P0045 Theorem on `J(X)`, constant `2c₀ C(k, N)`,
  CONDITIONAL ON the repaired (25), the major arc analysis, ONLY.

KNOWN mathematics. AI wrote this Lean code. Checked only by the Lean kernel.
Binary Goldbach is OPEN; nothing here is Goldbach.
-/
import Mathlib
import LeanLab.LPZ2007.RgUpperProof
import LeanLab.PNTPort.Vinogradov.MinorArcs

namespace LeanLab.LPZ2007.MinorBoundProof

open Finset Real LeanLab.LPZ2007 LeanLab.LPZ2007.ExceptionalOfSup LeanLab.LPZ2007.MinorBessel

noncomputable section

theorem e_eq (x : ℝ) : LeanLab.LPZ2007.e x = LeanLab.PNTPort.LargeSieve.e x := by
  unfold LeanLab.LPZ2007.e LeanLab.PNTPort.LargeSieve.e
  congr 1
  push_cast
  ring

theorem Sx_eq (X α : ℝ) : Sx X α = LeanLab.PNTPort.Vinogradov.S ⌊X⌋₊ α := by
  unfold Sx LeanLab.PNTPort.Vinogradov.S
  refine sum_congr rfl fun m _ => ?_
  rw [e_eq]

/-- A point of the minor arcs has a Dirichlet approximation with `P < q ≤ X/P`. -/
theorem minor_dirichlet {X P : ℝ} (hP1 : 1 ≤ P) (hPX : P * (P + 1) ≤ X) {α : ℝ}
    (hα : α ∈ minorArcs X P) :
    ∃ (a : ℤ) (q : ℕ), 1 ≤ q ∧ P < q ∧ (q : ℝ) ≤ X / P ∧ IsCoprime a (q : ℤ) ∧
      |α - a / q| ≤ 1 / (q : ℝ) ^ 2 := by
  have hP0 : 0 < P := by linarith
  have hX : 0 < X := by nlinarith
  have hXP1 : 1 ≤ X / P := by rw [le_div_iff₀ hP0]; nlinarith
  set Q : ℕ := ⌊X / P⌋₊ with hQdef
  have hQ1 : 1 ≤ Q := Nat.le_floor (by exact_mod_cast hXP1)
  obtain ⟨a, q, hq1, hqQ, hcop, hαq⟩ := LeanLab.PNTPort.Vinogradov.dirichlet_reduced α hQ1
  have hQlt : X / P < (Q : ℝ) + 1 := Nat.lt_floor_add_one _
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hq0 : (0 : ℝ) < q := by linarith
  have hqQr : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hqXP : (q : ℝ) ≤ X / P := hqQr.trans (Nat.floor_le (by positivity))
  have hXlt : X < P * ((Q : ℝ) + 1) := by rwa [div_lt_iff₀ hP0, mul_comm] at hQlt
  have hsmall : 1 / ((q : ℝ) * ((Q : ℝ) + 1)) < P / (q * X) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have habs := abs_le.1 hαq
  refine ⟨a, q, hq1, ?_, hqXP, hcop, ?_⟩
  · by_contra hle
    push_neg at hle
    apply hα.2
    have hlo : P / X ≤ α := hα.1.1
    have hhi : α ≤ 1 + P / X := hα.1.2
    -- `a ≥ 1`
    have hPqX : P / (q * X) ≤ P / X := by
      apply div_le_div_of_nonneg_left hP0.le hX; nlinarith
    have ha_pos : (0 : ℝ) < a / q := by linarith [habs.1, habs.2, hlo, hsmall, hPqX]
    have ha_pos' : (0 : ℝ) < a := by
      have := mul_pos ha_pos hq0; rwa [div_mul_cancel₀ _ hq0.ne'] at this
    have ha1 : (1 : ℤ) ≤ a := by
      have : (0 : ℤ) < a := by exact_mod_cast ha_pos'
      omega
    -- `a ≤ q`
    have hupper : (a : ℝ) / q < 1 + 1 / q := by
      have h1 : (a : ℝ) / q < 1 + P / X + P / (q * X) := by linarith [habs.1, habs.2, hhi, hsmall]
      have h2 : P / X + P / (q * X) ≤ 1 / q := by
        rw [div_add_div _ _ hX.ne' (by positivity), div_le_div_iff₀ (by positivity) hq0]
        have : P * (q + 1) ≤ X := by nlinarith
        have hm := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ (q : ℝ) * X)
        nlinarith [hm]
      linarith
    have haq : a ≤ (q : ℤ) := by
      have : (a : ℝ) < q + 1 := by
        have := mul_lt_mul_of_pos_right hupper hq0
        rwa [div_mul_cancel₀ _ hq0.ne', add_mul, one_mul, div_mul_cancel₀ _ hq0.ne'] at this
      have : a < (q : ℤ) + 1 := by exact_mod_cast this
      omega
    set a' : ℕ := a.toNat with ha'
    have ha'a : ((a' : ℕ) : ℤ) = a := Int.toNat_of_nonneg (by omega)
    have ha'r : ((a' : ℕ) : ℝ) = (a : ℝ) := by rw [← ha'a]; rfl
    have hcop' : Nat.Coprime a' q := by
      rw [← ha'a, Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast] at hcop
      exact hcop
    have hwidth : 1 / ((q : ℝ) * (X / P)) = P / (q * X) := by field_simp
    refine ⟨q, a', hq1, hle, by omega, by omega, hcop', ?_, ?_⟩
    · rw [ha'r, hwidth]; linarith [habs.1, habs.2]
    · rw [ha'r, hwidth]; linarith [habs.1, habs.2]
  · refine hαq.trans ?_
    rw [sq]
    apply one_div_le_one_div_of_le (by positivity)
    apply mul_le_mul_of_nonneg_left _ hq0.le
    linarith

/-- **P0045's Section 3 minor arc bound, PROVED unconditional**: `S(α) ≤ 14400 X^{4/5} L⁴` on `𝔪`. -/
theorem minorBound_proved : MinorBound := by
  refine ⟨300 * 3 * 16, 64, fun X hX P hP α hα => ?_⟩
  obtain ⟨hP0, hPX⟩ := Eq3Reduce.prange_ok hX hP
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hP1 : 1 ≤ P := le_trans (Real.one_le_rpow hX1 (by norm_num)) hP.1
  obtain ⟨a, q, hq1, hPq, hqXP, hcop, hαq⟩ := minor_dirichlet hP1 hPX hα
  set N : ℕ := ⌊X⌋₊ with hNdef
  have hNX : (N : ℝ) ≤ X := Nat.floor_le hX0.le
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.le_floor (by exact_mod_cast hX1 : ((1 : ℕ) : ℝ) ≤ X)
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqN : q ≤ N := Nat.le_floor (hqXP.trans (div_le_self hX0.le hP1))
  have hv := LeanLab.PNTPort.Vinogradov.vinogradov_minor hq1 hcop hαq hqN
  rw [Sx_eq]
  refine hv.trans ?_
  -- `√P ≥ X^{1/5}`
  have hsP : X ^ (1 / 5 : ℝ) ≤ Real.sqrt P := by
    rw [Real.sqrt_eq_rpow]
    calc X ^ (1 / 5 : ℝ) = (X ^ (0.4 : ℝ)) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul hX0.le]; norm_num
      _ ≤ P ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) hP.1 (by norm_num)
  have hX15 : 0 < X ^ (1 / 5 : ℝ) := by positivity
  have hsplit : X = X ^ (1 / 5 : ℝ) * X ^ (4 / 5 : ℝ) := by
    rw [← Real.rpow_add hX0]; norm_num
  have hXsP : X / Real.sqrt P ≤ X ^ (4 / 5 : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    calc X = X ^ (4 / 5 : ℝ) * X ^ (1 / 5 : ℝ) := by rw [mul_comm]; exact hsplit
      _ ≤ X ^ (4 / 5 : ℝ) * Real.sqrt P := by gcongr
  have hsq : Real.sqrt q ≥ Real.sqrt P := Real.sqrt_le_sqrt hPq.le
  have hsP0 : 0 < Real.sqrt P := by linarith
  have t1 : (N : ℝ) / Real.sqrt q ≤ X ^ (4 / 5 : ℝ) := by
    calc (N : ℝ) / Real.sqrt q ≤ X / Real.sqrt P := by
          apply div_le_div₀ hX0.le hNX hsP0 hsq
      _ ≤ _ := hXsP
  have t2 : (N : ℝ) ^ ((4 : ℝ) / 5) ≤ X ^ (4 / 5 : ℝ) := by
    have := Real.rpow_le_rpow (by linarith) hNX (show (0 : ℝ) ≤ 4 / 5 by norm_num)
    simpa using this
  have t3 : Real.sqrt (N * q) ≤ X ^ (4 / 5 : ℝ) := by
    have hNq : (N : ℝ) * q ≤ X * (X / P) := mul_le_mul hNX hqXP (by linarith) hX0.le
    have : Real.sqrt (X * (X / P)) = X / Real.sqrt P := by
      rw [Real.sqrt_mul hX0.le, Real.sqrt_div hX0.le, ← mul_div_assoc, Real.mul_self_sqrt hX0.le]
    calc Real.sqrt (N * q) ≤ Real.sqrt (X * (X / P)) := Real.sqrt_le_sqrt hNq
      _ = X / Real.sqrt P := this
      _ ≤ _ := hXsP
  have hL1 : 1 ≤ Lg X := one_le_Lg (by linarith)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlog : 1 + Real.log N ≤ 2 * Lg X := by
    have h1 : Real.log N ≤ Real.log X := Real.log_le_log (by linarith) hNX
    have h2 : Real.log X = Real.log 2 * Lg X := log_eq_Lg
    have h3 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have h4 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  have hpow : (1 + Real.log N) ^ 4 ≤ 16 * Lg X ^ 4 := by
    calc (1 + Real.log N) ^ 4 ≤ (2 * Lg X) ^ 4 := pow_le_pow_left₀ (by linarith) hlog 4
      _ = 16 * Lg X ^ 4 := by ring
  have hX45 : 0 ≤ X ^ (4 / 5 : ℝ) := by positivity
  calc 300 * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * q)) *
        (1 + Real.log N) ^ 4
      ≤ 300 * (3 * X ^ (4 / 5 : ℝ)) * (16 * Lg X ^ 4) := by
        have hsum : (N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * q) ≤
            3 * X ^ (4 / 5 : ℝ) := by linarith
        have hD : 0 ≤ (1 + Real.log N) ^ 4 := by positivity
        have hA : 0 ≤ 300 * (3 * X ^ (4 / 5 : ℝ)) := by positivity
        calc 300 * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * q)) *
              (1 + Real.log N) ^ 4 ≤ 300 * (3 * X ^ (4 / 5 : ℝ)) * (1 + Real.log N) ^ 4 := by
              apply mul_le_mul_of_nonneg_right _ hD; linarith
          _ ≤ 300 * (3 * X ^ (4 / 5 : ℝ)) * (16 * Lg X ^ 4) :=
              mul_le_mul_of_nonneg_left hpow hA
    _ = 300 * 3 * 16 * X ^ (4 / 5 : ℝ) * Lg X ^ 4 := by ring

/-- P0045's (7), PROVED unconditional. -/
theorem eq7_proved : Eq7 := eq7_of_minorBound minorBound_proved

/-- P0045's Section 3 L² bound, PROVED unconditional. -/
theorem minorL2_proved : MinorL2 := minorL2_of_minorBound minorBound_proved

/-- **The repaired P0045 Theorem on `J(X)`**, constant `2c₀ C(k, N)`, CONDITIONAL ON the repaired
(25) only, the major arc analysis. -/
theorem mainJ_twoC0_of_eq25 (h25 : Eq25C (fun k N => twoC0 * Ckn k N)) : MainJ_twoC0 :=
  RgUpperProof.mainJ_twoC0_of_two_inputs minorBound_proved h25

/-- The printed Theorem with the printed constant `C(k, N)`, CONDITIONAL ON the printed (25), which
F-0038 says is false; kept to show where the error enters. -/
theorem mainJ_of_eq25 (h25 : Eq25) : MainJ :=
  mainJC_of_sec5 Ckn RgUpperProof.eq3_proved eq7_proved h25

end

end LeanLab.LPZ2007.MinorBoundProof
