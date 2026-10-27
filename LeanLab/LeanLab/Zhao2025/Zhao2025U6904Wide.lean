import Mathlib
import LeanLab.Zhao2025.Zhao2025U6900Cert

/-!
# Zhao 2025, the Theorem I check with `e^{-a}` bounded below up to `a = 16`

G. Zhao, arXiv 2511.05631v2, a preprint.  Unit U-6904, CLOUD MANUAL-M2, T2.  AI wrote the Lean code.
Binary Goldbach is open.

`chk` of U-6900 needs `2z₂ ≤ 8` for the lower Taylor bound of `e^{-2z₂}`; grids with small `λ₀` and a
top of 5.2 or 5.68 reach `2z₂` near 10.  Here `e^{-a} ≥ eloq(a/2)²` for `0 ≤ a ≤ 16`, and `chkW`,
`chkW_sound` are `chk`, `chk_sound` with that bound.
-/

namespace LeanLab.Zhao2025.U6900

open LeanLab.Pintz2018 LeanLab.Zhao2025.U6825 LeanLab.Zhao2025.U6841

/-- `e^{-a} ≥ eloq(a/2)²`, valid for `0 ≤ a ≤ 16`. -/
def eloqW (a : ℚ) : ℚ := eloq (a / 2) ^ 2

def G2loW (z : ℚ) : ℚ := 4 * (z + 1) ^ 2 * eloqW (2 * z) / z ^ 6 + Rq z

def chkW (l0 L x : ℚ) (n : ℕ) : Bool :=
  decide (4 * l0 / 5 ≤ x) && decide (0 < l0) && decide (l0 < L) &&
  decide (2 * ((L - l0) / x) ≤ 16) && decide (-2 * (-l0 / x) ≤ 8) &&
  decide (0 < eloq (2 * ((L - l0) / x) / 2)) && decide (0 < eloq (-2 * (-l0 / x))) &&
  decide (0 < G1lo (-l0 / x)) && decide (0 < G2loW ((L - l0) / x) - 8 / 45 * x) &&
  decide (1 < ((n : ℚ) + 1) *
    ((G2loW ((L - l0) / x) - 8 / 45 * x) ^ 2 / G1hi (-l0 / x) ^ 2 - 1 / 10 ^ 8))

theorem eloqW_le (a : ℚ) (h0 : 0 ≤ a) (h16 : a ≤ 16) (hp : 0 < eloq (a / 2)) :
    ((eloqW a : ℚ) : ℝ) ≤ Real.exp (-(a : ℝ)) := by
  have h := eloq_le (a / 2) (by linarith) (by linarith)
  have hp' : (0 : ℝ) ≤ ((eloq (a / 2) : ℚ) : ℝ) := by exact_mod_cast hp.le
  unfold eloqW; push_cast
  have e : Real.exp (-(a : ℝ)) = Real.exp (-(((a / 2 : ℚ)) : ℝ)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e]; exact pow_le_pow_left₀ hp' h 2

theorem G2loW_le (z : ℚ) (hz : 0 < z) (h16 : 2 * z ≤ 16) (hp : 0 < eloq (2 * z / 2)) :
    ((G2loW z : ℚ) : ℝ) ≤ Gz (z : ℝ) := by
  have hz' : (0 : ℝ) < z := by exact_mod_cast hz
  rw [Gz_eq _ hz'.ne']
  unfold G2loW; push_cast; rw [Rq_cast]
  have he := eloqW_le (2 * z) (by linarith) h16 hp
  push_cast at he
  have hc : 0 ≤ 4 * ((z : ℝ) + 1) ^ 2 / (z : ℝ) ^ 6 := by positivity
  have := mul_le_mul_of_nonneg_left he hc
  have e1 : 4 * ((z : ℝ) + 1) ^ 2 * ((eloqW (2 * z) : ℚ) : ℝ) / (z : ℝ) ^ 6 =
      4 * ((z : ℝ) + 1) ^ 2 / (z : ℝ) ^ 6 * ((eloqW (2 * z) : ℚ) : ℝ) := by ring
  have e2 : 4 * ((z : ℝ) + 1) ^ 2 * Real.exp (-(2 * (z : ℝ))) / (z : ℝ) ^ 6 =
      4 * ((z : ℝ) + 1) ^ 2 / (z : ℝ) ^ 6 * Real.exp (-(2 * (z : ℝ))) := by ring
  rw [e1, e2]; linarith

/-- PROVED: a passing wide check gives `Δ > 0`, `Δ² > ε` and `1/(Δ² - ε) < n + 1` for `0 ≤ ε ≤ 10⁻⁸`. -/
theorem chkW_sound (l0 L x : ℚ) (n : ℕ) (h : chkW l0 L x n = true) (ε : ℝ) (hε : ε ≤ 1 / 10 ^ 8) :
    4 * (l0 : ℝ) / 5 ≤ x ∧ 0 < Delta x L l0 ∧ ε < Delta x L l0 ^ 2 ∧
      1 / (Delta x L l0 ^ 2 - ε) < n + 1 := by
  simp only [chkW, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hx, hl0⟩, hlL⟩, h8a⟩, h8b⟩, hpa⟩, hpb⟩, hG1lo⟩, hnum⟩, hfin⟩ := h
  have hxpos : 0 < x := by linarith
  have hz2 : 0 < (L - l0) / x := div_pos (by linarith) hxpos
  have hz1 : -l0 / x < 0 := div_neg_of_neg_of_pos (by linarith) hxpos
  have g2 := G2loW_le _ hz2 h8a hpa
  obtain ⟨g1l, g1h⟩ := G1_bounds _ hz1 h8b hpb
  have c2 : (((L - l0) / x : ℚ) : ℝ) = ((L : ℝ) - l0) / x := by push_cast; rfl
  have c1 : ((-l0 / x : ℚ) : ℝ) = -(l0 : ℝ) / x := by push_cast; rfl
  rw [c2] at g2; rw [c1] at g1l g1h
  set num : ℚ := G2loW ((L - l0) / x) - 8 / 45 * x with hnumdef
  set den : ℚ := G1hi (-l0 / x) with hdendef
  have hG1pos : (0 : ℝ) < Gz (-(l0 : ℝ) / x) := lt_of_lt_of_le (by exact_mod_cast hG1lo) g1l
  have hden : (0 : ℝ) < (den : ℝ) := lt_of_lt_of_le hG1pos g1h
  have hnum' : (0 : ℝ) < (num : ℝ) := by exact_mod_cast hnum
  have hnumle : (num : ℝ) ≤ Gz (((L : ℝ) - l0) / x) - 8 / 45 * (x : ℝ) := by
    rw [hnumdef]; push_cast; linarith
  have hD : Delta x L l0 = (Gz (((L : ℝ) - l0) / x) - 8 / 45 * (x : ℝ)) / Gz (-(l0 : ℝ) / x) := by
    unfold Delta; field_simp; ring
  have hDlo : (num : ℝ) / den ≤ Delta x L l0 := by
    rw [hD]
    calc (num : ℝ) / den ≤ (num : ℝ) / Gz (-(l0 : ℝ) / x) :=
          div_le_div_of_nonneg_left hnum'.le hG1pos g1h
      _ ≤ _ := div_le_div_of_nonneg_right hnumle hG1pos.le
  have hq : (0 : ℝ) < (num : ℝ) / den := div_pos hnum' hden
  have hDpos : 0 < Delta x L l0 := lt_of_lt_of_le hq hDlo
  have hsq : ((num : ℝ) / den) ^ 2 ≤ Delta x L l0 ^ 2 := pow_le_pow_left₀ hq.le hDlo 2
  have hfin' : (1 : ℝ) < ((n : ℝ) + 1) * (((num : ℝ) / den) ^ 2 - 1 / 10 ^ 8) := by
    have : ((1 : ℚ) : ℝ) < ((((n : ℚ) + 1) * (num ^ 2 / den ^ 2 - 1 / 10 ^ 8) : ℚ) : ℝ) := by
      exact_mod_cast hfin
    push_cast at this; rw [div_pow]; linarith
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpos : 0 < Delta x L l0 ^ 2 - ε := by
    by_contra hc; push Not at hc
    have : ((n : ℝ) + 1) * (((num : ℝ) / den) ^ 2 - 1 / 10 ^ 8) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos hn1.le
      nlinarith
    linarith
  refine ⟨by exact_mod_cast hx, hDpos, by linarith, ?_⟩
  rw [div_lt_iff₀ hpos]
  nlinarith

end LeanLab.Zhao2025.U6900
