import LeanLab.RieselVaughan1983.Lemma8
import LeanLab.ChenExplicit.TwinCNumeric

/-!
# P0032 Lemma 5, the final numerical step (3.21) at the rows the lab uses

Session 20261020T2113Z-cloud51, unit U-6740, paper P0032 Riesel-Vaughan 1983, track T1.
AI wrote this Lean code. Binary Goldbach is OPEN; nothing here bears on it directly.

Lemma 5, p. 53 to 55, is proved in the paper in three steps: Montgomery-Vaughan 1973
Corollary 1 gives (3.19); Lemma 4 with λ = 3/2 gives `F(x) > B` for `x ≥ e^L`, hence (3.20);
and the inequality (3.21), `(log x)(A + log x)(B + log x) < 4C(B − A) x^{1/2} / 51` at
`x = e^L`, turns the `2x^{1/2}` of (3.20) into the `−100x^{1/2}` of the statement.
This file proves only the last step, (3.21) at `x = e^L`, for the rows
`(L, A, B) = (24, 0, 0.97), (42, 8, 8.04), (60, 8.3, 8.302), (278, 8.43, 8.4301),
(396, 8.44, 8.44004)` used by `theorem_LS4`, with `C = Ctw = 2 twinC` and the lab's
`twinC_ge_065`. The tightest row is L = 24, ratio about 1.137 with the paper's C.
The paper's extension from `x = e^L` to `x ≥ e^L` uses that `(log x) x^{-1/6}` decreases,
not formalized here. Rows of `Lemma5Used` and `Lemma5Neg` stay CITED.
-/

namespace LeanLab.RieselVaughan1983

open Real

lemma Ctw_ge : (13 / 10 : ℝ) ≤ Ctw := by
  have := LeanLab.ChenExplicit.twinC_ge_065
  unfold Ctw; linarith

/-- `e^n ≥ 2.7^n`. -/
lemma exp_nat_ge (n : ℕ) : (27 / 10 : ℝ) ^ n ≤ Real.exp n := by
  have he : (27 / 10 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  calc (27 / 10 : ℝ) ^ n ≤ Real.exp 1 ^ n := pow_le_pow_left₀ (by norm_num) he n
    _ = Real.exp n := by rw [← Real.exp_nat_mul, mul_one]

/-- (3.21) at `x = e^L`, written with `log x = L` and `x^{1/2} = e^{L/2}`. -/
def Eq321 (L A B : ℝ) : Prop :=
  L * (A + L) * (B + L) < 4 * Ctw * (B - A) / 51 * Real.exp (L / 2)

lemma eq321_of (L A B : ℝ) (n : ℕ) (hn : L / 2 = n) (hBA : 0 < B - A)
    (h : L * (A + L) * (B + L) < 4 * (13 / 10) * (B - A) / 51 * (27 / 10 : ℝ) ^ n) :
    Eq321 L A B := by
  unfold Eq321
  have hC := Ctw_ge
  have hE := exp_nat_ge n
  rw [hn]
  have hp : (0 : ℝ) < (27 / 10 : ℝ) ^ n := by positivity
  calc L * (A + L) * (B + L) < 4 * (13 / 10) * (B - A) / 51 * (27 / 10 : ℝ) ^ n := h
    _ ≤ 4 * Ctw * (B - A) / 51 * Real.exp n := by
      apply mul_le_mul _ hE hp.le (by positivity)
      apply div_le_div_of_nonneg_right _ (by norm_num)
      nlinarith

theorem eq321_24 : Eq321 24 0 (97 / 100) :=
  eq321_of _ _ _ 12 (by norm_num) (by norm_num) (by norm_num)

theorem eq321_42 : Eq321 42 8 (804 / 100) :=
  eq321_of _ _ _ 21 (by norm_num) (by norm_num) (by norm_num)

theorem eq321_60 : Eq321 60 (83 / 10) (8302 / 1000) :=
  eq321_of _ _ _ 30 (by norm_num) (by norm_num) (by norm_num)

theorem eq321_278 : Eq321 278 (843 / 100) (84301 / 10000) :=
  eq321_of _ _ _ 139 (by norm_num) (by norm_num) (by norm_num)

theorem eq321_396 : Eq321 396 (844 / 100) (844004 / 100000) :=
  eq321_of _ _ _ 198 (by norm_num) (by norm_num) (by norm_num)

end LeanLab.RieselVaughan1983

/-! ## Extension of (3.21) from `x = e^L` to all `x ≥ e^L`, writing `t = log x`

The paper: `(log x) x^{-1/6}` decreases for `x ≥ e^6`. Here: for `c ≥ 0`, `6 ≤ s ≤ t`,
`c + t ≤ (c + s) e^{(t-s)/6}`, from `e^u ≥ 1 + u`, applied to the three factors. -/

namespace LeanLab.RieselVaughan1983

lemma factor_le (c s t : ℝ) (hc : 0 ≤ c) (hs : 6 ≤ s) (hst : s ≤ t) :
    c + t ≤ (c + s) * Real.exp ((t - s) / 6) := by
  have h1 := Real.add_one_le_exp ((t - s) / 6)
  have hcs : 0 ≤ c + s := by linarith
  have : (c + s) * ((t - s) / 6 + 1) ≤ (c + s) * Real.exp ((t - s) / 6) :=
    mul_le_mul_of_nonneg_left h1 hcs
  nlinarith

theorem eq321_mono (L A B t : ℝ) (h : Eq321 L A B) (hL : 6 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht : L ≤ t) : Eq321 t A B := by
  unfold Eq321 at *
  set E := Real.exp ((t - L) / 6) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hexp : Real.exp (t / 2) = Real.exp (L / 2) * E ^ 3 := by
    rw [hE, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have f0 := factor_le 0 L t le_rfl hL ht
  have fA := factor_le A L t hA hL ht
  have fB := factor_le B L t hB hL ht
  simp only [zero_add] at f0
  have hL0 : 0 ≤ L := by linarith
  have hp1 : t * (A + t) ≤ (L * E) * ((A + L) * E) :=
    mul_le_mul f0 fA (by linarith) (by positivity)
  have hp2 : t * (A + t) * (B + t) ≤ (L * E) * ((A + L) * E) * ((B + L) * E) :=
    mul_le_mul hp1 fB (by linarith) (by positivity)
  have hE3 : 0 < E ^ 3 := by positivity
  calc t * (A + t) * (B + t) ≤ L * (A + L) * (B + L) * E ^ 3 := by linarith [hp2]
    _ < 4 * Ctw * (B - A) / 51 * Real.exp (L / 2) * E ^ 3 := mul_lt_mul_of_pos_right h hE3
    _ = 4 * Ctw * (B - A) / 51 * Real.exp (t / 2) := by rw [hexp]; ring

end LeanLab.RieselVaughan1983
