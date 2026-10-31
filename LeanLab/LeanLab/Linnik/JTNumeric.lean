/-
AI-written Lean code, Claude, 2026-10-18, run 20261018T0903Z-17311, unit U-0921.
P0025 Johnston, Trudgian 2026, An update on the Linnik-Goldbach problem, arXiv 2605.17825 v2,
read in Claude in Chrome at arxiv.org/html/2605.17825v2, Section 3: Theorem 2, the
Pintz-Ruzsa criterion (23); C₂' of (19); c₁ of (20); R₀ bounds (17); A(k) bounds of
Khalfalah-Pintz; C₀ the twin prime constant (4); C₁ = 6.7814 of Proposition 2; Table 1.

The analytic content, Theorem 2 and Proposition 2, stays cited. PROVED here: the numeric step
of the proof of Theorem 1, and that Table 1's unconditional K = 7 entry is not the threshold of
the paper's own setup P = N^{4/9-ε}: C₁ = 6.75 already satisfies (23), where the table asks for
6.737. The printed 6.737 matches P = N^{0.4}, Pintz-Ruzsa's choice, by the lab's Python,
numerics jt_U0921.py. The paper's conclusions survive: Theorem 1 is unaffected, and C₁ = 6.7814
is still above 6.7619, so K = 7 unconditionally is still just out of reach by this method.
Goldbach is open.
-/
import LeanLab.ChenExplicit.TwinCNumeric
import LeanLab.ChenExplicit.Reductions

open Real

noncomputable section
namespace LeanLab.Linnik.JT

/-- (19) C₂' = ½(C₁ + ε - 2) R₀ C₀ + (1 - log P / log N) log 2 / 2, with `lp = log P / log N`. -/
def C2p (C1 ε R0 C0 lp : ℝ) : ℝ := 1 / 2 * (C1 + ε - 2) * R0 * C0 + (1 - lp) * log 2 / 2

/-- The left side of (23) for K = i + j. -/
def crit (Ai Aj C2 c1 : ℝ) (i j : ℕ) : ℝ :=
  √(Ai + C2 * c1 ^ (2 * i - 2)) * √(Aj + C2 * c1 ^ (2 * j - 2))

lemma C2p_le {C1 ε R0 C0 lp C1m εm R0m C0m lpm : ℝ} (h1 : C1 ≤ C1m) (he : ε ≤ εm)
    (hpos : 0 ≤ C1 + ε - 2) (hR0 : 0 ≤ R0) (hR : R0 ≤ R0m) (hC00 : 0 ≤ C0) (hC0 : C0 ≤ C0m)
    (hl : lpm ≤ lp) : C2p C1 ε R0 C0 lp ≤ C2p C1m εm R0m C0m lpm := by
  unfold C2p
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have a : (C1 + ε - 2) * R0 * C0 ≤ (C1m + εm - 2) * R0m * C0m := by
    have := mul_le_mul (mul_le_mul (by linarith : C1 + ε - 2 ≤ C1m + εm - 2) hR hR0 (by linarith))
      hC0 hC00 (by have := mul_nonneg hpos hR0; nlinarith)
    exact this
  have b : (1 - lp) * log 2 ≤ (1 - lpm) * log 2 := mul_le_mul_of_nonneg_right (by linarith) hl2.le
  nlinarith

/-- **Proof of Theorem 1, numeric step**: K = 6 = 3 + 3 under GRH, c₁ = 0.7163436,
C₁ = 6.7814, log P / log N near 1/2. The left side of (23) is below 0.87 for every A(3) ≤ 0.013598,
R₀ ≤ 1.93656, C₀ ≤ 0.6614, ε ≤ 10⁻³ and log P / log N ≥ 0.49. The paper prints ≤ 0.865, which
needs the sharper C₀ = 0.66016. -/
theorem thm1_numeric {A3 R0 C0 ε lp : ℝ} (hA0 : 0 ≤ A3) (hA : A3 ≤ 0.013598)
    (hR0 : 0 ≤ R0) (hR : R0 ≤ 1.93656) (hC00 : 0 ≤ C0) (hC0 : C0 ≤ 0.6614)
    (he0 : 0 ≤ ε) (he : ε ≤ 1e-3) (hl : 0.49 ≤ lp) (hl1 : lp ≤ 1) :
    crit A3 A3 (C2p 6.7814 ε R0 C0 lp) 0.7163436 3 3 < 0.87 := by
  have hC := C2p_le (C1 := 6.7814) (C1m := 6.7814) (εm := 1e-3) (R0m := 1.93656) (C0m := 0.6614)
    (lpm := 0.49) le_rfl he (by linarith) hR0 hR hC00 hC0 hl
  have hC2 : 0 ≤ C2p 6.7814 ε R0 C0 lp := by
    unfold C2p
    have : 0 ≤ (1 - lp) * log 2 / 2 := by
      have := log_pos (show (1 : ℝ) < 2 by norm_num); nlinarith
    have : 0 ≤ 1 / 2 * (6.7814 + ε - 2) * R0 * C0 := by
      apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hR0 |>.trans_eq rfl |> fun h => mul_nonneg h hC00
    linarith
  have hmax : C2p 6.7814 1e-3 1.93656 0.6614 0.49 ≤ 3.24 := by
    unfold C2p; have := log_two_lt_d9; norm_num at this ⊢; linarith
  unfold crit
  have hx : 0 ≤ A3 + C2p 6.7814 ε R0 C0 lp * 0.7163436 ^ (2 * 3 - 2) := by positivity
  rw [← sqrt_mul hx, sqrt_mul_self hx]
  norm_num
  have : C2p 6.7814 ε R0 C0 lp * 0.7163436 ^ 4 ≤ 3.24 * 0.7163436 ^ 4 :=
    mul_le_mul_of_nonneg_right (hC.trans hmax) (by positivity)
  norm_num at this ⊢
  linarith

/-- The same with C₀ the twin prime constant, from `twinC_le_06614`. -/
theorem thm1_numeric_twinC {A3 R0 ε lp : ℝ} (hA0 : 0 ≤ A3) (hA : A3 ≤ 0.013598)
    (hR0 : 0 ≤ R0) (hR : R0 ≤ 1.93656) (he0 : 0 ≤ ε) (he : ε ≤ 1e-3) (hl : 0.49 ≤ lp)
    (hl1 : lp ≤ 1) :
    crit A3 A3 (C2p 6.7814 ε R0 LeanLab.ChenExplicit.twinC lp) 0.7163436 3 3 < 1 := by
  have h := thm1_numeric hA0 hA hR0 hR LeanLab.ChenExplicit.twinC_pos.le
    (by have := LeanLab.ChenExplicit.twinC_le_06614; norm_num at this ⊢; linarith) he0 he hl hl1
  linarith

/-- **Table 1, K = 7 = 4 + 3 unconditionally, c₁ = 0.7894009, P = N^{4/9-ε}**: C₁ = 6.75 already
satisfies (23), for every A(4) ≤ 0.003992, A(3) ≤ 0.013598, R₀ ≤ 1.93656, C₀ ≤ 0.6614,
ε ≤ 10⁻⁴ and log P / log N ≥ 0.444. Table 1 prints 6.737 as the C₁ required. -/
theorem table1_K7_uncond {A3 A4 R0 C0 ε lp : ℝ} (hA30 : 0 ≤ A3) (hA3 : A3 ≤ 0.013598)
    (hA40 : 0 ≤ A4) (hA4 : A4 ≤ 0.003992) (hR0 : 0 ≤ R0) (hR : R0 ≤ 1.93656)
    (hC00 : 0 ≤ C0) (hC0 : C0 ≤ 0.6614) (he0 : 0 ≤ ε) (he : ε ≤ 1e-4) (hl : 0.444 ≤ lp)
    (hl1 : lp ≤ 1) :
    crit A4 A3 (C2p 6.75 ε R0 C0 lp) 0.7894009 4 3 < 1 := by
  have hC := C2p_le (C1 := 6.75) (C1m := 6.75) (εm := 1e-4) (R0m := 1.93656) (C0m := 0.6614)
    (lpm := 0.444) le_rfl he (by linarith) hR0 hR hC00 hC0 hl
  have hC2 : 0 ≤ C2p 6.75 ε R0 C0 lp := by
    unfold C2p
    have : 0 ≤ (1 - lp) * log 2 / 2 := by
      have := log_pos (show (1 : ℝ) < 2 by norm_num); nlinarith
    have h1 : 0 ≤ 1 / 2 * (6.75 + ε - 2) := by linarith
    have : 0 ≤ 1 / 2 * (6.75 + ε - 2) * R0 * C0 := mul_nonneg (mul_nonneg h1 hR0) hC00
    linarith
  have hmax : C2p 6.75 1e-4 1.93656 0.6614 0.444 ≤ 3.2348 := by
    unfold C2p; have := log_two_lt_d9; norm_num at this ⊢; linarith
  set C2 := C2p 6.75 ε R0 C0 lp
  have hCm : C2 ≤ 3.2348 := hC.trans hmax
  unfold crit
  have ha : 0 ≤ A4 + C2 * 0.7894009 ^ (2 * 4 - 2) := by positivity
  have hb : 0 ≤ A3 + C2 * 0.7894009 ^ (2 * 3 - 2) := by positivity
  rw [← sqrt_mul ha, sqrt_lt' (by norm_num)]
  norm_num
  have a1 : A4 + C2 * 0.7894009 ^ 6 ≤ 0.003992 + 3.2348 * 0.7894009 ^ 6 := by
    have := mul_le_mul_of_nonneg_right hCm (show (0 : ℝ) ≤ 0.7894009 ^ 6 by positivity)
    linarith
  have b1 : A3 + C2 * 0.7894009 ^ 4 ≤ 0.013598 + 3.2348 * 0.7894009 ^ 4 := by
    have := mul_le_mul_of_nonneg_right hCm (show (0 : ℝ) ≤ 0.7894009 ^ 4 by positivity)
    linarith
  have a0 : 0 ≤ A4 + C2 * 0.7894009 ^ 6 := by positivity
  have b0 : 0 ≤ A3 + C2 * 0.7894009 ^ 4 := by positivity
  have := mul_le_mul a1 b1 b0 (by positivity)
  have c : (0.003992 + 3.2348 * 0.7894009 ^ 6) * (0.013598 + 3.2348 * 0.7894009 ^ 4) < (1 : ℝ) := by
    norm_num
  norm_num at this ⊢
  linarith

#print axioms thm1_numeric
#print axioms thm1_numeric_twinC
#print axioms table1_K7_uncond

end LeanLab.Linnik.JT
