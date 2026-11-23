/-
AI wrote this Lean code, Claude, ROUTE BURST S76, burst-20261122, unit final_combination.
A proof of the LEAF `ProgressionEPS70.final_combination`, Ernvall-Hytonen and Palojarvi,
arXiv 2003.01925v4, pp. 45 to 46: the assembled bound of the proof of Theorem 1 is at most
the closed form of Theorem 1, for `x ≥ q ≥ 3`.
Method: write `L = log x`, `l = log q`, `y = x^(1/4) = exp (L/4)`, `√x = y^2`.
The `√x` terms match up to nonnegative slack, the `log log √x` term gains `log 2`,
and the rest reduces to `l α(L) + γ(L) ≤ l β(L,y) + δ(L,y)`, proved from
`exp u ≥ ∑_{k ≤ 8} u^k/k!`, by a coefficient check after a shift for large `L`
and by interval pieces for `1.098 ≤ L ≤ 7`. `R₁(q)` is bounded case by case.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.ProgressionEPS70

namespace LeanLab.BS2022GRH.ProgressionFinalS76
open Real LeanLab.BS2022GRH.ProgressionEPS70 ChenThresholdGRH
noncomputable section

/-- Taylor lower bound for `exp (L/4)` at a point `a ≤ L`. -/
theorem T8_le_exp (a L : ℝ) (ha : 0 ≤ a) (haL : a ≤ L) :
    1 + a/4 + (a/4)^2/2 + (a/4)^3/6 + (a/4)^4/24 + (a/4)^5/120 + (a/4)^6/720
      + (a/4)^7/5040 + (a/4)^8/40320 ≤ exp (L/4) := by
  have h := Real.sum_le_exp_of_nonneg (x := a/4) (by positivity) 9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  have h2 : exp (a/4) ≤ exp (L/4) := exp_le_exp.2 (by linarith)
  linarith

/-! Constant part `γ(L) ≤ δ(L, y)`, multiplied by `L^3`. -/

theorem d_big (L : ℝ) (hL : 7 ≤ L) :
    (0.5*L + 654.62)*L^3 ≤
      (5.718*L^3 + 284.48*L^2 + 2456.58*L + 11605.05) * exp (L/4) := by
  have hT := T8_le_exp L L (by linarith) le_rfl
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ L = 7 + t := ⟨L - 7, by linarith, by ring⟩
  have hc : 0 ≤ 5.718*(7+t)^3 + 284.48*(7+t)^2 + 2456.58*(7+t) + 11605.05 := by positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hT hc)
  have : 0 ≤ (5.718*(7+t)^3 + 284.48*(7+t)^2 + 2456.58*(7+t) + 11605.05) *
      (1 + (7+t)/4 + ((7+t)/4)^2/2 + ((7+t)/4)^3/6 + ((7+t)/4)^4/24 + ((7+t)/4)^5/120
        + ((7+t)/4)^6/720 + ((7+t)/4)^7/5040 + ((7+t)/4)^8/40320)
      - (0.5*(7+t) + 654.62)*(7+t)^3 := by
    ring_nf; positivity
  linarith

theorem d_piece (L a b : ℝ) (ha : 0 ≤ a) (haL : a ≤ L) (hLb : L ≤ b)
    (hnum : (0.5*b + 654.62)*b^3 ≤ (5.718*a^3 + 284.48*a^2 + 2456.58*a + 11605.05) *
      (1 + a/4 + (a/4)^2/2 + (a/4)^3/6 + (a/4)^4/24 + (a/4)^5/120 + (a/4)^6/720
        + (a/4)^7/5040 + (a/4)^8/40320)) :
    (0.5*L + 654.62)*L^3 ≤
      (5.718*L^3 + 284.48*L^2 + 2456.58*L + 11605.05) * exp (L/4) := by
  have hT := T8_le_exp a L ha haL
  have hL0 : 0 ≤ L := by linarith
  have h1 : (0.5*L + 654.62)*L^3 ≤ (0.5*b + 654.62)*b^3 := by
    gcongr; nlinarith
  have h2 : 5.718*a^3 + 284.48*a^2 + 2456.58*a + 11605.05
      ≤ 5.718*L^3 + 284.48*L^2 + 2456.58*L + 11605.05 := by gcongr
  have hTa : 0 ≤ 1 + a/4 + (a/4)^2/2 + (a/4)^3/6 + (a/4)^4/24 + (a/4)^5/120 + (a/4)^6/720
        + (a/4)^7/5040 + (a/4)^8/40320 := by positivity
  exact h1.trans (hnum.trans (mul_le_mul h2 hT hTa (by positivity)))

theorem d_all (L : ℝ) (hL : 1.098 ≤ L) :
    (0.5*L + 654.62)*L^3 ≤
      (5.718*L^3 + 284.48*L^2 + 2456.58*L + 11605.05) * exp (L/4) := by
  rcases le_or_gt 7 L with h | h
  · exact d_big L h
  rcases le_or_gt 6.85 L with h1 | h1
  · exact d_piece L 6.85 7 (by norm_num) h1 h.le (by norm_num)
  rcases le_or_gt 6.6 L with h2 | h2
  · exact d_piece L 6.6 6.85 (by norm_num) h2 h1.le (by norm_num)
  rcases le_or_gt 6.3 L with h3 | h3
  · exact d_piece L 6.3 6.6 (by norm_num) h3 h2.le (by norm_num)
  rcases le_or_gt 6 L with h4 | h4
  · exact d_piece L 6 6.3 (by norm_num) h4 h3.le (by norm_num)
  rcases le_or_gt 5.7 L with h5 | h5
  · exact d_piece L 5.7 6 (by norm_num) h5 h4.le (by norm_num)
  rcases le_or_gt 5.3 L with h6 | h6
  · exact d_piece L 5.3 5.7 (by norm_num) h6 h5.le (by norm_num)
  rcases le_or_gt 4.8 L with h7 | h7
  · exact d_piece L 4.8 5.3 (by norm_num) h7 h6.le (by norm_num)
  rcases le_or_gt 4.1 L with h8 | h8
  · exact d_piece L 4.1 4.8 (by norm_num) h8 h7.le (by norm_num)
  rcases le_or_gt 3 L with h9 | h9
  · exact d_piece L 3 4.1 (by norm_num) h9 h8.le (by norm_num)
  · exact d_piece L 1.098 3 (by norm_num) hL h9.le (by norm_num)

/-! Linear part `α(L) ≤ β(L, y)`, multiplied by `L^3`, three cases of `R₁`. -/

theorem b1_big (L : ℝ) (hL : 7 ≤ L) :
    (2.015*L + 18.84)*L^3 ≤
      (0.1275*L^3 + 11.364*L^2 + 272.74*L + 1841.85) * exp (L/4) := by
  have hT := T8_le_exp L L (by linarith) le_rfl
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ L = 7 + t := ⟨L - 7, by linarith, by ring⟩
  have hc : 0 ≤ 0.1275*(7+t)^3 + 11.364*(7+t)^2 + 272.74*(7+t) + 1841.85 := by positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hT hc)
  have : 0 ≤ (0.1275*(7+t)^3 + 11.364*(7+t)^2 + 272.74*(7+t) + 1841.85) *
      (1 + (7+t)/4 + ((7+t)/4)^2/2 + ((7+t)/4)^3/6 + ((7+t)/4)^4/24 + ((7+t)/4)^5/120
        + ((7+t)/4)^6/720 + ((7+t)/4)^7/5040 + ((7+t)/4)^8/40320)
      - (2.015*(7+t) + 18.84)*(7+t)^3 := by
    ring_nf; positivity
  linarith

theorem b1_piece (L a b : ℝ) (ha : 0 ≤ a) (haL : a ≤ L) (hLb : L ≤ b)
    (hnum : (2.015*b + 18.84)*b^3 ≤ (0.1275*a^3 + 11.364*a^2 + 272.74*a + 1841.85) *
      (1 + a/4 + (a/4)^2/2 + (a/4)^3/6 + (a/4)^4/24 + (a/4)^5/120 + (a/4)^6/720
        + (a/4)^7/5040 + (a/4)^8/40320)) :
    (2.015*L + 18.84)*L^3 ≤
      (0.1275*L^3 + 11.364*L^2 + 272.74*L + 1841.85) * exp (L/4) := by
  have hT := T8_le_exp a L ha haL
  have hL0 : 0 ≤ L := by linarith
  have h1 : (2.015*L + 18.84)*L^3 ≤ (2.015*b + 18.84)*b^3 := by
    gcongr; nlinarith
  have h2 : 0.1275*a^3 + 11.364*a^2 + 272.74*a + 1841.85
      ≤ 0.1275*L^3 + 11.364*L^2 + 272.74*L + 1841.85 := by gcongr
  have hTa : 0 ≤ 1 + a/4 + (a/4)^2/2 + (a/4)^3/6 + (a/4)^4/24 + (a/4)^5/120 + (a/4)^6/720
        + (a/4)^7/5040 + (a/4)^8/40320 := by positivity
  exact h1.trans (hnum.trans (mul_le_mul h2 hT hTa (by positivity)))

theorem b1_all (L : ℝ) (hL : 1.098 ≤ L) :
    (2.015*L + 18.84)*L^3 ≤
      (0.1275*L^3 + 11.364*L^2 + 272.74*L + 1841.85) * exp (L/4) := by
  rcases le_or_gt 7 L with h | h
  · exact b1_big L h
  rcases le_or_gt 6.8 L with h1 | h1
  · exact b1_piece L 6.8 7 (by norm_num) h1 h.le (by norm_num)
  rcases le_or_gt 4.6 L with h2 | h2
  · exact b1_piece L 4.6 6.8 (by norm_num) h2 h1.le (by norm_num)
  · exact b1_piece L 1.098 4.6 (by norm_num) hL h2.le (by norm_num)

theorem b2_all (L : ℝ) (hL : 12 ≤ L) :
    (4.696*L + 6.047)*L^3 ≤
      (0.1275*L^3 + 11.364*L^2 + 272.74*L + 1841.85) * exp (L/4) := by
  have hT := T8_le_exp L L (by linarith) le_rfl
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ L = 12 + t := ⟨L - 12, by linarith, by ring⟩
  have hc : 0 ≤ 0.1275*(12+t)^3 + 11.364*(12+t)^2 + 272.74*(12+t) + 1841.85 := by positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hT hc)
  have : 0 ≤ (0.1275*(12+t)^3 + 11.364*(12+t)^2 + 272.74*(12+t) + 1841.85) *
      (1 + (12+t)/4 + ((12+t)/4)^2/2 + ((12+t)/4)^3/6 + ((12+t)/4)^4/24 + ((12+t)/4)^5/120
        + ((12+t)/4)^6/720 + ((12+t)/4)^7/5040 + ((12+t)/4)^8/40320)
      - (4.696*(12+t) + 6.047)*(12+t)^3 := by
    ring_nf; positivity
  linarith

theorem b3_all (L : ℝ) (hL : 60 ≤ L) :
    (0.4285*L^2 + 2.885*L + 6.047)*L^3 ≤
      (0.1275*L^3 + 11.364*L^2 + 272.74*L + 1841.85) * exp (L/4) := by
  have hT := T8_le_exp L L (by linarith) le_rfl
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ L = 60 + t := ⟨L - 60, by linarith, by ring⟩
  have hc : 0 ≤ 0.1275*(60+t)^3 + 11.364*(60+t)^2 + 272.74*(60+t) + 1841.85 := by positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hT hc)
  have : 0 ≤ (0.1275*(60+t)^3 + 11.364*(60+t)^2 + 272.74*(60+t) + 1841.85) *
      (1 + (60+t)/4 + ((60+t)/4)^2/2 + ((60+t)/4)^3/6 + ((60+t)/4)^4/24 + ((60+t)/4)^5/120
        + ((60+t)/4)^6/720 + ((60+t)/4)^7/5040 + ((60+t)/4)^8/40320)
      - (0.4285*(60+t)^2 + 2.885*(60+t) + 6.047)*(60+t)^3 := by
    ring_nf; positivity
  linarith

/-- Dividing by `L^3`. -/
theorem div_form (L e P c0 c1 c2 c3 : ℝ) (hL : 0 < L)
    (h : P * L^3 ≤ (c0*L^3 + c1*L^2 + c2*L + c3) * e) :
    P ≤ c0*e + c1*e/L + c2*e/L^2 + c3*e/L^3 := by
  have : c0*e + c1*e/L + c2*e/L^2 + c3*e/L^3 = (c0*L^3 + c1*L^2 + c2*L + c3) * e / L^3 := by
    field_simp
  rw [this, le_div_iff₀ (by positivity)]; exact h

/-- The reduced inequality `A ≤ l β + δ` of the proof, with `R₁(q)` bounded in its three
cases of EP2022 Theorem 3 p. 3. -/
theorem key_ineq (q : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : (q : ℝ) ≤ x) :
    (2.015 * log q + 0.5) * (log x - 1) + 2.754 * log q + 0.534 + R1 q / log 2 + 4.886
        + 237.934 ≤
      log q * (0.1275 * x ^ ((1:ℝ)/4) + 11.364 * x ^ ((1:ℝ)/4) / log x
        + 272.74 * x ^ ((1:ℝ)/4) / log x ^ 2 + 1841.85 * x ^ ((1:ℝ)/4) / log x ^ 3)
      + (5.718 * x ^ ((1:ℝ)/4) + 284.48 * x ^ ((1:ℝ)/4) / log x
        + 2456.58 * x ^ ((1:ℝ)/4) / log x ^ 2 + 11605.05 * x ^ ((1:ℝ)/4) / log x ^ 3) := by
  have hq3 : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hx0 : 0 < x := by linarith
  have hl3 : 1.098 ≤ log (q:ℝ) := by
    have := log_three_gt_d9; have := log_le_log (by norm_num) hq3; linarith
  have hlL : log (q:ℝ) ≤ log x := log_le_log (by linarith) hx
  have hL : 1.098 ≤ log x := by linarith
  have hL0 : 0 < log x := by linarith
  have hyexp : x ^ ((1:ℝ)/4) = exp (log x / 4) := by
    rw [rpow_def_of_pos hx0]; congr 1; ring
  have hlog2 := log_two_gt_d9
  have hlog2pos : 0 < log 2 := by linarith
  have hR1div : ∀ R : ℝ, 0 ≤ R → R / log 2 ≤ 1.4427 * R := fun R hR => by
    rw [div_le_iff₀ hlog2pos]; nlinarith
  have hl0 : 0 ≤ log (q:ℝ) := by linarith
  have hd : 0.5 * log x + 654.62 ≤ 5.718 * x ^ ((1:ℝ)/4) + 284.48 * x ^ ((1:ℝ)/4) / log x
        + 2456.58 * x ^ ((1:ℝ)/4) / log x ^ 2 + 11605.05 * x ^ ((1:ℝ)/4) / log x ^ 3 :=
    div_form _ _ _ _ _ _ _ hL0 (by rw [hyexp]; exact d_all _ hL)
  have hll : log q * log q ≤ log q * log x := mul_le_mul_of_nonneg_left hlL hl0
  unfold R1
  split_ifs with c1 c2
  · have hsq : √(q:ℝ) ≤ 633 := by
      rw [show (633:ℝ) = √(633^2) by rw [sqrt_sq (by norm_num)]]
      exact sqrt_le_sqrt (by linarith)
    have hs0 : 0 ≤ √(q:ℝ) := sqrt_nonneg _
    have hRb : 0.014 * √(q:ℝ) * log q + 0.034 * √(q:ℝ) + 3.679 * log q + 263.886
        ≤ 12.541 * log q + 285.408 := by nlinarith [mul_le_mul_of_nonneg_right hsq hl0]
    have hR0 : 0 ≤ 0.014 * √(q:ℝ) * log q + 0.034 * √(q:ℝ) + 3.679 * log q + 263.886 := by
      positivity
    have hR := hR1div _ hR0
    have hb : 2.015 * log x + 18.84 ≤ 0.1275 * x ^ ((1:ℝ)/4) + 11.364 * x ^ ((1:ℝ)/4) / log x
        + 272.74 * x ^ ((1:ℝ)/4) / log x ^ 2 + 1841.85 * x ^ ((1:ℝ)/4) / log x ^ 3 :=
      div_form _ _ _ _ _ _ _ hL0 (by rw [hyexp]; exact b1_all _ hL)
    have hb' := mul_le_mul_of_nonneg_left hb hl0
    nlinarith
  · have h4 : (400000:ℝ) ≤ q := by push_neg at c1; norm_num at c1 ⊢; linarith
    have he : exp 12 ≤ 400000 := by
      have : exp 12 = exp 1 ^ 12 := by rw [← exp_nat_mul]; norm_num
      rw [this]
      exact (pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 12).trans (by norm_num)
    have hl12 : 12 ≤ log (q:ℝ) := by
      have := log_le_log (exp_pos 12) (he.trans h4); rwa [log_exp] at this
    have hR0 : 0 ≤ 1.858 * log (q:ℝ) ^ 2 + 3.679 * log q + 104.626 := by positivity
    have hR := hR1div _ hR0
    have hb : 4.696 * log x + 6.047 ≤ 0.1275 * x ^ ((1:ℝ)/4) + 11.364 * x ^ ((1:ℝ)/4) / log x
        + 272.74 * x ^ ((1:ℝ)/4) / log x ^ 2 + 1841.85 * x ^ ((1:ℝ)/4) / log x ^ 3 :=
      div_form _ _ _ _ _ _ _ hL0 (by rw [hyexp]; exact b2_all _ (by linarith))
    have hb' := mul_le_mul_of_nonneg_left hb hl0
    nlinarith
  · have h4 : (10 ^ 29:ℝ) ≤ q := by push_neg at c2; linarith
    have he : exp 60 ≤ 10 ^ 29 := by
      have : exp 60 = exp 1 ^ 60 := by rw [← exp_nat_mul]; norm_num
      rw [this]
      exact (pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 60).trans (by norm_num)
    have hl60 : 60 ≤ log (q:ℝ) := by
      have := log_le_log (exp_pos 60) (he.trans h4); rwa [log_exp] at this
    have hll0 : 0 ≤ log (log (q:ℝ)) := log_nonneg (by linarith)
    have hllL : log (log (q:ℝ)) ≤ log x := by
      have := log_le_sub_one_of_pos (show 0 < log (q:ℝ) by linarith); linarith
    have hc : (0.297 * log (log (q:ℝ)) + 0.603) * log q ^ 2
        ≤ (0.297 * log x + 0.603) * (log q * log x) := by
      rw [sq]
      exact mul_le_mul (by linarith) hll (by positivity) (by positivity)
    have hR0 : 0 ≤ (0.297 * log (log (q:ℝ)) + 0.603) * log q ^ 2 + 3.679 * log q + 104.626 := by
      positivity
    have hR := hR1div _ hR0
    have hb : 0.4285 * log x ^ 2 + 2.885 * log x + 6.047 ≤ 0.1275 * x ^ ((1:ℝ)/4)
        + 11.364 * x ^ ((1:ℝ)/4) / log x
        + 272.74 * x ^ ((1:ℝ)/4) / log x ^ 2 + 1841.85 * x ^ ((1:ℝ)/4) / log x ^ 3 :=
      div_form _ _ _ _ _ _ _ hL0 (by rw [hyexp]; exact b3_all _ (by linarith))
    have hb' := mul_le_mul_of_nonneg_left hb hl0
    nlinarith

/-- PROVED: EP2022 pp. 45 to 46, the statement of the LEAF
`ProgressionEPS70.final_combination`, copied verbatim. -/
theorem final_combination_S76 (q : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : (q : ℝ) ≤ x) :
    lemma31RHS q x + 1.4262 * √x / log x + display52RHS x
        + |-liPV 2 + 2 / log 2| / (q.totient : ℝ) ≤
      (1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π)) * √x * log x
      + (0.184 * log q + 8.396) * √x
      + (6.05 * log q + 158.745) * √x / log x
      + (5.048 * log q ^ 2 + 152.085 * log q + 1731.270) * √x / log x ^ 2
      + (0.184 * log q + 8.250) * x ^ ((1 : ℝ) / 4) * log (log x)
      + (5.254 * log q ^ 2 + 121.765 * log q + 939.260) * x ^ ((1 : ℝ) / 4)
      + (80.768 * log q ^ 2 + 1753.168 * log q + 11605.056) * √x / log x ^ 3
      - 237.934 := by
  have key := key_ineq q x hq hx
  have hq3 : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hx0 : 0 < x := by linarith
  have hl3 : 1.098 ≤ log (q:ℝ) := by
    have := log_three_gt_d9; have := log_le_log (by norm_num) hq3; linarith
  have hlL : log (q:ℝ) ≤ log x := log_le_log (by linarith) hx
  have hL0 : 0 < log x := by linarith
  have hl0 : 0 ≤ log (q:ℝ) := by linarith
  have hlog2 := log_two_gt_d9
  have hlog2pos : 0 < log 2 := by linarith
  have hs : √x = x ^ ((1:ℝ)/4) * x ^ ((1:ℝ)/4) := by
    rw [← rpow_add hx0, sqrt_eq_rpow]; norm_num
  have hy0 : 0 < x ^ ((1:ℝ)/4) := rpow_pos_of_pos hx0 _
  have hg : log (log x) ≤ log x - 1 := log_le_sub_one_of_pos hL0
  have hphi : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  obtain ⟨hli0, hli2⟩ := liPV_two_le
  have hinv : 2 / log 2 ≤ 2.8854 := by rw [div_le_iff₀ hlog2pos]; linarith
  have hinv0 : 0 < 2 / log 2 := div_pos two_pos hlog2pos
  have hC : |-liPV 2 + 2 / log 2| / (q.totient : ℝ) ≤ 4.886 := by
    have h1 : |-liPV 2 + 2 / log 2| ≤ 4.886 := by
      rw [abs_le]; constructor <;> linarith
    exact (div_le_self (abs_nonneg _) hphi).trans h1
  have hd52 : 1.4262 * x ^ ((1:ℝ)/4) / log 2 ≤ 2.058 * x ^ ((1:ℝ)/4) := by
    rw [div_le_iff₀ hlog2pos]; nlinarith
  unfold lemma31RHS display52RHS
  rw [log_sqrt hx0.le, log_div hL0.ne' two_ne_zero, hs]
  set L := log x with hLdef
  set l := log (q:ℝ) with hldef
  set y := x ^ ((1:ℝ)/4) with hydef
  have hF1 : 0.1275 * l * y + 5.718 * y ≤ (0.184 * l + 8.25) * y * log 2 := by
    nlinarith [mul_nonneg hl0 hy0.le]
  have hF2 : 0 ≤ (l ^ 2 - 1.098 * l) * (y / L ^ 2) :=
    mul_nonneg (by nlinarith) (by positivity)
  have hF3 : 0 ≤ (l ^ 2 - 1.098 * l) * (y / L ^ 3) :=
    mul_nonneg (by nlinarith) (by positivity)
  have hF4 : 0 ≤ y * y / L := by positivity
  have hF5 : 0 ≤ y * y / L ^ 2 := by positivity
  have hF6 : (2.015 * l + 0.5) * log L ≤ (2.015 * l + 0.5) * (L - 1) :=
    mul_le_mul_of_nonneg_left hg (by linarith)
  have hF7 : 0 ≤ l * (y / L ^ 3) := by positivity
  have hF8 : 0 ≤ y / L ^ 3 := by positivity
  have hF9 : 0 ≤ y / L := by positivity
  have hF10 : 0 ≤ l * (y / L ^ 2) := by positivity
  have hF11 : 0 ≤ y / L ^ 2 := by positivity
  have e1 : (80.768 * l ^ 2 + 1753.168 * l + 11605.056) * y / L ^ 3 * (y - 1)
      = (80.768 * l ^ 2 + 1753.168 * l + 11605.056) * (y * y) / L ^ 3
        - (80.768 * l ^ 2 + 1753.168 * l + 11605.056) * y / L ^ 3 := by ring
  rw [e1]
  linear_combination key + hF1 + 10.096 * hF2 + 80.768 * hF3 + hF6 + hC + hd52
    + (1/1250) * hF4 + (1/2500) * hF5 + (21/2500) * hF9 + (213/62500) * hF10
    + (7/1250) * hF11 + (79/62500) * hF7 + (3/500) * hF8

#print axioms final_combination_S76

end

end LeanLab.BS2022GRH.ProgressionFinalS76
