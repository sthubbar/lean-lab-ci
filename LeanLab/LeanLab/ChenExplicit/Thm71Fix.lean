/-
AI-written Lean code, Claude, 2026-10-18, run 20261018T1203Z-2488, unit U-0941.
P0010 T. Yamada, Explicit Chen's theorem, arXiv 1511.03409v2, Section 7, (127) to (129) and
Theorem 7.1, and Section 8, (132), read in Claude in Chrome on ar5iv.

(128) bounds S(B) by `c₂(1+ε) N U⁽¹⁾ / log N · (4e^γ / log N + 845.33255 / log^{3/2} N)`.
Taking `1 / log N` out of the bracket gives `845.33255 / log^{1/2} N`, and with (47)
`845.33255 · 58/57 ≤ 860.16295 / log^{1/2} N`. Theorem 7.1, (98), and (129) print
`860.16295 / log^{3/2} N`, which the proof does not give; Section 8's (132) uses
`430.0815 = 860.163 / 2` over `log^{1/2} N`, the version the proof does give.
* `Thm71W`: Theorem 7.1 with `log^{1/2} N`, what (128) and (47) actually give. CITED.
* PROVED `eq129_not_from_128`: the (128) term exceeds the (129) term for every `log N ≥ 2`.
* PROVED `yamada_of_section8_C6W`: Section 8 with `Thm71W` in place of the printed `Thm71`;
  the proof is `yamada_of_section8_C6` with `s₃ = s`.
* `yamada_of_section8_corrW`: Theorem 1.1 CONDITIONAL ON (48), Theorems 5.1, 7.1 as the proof
  gives it, `c₂` bound, and Theorem 6.1 with the corrected `C6corr` of Eq93Exact.lean.
Chen's theorem is known; binary Goldbach is OPEN.
-/
import LeanLab.ChenExplicit.Eq93Exact

open Finset Real

noncomputable section
namespace LeanLab.ChenExplicit.Yamada

open LeanLab.ChenExplicit

/-- Theorem 7.1 with `860.16295 / log^{1/2} N`, as (128) and (47) give it. CITED. -/
def Thm71W : Prop :=
  ∀ N : ℕ, Even N → exp (exp 36) < N → ∀ ε : ℝ, 0 < ε → ε < 1 / 100 →
    (SB N (zN N) (yN N) : ℝ) ≤
      c2 * (1 + ε) * N * U N / log N ^ 2 *
          (4 * exp eulerMascheroniConstant * (1 + eps0 N) + 86016295 / 100000 / √(log N)) +
        exp (-138) * N / (ε * log N ^ 3)

/-- The printed Theorem 7.1 implies the weak form. -/
theorem thm71W_of_thm71 (h : Thm71) : Thm71W := by
  intro N hE hN ε h0 h1
  refine (h N hE hN ε h0 h1).trans ?_
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  have hL : exp 36 < log N := (Real.lt_log_iff_exp_lt hpos).mpr hN
  have hL1 : 1 ≤ log N := by have := add_one_le_exp 36; linarith
  have hsq : 0 < √(log N) := Real.sqrt_pos.mpr (by linarith)
  have hU : 0 < U N := by have := U_ge N; linarith
  have hc : 0 ≤ c2 * (1 + ε) * N * U N / log N ^ 2 := by
    have := c2_pos; positivity
  have : 86016295 / 100000 / (log N * √(log N)) ≤ 86016295 / 100000 / √(log N) := by
    apply div_le_div_of_nonneg_left (by norm_num) hsq
    exact le_mul_of_one_le_left hsq.le hL1
  gcongr

/-- (128) to (129) fails. With `X = c₂(1+ε) N U⁽¹⁾ > 0` and `L = log N`, the second term of
(128), `X · 845.33255 / (L · L^{3/2})`, exceeds `X · 860.16295 / (L² · L^{3/2})`, the second term
of (129) even with `U⁽¹⁾` for `U (1 + ε₀)`, for every `L ≥ 2`. -/
theorem eq129_not_from_128 (X L : ℝ) (hX : 0 < X) (hL : 2 ≤ L) :
    X * (86016295 / 100000) / (L ^ 2 * (L * √L)) <
      X * (84533255 / 100000) / (L * (L * √L)) := by
  have hs : 0 < √L := Real.sqrt_pos.mpr (by linarith)
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have : 0 < X * (L * (L * √L)) := by positivity
  nlinarith [mul_nonneg this.le (sub_nonneg.mpr hL)]

theorem yamada_of_section8_C6W (C6 : ℝ) (hC6 : C6 ≤ 2500) (h48 : Thm48) (h51 : Thm51)
    (h61 : Thm61C C6) (h71 : Thm71W) (hc2 : C2Bound) : Yamada := by
  intro N hEven hN
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  set L := Real.log N with hLdef
  have hL : exp 36 < L := (Real.lt_log_iff_exp_lt hpos).mpr hN
  have hL6 := exp_32_7_gt
  have h36 : exp (327 / 10) ≤ exp 36 := exp_le_exp.mpr (by norm_num)
  have hL0 : 0 < L := by linarith
  have hNe : (N : ℝ) = exp L := (exp_log hpos).symm
  have hz : zN N = exp (L / 8) := by
    simp only [zN]; rw [rpow_def_of_pos hpos, ← hLdef]; ring_nf
  have hy : yN N = exp (L / 3) := by
    simp only [yN]; rw [rpow_def_of_pos hpos, ← hLdef]; ring_nf
  have hz2 : 2 ≤ zN N := by
    rw [hz]; have := add_one_le_exp (L / 8); linarith
  have hy0 : 0 < yN N := by rw [hy]; exact exp_pos _
  have hy3 : (N : ℝ) ≤ yN N ^ 3 := by
    rw [hy, ← exp_nat_mul, hNe]; apply exp_le_exp.mpr; push_cast; linarith
  have hchen := chen_inequality N (zN N) (yN N) hz2 hy0 hy3
  -- the quantities
  set g := exp eulerMascheroniConstant with hg
  set e0 := eps0 N with he0
  set A : ℝ := (Acard N : ℝ) with hA
  have hU := U_ge N
  have hU0 : 0 < U N := by linarith
  set K := U N * N / L ^ 2 with hK
  set M := U N * A / L with hM
  have hA48 := h48 N hEven hN
  have hKM : K < M := by
    rw [hK, hM]
    have : (N : ℝ) / L ^ 2 < A / L := by
      rw [show (N : ℝ) / L ^ 2 = (N / L) / L by ring]
      exact div_lt_div_of_pos_right hA48 hL0
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_lt_mul_of_pos_left this hU0
  have hK0 : 0 < K := by rw [hK]; positivity
  have hM0 : 0 < M := lt_trans hK0 hKM
  -- e₀ ≤ 1/57
  have he00 : 0 ≤ e0 := by rw [he0, eps0]; positivity
  have he01 : e0 ≤ 1 / 57 := by
    rw [he0, eps0]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (le_max_left _ _)
  -- s = 1/√L
  have hsq : exp 18 < √L := by
    have e : √(exp 36) = exp 18 := by
      rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (exp_pos _), ← exp_add]; norm_num
    rw [← e]
    exact Real.sqrt_lt_sqrt (exp_pos _).le hL
  have h18 := exp_18_gt
  have hsq0 : 0 < √L := by linarith
  set s := 1 / √L with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 2 / 10 ^ 8 := by
    rw [hs, div_le_div_iff₀ hsq0 (by norm_num)]; linarith
  have hL1 : 1 ≤ L := by
    have := add_one_le_exp 36; linarith
  -- ε = e^{-50}
  set ε := exp (-50) with hε
  have hε0 : 0 < ε := exp_pos _
  have h50 := exp_50_gt
  have hε1 : ε ≤ 1 / 10 ^ 20 := by
    rw [hε, exp_neg, inv_eq_one_div, div_le_div_iff₀ (exp_pos _) (by norm_num)]; linarith
  have hεs : ε < 1 / 100 := by linarith
  have hc20 := c2_pos
  set c := c2 * (1 + ε) with hc
  have hc0 : 0 ≤ c := by positivity
  have hcb : c ≤ 3630900001 / 10000000000 := by
    rw [hc]; unfold C2Bound at hc2
    nlinarith
  -- the sieve bounds
  have h1 := h51 N hEven hN
  have h2 := h61 N hEven hN
  have h3 := h71 N hEven hN ε hε0 hεs
  set P := 4 * g * (1 + e0) + 86016295 / 100000 / √L with hP
  have hg0 : 0 < g := exp_pos _
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have h3' : (SB N (zN N) (yN N) : ℝ) ≤ c * M * P + exp (-138) * N / (ε * L ^ 3) := by
    have e : c2 * (1 + ε) * N * U N / L ^ 2 * P = c * K * P := by rw [hc, hK]; ring
    rw [← hLdef] at h3
    have : c * K * P ≤ c * M * P := by
      apply mul_le_mul_of_nonneg_right _ hP0
      exact mul_le_mul_of_nonneg_left hKM.le hc0
    linarith
  -- the small error terms
  have hE1 : 2 * (N : ℝ) / zN N + yN N ≤ 1 / 10 ^ 12 * K := by
    rw [hK]; exact err1 N hpos hL hU
  have hE2 : exp (-138) * N / (ε * L ^ 3) ≤ 1 / 10 ^ 12 * K := by
    rw [hK, hε]; exact err2 N hpos hL1 hU
  -- Theorem 7.1 as the proof gives it: s₃ = s
  have hnum := section8_numeric C6 hC6 g c e0 s s (by rw [hg]; exact exp_gamma_gt) hc0
    hcb he00 he01 hs0 hs1 hs0 le_rfl
  -- assemble
  have hSA : M * (4 * g * log 3 - 5198 / 10000 * e0 - 7677471 / 10000 * s) <
      (SA N (zN N) : ℝ) := by
    have : 7677471 / 10000 / √L = 7677471 / 10000 * s := by rw [hs]; ring
    rw [hM]; rw [← hLdef, this] at h1; linarith
  have hQ : (sumSAq N (zN N) (yN N) : ℝ) <
      M * (4 * g * log 6 * (1 + e0) + C6 * s) := by
    have : C6 / √L = C6 * s := by rw [hs]; ring
    rw [hM]; rw [← hLdef, this] at h2; linarith
  have hPe : P = 4 * g * (1 + e0) + 86016295 / 100000 * s := by rw [hP, hs]; ring
  have hfin : (704 / 100000 : ℝ) * M ≤
      M * (4 * g * log 3 - 5198 / 10000 * e0 - 7677471 / 10000 * s) -
        M * (4 * g * log 6 * (1 + e0) + C6 * s) / 2 - c * M * P / 2 := by
    rw [hPe]
    have := mul_le_mul_of_nonneg_left hnum hM0.le
    linarith
  have hgoal : (7 / 1000 : ℝ) * U N * N / Real.log N ^ 2 = 7 / 1000 * K := by
    rw [hK]; ring
  rw [hgoal]
  linarith


/-- **Yamada Theorem 1.1 with both corrections.** CONDITIONAL ON (48), Theorem 5.1, Theorem 7.1
in the form its proof gives, `c₂ < 0.36309`, which C2Bound.lean proves, and Theorem 6.1 with
the corrected constant `C6corr ≈ 2106.5` from Eq93Exact.lean. -/
theorem yamada_of_section8_corrW (h48 : Thm48) (h51 : Thm51) (h61 : Thm61C C6corr)
    (h71 : Thm71W) (hc2 : C2Bound) : Yamada :=
  yamada_of_section8_C6W C6corr (C6corr_le.trans (by norm_num)) h48 h51 h61 h71 hc2

end LeanLab.ChenExplicit.Yamada
