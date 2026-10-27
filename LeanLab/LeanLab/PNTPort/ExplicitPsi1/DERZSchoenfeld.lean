import LeanLab.DERZ1997.LemmaPsi
import LeanLab.DERZ1997.MainHSW

/-!
# P0011 DERZ 1997 with the printed constant `1.615 · 10^12`, without Schoenfeld

I-5260, unit U-6707, CLOUD 20261020T1816Z-cloud48, track T2. AI wrote this file. Known
mathematics: Schoenfeld's method of one unsmoothing with a fixed smoothing length.

P0011's intermediate lemma cites Schoenfeld 1976 (6.1), in the lab as `Schoenfeld61` for `θ`
and `SchoenfeldPsi61` for `ψ`, for all `x ≥ 2.3 · 10^9`. Both are used only through the uniform
bound `807195 · 10^6` on `10^11 ≤ x ≤ 10^20`, in `schoenfeld61_uniform` and in the `hu` step of
`derz_lemma_of_schoenfeldPsi`. Here that uniform bound is proved under RH, CONDITIONAL ON the
Hasanalizade-Shen-Wong counts `HSWN70`, `HSWHead14` and on `Ordinates14`, all for the true
ordinates `gZ`, from `psi_upper_gen` and `psi_lower_gen` with the fixed choice
`h = 9 · 10^10`, `T = 2 · 10^9`:
* `psi_uniform_hsw`: `|ψ(x) - x| ≤ 76 · 10^10` on `[10^11, 10^20]`;
* `theta_uniform_hsw`: `|θ(x) - x| ≤ 772 · 10^9` there, adding `ψ - θ ≤ 1.2 √x`;
* `schoenfeld61_uniform_hsw`, `psi61_uniform_hsw`: the `807195 · 10^6` bounds DERZ consumes;
* the headlines `derz_lemma_of_schoenfeld61_hsw`, `derz_lemma_of_hsw`,
  `derz_lemma_of_schoenfeldPsi_hsw`, `derz_main_of_psi_hsw`, `derz_main_of_lemma_hsw`, each the
  original with the Schoenfeld input replaced by RH or GRH and the three zero-count inputs;
  the main theorems remain CONDITIONAL ON Zinoviev's `10^20` bound and the `10^13` even check.
`cor1_uniform_hsw` of MainHSW.lean already covers `cor1_uniform`; `derz_lemma_of_cor1_hsw` here
restates `derz_lemma_of_cor1`.

Not covered: KanieckiGap/Lemma6.lean and Lemma6Gap.lean take the full `Schoenfeld61` Prop for
all `x ≥ 2.3 · 10^9`; nothing here replaces that.

Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/

namespace LeanLab.DERZ1997
open Real Chebyshev
open LeanLab.Dudek2014.Section22
open LeanLab.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14 S1 S2)
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ psi_upper_gen psi_lower_gen psiF_eq_psi
  psi_sub_theta_large rpow_three_halves)

/-! ### The zero sums at `T = 2 · 10^9` -/

lemma log_T_le : Real.log (2 * 10 ^ 9) ≤ 21.42 := by
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have := log_ten_lt'
  have := Real.log_two_lt_d9
  push_cast; linarith

lemma S1_T_le : S1 (2 * 10 ^ 9) ≤ 63 := by
  unfold S1
  have a := log_T_le
  have b := LeanLab.ChirreHagen2025.Lemma26H.c_lower
  have hge : Real.log (2 * π) ≤ Real.log (2 * 10 ^ 9) :=
    Real.log_le_log (by positivity) (by nlinarith [Real.pi_le_four])
  have hpi := Real.pi_gt_d2
  generalize Real.log (2 * 10 ^ 9) = L at *
  generalize Real.log (2 * π) = M at *
  have h1 : (L - M) ^ 2 ≤ 19.62 ^ 2 := by nlinarith
  have h2 : (L - M) ^ 2 / (2 * π) ≤ 19.62 ^ 2 / (2 * 3.14) :=
    div_le_div₀ (by norm_num) h1 (by norm_num) (by linarith)
  have h3 : (19.62 : ℝ) ^ 2 / (2 * 3.14) ≤ 61.4 := by norm_num
  linarith

lemma S2_T_le : S2 (2 * 10 ^ 9) ≤ 3.42e-9 := by
  unfold S2
  have a := log_T_le
  have hpi := Real.pi_gt_d2
  have l0 : 0 ≤ Real.log ((2 : ℝ) * 10 ^ 9) := Real.log_nonneg (by norm_num)
  generalize Real.log (2 * 10 ^ 9) = L at *
  have t1 : L / (π * (2 * 10 ^ 9)) ≤ 3.42e-9 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have t2 : (1.004 * L + 41.26 - 0.25 * (2 * 10 ^ 9)) / ((2 : ℝ) * 10 ^ 9) ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num; linarith) (by positivity)
  generalize L / (π * (2 * 10 ^ 9)) = A at *
  generalize (1.004 * L + 41.26 - 0.25 * (2 * 10 ^ 9)) / ((2 : ℝ) * 10 ^ 9) ^ 2 = B at *
  linarith

/-! ### The uniform bounds on `[10^11, 10^20]` -/

/-- `y^{1/2} ≤ K` and `y^{3/2} ≤ Y K` for `0 ≤ y ≤ Y ≤ K²`, `0 ≤ K`. -/
lemma halves_le {y Y K : ℝ} (hy : 0 ≤ y) (hY : y ≤ Y) (hK : 0 ≤ K) (hYK : Y ≤ K ^ 2) :
    0 ≤ y ^ (1 / 2 : ℝ) ∧ y ^ (1 / 2 : ℝ) ≤ K ∧ 0 ≤ y ^ (3 / 2 : ℝ) ∧
      y ^ (3 / 2 : ℝ) ≤ Y * K := by
  have h0 : 0 ≤ y ^ (1 / 2 : ℝ) := Real.rpow_nonneg hy _
  have h1 : y ^ (1 / 2 : ℝ) ≤ K := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left hK]; linarith
  refine ⟨h0, h1, Real.rpow_nonneg hy _, ?_⟩
  rw [rpow_three_halves hy]
  exact mul_le_mul hY h1 h0 (by linarith)

/-- **`|ψ(x) - x| ≤ 76 · 10^10` for `10^11 ≤ x ≤ 10^20`**, under RH, CONDITIONAL ON `HSWN70`,
`HSWHead14`, `Ordinates14`; `h = 9 · 10^10`, `T = 2 · 10^9`. -/
theorem psi_uniform_hsw (hRH : RiemannHypothesis) (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (hH : HSWHead14 gZ) (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    {x : ℝ} (h1 : 10 ^ 11 ≤ x) (h2 : x ≤ 10 ^ 20) : |ψ x - x| ≤ 76 * 10 ^ 10 := by
  have U := psi_upper_gen hRH hN hH h14 (x := x) (h := 9 * 10 ^ 10) (T := 2 * 10 ^ 9)
    (by linarith) (by norm_num) (by norm_num)
  have W := psi_lower_gen hRH hN hH h14 (x := x) (h := 9 * 10 ^ 10) (T := 2 * 10 ^ 9)
    (by linarith) (by norm_num) (by norm_num)
  rw [psiF_eq_psi] at U W
  have hS1 := S1_T_le
  have hS2 := S2_T_le
  have hc1 := LeanLab.ChirreHagen2025.Lemma26H.c_lower
  have hc2 := LeanLab.ChirreHagen2025.Lemma26H.c_upper
  obtain ⟨a0, a1, b0, b1⟩ := halves_le (y := x + 9 * 10 ^ 10) (Y := 10 ^ 20 + 9 * 10 ^ 10)
    (K := 10000001000) (by linarith) (by linarith) (by norm_num) (by norm_num)
  obtain ⟨c0, c1, d0, d1⟩ := halves_le (y := x) (Y := 10 ^ 20 + 9 * 10 ^ 10)
    (K := 10000001000) (by linarith) (by linarith) (by norm_num) (by norm_num)
  -- the S₁ terms
  have p1 : (x + 9 * 10 ^ 10) ^ (1 / 2 : ℝ) * S1 (2 * 10 ^ 9) ≤ 10000001000 * 63 :=
    (mul_le_mul_of_nonneg_left hS1 a0).trans (mul_le_mul_of_nonneg_right a1 (by norm_num))
  have q1 : x ^ (1 / 2 : ℝ) * S1 (2 * 10 ^ 9) ≤ 10000001000 * 63 :=
    (mul_le_mul_of_nonneg_left hS1 c0).trans (mul_le_mul_of_nonneg_right c1 (by norm_num))
  -- the S₂ terms
  have p2 : 2 * (x + 9 * 10 ^ 10) ^ (3 / 2 : ℝ) * S2 (2 * 10 ^ 9) / (9 * 10 ^ 10) ≤
      2 * ((10 ^ 20 + 9 * 10 ^ 10) * 10000001000) * 3.42e-9 / (9 * 10 ^ 10) := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    have e1 := mul_le_mul_of_nonneg_left hS2 b0
    have e2 := mul_le_mul_of_nonneg_right b1 (by norm_num : (0 : ℝ) ≤ 3.42e-9)
    nlinarith
  have q2 : 2 * x ^ (3 / 2 : ℝ) * S2 (2 * 10 ^ 9) / (9 * 10 ^ 10) ≤
      2 * ((10 ^ 20 + 9 * 10 ^ 10) * 10000001000) * 3.42e-9 / (9 * 10 ^ 10) := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    have e1 := mul_le_mul_of_nonneg_left hS2 d0
    have e2 := mul_le_mul_of_nonneg_right d1 (by norm_num : (0 : ℝ) ≤ 3.42e-9)
    nlinarith
  have num : (9 * 10 ^ 10 : ℝ) / 2 + 2 + 4.786 / (9 * 10 ^ 10) + 10000001000 * 63 +
      2 * ((10 ^ 20 + 9 * 10 ^ 10) * 10000001000) * 3.42e-9 / (9 * 10 ^ 10) ≤ 76 * 10 ^ 10 := by
    norm_num
  generalize 2 * (x + 9 * 10 ^ 10) ^ (3 / 2 : ℝ) * S2 (2 * 10 ^ 9) / (9 * 10 ^ 10) = D at *
  generalize 2 * x ^ (3 / 2 : ℝ) * S2 (2 * 10 ^ 9) / (9 * 10 ^ 10) = E at *
  generalize (x + 9 * 10 ^ 10) ^ (1 / 2 : ℝ) * S1 (2 * 10 ^ 9) = C at *
  generalize x ^ (1 / 2 : ℝ) * S1 (2 * 10 ^ 9) = F at *
  have hB : (0 : ℝ) ≤ 4.786 / (9 * 10 ^ 10) := by norm_num
  generalize (4.786 : ℝ) / (9 * 10 ^ 10) = B at *
  generalize Real.log (2 * π) = M at *
  rw [abs_le]; constructor <;> linarith

/-- **`|θ(x) - x| ≤ 772 · 10^9` for `10^11 ≤ x ≤ 10^20`**, under RH, CONDITIONAL ON `HSWN70`,
`HSWHead14`, `Ordinates14`. -/
theorem theta_uniform_hsw (hRH : RiemannHypothesis) (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (hH : HSWHead14 gZ) (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    {x : ℝ} (h1 : 10 ^ 11 ≤ x) (h2 : x ≤ 10 ^ 20) : |θ x - x| ≤ 772 * 10 ^ 9 := by
  have a := psi_uniform_hsw hRH hN hH h14 h1 h2
  have b := psi_sub_theta_large h1
  have c := Chebyshev.theta_le_psi x
  have s := sqrt_le_1e10 h2
  rw [abs_le] at a ⊢; constructor <;> linarith [a.1, a.2]

/-- `schoenfeld61_uniform` from RH and the zero counts instead of `Schoenfeld61`. -/
theorem schoenfeld61_uniform_hsw (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) (hH : HSWHead14 gZ)
    (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    (x : ℝ) (h1 : 10 ^ 11 ≤ x) (h2 : x ≤ 10 ^ 20) :
    |θ x - x| ≤ 807195 * 10 ^ 6 :=
  (theta_uniform_hsw hRH hN hH h14 h1 h2).trans (by norm_num)

/-- The `hu` step of `derz_lemma_of_schoenfeldPsi` from RH and the zero counts. -/
theorem psi61_uniform_hsw (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) (hH : HSWHead14 gZ)
    (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ) :
    ∀ x : ℝ, 10 ^ 11 ≤ x → x ≤ 10 ^ 20 → |ψ x - x| ≤ 807195 * 10 ^ 6 :=
  fun _ h1 h2 => (psi_uniform_hsw hRH hN hH h14 h1 h2).trans (by norm_num)

/-! ### The θ-form headlines -/

/-- **P0011 intermediate lemma with the printed constant `1.615 · 10^12`**, under RH,
CONDITIONAL ON `HSWN70`, `HSWHead14`, `Ordinates14`; no Schoenfeld input. -/
theorem derz_lemma_of_schoenfeld61_hsw (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) (hH : HSWHead14 gZ)
    (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ) :
    ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 → ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 1615 * 10 ^ 9 :=
  gap_of_theta (10 ^ 11) (807195 * 10 ^ 6) (1615 * 10 ^ 9) le_rfl
    (fun x h1 h2 => schoenfeld61_uniform_hsw hRH hN hH h14 x h1 h2)
    (by have := log_1e20_lt; norm_num; linarith) (by norm_num)

/-- `derz_lemma_of` with the three zero-count inputs in place of `GRH → Schoenfeld61`. This is
the statement of the cited `derz_lemma`, CONDITIONAL ON `HSWN70`, `HSWHead14`, `Ordinates14`. -/
theorem derz_lemma_of_hsw (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) (hH : HSWHead14 gZ)
    (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ) :
    GRH → ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 →
      ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 1615 * 10 ^ 9 :=
  fun hG => derz_lemma_of_schoenfeld61_hsw (rh_of_GRH hG) hN hH h14

/-- `derz_lemma_of_cor1` under RH and the zero counts, no `SchoenfeldCor1`. -/
theorem derz_lemma_of_cor1_hsw (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) (hH : HSWHead14 gZ)
    (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ) :
    ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 → ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 169 * 10 ^ 10 :=
  gap_of_theta (10 ^ 11) (843842 * 10 ^ 6) (169 * 10 ^ 10) le_rfl
    (fun x h1 h2 => cor1_uniform_hsw hRH hN hH h14 x h1 h2)
    (by have := log_1e20_lt; norm_num; linarith) (by norm_num)

/-- **P0011 main theorem through the printed lemma**: `derz_main` with `derz_lemma` replaced by
`derz_lemma_of_hsw`. GRH implies ternary Goldbach, CONDITIONAL ON Zinoviev's `10^20` bound, the
`10^13` even check and `HSWN70`, `HSWHead14`, `Ordinates14`. -/
theorem derz_main_of_lemma_hsw
    (hZ : GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → IsTernarySum n)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) (hH : HSWHead14 gZ)
    (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ) (hD : EvenGoldbachUpTo (10 ^ 13)) :
    GRH → TernaryGoldbach :=
  derz_main_of hZ (derz_lemma_of_hsw hN hH h14) hD

/-! ### The ψ-form headlines -/

/-- `derz_lemma_of_schoenfeldPsi` for any uniform ψ bound `807195 · 10^6` on `[10^11, 10^20]`;
the proof is the original one with its `hu` step taken as the hypothesis. -/
theorem derz_lemma_of_psi_uniform
    (hu : ∀ x : ℝ, 10 ^ 11 ≤ x → x ≤ 10 ^ 20 → |ψ x - x| ≤ 807195 * 10 ^ 6) :
    ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 → ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 1615 * 10 ^ 9 := by
  intro n h6 hn
  rcases Nat.lt_or_ge n (1615 * 10 ^ 9 + 4) with hsmall | hbig
  · rcases Nat.lt_or_ge n 7 with h7 | h7
    · exact ⟨2, Nat.prime_two, by omega, by omega⟩
    · exact ⟨3, Nat.prime_three, by omega, by omega⟩
  set m := n - 4 with hm
  obtain ⟨q, hq, hq1, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul (m / 2) (by omega)
  have hqm : q ≤ m := by omega
  set p := Nat.findGreatest Nat.Prime m with hpdef
  have hqp : q ≤ p := Nat.le_findGreatest hqm hq
  have hp : p.Prime := Nat.findGreatest_spec hqm hq
  have hpm : p ≤ m := Nat.findGreatest_le m
  have hnp : ∀ k, p < k → k ≤ m → ¬ k.Prime := fun k h1 h2 =>
    Nat.findGreatest_is_greatest h1 h2
  have hp11 : 5 * 10 ^ 11 ≤ p := by omega
  refine ⟨p, hp, by omega, ?_⟩
  have hθg := theta_gap hpm (by omega) hnp
  rw [show m + 4 = n by omega] at hθg
  have hpR : (5 * 10 ^ 11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp11
  have hnR : (n : ℝ) ≤ 10 ^ 20 := by exact_mod_cast hn
  have hpn : (p : ℝ) ≤ n := by exact_mod_cast (by omega : p ≤ n)
  have h1 := hu n (by linarith) hnR
  have h2 := hu p (by linarith) (by linarith)
  have hd1 := psi_sub_theta_upper (x := n) (by linarith) hnR
  have hd2 := psi_sub_theta_lower (x := p) (by linarith) (by linarith)
  have hd3 := theta_sqrt_diff (p := p) (y := n) (by linarith) hpn
  have hlogn : Real.log n ≤ 46.0522 := (Real.log_le_log (by linarith) hnR).trans log_1e20_lt.le
  have hlogsq : Real.log (√(n : ℝ)) ≤ 23.03 := by
    rw [Real.log_sqrt (by linarith)]; linarith
  have hlogsq0 : 0 ≤ Real.log (√(n : ℝ)) := Real.log_nonneg (by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith)
  have hsp : (7 * 10 ^ 5 : ℝ) ≤ √(p : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hsn : √(p : ℝ) ≤ √(n : ℝ) := Real.sqrt_le_sqrt hpn
  have hroot : (√(n : ℝ) - √(p : ℝ)) * (2 * (7 * 10 ^ 5)) ≤ (n : ℝ) - p := by
    have e : (√(n : ℝ) - √(p : ℝ)) * (√(n : ℝ) + √(p : ℝ)) = (n : ℝ) - p := by
      have a := Real.sq_sqrt (show (0 : ℝ) ≤ n by linarith)
      have b := Real.sq_sqrt (show (0 : ℝ) ≤ p by linarith)
      nlinarith
    have : (2 * (7 * 10 ^ 5) : ℝ) ≤ √(n : ℝ) + √(p : ℝ) := by linarith
    nlinarith
  have hD : (√(n : ℝ) - √(p : ℝ) + 1) * Real.log (√(n : ℝ))
      ≤ ((n : ℝ) - p) / (14 * 10 ^ 5) * 23.03 + 23.03 := by
    have hd0 : 0 ≤ √(n : ℝ) - √(p : ℝ) := by linarith
    have : √(n : ℝ) - √(p : ℝ) ≤ ((n : ℝ) - p) / (14 * 10 ^ 5) := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    nlinarith
  have hreal : (n : ℝ) - p < 1615 * 10 ^ 9 := by
    have a1 := (abs_le.mp h1).1
    have a2 := (abs_le.mp h2).2
    have hθ0 := theta_nonneg (√(p : ℝ))
    nlinarith
  have : ((n - p : ℕ) : ℝ) < 1615 * 10 ^ 9 := by
    rw [Nat.cast_sub (by omega)]; exact hreal
  exact_mod_cast this.le

/-- **`derz_lemma_of_schoenfeldPsi` without `SchoenfeldPsi61`**: the printed constant
`1.615 · 10^12` under RH, CONDITIONAL ON `HSWN70`, `HSWHead14`, `Ordinates14`. -/
theorem derz_lemma_of_schoenfeldPsi_hsw (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) (hH : HSWHead14 gZ)
    (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ) :
    ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 → ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 1615 * 10 ^ 9 :=
  derz_lemma_of_psi_uniform (psi61_uniform_hsw hRH hN hH h14)

/-- **`derz_main_of_psi` without `SchoenfeldPsi61`**: GRH implies ternary Goldbach, CONDITIONAL
ON Zinoviev's `10^20` bound, the `10^13` even check and `HSWN70`, `HSWHead14`, `Ordinates14`. -/
theorem derz_main_of_psi_hsw
    (hZ : GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → IsTernarySum n)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) (hH : HSWHead14 gZ)
    (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ) (hD : EvenGoldbachUpTo (10 ^ 13)) :
    GRH → TernaryGoldbach :=
  derz_main_of_gap (1615 * 10 ^ 9) (by norm_num) hZ
    (fun hG => derz_lemma_of_schoenfeldPsi_hsw (rh_of_GRH hG) hN hH h14) hD

end LeanLab.DERZ1997
