/-
AI-written Lean code, Claude, Lean Lab run 20261022T1302Z-31860, unit U-1486, track T2 FRONTIER,
paper P0009 Bordignon, Johnston, Starichkova 2022, follow-up of U-1483.

Settles the U-1483 input `Thm11C`, the c-form of Bordignon arXiv 1907.08327 v1 Theorem 1.1,
in the range that U-1483 uses it, q at least 1e11, c in [100, 1000].

Source, read this unit via arxiv.org/abs, arxiv.org/pdf, arxiv.org/html and ar5iv:
* Section 2.2 Theorem 2.1, after Louboutin: chi even primitive mod q, A = floor(sqrt q) - 1,
  f on [4, oo) decreasing to 0 with f(n) - 2 f(n+1) + f(n+2) >= 0 for n >= 4; then for some
  0 <= theta <= 1, |sum_{n >= 4} chi(n) f(n)| <= sum_{n=4}^A f(n) - (A/2) f(A)
  + (A/2)(f(A) - f(A+1)) + (1/2) f(A+1) + (theta/2)((A+1)(f(A+1) - f(A+2)) + f(A+2))
  + 18 f(4) - 12 f(5).
* Section 2.2 then assumes beta0 >= 1 - c/(sqrt q log^2 q) with c in [100, 1000] "to be chosen
  later", takes f(n) = log n / n^sigma, sigma in (beta0, 1), and obtains eq (9):
  |L'(sigma, chi)| <= q^{(1-beta0)/2} (1/8) log^2 q + R(A, sigma), R(A, sigma) the terms of the
  right side of Theorem 2.1 other than the sum.  "choosing c = 100 it is easy to see" the bound
  log^2 q / 8.  The paper never writes the R estimate; it is done here.
* The analytic input is therefore the cited Prop `BordignonEq9`, eq (9) with R written out and
  theta existential, under the printed Section 2.2 hypothesis with general c.  What remains is
  real arithmetic, proved here: `eq9_arith`.  Numerics, U1486eq9.py in the session scratchpad:
  the margin log^2 q/8 - RHS(9) is 4.22 at log q = 26.4 and 9.12 at log q = 46 for
  c = 4 log(q/4); at q = 4e5 eq (9) allows only c <= 637.8, so the full U-1483 `Thm11C`
  for every q > 4e5 and c <= 1000 is NOT given by the argument; the range q >= 1e11 is.

Nothing about L-functions is proved here.  Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.ChenExplicit.U1483SiegelQ

namespace LeanLab.ChenExplicit.U1486

open Real DirichletCharacter LeanLab.ChenExplicit.U1483

/-- Bordignon's `f(x) = log x / x^σ`, Section 2.2. -/
noncomputable def fB (σ x : ℝ) : ℝ := Real.log x / x ^ σ

/-- the right side of Bordignon Theorem 2.1 minus the sum, at `f = fB σ`: `R(A, σ)` of eq (9). -/
noncomputable def RB (A σ θ : ℝ) : ℝ :=
  -(A / 2) * fB σ A + (A / 2) * (fB σ A - fB σ (A + 1)) + (1 / 2) * fB σ (A + 1)
    + (θ / 2) * ((A + 1) * (fB σ (A + 1) - fB σ (A + 2)) + fB σ (A + 2))
    + 18 * fB σ 4 - 12 * fB σ 5

/-- Bordignon's `A = ⌊√q⌋ - 1`. -/
noncomputable def AB (q : ℝ) : ℝ := (⌊Real.sqrt q⌋₊ : ℝ) - 1

/-- CITED, Bordignon arXiv 1907.08327 v1, Section 2.2 eq (9), with `R(A, σ)` the non-sum part of
the right side of Theorem 2.1 and `θ ∈ [0,1]` as there, under the Section 2.2 hypothesis
`β₀ ≥ 1 - c/(√q log² q)`, `c ∈ [100, 1000]`, `q > 4·10⁵`. -/
def BordignonEq9 : Prop :=
  ∀ (c : ℝ), 100 ≤ c → c ≤ 1000 →
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), EvenRealPrim χ → (4e5 : ℝ) < q →
    ∀ β σ : ℝ, RealZero χ β →
      1 - c / (Real.sqrt q * Real.log q ^ 2) ≤ β → β < σ → σ < 1 →
      ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
        ‖deriv (LFunction χ) (σ : ℂ)‖ ≤
          (q : ℝ) ^ ((1 - β) / 2) * (Real.log q ^ 2 / 8) + RB (AB q) σ θ

/-- the c-form of Theorem 1.1 for `q ≥ 10¹¹`: exactly U-1483's `Thm11C` with `4·10⁵ < q`
replaced by `10¹¹ ≤ q`. -/
def Thm11CLarge : Prop :=
  ∀ (c : ℝ), 100 ≤ c → c ≤ 1000 →
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), EvenRealPrim χ → (1e11 : ℝ) ≤ q →
    ∀ β σ : ℝ, RealZero χ β →
      1 - c / (Real.sqrt q * Real.log q ^ 2) ≤ β → β < σ → σ < 1 →
      ‖deriv (LFunction χ) (σ : ℂ)‖ ≤ Real.log q ^ 2 / 8

/-! ### elementary bounds -/

lemma log4_ge : (1.38 : ℝ) ≤ Real.log 4 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have := Real.log_two_gt_d9; push_cast; nlinarith

lemma exp_nat_le {n : ℕ} {B : ℝ} (h : (2.7182818286 : ℝ) ^ n ≤ B) : Real.exp n ≤ B := by
  have e : Real.exp n = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have := Real.exp_one_lt_d9
  have : Real.exp 1 ^ n ≤ (2.7182818286 : ℝ) ^ n :=
    pow_le_pow_left₀ (Real.exp_pos 1).le this.le n
  linarith

lemma exp_nat_ge {n : ℕ} {B : ℝ} (h : B ≤ (2.7182818283 : ℝ) ^ n) : B ≤ Real.exp n := by
  have e : Real.exp n = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have := Real.exp_one_gt_d9
  have : (2.7182818283 : ℝ) ^ n ≤ Real.exp 1 ^ n :=
    pow_le_pow_left₀ (by norm_num) this.le n
  linarith

/-- `exp t ≤ 1 + 2t` on `[0, 1]`. -/
lemma exp_le_one_add_two {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Real.exp t ≤ 1 + 2 * t := by
  have := Real.abs_exp_sub_one_le (x := t) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at this
  have := le_abs_self (Real.exp t - 1)
  linarith

/-- the `fB` sandwich: for `1 ≤ x ≤ q`, `0 ≤ 1 - σ ≤ s₀`, `log x / x ≤ fB σ x ≤ q^{s₀} log x / x`. -/
lemma fB_bounds {q x σ s0 : ℝ} (hx : 1 ≤ x) (hxq : x ≤ q) (hσ : σ ≤ 1) (hs : 1 - σ ≤ s0) :
    Real.log x / x ≤ fB σ x ∧ fB σ x ≤ q ^ s0 * Real.log x / x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hxs : 0 < x ^ σ := Real.rpow_pos_of_pos hx0 σ
  have h1 : x ^ σ ≤ x := by
    have := Real.rpow_le_rpow_of_exponent_le hx hσ; rwa [Real.rpow_one] at this
  have h2 : x ≤ x ^ σ * q ^ s0 := by
    have e : x = x ^ σ * x ^ (1 - σ) := by
      rw [← Real.rpow_add hx0]; simp
    have h3 : x ^ (1 - σ) ≤ q ^ (1 - σ) := Real.rpow_le_rpow hx0.le hxq (by linarith)
    have h4 : q ^ (1 - σ) ≤ q ^ s0 := Real.rpow_le_rpow_of_exponent_le (by linarith) hs
    calc x = x ^ σ * x ^ (1 - σ) := e
      _ ≤ x ^ σ * q ^ s0 := by gcongr; linarith
  unfold fB
  constructor
  · exact div_le_div_of_nonneg_left hl hxs h1
  · rw [div_le_div_iff₀ hxs hx0]; nlinarith

/-- `R(A, σ)` regrouped. -/
lemma RB_eq (A σ θ : ℝ) : RB A σ θ = -((A - 1) / 2) * fB σ (A + 1)
    + (θ / 2) * ((A + 1) * fB σ (A + 1) - A * fB σ (A + 2)) + 18 * fB σ 4 - 12 * fB σ 5 := by
  unfold RB; ring

/-- **The R estimate**, pure arithmetic: under the sandwich bounds, `R(A, σ) ≤ -2`. -/
theorem rb_le {A θ T l1 l2 g f1 f2 f4 f5 : ℝ} (hA : 316225 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hT1 : 1 ≤ T) (hT : T ≤ 1.001) (hl1 : 12 ≤ l1) (hl12 : l1 ≤ l2)
    (hg0 : 1.38 ≤ g) (hg1 : g ≤ 1.3863)
    (hf1l : l1 / (A + 1) ≤ f1) (hf1u : f1 ≤ T * l1 / (A + 1)) (hf2 : l2 / (A + 2) ≤ f2)
    (hf4 : f4 ≤ T * g / 4) (hf5 : g / 5 ≤ f5) :
    -((A - 1) / 2) * f1 + (θ / 2) * ((A + 1) * f1 - A * f2) + 18 * f4 - 12 * f5 ≤ -2 := by
  have hA1 : 0 < A + 1 := by linarith
  have hA2 : 0 < A + 2 := by linarith
  set p := (A + 1) * f1 with hp
  have hpl : l1 ≤ p := by rw [div_le_iff₀ hA1] at hf1l; linarith
  have hpu : p ≤ T * l1 := by rw [le_div_iff₀ hA1] at hf1u; linarith
  have hw : l2 ≤ (A + 2) * f2 := by rw [div_le_iff₀ hA2] at hf2; linarith
  -- term 1: -((A-1)/2) f1 = -(α/2) p with α = (A-1)/(A+1) ≥ 0.9999
  have e1 : -((A - 1) / 2) * f1 = -((A - 1) / (A + 1) / 2) * p := by
    rw [hp]; field_simp
  have hα : (0.9999 : ℝ) ≤ (A - 1) / (A + 1) := by rw [le_div_iff₀ hA1]; linarith
  -- term 2: X = p - β' w, β' = A/(A+2) ≥ 0.9999
  have e2 : A * f2 = A / (A + 2) * ((A + 2) * f2) := by field_simp
  have hβ' : (0.9999 : ℝ) ≤ A / (A + 2) := by rw [le_div_iff₀ hA2]; linarith
  have hβ1 : A / (A + 2) ≤ 1 := by rw [div_le_iff₀ hA2]; linarith
  have hX : p - A * f2 ≤ (T - A / (A + 2)) * l1 := by
    rw [e2]
    have : A / (A + 2) * l1 ≤ A / (A + 2) * ((A + 2) * f2) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  have hY0 : 0 ≤ (T - A / (A + 2)) * l1 := by
    apply mul_nonneg (by linarith) (by linarith)
  have hθX : θ / 2 * (p - A * f2) ≤ (T - A / (A + 2)) * l1 / 2 := by
    have : θ * (p - A * f2) ≤ θ * ((T - A / (A + 2)) * l1) :=
      mul_le_mul_of_nonneg_left hX hθ0
    nlinarith
  have ht1 : -((A - 1) / (A + 1) / 2) * p ≤ -((A - 1) / (A + 1) / 2) * l1 := by
    have : 0 ≤ (A - 1) / (A + 1) := by linarith
    nlinarith
  rw [e1]
  have : 18 * f4 - 12 * f5 ≤ g * (4.5 * T - 2.4) := by nlinarith
  nlinarith

/-- `125 log q ≤ √q` for `√q ≥ 316227`. -/
lemma log_le_sqrt_div {r : ℝ} (hr : 316227 ≤ r) : 125 * (2 * Real.log r) ≤ r := by
  have h0 : 0 < r := by linarith
  have e : Real.log r = Real.log 2000 + Real.log (r / 2000) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; field_simp
  have h1 : Real.log (r / 2000) ≤ r / 2000 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log 2000 ≤ 8 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    exact exp_nat_ge (n := 8) (by norm_num)
  rw [e]; nlinarith

/-- **The arithmetic of eq (9)**, PROVED: for `q ≥ 10¹¹`, `0 ≤ c ≤ 1000`,
`1 - c/(√q log² q) ≤ β < σ < 1`, `θ ∈ [0,1]`:
`q^{(1-β)/2} log² q / 8 + R(A, σ) ≤ log² q / 8`. -/
theorem eq9_arith {q c β σ θ : ℝ} (hq : 1e11 ≤ q) (hc0 : 0 ≤ c) (hc : c ≤ 1000)
    (hβ : 1 - c / (Real.sqrt q * Real.log q ^ 2) ≤ β) (hβσ : β < σ) (hσ : σ < 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    q ^ ((1 - β) / 2) * (Real.log q ^ 2 / 8) + RB (AB q) σ θ ≤ Real.log q ^ 2 / 8 := by
  have hq0 : 0 < q := by linarith
  set L := Real.log q with hL
  set r := Real.sqrt q with hr
  have hL25 : 25 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hq0]
    have := exp_nat_le (n := 25) (B := 1e11) (by norm_num); push_cast at this; linarith
  have hr0 : 316227 ≤ r := by
    rw [hr, Real.le_sqrt (by norm_num)] <;> norm_num <;> linarith
  have hrr : r * r = q := Real.mul_self_sqrt hq0.le
  have hD : 0 < r * L ^ 2 := by positivity
  set s0 := 1 - β with hs0
  have hs0c : s0 * (r * L ^ 2) ≤ c := by
    have : c / (r * L ^ 2) * (r * L ^ 2) = c := div_mul_cancel₀ c hD.ne'
    have h' : s0 ≤ c / (r * L ^ 2) := by rw [hs0]; linarith
    nlinarith
  have hs0pos : 0 < s0 := by rw [hs0]; linarith
  -- x0 = s0 L is small
  have hx0 : s0 * L ≤ 1 / 5000 := by
    have : s0 * L * (r * L) ≤ 1000 := by nlinarith
    have hrL : 5000000 ≤ r * L := by nlinarith
    nlinarith
  have hx0pos : 0 ≤ s0 * L := by positivity
  -- T = q^{s0}, E = q^{s0/2}
  have hT : q ^ s0 = Real.exp (s0 * L) := by
    rw [Real.rpow_def_of_pos hq0]; congr 1; rw [hL]; ring
  have hE : q ^ (s0 / 2) = Real.exp (s0 * L / 2) := by
    rw [Real.rpow_def_of_pos hq0]; congr 1; rw [hL]; ring
  have hTu : q ^ s0 ≤ 1 + 2 * (s0 * L) := by rw [hT]; exact exp_le_one_add_two hx0pos (by linarith)
  have hTl : 1 ≤ q ^ s0 := Real.one_le_rpow (by linarith) hs0pos.le
  have hEu : q ^ (s0 / 2) ≤ 1 + s0 * L := by
    rw [hE]; have := exp_le_one_add_two (t := s0 * L / 2) (by positivity) (by linarith); linarith
  -- (E - 1) L² / 8 ≤ 1
  have hEL : (q ^ (s0 / 2) - 1) * (L ^ 2 / 8) ≤ 1 := by
    have h1 : (q ^ (s0 / 2) - 1) * L ^ 2 ≤ s0 * L * L ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hLr : 125 * L ≤ r := by
      have := log_le_sqrt_div hr0
      have e : L = 2 * Real.log r := by
        rw [hL, ← hrr, Real.log_mul (by positivity) (by positivity)]; ring
      rw [e]; exact this
    have h2 : s0 * L * L ^ 2 * r ≤ 1000 * L := by nlinarith
    have h3 : s0 * L * L ^ 2 ≤ 8 := by nlinarith
    nlinarith
  -- the R estimate
  set A := AB q with hA
  have hfl : (⌊r⌋₊ : ℝ) ≤ r := Nat.floor_le (by positivity)
  have hfu : r < (⌊r⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one r
  have hA0 : 316225 ≤ A := by rw [hA, AB]; linarith
  have hAq : A + 2 ≤ q := by rw [hA, AB]; nlinarith
  have hσ1 : 1 - σ ≤ s0 := by rw [hs0]; linarith
  obtain ⟨hf1l, hf1u⟩ := fB_bounds (q := q) (x := A + 1) (by linarith) (by linarith) hσ.le hσ1
  obtain ⟨hf2l, -⟩ := fB_bounds (q := q) (x := A + 2) (by linarith) hAq hσ.le hσ1
  obtain ⟨-, hf4u⟩ := fB_bounds (q := q) (x := 4) (by norm_num) (by linarith) hσ.le hσ1
  obtain ⟨hf5l, -⟩ := fB_bounds (q := q) (x := 5) (by norm_num) (by linarith) hσ.le hσ1
  have hl1 : 12 ≤ Real.log (A + 1) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := exp_nat_le (n := 12) (B := 316226) (by norm_num); push_cast at this; linarith
  have hl12 : Real.log (A + 1) ≤ Real.log (A + 2) := Real.log_le_log (by linarith) (by linarith)
  have hg0 := log4_ge
  have hg1 := log4_le
  have hg5 : Real.log 4 / 5 ≤ fB σ 5 := by
    have : Real.log 4 ≤ Real.log 5 := Real.log_le_log (by norm_num) (by norm_num)
    linarith
  have hR := rb_le hA0 hθ0 hθ1 hTl (by linarith) hl1 hl12 hg0 hg1 hf1l
    hf1u hf2l hf4u hg5
  rw [RB_eq]
  have e : (1 - β) / 2 = s0 / 2 := by rw [hs0]
  rw [e]
  nlinarith

/-- **Thm11C for `q ≥ 10¹¹`**, CONDITIONAL ON `BordignonEq9` only. -/
theorem thm11CLarge_of_eq9 (h9 : BordignonEq9) : Thm11CLarge := by
  intro c hc1 hc2 q _ χ hχ hq β σ hβ h1 h2 h3
  obtain ⟨θ, hθ0, hθ1, hb⟩ := h9 c hc1 hc2 q χ hχ (by linarith) β σ hβ h1 h2 h3
  have := eq9_arith hq (by linarith) hc2 h1 h2 h3 hθ0 hθ1
  linarith

/-- `100 ≤ 4 log(q/4)` forces `q ≥ 10¹¹`. -/
lemma large_of_c {q : ℝ} (hq : 0 < q) (hc : 100 ≤ 4 * Real.log (q / 4)) : (1e11 : ℝ) ≤ q := by
  have h : 25 ≤ Real.log (q / 4) := by linarith
  rw [Real.le_log_iff_exp_le (by positivity)] at h
  have := exp_nat_ge (n := 25) (B := 2.5e10) (by norm_num)
  push_cast at this
  linarith

/-- **U-1483's `siegel_even_q_dep` with `Thm11C` replaced by the printed eq (9)**, CONDITIONAL ON
`ClassNumberH1`, `MeanValueStep`, `BordignonEq9`, `BordignonThm13`. -/
theorem siegel_even_q_dep_eq9 (hC : ClassNumberH1) (hM : MeanValueStep) (h9 : BordignonEq9)
    (h13 : BordignonThm13) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : EvenRealPrim χ)
    (hq : (4e5 : ℝ) < q) (hqU : Real.log ((q : ℝ) / 4) ≤ 250) (β : ℝ) (hβ : RealZero χ β) :
    β ≤ 1 - gapQ q := by
  have hq1 : (1 : ℝ) < q := by linarith
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 (by linarith)
  unfold gapQ cQ
  rcases le_total (4 * Real.log ((q : ℝ) / 4)) 100 with hc | hc
  · rw [max_eq_left hc]; exact h13 q χ hχ hq β hβ
  · rw [max_eq_right hc]
    by_contra hcon
    push_neg at hcon
    obtain ⟨σ, hσ1, hσ2, hmv⟩ := hM q χ hχ β hβ
    have hMle := thm11CLarge_of_eq9 h9 (4 * Real.log ((q : ℝ) / 4)) hc (by linarith) q χ hχ
      (large_of_c (by linarith) hc) β σ hβ hcon.le hσ1 hσ2
    obtain ⟨h, u, v, hh, hu, hv, _, hL⟩ := hC q χ hχ hq
    have hA : 0 < Real.log ((q : ℝ) / 4) := by linarith
    have hunit := log_unit_ge_any (d := (q : ℝ)) (by linarith) hu hv
    have hL1 : Real.log ((q : ℝ) / 4) / (2 * Real.sqrt q) ≤ ‖LFunction χ 1‖ := by
      rw [hL]
      have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
      have hlu : 0 ≤ Real.log ((v + u * Real.sqrt q) / 2) := by linarith
      rw [div_le_div_iff₀ (by positivity) hs]
      have : Real.log ((q : ℝ) / 4) ≤ 2 * (h * Real.log ((v + u * Real.sqrt q) / 2)) := by
        nlinarith
      nlinarith
    have hg := gap_core hq1 hA (norm_nonneg _) hMle hL1 hmv
    linarith

/-- the eq 91 form up to `K`, CONDITIONAL ON the same four printed inputs. -/
theorem siegel_even_upto_K_eq9 (hC : ClassNumberH1) (hM : MeanValueStep) (h9 : BordignonEq9)
    (h13 : BordignonThm13) {K : ℝ} (hK : 100 ≤ 4 * Real.log (K / 4))
    (hKU : Real.log (K / 4) ≤ 250) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : EvenRealPrim χ) (hq : (4e5 : ℝ) < q) (hqK : (q : ℝ) ≤ K)
    (β : ℝ) (hβ : RealZero χ β) :
    β ≤ 1 - 4 * Real.log (K / 4) / (Real.sqrt K * Real.log K ^ 2) := by
  have hq0 : (0 : ℝ) < q := by norm_num at hq ⊢; linarith
  have hqU : Real.log ((q : ℝ) / 4) ≤ 250 :=
    le_trans (Real.log_le_log (by positivity) (by linarith)) hKU
  have := siegel_even_q_dep_eq9 hC hM h9 h13 q χ hχ hq hqU β hβ
  have := gapQ_ge_K hq hqK hK
  linarith

/-! ### vacuity tests -/

/-- Vacuity 1: the hypotheses of `eq9_arith` are jointly satisfiable at `q = 10¹¹`, `c = 1000`,
`β = 1 - c/(√q log² q)`, `σ = (1 + β)/2`, `θ = 1`, so the theorem has content there. -/
example : ∃ β σ : ℝ, 1 - 1000 / (Real.sqrt 1e11 * Real.log 1e11 ^ 2) ≤ β ∧ β < σ ∧ σ < 1 ∧
    (1e11 : ℝ) ^ ((1 - β) / 2) * (Real.log 1e11 ^ 2 / 8) + RB (AB 1e11) σ 1
      ≤ Real.log 1e11 ^ 2 / 8 := by
  have hpos : 0 < 1000 / (Real.sqrt 1e11 * Real.log 1e11 ^ 2) := by
    have : 0 < Real.log (1e11 : ℝ) := Real.log_pos (by norm_num)
    positivity
  refine ⟨1 - 1000 / (Real.sqrt 1e11 * Real.log 1e11 ^ 2),
    (1 + (1 - 1000 / (Real.sqrt 1e11 * Real.log 1e11 ^ 2))) / 2, le_rfl, by linarith,
    by linarith, ?_⟩
  exact eq9_arith (by norm_num) (by norm_num) le_rfl le_rfl (by linarith) (by linarith)
    (by norm_num) le_rfl

/-- Vacuity 2: the hypotheses of `rb_le` are jointly satisfiable, with `f` values at the bottom
of the sandwich: `A = 316225`, `T = 1`, `l1 = l2 = 12.7`, `g = 1.3863`. -/
example : -((316225 - 1) / 2) * (12.7 / (316225 + 1)) + (1 / 2) * ((316225 + 1) *
    (12.7 / (316225 + 1)) - 316225 * (12.7 / (316225 + 2))) + 18 * (1 * 1.3863 / 4)
    - 12 * (1.3863 / 5) ≤ (-2 : ℝ) :=
  rb_le (A := 316225) (θ := 1) (T := 1) (l1 := 12.7) (l2 := 12.7) (g := 1.3863)
    le_rfl (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) le_rfl (by norm_num) le_rfl
    le_rfl (by norm_num) le_rfl le_rfl le_rfl

/-- Vacuity 3: the side condition of the large range is real: `q = 4·10⁵ + 1` is a modulus of
Theorem 1.1 below `10¹¹`. -/
example : (4e5 : ℝ) < 400001 ∧ ¬ ((1e11 : ℝ) ≤ 400001) := by norm_num

end LeanLab.ChenExplicit.U1486

#print axioms LeanLab.ChenExplicit.U1486.log4_ge
#print axioms LeanLab.ChenExplicit.U1486.exp_le_one_add_two
#print axioms LeanLab.ChenExplicit.U1486.fB_bounds
#print axioms LeanLab.ChenExplicit.U1486.RB_eq
#print axioms LeanLab.ChenExplicit.U1486.rb_le
#print axioms LeanLab.ChenExplicit.U1486.log_le_sqrt_div
#print axioms LeanLab.ChenExplicit.U1486.eq9_arith
#print axioms LeanLab.ChenExplicit.U1486.thm11CLarge_of_eq9
#print axioms LeanLab.ChenExplicit.U1486.large_of_c
#print axioms LeanLab.ChenExplicit.U1486.siegel_even_q_dep_eq9
#print axioms LeanLab.ChenExplicit.U1486.siegel_even_upto_K_eq9
