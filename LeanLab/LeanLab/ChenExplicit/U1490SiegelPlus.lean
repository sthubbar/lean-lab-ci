/-
AI-written Lean code, Claude, Lean Lab run 20261022T1603Z-23862, unit U-1490, track T2 FRONTIER,
paper P0009 Bordignon, Johnston, Starichkova 2022, idea I-0105, NEXT ACTION of U-1486.

The plus-4 form of the q-dependent exceptional zero bound for even primitive real characters.

Source, Bordignon arXiv 1907.08327 v1, read this unit via arxiv.org/pdf and ar5iv with WebFetch:
* Section 2.1 eq (5): L(1, chi) = h(sqrt d) log eta_d / sqrt d, chi(-1) = 1, "eta_d = (v0 + u0 sqrt d)/2,
  with v0 and u0 the minimal positive integers satisfying v0^2 - d u0^2 = 4".  Only the +4 equation.
  U-1486 checked, d from 5 to 93, that L(1) sqrt d / log eta_d is h for a norm -1 fundamental unit
  and 2h for a norm +1 one; so eq (5) with SOME integer factor at least 1 in place of h is true in
  both cases.  That is the cited Prop `ClassNumberPlus4`.
* Section 2.2: "beta0 >= 1 - c/(sqrt q log^2 q), with c in [100, 1000] to be chosen later, and
  q >= 4 10^5", and eq (9), |L'(sigma, chi)| <= q^{(1-beta0)/2} log^2 q / 8 + R(A, sigma):
  U-1486's `BordignonEq9`, reused unchanged.
* Theorem 1.3, eq (3), beta0 <= 1 - 100/(sqrt q log^2 q), q > 4 10^5: U-1483's `BordignonThm13`.
* Section 2 eq (4), 1 - beta0 = L(1, chi)/|L'(sigma, chi)|: U-1483's `MeanValueStep`.

New here: the constant max(100, 4 log q) in place of U-1483's max(100, 4 log(q/4)), through
U-1480 `log_unit_ge` inside U-1483 `gap_plus_of_unit`; and `eq9_arith7`, U-1486's arithmetic of
eq (9) on the larger range q >= 7.2e10, which the crossover 4 log q = 100, log q = 25, needs.
Nothing about L-functions is proved here.  Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.ChenExplicit.U1486Thm11C

namespace LeanLab.ChenExplicit.U1490

open Real DirichletCharacter LeanLab.ChenExplicit.U1483 LeanLab.ChenExplicit.U1486

/-- CITED, Bordignon arXiv 1907.08327 Section 2.1 eq (5), the class number formula with the
`+4` unit `η_d = (v + u √q)/2`, `v² - q u² = 4`, `u ≥ 1`, `v > 0`, and an integer factor `h ≥ 1`
(the class number, or twice it when the fundamental unit has norm `+1`). -/
def ClassNumberPlus4 : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), EvenRealPrim χ → (4e5 : ℝ) < q →
    ∃ (h : ℕ) (u v : ℝ), 1 ≤ h ∧ 1 ≤ u ∧ 0 < v ∧ v ^ 2 - q * u ^ 2 = 4 ∧
      ‖LFunction χ 1‖ = h * Real.log ((v + u * Real.sqrt q) / 2) / Real.sqrt q

/-- the plus-4 constant `max(100, 4 log q)`. -/
noncomputable def cP (q : ℝ) : ℝ := max 100 (4 * Real.log q)

/-- the plus-4 Siegel gap `cP q / (√q log² q)`. -/
noncomputable def gapP (q : ℝ) : ℝ := cP q / (Real.sqrt q * Real.log q ^ 2)

/-! ### eq (9) arithmetic for `q ≥ 7.2·10¹⁰` -/

/-- U-1486 `rb_le` with `A ≥ 20000` in place of `A ≥ 316225`; proof verbatim. -/
theorem rb_le' {A θ T l1 l2 g f1 f2 f4 f5 : ℝ} (hA : 20000 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
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
  have e1 : -((A - 1) / 2) * f1 = -((A - 1) / (A + 1) / 2) * p := by
    rw [hp]; field_simp
  have hα : (0.9999 : ℝ) ≤ (A - 1) / (A + 1) := by rw [le_div_iff₀ hA1]; linarith
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

/-- `250 log r ≤ r` for `r ≥ 2000`. -/
lemma log_le_sqrt_div' {r : ℝ} (hr : 2000 ≤ r) : 125 * (2 * Real.log r) ≤ r := by
  have h0 : 0 < r := by linarith
  have e : Real.log r = Real.log 2000 + Real.log (r / 2000) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; field_simp
  have h1 : Real.log (r / 2000) ≤ r / 2000 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log 2000 ≤ 8 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    exact exp_nat_ge (n := 8) (by norm_num)
  rw [e]; nlinarith

/-- **The arithmetic of eq (9) for `q ≥ 7.2·10¹⁰`**, PROVED; U-1486 `eq9_arith` had `q ≥ 10¹¹`. -/
theorem eq9_arith7 {q c β σ θ : ℝ} (hq : 7.2e10 ≤ q) (hc0 : 0 ≤ c) (hc : c ≤ 1000)
    (hβ : 1 - c / (Real.sqrt q * Real.log q ^ 2) ≤ β) (hβσ : β < σ) (hσ : σ < 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    q ^ ((1 - β) / 2) * (Real.log q ^ 2 / 8) + RB (AB q) σ θ ≤ Real.log q ^ 2 / 8 := by
  have hq0 : 0 < q := by linarith
  set L := Real.log q with hL
  set r := Real.sqrt q with hr
  have hL24 : 24 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hq0]
    have := exp_nat_le (n := 24) (B := 7.2e10) (by norm_num); push_cast at this; linarith
  have hr0 : 268000 ≤ r := by
    rw [hr, Real.le_sqrt (by norm_num)] <;> norm_num <;> linarith
  have hrr : r * r = q := Real.mul_self_sqrt hq0.le
  have hD : 0 < r * L ^ 2 := by positivity
  set s0 := 1 - β with hs0
  have hs0c : s0 * (r * L ^ 2) ≤ c := by
    have : c / (r * L ^ 2) * (r * L ^ 2) = c := div_mul_cancel₀ c hD.ne'
    have h' : s0 ≤ c / (r * L ^ 2) := by rw [hs0]; linarith
    nlinarith
  have hs0pos : 0 < s0 := by rw [hs0]; linarith
  have hx0 : s0 * L ≤ 1 / 5000 := by
    have : s0 * L * (r * L) ≤ 1000 := by nlinarith
    have hrL : 5000000 ≤ r * L := by nlinarith
    nlinarith
  have hx0pos : 0 ≤ s0 * L := by positivity
  have hT : q ^ s0 = Real.exp (s0 * L) := by
    rw [Real.rpow_def_of_pos hq0]; congr 1; rw [hL]; ring
  have hE : q ^ (s0 / 2) = Real.exp (s0 * L / 2) := by
    rw [Real.rpow_def_of_pos hq0]; congr 1; rw [hL]; ring
  have hTu : q ^ s0 ≤ 1 + 2 * (s0 * L) := by rw [hT]; exact exp_le_one_add_two hx0pos (by linarith)
  have hTl : 1 ≤ q ^ s0 := Real.one_le_rpow (by linarith) hs0pos.le
  have hEu : q ^ (s0 / 2) ≤ 1 + s0 * L := by
    rw [hE]; have := exp_le_one_add_two (t := s0 * L / 2) (by positivity) (by linarith); linarith
  have hEL : (q ^ (s0 / 2) - 1) * (L ^ 2 / 8) ≤ 1 := by
    have h1 : (q ^ (s0 / 2) - 1) * L ^ 2 ≤ s0 * L * L ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hLr : 125 * L ≤ r := by
      have := log_le_sqrt_div' (by linarith : (2000 : ℝ) ≤ r)
      have e : L = 2 * Real.log r := by
        rw [hL, ← hrr, Real.log_mul (by positivity) (by positivity)]; ring
      rw [e]; exact this
    have h2 : s0 * L * L ^ 2 * r ≤ 1000 * L := by nlinarith
    have h3 : s0 * L * L ^ 2 ≤ 8 := by nlinarith
    nlinarith
  set A := AB q with hA
  have hfl : (⌊r⌋₊ : ℝ) ≤ r := Nat.floor_le (by positivity)
  have hfu : r < (⌊r⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one r
  have hA0 : 20000 ≤ A := by rw [hA, AB]; linarith
  have hA1' : 200000 ≤ A := by rw [hA, AB]; linarith
  have hAq : A + 2 ≤ q := by rw [hA, AB]; nlinarith
  have hσ1 : 1 - σ ≤ s0 := by rw [hs0]; linarith
  obtain ⟨hf1l, hf1u⟩ := fB_bounds (q := q) (x := A + 1) (by linarith) (by linarith) hσ.le hσ1
  obtain ⟨hf2l, -⟩ := fB_bounds (q := q) (x := A + 2) (by linarith) hAq hσ.le hσ1
  obtain ⟨-, hf4u⟩ := fB_bounds (q := q) (x := 4) (by norm_num) (by linarith) hσ.le hσ1
  obtain ⟨hf5l, -⟩ := fB_bounds (q := q) (x := 5) (by norm_num) (by linarith) hσ.le hσ1
  have hl1 : 12 ≤ Real.log (A + 1) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := exp_nat_le (n := 12) (B := 200000) (by norm_num); push_cast at this; linarith
  have hl12 : Real.log (A + 1) ≤ Real.log (A + 2) := Real.log_le_log (by linarith) (by linarith)
  have hg0 := log4_ge
  have hg1 := log4_le
  have hg5 : Real.log 4 / 5 ≤ fB σ 5 := by
    have : Real.log 4 ≤ Real.log 5 := Real.log_le_log (by norm_num) (by norm_num)
    linarith
  have hR := rb_le' hA0 hθ0 hθ1 hTl (by linarith) hl1 hl12 hg0 hg1 hf1l
    hf1u hf2l hf4u hg5
  rw [RB_eq]
  have e : (1 - β) / 2 = s0 / 2 := by rw [hs0]
  rw [e]
  nlinarith

/-- `Thm11C` for `q ≥ 7.2·10¹⁰`, CONDITIONAL ON `BordignonEq9` only. -/
theorem thm11C7_of_eq9 (h9 : BordignonEq9) (c : ℝ) (hc1 : 100 ≤ c) (hc2 : c ≤ 1000)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : EvenRealPrim χ) (hq : (7.2e10 : ℝ) ≤ q)
    (β σ : ℝ) (hβ : RealZero χ β) (h1 : 1 - c / (Real.sqrt q * Real.log q ^ 2) ≤ β)
    (h2 : β < σ) (h3 : σ < 1) :
    ‖deriv (LFunction χ) (σ : ℂ)‖ ≤ Real.log q ^ 2 / 8 := by
  obtain ⟨θ, hθ0, hθ1, hb⟩ := h9 c hc1 hc2 q χ hχ (by linarith) β σ hβ h1 h2 h3
  have := eq9_arith7 hq (by linarith) hc2 h1 h2 h3 hθ0 hθ1
  linarith

/-- `100 ≤ 4 log q` forces `q ≥ 7.2·10¹⁰`. -/
lemma large_of_cP {q : ℝ} (hq : 0 < q) (hc : 100 ≤ 4 * Real.log q) : (7.2e10 : ℝ) ≤ q := by
  have h : 25 ≤ Real.log q := by linarith
  rw [Real.le_log_iff_exp_le hq] at h
  have := exp_nat_ge (n := 25) (B := 7.2e10) (by norm_num)
  push_cast at this
  linarith

/-- **The plus-4 composed bound**, CONDITIONAL ON `ClassNumberPlus4`, `MeanValueStep`,
`BordignonEq9`, `BordignonThm13`: for every even primitive real `χ` mod `q > 4·10⁵` with
`log q ≤ 250` and every real zero `β ∈ (0,1)`, `β ≤ 1 - max(100, 4 log q)/(√q log² q)`. -/
theorem siegel_even_q_dep_plus (hC : ClassNumberPlus4) (hM : MeanValueStep) (h9 : BordignonEq9)
    (h13 : BordignonThm13) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : EvenRealPrim χ)
    (hq : (4e5 : ℝ) < q) (hqU : Real.log (q : ℝ) ≤ 250) (β : ℝ) (hβ : RealZero χ β) :
    β ≤ 1 - gapP q := by
  have hq1 : (1 : ℝ) < q := by linarith
  have hl : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 (by linarith)
  unfold gapP cP
  rcases le_total (4 * Real.log (q : ℝ)) 100 with hc | hc
  · rw [max_eq_left hc]; exact h13 q χ hχ hq β hβ
  · rw [max_eq_right hc]
    by_contra hcon
    push_neg at hcon
    obtain ⟨σ, hσ1, hσ2, hmv⟩ := hM q χ hχ β hβ
    have hMle := thm11C7_of_eq9 h9 (4 * Real.log (q : ℝ)) hc (by linarith) q χ hχ
      (large_of_cP (by linarith) hc) β σ hβ hcon.le hσ1 hσ2
    obtain ⟨h, u, v, hh, hu, hv, hpell, hL⟩ := hC q χ hχ hq
    have hunit := LeanLab.Routes.U1480.log_unit_ge (d := (q : ℝ)) (by linarith) hu hv hpell
    have hlu : 0 < Real.log ((v + u * Real.sqrt q) / 2) := by linarith
    have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
    -- `log η / √q ≤ ‖L(1)‖ = (1-β) ‖L'(σ)‖`
    have hle : Real.log ((v + u * Real.sqrt q) / 2) / Real.sqrt q ≤ ‖LFunction χ 1‖ := by
      rw [hL]
      apply div_le_div_of_nonneg_right _ hs.le
      nlinarith
    have hpos : 0 < ‖deriv (LFunction χ) (σ : ℂ)‖ := by
      rcases (norm_nonneg (deriv (LFunction χ) (σ : ℂ))).lt_or_eq with h0 | h0
      · exact h0
      · exfalso
        have : 0 < Real.log ((v + u * Real.sqrt q) / 2) / Real.sqrt q := by positivity
        rw [hmv, ← h0, mul_zero] at hle; linarith
    have hg := gap_plus_of_unit (q := (q : ℝ)) hq1 hu hv hpell hpos hMle rfl
      (hle.trans hmv.le)
    have e : 4 * Real.log (q : ℝ) / (Real.sqrt q * Real.log q ^ 2) =
        4 / (Real.sqrt q * Real.log q) := by field_simp
    rw [e] at hcon
    linarith

/-- `gapP q ≥ 4/(√K log K)` for `4·10⁵ < q ≤ K`: the plus-4 gap at `q` dominates its value at `K`. -/
theorem gapP_ge_K {q K : ℝ} (hq : 4e5 < q) (hqK : q ≤ K) :
    4 / (Real.sqrt K * Real.log K) ≤ gapP q := by
  have hq0 : 0 < q := by linarith
  have hlq : 0 < Real.log q := Real.log_pos (by linarith)
  have hlqK : Real.log q ≤ Real.log K := Real.log_le_log hq0 hqK
  have hsq0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hsqK : Real.sqrt q ≤ Real.sqrt K := Real.sqrt_le_sqrt hqK
  have hbase : 4 / (Real.sqrt K * Real.log K) ≤ 4 / (Real.sqrt q * Real.log q) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul hsqK hlqK hlq.le (by positivity))
  unfold gapP cP
  rcases le_total (4 * Real.log q) 100 with h | h
  · rw [max_eq_left h]
    have : 4 / (Real.sqrt q * Real.log q) ≤ 100 / (Real.sqrt q * Real.log q ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 < Real.sqrt q * Real.log q := by positivity
      nlinarith [mul_pos this hlq]
    linarith
  · rw [max_eq_right h]
    have e : 4 * Real.log q / (Real.sqrt q * Real.log q ^ 2) = 4 / (Real.sqrt q * Real.log q) := by
      field_simp
    rw [e]; exact hbase

/-- **The eq (91) form up to `K`**, CONDITIONAL ON `ClassNumberPlus4`, `MeanValueStep`,
`BordignonEq9`, `BordignonThm13`: for `log K ≤ 250`, every real zero of every even primitive
real `L(s, χ)` mod `q`, `4·10⁵ < q ≤ K`, is at most `1 - 4/(√K log K)`. -/
theorem siegel_even_upto_K_plus (hC : ClassNumberPlus4) (hM : MeanValueStep) (h9 : BordignonEq9)
    (h13 : BordignonThm13) {K : ℝ} (hKU : Real.log K ≤ 250) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : EvenRealPrim χ) (hq : (4e5 : ℝ) < q) (hqK : (q : ℝ) ≤ K)
    (β : ℝ) (hβ : RealZero χ β) :
    β ≤ 1 - 4 / (Real.sqrt K * Real.log K) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hqU : Real.log (q : ℝ) ≤ 250 := le_trans (Real.log_le_log hq0 hqK) hKU
  have := siegel_even_q_dep_plus hC hM h9 h13 q χ hχ hq hqU β hβ
  have := gapP_ge_K hq hqK
  linarith

/-- the plus-4 gap is never below U-1483's `gapQ`. -/
theorem gapQ_le_gapP {q : ℝ} (hq : 4 < q) : gapQ q ≤ gapP q := by
  have hq0 : 0 < q := by linarith
  have hl : 0 < Real.log q := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  unfold gapQ gapP cQ cP
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply max_le_max le_rfl
  have : Real.log (q / 4) ≤ Real.log q := Real.log_le_log (by positivity) (by linarith)
  linarith

/-! ### vacuity tests -/

/-- Vacuity 1: the Pell hypothesis of `ClassNumberPlus4` is satisfiable with `u ≥ 1`, `v > 0`:
`q = 5`, `u = 1`, `v = 3`. -/
example : ∃ u v : ℝ, 1 ≤ u ∧ 0 < v ∧ v ^ 2 - 5 * u ^ 2 = 4 := ⟨1, 3, le_rfl, by norm_num, by norm_num⟩

/-- Vacuity 2: the hypotheses of `eq9_arith7` hold at `q = 7.2·10¹⁰`, below U-1486's `10¹¹`. -/
example : ∃ β σ : ℝ, 1 - 1000 / (Real.sqrt 7.2e10 * Real.log 7.2e10 ^ 2) ≤ β ∧ β < σ ∧ σ < 1 ∧
    (7.2e10 : ℝ) ^ ((1 - β) / 2) * (Real.log 7.2e10 ^ 2 / 8) + RB (AB 7.2e10) σ 1
      ≤ Real.log 7.2e10 ^ 2 / 8 := by
  have hpos : 0 < 1000 / (Real.sqrt 7.2e10 * Real.log 7.2e10 ^ 2) := by
    have : 0 < Real.log (7.2e10 : ℝ) := Real.log_pos (by norm_num)
    positivity
  refine ⟨1 - 1000 / (Real.sqrt 7.2e10 * Real.log 7.2e10 ^ 2),
    (1 + (1 - 1000 / (Real.sqrt 7.2e10 * Real.log 7.2e10 ^ 2))) / 2, le_rfl, by linarith,
    by linarith, ?_⟩
  exact eq9_arith7 (by norm_num) (by norm_num) le_rfl le_rfl (by linarith) (by linarith)
    (by norm_num) le_rfl

/-- Vacuity 3: both branches of `cP` occur, `4 log q < 100` at `q = e^{20}`, `> 100` at `e^{30}`. -/
example : 4 * Real.log (Real.exp 20) < 100 ∧ 100 < 4 * Real.log (Real.exp 30) := by
  simp only [Real.log_exp]; norm_num

end LeanLab.ChenExplicit.U1490
