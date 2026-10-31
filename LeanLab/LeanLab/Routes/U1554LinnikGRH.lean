import LeanLab.HeathBrownPuchta.Assembly
import LeanLab.HeathBrownPuchta.Lemma8Const
import LeanLab.HeathBrownPuchta.Decomp1530c
import LeanLab.Romanov.HMean

/-!
# Linnik-Goldbach under GRH: K = 6 inside the Heath-Brown and Puchta 2002 scheme

Unit U-1554, run 20261026T1219Z-15327, track T2 FRONTIER, idea I-0129. AI wrote the Lean code.
Binary Goldbach is OPEN; this file concerns the Linnik-Goldbach line only.

Heath-Brown and Puchta 2002, Section 6, p. 28, decide `K` by `13.968 λ^{K-2} < 2.7895`, with
`λ = 0.722428` on GRH from Lemma 1, `E(λ) > 1/2`, computed at `h = 16` in Section 7, p. 31.
That gives `K > 6.9545`, so `K = 7`, and `K = 6` fails: `13.968 λ^4 = 3.8046`.

Lever map, Python `Routes/numerics/k6_grh_U1554.py` and `.out`:
* `13.968 = (C₁ - 2) C₂ + log 2 / C₀` with Chen's `C₁ = 7.8342` and `C₂ ≤ 2.2141`, (41) p. 26.
* Single levers for `K = 6`: the minor constant below `10.2411`; or `λ < 0.668495`; or the major
  constant above `3.8046`, beyond the cap `2/C₀ = 3.0296`; or `C₁ < 6.1512`; or `C₂ < 1.5754`,
  below the true value `≈ 1.9366`. None of these is reachable alone.
* Combined: Johnston and Trudgian's `C₁ = 6.7814`, 2026 Prop 2, from Lichtman, with Pintz and
  Ruzsa's `C₂ < 1.94`, 2003 Lemma 4, gives a minor constant `≤ 10.326`, which needs
  `λ < 0.720934`. Display 44 at larger `h` gives `λ_h`: `0.722427` at 16, `0.721215` at 20,
  `0.720774` at 22, `0.720406` at 24, `0.720244` at 25. So `λ = 0.7208` with `h = 22` or `24`
  closes `K = 6`. The unconditional `λ_23 = 0.862327` reproduces Liu and Lü's value at `h = 23`,
  so the larger `h` lever is KNOWN.

The improved input, `NeededInput`, is `E(0.7208) > 1/2` from display 44 at some `h`: a finite
computation. It is weaker than Platt and Trudgian's GRH value `λ = 0.7163436`, so the route is
KNOWN in substance, and `K = 6` on GRH is KNOWN, Johnston and Trudgian 2026; `K = 5` on GRH is
claimed by Li and Liu 2026.

PROVED unconditional: `C9_JT_le`, `crit6_new`, `crit6_hbp_fails`, `crit6_jt_at_hbp_lam_fails`,
`Fzero_pos`, `Fzero_le_exp`, `lambdaGood_mono`, `lambdaGood_two` (vacuity of `LambdaGood`),
`inputs6_consistent` (vacuity of `Inputs6`), `consistent6_positive`.
ASSEMBLY, real proofs: `section6_six`, `allLarge_six`, `neededInput_of_h22`,
`neededInput_of_h24`, `K6_of_input`.
PROVED in task191: `E22_num`, `E24_num`, `reT_succ`, `reT_reflect`, `C2_summable`.
The rational certificate transfer and reflection are proved below.
CONDITIONAL ON `polynomialAverage_eq_carry191`: `Fzero22_le`, `Fzero24_le`.
LEAF: `polynomialAverage_eq_carry191`. Cited: `pintzRuzsa_C2_le`.
-/

namespace LeanLab.Routes.U1554LinnikGRH

open Filter Real LeanLab.Linnik
open LeanLab.HeathBrownPuchta.Assembly (C9 small_of_rpow)
open LeanLab.HeathBrownPuchta.Decomp1530a (F)
open LeanLab.HeathBrownPuchta.Decomp1530c (Fzero Emodel Emodel_anti F_eq_Fzero)

/-! ## The sealed target -/

/-- Lemma 1 of Heath-Brown and Puchta in the form of Section 7, p. 30 to 31: the exponent
`E(λ) = ξλ/log 2 - log F(ξ, h)/(h log 2)`, with `F` at `β = 0`, `ρ = 1` as in display 44,
exceeds the GRH threshold `1/2` for some `ξ > 0` and `h ≥ 1`. -/
def LambdaGood (lam : ℝ) : Prop :=
  ∃ ξ : ℝ, 0 < ξ ∧ ∃ hh : ℕ, 0 < hh ∧ 1 / 2 < Emodel ξ lam (Fzero ξ hh) hh

/-- The `λ` this route needs, `0.7208`, against the paper's `0.722428`. -/
noncomputable def lam6 : ℝ := 7208 / 10000

/-- CONDITIONAL target, I-0129: `E(0.7208) > 1/2` from display 44 at some `h`. -/
def NeededInput : Prop := LambdaGood lam6

/-! ## Helpers, PROVED -/

theorem Fzero_pos (ξ : ℝ) (hh : ℕ) : 0 < Fzero ξ hh := by
  unfold Fzero
  apply mul_pos (by positivity)
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨0, by simp⟩

/-- `F(ξ, h) ≤ e^{ξh}` for `ξ ≥ 0`, since every cosine is at most 1. -/
theorem Fzero_le_exp {ξ : ℝ} (hξ : 0 ≤ ξ) (hh : ℕ) : Fzero ξ hh ≤ Real.exp (ξ * hh) := by
  unfold Fzero
  have hterm : ∀ r ∈ Finset.range (2 ^ hh),
      Real.exp (ξ * ∑ n ∈ Finset.range hh, Real.cos (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh))) ≤
        Real.exp (ξ * hh) := by
    intro r _
    apply Real.exp_le_exp.2
    apply mul_le_mul_of_nonneg_left _ hξ
    calc ∑ n ∈ Finset.range hh, Real.cos (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh))
        ≤ ∑ _n ∈ Finset.range hh, (1 : ℝ) := Finset.sum_le_sum fun n _ => Real.cos_le_one _
      _ = hh := by simp
  have hs := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have h2 : (0 : ℝ) < 2 ^ hh := by positivity
  calc 1 / 2 ^ hh * ∑ r ∈ Finset.range (2 ^ hh),
        Real.exp (ξ * ∑ n ∈ Finset.range hh, Real.cos (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh)))
      ≤ 1 / 2 ^ hh * (((2 ^ hh : ℕ) : ℝ) * Real.exp (ξ * hh)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = Real.exp (ξ * hh) := by push_cast; field_simp

/-- `LambdaGood` is monotone in `λ`. -/
theorem lambdaGood_mono {l1 l2 : ℝ} (hl : l1 ≤ l2) (h1 : LambdaGood l1) : LambdaGood l2 := by
  obtain ⟨ξ, hξ, hh, hhp, hE⟩ := h1
  refine ⟨ξ, hξ, hh, hhp, lt_of_lt_of_le hE ?_⟩
  unfold Emodel
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : ξ * l1 / Real.log 2 ≤ ξ * l2 / Real.log 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl hξ.le) hl2.le
  linarith

/-- Vacuity of `LambdaGood`: it holds at `λ = 2`, with `ξ = 1`, `h = 1`. -/
theorem lambdaGood_two : LambdaGood 2 := by
  refine ⟨1, one_pos, 1, one_pos, ?_⟩
  unfold Emodel
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' := Real.log_two_lt_d9
  have hF := Fzero_le_exp (ξ := 1) zero_le_one 1
  have hlog : Real.log (Fzero 1 1) ≤ 1 := by
    have := Real.log_le_log (Fzero_pos 1 1) hF
    simpa using this
  have e1 : Real.log (Fzero 1 1) / ((1 : ℕ) * Real.log 2) ≤ 1 / Real.log 2 := by
    rw [Nat.cast_one, one_mul]; exact div_le_div_of_nonneg_right hlog hl2.le
  have e2 : (1 : ℝ) * 2 / Real.log 2 - 1 / Real.log 2 = 1 / Real.log 2 := by ring
  have e3 : (1 : ℝ) / 2 < 1 / Real.log 2 := by
    rw [div_lt_div_iff₀ (by norm_num) hl2]; norm_num at hl2' ⊢; linarith
  linarith

/-! ## Section 6 with the new constants -/

/-- Lemma 9's minor constant with Johnston and Trudgian's `C₁ = 6.7814`, `C₂ ≤ 1.94`,
`C₀ ≥ 0.66016`, `0 ≤ ϖ ≤ 10⁻⁵`: at most `10.326`. -/
theorem C9_JT_le {C2 C0 w : ℝ} (hC2 : C2 ≤ 194 / 100) (hC0 : 66016 / 100000 ≤ C0)
    (hw0 : 0 ≤ w) (hw : w ≤ 1 / 100000) : C9 (67814 / 10000) C2 C0 w ≤ 10326 / 1000 := by
  unfold C9
  have l2 := Real.log_two_lt_d9
  norm_num at l2
  have hC0p : 0 < C0 := by linarith
  have h1 : Real.log 2 / C0 ≤ Real.log 2 / (66016 / 100000) :=
    div_le_div_of_nonneg_left (Real.log_pos (by norm_num)).le (by norm_num) hC0
  have h2 : Real.log 2 / (66016 / 100000) ≤ 108304247 / 156250000 / (66016 / 100000) :=
    div_le_div_of_nonneg_right l2.le (by norm_num)
  have h3 : (67814 / 10000 - 2 + 2 * w) * C2 ≤ (67814 / 10000 - 2 + 2 * w) * (194 / 100) :=
    mul_le_mul_of_nonneg_left hC2 (by linarith)
  nlinarith

/-- The new decision at `K = 6`: `10.326 · 0.7208^4 < 2.7895 (1 - 3 · 10⁻⁵)`. -/
theorem crit6_new : 10326 / 1000 * (7208 / 10000 : ℝ) ^ (6 - 2) <
    27895 / 10000 * (1 - 3 * (1 / 100000)) := by norm_num

/-- The paper's decision fails at `K = 6`: `13.968 · 0.722428^4 ≥ 2.7895`. -/
theorem crit6_hbp_fails : ¬ (13968 / 1000 * (722428 / 1000000 : ℝ) ^ (6 - 2) < 27895 / 10000) := by
  norm_num

/-- The new constants alone do not suffice at the paper's `λ`:
`10.309 · 0.722428^4 ≥ 2.7895`, `10.309` being below the true minor constant `10.3095`. -/
theorem crit6_jt_at_hbp_lam_fails :
    ¬ (10309 / 1000 * (722428 / 1000000 : ℝ) ^ (6 - 2) < 27895 / 10000) := by
  norm_num

/-- The analytic inputs of Sections 4 to 6 with `C₁ = 6.7814` and `C₂` the series (35). Same
shape as `Assembly.AnalyticInputs`; CONDITIONAL inputs, not proved here. -/
structure Inputs6 (K : ℕ) (lam θ E w : ℝ) where
  R : ℕ → ℝ
  maj : ℕ → ℝ
  mout : ℕ → ℝ
  minr : ℕ → ℝ
  X : ℕ → ℝ
  C2 : ℝ
  C0 : ℝ
  split : ∀ N, R N = maj N + mout N + minr N
  scale : ∃ c > 0, ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ≤ X N
  bound_C2 : C2 ≤ 194 / 100
  bound_C0 : 66016 / 100000 ≤ C0
  /-- Lemma 7 at this `K`. -/
  lemma7 : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, (27895 / 10000 * (1 - 3 * w) - ε) * X N ≤ maj N
  /-- Lemma 9 with Johnston and Trudgian's `C₁ = 6.7814` and `|T| < λL` off `𝒜_λ`. -/
  lemma9_out : ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
    |mout N| ≤ (C9 (67814 / 10000) C2 C0 w * lam ^ (K - 2) + ε) * X N
  /-- Lemma 1 with the sup bound `S ≪ N^{θ + o(1)}` on the minor arcs. -/
  lemma1_in : ∀ δ > 0, ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, |minr N| ≤ C * (N : ℝ) ^ (2 * θ - E + δ)

/-- ASSEMBLY, Section 6 with the new minor constant: the integral is eventually positive once
`10.326 λ^{K-2} < 2.7895 (1 - 3ϖ)` and `2θ - 1 < E`. CONDITIONAL ON the fields of `Inputs6`. -/
theorem section6_six {K : ℕ} {lam θ E w : ℝ} (I : Inputs6 K lam θ E w)
    (hw0 : 0 ≤ w) (hw : w ≤ 1 / 100000) (hlam : 0 ≤ lam) (hE : 2 * θ - 1 < E)
    (hcrit : 10326 / 1000 * lam ^ (K - 2) < 27895 / 10000 * (1 - 3 * w)) :
    ∀ᶠ N : ℕ in atTop, 0 < I.R N := by
  obtain ⟨c, hc, hX⟩ := I.scale
  set g := 27895 / 10000 * (1 - 3 * w) - 10326 / 1000 * lam ^ (K - 2) with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  have hC9 := C9_JT_le I.bound_C2 I.bound_C0 hw0 hw
  have hlk : 0 ≤ lam ^ (K - 2) := pow_nonneg hlam _
  set δ := (1 - (2 * θ - E)) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨C, hC⟩ := I.lemma1_in δ hδ0
  have hsmall := small_of_rpow (C := C) (b := 2 * θ - E + δ) (a := g / 4 * c)
    (by rw [hδ]; linarith) (by positivity)
  filter_upwards [I.lemma7 (g / 4) (by positivity), I.lemma9_out (g / 4) (by positivity), hC,
    hsmall, hX, eventually_gt_atTop 0] with N h7 h9 h1 hs hx hN0
  have hN0' : (0 : ℝ) < N := by exact_mod_cast hN0
  have hXp : 0 < I.X N := lt_of_lt_of_le (by positivity) hx
  have hX0 : 0 ≤ I.X N := hXp.le
  have e1 : C9 (67814 / 10000) I.C2 I.C0 w * lam ^ (K - 2) ≤ 10326 / 1000 * lam ^ (K - 2) :=
    mul_le_mul_of_nonneg_right hC9 hlk
  have h9' : -(I.mout N) ≤ (10326 / 1000 * lam ^ (K - 2) + g / 4) * I.X N := by
    have := neg_le_abs (I.mout N)
    have : (C9 (67814 / 10000) I.C2 I.C0 w * lam ^ (K - 2) + g / 4) * I.X N ≤
        (10326 / 1000 * lam ^ (K - 2) + g / 4) * I.X N :=
      mul_le_mul_of_nonneg_right (by linarith) hX0
    linarith
  have h1' : -(I.minr N) ≤ g / 4 * I.X N := by
    have := neg_le_abs (I.minr N)
    have : g / 4 * (c * N) ≤ g / 4 * I.X N := mul_le_mul_of_nonneg_left hx (by positivity)
    nlinarith
  rw [I.split N]
  have key : 0 < g / 4 * I.X N := by positivity
  have : (27895 / 10000 * (1 - 3 * w) - g / 4) * I.X N =
      (10326 / 1000 * lam ^ (K - 2) + g / 4) * I.X N + g / 4 * I.X N + g / 4 * I.X N := by
    rw [hg]; ring
  linarith

/-- ASSEMBLY with the circle method identity. CONDITIONAL ON `Inputs6` and `circle`. -/
theorem allLarge_six {K : ℕ} {lam θ E w : ℝ} (I : Inputs6 K lam θ E w)
    (circle : ∀ N, 0 < I.R N → LinnikExact K N)
    (hw0 : 0 ≤ w) (hw : w ≤ 1 / 100000) (hlam : 0 ≤ lam) (hE : 2 * θ - 1 < E)
    (hcrit : 10326 / 1000 * lam ^ (K - 2) < 27895 / 10000 * (1 - 3 * w)) :
    AllLargeEven (LinnikExact K) := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (section6_six I hw0 hw hlam hE hcrit)
  exact ⟨N0, fun N _ hN => circle N (hN0 N hN.le)⟩

/-- `K6_of_input`, CONDITIONAL ON `NeededInput`, on the GRH analytic inputs `Inputs6` at
`λ = 0.7208`, `θ = 3/4` for every `E` below the display 44 exponent, on `circle`, and through
`F_eq_Fzero` on the leaves of Decomp1530a: every large even `N` is two primes and exactly six
powers of 2. -/
theorem K6_of_input (hin : NeededInput)
    (I : ∀ (ξ : ℝ) (hh : ℕ) (E : ℝ), 0 < ξ → 0 < hh → E < Emodel ξ lam6 (F ξ hh) hh →
      Inputs6 6 lam6 (3 / 4) E (1 / 100000))
    (circle : ∀ ξ hh E (hξ : 0 < ξ) (hhp : 0 < hh) (hE : E < Emodel ξ lam6 (F ξ hh) hh) N,
      0 < (I ξ hh E hξ hhp hE).R N → LinnikExact 6 N) :
    AllLargeEven (LinnikExact 6) := by
  obtain ⟨ξ, hξ, hh, hhp, hE⟩ := hin
  rw [← F_eq_Fzero hξ.le hh] at hE
  set E0 := Emodel ξ lam6 (F ξ hh) hh with hE0
  have hlt : (1 / 2 + E0) / 2 < E0 := by linarith
  refine allLarge_six (I ξ hh _ hξ hhp hlt) (circle ξ hh _ hξ hhp hlt) (by norm_num) le_rfl
    (by unfold lam6; norm_num) (by linarith) ?_
  unfold lam6; exact crit6_new

open Finset LeanLab.HeathBrownPuchta.Decomp1530c in
/-- A rational certificate for display 44 at any level within the exponential envelope.
Source: Heath-Brown and Puchta 2002, page 30. The existing task177 envelopes apply
when the absolute exponential argument is at most 32. -/
theorem Fzero_le_Fupper191 (ξ : ℚ) (hξ : 0 ≤ ξ) (hh : ℕ)
    (hargBound : (ξ : ℝ) * hh * (1001 / 1000) ≤ 32) :
    Fzero (ξ : ℝ) hh ≤ (Fupper177 ξ hh : ℝ) := by
  have hξ' : (0 : ℝ) ≤ ξ := by exact_mod_cast hξ
  have hpos : 0 < 2^hh := by positivity
  have hpoint (r : ℕ) :
      Real.exp ((ξ : ℝ) * ∑ n ∈ range hh, Real.cos (2 * π * ((r : ℝ) * 2^n / 2^hh))) ≤
        (expUpper177 (ξ * ∑ n ∈ range hh, cosUpper177 (2^hh) (r * 2^n)) : ℝ) := by
    let s : ℚ := ∑ n ∈ range hh, cosUpper177 (2^hh) (r * 2^n)
    have hsum : |(s : ℝ)| ≤ (hh : ℝ) * (1001/1000) := by
      change |((∑ n ∈ range hh, cosUpper177 (2^hh) (r * 2^n) : ℚ) : ℝ)| ≤ _
      rw [Rat.cast_sum]
      calc
        _ ≤ ∑ n ∈ range hh, |(cosUpper177 (2^hh) (r * 2^n) : ℝ)| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ range hh, (1001/1000 : ℝ) := sum_le_sum fun n hn => (cosUpper_bounds177 _ _ hpos).2
        _ = _ := by simp
    have harg : |((ξ * s : ℚ) : ℝ)| ≤ 32 := by
      rw [Rat.cast_mul, abs_mul, abs_of_nonneg hξ']
      calc (ξ : ℝ) * |(s : ℝ)| ≤ (ξ : ℝ) * ((hh : ℝ) * (1001/1000)) :=
          mul_le_mul_of_nonneg_left hsum hξ'
        _ ≤ 32 := by nlinarith [hargBound]
    apply le_trans _ (expUpper_bound177 (ξ * s) harg)
    apply Real.exp_le_exp.mpr
    rw [Rat.cast_mul, Rat.cast_sum]
    apply mul_le_mul_of_nonneg_left _ hξ'
    apply sum_le_sum
    intro n hn
    convert (cosUpper_bounds177 (2^hh) (r * 2^n) hpos).1 using 1
    congr 1
    push_cast
    ring
  unfold Fzero Fupper177
  push_cast
  rw [one_div_mul_eq_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact sum_le_sum fun r hr => hpoint r

/-- The maximum cosine estimate is too large for both display 44 targets.
Source: Heath-Brown and Puchta 2002, page 30. This records an estimate obstruction. -/
theorem crude_Fzero_bounds_too_large :
    (80905 / 100 : ℝ) < Real.exp ((9031 / 10000) * 22) ∧
      (146005 / 100 : ℝ) < Real.exp ((9025 / 10000) * 24) := by
  constructor
  · have ht := Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (9031 / 10000) * 22 by norm_num) 4
    have hs : (80905 / 100 : ℝ) <
        ∑ i ∈ Finset.range 4, ((9031 / 10000 : ℝ) * 22) ^ i / i.factorial := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact hs.trans_le ht
  · have ht := Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (9025 / 10000) * 24 by norm_num) 4
    have hs : (146005 / 100 : ℝ) <
        ∑ i ∈ Finset.range 4, ((9025 / 10000 : ℝ) * 24) ^ i / i.factorial := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact hs.trans_le ht

open Finset LeanLab.HeathBrownPuchta.Decomp1530c in
/-- Reflection halves the rational certificate sum in display 44.
Source: Heath-Brown and Puchta 2002, page 30. The endpoints remain separate. -/
theorem Fupper_half191 (ξ : ℚ) (hh : ℕ) :
    let f := fun r => expUpper177 (ξ *
      ∑ n ∈ range (hh + 1), cosUpper177 (2 ^ (hh + 1)) (r * 2 ^ n))
    Fupper177 ξ (hh + 1) =
      (f 0 + f (2 ^ hh) + 2 * ∑ r ∈ range (2 ^ hh - 1), f (r + 1)) / 2 ^ (hh + 1) := by
  let f := fun r => expUpper177 (ξ *
    ∑ n ∈ range (hh + 1), cosUpper177 (2 ^ (hh + 1)) (r * 2 ^ n))
  change (∑ r ∈ range (2 ^ (hh + 1)), f r) / 2 ^ (hh + 1) = _
  have hsym : ∀ r ≤ 2 * 2 ^ hh, f (2 * 2 ^ hh - r) = f r := by
    intro r hr
    have he : 2 * 2 ^ hh = 2 ^ (hh + 1) := by ring
    rw [he] at hr ⊢
    dsimp [f]
    congr 1
    congr 1
    exact sum_congr rfl fun n _ => cosUpper_reflect177 _ r (2 ^ n) hr
  have hs := sum_half177 f (2 ^ hh) (by positivity) hsym
  rw [show 2 * 2 ^ hh = 2 ^ (hh + 1) by ring] at hs
  rw [hs]

/-- The first sixteen exponential series terms. Source: display 44 proof, page 30. -/
noncomputable def expTaylor16_191 (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range 16, z ^ j / (j.factorial : ℂ)

/-- Squared norms of the exponential and its Taylor polynomial differ by at most 10^-16
on the half unit disk. A lab error certificate for the exponential series on page 30. -/
theorem expTaylor16_sq_error191 {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    |‖Complex.exp z‖ ^ 2 - ‖expTaylor16_191 z‖ ^ 2| ≤ 1 / 10 ^ 16 := by
  have hb := Complex.exp_bound (x := z) (by linarith : ‖z‖ ≤ 1) (n := 16) (by norm_num)
  have he : ‖Complex.exp z - expTaylor16_191 z‖ ≤ 1 / 10 ^ 18 := by
    apply hb.trans
    calc ‖z‖ ^ 16 * ((16 + 1 : ℕ) / ((Nat.factorial 16 : ℝ) * 16))
        ≤ (1 / 2 : ℝ) ^ 16 * ((16 + 1 : ℕ) / ((Nat.factorial 16 : ℝ) * 16)) := by gcongr
      _ ≤ 1 / 10 ^ 18 := by norm_num
  have hx : ‖Complex.exp z‖ ≤ 2 := by
    calc ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := Complex.norm_exp_le_exp_norm z
      _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hz
      _ ≤ 2 := by
        have ht := Real.exp_bound_div_one_sub_of_interval
          (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
        norm_num at ht
        exact ht
  have hp : ‖expTaylor16_191 z‖ ≤ 3 := by
    calc ‖expTaylor16_191 z‖ = ‖(expTaylor16_191 z - Complex.exp z) + Complex.exp z‖ := by congr 1; ring
      _ ≤ ‖expTaylor16_191 z - Complex.exp z‖ + ‖Complex.exp z‖ := norm_add_le _ _
      _ ≤ 3 := by rw [norm_sub_rev]; linarith
  have hd : |‖Complex.exp z‖ - ‖expTaylor16_191 z‖| ≤ 1 / 10 ^ 18 :=
    (abs_norm_sub_norm_le _ _).trans he
  calc |‖Complex.exp z‖ ^ 2 - ‖expTaylor16_191 z‖ ^ 2|
      = |‖Complex.exp z‖ - ‖expTaylor16_191 z‖| * (‖Complex.exp z‖ + ‖expTaylor16_191 z‖) := by
        rw [← abs_of_nonneg (show 0 ≤ ‖Complex.exp z‖ + ‖expTaylor16_191 z‖ by positivity), ← abs_mul]
        congr 1
        ring
    _ ≤ (1 / 10 ^ 18) * 5 := by gcongr; linarith
    _ ≤ 1 / 10 ^ 16 := by norm_num

/-- Integer coefficients for the positive degree 15 exponential Taylor polynomial.
The common denominator is 20000^15 times 15 factorial. Lab certificate for page 30. -/
def carryCoeffs191 (num : ℕ) : Array ℕ :=
  Array.ofFn fun j : Fin 16 => num ^ j.val * 20000 ^ (15 - j.val) *
    (Nat.factorial 15 / Nat.factorial j.val)

/-- The integer convolution coefficients of the Taylor polynomial and its reflected copy.
Index t represents Fourier exponent t minus 15. Lab certificate for pages 30 and 31. -/
def carryWeights191 (num : ℕ) : Array ℕ :=
  let a := carryCoeffs191 num
  Array.ofFn fun t : Fin 31 => ∑ j ∈ Finset.range 16,
    if t.val ≤ j + 15 ∧ j ≤ t.val then
      a[j]?.getD 0 * a[j + 15 - t.val]?.getD 0 else 0

/-- A binary carry step on the 31 states from minus 15 to 15.
Only Fourier exponents with the required even parity contribute. Lab certificate for page 31. -/
def carryStep191 (w v : Array ℕ) : Array ℕ :=
  Array.ofFn fun j : Fin 31 => ∑ i ∈ Finset.range 31,
    if i ≤ 2 * j.val ∧ 2 * j.val ≤ i + 30 then
      v[i]?.getD 0 * w[2 * j.val - i]?.getD 0 else 0

/-- Iterate binary carry steps from the unit mass at carry zero.
This is finite integer recurrence data for the dyadic average on page 30. -/
def carryRows191 (w : Array ℕ) : ℕ → Array ℕ
  | 0 => Array.ofFn fun i : Fin 31 => if i.val = 15 then 1 else 0
  | h + 1 => carryStep191 w (carryRows191 w h)

/-- The total integer mass after h carry steps for the indicated Taylor numerator.
The normalization is carryDen191 to the h. Lab certificate data for display 44. -/
def carryTotal191 (num h : ℕ) : ℕ := (carryRows191 (carryWeights191 num) h).foldl (· + ·) 0

/-- The squared common denominator of the positive Taylor coefficients.
Lab normalization for the polynomial certificate of display 44. -/
def carryDen191 : ℕ := (20000 ^ 15 * Nat.factorial 15) ^ 2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The h = 22 integer carry recurrence fits the required bound, including the product error.
A lab finite certificate for Heath-Brown and Puchta 2002, display 44, page 30.
This is arithmetic only. The Fourier transfer to Fzero is not asserted here. -/
theorem carry22_certificate191 :
    (carryTotal191 9031 22 : ℚ) / (carryDen191 : ℚ) ^ 22 +
      22 * 3 ^ 22 / 10 ^ 16 ≤ 80905 / 100 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The h = 24 integer carry recurrence fits the required bound, including the product error.
A lab finite certificate for Heath-Brown and Puchta 2002, display 44, page 30.
This is arithmetic only. The Fourier transfer to Fzero is not asserted here. -/
theorem carry24_certificate191 :
    (carryTotal191 9025 24 : ℚ) / (carryDen191 : ℚ) ^ 24 +
      24 * 3 ^ 24 / 10 ^ 16 ≤ 146005 / 100 := by
  decide +kernel

open Finset in
/-- Bounded nonnegative factors propagate a uniform error through a finite product.
This lab helper controls the Taylor products for display 44 on page 30. -/
theorem product_error191 (a b : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ 3) (hb : ∀ n, 0 ≤ b n ∧ b n ≤ 3)
    (hd : ∀ n, |a n - b n| ≤ δ) (h : ℕ) :
    |(∏ n ∈ range h, a n) - ∏ n ∈ range h, b n| ≤ (h : ℝ) * δ * 3 ^ h := by
  induction h with
  | zero => simp
  | succ h ih =>
    let A := ∏ n ∈ range h, a n
    let B := ∏ n ∈ range h, b n
    have hB0 : 0 ≤ B := prod_nonneg fun n _ => (hb n).1
    have hB3 : B ≤ 3 ^ h := by
      calc B ≤ ∏ _n ∈ range h, (3 : ℝ) :=
          prod_le_prod₀ (fun n _ => (hb n).1) (fun n _ => (hb n).2)
        _ = 3 ^ h := by simp
    have ha0 := (ha h).1
    have ha3 := (ha h).2
    have hd' := hd h
    rw [prod_range_succ, prod_range_succ]
    change |A * a h - B * b h| ≤ _
    rw [show A * a h - B * b h = (A - B) * a h + B * (a h - b h) by ring]
    calc |(A - B) * a h + B * (a h - b h)|
        ≤ |(A - B) * a h| + |B * (a h - b h)| := abs_add_le _ _
      _ = |A - B| * a h + B * |a h - b h| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hB0]
      _ ≤ ((h : ℝ) * δ * 3 ^ h) * 3 + 3 ^ h * δ := by
        dsimp [A, B]
        gcongr
      _ ≤ ((h + 1 : ℕ) : ℝ) * δ * 3 ^ (h + 1) := by
        rw [Nat.cast_add, Nat.cast_one, pow_succ]
        nlinarith [mul_nonneg hδ (show (0 : ℝ) ≤ 3 ^ h by positivity)]

/-- Each cosine exponential factor is approximated by the squared Taylor norm
with error at most 10^-16 for xi between 0 and 1. Source: display 44, page 30. -/
theorem exp_cos_taylor_error191 {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (θ : ℝ) :
    |Real.exp (ξ * Real.cos θ) -
      ‖expTaylor16_191 (((ξ / 2 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2| ≤
      1 / 10 ^ 16 := by
  let z : ℂ := ((ξ / 2 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
  have hz : ‖z‖ ≤ 1 / 2 := by
    dsimp [z]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ ξ / 2 by positivity)] using
      (show ξ / 2 ≤ (1 / 2 : ℝ) by linarith)
  have he := expTaylor16_sq_error191 hz
  have heq : ‖Complex.exp z‖ ^ 2 = Real.exp (ξ * Real.cos θ) := by
    rw [Complex.norm_exp, pow_two, ← Real.exp_add]
    congr 1
    dsimp [z]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.exp_ofReal_mul_I_re]
    ring
  rw [heq] at he
  exact he

/-- The nonnegative squared norm Taylor factor for display 44 on page 30. -/
noncomputable def polynomialFactor191 (ξ θ : ℝ) : ℝ :=
  ‖expTaylor16_191 (((ξ / 2 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2

open Finset in
/-- The dyadic average of the Taylor factor products.
This is the finite polynomial approximation to display 44 on page 30. -/
noncomputable def polynomialAverage191 (ξ : ℝ) (hh : ℕ) : ℝ :=
  1 / 2 ^ hh * ∑ r ∈ range (2 ^ hh),
    ∏ n ∈ range hh, polynomialFactor191 ξ (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh))

open Finset in
/-- The Taylor product average bounds Fzero with an explicit accumulated error.
Source: Heath-Brown and Puchta 2002, display 44, page 30. -/
theorem Fzero_le_polynomialAverage191 {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (hh : ℕ) :
    Fzero ξ hh ≤ polynomialAverage191 ξ hh + (hh : ℝ) * (1 / 10 ^ 16) * 3 ^ hh := by
  have hpoint (r : ℕ) :
      Real.exp (ξ * ∑ n ∈ range hh, Real.cos (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh))) ≤
        (∏ n ∈ range hh, polynomialFactor191 ξ (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh))) +
          (hh : ℝ) * (1 / 10 ^ 16) * 3 ^ hh := by
    let θ := fun n : ℕ => 2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh)
    let a := fun n : ℕ => Real.exp (ξ * Real.cos (θ n))
    let b := fun n : ℕ => polynomialFactor191 ξ (θ n)
    have ha : ∀ n, 0 ≤ a n ∧ a n ≤ 14 / 5 := by
      intro n
      have harg : ξ * Real.cos (θ n) ≤ 1 := by
        have ht := mul_le_mul_of_nonneg_left (Real.cos_le_one (θ n)) hξ0
        nlinarith
      have he := Real.exp_le_exp.mpr harg
      have he1 := Real.exp_one_lt_d9
      norm_num at he1
      exact ⟨(Real.exp_pos _).le, by dsimp [a]; linarith⟩
    have hd : ∀ n, |a n - b n| ≤ 1 / 10 ^ 16 := by
      intro n
      exact exp_cos_taylor_error191 hξ0 hξ1 (θ n)
    have hb : ∀ n, 0 ≤ b n ∧ b n ≤ 3 := by
      intro n
      have he := (abs_le.mp (hd n)).1
      have he1 := (ha n).2
      refine ⟨by dsimp [b, polynomialFactor191]; positivity, ?_⟩
      linarith
    have he := product_error191 a b (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 16)
      (fun n => ⟨(ha n).1, (ha n).2.trans (by norm_num)⟩) hb hd hh
    have hprod : (∏ n ∈ range hh, a n) =
        Real.exp (ξ * ∑ n ∈ range hh, Real.cos (θ n)) := by
      dsimp [a]
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
    rw [hprod] at he
    have he' := (abs_le.mp he).2
    change Real.exp (ξ * ∑ n ∈ range hh, Real.cos (θ n)) ≤
      (∏ n ∈ range hh, b n) + (hh : ℝ) * (1 / 10 ^ 16) * 3 ^ hh
    linarith
  unfold Fzero polynomialAverage191
  have hs := sum_le_sum (s := range (2 ^ hh)) (fun r _ => hpoint r)
  have h2 : (0 : ℝ) < 2 ^ hh := by positivity
  calc 1 / 2 ^ hh * ∑ r ∈ range (2 ^ hh),
        Real.exp (ξ * ∑ n ∈ range hh, Real.cos (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh)))
      ≤ 1 / 2 ^ hh * ∑ r ∈ range (2 ^ hh),
        ((∏ n ∈ range hh, polynomialFactor191 ξ (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh))) +
          (hh : ℝ) * (1 / 10 ^ 16) * 3 ^ hh) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by
      rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_add]
      push_cast
      field_simp

/-- LEAF. Heath-Brown and Puchta 2002, display 44 on page 30 and the power of two
congruence constraint below display 46 on page 31. The dyadic average of the finite
Taylor products equals the integer carry recurrence divided by its common denominator.
This is a lab encoding of the finite Fourier orthogonality step. All final carries are summed. -/
theorem polynomialAverage_eq_carry191 (num hh : ℕ) :
    polynomialAverage191 ((num : ℝ) / 10000) hh =
      (carryTotal191 num hh : ℝ) / (carryDen191 : ℝ) ^ hh := by
  sorry

/-! ## Leaves toward `NeededInput` -/

/-- LEAF. Unit U-1554. Heath-Brown and Puchta 2002, display 44, p. 30, at `h = 22`:
`F(0.9031, 22) = 2^{-22} Σ_{r < 2^22} exp(0.9031 Σ_{n < 22} cos(2π r 2^n/2^22)) ≤ 809.05`,
numpy value `809.0484869`. -/
theorem Fzero22_le : Fzero (9031 / 10000) 22 ≤ 80905 / 100 := by
  have hb := Fzero_le_polynomialAverage191 (ξ := 9031 / 10000)
    (by norm_num) (by norm_num) 22
  have hi := polynomialAverage_eq_carry191 9031 22
  simp only [Nat.cast_ofNat] at hi
  rw [hi] at hb
  have hc := (Rat.cast_le (K := ℝ)).mpr carry22_certificate191
  simp only [Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] at hc
  have hc' : (carryTotal191 9031 22 : ℝ) / (carryDen191 : ℝ) ^ 22 +
      (22 : ℝ) * (1 / 10 ^ 16) * 3 ^ 22 ≤ 80905 / 100 := by
    convert hc using 1 <;> ring
  exact hb.trans hc'

/-- LEAF. Unit U-1554. Heath-Brown and Puchta 2002, Section 7, p. 30:
`0.9031 · 0.7208/log 2 - log 809.05/(22 log 2) > 1/2 + 10^-5`, double precision margin
about `3.4e-5`. -/
theorem E22_num : 1 / 2 + 1 / 10 ^ 5 < Emodel (9031 / 10000) (7208 / 10000) (80905 / 100) 22 := by
  unfold Emodel
  norm_num only [Nat.cast_ofNat]
  have hl : Real.log (80905 / 100) < (66959 / 10000 : ℝ) := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    have ht := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 66959 / 10000 by norm_num) 32
    have hs : (80905 / 100 : ℝ) <
        ∑ i ∈ Finset.range 32, (66959 / 10000 : ℝ) ^ i / i.factorial := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact hs.trans_le ht
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb := Real.log_two_lt_d9
  have he : (1 / 2 + 1 / 10 ^ 5 : ℝ) * (22 * Real.log 2) <
      22 * (9031 / 10000) * (7208 / 10000) - Real.log (80905 / 100) := by nlinarith
  have hd := (lt_div_iff₀ (show 0 < 22 * Real.log 2 by positivity)).mpr he
  convert hd using 1 <;> norm_num <;> field_simp <;> ring

/-- LEAF. Unit U-1554. Heath-Brown and Puchta 2002, display 44, p. 30, at `h = 24`:
`F(0.9025, 24) ≤ 1460.05`, numpy value `1460.0441809`. -/
theorem Fzero24_le : Fzero (9025 / 10000) 24 ≤ 146005 / 100 := by
  have hb := Fzero_le_polynomialAverage191 (ξ := 9025 / 10000)
    (by norm_num) (by norm_num) 24
  have hi := polynomialAverage_eq_carry191 9025 24
  simp only [Nat.cast_ofNat] at hi
  rw [hi] at hb
  have hc := (Rat.cast_le (K := ℝ)).mpr carry24_certificate191
  simp only [Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] at hc
  have hc' : (carryTotal191 9025 24 : ℝ) / (carryDen191 : ℝ) ^ 24 +
      (24 : ℝ) * (1 / 10 ^ 16) * 3 ^ 24 ≤ 146005 / 100 := by
    convert hc using 1 <;> ring
  exact hb.trans hc'

/-- LEAF. Unit U-1554. Heath-Brown and Puchta 2002, Section 7, p. 30:
`0.9025 · 0.7208/log 2 - log 1460.05/(24 log 2) > 1/2 + 10^-4`, double precision margin
about `5.1e-4`. -/
theorem E24_num :
    1 / 2 + 1 / 10 ^ 4 < Emodel (9025 / 10000) (7208 / 10000) (146005 / 100) 24 := by
  unfold Emodel
  norm_num only [Nat.cast_ofNat]
  have hl : Real.log (146005 / 100) < (72863 / 10000 : ℝ) := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    have ht := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 72863 / 10000 by norm_num) 32
    have hs : (146005 / 100 : ℝ) <
        ∑ i ∈ Finset.range 32, (72863 / 10000 : ℝ) ^ i / i.factorial := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact hs.trans_le ht
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb := Real.log_two_lt_d9
  have he : (1 / 2 + 1 / 10 ^ 4 : ℝ) * (24 * Real.log 2) <
      24 * (9025 / 10000) * (7208 / 10000) - Real.log (146005 / 100) := by nlinarith
  have hd := (lt_div_iff₀ (show 0 < 24 * Real.log 2 by positivity)).mpr he
  convert hd using 1 <;> norm_num <;> field_simp <;> ring

/-- LEAF. Unit U-1554. Heath-Brown and Puchta 2002, Section 7, p. 29, `T_{h+1}(α) = e(α) +
T_h(2α)` at `α = r/2^{h+1}`, real parts: the cosine sum at level `h + 1` is
`cos(2π r/2^{h+1})` plus the cosine sum at level `h`. Used to compute display 44 recursively. -/
theorem reT_succ (hh r : ℕ) :
    ∑ n ∈ Finset.range (hh + 1), Real.cos (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ (hh + 1))) =
      Real.cos (2 * π * ((r : ℝ) / 2 ^ (hh + 1))) +
        ∑ n ∈ Finset.range hh, Real.cos (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh)) := by
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  rw [pow_succ, pow_succ]
  field_simp

/-- LEAF. Unit U-1554. Heath-Brown and Puchta 2002, display 44, p. 30, the symmetry
`r ↦ 2^h - r`: for `r ≤ 2^h` the cosine sums at `r` and `2^h - r` agree, halving the work. -/
theorem reT_reflect (hh r : ℕ) (hr : r ≤ 2 ^ hh) :
    ∑ n ∈ Finset.range hh, Real.cos (2 * π * (((2 ^ hh - r : ℕ) : ℝ) * 2 ^ n / 2 ^ hh)) =
      ∑ n ∈ Finset.range hh, Real.cos (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh)) := by
  apply Finset.sum_congr rfl
  intro n _
  rw [Nat.cast_sub hr, Nat.cast_pow, Nat.cast_ofNat]
  have hangle : 2 * π * ((2 ^ hh - (r : ℝ)) * 2 ^ n / 2 ^ hh) =
      (2 ^ n : ℕ) * (2 * π) - 2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh) := by
    push_cast
    field_simp
  rw [hangle, Real.cos_nat_mul_two_pi_sub]

/-- LEAF. Unit U-1554. Heath-Brown and Puchta 2002, (35) and (36), p. 21: the series
`C₂ = Σ_d k(d)/ε(d)` converges. -/
theorem C2_summable :
    Summable fun d : ℕ => (LeanLab.HeathBrownPuchta.Lemma8Const.k d : ℝ) /
      LeanLab.HeathBrownPuchta.Lemma8Const.eps d := by
  exact LeanLab.Romanov.hbp_C2_summable

/-- Cited, not proved in the lab: Pintz and Ruzsa 2003, part I, Lemma 4, the constant
`Σ' f(d)/ξ(d) < 1.94`, which is Heath-Brown and Puchta's `C₂` of (35), p. 21. -/
theorem pintzRuzsa_C2_le : LeanLab.HeathBrownPuchta.Lemma8Const.C2 ≤ 194 / 100 := by
  sorry

/-- ASSEMBLY, CONDITIONAL ON `Fzero22_le` and `E22_num`: `NeededInput` at `h = 22`. -/
theorem neededInput_of_h22 : NeededInput := by
  refine ⟨9031 / 10000, by norm_num, 22, by norm_num, ?_⟩
  have h := Emodel_anti (ξ := 9031 / 10000) (lam := lam6) (hh := 22) (by norm_num) (Fzero_pos _ 22) Fzero22_le
  have h2 := E22_num
  unfold lam6 at h ⊢
  linarith

/-- ASSEMBLY, CONDITIONAL ON `Fzero24_le` and `E24_num`: `NeededInput` at `h = 24`. -/
theorem neededInput_of_h24 : NeededInput := by
  refine ⟨9025 / 10000, by norm_num, 24, by norm_num, ?_⟩
  have h := Emodel_anti (ξ := 9025 / 10000) (lam := lam6) (hh := 24) (by norm_num) (Fzero_pos _ 24) Fzero24_le
  have h2 := E24_num
  unfold lam6 at h ⊢
  linarith

/-! ## Vacuity of `Inputs6` -/

/-- Vacuity: a model of `Inputs6` at `K = 6`, `λ = 0.7208`, `θ = 3/4`, `E = 1`, `ϖ = 0`. -/
noncomputable def inputs6_consistent : Inputs6 6 lam6 (3 / 4) 1 0 where
  R N := 3 * N
  maj N := 3 * N
  mout _ := 0
  minr _ := 0
  X N := N
  C2 := 194 / 100
  C0 := 1
  split N := by ring
  scale := ⟨1, one_pos, Eventually.of_forall fun N => by simp⟩
  bound_C2 := le_rfl
  bound_C0 := by norm_num
  lemma7 ε hε := Eventually.of_forall fun N => by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  lemma9_out ε hε := Eventually.of_forall fun N => by
    simp only [abs_zero]
    have hC : 0 ≤ C9 (67814 / 10000) (194 / 100) 1 0 := by
      unfold C9; have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
    have : 0 ≤ lam6 ^ (6 - 2) := by unfold lam6; positivity
    exact mul_nonneg (by nlinarith [mul_nonneg hC this]) (Nat.cast_nonneg N)
  lemma1_in δ hδ := ⟨0, Eventually.of_forall fun N => by simp⟩

theorem consistent6_positive : ∀ᶠ N : ℕ in atTop, 0 < inputs6_consistent.R N := by
  filter_upwards [eventually_gt_atTop 0] with N hN
  show (0 : ℝ) < 3 * N
  have : (0 : ℝ) < N := by exact_mod_cast hN
  linarith

end LeanLab.Routes.U1554LinnikGRH
