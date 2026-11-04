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

/-! ## Proof of `polynomialAverage_eq_carry191`

The Taylor product is expanded over tuples of Taylor indices, the dyadic average is evaluated by
orthogonality of the `2^hh`-th roots of unity, and the surviving tuples are counted by the binary
carry recurrence of `carryRows191`. No new declaration is introduced: every quantity below is
written out in full, and the helper lemmas are `private` and sit directly above their users.
-/

section PolynomialAverageCarry191

set_option quotPrecheck false

open Finset


private lemma twopi_ne : ((2 * (Real.pi : ℂ) * Complex.I)) ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
  simp [hpi, Complex.I_ne_zero]

/-- Orthogonality of the `N`-th roots of unity (display 44, page 30). -/
private theorem sum_exp_orthog (T : ℤ) {N : ℕ} (hN : 0 < N) :
    ∑ r ∈ Finset.range N, Complex.exp (((2 * (Real.pi : ℂ) * Complex.I)) * (r : ℂ) * (T : ℂ) / (N : ℂ)) =
      if (N : ℤ) ∣ T then (N : ℂ) else 0 := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set w : ℂ := Complex.exp (((2 * (Real.pi : ℂ) * Complex.I)) * (T : ℂ) / (N : ℂ)) with hwdef
  have hterm : ∀ r : ℕ, Complex.exp (((2 * (Real.pi : ℂ) * Complex.I)) * (r : ℂ) * (T : ℂ) / (N : ℂ)) = w ^ r := by
    intro r
    rw [hwdef, ← Complex.exp_nat_mul]
    congr 1
    field_simp
  rw [Finset.sum_congr rfl fun r _ => hterm r]
  by_cases hd : (N : ℤ) ∣ T
  · rw [if_pos hd]
    obtain ⟨m, hm⟩ := hd
    have hw1 : w = 1 := by
      rw [hwdef, Complex.exp_eq_one_iff]
      refine ⟨m, ?_⟩
      rw [hm]
      push_cast
      field_simp
    rw [hw1]
    simp
  · rw [if_neg hd]
    have hwN : w ^ N = 1 := by
      rw [← hterm N]
      have h : ((2 * (Real.pi : ℂ) * Complex.I)) * (N : ℂ) * (T : ℂ) / (N : ℂ) = (T : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I)) := by
        field_simp
      rw [h]
      simpa using Complex.exp_int_mul_two_pi_mul_I T
    have hw1 : w ≠ 1 := by
      intro h
      apply hd
      rw [hwdef, Complex.exp_eq_one_iff] at h
      obtain ⟨m, hm⟩ := h
      have h2 : ((2 * (Real.pi : ℂ) * Complex.I)) * ((T : ℂ) / (N : ℂ)) = (m : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I)) := by
        rw [← mul_div_assoc, hm]
      have h2' : ((T : ℂ) / (N : ℂ)) * ((2 * (Real.pi : ℂ) * Complex.I)) = (m : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I)) := by
        rw [mul_comm ((T : ℂ) / (N : ℂ)), h2, mul_comm]
      have h1 : (T : ℂ) / (N : ℂ) = (m : ℂ) := mul_right_cancel₀ twopi_ne h2'
      have h3 : (T : ℂ) = (m : ℂ) * (N : ℂ) := by
        rw [div_eq_iff hNc] at h1
        linear_combination h1
      refine ⟨m, ?_⟩
      have h4 : T = m * (N : ℤ) := by exact_mod_cast h3
      rw [h4]; ring
    have hgs := geom_sum_mul w N
    rw [hwN, sub_self] at hgs
    rcases mul_eq_zero.mp hgs with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hw1

/-! ## The Taylor factor as a double sum over exponents -/


/-- Exponent sums attached to a tuple of pairs of Taylor indices. -/



private theorem expTaylor16_eq_sum (ξ θ : ℝ) :
    expTaylor16_191 (((ξ / 2 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      ∑ j ∈ Finset.range 16, (((((ξ / 2) ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) : ℝ)) : ℂ) *
        Complex.exp (((j : ℂ) * (θ : ℂ)) * Complex.I) := by
  unfold expTaylor16_191
  refine Finset.sum_congr rfl fun j hj => ?_
  have hcpow : ((((ξ / 2 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ j)
      = (((ξ / 2) ^ j : ℝ) : ℂ) * Complex.exp (((j : ℂ) * (θ : ℂ)) * Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast
    congr 2
    ring
  have hcj : (((((ξ / 2) ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) : ℝ)) : ℂ) = (((ξ / 2) ^ j : ℝ) : ℂ) / ((j.factorial : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcpow, hcj]
  push_cast
  field_simp

/-- The squared Taylor factor as a double sum of exponentials (display 44). -/
private theorem pfac_cast (ξ θ : ℝ) :
    ((polynomialFactor191 ξ θ : ℝ) : ℂ) =
      ∑ jk : Fin 16 × Fin 16, ((((((ξ / 2) ^ (jk.1 : ℕ) / (Nat.factorial (jk.1 : ℕ) : ℝ)) : ℝ)) * ((((ξ / 2) ^ (jk.2 : ℕ) / (Nat.factorial (jk.2 : ℕ) : ℝ)) : ℝ)) : ℝ) : ℂ) *
        Complex.exp ((((jk.1 : ℂ) - (jk.2 : ℂ)) * (θ : ℂ)) * Complex.I) := by
  unfold polynomialFactor191
  set w : ℂ := expTaylor16_191 (((ξ / 2 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) with hwdef
  have hbridge : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * (starRingEnd ℂ) w := by
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [hbridge]
  have hsum : w = ∑ j : Fin 16, (((((ξ / 2) ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) : ℝ)) : ℂ) *
      Complex.exp (((j : ℂ) * (θ : ℂ)) * Complex.I) := by
    rw [hwdef, expTaylor16_eq_sum,
      ← Fin.sum_univ_eq_sum_range (fun j : ℕ => (((((ξ / 2) ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) : ℝ)) : ℂ) *
        Complex.exp (((j : ℂ) * (θ : ℂ)) * Complex.I))]
  rw [hsum]
  have hconj : ∀ k : Fin 16, (starRingEnd ℂ) ((((((ξ / 2) ^ (k : ℕ) / (Nat.factorial (k : ℕ) : ℝ)) : ℝ)) : ℂ) *
      Complex.exp (((k : ℂ) * (θ : ℂ)) * Complex.I))
      = (((((ξ / 2) ^ (k : ℕ) / (Nat.factorial (k : ℕ) : ℝ)) : ℝ)) : ℂ) * Complex.exp ((-((k : ℂ) * (θ : ℂ))) * Complex.I) := by
    intro k
    have harg : (starRingEnd ℂ) (((k : ℂ) * (θ : ℂ)) * Complex.I)
        = -((k : ℂ) * (θ : ℂ)) * Complex.I := by
      rw [map_mul]
      have hreal : (starRingEnd ℂ) ((k : ℂ) * (θ : ℂ)) = (k : ℂ) * (θ : ℂ) := by simp
      rw [hreal, Complex.conj_I]
      ring
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, harg]
  calc (∑ j : Fin 16, (((((ξ / 2) ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) : ℝ)) : ℂ) * Complex.exp (((j : ℂ) * (θ : ℂ)) * Complex.I)) *
        (starRingEnd ℂ) (∑ k : Fin 16, (((((ξ / 2) ^ (k : ℕ) / (Nat.factorial (k : ℕ) : ℝ)) : ℝ)) : ℂ) *
          Complex.exp (((k : ℂ) * (θ : ℂ)) * Complex.I))
      = (∑ j : Fin 16, (((((ξ / 2) ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) : ℝ)) : ℂ) * Complex.exp (((j : ℂ) * (θ : ℂ)) * Complex.I)) *
        ∑ k : Fin 16, (starRingEnd ℂ) ((((((ξ / 2) ^ (k : ℕ) / (Nat.factorial (k : ℕ) : ℝ)) : ℝ)) : ℂ) *
          Complex.exp (((k : ℂ) * (θ : ℂ)) * Complex.I)) := by rw [map_sum]
    _ = ∑ j : Fin 16, ∑ k : Fin 16,
          ((((((ξ / 2) ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) : ℝ)) : ℂ) * Complex.exp (((j : ℂ) * (θ : ℂ)) * Complex.I)) *
          ((starRingEnd ℂ) ((((((ξ / 2) ^ (k : ℕ) / (Nat.factorial (k : ℕ) : ℝ)) : ℝ)) : ℂ) *
            Complex.exp (((k : ℂ) * (θ : ℂ)) * Complex.I))) :=
        Finset.sum_mul_sum _ _ _ _
    _ = ∑ j : Fin 16, ∑ k : Fin 16, ((((((ξ / 2) ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) : ℝ)) * ((((ξ / 2) ^ (k : ℕ) / (Nat.factorial (k : ℕ) : ℝ)) : ℝ)) : ℝ) : ℂ) *
          Complex.exp ((((j : ℂ) - (k : ℂ)) * (θ : ℂ)) * Complex.I) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [hconj k]
        have hre : (((((ξ / 2) ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) : ℝ)) : ℂ) * Complex.exp (((j : ℂ) * (θ : ℂ)) * Complex.I) *
            ((((((ξ / 2) ^ (k : ℕ) / (Nat.factorial (k : ℕ) : ℝ)) : ℝ)) : ℂ) * Complex.exp ((-((k : ℂ) * (θ : ℂ))) * Complex.I))
            = ((((((ξ / 2) ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) : ℝ)) : ℂ) * (((((ξ / 2) ^ (k : ℕ) / (Nat.factorial (k : ℕ) : ℝ)) : ℝ)) : ℂ)) *
              (Complex.exp (((j : ℂ) * (θ : ℂ)) * Complex.I) *
                Complex.exp ((-((k : ℂ) * (θ : ℂ))) * Complex.I)) := by ring
        rw [hre, ← Complex.exp_add]
        have hcast : ((((((ξ / 2) ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) : ℝ)) * ((((ξ / 2) ^ (k : ℕ) / (Nat.factorial (k : ℕ) : ℝ)) : ℝ)) : ℝ) : ℂ) = (((((ξ / 2) ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) : ℝ)) : ℂ) * (((((ξ / 2) ^ (k : ℕ) / (Nat.factorial (k : ℕ) : ℝ)) : ℝ)) : ℂ) := by
          push_cast
          ring
        rw [hcast]
        have harg : (j : ℂ) * (θ : ℂ) * Complex.I + -((k : ℂ) * (θ : ℂ)) * Complex.I
            = ((j : ℂ) - (k : ℂ)) * (θ : ℂ) * Complex.I := by ring
        rw [harg]
    _ = ∑ jk : Fin 16 × Fin 16, ((((((ξ / 2) ^ (jk.1 : ℕ) / (Nat.factorial (jk.1 : ℕ) : ℝ)) : ℝ)) * ((((ξ / 2) ^ (jk.2 : ℕ) / (Nat.factorial (jk.2 : ℕ) : ℝ)) : ℝ)) : ℝ) : ℂ) *
          Complex.exp ((((jk.1 : ℂ) - (jk.2 : ℂ)) * (θ : ℂ)) * Complex.I) :=
        (Fintype.sum_prod_type (f := fun jk : Fin 16 × Fin 16 =>
          ((((((ξ / 2) ^ (jk.1 : ℕ) / (Nat.factorial (jk.1 : ℕ) : ℝ)) : ℝ)) * ((((ξ / 2) ^ (jk.2 : ℕ) / (Nat.factorial (jk.2 : ℕ) : ℝ)) : ℝ)) : ℝ) : ℂ) *
            Complex.exp ((((jk.1 : ℂ) - (jk.2 : ℂ)) * (θ : ℂ)) * Complex.I))).symm

/-- The weighted exponent identity behind the Fourier orthogonality. -/
private lemma real_core (hh : ℕ) (x : Fin hh → Fin 16 × Fin 16) :
    ∑ n : Fin hh, (((x n).1 : ℝ) - ((x n).2 : ℝ)) * 2 ^ (n : ℕ)
      = ((((∑ n : Fin hh, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) : ℝ) - ((((∑ n : Fin hh, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) : ℝ) := by
  have hstep : ∀ n : Fin hh, (((x n).1 : ℝ) - ((x n).2 : ℝ)) * 2 ^ (n : ℕ)
      = ((x n).1 : ℝ) * 2 ^ (n : ℕ) - ((x n).2 : ℝ) * 2 ^ (n : ℕ) := by
    intro n
    ring
  rw [Finset.sum_congr rfl fun n _ => hstep n, Finset.sum_sub_distrib]
  push_cast
  ring

/-- The summed phase of a tuple of Taylor indices, at `r / 2^hh`. -/
private lemma arg_fold (hh : ℕ) (r : ℕ) (x : Fin hh → Fin 16 × Fin 16) :
    ∑ n : Fin hh, (((x n).1 : ℂ) - ((x n).2 : ℂ)) *
        (((2 * π * ((r : ℝ) * 2 ^ (n : ℕ) / 2 ^ hh)) : ℝ) : ℂ) * Complex.I
      = ((2 * (Real.pi : ℂ) * Complex.I)) * (r : ℂ) * ((((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ)) : ℤ) : ℂ) / ((2 : ℕ) ^ hh : ℂ) := by
  have h1 : ∀ n : Fin hh, (((x n).1 : ℂ) - ((x n).2 : ℂ)) *
        (((2 * π * ((r : ℝ) * 2 ^ (n : ℕ) / 2 ^ hh)) : ℝ) : ℂ) * Complex.I
      = (((((x n).1 : ℝ) - ((x n).2 : ℝ)) *
          (2 * π * ((r : ℝ) * 2 ^ (n : ℕ) / 2 ^ hh)) : ℝ) : ℂ) * Complex.I := by
    intro n
    push_cast
    ring
  have hsump : ∑ n : Fin hh, (((x n).1 : ℝ) - ((x n).2 : ℝ)) *
        (2 * π * ((r : ℝ) * 2 ^ (n : ℕ) / 2 ^ hh))
      = 2 * π * (r : ℝ) * ((((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ)) : ℤ) : ℝ) / ((2 : ℕ) ^ hh : ℝ) := by
    have hfac : ∀ n : Fin hh, (((x n).1 : ℝ) - ((x n).2 : ℝ)) *
          (2 * π * ((r : ℝ) * 2 ^ (n : ℕ) / 2 ^ hh))
        = (2 * π * (r : ℝ) / ((2 : ℕ) ^ hh : ℝ)) *
            ((((x n).1 : ℝ) - ((x n).2 : ℝ)) * 2 ^ (n : ℕ)) := by
      intro n
      ring
    rw [Finset.sum_congr rfl fun n _ => hfac n, ← Finset.mul_sum, real_core]
    have hT : ((((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ)) : ℤ) : ℝ) = ((((∑ n : Fin hh, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) : ℝ) - ((((∑ n : Fin hh, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) : ℝ) := by
      push_cast
      ring
    rw [hT]
    field_simp
  rw [Finset.sum_congr rfl fun n _ => h1 n, ← Finset.sum_mul, ← Complex.ofReal_sum, hsump]
  push_cast
  field_simp

/-- The dyadic product of the Taylor factors, expanded over tuples of Taylor indices. -/
private theorem prod_pfac_cast (ξ : ℝ) (hh : ℕ) (r : ℕ) :
    ((∏ n ∈ Finset.range hh,
        polynomialFactor191 ξ (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh)) : ℝ) : ℂ)
      = ∑ x : Fin hh → Fin 16 × Fin 16,
          ((∏ n : Fin hh, (((((ξ / 2) ^ ((x n).1 : ℕ) / (Nat.factorial ((x n).1 : ℕ) : ℝ)) : ℝ)) * ((((ξ / 2) ^ ((x n).2 : ℕ) / (Nat.factorial ((x n).2 : ℕ) : ℝ)) : ℝ))) : ℝ) : ℂ) *
            Complex.exp (((2 * (Real.pi : ℂ) * Complex.I)) * (r : ℂ) * ((((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ)) : ℤ) : ℂ) / ((2 : ℕ) ^ hh : ℂ)) := by
  rw [Complex.ofReal_prod,
    ← Fin.prod_univ_eq_prod_range (fun n : ℕ =>
      ((polynomialFactor191 ξ (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh)) : ℝ) : ℂ))]
  have hstep : ∀ n : Fin hh,
      ((polynomialFactor191 ξ (2 * π * ((r : ℝ) * 2 ^ (n : ℕ) / 2 ^ hh)) : ℝ) : ℂ)
      = ∑ jk : Fin 16 × Fin 16, ((((((ξ / 2) ^ (jk.1 : ℕ) / (Nat.factorial (jk.1 : ℕ) : ℝ)) : ℝ)) * ((((ξ / 2) ^ (jk.2 : ℕ) / (Nat.factorial (jk.2 : ℕ) : ℝ)) : ℝ)) : ℝ) : ℂ) *
          Complex.exp ((((jk.1 : ℂ) - (jk.2 : ℂ)) *
            ((2 * π * ((r : ℝ) * 2 ^ (n : ℕ) / 2 ^ hh) : ℝ) : ℂ)) * Complex.I) := by
    intro n
    exact pfac_cast ξ _
  rw [Finset.prod_congr rfl fun n _ => hstep n, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, arg_fold, ← Complex.ofReal_prod]

/-- The dyadic average equals the sum over tuples whose exponent sum is divisible by `2^hh`. -/
private theorem polynomialAverage_eq_sum (ξ : ℝ) (hh : ℕ) :
    polynomialAverage191 ξ hh =
      ∑ x : Fin hh → Fin 16 × Fin 16,
        if (2 : ℤ) ^ hh ∣ ((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ)) then
          (∏ n : Fin hh, (((((ξ / 2) ^ ((x n).1 : ℕ) / (Nat.factorial ((x n).1 : ℕ) : ℝ)) : ℝ)) * ((((ξ / 2) ^ ((x n).2 : ℕ) / (Nat.factorial ((x n).2 : ℕ) : ℝ)) : ℝ))) : ℝ) else 0 := by
  have hNpos : (0 : ℕ) < 2 ^ hh := by positivity
  have hNc : ((2 : ℕ) ^ hh : ℝ) ≠ 0 := by positivity
  refine Complex.ofReal_injective ?_
  have hcast : ((∑ x : Fin hh → Fin 16 × Fin 16,
        if (2 : ℤ) ^ hh ∣ ((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ)) then
          (∏ n : Fin hh, (((((ξ / 2) ^ ((x n).1 : ℕ) / (Nat.factorial ((x n).1 : ℕ) : ℝ)) : ℝ)) * ((((ξ / 2) ^ ((x n).2 : ℕ) / (Nat.factorial ((x n).2 : ℕ) : ℝ)) : ℝ))) : ℝ) else 0 : ℝ) : ℂ)
      = ∑ x : Fin hh → Fin 16 × Fin 16,
          if (2 : ℤ) ^ hh ∣ ((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ)) then
            ((∏ n : Fin hh, (((((ξ / 2) ^ ((x n).1 : ℕ) / (Nat.factorial ((x n).1 : ℕ) : ℝ)) : ℝ)) * ((((ξ / 2) ^ ((x n).2 : ℕ) / (Nat.factorial ((x n).2 : ℕ) : ℝ)) : ℝ))) : ℝ) : ℂ) else 0 := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hd : (2 : ℤ) ^ hh ∣ ((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ))
    · rw [if_pos hd, if_pos hd, Complex.ofReal_prod]
    · rw [if_neg hd, if_neg hd, Complex.ofReal_zero]
  rw [hcast]
  unfold polynomialAverage191
  push_cast
  simp only [Finset.mul_sum]
  have hprod : ∀ r : ℕ, (∏ n ∈ Finset.range hh,
        ((polynomialFactor191 ξ (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh)) : ℝ) : ℂ))
      = ∑ x : Fin hh → Fin 16 × Fin 16,
          ((∏ n : Fin hh, (((((ξ / 2) ^ ((x n).1 : ℕ) / (Nat.factorial ((x n).1 : ℕ) : ℝ)) : ℝ)) * ((((ξ / 2) ^ ((x n).2 : ℕ) / (Nat.factorial ((x n).2 : ℕ) : ℝ)) : ℝ))) : ℝ) : ℂ) *
            Complex.exp (((2 * (Real.pi : ℂ) * Complex.I)) * (r : ℂ) * ((((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ)) : ℤ) : ℂ) / ((2 : ℕ) ^ hh : ℂ)) := by
    intro r
    rw [← Complex.ofReal_prod]
    exact prod_pfac_cast ξ hh r
  simp only [hprod]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hfac : ∀ r : ℕ, (1 / (2 : ℂ) ^ hh) *
        (((∏ n : Fin hh, (((((ξ / 2) ^ ((x n).1 : ℕ) / (Nat.factorial ((x n).1 : ℕ) : ℝ)) : ℝ)) * ((((ξ / 2) ^ ((x n).2 : ℕ) / (Nat.factorial ((x n).2 : ℕ) : ℝ)) : ℝ))) : ℝ) : ℂ) *
          Complex.exp (((2 * (Real.pi : ℂ) * Complex.I)) * (r : ℂ) * ((((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ)) : ℤ) : ℂ) / ((2 : ℕ) ^ hh : ℂ)))
      = ((∏ n : Fin hh, (((((ξ / 2) ^ ((x n).1 : ℕ) / (Nat.factorial ((x n).1 : ℕ) : ℝ)) : ℝ)) * ((((ξ / 2) ^ ((x n).2 : ℕ) / (Nat.factorial ((x n).2 : ℕ) : ℝ)) : ℝ))) : ℝ) : ℂ) *
        ((1 / (2 : ℂ) ^ hh) *
          Complex.exp (((2 * (Real.pi : ℂ) * Complex.I)) * (r : ℂ) * ((((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ)) : ℤ) : ℂ) / ((2 : ℕ) ^ hh : ℂ))) := by
    intro r
    ring
  rw [Finset.sum_congr rfl fun r _ => hfac r, ← Finset.mul_sum, ← Finset.mul_sum]
  have hc : ((2 : ℂ) ^ hh) = (((2 : ℕ) ^ hh : ℕ) : ℂ) := (Nat.cast_pow (α := ℂ) 2 hh).symm
  rw [hc, ← Nat.cast_pow, sum_exp_orthog (((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ))) hNpos]
  have hz : ((2 : ℤ) ^ hh) = (((2 : ℕ) ^ hh : ℕ) : ℤ) := (Nat.cast_pow (α := ℤ) 2 hh).symm
  rw [hz]
  by_cases hd : (((2 : ℕ) ^ hh : ℕ) : ℤ) ∣ ((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ))
  · rw [if_pos hd, if_pos hd]
    have hNc' : (((2 : ℕ) ^ hh : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hNc
    field_simp
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun n _ => ?_
    push_cast
    ring
  · rw [if_neg hd, if_neg hd]
    ring
/-! ## The carry recurrence: coefficients, weights, rows

The lemmas below all compile. Toward `polynomialAverage_eq_carry191` they give the weight array
as an explicit sum, the row recursion as a function `rowF`, and the splitting of a tuple at its
last index. What remains for that leaf is `rows_invariant` (the induction relating `rowF` to the
tuple sum of `polynomialAverage_eq_sum`) and the final assembly. -/



private lemma aF_eq_zero {num j : ℕ} (hj : 16 ≤ j) : (((num ^ (j : ℕ) * 20000 ^ (15 - (j : ℕ)) *
    (Nat.factorial 15 / Nat.factorial (j : ℕ))) : ℕ)) = 0 := by
  have h1 : 15 - j = 0 := by omega
  have hlt : Nat.factorial 15 < Nat.factorial j := by
    have h16 : Nat.factorial 15 < Nat.factorial 16 := by norm_num [Nat.factorial]
    have h2 : Nat.factorial 16 ≤ Nat.factorial j := Nat.factorial_le (by omega)
    omega
  rw [h1, Nat.div_eq_of_lt hlt, pow_zero, mul_one, mul_zero]

/-- Splitting the weight sums: the coefficient accessor. -/
private lemma coeffs_get? (num j : ℕ) :
    (carryCoeffs191 num)[j]? = if j < 16 then some ((((num ^ (j : ℕ) * 20000 ^ (15 - (j : ℕ)) *
    (Nat.factorial 15 / Nat.factorial (j : ℕ))) : ℕ))) else none := by
  unfold carryCoeffs191
  rw [Array.getElem?_ofFn]
  split_ifs with h
  · rfl
  · rfl

private lemma coeffs_getD (num j : ℕ) : (carryCoeffs191 num).getD j 0 = (((num ^ (j : ℕ) * 20000 ^ (15 - (j : ℕ)) *
    (Nat.factorial 15 / Nat.factorial (j : ℕ))) : ℕ)) := by
  rw [Array.getD_eq_getD_getElem?, coeffs_get? num j]
  split_ifs with hj
  · rfl
  · push_neg at hj
    exact (aF_eq_zero (by omega)).symm

/-- The inner weight sum selects the single index `q` with `j + 15 = q + t`. -/
private lemma weights_inner (num t j : ℕ) (ht : t ≤ 30) (hj : j < 16) :
    ∑ q ∈ Finset.range 16, (if j + 15 = q + t then (((num ^ (j : ℕ) * 20000 ^ (15 - (j : ℕ)) *
    (Nat.factorial 15 / Nat.factorial (j : ℕ))) : ℕ)) * (((num ^ (q : ℕ) * 20000 ^ (15 - (q : ℕ)) *
    (Nat.factorial 15 / Nat.factorial (q : ℕ))) : ℕ)) else 0)
      = if (t ≤ j + 15 ∧ j ≤ t) then (((num ^ (j : ℕ) * 20000 ^ (15 - (j : ℕ)) *
    (Nat.factorial 15 / Nat.factorial (j : ℕ))) : ℕ)) * (((num ^ ((j + 15 - t) : ℕ) * 20000 ^ (15 - ((j + 15 - t) : ℕ)) *
    (Nat.factorial 15 / Nat.factorial ((j + 15 - t) : ℕ))) : ℕ)) else 0 := by
  by_cases h : t ≤ j + 15 ∧ j ≤ t
  · rw [if_pos h]
    obtain ⟨h1, h2⟩ := h
    have hlt : j + 15 - t < 16 := by omega
    rw [Finset.sum_eq_single (j + 15 - t)]
    · rw [if_pos (by omega)]
    · intro q hq hne
      refine if_neg ?_
      intro he
      exact hne (by omega)
    · intro hmem
      exact absurd (Finset.mem_range.mpr hlt) hmem
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun q hq => ?_
    have hq16 : q < 16 := Finset.mem_range.mp hq
    refine if_neg ?_
    intro he
    exact h (by omega)

private lemma carryWeights_def (num : ℕ) :
    carryWeights191 num = Array.ofFn (fun t : Fin 31 => ∑ j ∈ Finset.range 16,
      if t.val ≤ j + 15 ∧ j ≤ t.val then
        (carryCoeffs191 num)[j]?.getD 0 * (carryCoeffs191 num)[j + 15 - t.val]?.getD 0
      else 0) := rfl

private lemma weights_getD (num t : ℕ) (ht : t < 31) :
    (carryWeights191 num).getD t 0
      = ∑ j ∈ Finset.range 16, ∑ q ∈ Finset.range 16,
          (if j + 15 = q + t then (((num ^ (j : ℕ) * 20000 ^ (15 - (j : ℕ)) *
    (Nat.factorial 15 / Nat.factorial (j : ℕ))) : ℕ)) * (((num ^ (q : ℕ) * 20000 ^ (15 - (q : ℕ)) *
    (Nat.factorial 15 / Nat.factorial (q : ℕ))) : ℕ)) else 0) := by
  rw [Array.getD_eq_getD_getElem?, carryWeights_def, Array.getElem?_ofFn]
  rw [dif_pos ht]
  simp only [Option.getD_some]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [weights_inner num t j (by omega) (Finset.mem_range.mp hj)]
  by_cases hg : (t ≤ j + 15 ∧ j ≤ t)
  · rw [if_pos hg, if_pos hg, ← Array.getD_eq_getD_getElem?,
      ← Array.getD_eq_getD_getElem?, coeffs_getD, coeffs_getD]
  · rw [if_neg hg, if_neg hg]

/-! ## Bounds and the split of a tuple at its last index -/

private lemma two_pow_sum (hh : ℕ) : ∑ n ∈ Finset.range hh, 2 ^ n = 2 ^ hh - 1 := by
  induction hh with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : 1 ≤ 2 ^ h := Nat.one_le_two_pow
    have h2 : 2 ^ (h + 1) = 2 * 2 ^ h := by ring
    omega

private lemma aOf_le (hh : ℕ) (x : Fin hh → Fin 16 × Fin 16) : (((∑ n : Fin hh, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) ≤ 15 * (2 ^ hh - 1) := by
  calc ∑ n : Fin hh, ((x n).1 : ℕ) * 2 ^ (n : ℕ)
      ≤ ∑ n : Fin hh, 15 * 2 ^ (n : ℕ) := by
        refine Finset.sum_le_sum fun n _ => ?_
        exact Nat.mul_le_mul_right _ (by have := (x n).1.isLt; omega)
    _ = 15 * ∑ n : Fin hh, 2 ^ (n : ℕ) := (Finset.mul_sum _ _ _).symm
    _ = 15 * (2 ^ hh - 1) := by
        congr 1
        rw [Fin.sum_univ_eq_sum_range (fun n => 2 ^ n) hh]
        exact two_pow_sum hh

private lemma bOf_le (hh : ℕ) (x : Fin hh → Fin 16 × Fin 16) : (((∑ n : Fin hh, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) ≤ 15 * (2 ^ hh - 1) := by
  calc ∑ n : Fin hh, ((x n).2 : ℕ) * 2 ^ (n : ℕ)
      ≤ ∑ n : Fin hh, 15 * 2 ^ (n : ℕ) := by
        refine Finset.sum_le_sum fun n _ => ?_
        exact Nat.mul_le_mul_right _ (by have := (x n).2.isLt; omega)
    _ = 15 * ∑ n : Fin hh, 2 ^ (n : ℕ) := (Finset.mul_sum _ _ _).symm
    _ = 15 * (2 ^ hh - 1) := by
        congr 1
        rw [Fin.sum_univ_eq_sum_range (fun n => 2 ^ n) hh]
        exact two_pow_sum hh

private lemma aOf_snoc (hh : ℕ) (x : Fin hh → Fin 16 × Fin 16) (a : Fin 16 × Fin 16) :
    (((∑ n : Fin (hh + 1), ((((Fin.snoc x a : Fin (hh + 1) → Fin 16 × Fin 16) n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ))
      = (((∑ n : Fin hh, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + (a.1 : ℕ) * 2 ^ hh := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · exact Finset.sum_congr rfl fun n _ => by simp [Fin.snoc_castSucc]
  · simp [Fin.snoc_last, Fin.val_last]

private lemma bOf_snoc (hh : ℕ) (x : Fin hh → Fin 16 × Fin 16) (a : Fin 16 × Fin 16) :
    (((∑ n : Fin (hh + 1), ((((Fin.snoc x a : Fin (hh + 1) → Fin 16 × Fin 16) n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ))
      = (((∑ n : Fin hh, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + (a.2 : ℕ) * 2 ^ hh := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · exact Finset.sum_congr rfl fun n _ => by simp [Fin.snoc_castSucc]
  · simp [Fin.snoc_last, Fin.val_last]

private lemma bprod_snoc (num hh : ℕ) (x : Fin hh → Fin 16 × Fin 16) (a : Fin 16 × Fin 16) :
    (((∏ n : Fin (hh + 1), (((num ^ ((((Fin.snoc x a : Fin (hh + 1) → Fin 16 × Fin 16) n).1) : ℕ) * 20000 ^ (15 - ((((Fin.snoc x a : Fin (hh + 1) → Fin 16 × Fin 16) n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial ((((Fin.snoc x a : Fin (hh + 1) → Fin 16 × Fin 16) n).1) : ℕ))) : ℕ)) * (((num ^ ((((Fin.snoc x a : Fin (hh + 1) → Fin 16 × Fin 16) n).2) : ℕ) * 20000 ^ (15 - ((((Fin.snoc x a : Fin (hh + 1) → Fin 16 × Fin 16) n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial ((((Fin.snoc x a : Fin (hh + 1) → Fin 16 × Fin 16) n).2) : ℕ))) : ℕ))) : ℕ))
      = (((∏ n : Fin hh, (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ)) * ((((num ^ (a.1 : ℕ) * 20000 ^ (15 - (a.1 : ℕ)) *
    (Nat.factorial 15 / Nat.factorial (a.1 : ℕ))) : ℕ)) * (((num ^ (a.2 : ℕ) * 20000 ^ (15 - (a.2 : ℕ)) *
    (Nat.factorial 15 / Nat.factorial (a.2 : ℕ))) : ℕ))) := by
  rw [Fin.prod_univ_castSucc]
  congr 1
  · exact Finset.prod_congr rfl fun n _ => by rw [Fin.snoc_castSucc]
  · simp [Fin.snoc_last, Fin.val_last]

private lemma sum_fin_succ_split {A : Type} [Fintype A] {M : Type} [AddCommMonoid M] (h : ℕ)
    (g : (Fin (h + 1) → A) → M) :
    ∑ x : Fin (h + 1) → A, g x = ∑ x' : Fin h → A, ∑ a : A, g (Fin.snoc x' a) := by
  rw [Finset.sum_comm, ← Fintype.sum_prod_type (f := fun p : A × (Fin h → A) => g (Fin.snoc p.2 p.1))]
  exact (Equiv.sum_comp (Fin.snocEquiv (fun _ => A)) g).symm

/-! ## The row recursion in terms of `carryRows191` -/

private lemma carryStep_def (w v : Array ℕ) :
    carryStep191 w v = Array.ofFn (fun j : Fin 31 => ∑ i ∈ Finset.range 31,
      if i ≤ 2 * j.val ∧ 2 * j.val ≤ i + 30 then
        v[i]?.getD 0 * w[2 * j.val - i]?.getD 0 else 0) := rfl

/-- The initial row: unit mass at carry `0`, index `15`. -/
private lemma rows_base (num i : ℕ) :
    (carryRows191 (carryWeights191 num) 0).getD i 0 = (if i = 15 then 1 else 0) := by
  show (Array.ofFn (fun i : Fin 31 => if i.val = 15 then 1 else 0)).getD i 0 = _
  rw [Array.getD_eq_getD_getElem?]
  by_cases hi : i < 31
  · rw [Array.getElem?_ofFn, dif_pos hi]
    rfl
  · rw [Array.getElem?_ofFn, dif_neg hi]
    simp only [Option.getD_none]
    have h15 : i ≠ 15 := by omega
    simp [h15]

/-- One row of the recursion, as an array index equation. -/
private lemma rows_rec (num h i : ℕ) (hi : i < 31) :
    (carryRows191 (carryWeights191 num) (h + 1)).getD i 0
      = ∑ i₀ ∈ Finset.range 31,
          (if i₀ ≤ 2 * i ∧ 2 * i ≤ i₀ + 30 then
            (carryRows191 (carryWeights191 num) h).getD i₀ 0 *
              (carryWeights191 num).getD (2 * i - i₀) 0 else 0) := by
  have hstep : carryRows191 (carryWeights191 num) (h + 1)
      = carryStep191 (carryWeights191 num) (carryRows191 (carryWeights191 num) h) := rfl
  rw [hstep, Array.getD_eq_getD_getElem?, carryStep_def, Array.getElem?_ofFn, dif_pos hi]
  simp only [Option.getD_some]
  refine Finset.sum_congr rfl fun i₀ hi₀ => ?_
  rw [← Array.getD_eq_getD_getElem?, ← Array.getD_eq_getD_getElem?]


/-! ## The index determined by the last tuple coordinate -/


/-- The weight array as a sum over `Fin 16 × Fin 16`, the form used downstream. -/
private lemma weights_getD_fin (num t : ℕ) (ht : t < 31) :
    (carryWeights191 num).getD t 0 = ∑ j : Fin 16, ∑ q : Fin 16,
      (if (j : ℕ) + 15 = (q : ℕ) + t then (((num ^ (j : ℕ) * 20000 ^ (15 - (j : ℕ)) *
    (Nat.factorial 15 / Nat.factorial (j : ℕ))) : ℕ)) * (((num ^ (q : ℕ) * 20000 ^ (15 - (q : ℕ)) *
    (Nat.factorial 15 / Nat.factorial (q : ℕ))) : ℕ)) else 0) := by
  rw [weights_getD num t ht, ← Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    ∑ q ∈ Finset.range 16, (if j + 15 = q + t then (((num ^ (j : ℕ) * 20000 ^ (15 - (j : ℕ)) *
    (Nat.factorial 15 / Nat.factorial (j : ℕ))) : ℕ)) * (((num ^ (q : ℕ) * 20000 ^ (15 - (q : ℕ)) *
    (Nat.factorial 15 / Nat.factorial (q : ℕ))) : ℕ)) else 0))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun q : ℕ =>
    (if (j : ℕ) + 15 = q + t then (((num ^ ((j : ℕ) : ℕ) * 20000 ^ (15 - ((j : ℕ) : ℕ)) *
    (Nat.factorial 15 / Nat.factorial ((j : ℕ) : ℕ))) : ℕ)) * (((num ^ (q : ℕ) * 20000 ^ (15 - (q : ℕ)) *
    (Nat.factorial 15 / Nat.factorial (q : ℕ))) : ℕ)) else 0))]



/-! ## The array index determined by the last tuple coordinate -/

private lemma sub_mul_add (x y P : ℕ) (h : y ≤ x) : (x - y) * P + y * P = x * P := by
  rw [← add_mul, Nat.sub_add_cancel h]

/-- The array index `i₀` is determined by the last coordinate `(j, q)` of the tuple. -/
private lemma idx_solutions (A B P i j q : ℕ) (hP : 0 < P) (hA : A ≤ 15 * (P - 1))
    (hB : B ≤ 15 * (P - 1)) (hj : j < 16) (hq : q < 16) :
    ∑ i₀ ∈ Finset.range 31,
      (if i₀ ≤ 2 * i ∧ 2 * i ≤ i₀ + 30 ∧ A + 15 * P = B + i₀ * P ∧
          j + 15 = q + (2 * i - i₀) then (1 : ℕ) else 0)
      = if A + (j * P + 15 * (2 * P)) = B + (q * P + i * (2 * P)) then 1 else 0 := by
  have hP1 : 1 ≤ P := hP
  have hbA : (A : ℤ) ≤ 15 * ((P : ℤ) - 1) := by
    have h := hA
    have h1 : ((15 * (P - 1) : ℕ) : ℤ) = 15 * ((P : ℤ) - 1) := by
      push_cast [Nat.cast_sub hP1]; ring
    have h2 : (A : ℤ) ≤ ((15 * (P - 1) : ℕ) : ℤ) := by exact_mod_cast h
    linarith
  have hbB : (B : ℤ) ≤ 15 * ((P : ℤ) - 1) := by
    have h := hB
    have h1 : ((15 * (P - 1) : ℕ) : ℤ) = 15 * ((P : ℤ) - 1) := by
      push_cast [Nat.cast_sub hP1]; ring
    have h2 : (B : ℤ) ≤ ((15 * (P - 1) : ℕ) : ℤ) := by exact_mod_cast h
    linarith
  have hPz : (0 : ℤ) < (P : ℤ) := by exact_mod_cast hP
  by_cases hT : A + (j * P + 15 * (2 * P)) = B + (q * P + i * (2 * P))
  · rw [if_pos hT]
    have hTz : (A : ℤ) + ((j : ℤ) * P + 15 * (2 * (P : ℤ)))
        = (B : ℤ) + ((q : ℤ) * P + (i : ℤ) * (2 * (P : ℤ))) := by
      have h := hT
      have h' : ((A + (j * P + 15 * (2 * P)) : ℕ) : ℤ)
          = ((B + (q * P + i * (2 * P)) : ℕ) : ℤ) := by rw [h]
      push_cast at h'
      linarith
    have hcP : (((q : ℤ) + 2 * (i : ℤ) - ((j : ℤ) + 15)) * (P : ℤ))
        = (A : ℤ) + 15 * (P : ℤ) - (B : ℤ) := by
      ring_nf at hTz ⊢
      linarith
    have hpos : (0 : ℤ) < (q : ℤ) + 2 * (i : ℤ) - ((j : ℤ) + 15) := by
      have h1 : (0 : ℤ) < ((q : ℤ) + 2 * (i : ℤ) - ((j : ℤ) + 15)) * (P : ℤ) := by
        rw [hcP]
        nlinarith [hbB, hPz]
      exact (mul_pos_iff_of_pos_right hPz).mp h1
    have hjq : j + 15 ≤ 2 * i + q := by
      have h2 : ((j : ℤ) + 15) ≤ 2 * (i : ℤ) + (q : ℤ) := by linarith
      exact_mod_cast h2
    set i₀ := 2 * i + q - (j + 15) with hi₀
    have hi₀val : (i₀ : ℤ) = (q : ℤ) + 2 * (i : ℤ) - ((j : ℤ) + 15) := by
      rw [hi₀, Nat.cast_sub hjq]
      push_cast
      ring_nf
    have hi₀le : i₀ ≤ 2 * i := by omega
    have hguard2 : 2 * i ≤ i₀ + 30 := by omega
    have hC : A + 15 * P = B + i₀ * P := by
      have hz : (A : ℤ) + 15 * (P : ℤ) = (B : ℤ) + (i₀ : ℤ) * (P : ℤ) := by
        rw [hi₀val]
        linarith [hcP]
      exact_mod_cast hz
    have hD : j + 15 = q + (2 * i - i₀) := by omega
    have hlt : i₀ < 31 := by
      have h1 : i₀ * P + B = A + 15 * P := by omega
      have h2 : i₀ * P ≤ 15 * (P - 1) + 15 * P := by omega
      have h3 : 15 * (P - 1) + 15 * P < 30 * P := by
        have e : 15 * (P - 1) + 15 = 15 * P := by
          have hstep : (P - 1) + 1 = P := Nat.sub_add_cancel hP1
          calc 15 * (P - 1) + 15 = 15 * ((P - 1) + 1) := by ring
            _ = 15 * P := by rw [hstep]
        omega
      have h4 : i₀ * P < 30 * P := by omega
      have h30 : i₀ < 30 := (Nat.mul_lt_mul_right hP).mp h4
      omega
    rw [Finset.sum_eq_single i₀]
    · rw [if_pos ⟨hi₀le, hguard2, hC, hD⟩]
    · intro i₁ hi₁ hne
      refine if_neg ?_
      intro hcon
      exact hne (by omega)
    · intro hmem
      exact absurd (Finset.mem_range.mpr hlt) hmem
  · rw [if_neg hT]
    refine Finset.sum_eq_zero fun i₀ hi₀ => ?_
    refine if_neg ?_
    rintro ⟨h1, h2, h3, h4⟩
    apply hT
    have hkey : i₀ = 2 * i + q - (j + 15) := by omega
    have hjq : j + 15 ≤ 2 * i + q := by omega
    have e1 : (q + 2 * i) * P = i₀ * P + (j + 15) * P := by
      rw [hkey, sub_mul_add (2 * i + q) (j + 15) P hjq]
      ring
    have h3' : B + i₀ * P = A + 15 * P := by rw [← h3]
    have e2 : (q + 2 * i) * P = q * P + i * (2 * P) := by ring
    have e3 : (j + 15) * P = j * P + 15 * P := by ring
    have e4 : 15 * P + 15 * P = 15 * (2 * P) := by ring
    linarith [e1, e2, e3, e4, h3']




/-! ## The invariant: the carry recurrence computes the tuple sum -/

private lemma sum_mul_double {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (f : A → ℕ) (g : B → C → ℕ) :
    (∑ a, f a) * (∑ b, ∑ c, g b c) = ∑ a, ∑ b, ∑ c, f a * g b c := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]

/-! ## The invariant: the carry rows compute the tuple sum -/

/-- Splitting the tuple sum at the last tuple coordinate. -/
private lemma tSum_succ (num h i : ℕ) :
    (((∑ x : Fin (h + 1) → Fin 16 × Fin 16,
    (if ((∑ n : Fin (h + 1), (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ) + 15 * 2 ^ (h + 1) = ((∑ n : Fin (h + 1), (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ) + i * 2 ^ (h + 1) then ((∏ n : Fin (h + 1), (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ) else 0)) : ℕ)) = ∑ x' : Fin h → Fin 16 × Fin 16, ∑ j : Fin 16, ∑ q : Fin 16,
      (if (((∑ n : Fin h, (((x' n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + ((j : ℕ) * 2 ^ h + 15 * (2 * 2 ^ h))
          = (((∑ n : Fin h, (((x' n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + ((q : ℕ) * 2 ^ h + i * (2 * 2 ^ h))
        then (((∏ n : Fin h, (((num ^ (((x' n).1) : ℕ) * 20000 ^ (15 - (((x' n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x' n).1) : ℕ))) : ℕ)) * (((num ^ (((x' n).2) : ℕ) * 20000 ^ (15 - (((x' n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x' n).2) : ℕ))) : ℕ))) : ℕ)) * ((((num ^ ((j : ℕ) : ℕ) * 20000 ^ (15 - ((j : ℕ) : ℕ)) *
    (Nat.factorial 15 / Nat.factorial ((j : ℕ) : ℕ))) : ℕ)) * (((num ^ ((q : ℕ) : ℕ) * 20000 ^ (15 - ((q : ℕ) : ℕ)) *
    (Nat.factorial 15 / Nat.factorial ((q : ℕ) : ℕ))) : ℕ))) else 0) := by
  rw [sum_fin_succ_split]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
  rw [aOf_snoc, bOf_snoc, bprod_snoc]
  have hp : 2 ^ (h + 1) = 2 * 2 ^ h := by ring
  rw [hp]
  congr 2
  · ring
  · ring

/-- One carry step, written over tuples. -/
private lemma step1 (num h i i₀ : ℕ) (hi : i < 31) (hi₀ : i₀ < 31)
    (hg : i₀ ≤ 2 * i ∧ 2 * i ≤ i₀ + 30) (ih : (carryRows191 (carryWeights191 num) h).getD i₀ 0 = (((∑ x : Fin h → Fin 16 × Fin 16,
    (if ((∑ n : Fin h, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ) + 15 * 2 ^ h = ((∑ n : Fin h, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ) + i₀ * 2 ^ h then ((∏ n : Fin h, (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ) else 0)) : ℕ))) :
    (carryRows191 (carryWeights191 num) h).getD i₀ 0 * (carryWeights191 num).getD (2 * i - i₀) 0
      = ∑ x' : Fin h → Fin 16 × Fin 16, ∑ j : Fin 16, ∑ q : Fin 16,
          (if i₀ ≤ 2 * i ∧ 2 * i ≤ i₀ + 30 ∧
              (((∑ n : Fin h, (((x' n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + 15 * 2 ^ h = (((∑ n : Fin h, (((x' n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + i₀ * 2 ^ h ∧
              (j : ℕ) + 15 = (q : ℕ) + (2 * i - i₀)
            then (((∏ n : Fin h, (((num ^ (((x' n).1) : ℕ) * 20000 ^ (15 - (((x' n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x' n).1) : ℕ))) : ℕ)) * (((num ^ (((x' n).2) : ℕ) * 20000 ^ (15 - (((x' n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x' n).2) : ℕ))) : ℕ))) : ℕ)) * ((((num ^ ((j : ℕ) : ℕ) * 20000 ^ (15 - ((j : ℕ) : ℕ)) *
    (Nat.factorial 15 / Nat.factorial ((j : ℕ) : ℕ))) : ℕ)) * (((num ^ ((q : ℕ) : ℕ) * 20000 ^ (15 - ((q : ℕ) : ℕ)) *
    (Nat.factorial 15 / Nat.factorial ((q : ℕ) : ℕ))) : ℕ))) else 0) := by
  have hlt : 2 * i - i₀ < 31 := by omega
  rw [ih]
  rw [weights_getD_fin num (2 * i - i₀) hlt, sum_mul_double]
  refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun q _ => ?_
  by_cases hc : ((((∑ n : Fin h, (((x' n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + 15 * 2 ^ h = (((∑ n : Fin h, (((x' n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + i₀ * 2 ^ h) <;>
  by_cases hd : ((j : ℕ) + 15 = (q : ℕ) + (2 * i - i₀)) <;>
  simp [hc, hd, hg, mul_zero]

/-- Summing one carry step over the array indices, then exchanging the sums. -/
private lemma step2 (num h i : ℕ) (hi : i < 31)
    (ih : ∀ i₀, i₀ < 31 → (carryRows191 (carryWeights191 num) h).getD i₀ 0 = (((∑ x : Fin h → Fin 16 × Fin 16,
    (if ((∑ n : Fin h, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ) + 15 * 2 ^ h = ((∑ n : Fin h, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ) + i₀ * 2 ^ h then ((∏ n : Fin h, (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ) else 0)) : ℕ))) :
    (∑ i₀ ∈ Finset.range 31,
        (if i₀ ≤ 2 * i ∧ 2 * i ≤ i₀ + 30 then
          (carryRows191 (carryWeights191 num) h).getD i₀ 0 * (carryWeights191 num).getD (2 * i - i₀) 0 else 0))
      = ∑ x' : Fin h → Fin 16 × Fin 16, ∑ j : Fin 16, ∑ q : Fin 16,
          ∑ i₀ ∈ Finset.range 31,
            (if i₀ ≤ 2 * i ∧ 2 * i ≤ i₀ + 30 ∧
                (((∑ n : Fin h, (((x' n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + 15 * 2 ^ h = (((∑ n : Fin h, (((x' n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + i₀ * 2 ^ h ∧
                (j : ℕ) + 15 = (q : ℕ) + (2 * i - i₀)
              then (((∏ n : Fin h, (((num ^ (((x' n).1) : ℕ) * 20000 ^ (15 - (((x' n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x' n).1) : ℕ))) : ℕ)) * (((num ^ (((x' n).2) : ℕ) * 20000 ^ (15 - (((x' n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x' n).2) : ℕ))) : ℕ))) : ℕ)) * ((((num ^ ((j : ℕ) : ℕ) * 20000 ^ (15 - ((j : ℕ) : ℕ)) *
    (Nat.factorial 15 / Nat.factorial ((j : ℕ) : ℕ))) : ℕ)) * (((num ^ ((q : ℕ) : ℕ) * 20000 ^ (15 - ((q : ℕ) : ℕ)) *
    (Nat.factorial 15 / Nat.factorial ((q : ℕ) : ℕ))) : ℕ))) else 0) := by
  have step1' : ∀ i₀ ∈ Finset.range 31,
      (if i₀ ≤ 2 * i ∧ 2 * i ≤ i₀ + 30 then
        (carryRows191 (carryWeights191 num) h).getD i₀ 0 * (carryWeights191 num).getD (2 * i - i₀) 0 else 0)
      = ∑ x' : Fin h → Fin 16 × Fin 16, ∑ j : Fin 16, ∑ q : Fin 16,
          (if i₀ ≤ 2 * i ∧ 2 * i ≤ i₀ + 30 ∧
              (((∑ n : Fin h, (((x' n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + 15 * 2 ^ h = (((∑ n : Fin h, (((x' n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + i₀ * 2 ^ h ∧
              (j : ℕ) + 15 = (q : ℕ) + (2 * i - i₀)
            then (((∏ n : Fin h, (((num ^ (((x' n).1) : ℕ) * 20000 ^ (15 - (((x' n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x' n).1) : ℕ))) : ℕ)) * (((num ^ (((x' n).2) : ℕ) * 20000 ^ (15 - (((x' n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x' n).2) : ℕ))) : ℕ))) : ℕ)) * ((((num ^ ((j : ℕ) : ℕ) * 20000 ^ (15 - ((j : ℕ) : ℕ)) *
    (Nat.factorial 15 / Nat.factorial ((j : ℕ) : ℕ))) : ℕ)) * (((num ^ ((q : ℕ) : ℕ) * 20000 ^ (15 - ((q : ℕ) : ℕ)) *
    (Nat.factorial 15 / Nat.factorial ((q : ℕ) : ℕ))) : ℕ))) else 0) := by
    intro i₀ hi₀
    have hi₀31 : i₀ < 31 := Finset.mem_range.mp hi₀
    by_cases hg : (i₀ ≤ 2 * i ∧ 2 * i ≤ i₀ + 30)
    · rw [if_pos hg]
      exact step1 num h i i₀ hi hi₀31 hg (ih i₀ hi₀31)
    · rw [if_neg hg]
      refine Eq.symm (Finset.sum_eq_zero fun x' _ => Finset.sum_eq_zero fun j _ =>
        Finset.sum_eq_zero fun q _ => ?_)
      exact if_neg (by tauto)
  rw [Finset.sum_congr rfl step1', Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]



set_option maxHeartbeats 2000000 in
/-- The invariant: the carry recurrence computes the tuple sum. -/
private lemma rows_invariant (num h : ℕ) : ∀ i, i < 31 → (carryRows191 (carryWeights191 num) h).getD i 0 = (((∑ x : Fin h → Fin 16 × Fin 16,
    (if ((∑ n : Fin h, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ) + 15 * 2 ^ h = ((∑ n : Fin h, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ) + i * 2 ^ h then ((∏ n : Fin h, (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ) else 0)) : ℕ)) := by
  induction h with
  | zero =>
    intro i hi
    have hrow : (carryRows191 (carryWeights191 num) 0).getD i 0 = if i = 15 then 1 else 0 :=
      rows_base num i
    have hconst : ∀ x : Fin 0 → Fin 16 × Fin 16,
        (if (((∑ n : Fin 0, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + 15 * 2 ^ 0 = (((∑ n : Fin 0, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + i * 2 ^ 0 then (((∏ n : Fin 0, (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ)) else 0)
          = (if i = 15 then 1 else 0) := by
      intro x
      have h2 : (((∑ n : Fin 0, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) = 0 := by simp
      have h3 : (((∑ n : Fin 0, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) = 0 := by simp
      have h1 : (((∏ n : Fin 0, (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ)) = 1 := by simp
      by_cases h : i = 15
      · simp [h2, h3, h1, h]
      · have h' : ¬(15 = i) := fun hh => h hh.symm
        simp [h2, h3, h1, h, h']
    have hsum : (∑ x : Fin 0 → Fin 16 × Fin 16,
        (if (((∑ n : Fin 0, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + 15 * 2 ^ 0 = (((∑ n : Fin 0, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + i * 2 ^ 0 then (((∏ n : Fin 0, (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ)) else 0))
        = ∑ _x : Fin 0 → Fin 16 × Fin 16, (if i = 15 then 1 else 0) :=
      Finset.sum_congr rfl fun x _ => hconst x
    rw [hrow, hsum]
    simp
  | succ h ih =>
    intro i hi
    have hstep : (carryRows191 (carryWeights191 num) (h + 1)).getD i 0 = ∑ i₀ ∈ Finset.range 31,
        (if i₀ ≤ 2 * i ∧ 2 * i ≤ i₀ + 30 then
          (carryRows191 (carryWeights191 num) h).getD i₀ 0 * (carryWeights191 num).getD (2 * i - i₀) 0 else 0) := rows_rec num h i hi
    rw [hstep, step2 num h i hi ih, tSum_succ]
    refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun q _ => ?_
    have key := idx_solutions ((((∑ n : Fin h, (((x' n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ))) ((((∑ n : Fin h, (((x' n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ))) (2 ^ h) i (j : ℕ) (q : ℕ) (by positivity)
      (aOf_le h x') (bOf_le h x') j.isLt q.isLt
    have e1 : (∑ i₀ ∈ Finset.range 31,
          (if i₀ ≤ 2 * i ∧ 2 * i ≤ i₀ + 30 ∧
              (((∑ n : Fin h, (((x' n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + 15 * 2 ^ h = (((∑ n : Fin h, (((x' n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + i₀ * 2 ^ h ∧
              (j : ℕ) + 15 = (q : ℕ) + (2 * i - i₀)
            then (((∏ n : Fin h, (((num ^ (((x' n).1) : ℕ) * 20000 ^ (15 - (((x' n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x' n).1) : ℕ))) : ℕ)) * (((num ^ (((x' n).2) : ℕ) * 20000 ^ (15 - (((x' n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x' n).2) : ℕ))) : ℕ))) : ℕ)) * ((((num ^ ((j : ℕ) : ℕ) * 20000 ^ (15 - ((j : ℕ) : ℕ)) *
    (Nat.factorial 15 / Nat.factorial ((j : ℕ) : ℕ))) : ℕ)) * (((num ^ ((q : ℕ) : ℕ) * 20000 ^ (15 - ((q : ℕ) : ℕ)) *
    (Nat.factorial 15 / Nat.factorial ((q : ℕ) : ℕ))) : ℕ))) else 0))
        = ((((∏ n : Fin h, (((num ^ (((x' n).1) : ℕ) * 20000 ^ (15 - (((x' n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x' n).1) : ℕ))) : ℕ)) * (((num ^ (((x' n).2) : ℕ) * 20000 ^ (15 - (((x' n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x' n).2) : ℕ))) : ℕ))) : ℕ)) * ((((num ^ ((j : ℕ) : ℕ) * 20000 ^ (15 - ((j : ℕ) : ℕ)) *
    (Nat.factorial 15 / Nat.factorial ((j : ℕ) : ℕ))) : ℕ)) * (((num ^ ((q : ℕ) : ℕ) * 20000 ^ (15 - ((q : ℕ) : ℕ)) *
    (Nat.factorial 15 / Nat.factorial ((q : ℕ) : ℕ))) : ℕ)))) *
          ∑ i₀ ∈ Finset.range 31,
            (if i₀ ≤ 2 * i ∧ 2 * i ≤ i₀ + 30 ∧
                (((∑ n : Fin h, (((x' n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + 15 * 2 ^ h = (((∑ n : Fin h, (((x' n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + i₀ * 2 ^ h ∧
                (j : ℕ) + 15 = (q : ℕ) + (2 * i - i₀)
              then (1 : ℕ) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i₀ _ => ?_
      by_cases hK : (i₀ ≤ 2 * i ∧ 2 * i ≤ i₀ + 30 ∧
          (((∑ n : Fin h, (((x' n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + 15 * 2 ^ h = (((∑ n : Fin h, (((x' n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + i₀ * 2 ^ h ∧
          (j : ℕ) + 15 = (q : ℕ) + (2 * i - i₀))
      · rw [if_pos hK, if_pos hK, mul_one]
      · rw [if_neg hK, if_neg hK, mul_zero]
    rw [e1, key]
    by_cases hT : ((((∑ n : Fin h, (((x' n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + ((j : ℕ) * 2 ^ h + 15 * (2 * 2 ^ h))
        = (((∑ n : Fin h, (((x' n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + ((q : ℕ) * 2 ^ h + i * (2 * 2 ^ h)))
    · rw [if_pos hT, if_pos hT, mul_one]
    · rw [if_neg hT, if_neg hT, mul_zero]




/-! ## The Taylor coefficients against the integer certificate -/

private lemma coeff_eq (num j k : ℕ) (hj : j < 16) (hk : k < 16) :
    ((((((num : ℝ) / 10000) / 2) ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) : ℝ)) * ((((((num : ℝ) / 10000) / 2) ^ (k : ℕ) / (Nat.factorial (k : ℕ) : ℝ)) : ℝ))
      = (((((num ^ (j : ℕ) * 20000 ^ (15 - (j : ℕ)) *
    (Nat.factorial 15 / Nat.factorial (j : ℕ))) : ℕ)) : ℝ) * ((((num ^ (k : ℕ) * 20000 ^ (15 - (k : ℕ)) *
    (Nat.factorial 15 / Nat.factorial (k : ℕ))) : ℕ)))) / (carryDen191 : ℝ) := by
  have hjle : j ≤ 15 := by omega
  have hkle : k ≤ 15 := by omega
  have hjd : ((Nat.factorial 15 / Nat.factorial j : ℕ) : ℝ)
      = (Nat.factorial 15 : ℝ) / (Nat.factorial j : ℝ) := by
    have h := Nat.mul_div_cancel' (Nat.factorial_dvd_factorial hjle)
    have h' : (Nat.factorial j : ℝ) * ((Nat.factorial 15 / Nat.factorial j : ℕ) : ℝ)
        = (Nat.factorial 15 : ℝ) := by
      rw [← Nat.cast_mul, h]
    rw [eq_div_iff (by positivity), mul_comm]
    exact h'
  have hkd : ((Nat.factorial 15 / Nat.factorial k : ℕ) : ℝ)
      = (Nat.factorial 15 : ℝ) / (Nat.factorial k : ℝ) := by
    have h := Nat.mul_div_cancel' (Nat.factorial_dvd_factorial hkle)
    have h' : (Nat.factorial k : ℝ) * ((Nat.factorial 15 / Nat.factorial k : ℕ) : ℝ)
        = (Nat.factorial 15 : ℝ) := by
      rw [← Nat.cast_mul, h]
    rw [eq_div_iff (by positivity), mul_comm]
    exact h'
  have hcj : ∀ m : ℕ, ((((((num : ℝ) / 10000) / 2) ^ (m : ℕ) / (Nat.factorial (m : ℕ) : ℝ)) : ℝ)) = ((num : ℝ) / 20000) ^ m / (m.factorial : ℝ) := by
    intro m
    rw [show (num : ℝ) / 10000 / 2 = (num : ℝ) / 20000 by ring]
  rw [hcj j, hcj k]
  have hD : (carryDen191 : ℝ) = ((20000 : ℝ) ^ 15 * (Nat.factorial 15 : ℝ)) ^ 2 := by
    unfold carryDen191
    push_cast
    ring
  rw [hD]
  have hpj : (20000 : ℝ) ^ (15 - j) = (20000 : ℝ) ^ 15 / (20000 : ℝ) ^ j := by
    have h : (20000 : ℝ) ^ (15 - j) * (20000 : ℝ) ^ j = (20000 : ℝ) ^ 15 := by
      rw [← pow_add, Nat.sub_add_cancel hjle]
    rw [eq_div_iff (by positivity)]
    exact h
  have hpk : (20000 : ℝ) ^ (15 - k) = (20000 : ℝ) ^ 15 / (20000 : ℝ) ^ k := by
    have h : (20000 : ℝ) ^ (15 - k) * (20000 : ℝ) ^ k = (20000 : ℝ) ^ 15 := by
      rw [← pow_add, Nat.sub_add_cancel hkle]
    rw [eq_div_iff (by positivity)]
    exact h
  push_cast
  rw [hjd, hkd, hpj, hpk]
  have hinv : ∀ m : ℕ, ((1 : ℝ) / 20000) ^ m = 1 / (20000 : ℝ) ^ m := by
    intro m
    rw [div_pow]
    norm_num
  field_simp
  have h1 : ((num : ℝ) / 20000) ^ j * (20000 : ℝ) ^ j = (num : ℝ) ^ j := by
    rw [← mul_pow]
    congr 1
    ring
  have h2 : ((num : ℝ) / 20000) ^ k * (20000 : ℝ) ^ k = (num : ℝ) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  rw [show ((num : ℝ) / 20000) ^ j * ((num : ℝ) / 20000) ^ k * 20000 ^ j * 20000 ^ k
      = (((num : ℝ) / 20000) ^ j * 20000 ^ j) *
          (((num : ℝ) / 20000) ^ k * 20000 ^ k) by ring,
    h1, h2]

/-- The product of Taylor coefficient pairs over a tuple equals its integer weight over the
common denominator. -/
private lemma prod_coeff_eq (num h : ℕ) (x : Fin h → Fin 16 × Fin 16) :
    (∏ n : Fin h, (((((((num : ℝ) / 10000) / 2) ^ ((x n).1 : ℕ) / (Nat.factorial ((x n).1 : ℕ) : ℝ)) : ℝ)) * ((((((num : ℝ) / 10000) / 2) ^ ((x n).2 : ℕ) / (Nat.factorial ((x n).2 : ℕ) : ℝ)) : ℝ))))
      = ((((∏ n : Fin h, (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ)) : ℝ) / (carryDen191 : ℝ) ^ h := by
  rw [Finset.prod_congr rfl fun n _ =>
      coeff_eq num (x n).1 (x n).2 (x n).1.isLt (x n).2.isLt,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Nat.cast_prod]
  exact Finset.prod_congr rfl fun n _ => by push_cast; ring


/-! ## The sum of the final carry row -/

private lemma list_foldl_add (l : List ℕ) (a : ℕ) : l.foldl (·+·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl, List.sum_cons, ih]
    omega

private lemma foldl_ofFn_sum (n : ℕ) (f : Fin n → ℕ) :
    (Array.ofFn f).foldl (·+·) 0 = ∑ i : Fin n, f i := by
  rw [← Array.foldl_toList, Array.toList_ofFn, list_foldl_add, List.sum_ofFn, Nat.zero_add]

/-- `carryTotal191` is the sum of the entries of the final row. -/
private lemma carryTotal_eq_sum (num h : ℕ) :
    carryTotal191 num h = ∑ i : Fin 31, (carryRows191 (carryWeights191 num) h).getD i 0 := by
  cases h with
  | zero => exact foldl_ofFn_sum 31 _
  | succ k =>
    let g : Fin 31 → ℕ := fun j => ∑ i ∈ Finset.range 31,
      if i ≤ 2 * j.val ∧ 2 * j.val ≤ i + 30 then
        (carryRows191 (carryWeights191 num) k)[i]?.getD 0 *
          (carryWeights191 num)[2 * j.val - i]?.getD 0 else 0
    have harrow : carryRows191 (carryWeights191 num) (k + 1) = Array.ofFn g := rfl
    rw [carryTotal191, harrow, foldl_ofFn_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos i.isLt]
    rfl

/-! ## Divisibility against the carry state -/

/-- `Tof` is the difference of the two digit sums, in `ℤ`. -/
private lemma Tof_eq (hh : ℕ) (x : Fin hh → Fin 16 × Fin 16) :
    ((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ)) = ((((∑ n : Fin hh, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) : ℤ) - ((((∑ n : Fin hh, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) : ℤ) := by
  push_cast
  ring

private lemma mul_two_pow_cancel {a b h : ℕ} (hEq : a * 2 ^ h = b * 2 ^ h) : a = b :=
  Nat.eq_of_mul_eq_mul_right (by positivity) hEq

/-- The exponent sum of a tuple is divisible by `2 ^ h` exactly when the carry state of the
final row is one of the 31 admissible values. -/
private lemma dvd_iff_carry (A B h : ℕ) (hA : A ≤ 15 * (2 ^ h - 1)) (hB : B ≤ 15 * (2 ^ h - 1)) :
    ((2 : ℤ) ^ h ∣ (A : ℤ) - (B : ℤ)) ↔
      ∃ i : ℕ, i < 31 ∧ A + 15 * 2 ^ h = B + i * 2 ^ h := by
  have hPpos : (0 : ℤ) < (2 : ℤ) ^ h := by positivity
  have hP1 : (1 : ℤ) ≤ (2 : ℤ) ^ h := by
    have h := hPpos
    omega
  have hn1 : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  have hAz : (A : ℤ) ≤ 15 * ((2 : ℤ) ^ h - 1) := by
    have hcast : ((15 * (2 ^ h - 1) : ℕ) : ℤ) = 15 * ((2 : ℤ) ^ h - 1) := by
      push_cast [Nat.cast_sub hn1]
      ring
    rw [← hcast]
    exact_mod_cast hA
  have hBz : (B : ℤ) ≤ 15 * ((2 : ℤ) ^ h - 1) := by
    have hcast : ((15 * (2 ^ h - 1) : ℕ) : ℤ) = 15 * ((2 : ℤ) ^ h - 1) := by
      push_cast [Nat.cast_sub hn1]
      ring
    rw [← hcast]
    exact_mod_cast hB
  constructor
  · rintro ⟨m, hm⟩
    have hdiff : (A : ℤ) - (B : ℤ) = (2 : ℤ) ^ h * m := by rw [hm]
    have hle : (A : ℤ) - (B : ℤ) ≤ 15 * ((2 : ℤ) ^ h - 1) := by linarith
    have hge : -((2 : ℤ) ^ h) * 15 < (A : ℤ) - (B : ℤ) := by nlinarith
    have habs : |m| * (2 : ℤ) ^ h = |(A : ℤ) - (B : ℤ)| := by
      rw [hdiff, abs_mul, abs_of_pos hPpos, mul_comm]
    have hlt : |m| * (2 : ℤ) ^ h < 15 * (2 : ℤ) ^ h := by
      rw [habs]
      have h1 : |(A : ℤ) - (B : ℤ)| ≤ 15 * ((2 : ℤ) ^ h - 1) := by
        rw [abs_le]
        constructor <;> nlinarith
      have h2 : 15 * ((2 : ℤ) ^ h - 1) < 15 * (2 : ℤ) ^ h := by linarith
      linarith
    have hm15 : |m| < 15 := by
      by_contra hc
      push_neg at hc
      have : 15 * (2 : ℤ) ^ h ≤ |m| * (2 : ℤ) ^ h := by
        have h0 : (0 : ℤ) ≤ (2 : ℤ) ^ h := le_of_lt hPpos
        exact mul_le_mul_of_nonneg_right hc h0
      linarith
    have hm_lo : -15 < m := (abs_lt.mp hm15).1
    have hm_hi : m < 15 := (abs_lt.mp hm15).2
    have hnonneg : 0 ≤ m + 15 := by omega
    refine ⟨(m + 15).toNat, ?_, ?_⟩
    · have hi : (((m + 15).toNat : ℕ) : ℤ) = m + 15 := Int.toNat_of_nonneg hnonneg
      have : ((m + 15).toNat : ℤ) < 31 := by rw [hi]; omega
      exact_mod_cast this
    · have hi : (((m + 15).toNat : ℕ) : ℤ) = m + 15 := Int.toNat_of_nonneg hnonneg
      have hkey : ((A + 15 * 2 ^ h : ℕ) : ℤ) = ((B + (m + 15).toNat * 2 ^ h : ℕ) : ℤ) := by
        push_cast
        rw [hi]
        linarith
      exact_mod_cast hkey
  · rintro ⟨i, hi, hEq⟩
    refine ⟨(i : ℤ) - 15, ?_⟩
    have hkey : ((A + 15 * 2 ^ h : ℕ) : ℤ) = ((B + i * 2 ^ h : ℕ) : ℤ) := by exact_mod_cast hEq
    push_cast at hkey
    linarith

/-- The 31 carry states collect the divisible tuples exactly once. -/
private lemma sum_tSum_eq (num h : ℕ) :
    ∑ i ∈ Finset.range 31, (((∑ x : Fin h → Fin 16 × Fin 16,
    (if ((∑ n : Fin h, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ) + 15 * 2 ^ h = ((∑ n : Fin h, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ) + i * 2 ^ h then ((∏ n : Fin h, (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ) else 0)) : ℕ))
      = ∑ x : Fin h → Fin 16 × Fin 16,
          (if (2 : ℤ) ^ h ∣ ((((∑ n : Fin h, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin h, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ)) then (((∏ n : Fin h, (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ)) else 0) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => (((∑ x : Fin h → Fin 16 × Fin 16,
    (if ((∑ n : Fin h, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ) + 15 * 2 ^ h = ((∑ n : Fin h, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ) + i * 2 ^ h then ((∏ n : Fin h, (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ) else 0)) : ℕ))) 31, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Tof_eq h x]
  have hfac : ∀ i : Fin 31,
      (if (((∑ n : Fin h, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + 15 * 2 ^ h = (((∑ n : Fin h, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + (i : ℕ) * 2 ^ h then (((∏ n : Fin h, (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ)) else 0)
        = (((∏ n : Fin h, (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ)) *
            (if (((∑ n : Fin h, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + 15 * 2 ^ h = (((∑ n : Fin h, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + (i : ℕ) * 2 ^ h then 1 else 0) := by
    intro i
    by_cases hc : (((∑ n : Fin h, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + 15 * 2 ^ h = (((∑ n : Fin h, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + (i : ℕ) * 2 ^ h
    · rw [if_pos hc, if_pos hc, mul_one]
    · rw [if_neg hc, if_neg hc, mul_zero]
  rw [Finset.sum_congr rfl fun i _ => hfac i, ← Finset.mul_sum]
  set S := Finset.univ.filter (fun i : Fin 31 =>
    (((∑ n : Fin h, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + 15 * 2 ^ h = (((∑ n : Fin h, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + (i : ℕ) * 2 ^ h) with hS
  have huniq : ∀ i ∈ S, ∀ i' ∈ S, i = i' := by
    intro i hi i' hi'
    rw [Finset.mem_filter] at hi hi'
    have h2 : (i : ℕ) * 2 ^ h = (i' : ℕ) * 2 ^ h :=
      Nat.add_left_cancel (hi.2.symm.trans hi'.2)
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by positivity) h2)
  have hiff : (∃ i : Fin 31, (((∑ n : Fin h, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + 15 * 2 ^ h = (((∑ n : Fin h, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + (i : ℕ) * 2 ^ h)
      ↔ ((2 : ℤ) ^ h ∣ ((((∑ n : Fin h, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) : ℤ) - ((((∑ n : Fin h, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) : ℤ)) := by
    have hb := dvd_iff_carry ((((∑ n : Fin h, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ))) ((((∑ n : Fin h, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ))) h (aOf_le h x) (bOf_le h x)
    constructor
    · rintro ⟨i, hi⟩
      exact hb.mpr ⟨(i : ℕ), i.isLt, hi⟩
    · rintro hd
      obtain ⟨i, hi, hc⟩ := hb.mp hd
      exact ⟨⟨i, hi⟩, hc⟩
  have hcard : S.card = (if (∃ i : Fin 31,
      (((∑ n : Fin h, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + 15 * 2 ^ h = (((∑ n : Fin h, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + (i : ℕ) * 2 ^ h) then 1 else 0) := by
    by_cases hex : ∃ i : Fin 31, (((∑ n : Fin h, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + 15 * 2 ^ h = (((∑ n : Fin h, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) + (i : ℕ) * 2 ^ h
    · rw [if_pos hex]
      obtain ⟨i₀, hi₀⟩ := hex
      have hle : S.card ≤ 1 := by
        rw [Finset.card_le_one]
        exact huniq
      have hpos : 0 < S.card := by
        rw [Finset.card_pos]
        exact ⟨i₀, by rw [hS]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩⟩
      omega
    · rw [if_neg hex]
      have h0 : S.card = 0 := by
        rw [Finset.card_eq_zero]
        rw [hS, Finset.filter_eq_empty_iff]
        intro i _ hi
        exact hex ⟨i, hi⟩
      omega
  rw [← Finset.card_filter, hcard]
  by_cases hd : (2 : ℤ) ^ h ∣ ((((∑ n : Fin h, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) : ℤ) - ((((∑ n : Fin h, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ)) : ℤ)
  · rw [if_pos (hiff.mpr hd), if_pos hd, mul_one]
  · rw [if_neg (fun hc => hd (hiff.mp hc)), if_neg hd, mul_zero]

/-! ## The leaf -/

/-- LEAF. Heath-Brown and Puchta 2002, display 44 on page 30 and the power of two
congruence constraint below display 46 on page 31. The dyadic average of the finite
Taylor products equals the integer carry recurrence divided by its common denominator.
This is a lab encoding of the finite Fourier orthogonality step. All final carries are summed. -/
theorem polynomialAverage_eq_carry191 (num hh : ℕ) :
    polynomialAverage191 ((num : ℝ) / 10000) hh =
      (carryTotal191 num hh : ℝ) / (carryDen191 : ℝ) ^ hh := by
  rw [polynomialAverage_eq_sum ((num : ℝ) / 10000) hh]
  have hterm : ∀ x : Fin hh → Fin 16 × Fin 16,
      (if (2 : ℤ) ^ hh ∣ ((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ)) then
        (∏ n : Fin hh, (((((((num : ℝ) / 10000) / 2) ^ ((x n).1 : ℕ) / (Nat.factorial ((x n).1 : ℕ) : ℝ)) : ℝ)) *
          ((((((num : ℝ) / 10000) / 2) ^ ((x n).2 : ℕ) / (Nat.factorial ((x n).2 : ℕ) : ℝ)) : ℝ)))) else 0)
      = (if (2 : ℤ) ^ hh ∣ ((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ)) then ((((∏ n : Fin hh, (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ)) : ℝ) else 0) /
          (carryDen191 : ℝ) ^ hh := by
    intro x
    by_cases hx : (2 : ℤ) ^ hh ∣ ((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ))
    · rw [if_pos hx, if_pos hx, prod_coeff_eq]
    · rw [if_neg hx, if_neg hx, zero_div]
  rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.sum_div]
  have hcast : (∑ x : Fin hh → Fin 16 × Fin 16,
        (if (2 : ℤ) ^ hh ∣ ((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ)) then ((((∏ n : Fin hh, (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ)) : ℝ) else 0))
      = (((∑ x : Fin hh → Fin 16 × Fin 16,
        (if (2 : ℤ) ^ hh ∣ ((((∑ n : Fin hh, (((x n).1 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ))) -
    (∑ n : Fin hh, (((x n).2 : ℕ) : ℤ) * ((2 : ℤ) ^ (n : ℕ)))) : ℤ)) then (((∏ n : Fin hh, (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ)) else 0)) : ℕ) : ℝ) := by
    push_cast
    rfl
  have hnat : (∑ i ∈ Finset.range 31,
        (carryRows191 (carryWeights191 num) hh).getD i 0) = carryTotal191 num hh := by
    rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      (carryRows191 (carryWeights191 num) hh).getD i 0) 31, ← carryTotal_eq_sum]
  have hnatR : ((∑ i ∈ Finset.range 31,
        (carryRows191 (carryWeights191 num) hh).getD i 0 : ℕ) : ℝ)
      = (carryTotal191 num hh : ℝ) := by
    rw [hnat]
  have hstep : ((∑ i ∈ Finset.range 31, (((∑ x : Fin hh → Fin 16 × Fin 16,
    (if ((∑ n : Fin hh, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ) + 15 * 2 ^ hh = ((∑ n : Fin hh, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ) + i * 2 ^ hh then ((∏ n : Fin hh, (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ) else 0)) : ℕ)) : ℕ) : ℝ)
      = ((∑ i ∈ Finset.range 31,
          (carryRows191 (carryWeights191 num) hh).getD i 0 : ℕ) : ℝ) := by
    rw [show (∑ i ∈ Finset.range 31, (((∑ x : Fin hh → Fin 16 × Fin 16,
    (if ((∑ n : Fin hh, (((x n).1 : ℕ) * 2 ^ (n : ℕ))) : ℕ) + 15 * 2 ^ hh = ((∑ n : Fin hh, (((x n).2 : ℕ) * 2 ^ (n : ℕ))) : ℕ) + i * 2 ^ hh then ((∏ n : Fin hh, (((num ^ (((x n).1) : ℕ) * 20000 ^ (15 - (((x n).1) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).1) : ℕ))) : ℕ)) * (((num ^ (((x n).2) : ℕ) * 20000 ^ (15 - (((x n).2) : ℕ)) *
  (Nat.factorial 15 / Nat.factorial (((x n).2) : ℕ))) : ℕ))) : ℕ) else 0)) : ℕ)))
        = ∑ i ∈ Finset.range 31, (carryRows191 (carryWeights191 num) hh).getD i 0 from
      Finset.sum_congr rfl fun i hi => (rows_invariant num hh i (Finset.mem_range.mp hi)).symm]
  rw [hcast, ← sum_tSum_eq num hh, hstep, hnatR]

end PolynomialAverageCarry191

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
