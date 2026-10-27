/-
Pintz and Althöfer, "The Goldbach exceptional set: an exponent of 7/12 and conditional
refinements", arXiv 2610.15559v1, 11 October 2026, read in Chrome by run 20261019T2003Z-20508,
unit U-1103, T2 FRONTIER, idea I-0080. Not one of the 100 catalogued papers.

What is here:
* `Hθ`, the hypothesis (1.1): every nontrivial zero of every primitive Dirichlet L-function has
  real part at most θ.
* `theorem1_stmt`, `corollary2_stmt`, `theorem3_stmt`: the paper's three results, as cited Props,
  NOT proved here. `openAI78_stmt` is the external input [6, Theorem 1.1], NOT proved here.
* PROVED unconditional: every exponent identity and inequality the paper prints, Sections 1, 3,
  4.2, 4.5 and 5: g = 2a − 1, the closed form of g, the table, g strictly increasing with slope
  at least 5/16, h with slope at least 5/32, a ≥ 3/4, D − 1/2 ≥ 1/4, the 11/20 threshold
  (61 − √201)/80, the 13/24 comparison, the 7/10 Guth-Maynard boundary, δ < 1/72.
* PROVED CONDITIONAL ON `BesselInput θ`, the Section 4.4 L² input: `theorem3_of_bessel`, the
  paper's last step, Bessel count to window bound to dyadic sum, giving E(X) ≪ X^{g(θ)+ε}.
* `corollary2_of_cited`: Corollary 2 from the two cited Props, a composition only.

AI wrote this Lean code. Binary Goldbach is OPEN. The 7/8 theorem is an external claim the lab
has not checked.
-/
import LeanLab.ExceptionalSet.MVConditional

namespace LeanLab.ExceptionalSet.PintzAlthofer2026

open Real Finset

attribute [local instance] Classical.propDecidable

/-! ### The hypothesis and the cited statements -/

/-- (1.1) `H_θ`: every nontrivial zero of every primitive Dirichlet L-function, the zeta
function included as conductor one, has real part at most `θ`. Nontrivial: `0 < Re s < 1`. -/
def Hθ (θ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re ≤ θ

/-- Theorem 1, cited: a fixed zero-free half-plane `Re s > θ₀`, `θ₀ < 1`, gives
`E(X) ≪_ε X^{7/12+ε}` for every `ε > 0`. -/
def theorem1_stmt : Prop :=
  ∀ θ₀ : ℝ, 1 / 2 ≤ θ₀ → θ₀ < 1 → Hθ θ₀ → ∀ ε : ℝ, 0 < ε → PowerBound (7 / 12 + ε)

/-- The external input [6, Theorem 1.1], OpenAI Math Release, 30 September 2026, as the paper
uses it: `H_{7/8}`. Cited, not checked by the lab. -/
def openAI78_stmt : Prop := Hθ (7 / 8)

/-- Corollary 2, cited: `E(X) ≪_ε X^{7/12+ε}`. -/
def corollary2_stmt : Prop := ∀ ε : ℝ, 0 < ε → PowerBound (7 / 12 + ε)

/-! ### The exponents -/

/-- Ingham-Montgomery density exponent (4.1), `D(σ) = 3(1 − σ)/(2 − σ)`. -/
noncomputable def D (σ : ℝ) : ℝ := 3 * (1 - σ) / (2 - σ)

/-- (4.4) `a(θ) = θ − 1/4 + 3(1 − θ)/(2(2 − θ))`. -/
noncomputable def a (θ : ℝ) : ℝ := θ - 1 / 4 + 3 * (1 - θ) / (2 * (2 - θ))

/-- (1.3) `g(θ) = θ(5 − 4θ)/(2(2 − θ))`. -/
noncomputable def g (θ : ℝ) : ℝ := θ * (5 - 4 * θ) / (2 * (2 - θ))

/-- Theorem 3, cited: `H_θ`, `1/2 ≤ θ ≤ 2/3`, gives `E(X) ≪ X^{g(θ)+ε}`. -/
def theorem3_stmt : Prop :=
  ∀ θ : ℝ, 1 / 2 ≤ θ → θ ≤ 2 / 3 → Hθ θ → ∀ ε : ℝ, 0 < ε → PowerBound (g θ + ε)

/-- Section 4.2: `a = h`, `h(σ) = σ − 1/4 + D(σ)/2`. -/
theorem a_eq_h (σ : ℝ) : a σ = σ - 1 / 4 + D σ / 2 := by
  unfold a D; rw [mul_comm (2 : ℝ) (2 - σ), ← div_div]

/-- (1.3), first form: `g = 2a − 1 = 2θ − 3/2 + 3(1 − θ)/(2 − θ)`. -/
theorem two_a_sub_one (θ : ℝ) : 2 * a θ - 1 = 2 * θ - 3 / 2 + 3 * (1 - θ) / (2 - θ) := by
  unfold a; rw [mul_comm (2 : ℝ) (2 - θ), ← div_div]; ring

/-- (1.3), the two printed forms agree: `2a(θ) − 1 = g(θ)` for `θ ≠ 2`. -/
theorem g_eq_two_a_sub_one {θ : ℝ} (h : θ ≠ 2) : g θ = 2 * a θ - 1 := by
  have h2 : (2 : ℝ) - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  unfold g a
  field_simp
  ring

/-- `g(θ) = 2θ + 3/2 − 3/(2 − θ)`, the form used for monotonicity. -/
theorem g_alt {θ : ℝ} (h : θ ≠ 2) : g θ = 2 * θ + 3 / 2 - 3 / (2 - θ) := by
  have h2 : (2 : ℝ) - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  unfold g
  field_simp
  ring

theorem g_two_thirds : g (2 / 3) = 7 / 12 := by norm_num [g]
theorem g_13_20 : g (13 / 20) = 26 / 45 := by norm_num [g]
theorem g_5_8 : g (5 / 8) = 25 / 44 := by norm_num [g]
theorem g_3_5 : g (3 / 5) = 39 / 70 := by norm_num [g]
theorem g_7_12 : g (7 / 12) = 28 / 51 := by norm_num [g]
theorem g_half : g (1 / 2) = 1 / 2 := by norm_num [g]

/-- Section 1: `7/12 − 25/44 = 1/66`. -/
theorem gap_5_8 : (7 : ℝ) / 12 - 25 / 44 = 1 / 66 := by norm_num

/-- Section 4.5: on `[1/2, 2/3]`, `g y − g x ≥ (5/16)(y − x)`, the printed `g' ≥ 5/16`. -/
theorem g_slope {x y : ℝ} (hx : 1 / 2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2 / 3) :
    5 / 16 * (y - x) ≤ g y - g x := by
  have hx2 : x ≠ 2 := by intro h; linarith
  have hy2 : y ≠ 2 := by intro h; linarith
  rw [g_alt hx2, g_alt hy2]
  have ha : 0 < 2 - x := by linarith
  have hb : 0 < 2 - y := by linarith
  have hprod : (16 : ℝ) / 9 ≤ (2 - x) * (2 - y) := by nlinarith
  have key : 3 / (2 - x) - 3 / (2 - y) = -(3 * (y - x)) / ((2 - x) * (2 - y)) := by
    field_simp; ring
  have hq : 3 * (y - x) / ((2 - x) * (2 - y)) ≤ 27 / 16 * (y - x) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hprod)]
  have : g y - g x = 2 * (y - x) - 3 * (y - x) / ((2 - x) * (2 - y)) := by
    rw [g_alt hx2, g_alt hy2]
    have : -(3 * (y - x)) / ((2 - x) * (2 - y)) = -(3 * (y - x) / ((2 - x) * (2 - y))) :=
      neg_div _ _
    linarith [key]
  rw [g_alt hx2, g_alt hy2] at this
  linarith

/-- `g` is strictly increasing on `[1/2, 2/3]`. -/
theorem g_strictMonoOn : StrictMonoOn g (Set.Icc (1 / 2) (2 / 3)) := by
  intro x hx y hy hxy
  have := g_slope hx.1 hxy.le hy.2
  linarith

/-- Every fixed `θ < 2/3` in range gives an exponent strictly below `7/12`. -/
theorem g_lt_7_12 {θ : ℝ} (h1 : 1 / 2 ≤ θ) (h2 : θ < 2 / 3) : g θ < 7 / 12 := by
  have := g_strictMonoOn ⟨h1, h2.le⟩ ⟨by norm_num, le_rfl⟩ h2
  rwa [g_two_thirds] at this

/-- `g ≥ 1/2` on `[1/2, 2/3]`. -/
theorem g_ge_half {θ : ℝ} (h1 : 1 / 2 ≤ θ) (h2 : θ ≤ 2 / 3) : 1 / 2 ≤ g θ := by
  have := g_slope le_rfl h1 h2
  rw [g_half] at this; linarith

/-- Section 4.2: `h' ≥ 5/32`, as a slope bound for `a = h` on `[1/2, 2/3]`. -/
theorem a_slope {x y : ℝ} (hx : 1 / 2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2 / 3) :
    5 / 32 * (y - x) ≤ a y - a x := by
  have hx2 : x ≠ 2 := by intro h; linarith
  have hy2 : y ≠ 2 := by intro h; linarith
  have := g_slope hx hxy hy
  rw [g_eq_two_a_sub_one hx2, g_eq_two_a_sub_one hy2] at this
  linarith

/-- `a(θ) ≥ a(1/2) = 3/4` on `[1/2, 2/3]`. -/
theorem a_ge {θ : ℝ} (h1 : 1 / 2 ≤ θ) (h2 : θ ≤ 2 / 3) : 3 / 4 ≤ a θ := by
  have := a_slope le_rfl h1 h2
  have h : a (1 / 2) = 3 / 4 := by norm_num [a]
  linarith

/-- Section 4.4: `2a(θ) − 1 ≥ 1/2`, so the dyadic sum converges. -/
theorem two_a_sub_one_ge {θ : ℝ} (h1 : 1 / 2 ≤ θ) (h2 : θ ≤ 2 / 3) : 1 / 2 ≤ 2 * a θ - 1 := by
  linarith [a_ge h1 h2]

/-- Section 4.2: `D(σ) − 1/2 ≥ 1/4` for `1/2 ≤ σ ≤ 2/3`. -/
theorem D_sub_half_ge {σ : ℝ} (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 2 / 3) : 1 / 4 ≤ D σ - 1 / 2 := by
  unfold D
  have hb : 0 < 2 - σ := by linarith
  rw [le_sub_iff_add_le, le_div_iff₀ hb]
  nlinarith

/-- Section 4.5: the 11/20 threshold. `θ* = (61 − √201)/80` has `g(θ*) = 11/20`. -/
theorem g_threshold : g ((61 - Real.sqrt 201) / 80) = 11 / 20 := by
  have hs : Real.sqrt 201 ^ 2 = 201 := Real.sq_sqrt (by norm_num)
  have hs14 : (14 : ℝ) < Real.sqrt 201 := by
    rw [show (14 : ℝ) = Real.sqrt (14 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hden : (2 : ℝ) * (2 - (61 - Real.sqrt 201) / 80) ≠ 0 := by
    have : 0 < Real.sqrt 201 := by linarith
    nlinarith
  unfold g
  rw [div_eq_iff hden]
  linear_combination (-1 / 1600 : ℝ) * hs

/-- `θ*` lies in `(1/2, 2/3)`, numerically `0.58528...`. -/
theorem threshold_mem : 1 / 2 < (61 - Real.sqrt 201) / 80 ∧ (61 - Real.sqrt 201) / 80 < 2 / 3 := by
  have h14 : (14 : ℝ) < Real.sqrt 201 := by
    rw [show (14 : ℝ) = Real.sqrt (14 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h15 : Real.sqrt 201 < 15 := by
    rw [show (15 : ℝ) = Real.sqrt (15 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  constructor <;> linarith

/-- Below `θ*` the exponent is below `11/20 = 0.55`. -/
theorem g_lt_11_20 {θ : ℝ} (h1 : 1 / 2 ≤ θ) (h2 : θ < (61 - Real.sqrt 201) / 80) :
    g θ < 11 / 20 := by
  have hm := threshold_mem
  have := g_strictMonoOn ⟨h1, by linarith⟩ ⟨hm.1.le, hm.2.le⟩ h2
  rwa [g_threshold] at this

/-- Section 4.5: the total count alone gives `2θ − 1/2`, below `7/12` iff `θ < 13/24`. -/
theorem weak_exponent_iff (θ : ℝ) : 2 * θ - 1 / 2 < 7 / 12 ↔ θ < 13 / 24 := by
  constructor <;> intro h <;> linarith

/-- Section 5: Guth-Maynard's exponent beats Ingham's, for `1/2 ≤ σ < 1`, iff `σ > 7/10`. -/
theorem gm_lt_ingham_iff {σ : ℝ} (h1 : 1 / 2 ≤ σ) (h2 : σ < 1) :
    15 * (1 - σ) / (3 + 5 * σ) < 3 * (1 - σ) / (2 - σ) ↔ 7 / 10 < σ := by
  have ha : 0 < 3 + 5 * σ := by linarith
  have hb : 0 < 2 - σ := by linarith
  have hc : 0 < 1 - σ := by linarith
  rw [div_lt_div_iff₀ ha hb]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Section 3: `5/9 + 2δ < 7/12` iff `δ < 1/72`. -/
theorem theorem1_delta_iff (δ : ℝ) : 5 / 9 + 2 * δ < 7 / 12 ↔ δ < 1 / 72 := by
  constructor <;> intro h <;> linarith

/-- Section 1: the minor arc exponents, `2·4/5 − 1 = 3/5`, `2·19/24 − 1 = 7/12`. -/
theorem minor_exponents : (2 : ℝ) * (4 / 5) - 1 = 3 / 5 ∧ (2 : ℝ) * (19 / 24) - 1 = 7 / 12 := by
  constructor <;> norm_num

/-! ### Section 4.4, from the Bessel inequality to the power bound -/

/-- The bad even numbers in `(x/2, x]`; its card is `MV.badWindow x`. -/
noncomputable def windowSet (x : ℕ) : Finset ℕ :=
  (Finset.Icc (x / 2 + 1) x).filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)

theorem card_windowSet (x : ℕ) : (windowSet x).card = MV.badWindow x := rfl

/-- The L² input of Section 4.4, CITED: for every `η > 0`, for large `x`, real coefficients,
the absolute values of the Fourier coefficients of `F_X² − V_X²`, that are at least `c x` at
every bad even `n` in `(x/2, x]`, by (4.18) and (4.19), and whose squares sum, by Bessel and
(4.13), to at most `K x^{2a(θ)+1+2η} log x`. -/
def BesselInput (θ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ K c : ℝ, ∃ X0 : ℕ, 0 < c ∧ ∀ x : ℕ, X0 ≤ x →
    ∃ coef : ℕ → ℝ, (∀ n ∈ windowSet x, c * x ≤ |coef n|) ∧
      ∑ n ∈ windowSet x, coef n ^ 2 ≤ K * (x : ℝ) ^ (2 * a θ + 1 + 2 * η) * Real.log x

/-- Bessel counting: `|coef| ≥ m ≥ 0` on `S` and `Σ coef² ≤ B` give `#S · m² ≤ B`. -/
theorem card_mul_sq_le {S : Finset ℕ} {coef : ℕ → ℝ} {m B : ℝ} (hm : 0 ≤ m)
    (hlow : ∀ n ∈ S, m ≤ |coef n|) (hsum : ∑ n ∈ S, coef n ^ 2 ≤ B) :
    (S.card : ℝ) * m ^ 2 ≤ B := by
  have : ∑ n ∈ S, m ^ 2 ≤ ∑ n ∈ S, coef n ^ 2 := by
    apply Finset.sum_le_sum
    intro n hn
    have := hlow n hn
    rw [← sq_abs (coef n)]
    exact pow_le_pow_left₀ hm this 2
  rw [Finset.sum_const, nsmul_eq_mul] at this
  linarith

/-- The window bound from the L² input, with exponent `2a(θ) − 1 + 3η`. -/
theorem window_of_bessel_eta {θ η K c : ℝ} {X0 : ℕ} (hη : 0 < η) (hc : 0 < c)
    (h : ∀ x : ℕ, X0 ≤ x → ∃ coef : ℕ → ℝ, (∀ n ∈ windowSet x, c * x ≤ |coef n|) ∧
      ∑ n ∈ windowSet x, coef n ^ 2 ≤ K * (x : ℝ) ^ (2 * a θ + 1 + 2 * η) * Real.log x) :
    MV.WindowBound (2 * a θ - 1 + 3 * η) (max K 0 / (c ^ 2 * η)) (max X0 1) := by
  intro x hx
  obtain ⟨coef, hlow, hsum⟩ := h x (le_trans (le_max_left _ _) hx)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := by linarith
  set e := 2 * a θ - 1 + 3 * η with he
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog : Real.log x ≤ (x : ℝ) ^ η / η := Real.log_le_rpow_div hx0.le hη
  have hK : K * (x : ℝ) ^ (2 * a θ + 1 + 2 * η) * Real.log x
      ≤ max K 0 * (x : ℝ) ^ (2 * a θ + 1 + 2 * η) * Real.log x := by
    gcongr
    · exact le_max_left _ _
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have hpow : (x : ℝ) ^ (2 * a θ + 1 + 2 * η) * (x : ℝ) ^ η = (x : ℝ) ^ e * (x : ℝ) ^ 2 := by
    rw [← Real.rpow_add hx0, ← Real.rpow_natCast, ← Real.rpow_add hx0]
    congr 1; push_cast; rw [he]; ring
  have hB : ∑ n ∈ windowSet x, coef n ^ 2 ≤ max K 0 / η * ((x : ℝ) ^ e * (x : ℝ) ^ 2) := by
    calc ∑ n ∈ windowSet x, coef n ^ 2
        ≤ max K 0 * (x : ℝ) ^ (2 * a θ + 1 + 2 * η) * Real.log x := hsum.trans hK
      _ ≤ max K 0 * (x : ℝ) ^ (2 * a θ + 1 + 2 * η) * ((x : ℝ) ^ η / η) := by gcongr
      _ = max K 0 / η * ((x : ℝ) ^ (2 * a θ + 1 + 2 * η) * (x : ℝ) ^ η) := by ring
      _ = max K 0 / η * ((x : ℝ) ^ e * (x : ℝ) ^ 2) := by rw [hpow]
  have hcard := card_mul_sq_le (mul_nonneg hc.le hx0.le) hlow hB
  rw [← card_windowSet]
  have hcx : 0 < (c * x) ^ 2 := by positivity
  have : ((windowSet x).card : ℝ) ≤ max K 0 / η * ((x : ℝ) ^ e * (x : ℝ) ^ 2) / (c * x) ^ 2 := by
    rw [le_div_iff₀ hcx]; exact hcard
  calc ((windowSet x).card : ℝ) ≤ max K 0 / η * ((x : ℝ) ^ e * (x : ℝ) ^ 2) / (c * x) ^ 2 := this
    _ = max K 0 / (c ^ 2 * η) * (x : ℝ) ^ e := by
        field_simp

/-- Theorem 3's last step, PROVED CONDITIONAL ON `BesselInput θ`: for `1/2 ≤ θ ≤ 2/3`,
`E(X) ≪ X^{g(θ)+ε}` for every `ε > 0`. -/
theorem theorem3_of_bessel {θ : ℝ} (h1 : 1 / 2 ≤ θ) (h2 : θ ≤ 2 / 3) (hB : BesselInput θ) :
    ∀ ε : ℝ, 0 < ε → PowerBound (g θ + ε) := by
  intro ε hε
  obtain ⟨K, c, X0, hc, h⟩ := hB (ε / 3) (by positivity)
  have hw := window_of_bessel_eta (by positivity) hc h
  have hθ2 : θ ≠ 2 := by intro h; linarith
  have hexp : 2 * a θ - 1 + 3 * (ε / 3) = g θ + ε := by
    rw [g_eq_two_a_sub_one hθ2]; ring
  rw [hexp] at hw
  exact MV.powerBound_of_window (by linarith [g_ge_half h1 h2]) hw

/-- Corollary 2 from the two cited inputs, Theorem 1 and the external 7/8 theorem. -/
theorem corollary2_of_cited (h1 : theorem1_stmt) (h78 : openAI78_stmt) : corollary2_stmt :=
  fun ε hε => h1 (7 / 8) (by norm_num) (by norm_num) h78 ε hε

/-- Theorem 3 at `θ = 5/8`, CONDITIONAL ON its Bessel input: `E(X) ≪ X^{25/44+ε}`. -/
theorem five_eighths_of_bessel (hB : BesselInput (5 / 8)) :
    ∀ ε : ℝ, 0 < ε → PowerBound (25 / 44 + ε) := by
  intro ε hε
  have := theorem3_of_bessel (by norm_num) (by norm_num) hB ε hε
  rwa [g_5_8] at this

/-- Vacuity check for `Hθ`: the hypothesis is a genuine restriction on `θ` only through zeros;
at `θ = 1` it holds outright, since nontrivial zeros are taken with `Re s < 1`. -/
theorem Hθ_one : Hθ 1 := by
  intro q _ χ _ s _ hs1 _
  exact hs1.le

/-- `Hθ` is monotone in `θ`, so `H_{7/8}` follows from `H_θ` for any `θ ≤ 7/8`. -/
theorem Hθ_mono {θ θ' : ℝ} (h : θ ≤ θ') (hθ : Hθ θ) : Hθ θ' :=
  fun q _ χ hχ s h0 h1 hz => (hθ q χ hχ s h0 h1 hz).trans h

end LeanLab.ExceptionalSet.PintzAlthofer2026
