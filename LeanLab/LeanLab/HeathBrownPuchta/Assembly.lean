import LeanLab.HeathBrownPuchta.Numerics
import LeanLab.Linnik.Statements

/-!
# Heath-Brown and Puchta 2002, Section 6: the main theorems from their named analytic inputs

Lab proof, unit U-1272, PC run 20261020T2004Z-7678. AI wrote the Lean code. P0012, arXiv
math/0201299, Sections 5 and 6.

The paper writes `R(N) = ∫₀¹ S(α)² T(α)^K e(-αN) dα` and splits `[0,1]` into the major arcs `𝔐`,
the minor arcs outside `𝒜_λ = {α : |T(α)| ≥ λL}`, and the minor arcs inside `𝒜_λ`. With the
scale `X(N) = C₀ N L^{K-2} / log² 2` it uses:

* Lemma 7, major arcs: `∫_𝔐 ≥ (2.7895 (1 - 3ϖ) + o(1)) X(N)`;
* Lemma 9 and `|T| < λL` off `𝒜_λ`: `|∫_{𝔪 \ 𝒜_λ}| ≤ λ^{K-2} ((C₁ - 2 + 2ϖ) C₂ + log 2 / C₀ + o(1)) X(N)`,
  with `C₁ = 7.8342`, Chen; `C₂ ≤ 2.2141`; `C₀ ≥ 0.66`;
* Lemma 1 and the sup bound `S(α) ≪ N^{θ + o(1)}` on `𝔪`:
  `|∫_{𝔪 ∩ 𝒜_λ}| ≪ N^{2θ - E(λ) + o(1)}`, with `θ = 263/308 + 3ϖ`, Vaughan, or `θ = 3/4` on GRH,
  Baker and Harman, and `E(0.863665) > 109/154`, `E(0.722428) > 1/2`;
* the circle method identity: `R(N) > 0` gives a representation.

PROVED here, unconditional: `lemma10_of_lemma9`, Lemma 10's `13.968` from Lemma 9 for every
`0 ≤ ϖ ≤ 10⁻⁵`; `uncond_exponent`, `grh_exponent`, the identities `2 · 263/308 - 1 = 109/154` and
`2 · 3/4 - 1 = 1/2` behind Lemma 1's two exponents; `small_of_rpow`, `N^b = o(N)` for `b < 1`;
`scale_of_L`; `crit13`, `crit7`; `section6_positive`, the Section 6 assembly: the integral is
eventually positive once `13.968 λ^{K-2} < 2.7895 (1 - 3ϖ)` and `2θ - 1 < E`.
CONDITIONAL: `theorem1_conditional` ON Lemma 7, Lemma 9, Lemma 1 with Vaughan's sup bound, and the
circle identity; `theorem2_conditional` ON the same with the GRH sup bound of Baker and Harman.
`inputs_consistent`: vacuity test, the analytic hypotheses have a model.
Also PROVED: `lemma9_of_lemma8`, `lemma9_units`, `lemma9_out_of_J`, `lemma9_out_of_lemma8`: the
field `lemma9_out` follows from Lemma 8, the `J(𝔐)` lower bound of Lemma 9 and `|T| < λL`.
Binary Goldbach is OPEN.
-/

namespace LeanLab.HeathBrownPuchta.Assembly

open Filter Real LeanLab.Linnik

/-- Lemma 9's minor arc constant, in units of `C₀ N / log² 2`. -/
noncomputable def C9 (C1 C2 C0 w : ℝ) : ℝ := (C1 - 2 + 2 * w) * C2 + Real.log 2 / C0

/-- Lemma 10 from Lemma 9: `(C₁ - 2 + 2ϖ) C₂ + log 2 / C₀ ≤ 13.968` for `C₁ = 7.8342`,
`C₂ ≤ 2.2141`, `C₀ ≥ 0.66`, `0 ≤ ϖ ≤ 10⁻⁵`. -/
theorem lemma10_of_lemma9 {C2 C0 w : ℝ} (hC2 : C2 ≤ 22141 / 10000) (hC0 : 66 / 100 ≤ C0)
    (hw0 : 0 ≤ w) (hw : w ≤ 1 / 100000) : C9 (78342 / 10000) C2 C0 w ≤ 13968 / 1000 := by
  unfold C9
  have l2 := Real.log_two_lt_d9
  have l2' := Real.log_two_gt_d9
  norm_num at l2 l2'
  have hC0p : 0 < C0 := by linarith
  have h1 : Real.log 2 / C0 ≤ Real.log 2 / (66 / 100) :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) hC0
  have h2 : Real.log 2 / (66 / 100) ≤ 108304247 / 156250000 / (66 / 100) :=
    div_le_div_of_nonneg_right l2.le (by norm_num)
  have h3 : (78342 / 10000 - 2 + 2 * w) * C2 ≤ (78342 / 10000 - 2 + 2 * w) * (22141 / 10000) :=
    mul_le_mul_of_nonneg_left hC2 (by linarith)
  nlinarith

/-- Section 6, unconditional exponent: `2 θ - 1 = 109/154` at `θ = 263/308`, Lemma 1's target. -/
theorem uncond_exponent : 2 * (263 / 308 : ℝ) - 1 = 109 / 154 := by norm_num

/-- Section 6, GRH exponent: `2 θ - 1 = 1/2` at `θ = 3/4`. -/
theorem grh_exponent : 2 * (3 / 4 : ℝ) - 1 = 1 / 2 := by norm_num

/-- `C N^b ≤ ε c N` eventually, for `b < 1`, `ε c > 0`. -/
theorem small_of_rpow {b C a : ℝ} (hb : b < 1) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ b ≤ a * N := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 - b))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have hpos : 0 < a / (|C| + 1) := by positivity
  filter_upwards [ht.eventually (gt_mem_nhds hpos), eventually_gt_atTop 0] with N hN hN0
  have hN0' : (0 : ℝ) < N := by exact_mod_cast hN0
  have e : (N : ℝ) ^ b = (N : ℝ) ^ (-(1 - b)) * N := by
    rw [← Real.rpow_add_one hN0'.ne']; ring_nf
  rw [e]
  have hr0 : 0 ≤ (N : ℝ) ^ (-(1 - b)) := Real.rpow_nonneg hN0'.le _
  have h1 : C * ((N : ℝ) ^ (-(1 - b)) * N) ≤ |C| * ((N : ℝ) ^ (-(1 - b)) * N) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have h2 : |C| * (N : ℝ) ^ (-(1 - b)) ≤ a := by
    rw [lt_div_iff₀ (by positivity)] at hN
    nlinarith [abs_nonneg C]
  nlinarith

/-- The scale `X(N) = C₀ N L^{K-2} / log² 2` is at least `(C₀ / log² 2) N` once `L ≥ 1`. -/
theorem scale_of_L {C0 : ℝ} (hC0 : 0 < C0) (K : ℕ) (L : ℕ → ℕ) (hL : ∀ᶠ N in atTop, 1 ≤ L N) :
    ∃ c > 0, ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ≤ C0 * N * (L N : ℝ) ^ (K - 2) / Real.log 2 ^ 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C0 / Real.log 2 ^ 2, by positivity, ?_⟩
  filter_upwards [hL] with N hN
  have h1 : (1 : ℝ) ≤ (L N : ℝ) ^ (K - 2) := one_le_pow₀ (by exact_mod_cast hN)
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
  have : (0 : ℝ) ≤ C0 * N := by positivity
  nlinarith

/-- The analytic inputs of Sections 4 to 6 for fixed `K`, `λ`, `θ`, `E`, `ϖ`. -/
structure AnalyticInputs (K : ℕ) (lam θ E w : ℝ) where
  /-- `R(N) = ∫₀¹ S(α)² T(α)^K e(-αN) dα`, real part. -/
  R : ℕ → ℝ
  /-- The three pieces: major arcs, minor arcs off `𝒜_λ`, minor arcs in `𝒜_λ`. -/
  maj : ℕ → ℝ
  mout : ℕ → ℝ
  minr : ℕ → ℝ
  /-- The scale `C₀ N L^{K-2} / log² 2`. -/
  X : ℕ → ℝ
  C2 : ℝ
  C0 : ℝ
  split : ∀ N, R N = maj N + mout N + minr N
  scale : ∃ c > 0, ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ≤ X N
  bound_C2 : C2 ≤ 22141 / 10000
  bound_C0 : 66 / 100 ≤ C0
  /-- Lemma 7. -/
  lemma7 : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, (27895 / 10000 * (1 - 3 * w) - ε) * X N ≤ maj N
  /-- Lemma 9 with `|T| < λL` off `𝒜_λ`, Chen's `C₁ = 7.8342`. -/
  lemma9_out : ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
    |mout N| ≤ (C9 (78342 / 10000) C2 C0 w * lam ^ (K - 2) + ε) * X N
  /-- Lemma 1, `meas 𝒜_λ ≪ N^{-E}`, with the sup bound `S ≪ N^{θ + o(1)}` and `|T| ≤ L`. -/
  lemma1_in : ∀ δ > 0, ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, |minr N| ≤ C * (N : ℝ) ^ (2 * θ - E + δ)

/-- Section 6: the integral is eventually positive. -/
theorem section6_positive {K : ℕ} {lam θ E w : ℝ} (I : AnalyticInputs K lam θ E w)
    (hw0 : 0 ≤ w) (hw : w ≤ 1 / 100000) (hlam : 0 ≤ lam) (hE : 2 * θ - 1 < E)
    (hcrit : 13968 / 1000 * lam ^ (K - 2) < 27895 / 10000 * (1 - 3 * w)) :
    ∀ᶠ N : ℕ in atTop, 0 < I.R N := by
  obtain ⟨c, hc, hX⟩ := I.scale
  set g := 27895 / 10000 * (1 - 3 * w) - 13968 / 1000 * lam ^ (K - 2) with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  have hC9 := lemma10_of_lemma9 I.bound_C2 I.bound_C0 hw0 hw
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
  have hcN : 0 ≤ c * (N : ℝ) := by positivity
  have e1 : C9 (78342 / 10000) I.C2 I.C0 w * lam ^ (K - 2) ≤ 13968 / 1000 * lam ^ (K - 2) :=
    mul_le_mul_of_nonneg_right hC9 hlk
  have h9' : -(I.mout N) ≤ (13968 / 1000 * lam ^ (K - 2) + g / 4) * I.X N := by
    have := neg_le_abs (I.mout N)
    have : (C9 (78342 / 10000) I.C2 I.C0 w * lam ^ (K - 2) + g / 4) * I.X N ≤
        (13968 / 1000 * lam ^ (K - 2) + g / 4) * I.X N :=
      mul_le_mul_of_nonneg_right (by linarith) hX0
    linarith
  have h1' : -(I.minr N) ≤ g / 4 * I.X N := by
    have := neg_le_abs (I.minr N)
    have : g / 4 * (c * N) ≤ g / 4 * I.X N := mul_le_mul_of_nonneg_left hx (by positivity)
    nlinarith
  rw [I.split N]
  have key : 0 < g / 4 * I.X N := by positivity
  have : (27895 / 10000 * (1 - 3 * w) - g / 4) * I.X N =
      (13968 / 1000 * lam ^ (K - 2) + g / 4) * I.X N + g / 4 * I.X N + g / 4 * I.X N := by
    rw [hg]; ring
  linarith

/-- Section 6 with the circle method identity: every large `N` is represented. -/
theorem allLarge_of_inputs {K : ℕ} {lam θ E w : ℝ} (I : AnalyticInputs K lam θ E w)
    (circle : ∀ N, 0 < I.R N → LinnikExact K N)
    (hw0 : 0 ≤ w) (hw : w ≤ 1 / 100000) (hlam : 0 ≤ lam) (hE : 2 * θ - 1 < E)
    (hcrit : 13968 / 1000 * lam ^ (K - 2) < 27895 / 10000 * (1 - 3 * w)) :
    AllLargeEven (LinnikExact K) := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (section6_positive I hw0 hw hlam hE hcrit)
  exact ⟨N0, fun N _ hN => circle N (hN0 N hN.le)⟩

/-- Section 6 numerics with the `ϖ` loss: `13.968 · 0.863665^{11} < 2.7895 (1 - 3 · 10⁻⁵)`. -/
theorem crit13 : 13968 / 1000 * (863665 / 1000000 : ℝ) ^ (13 - 2) <
    27895 / 10000 * (1 - 3 * (1 / 100000)) := by norm_num

/-- The same on GRH: `13.968 · 0.722428^5 < 2.7895 (1 - 3 · 10⁻⁵)`. -/
theorem crit7 : 13968 / 1000 * (722428 / 1000000 : ℝ) ^ (7 - 2) <
    27895 / 10000 * (1 - 3 * (1 / 100000)) := by norm_num

/-- Theorem 1, CONDITIONAL ON Lemma 7, Lemma 9 with Chen's `C₁`, Lemma 1 `E(0.863665) > 109/154`
with Vaughan's `θ = 263/308 + 3ϖ`, for every small `ϖ > 0`, and the circle method identity. -/
theorem theorem1_conditional (E : ℝ) (hE : 109 / 154 < E)
    (I : ∀ w : ℝ, 0 < w → AnalyticInputs 13 (863665 / 1000000) (263 / 308 + 3 * w) E w)
    (circle : ∀ w (hw : 0 < w) N, 0 < (I w hw).R N → LinnikExact 13 N) :
    AllLargeEven (LinnikExact 13) := by
  set w := min (1 / 100000 : ℝ) ((E - 109 / 154) / 12) with hwdef
  have hw0 : 0 < w := lt_min (by norm_num) (by linarith)
  have hw1 : w ≤ 1 / 100000 := min_le_left _ _
  have hw2 : w ≤ (E - 109 / 154) / 12 := min_le_right _ _
  refine allLarge_of_inputs (I w hw0) (circle w hw0) hw0.le hw1 (by norm_num) ?_ ?_
  · linarith
  · have := crit13; linarith

/-- Theorem 2, CONDITIONAL ON the same inputs at `λ = 0.722428`, `E > 1/2`, with the GRH sup bound
`θ = 3/4` of Baker and Harman in place of Vaughan's, and the circle method identity. -/
theorem theorem2_conditional (E : ℝ) (hE : 1 / 2 < E)
    (I : ∀ w : ℝ, 0 < w → AnalyticInputs 7 (722428 / 1000000) (3 / 4) E w)
    (circle : ∀ w (hw : 0 < w) N, 0 < (I w hw).R N → LinnikExact 7 N) :
    AllLargeEven (LinnikExact 7) := by
  have hw0 : (0 : ℝ) < 1 / 100000 := by norm_num
  refine allLarge_of_inputs (I _ hw0) (circle _ hw0) hw0.le le_rfl (by norm_num) ?_ crit7
  linarith

/-- Lemma 9 from Lemma 8 and the major arc lower bound: `J(𝔪) = J - J(𝔐)`, so
`J(𝔪) ≤ {C₀ C₁ C₂ / log² 2 + 1/log 2 - 2(1 - ϖ) C₀ C₂ / log² 2 + o(1)} N`, which is Lemma 9's
`{C₀ (C₁ - 2 + 2ϖ) C₂ / log² 2 + 1 / log 2 + o(1)} N`. -/
theorem lemma9_of_lemma8 {C0 C1 C2 w : ℝ} {J JM Jm : ℕ → ℝ} (hsplit : ∀ N, J N = JM N + Jm N)
    (h8 : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, J N ≤ (C0 * C1 * C2 / Real.log 2 ^ 2 + 1 / Real.log 2 + ε) * N)
    (hM : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, (2 * (1 - w) * C0 * C2 / Real.log 2 ^ 2 - ε) * N ≤ JM N) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      Jm N ≤ (C0 * (C1 - 2 + 2 * w) * C2 / Real.log 2 ^ 2 + 1 / Real.log 2 + ε) * N := by
  intro ε hε
  filter_upwards [h8 (ε / 2) (by positivity), hM (ε / 2) (by positivity)] with N h1 h2
  have e := hsplit N
  have : (C0 * (C1 - 2 + 2 * w) * C2 / Real.log 2 ^ 2 + 1 / Real.log 2 + ε) * N =
      (C0 * C1 * C2 / Real.log 2 ^ 2 + 1 / Real.log 2 + ε / 2) * N -
        (2 * (1 - w) * C0 * C2 / Real.log 2 ^ 2 - ε / 2) * N := by ring
  linarith

/-- In units of `X = C₀ N L^{K-2} / log² 2`, Lemma 9's bound times `(λL)^{K-2}` is the field
`lemma9_out`: `C₀ (C₁ - 2 + 2ϖ) C₂ / log² 2 + 1 / log 2 = (C₀ / log² 2) C9`. -/
theorem lemma9_units {C0 C1 C2 w : ℝ} (hC0 : C0 ≠ 0) :
    C0 * (C1 - 2 + 2 * w) * C2 / Real.log 2 ^ 2 + 1 / Real.log 2 =
      C0 / Real.log 2 ^ 2 * C9 C1 C2 C0 w := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold C9; field_simp

/-- The off-`𝒜_λ` step: `|∫_{𝔪 \ 𝒜_λ}| ≤ (λL)^{K-2} J(𝔪)` and Lemma 9 give the field
`lemma9_out` in units of `X(N) = C₀ N L^{K-2} / log² 2`, for `C₀ > 0`, `λ ≥ 0`. -/
theorem lemma9_out_of_J {K : ℕ} {lam C0 C1 C2 w : ℝ} (hC0 : 0 < C0) (hlam : 0 ≤ lam)
    {mout Jm : ℕ → ℝ} {L : ℕ → ℕ}
    (hT : ∀ᶠ N : ℕ in atTop, |mout N| ≤ (lam * L N) ^ (K - 2) * Jm N)
    (h9 : ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      Jm N ≤ (C0 * (C1 - 2 + 2 * w) * C2 / Real.log 2 ^ 2 + 1 / Real.log 2 + ε) * N) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, |mout N| ≤
      (C9 C1 C2 C0 w * lam ^ (K - 2) + ε) * (C0 * N * (L N : ℝ) ^ (K - 2) / Real.log 2 ^ 2) := by
  intro ε hε
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk : 0 < C0 / Real.log 2 ^ 2 := by positivity
  have hε' : 0 < ε * (C0 / Real.log 2 ^ 2) / (lam ^ (K - 2) + 1) := by positivity
  filter_upwards [hT, h9 _ hε'] with N h1 h2
  rw [lemma9_units hC0.ne'] at h2
  have hp : 0 ≤ (lam * L N) ^ (K - 2) := by positivity
  have h3 := mul_le_mul_of_nonneg_left h2 hp
  have hN : (0 : ℝ) ≤ N := N.cast_nonneg
  have hLp : 0 ≤ (L N : ℝ) ^ (K - 2) := by positivity
  have hlp : 0 ≤ lam ^ (K - 2) := by positivity
  have hq : ε * (C0 / Real.log 2 ^ 2) / (lam ^ (K - 2) + 1) * lam ^ (K - 2) ≤
      ε * (C0 / Real.log 2 ^ 2) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_pos hε hk]
  have hmp : 0 ≤ (L N : ℝ) ^ (K - 2) * N := by positivity
  have hfin : (lam * L N) ^ (K - 2) *
      ((C0 / Real.log 2 ^ 2 * C9 C1 C2 C0 w + ε * (C0 / Real.log 2 ^ 2) / (lam ^ (K - 2) + 1)) * N)
      ≤ (C9 C1 C2 C0 w * lam ^ (K - 2) + ε) * (C0 * N * (L N : ℝ) ^ (K - 2) / Real.log 2 ^ 2) := by
    rw [mul_pow]
    have : (lam ^ (K - 2) * (L N : ℝ) ^ (K - 2)) *
        ((C0 / Real.log 2 ^ 2 * C9 C1 C2 C0 w + ε * (C0 / Real.log 2 ^ 2) / (lam ^ (K - 2) + 1)) * N)
        = (C0 / Real.log 2 ^ 2 * C9 C1 C2 C0 w * lam ^ (K - 2) +
            ε * (C0 / Real.log 2 ^ 2) / (lam ^ (K - 2) + 1) * lam ^ (K - 2)) *
          ((L N : ℝ) ^ (K - 2) * N) := by ring
    rw [this]
    have : (C9 C1 C2 C0 w * lam ^ (K - 2) + ε) * (C0 * N * (L N : ℝ) ^ (K - 2) / Real.log 2 ^ 2) =
        (C0 / Real.log 2 ^ 2 * C9 C1 C2 C0 w * lam ^ (K - 2) + ε * (C0 / Real.log 2 ^ 2)) *
          ((L N : ℝ) ^ (K - 2) * N) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) hmp
  linarith

/-- Lemma 8 plus the Lemma 9 major arc bound plus `|T| < λL` off `𝒜_λ` give the field
`lemma9_out`: the minor arc input of `AnalyticInputs` reduces to Lemma 8 and `J(𝔐)`. -/
theorem lemma9_out_of_lemma8 {K : ℕ} {lam C0 C1 C2 w : ℝ} (hC0 : 0 < C0) (hlam : 0 ≤ lam)
    {mout J JM Jm : ℕ → ℝ} {L : ℕ → ℕ} (hsplit : ∀ N, J N = JM N + Jm N)
    (h8 : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, J N ≤ (C0 * C1 * C2 / Real.log 2 ^ 2 + 1 / Real.log 2 + ε) * N)
    (hM : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, (2 * (1 - w) * C0 * C2 / Real.log 2 ^ 2 - ε) * N ≤ JM N)
    (hT : ∀ᶠ N : ℕ in atTop, |mout N| ≤ (lam * L N) ^ (K - 2) * Jm N) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, |mout N| ≤
      (C9 C1 C2 C0 w * lam ^ (K - 2) + ε) * (C0 * N * (L N : ℝ) ^ (K - 2) / Real.log 2 ^ 2) :=
  lemma9_out_of_J hC0 hlam hT (lemma9_of_lemma8 hsplit h8 hM)

/-- Vacuity test: the analytic hypotheses have a model, `X = N`, `maj = 3N`, the minor pieces `0`. -/
def inputs_consistent : AnalyticInputs 13 (863665 / 1000000) (263 / 308) 1 0 where
  R N := 3 * N
  maj N := 3 * N
  mout _ := 0
  minr _ := 0
  X N := N
  C2 := 2
  C0 := 1
  split N := by ring
  scale := ⟨1, one_pos, Eventually.of_forall fun N => by simp⟩
  bound_C2 := by norm_num
  bound_C0 := by norm_num
  lemma7 ε hε := Eventually.of_forall fun N => by
    have : (0 : ℝ) ≤ N := N.cast_nonneg
    nlinarith
  lemma9_out ε hε := Eventually.of_forall fun N => by
    simp only [abs_zero]
    have : (0 : ℝ) ≤ C9 (78342 / 10000) 2 1 0 * (863665 / 1000000) ^ (13 - 2) := by
      unfold C9; have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity
    positivity
  lemma1_in δ hδ := ⟨0, Eventually.of_forall fun N => by simp⟩

/-- The model meets every side condition, so `section6_positive` is not vacuous. -/
theorem consistent_positive : ∀ᶠ N : ℕ in atTop, 0 < inputs_consistent.R N :=
  section6_positive inputs_consistent le_rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end LeanLab.HeathBrownPuchta.Assembly
