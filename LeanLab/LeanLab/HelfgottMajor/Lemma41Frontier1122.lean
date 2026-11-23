import LeanLab.HelfgottMajor.Lemma41Leaf123
import LeanLab.HelfgottMajor.MainLemma41Split123
import LeanLab.HelfgottMajor.Prep1121ContourShift
import LeanLab.HelfgottMajor.Prep1121DCtDecay
import LeanLab.HelfgottMajor.Prep1121VIBudget
import LeanLab.HelfgottMajor.Prep1121DLineCont
import LeanLab.HelfgottMajor.Prep1121DIntegrable
import LeanLab.HelfgottMajor.Prep1121DTail
import LeanLab.HelfgottMajor.Prep1121DLogWeight

/-!
ROUTE BURST S58, burst-20261122, tag lemma41-frontier, 2026-11-22.
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, Lemma 4.1, page 31,
displays 4.1 to 4.3, proved on pages 31 to 35, for the Gaussian η♥ of page 44, in the lab's
CORRECTED form, the sealed leaf `Lemma41Leaf123.lemma_4_1_gaussian_corrected`.

FRONTIER WIRING. `MainLemma41Split123` split the sealed leaf into `contour_shift`,
`residue_at_zero`, `vertical_integral_bound` and `laurent_c0_bound`; the first and third are
bare sorries there, and their split proofs `Prep1121ContourShift.contour_shift_of_leaves` and
`Prep1121VIBudget.vertical_integral_bound_of_leaves` sit downstream, so they cannot be wired in
place without an import cycle. `contour_shift_of_leaves` in turn still uses four sorried leaves
of `Prep1121ContourShift` whose proofs exist only as `_of_pieces` twins in the downstream file
`Prep1121DCtDecay`.

This file is downstream of all of them. `contour_shift_wired` repeats the proof of
`contour_shift_of_leaves` with the four PROVED twins `line_two_integrable_of_pieces`,
`contMellin_decay_strip_of_pieces`, `horizontal_tendsto_of_pieces` and
`zero_sum_summable_of_pieces` in place of the leaves, so the contour shift of pages 32 and 33,
displays 4.4 and 4.7, is sorry free in its closure. `lemma_4_1_gaussian_corrected_frontier`
repeats the proof of `lemma_4_1_gaussian_corrected_of_leaves` with `contour_shift_wired` and
`vertical_integral_bound_wired`, and has the exact sealed statement.

`vertical_integral_bound_wired` repeats `Prep1121VIBudget.vertical_integral_bound_of_leaves`,
`log_energy`, `Prep1121VIIntegral.certified_integral` and `half_le` with the PROVED twins
`Prep1121DLineCont.logDeriv_line_continuous`, `Prep1121DIntegrable.memLp_split`,
`expand_square`, `half_line_split`, `Prep1121DTail.tail_le` and
`Prep1121DLogWeight.integral_log_weight`, and with the seven pieces of `Prep1121VIPiecesLow`,
page 35, the integral after display 4.12 on [0, 1.2], PROVED here by left endpoint sums for the
antitone integrand, with the helpers of the pending branch claude/HelfgottMajor-vi_pieces_07_10.
The only sorries left in the closure are `Prep1121VIPiecesHigh.piece_07` to `piece_10`, PROVED
on that pending branch, and `Prep1122BinetSplit.digamma_log_laplace` and `sine_planck`, PROVED
on the pending branch claude/HelfgottMajor-binet_formula-leaves. No new LEAF and no new
definition here.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Lemma41Frontier1122
open Real MeasureTheory Set Filter LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123
open LeanLab.HelfgottMajor.MainLemma41Split123
open scoped Topology

/-- PROVED, sorry free in its closure. P0014 proof of Lemma 4.1, pages 32 and 33, displays 4.4
and 4.7: the exact statement of `MainLemma41Split123.contour_shift`, by the proof of
`Prep1121ContourShift.contour_shift_of_leaves` with its four leaves replaced by the PROVED
`_of_pieces` twins of `Prep1121DCtDecay`. -/
theorem contour_shift_wired (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      DifferentiableOn ℂ (contourIntegrand χ δ x) (Metric.closedBall 0 r \ {0}) ∧
      Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
          lowZeros χ δ x T + highZeros χ δ x T +
          (2 * π * Complex.I)⁻¹ * circleIntegral (contourIntegrand χ δ x) 0 r =
        -((2 * π : ℂ)⁻¹ *
          ∫ τ : ℝ, contourIntegrand χ δ x (-1 / 2 + τ * Complex.I)) := by
  rcases eq_or_ne q 1 with hq | hq
  · subst hq
    obtain ⟨r, hr, hF, h⟩ := PrincipalRoute669.contour_shift_conductor_one x hx χ δ T
    exact ⟨r, hr, hF, by rw [if_pos rfl]; exact h⟩
  obtain ⟨r, hr, hr2, hF⟩ := Prep1121ContourShift.small_disc χ hχ hq δ hx
  refine ⟨r, hr, hF, ?_⟩
  rw [if_neg hq]
  obtain ⟨C, hC, hgood⟩ := Linnik.ExplicitFormula.good_heights hχ
  choose! Tf hTfI hTf using hgood
  have hT5 : ∀ n : ℕ, (5 : ℝ) ≤ max (n : ℝ) 5 := fun n => le_max_right _ _
  have hYI : ∀ n : ℕ, Tf (max (n : ℝ) 5) ∈ Icc (max (n : ℝ) 5) (max (n : ℝ) 5 + 1) :=
    fun n => hTfI _ (hT5 n)
  have hYge : ∀ n : ℕ, (n : ℝ) ≤ Tf (max (n : ℝ) 5) :=
    fun n => (le_max_left _ _).trans (hYI n).1
  have hY1 : ∀ n : ℕ, 1 ≤ Tf (max (n : ℝ) 5) := fun n => by linarith [(hYI n).1, hT5 n]
  have hYtop : Tendsto (fun n : ℕ => Tf (max (n : ℝ) 5)) atTop atTop :=
    tendsto_atTop_mono hYge tendsto_natCast_atTop_atTop
  have hrect := fun n : ℕ => Prep1121ContourShift.rect_identity χ hχ hq δ hx (hY1 n) hr hr2 hF
    (fun σ hσ τ hτ => (hTf _ (hT5 n) σ hσ τ hτ).1)
  have hA := intervalIntegral_tendsto_integral (Prep1121DCtDecay.line_two_integrable_of_pieces χ δ hx)
    (tendsto_neg_atTop_atBot.comp hYtop) hYtop
  have hB := intervalIntegral_tendsto_integral (Prep1121ContourShift.line_minus_half_integrable χ δ hx)
    (tendsto_neg_atTop_atBot.comp hYtop) hYtop
  obtain ⟨hH1, hH2⟩ := Prep1121DCtDecay.horizontal_tendsto_of_pieces χ δ hx
    (Prep1121DCtDecay.contMellin_decay_strip_of_pieces δ) hC
    (fun n : ℕ => Tf (max (n : ℝ) 5)) hYI (fun n σ hσ τ hτ => (hTf _ (hT5 n) σ hσ τ hτ).2)
  have hs := Prep1121DCtDecay.zero_sum_summable_of_pieces χ hχ δ hx
  have hL := Prep1121ContourShift.low_zeros_tendsto χ δ x hs _ hYtop
  have hlhs := ((hA.const_mul (2 * π : ℂ)⁻¹).sub (hB.const_mul (2 * π : ℂ)⁻¹)).add
    ((hH2.sub hH1).const_mul (2 * π * Complex.I)⁻¹)
  have hrhs : Tendsto (fun n : ℕ => (2 * π * Complex.I)⁻¹ *
      circleIntegral (contourIntegrand χ δ x) 0 r + lowZeros χ δ x (Tf (max (n : ℝ) 5)))
      atTop (𝓝 ((2 * π * Complex.I)⁻¹ * circleIntegral (contourIntegrand χ δ x) 0 r +
        ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
          zeroTerm χ δ x ρ.val)) :=
    tendsto_const_nhds.add hL
  have heq := tendsto_nhds_unique (hlhs.congr (fun n => hrect n)) hrhs
  have hline := Prep1121ContourShift.line_two_eq χ δ hx
  have hsplit := Prep1121ContourShift.zero_sum_split χ δ x T hs
  linear_combination hline - heq + hsplit

/-- PROVED, by rfl. Match check: `contour_shift_wired` has exactly the type of the route step
`MainLemma41Split123.contour_shift`. -/
example : type_of% @contour_shift_wired = type_of% @MainLemma41Split123.contour_shift := rfl

section PiecesLow

/-- Helper for pieces 00 to 06, copied from the pending branch claude/HelfgottMajor-vi_pieces_07_10, Prep1121VIPiecesHigh, P0014 page 35, g as in the module doc. Continuity of g, so that every interval integral below exists. -/
private theorem g_cont : Continuous (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) := by
  refine Continuous.div ?_ (by fun_prop) (fun τ => by positivity)
  exact (Continuous.log (by fun_prop) (fun τ => by positivity)).pow 2

/-- Helper for pieces 00 to 06, copied from the pending branch claude/HelfgottMajor-vi_pieces_07_10, Prep1121VIPiecesHigh, P0014 page 35, g as in the module doc. The derivative of g by the quotient and chain rules. -/
private theorem g_hasDeriv (τ : ℝ) : HasDerivAt (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2))
    ((2 * Real.log (τ ^ 2 + 9 / 4) * (2 * τ / (τ ^ 2 + 9 / 4)) * (1 / 4 + τ ^ 2) -
      Real.log (τ ^ 2 + 9 / 4) ^ 2 * (2 * τ)) / (1 / 4 + τ ^ 2) ^ 2) τ := by
  have hv : HasDerivAt (fun τ : ℝ => τ ^ 2 + 9 / 4) (2 * τ) τ := by
    simpa using (hasDerivAt_pow 2 τ).add_const (9 / 4 : ℝ)
  have hL := hv.log (by positivity)
  have hD : HasDerivAt (fun τ : ℝ => 1 / 4 + τ ^ 2) (2 * τ) τ := by
    simpa using (hasDerivAt_pow 2 τ).const_add (1 / 4 : ℝ)
  have := (hL.pow 2).div hD (by positivity)
  convert this using 1
  simp

/-- Helper for pieces 00 to 06, copied from the pending branch claude/HelfgottMajor-vi_pieces_07_10, Prep1121VIPiecesHigh, P0014 page 35, g as in the module doc. g is antitone on [0, ∞): the derivative is 2τ L (2 - 4/v - L)/(1/4 + τ²)² with v = τ² + 9/4 and L = log v, and L ≥ log 4 + 1 - 4/v > 2 - 4/v. -/
private theorem g_antitone : AntitoneOn (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2))
    (Set.Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) g_cont.continuousOn
    (fun τ _ => (g_hasDeriv τ).differentiableAt.differentiableWithinAt) ?_
  intro τ hτ
  rw [interior_Ici] at hτ
  have hτ0 : 0 < τ := hτ
  rw [(g_hasDeriv τ).deriv]
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  set v := τ ^ 2 + 9 / 4 with hv
  have hv0 : 0 < v := by positivity
  have hD : 1 / 4 + τ ^ 2 = v - 2 := by rw [hv]; ring
  set L := Real.log v
  have h4 : 1 - (v / 4)⁻¹ ≤ Real.log (v / 4) := Real.one_sub_inv_le_log_of_pos (by positivity)
  rw [Real.log_div hv0.ne' (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow,
    inv_div] at h4
  have hl2 := Real.log_two_gt_d9
  have hL : 2 - 4 / v ≤ L := by push_cast at h4; linarith
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [hv]; nlinarith)
  rw [hD]
  have key : 2 * L * (2 * τ / v) * (v - 2) - L ^ 2 * (2 * τ) = 2 * τ * L * ((2 - 4 / v) - L) := by
    field_simp; ring
  rw [key]
  have : 0 ≤ 2 * τ * L := by positivity
  nlinarith

/-- Helper for pieces 00 to 06, copied from the pending branch claude/HelfgottMajor-vi_pieces_07_10, Prep1121VIPiecesHigh, P0014 page 35, g as in the module doc. Left endpoint bound on one step, from `g_antitone`: ∫_x^y g ≤ (y - x) g(x) for 0 ≤ x ≤ y. -/
private theorem step_le (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∫ τ in x..y, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤
      (y - x) * (Real.log (x ^ 2 + 9 / 4) ^ 2 / (1 / 4 + x ^ 2)) := by
  have h := intervalIntegral.integral_mono_on hxy (g_cont.intervalIntegrable x y)
    (intervalIntegrable_const (μ := MeasureTheory.volume)) (fun τ hτ => g_antitone (Set.mem_Ici.2 hx)
      (Set.mem_Ici.2 (hx.trans hτ.1)) hτ.1)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h
  exact h

/-- Helper for pieces 00 to 06, copied from the pending branch claude/HelfgottMajor-vi_pieces_07_10, Prep1121VIPiecesHigh, P0014 page 35, g as in the module doc. Rational upper bound for log v: m log v = k log 2 + log(v^m/2^k) ≤ k log 2 + v^m/2^k - 1, with log 2 < 0.6931471808. -/
private theorem log_ub (v : ℝ) (m k : ℕ) (hm : 0 < m) (hv : 0 < v) :
    Real.log v ≤ (k * 0.6931471808 + (v ^ m / 2 ^ k - 1)) / m := by
  have hy : 0 < v ^ m / 2 ^ k := by positivity
  have h := Real.log_le_sub_one_of_pos hy
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h
  have hl2 := Real.log_two_lt_d9
  have hk : (k : ℝ) * Real.log 2 ≤ k * 0.6931471808 :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg k)
  rw [le_div_iff₀ (by exact_mod_cast hm)]
  linarith

/-- Helper for pieces 00 to 06, copied from the pending branch claude/HelfgottMajor-vi_pieces_07_10, Prep1121VIPiecesHigh, P0014 page 35, g as in the module doc. Replacing log(x² + 9/4) by an upper bound U in g(x). -/
private theorem g_le (x U : ℝ) (_hx : 0 ≤ x) (h : Real.log (x ^ 2 + 9 / 4) ≤ U) :
    Real.log (x ^ 2 + 9 / 4) ^ 2 / (1 / 4 + x ^ 2) ≤ U ^ 2 / (1 / 4 + x ^ 2) := by
  have h0 : 0 ≤ Real.log (x ^ 2 + 9 / 4) := Real.log_nonneg (by nlinarith)
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ h0 h 2) (by positivity)

/-- PROVED. Exact statement of `Prep1121VIPiecesLow.piece_00`, P0014 page 35, the integral
after display 4.12, subinterval [0, 0.14]: ∫ g ≤ 0.368, by left endpoint sums with `g_antitone` and
the log bounds of `log_ub`. -/
theorem piece_00_wired :
    ∫ τ in (0 : ℝ)..0.14, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.368 := by
  have s0 : ∫ τ in (0 : ℝ)..0.07, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.184138 := by
    calc ∫ τ in (0 : ℝ)..0.07, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.07 - 0) * (Real.log ((0 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0 : ℝ) ^ 2)) :=
          step_le 0 0.07 (by norm_num) (by norm_num)
      _ ≤ (0.07 - 0) * (0.810946 ^ 2 / (1 / 4 + (0 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0 0.810946 (by norm_num)
            ((log_ub _ 6 7 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.184138 := by norm_num
  have s1 : ∫ τ in (0.07 : ℝ)..0.14, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.181588 := by
    calc ∫ τ in (0.07 : ℝ)..0.14, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.14 - 0.07) * (Real.log ((0.07 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.07 : ℝ) ^ 2)) :=
          step_le 0.07 0.14 (by norm_num) (by norm_num)
      _ ≤ (0.14 - 0.07) * (0.813166 ^ 2 / (1 / 4 + (0.07 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.07 0.813166 (by norm_num)
            ((log_ub _ 6 7 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.181588 := by norm_num
  have e1 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ) 0.07) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.07 : ℝ) 0.14)
  linarith [s0, s1, e1]

/-- PROVED. Exact statement of `Prep1121VIPiecesLow.piece_01`, P0014 page 35, the integral
after display 4.12, subinterval [0.14, 0.28]: ∫ g ≤ 0.333, by left endpoint sums with `g_antitone` and
the log bounds of `log_ub`. -/
theorem piece_01_wired :
    ∫ τ in (0.14 : ℝ)..0.28, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.333 := by
  have s0 : ∫ τ in (0.14 : ℝ)..0.168, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.069767 := by
    calc ∫ τ in (0.14 : ℝ)..0.168, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.168 - 0.14) * (Real.log ((0.14 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.14 : ℝ) ^ 2)) :=
          step_le 0.14 0.168 (by norm_num) (by norm_num)
      _ ≤ (0.168 - 0.14) * (0.819605 ^ 2 / (1 / 4 + (0.14 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.14 0.819605 (by norm_num)
            ((log_ub _ 11 13 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.069767 := by norm_num
  have s1 : ∫ τ in (0.168 : ℝ)..0.196, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.068248 := by
    calc ∫ τ in (0.168 : ℝ)..0.196, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.196 - 0.168) * (Real.log ((0.168 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.168 : ℝ) ^ 2)) :=
          step_le 0.168 0.196 (by norm_num) (by norm_num)
      _ ≤ (0.196 - 0.168) * (0.823496 ^ 2 / (1 / 4 + (0.168 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.168 0.823496 (by norm_num)
            ((log_ub _ 11 13 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.068248 := by norm_num
  have s2 : ∫ τ in (0.196 : ℝ)..0.224, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.066542 := by
    calc ∫ τ in (0.196 : ℝ)..0.224, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.224 - 0.196) * (Real.log ((0.196 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.196 : ℝ) ^ 2)) :=
          step_le 0.196 0.224 (by norm_num) (by norm_num)
      _ ≤ (0.224 - 0.196) * (0.827898 ^ 2 / (1 / 4 + (0.196 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.196 0.827898 (by norm_num)
            ((log_ub _ 5 6 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.066542 := by norm_num
  have s3 : ∫ τ in (0.224 : ℝ)..0.252, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.064724 := by
    calc ∫ τ in (0.224 : ℝ)..0.252, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.252 - 0.224) * (Real.log ((0.224 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.224 : ℝ) ^ 2)) :=
          step_le 0.224 0.252 (by norm_num) (by norm_num)
      _ ≤ (0.252 - 0.224) * (0.83299 ^ 2 / (1 / 4 + (0.224 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.224 0.83299 (by norm_num)
            ((log_ub _ 5 6 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.064724 := by norm_num
  have s4 : ∫ τ in (0.252 : ℝ)..0.28, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.062853 := by
    calc ∫ τ in (0.252 : ℝ)..0.28, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.28 - 0.252) * (Real.log ((0.252 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.252 : ℝ) ^ 2)) :=
          step_le 0.252 0.28 (by norm_num) (by norm_num)
      _ ≤ (0.28 - 0.252) * (0.838887 ^ 2 / (1 / 4 + (0.252 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.252 0.838887 (by norm_num)
            ((log_ub _ 5 6 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.062853 := by norm_num
  have e1 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.14 : ℝ) 0.168) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.168 : ℝ) 0.196)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.14 : ℝ) 0.196) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.196 : ℝ) 0.224)
  have e3 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.14 : ℝ) 0.224) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.224 : ℝ) 0.252)
  have e4 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.14 : ℝ) 0.252) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.252 : ℝ) 0.28)
  linarith [s0, s1, s2, s3, s4, e1, e2, e3, e4]

/-- PROVED. Exact statement of `Prep1121VIPiecesLow.piece_02`, P0014 page 35, the integral
after display 4.12, subinterval [0.28, 0.29]: ∫ g ≤ 0.026, by left endpoint sums with `g_antitone` and
the log bounds of `log_ub`. -/
theorem piece_02_wired :
    ∫ τ in (0.28 : ℝ)..0.29, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.026 := by
  have s0 : ∫ τ in (0.28 : ℝ)..0.29, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.021753 := by
    calc ∫ τ in (0.28 : ℝ)..0.29, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.29 - 0.28) * (Real.log ((0.28 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.28 : ℝ) ^ 2)) :=
          step_le 0.28 0.29 (by norm_num) (by norm_num)
      _ ≤ (0.29 - 0.28) * (0.8452 ^ 2 / (1 / 4 + (0.28 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.28 0.8452 (by norm_num)
            ((log_ub _ 9 11 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.021753 := by norm_num
  linarith [s0]

/-- PROVED. Exact statement of `Prep1121VIPiecesLow.piece_03`, P0014 page 35, the integral
after display 4.12, subinterval [0.29, 0.45]: ∫ g ≤ 0.319, by left endpoint sums with `g_antitone` and
the log bounds of `log_ub`. -/
theorem piece_03_wired :
    ∫ τ in (0.29 : ℝ)..0.45, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.319 := by
  have s0 : ∫ τ in (0.29 : ℝ)..0.3167, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.057418 := by
    calc ∫ τ in (0.29 : ℝ)..0.3167, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.3167 - 0.29) * (Real.log ((0.29 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.29 : ℝ) ^ 2)) :=
          step_le 0.29 0.3167 (by norm_num) (by norm_num)
      _ ≤ (0.3167 - 0.29) * (0.847628 ^ 2 / (1 / 4 + (0.29 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.29 0.847628 (by norm_num)
            ((log_ub _ 9 11 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.057418 := by norm_num
  have s1 : ∫ τ in (0.3167 : ℝ)..0.3433, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.055484 := by
    calc ∫ τ in (0.3167 : ℝ)..0.3433, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.3433 - 0.3167) * (Real.log ((0.3167 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.3167 : ℝ) ^ 2)) :=
          step_le 0.3167 0.3433 (by norm_num) (by norm_num)
      _ ≤ (0.3433 - 0.3167) * (0.854792 ^ 2 / (1 / 4 + (0.3167 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.3167 0.854792 (by norm_num)
            ((log_ub _ 9 11 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.055484 := by norm_num
  have s2 : ∫ τ in (0.3433 : ℝ)..0.37, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.053936 := by
    calc ∫ τ in (0.3433 : ℝ)..0.37, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.37 - 0.3433) * (Real.log ((0.3433 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.3433 : ℝ) ^ 2)) :=
          step_le 0.3433 0.37 (by norm_num) (by norm_num)
      _ ≤ (0.37 - 0.3433) * (0.862024 ^ 2 / (1 / 4 + (0.3433 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.3433 0.862024 (by norm_num)
            ((log_ub _ 4 5 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.053936 := by norm_num
  have s3 : ∫ τ in (0.37 : ℝ)..0.3967, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.052237 := by
    calc ∫ τ in (0.37 : ℝ)..0.3967, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.3967 - 0.37) * (Real.log ((0.37 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.37 : ℝ) ^ 2)) :=
          step_le 0.37 0.3967 (by norm_num) (by norm_num)
      _ ≤ (0.3967 - 0.37) * (0.870021 ^ 2 / (1 / 4 + (0.37 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.37 0.870021 (by norm_num)
            ((log_ub _ 4 5 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.052237 := by norm_num
  have s4 : ∫ τ in (0.3967 : ℝ)..0.4233, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.050406 := by
    calc ∫ τ in (0.3967 : ℝ)..0.4233, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.4233 - 0.3967) * (Real.log ((0.3967 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.3967 : ℝ) ^ 2)) :=
          step_le 0.3967 0.4233 (by norm_num) (by norm_num)
      _ ≤ (0.4233 - 0.3967) * (0.878608 ^ 2 / (1 / 4 + (0.3967 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.3967 0.878608 (by norm_num)
            ((log_ub _ 11 14 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.050406 := by norm_num
  have s5 : ∫ τ in (0.4233 : ℝ)..0.45, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.049013 := by
    calc ∫ τ in (0.4233 : ℝ)..0.45, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.45 - 0.4233) * (Real.log ((0.4233 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.4233 : ℝ) ^ 2)) :=
          step_le 0.4233 0.45 (by norm_num) (by norm_num)
      _ ≤ (0.45 - 0.4233) * (0.887601 ^ 2 / (1 / 4 + (0.4233 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.4233 0.887601 (by norm_num)
            ((log_ub _ 7 9 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.049013 := by norm_num
  have e1 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.29 : ℝ) 0.3167) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.3167 : ℝ) 0.3433)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.29 : ℝ) 0.3433) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.3433 : ℝ) 0.37)
  have e3 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.29 : ℝ) 0.37) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.37 : ℝ) 0.3967)
  have e4 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.29 : ℝ) 0.3967) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.3967 : ℝ) 0.4233)
  have e5 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.29 : ℝ) 0.4233) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.4233 : ℝ) 0.45)
  linarith [s0, s1, s2, s3, s4, s5, e1, e2, e3, e4, e5]

/-- PROVED. Exact statement of `Prep1121VIPiecesLow.piece_04`, P0014 page 35, the integral
after display 4.12, subinterval [0.45, 0.65]: ∫ g ≤ 0.326, by left endpoint sums with `g_antitone` and
the log bounds of `log_ub`. -/
theorem piece_04_wired :
    ∫ τ in (0.45 : ℝ)..0.65, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.326 := by
  have s0 : ∫ τ in (0.45 : ℝ)..0.4833, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.059237 := by
    calc ∫ τ in (0.45 : ℝ)..0.4833, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.4833 - 0.45) * (Real.log ((0.45 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.45 : ℝ) ^ 2)) :=
          step_le 0.45 0.4833 (by norm_num) (by norm_num)
      _ ≤ (0.4833 - 0.45) * (0.897187 ^ 2 / (1 / 4 + (0.45 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.45 0.897187 (by norm_num)
            ((log_ub _ 10 13 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.059237 := by norm_num
  have s1 : ∫ τ in (0.4833 : ℝ)..0.5167, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.057198 := by
    calc ∫ τ in (0.4833 : ℝ)..0.5167, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.5167 - 0.4833) * (Real.log ((0.4833 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.4833 : ℝ) ^ 2)) :=
          step_le 0.4833 0.5167 (by norm_num) (by norm_num)
      _ ≤ (0.5167 - 0.4833) * (0.910012 ^ 2 / (1 / 4 + (0.4833 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.4833 0.910012 (by norm_num)
            ((log_ub _ 3 4 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.057198 := by norm_num
  have s2 : ∫ τ in (0.5167 : ℝ)..0.55, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.054883 := by
    calc ∫ τ in (0.5167 : ℝ)..0.55, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.55 - 0.5167) * (Real.log ((0.5167 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.5167 : ℝ) ^ 2)) :=
          step_le 0.5167 0.55 (by norm_num) (by norm_num)
      _ ≤ (0.55 - 0.5167) * (0.923062 ^ 2 / (1 / 4 + (0.5167 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.5167 0.923062 (by norm_num)
            ((log_ub _ 3 4 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.054883 := by norm_num
  have s3 : ∫ τ in (0.55 : ℝ)..0.5833, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.052954 := by
    calc ∫ τ in (0.55 : ℝ)..0.5833, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.5833 - 0.55) * (Real.log ((0.55 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.55 : ℝ) ^ 2)) :=
          step_le 0.55 0.5833 (by norm_num) (by norm_num)
      _ ≤ (0.5833 - 0.55) * (0.937326 ^ 2 / (1 / 4 + (0.55 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.55 0.937326 (by norm_num)
            ((log_ub _ 3 4 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.052954 := by norm_num
  have s4 : ∫ τ in (0.5833 : ℝ)..0.6167, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.05126 := by
    calc ∫ τ in (0.5833 : ℝ)..0.6167, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.6167 - 0.5833) * (Real.log ((0.5833 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.5833 : ℝ) ^ 2)) :=
          step_le 0.5833 0.6167 (by norm_num) (by norm_num)
      _ ≤ (0.6167 - 0.5833) * (0.951758 ^ 2 / (1 / 4 + (0.5833 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.5833 0.951758 (by norm_num)
            ((log_ub _ 8 11 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.05126 := by norm_num
  have s5 : ∫ τ in (0.6167 : ℝ)..0.65, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.049415 := by
    calc ∫ τ in (0.6167 : ℝ)..0.65, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.65 - 0.6167) * (Real.log ((0.6167 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.6167 : ℝ) ^ 2)) :=
          step_le 0.6167 0.65 (by norm_num) (by norm_num)
      _ ≤ (0.65 - 0.6167) * (0.967133 ^ 2 / (1 / 4 + (0.6167 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.6167 0.967133 (by norm_num)
            ((log_ub _ 5 7 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.049415 := by norm_num
  have e1 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.45 : ℝ) 0.4833) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.4833 : ℝ) 0.5167)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.45 : ℝ) 0.5167) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.5167 : ℝ) 0.55)
  have e3 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.45 : ℝ) 0.55) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.55 : ℝ) 0.5833)
  have e4 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.45 : ℝ) 0.5833) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.5833 : ℝ) 0.6167)
  have e5 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.45 : ℝ) 0.6167) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.6167 : ℝ) 0.65)
  linarith [s0, s1, s2, s3, s4, s5, e1, e2, e3, e4, e5]

/-- PROVED. Exact statement of `Prep1121VIPiecesLow.piece_05`, P0014 page 35, the integral
after display 4.12, subinterval [0.65, 0.9]: ∫ g ≤ 0.332, by left endpoint sums with `g_antitone` and
the log bounds of `log_ub`. -/
theorem piece_05_wired :
    ∫ τ in (0.65 : ℝ)..0.9, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.332 := by
  have s0 : ∫ τ in (0.65 : ℝ)..0.7, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.071847 := by
    calc ∫ τ in (0.65 : ℝ)..0.7, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.7 - 0.65) * (Real.log ((0.65 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.65 : ℝ) ^ 2)) :=
          step_le 0.65 0.7 (by norm_num) (by norm_num)
      _ ≤ (0.7 - 0.65) * (0.983022 ^ 2 / (1 / 4 + (0.65 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.65 0.983022 (by norm_num)
            ((log_ub _ 12 17 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.071847 := by norm_num
  have s1 : ∫ τ in (0.7 : ℝ)..0.75, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.068648 := by
    calc ∫ τ in (0.7 : ℝ)..0.75, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.75 - 0.7) * (Real.log ((0.7 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.7 : ℝ) ^ 2)) :=
          step_le 0.7 0.75 (by norm_num) (by norm_num)
      _ ≤ (0.75 - 0.7) * (1.007959 ^ 2 / (1 / 4 + (0.7 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.7 1.007959 (by norm_num)
            ((log_ub _ 11 16 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.068648 := by norm_num
  have s2 : ∫ τ in (0.75 : ℝ)..0.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.065808 := by
    calc ∫ τ in (0.75 : ℝ)..0.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.8 - 0.75) * (Real.log ((0.75 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.75 : ℝ) ^ 2)) :=
          step_le 0.75 0.8 (by norm_num) (by norm_num)
      _ ≤ (0.8 - 0.75) * (1.034106 ^ 2 / (1 / 4 + (0.75 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.75 1.034106 (by norm_num)
            ((log_ub _ 2 3 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.065808 := by norm_num
  have s3 : ∫ τ in (0.8 : ℝ)..0.85, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.06333 := by
    calc ∫ τ in (0.8 : ℝ)..0.85, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.85 - 0.8) * (Real.log ((0.8 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.8 : ℝ) ^ 2)) :=
          step_le 0.8 0.85 (by norm_num) (by norm_num)
      _ ≤ (0.85 - 0.8) * (1.061728 ^ 2 / (1 / 4 + (0.8 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.8 1.061728 (by norm_num)
            ((log_ub _ 2 3 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.06333 := by norm_num
  have s4 : ∫ τ in (0.85 : ℝ)..0.9, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.061019 := by
    calc ∫ τ in (0.85 : ℝ)..0.9, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.9 - 0.85) * (Real.log ((0.85 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.85 : ℝ) ^ 2)) :=
          step_le 0.85 0.9 (by norm_num) (by norm_num)
      _ ≤ (0.9 - 0.85) * (1.089404 ^ 2 / (1 / 4 + (0.85 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.85 1.089404 (by norm_num)
            ((log_ub _ 7 11 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.061019 := by norm_num
  have e1 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.65 : ℝ) 0.7) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.7 : ℝ) 0.75)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.65 : ℝ) 0.75) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.75 : ℝ) 0.8)
  have e3 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.65 : ℝ) 0.8) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.8 : ℝ) 0.85)
  have e4 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.65 : ℝ) 0.85) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.85 : ℝ) 0.9)
  linarith [s0, s1, s2, s3, s4, e1, e2, e3, e4]

/-- PROVED. Exact statement of `Prep1121VIPiecesLow.piece_06`, P0014 page 35, the integral
after display 4.12, subinterval [0.9, 1.2]: ∫ g ≤ 0.333, by left endpoint sums with `g_antitone` and
the log bounds of `log_ub`. -/
theorem piece_06_wired :
    ∫ τ in (0.9 : ℝ)..1.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.333 := by
  have s0 : ∫ τ in (0.9 : ℝ)..0.975, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.08854 := by
    calc ∫ τ in (0.9 : ℝ)..0.975, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (0.975 - 0.9) * (Real.log ((0.9 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.9 : ℝ) ^ 2)) :=
          step_le 0.9 0.975 (by norm_num) (by norm_num)
      _ ≤ (0.975 - 0.9) * (1.118639 ^ 2 / (1 / 4 + (0.9 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.9 1.118639 (by norm_num)
            ((log_ub _ 5 8 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.08854 := by norm_num
  have s1 : ∫ τ in (0.975 : ℝ)..1.05, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.084557 := by
    calc ∫ τ in (0.975 : ℝ)..1.05, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (1.05 - 0.975) * (Real.log ((0.975 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (0.975 : ℝ) ^ 2)) :=
          step_le 0.975 1.05 (by norm_num) (by norm_num)
      _ ≤ (1.05 - 0.975) * (1.163446 ^ 2 / (1 / 4 + (0.975 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 0.975 1.163446 (by norm_num)
            ((log_ub _ 3 5 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.084557 := by norm_num
  have s2 : ∫ τ in (1.05 : ℝ)..1.125, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.081153 := by
    calc ∫ τ in (1.05 : ℝ)..1.125, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (1.125 - 1.05) * (Real.log ((1.05 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (1.05 : ℝ) ^ 2)) :=
          step_le 1.05 1.125 (by norm_num) (by norm_num)
      _ ≤ (1.125 - 1.05) * (1.209729 ^ 2 / (1 / 4 + (1.05 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 1.05 1.209729 (by norm_num)
            ((log_ub _ 4 7 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.081153 := by norm_num
  have s3 : ∫ τ in (1.125 : ℝ)..1.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.078222 := by
    calc ∫ τ in (1.125 : ℝ)..1.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (1.2 - 1.125) * (Real.log ((1.125 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (1.125 : ℝ) ^ 2)) :=
          step_le 1.125 1.2 (by norm_num) (by norm_num)
      _ ≤ (1.2 - 1.125) * (1.257268 ^ 2 / (1 / 4 + (1.125 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 1.125 1.257268 (by norm_num)
            ((log_ub _ 11 20 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.078222 := by norm_num
  have e1 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.9 : ℝ) 0.975) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.975 : ℝ) 1.05)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.9 : ℝ) 1.05) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.05 : ℝ) 1.125)
  have e3 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (0.9 : ℝ) 1.125) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.125 : ℝ) 1.2)
  linarith [s0, s1, s2, s3, e1, e2, e3]


/-- PROVED. Exact statement of `Prep1121VIPiecesLow.sum_low`, P0014 page 35: the sum of the
subinterval bounds on [0, 1.2], 2.037, from the PROVED pieces above. -/
theorem sum_low_wired :
    (∫ τ in (0 : ℝ)..0.14, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.14 : ℝ)..0.28, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.28 : ℝ)..0.29, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.29 : ℝ)..0.45, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.45 : ℝ)..0.65, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.65 : ℝ)..0.9, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.9 : ℝ)..1.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) ≤ 2.037 := by
  linarith [piece_00_wired, piece_01_wired, piece_02_wired, piece_03_wired, piece_04_wired,
    piece_05_wired, piece_06_wired]

/-- PROVED, by rfl. Match checks against the leaves of `Prep1121VIPiecesLow`. -/
example : type_of% @piece_00_wired = type_of% @Prep1121VIPiecesLow.piece_00 := rfl
example : type_of% @piece_01_wired = type_of% @Prep1121VIPiecesLow.piece_01 := rfl
example : type_of% @piece_02_wired = type_of% @Prep1121VIPiecesLow.piece_02 := rfl
example : type_of% @piece_03_wired = type_of% @Prep1121VIPiecesLow.piece_03 := rfl
example : type_of% @piece_04_wired = type_of% @Prep1121VIPiecesLow.piece_04 := rfl
example : type_of% @piece_05_wired = type_of% @Prep1121VIPiecesLow.piece_05 := rfl
example : type_of% @piece_06_wired = type_of% @Prep1121VIPiecesLow.piece_06 := rfl
example : type_of% @sum_low_wired = type_of% @Prep1121VIPiecesLow.sum_low := rfl

end PiecesLow

section VIWire
open Complex

theorem half_le_wired : ∫ τ in Ioi (0 : ℝ), Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 10.878 := by
  rw [Prep1121DIntegrable.half_line_split]
  linarith [sum_low_wired, Prep1121VIPiecesHigh.sum_high, Prep1121DTail.tail_le]

/-- PROVED up to the four pieces 07 to 10 of Prep1121VIPiecesHigh. Twin of
`Prep1121VIIntegral.certified_integral` with the PROVED twins of `Prep1121DIntegrable`,
`Prep1121DTail` and `Prep1121DLogWeight`. P0014 page 35, the integral after display 4.12 with the lab's constant 6.01 in place of
the printed √(226.844/(2π)) = 6.00868:
∫_ℝ ((1/2) log(τ² + 9/4) + 4.1396 + log π)² / (1/4 + τ²) dτ ≤ 2π · 6.01². -/
theorem certified_integral_wired :
    ∫ τ : ℝ, ((1 / 2) * Real.log (τ ^ 2 + 9 / 4) + (4.1396 + Real.log π)) ^ 2 /
        (1 / 4 + τ ^ 2) ≤ 2 * π * 6.01 ^ 2 := by
  rw [Prep1121DIntegrable.expand_square, Prep1121VIIntegral.full_eq_two_half,
    Prep1121DLogWeight.integral_log_weight, Prep1121VIIntegral.integral_weight]
  have hH := half_le_wired
  have hlp := Prep1121VIIntegral.log_pi_le
  have hlp0 : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hl2 := Real.log_two_lt_d9
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hpi1 := Real.pi_lt_d6
  have hpi2 := Real.pi_gt_d6
  set C := 4.1396 + Real.log π with hC
  have hC1 : C ≤ 5.2845 := by rw [hC]; linarith
  have hC0 : 0 ≤ C := by rw [hC]; linarith
  have h1 : C * (4 * π * Real.log 2) ≤ 5.2845 * (4 * 3.141593 * 0.6931471808) := by
    have : π * Real.log 2 ≤ 3.141593 * 0.6931471808 :=
      mul_le_mul hpi1.le hl2.le hl20 (by norm_num)
    have h' : 4 * π * Real.log 2 ≤ 4 * 3.141593 * 0.6931471808 := by nlinarith
    have h0 : 0 ≤ 4 * π * Real.log 2 := by positivity
    exact mul_le_mul hC1 h' h0 (by norm_num)
  have h2 : C ^ 2 * (2 * π) ≤ 5.2845 ^ 2 * (2 * 3.141593) := by
    have hsq : C ^ 2 ≤ 5.2845 ^ 2 := pow_le_pow_left₀ hC0 hC1 2
    exact mul_le_mul hsq (by linarith) (by positivity) (by norm_num)
  nlinarith

/-- P0014 pages 34 and 35, display 4.12 and the integral after it: hL and hbudget of
`Energy669.vertical_integral_bound_of_log_energy`, for primitive χ. -/
theorem log_energy_wired {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    MemLp (fun τ : ℝ =>
      (deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
        DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I)) /
          (-1 / 2 + τ * Complex.I)) 2 ∧
    Real.sqrt (∫ τ : ℝ,
      ‖(deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
        DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I)) /
          (-1 / 2 + τ * Complex.I)‖ ^ 2) ≤ Real.sqrt (2 * π) * (Real.log q + 6.01) := by
  set K : ℝ := 4.1396 + Real.log π with hK
  set u : ℝ → ℝ := fun τ => Real.log q / Real.sqrt (1 / 4 + τ ^ 2) with hu
  set v : ℝ → ℝ := fun τ => ((1 / 2) * Real.log (τ ^ 2 + 9 / 4) + K) /
    Real.sqrt (1 / 4 + τ ^ 2) with hv
  obtain ⟨hu2, hv2⟩ := Prep1121DIntegrable.memLp_split (Real.log q) K
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlpi : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hcont := Prep1121DLineCont.logDeriv_line_continuous hχ
  have hmeas : AEStronglyMeasurable (fun τ : ℝ =>
      (deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
        DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I)) /
          (-1 / 2 + τ * Complex.I)) volume := by
    refine (hcont.div (by fun_prop) ?_).aestronglyMeasurable
    intro τ h
    have := congrArg Complex.re h
    simp at this
  have hpt : ∀ τ : ℝ, ‖(deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
        DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I)) /
          (-1 / 2 + τ * Complex.I)‖ ≤ u τ + v τ := by
    intro τ
    have hP := Prep1121VIPointwise.pointwise_4_12 hχ τ
    have habs : |Real.log (q / π)| ≤ Real.log q + Real.log π := by
      rw [Real.log_div (by positivity) (by positivity)]
      rw [abs_le]; constructor <;> linarith
    have hs : 0 < Real.sqrt (1 / 4 + τ ^ 2) := Real.sqrt_pos.mpr (by positivity)
    rw [norm_div, Prep1121VIBudget.norm_line, hu, hv, ← add_div]
    apply div_le_div_of_nonneg_right _ hs.le
    rw [hK]; linarith
  obtain ⟨hL, hB⟩ := Prep1121VIBudget.l2_triangle _ u v hmeas hu2 hv2 hpt
  refine ⟨hL, hB.trans ?_⟩
  have hw := Prep1121VIIntegral.integral_weight
  have hsq : ∀ τ : ℝ, Real.sqrt (1 / 4 + τ ^ 2) ^ 2 = 1 / 4 + τ ^ 2 := fun τ =>
    Real.sq_sqrt (by positivity)
  have hU : ∫ τ, u τ ^ 2 = Real.log q ^ 2 * (2 * π) := by
    simp only [hu, div_pow, hsq]
    rw [← hw, ← integral_const_mul]
    congr 1; funext τ; ring
  have hV : ∫ τ, v τ ^ 2 = ∫ τ : ℝ, ((1 / 2) * Real.log (τ ^ 2 + 9 / 4) + (4.1396 + Real.log π)) ^ 2 /
        (1 / 4 + τ ^ 2) := by
    simp only [hv, div_pow, hsq, hK]
  have hI := certified_integral_wired
  rw [hU, hV]
  have h1 : Real.sqrt (Real.log q ^ 2 * (2 * π)) = Real.log q * Real.sqrt (2 * π) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hlq]
  have h2 : Real.sqrt (∫ τ : ℝ, ((1 / 2) * Real.log (τ ^ 2 + 9 / 4) + (4.1396 + Real.log π)) ^ 2 /
        (1 / 4 + τ ^ 2)) ≤ Real.sqrt (2 * π) * 6.01 := by
    calc _ ≤ Real.sqrt (2 * π * 6.01 ^ 2) := Real.sqrt_le_sqrt hI
      _ = Real.sqrt (2 * π) * 6.01 := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rw [h1]
  nlinarith [h2]

/-- P0014 Lemma 4.1, pages 34 and 35, displays 4.10 to 4.15: the exact statement of
`MainLemma41Split123.vertical_integral_bound`, proved from the leaves of the six
Prep1121VI files through `Energy669.vertical_integral_bound_of_log_energy`, with the PROVED twins in place of the
leaves `logDeriv_line_continuous`, `memLp_split`, `expand_square`, `half_line_split`, `tail_le` and
`integral_log_weight`. -/
theorem vertical_integral_bound_wired (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ : ℝ) :
    (2 * π)⁻¹ * ∫ τ : ℝ,
        ‖deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
            DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I) *
          MainLemma41Split123.contMellin δ (-1 / 2 + τ * Complex.I)‖ ≤
      (Real.log q + 6.01) * (Real.sqrt (Real.sqrt π / 4) + 2 * π * |δ| *
        Real.sqrt LeanLab.HelfgottMajor.Sec45.nTwo) := by
  obtain ⟨hL, hB⟩ := log_energy_wired hχ
  exact Energy669.vertical_integral_bound_of_log_energy q χ δ hL hB

/-- PROVED, by rfl. Match check: `vertical_integral_bound_wired` has exactly the type of the
route step `MainLemma41Split123.vertical_integral_bound`. -/
example : type_of% @vertical_integral_bound_wired =
    type_of% @MainLemma41Split123.vertical_integral_bound := rfl

end VIWire

open Classical in
/-- Assembly, no sorry of its own: the exact statement of the sealed
Lemma41Leaf123.lemma_4_1_gaussian_corrected, P0014 Lemma 4.1, page 31, displays 4.1 to 4.3, for
η♥ of page 44, in CORRECTED form, from `contour_shift_wired`, the PROVED
`MainLemma41Split123.residue_at_zero` and `laurent_c0_bound`, and
`vertical_integral_bound_wired`. -/
theorem lemma_4_1_gaussian_corrected_frontier (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    ∃ c : ℂ, ‖c‖ ≤ Lemma41Terms.c0 1.03045 1.07791 2.15581 1.03045 |δ| ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T +
        ((if q = 1 then ((log (2 * π) : ℝ) : ℂ) else
            ((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
              (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
                DirichletCharacter.LFunction χ 1)) +
          (if q ≠ 1 ∧ χ.Even then ((log x : ℝ) : ℂ) else 0) + c)‖ ≤
        (log q + 6.01) * (sqrt (sqrt π / 4) + 2 * π * |δ| * sqrt Sec45.nTwo) / sqrt x := by
  classical
  have hx0 : 0 < x := by linarith
  obtain ⟨r, hr, hF, hshift⟩ := contour_shift_wired x hx q χ hχ δ T
  have hres := MainLemma41Split123.residue_at_zero x hx q χ hχ δ r hr hF
  have hc0 : 0 ≤ Lemma41Terms.c0 1.03045 1.07791 2.15581 1.03045 |δ| := by
    unfold Lemma41Terms.c0; have := pi_pos; positivity
  refine ⟨if q ≠ 1 ∧ χ.Even then laurentC0 δ else 0, ?_, ?_⟩
  · split_ifs
    · exact MainLemma41Split123.laurent_c0_bound δ
    · simpa using hc0
  · have hsplit : ((if q = 1 then ((log (2 * π) : ℝ) : ℂ) else
            ((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
              (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
                DirichletCharacter.LFunction χ 1)) +
          (if q ≠ 1 ∧ χ.Even then ((log x : ℝ) : ℂ) else 0) +
          (if q ≠ 1 ∧ χ.Even then laurentC0 δ else 0)) =
        (2 * π * Complex.I)⁻¹ * circleIntegral (contourIntegrand χ δ x) 0 r := by
      rw [hres]; split_ifs <;> ring
    rw [hsplit, hshift, norm_neg, norm_mul]
    have hnorm : ∀ τ : ℝ, ‖contourIntegrand χ δ x (-1 / 2 + τ * Complex.I)‖ =
        ‖deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
            DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I) *
          contMellin δ (-1 / 2 + τ * Complex.I)‖ * (sqrt x)⁻¹ := by
      intro τ
      rw [contourIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      congr 1
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.one_re,
        Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
      rw [sqrt_eq_rpow, ← rpow_neg hx0.le]
      norm_num
    have hI := norm_integral_le_integral_norm (μ := volume)
      (fun τ : ℝ => contourIntegrand χ δ x (-1 / 2 + τ * Complex.I))
    simp_rw [hnorm] at hI
    rw [integral_mul_const] at hI
    have hV := vertical_integral_bound_wired q χ hχ δ
    have hn2 : ‖((2 * π : ℂ))⁻¹‖ = (2 * π)⁻¹ := by
      rw [norm_inv]; congr 1
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hn2]
    have hs : 0 < (sqrt x)⁻¹ := inv_pos.mpr (sqrt_pos.mpr hx0)
    have hp : 0 < (2 * π)⁻¹ := by positivity
    calc (2 * π)⁻¹ * ‖∫ τ : ℝ, contourIntegrand χ δ x (-1 / 2 + τ * Complex.I)‖
        ≤ (2 * π)⁻¹ * ((∫ τ : ℝ,
            ‖deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
              DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I) *
            contMellin δ (-1 / 2 + τ * Complex.I)‖) * (sqrt x)⁻¹) :=
          mul_le_mul_of_nonneg_left hI hp.le
      _ = ((2 * π)⁻¹ * ∫ τ : ℝ,
            ‖deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
              DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I) *
            contMellin δ (-1 / 2 + τ * Complex.I)‖) * (sqrt x)⁻¹ := by ring
      _ ≤ (log q + 6.01) * (sqrt (sqrt π / 4) + 2 * π * |δ| * sqrt Sec45.nTwo) *
            (sqrt x)⁻¹ := mul_le_mul_of_nonneg_right hV hs.le
      _ = _ := by ring

/-- PROVED, by rfl. Match check against the sealed parent. -/
example : type_of% @lemma_4_1_gaussian_corrected_frontier =
    type_of% @Lemma41Leaf123.lemma_4_1_gaussian_corrected := rfl

end LeanLab.HelfgottMajor.Lemma41Frontier1122

#print axioms LeanLab.HelfgottMajor.Lemma41Frontier1122.contour_shift_wired
#print axioms LeanLab.HelfgottMajor.Lemma41Frontier1122.piece_00_wired
#print axioms LeanLab.HelfgottMajor.Lemma41Frontier1122.piece_01_wired
#print axioms LeanLab.HelfgottMajor.Lemma41Frontier1122.piece_02_wired
#print axioms LeanLab.HelfgottMajor.Lemma41Frontier1122.piece_03_wired
#print axioms LeanLab.HelfgottMajor.Lemma41Frontier1122.piece_04_wired
#print axioms LeanLab.HelfgottMajor.Lemma41Frontier1122.piece_05_wired
#print axioms LeanLab.HelfgottMajor.Lemma41Frontier1122.piece_06_wired
#print axioms LeanLab.HelfgottMajor.Lemma41Frontier1122.sum_low_wired
#print axioms LeanLab.HelfgottMajor.Lemma41Frontier1122.half_le_wired
#print axioms LeanLab.HelfgottMajor.Lemma41Frontier1122.certified_integral_wired
#print axioms LeanLab.HelfgottMajor.Lemma41Frontier1122.log_energy_wired
#print axioms LeanLab.HelfgottMajor.Lemma41Frontier1122.vertical_integral_bound_wired
#print axioms LeanLab.HelfgottMajor.Lemma41Frontier1122.lemma_4_1_gaussian_corrected_frontier
