/-
AI-written Lean code, Claude, 2026-10-17, run 20261017T2104Z-19452, unit U-0376.
P0010 T. Yamada, Explicit Chen's theorem, arXiv 1511.03409v2, Section 7, (110), (111), (116).

(110) defines `H(u) = ∫_y^{(N/u)^{1/2}} d log log t / log(N/(ut))`, `y = N^{1/3}`, and Lemma 7.3's proof
uses `H(z) = log(26/21) / log N` for `z = N^{1/8}`. By (111) the true value is
`(1/log N) ∫_{1/3}^{7/16} dβ / (β (7/8 - β)) = (8/7) log(13/8) / log N ≈ 0.5549 / log N`, not
`log(26/21) / log N ≈ 0.2136 / log N`: the printed value keeps only the `1/(7/8 - β)` part of the
partial fractions and drops the factor `8/7`.
PROVED here: `H(z) ≥ (16/7) log(26/21) / log N > log(26/21) / log N` once `log N ≥ 100`.
`d log log t` is written `dt / (t log t)`. The effect on Yamada's results is of order
`1 / log³ N`, absorbed in the `2.207` of Lemma 7.3; no theorem changes.
-/
import LeanLab.ChenExplicit.Eq93

open Real intervalIntegral

noncomputable section
namespace LeanLab.ChenExplicit.Yamada

/-- (110): `H(u) = ∫_y^{(N/u)^{1/2}} d log log t / log(N/(ut))`, with `d log log t = dt/(t log t)`. -/
def Hfun (N u : ℝ) : ℝ :=
  ∫ t in N ^ ((1 : ℝ) / 3)..(N / u) ^ ((1 : ℝ) / 2), 1 / (t * log t * log (N / (u * t)))

lemma hasDerivAt_G (c t : ℝ) (ht : 0 < t) (hg : 0 < c - log t) :
    HasDerivAt (fun s => -log (c - log s)) (1 / (t * (c - log t))) t := by
  have h1 : HasDerivAt (fun s => c - log s) (-t⁻¹) t :=
    (Real.hasDerivAt_log ht.ne').const_sub c
  have h2 := (h1.log hg.ne').neg
  convert h2 using 1
  field_simp

/-- **`H(z)` as printed fails, PROVED.** For `log N ≥ 100`,
`H(N^{1/8}) ≥ (16/7) log(26/21) / log N > log(26/21) / log N`. -/
theorem Hz_gt (N : ℝ) (hN1 : 1 < N) (hN : 100 ≤ log N) :
    log (26 / 21) / log N < Hfun N (N ^ ((1 : ℝ) / 8)) := by
  have hN0 : 0 < N := by linarith
  set L := log N with hLdef
  have hL : 0 < L := by linarith
  have hy : N ^ ((1 : ℝ) / 3) = exp (L / 3) := by rw [rpow_def_of_pos hN0, ← hLdef]; ring_nf
  have hz : N ^ ((1 : ℝ) / 8) = exp (L / 8) := by rw [rpow_def_of_pos hN0, ← hLdef]; ring_nf
  have htop : (N / N ^ ((1 : ℝ) / 8)) ^ ((1 : ℝ) / 2) = exp (7 * L / 16) := by
    rw [hz, show N = exp L by rw [hLdef, exp_log hN0], ← exp_sub, rpow_def_of_pos (exp_pos _),
      log_exp]
    ring_nf
  unfold Hfun
  rw [hy, htop, hz]
  set a := exp (L / 3) with ha
  set b := exp (7 * L / 16) with hb
  have hab : a ≤ b := exp_le_exp.mpr (by linarith)
  have hI : ∀ t ∈ Set.uIcc a b, 0 < t ∧ L / 3 ≤ log t ∧ log t ≤ 7 * L / 16 := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : 0 < t := lt_of_lt_of_le (exp_pos _) ht.1
    refine ⟨ht0, ?_, ?_⟩
    · rw [← Real.log_exp (L / 3)]; exact Real.log_le_log (exp_pos _) ht.1
    · rw [← Real.log_exp (7 * L / 16)]; exact Real.log_le_log ht0 ht.2
  have hlogarg : ∀ t, 0 < t → log (N / (exp (L / 8) * t)) = 7 * L / 8 - log t := by
    intro t ht
    rw [Real.log_div hN0.ne' (by positivity), Real.log_mul (exp_pos _).ne' ht.ne', log_exp]
    ring
  set c := 7 * L / 8 with hc
  have hG := fun t (ht : t ∈ Set.uIcc a b) =>
    hasDerivAt_G c t (hI t ht).1 (by have := hI t ht; rw [hc]; linarith)
  have hcont_l : ContinuousOn (fun t => 1 / (t * (c - log t))) (Set.uIcc a b) := by
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_id.mul (continuousOn_const.sub (continuousOn_log.mono fun t ht =>
        (hI t ht).1.ne'))
    · intro t ht
      have h := hI t ht
      have : 0 < c - log t := by rw [hc]; linarith
      have := h.1
      positivity
  have hint : ∫ t in a..b, 16 / (7 * L) * (1 / (t * (c - log t))) =
      16 / (7 * L) * (-log (c - log b) - -log (c - log a)) := by
    rw [intervalIntegral.integral_const_mul,
      integral_eq_sub_of_hasDerivAt hG hcont_l.intervalIntegrable]
  have hcont_f : ContinuousOn (fun t => 1 / (t * log t * log (N / (exp (L / 8) * t))))
      (Set.uIcc a b) := by
    have e : Set.EqOn (fun t => 1 / (t * log t * log (N / (exp (L / 8) * t))))
        (fun t => 1 / (t * log t * (c - log t))) (Set.uIcc a b) := by
      intro t ht
      simp only
      rw [hlogarg t (hI t ht).1]
    apply ContinuousOn.congr _ e
    apply ContinuousOn.div continuousOn_const
    · apply ContinuousOn.mul
      · exact continuousOn_id.mul (continuousOn_log.mono fun t ht => (hI t ht).1.ne')
      · exact continuousOn_const.sub (continuousOn_log.mono fun t ht => (hI t ht).1.ne')
    · intro t ht
      have h := hI t ht
      have : 0 < c - log t := by rw [hc]; linarith
      have : 0 < log t := by linarith
      have := h.1
      positivity
  have hmono : ∫ t in a..b, 16 / (7 * L) * (1 / (t * (c - log t))) ≤
      ∫ t in a..b, 1 / (t * log t * log (N / (exp (L / 8) * t))) := by
    apply intervalIntegral.integral_mono_on hab (hcont_l.intervalIntegrable.const_mul _)
      hcont_f.intervalIntegrable
    intro t ht
    have ht' : t ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact ht
    have h := hI t ht'
    have hg : 0 < c - log t := by rw [hc]; linarith
    have hlt : 0 < log t := by linarith
    rw [hlogarg t h.1]
    have hP : 0 < t * (c - log t) := by have := h.1; positivity
    rw [mul_one_div, show t * log t * (c - log t) = log t * (t * (c - log t)) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : 16 / (7 * L) * log t ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one (by positivity)]; linarith [h.2.2]
    nlinarith [mul_le_mul_of_nonneg_right h3 hP.le]
  -- evaluate
  have hla : log a = L / 3 := by rw [ha, log_exp]
  have hlb : log b = 7 * L / 16 := by rw [hb, log_exp]
  rw [hla, hlb] at hint
  have e1 : c - 7 * L / 16 = 7 / 16 * L := by rw [hc]; ring
  have e2 : c - L / 3 = 13 / 24 * L := by rw [hc]; ring
  rw [e1, e2, Real.log_mul (by norm_num) hL.ne', Real.log_mul (by norm_num) hL.ne'] at hint
  have hval : 16 / (7 * L) * (-(log (7 / 16) + log L) - -(log (13 / 24) + log L)) =
      16 / 7 * log (26 / 21) / L := by
    have : log (26 / 21 : ℝ) = log (13 / 24) - log (7 / 16) := by
      rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
    rw [this]; field_simp; ring
  rw [hval] at hint
  have hpos : 0 < log (26 / 21 : ℝ) := Real.log_pos (by norm_num)
  have hlt : log (26 / 21) / L < 16 / 7 * log (26 / 21) / L := by
    apply div_lt_div_of_pos_right _ hL; linarith
  linarith

end LeanLab.ChenExplicit.Yamada
