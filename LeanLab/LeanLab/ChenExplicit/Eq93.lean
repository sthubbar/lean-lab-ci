/-
AI-written Lean code, Claude, 2026-10-17, run 20261017T2104Z-19452, unit U-0375.
P0010 T. Yamada, Explicit Chen's theorem, arXiv 1511.03409v2, Section 6, equation (93).

(93) bounds `∫_z^y dt / (t log t log^{3/2}(N^{1/2}/t))`, `z = N^{1/8}`, `y = N^{1/3}`, by
`4√2(√3 - √(4/3)) / log^{3/2} N + 188.2 / log^{7/2} N`, with `4√2(√3 - √(4/3)) = 3.26599`.
PROVED here: the integral is at least `6(√6 - √(8/3)) / log^{3/2} N ≈ 4.899 / log^{3/2} N`, so the
printed bound FAILS for every `N` with `log N ≥ 100`. With `t = N^u` the integral is exactly
`∫_{1/8}^{1/3} du / (u (1/2 - u)^{3/2}) / log^{3/2} N ≈ 6.9909 / log^{3/2} N`, our Python.
`log^{3/2}` is written `g · √g`. Section 8 survives, see `yamada_of_section8_C6`.
-/
import LeanLab.ChenExplicit.Thm48

open Real intervalIntegral

noncomputable section
namespace LeanLab.ChenExplicit.Yamada

/-- The integrand of (93), with `log^{3/2} x` written `log x · √(log x)`. -/
def integrand93 (N t : ℝ) : ℝ :=
  1 / (t * log t * (log (√N / t) * √(log (√N / t))))

/-- The right side of (93). -/
def rhs93 (N : ℝ) : ℝ :=
  4 * √2 * (√3 - √(4 / 3)) / (log N * √(log N)) + 1882 / 10 / (log N ^ 3 * √(log N))

lemma log_sqrt_div (N t : ℝ) (hN : 0 < N) (ht : 0 < t) :
    log (√N / t) = log N / 2 - log t := by
  rw [Real.log_div (Real.sqrt_pos.mpr hN).ne' ht.ne', Real.log_sqrt hN.le]

/-- The antiderivative `2 / √(L/2 - log t)` of `1 / (t (L/2 - log t)^{3/2})`. -/
lemma hasDerivAt_F (L t : ℝ) (ht : 0 < t) (hg : 0 < L / 2 - log t) :
    HasDerivAt (fun s => 2 / √(L / 2 - log s))
      (1 / (t * ((L / 2 - log t) * √(L / 2 - log t)))) t := by
  have h1 : HasDerivAt (fun s => L / 2 - log s) (-t⁻¹) t := by
    exact (Real.hasDerivAt_log ht.ne').const_sub (L / 2)
  have h2 := h1.sqrt hg.ne'
  have hs : 0 < √(L / 2 - log t) := Real.sqrt_pos.mpr hg
  have h3 := (hasDerivAt_const t (2 : ℝ)).div h2 hs.ne'
  convert h3 using 1
  have hsq : √(L / 2 - log t) ^ 2 = L / 2 - log t := Real.sq_sqrt hg.le
  generalize √(L / 2 - log t) = S at hsq hs ⊢
  rw [← hsq]
  field_simp
  ring

lemma interval_facts (N t : ℝ) (hN1 : 1 < N)
    (ht : t ∈ Set.uIcc (N ^ ((1 : ℝ) / 8)) (N ^ ((1 : ℝ) / 3))) :
    0 < t ∧ log N / 8 ≤ log t ∧ log t ≤ log N / 3 := by
  have hN0 : 0 < N := by linarith
  have hL : 0 < log N := Real.log_pos hN1
  have hz : N ^ ((1 : ℝ) / 8) = exp (log N / 8) := by rw [rpow_def_of_pos hN0]; ring_nf
  have hy : N ^ ((1 : ℝ) / 3) = exp (log N / 3) := by rw [rpow_def_of_pos hN0]; ring_nf
  have hzy : exp (log N / 8) ≤ exp (log N / 3) := exp_le_exp.mpr (by linarith)
  rw [hz, hy, Set.uIcc_of_le hzy] at ht
  have ht0 : 0 < t := lt_of_lt_of_le (exp_pos _) ht.1
  refine ⟨ht0, ?_, ?_⟩
  · rw [← Real.log_exp (log N / 8)]; exact Real.log_le_log (exp_pos _) ht.1
  · rw [← Real.log_exp (log N / 3)]; exact Real.log_le_log ht0 ht.2

/-- **(93) fails, PROVED.** For every `N` with `log N ≥ 100`, the integral in (93) exceeds the
printed bound. -/
theorem eq93_fails (N : ℝ) (hN1 : 1 < N) (hN : 100 ≤ log N) :
    rhs93 N < ∫ t in N ^ ((1 : ℝ) / 8)..N ^ ((1 : ℝ) / 3), integrand93 N t := by
  have hN0 : 0 < N := by linarith
  set L := log N with hLdef
  have hL : 0 < L := by linarith
  set z := N ^ ((1 : ℝ) / 8) with hzdef
  set y := N ^ ((1 : ℝ) / 3) with hydef
  have hz : z = exp (L / 8) := by rw [hzdef, rpow_def_of_pos hN0, ← hLdef]; ring_nf
  have hy : y = exp (L / 3) := by rw [hydef, rpow_def_of_pos hN0, ← hLdef]; ring_nf
  have hzy : z ≤ y := by rw [hz, hy]; exact exp_le_exp.mpr (by linarith)
  have hF := fun t (ht : t ∈ Set.uIcc z y) =>
    hasDerivAt_F L t (interval_facts N t hN1 ht).1 (by
      have := interval_facts N t hN1 ht; linarith)
  set ℓ : ℝ → ℝ := fun t => 3 / L * (1 / (t * ((L / 2 - log t) * √(L / 2 - log t)))) with hℓ
  have hcont_l : ContinuousOn (fun t => 1 / (t * ((L / 2 - log t) * √(L / 2 - log t))))
      (Set.uIcc z y) := by
    apply ContinuousOn.div continuousOn_const
    · apply ContinuousOn.mul continuousOn_id
      apply ContinuousOn.mul
      · exact continuousOn_const.sub (continuousOn_log.mono fun t ht =>
          (interval_facts N t hN1 ht).1.ne')
      · exact Real.continuous_sqrt.comp_continuousOn (continuousOn_const.sub
          (continuousOn_log.mono fun t ht => (interval_facts N t hN1 ht).1.ne'))
    · intro t ht
      have h := interval_facts N t hN1 ht
      have hg : 0 < L / 2 - log t := by linarith
      have := Real.sqrt_pos.mpr hg
      have := h.1
      positivity
  have hint_l : ∫ t in z..y, ℓ t = 3 / L * (2 / √(L / 2 - log y) - 2 / √(L / 2 - log z)) := by
    rw [hℓ, intervalIntegral.integral_const_mul,
      integral_eq_sub_of_hasDerivAt hF (hcont_l.intervalIntegrable)]
  have hcont_f : ContinuousOn (integrand93 N) (Set.uIcc z y) := by
    have e : Set.EqOn (integrand93 N)
        (fun t => 1 / (t * log t * ((L / 2 - log t) * √(L / 2 - log t)))) (Set.uIcc z y) := by
      intro t ht
      simp only [integrand93]
      rw [log_sqrt_div N t hN0 (interval_facts N t hN1 ht).1]
    apply ContinuousOn.congr _ e
    apply ContinuousOn.div continuousOn_const
    · apply ContinuousOn.mul
      · exact continuousOn_id.mul (continuousOn_log.mono fun t ht =>
          (interval_facts N t hN1 ht).1.ne')
      apply ContinuousOn.mul
      · exact continuousOn_const.sub (continuousOn_log.mono fun t ht =>
          (interval_facts N t hN1 ht).1.ne')
      · exact Real.continuous_sqrt.comp_continuousOn (continuousOn_const.sub
          (continuousOn_log.mono fun t ht => (interval_facts N t hN1 ht).1.ne'))
    · intro t ht
      have h := interval_facts N t hN1 ht
      have hg : 0 < L / 2 - log t := by linarith
      have := Real.sqrt_pos.mpr hg
      have := h.1
      have : 0 < log t := by linarith
      positivity
  have hmono : ∫ t in z..y, ℓ t ≤ ∫ t in z..y, integrand93 N t := by
    apply intervalIntegral.integral_mono_on hzy (hcont_l.intervalIntegrable.const_mul _)
      hcont_f.intervalIntegrable
    intro t ht
    have ht' : t ∈ Set.uIcc z y := by rw [Set.uIcc_of_le hzy]; exact ht
    have h := interval_facts N t hN1 ht'
    have hg : 0 < L / 2 - log t := by linarith
    have hs := Real.sqrt_pos.mpr hg
    have hlt : 0 < log t := by linarith
    simp only [hℓ, integrand93]
    rw [log_sqrt_div N t hN0 h.1]
    have hP : 0 < t * ((L / 2 - log t) * √(L / 2 - log t)) := by have := h.1; positivity
    rw [mul_one_div, show t * log t * ((L / 2 - log t) * √(L / 2 - log t)) =
      log t * (t * ((L / 2 - log t) * √(L / 2 - log t))) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : 3 / L * log t ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one hL]; linarith [h.2.2]
    nlinarith [mul_le_mul_of_nonneg_right h3 hP.le]
  -- evaluate
  have hly : log y = L / 3 := by rw [hy, Real.log_exp]
  have hlz : log z = L / 8 := by rw [hz, Real.log_exp]
  rw [hly, hlz] at hint_l
  set r := √L with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hL
  have hr2 : r ^ 2 = L := Real.sq_sqrt hL.le
  have e1 : √(L / 2 - L / 3) = r / √6 := by
    rw [show L / 2 - L / 3 = L / 6 by ring, Real.sqrt_div' _ (by norm_num)]
  have e2 : √(L / 2 - L / 8) = √(3 / 8) * r := by
    rw [show L / 2 - L / 8 = 3 / 8 * L by ring, Real.sqrt_mul (by norm_num)]
  rw [e1, e2] at hint_l
  have s6 : (2449 / 1000 : ℝ) < √6 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s38 : (6123 / 10000 : ℝ) < √(3 / 8) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : √2 < 141422 / 100000 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have s3 : √3 < 173206 / 100000 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have s43 : (11547 / 10000 : ℝ) < √(4 / 3) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h6pos : 0 < √6 := by linarith
  have h38pos : 0 < √(3 / 8) := by linarith
  -- the lower bound in the form c / (L r)
  have hlow : 3 * (2 * (2449 / 1000) - 2 * (10000 / 6123)) / (L * r) ≤ ∫ t in z..y, ℓ t := by
    rw [hint_l]
    have a1 : 2 / (r / √6) = 2 * √6 / r := by field_simp
    have a2 : 2 / (√(3 / 8) * r) = 2 / √(3 / 8) / r := by field_simp
    have a3 : 2 / √(3 / 8) ≤ 2 * (10000 / 6123) := by
      rw [div_le_iff₀ h38pos]; nlinarith
    rw [a1, a2, show 3 / L * (2 * √6 / r - 2 / √(3 / 8) / r) =
      3 * (2 * √6 - 2 / √(3 / 8)) / (L * r) by field_simp]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hrhs : rhs93 N ≤ (4 * (141422 / 100000) * (173206 / 100000 - 11547 / 10000) +
      1882 / 10 / 10000) / (L * r) := by
    simp only [rhs93]
    rw [← hLdef, ← hr]
    have k1 : 4 * √2 * (√3 - √(4 / 3)) ≤ 4 * (141422 / 100000) * (173206 / 100000 - 11547 / 10000) := by
      have : 0 ≤ √2 := Real.sqrt_nonneg 2
      have : 0 ≤ √3 - √(4 / 3) := by
        rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by norm_num)
      nlinarith
    have k2 : 1882 / 10 / (L ^ 3 * r) ≤ 1882 / 10 / 10000 / (L * r) := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 10000 ≤ L ^ 2 := by nlinarith
      have hLr : 0 < L * r := by positivity
      nlinarith
    rw [add_div]
    apply add_le_add _ k2
    exact div_le_div_of_nonneg_right k1 (by positivity)
  have hLr : 0 < L * r := by positivity
  have final : (4 * (141422 / 100000) * (173206 / 100000 - 11547 / 10000) + 1882 / 10 / 10000) /
      (L * r) < 3 * (2 * (2449 / 1000) - 2 * (10000 / 6123)) / (L * r) :=
    div_lt_div_of_pos_right (by norm_num) hLr
  linarith

end LeanLab.ChenExplicit.Yamada
