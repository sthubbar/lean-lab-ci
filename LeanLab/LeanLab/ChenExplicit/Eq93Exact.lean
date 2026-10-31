/-
AI-written Lean code, Claude, 2026-10-18, run 20261018T1203Z-2488, unit U-0941.
P0010 T. Yamada, Explicit Chen's theorem, arXiv 1511.03409v2, Section 6, (91) to (97),
read in Claude in Chrome on ar5iv.

Eq93.lean, F-0013, showed the printed bound in (93) is too small. This file finds the exact
value and the corrected Theorem 6.1 constant:
* PROVED `integral93_eq`: for `N > 1` the integral of (93) from `N^{1/8}` to `N^{1/3}` equals
  `K93 / log^{3/2} N` with `K93 = 4(√6 - √(8/3)) + 2√2 log(2 + √3) ≈ 6.99091`.
  Yamada's `4√2(√3 - √(4/3)) = 4(√6 - √(8/3)) ≈ 3.26599` is the first term alone: the
  `2√2 log(2 + √3)` term, coming from the factor `1 / log t`, is missing.
* PROVED `K93_bounds`: `6.98 < K93 < 7.19`.
* Theorem 6.1's `993.2507` is `976.1256` of (97) plus `17.125`; (97)'s `976.1256` is
  `298.87013 × 3.26599`. With `K93` in place of `3.26599` the constant becomes
  `C6corr = 993.2507 - 976.1256 + 298.87013 K93 ≈ 2106.5`. PROVED `C6corr_le`: at most 2200.
* `yamada_of_section8_corr`: Theorem 1.1 CONDITIONAL ON (48), Theorems 5.1, 7.1, `c₂` bound and
  Theorem 6.1 with the corrected constant `C6corr`; the arithmetic is `yamada_of_section8_C6`.
Chen's theorem is known; binary Goldbach is OPEN.
-/
import LeanLab.ChenExplicit.Eq93

open Real intervalIntegral

noncomputable section
namespace LeanLab.ChenExplicit.Yamada

/-- The exact constant of (93). -/
def K93 : ℝ := 4 * (√6 - √(8 / 3)) + 2 * √2 * log (2 + √3)

/-- Antiderivative of the (93) integrand, `c = log N / 2`, `S = c - log t`. -/
def F93 (c t : ℝ) : ℝ :=
  2 / (c * √(c - log t)) -
    (log (√c + √(c - log t)) - log (√c - √(c - log t))) / (c * √c)

lemma hasDerivAt_F93 (c t : ℝ) (ht : 0 < t) (hlt : 0 < log t) (hS : 0 < c - log t) :
    HasDerivAt (F93 c)
      (1 / (t * log t * ((c - log t) * √(c - log t)))) t := by
  have hc : 0 < c := by linarith
  have h1 : HasDerivAt (fun s => c - log s) (-t⁻¹) t :=
    (Real.hasDerivAt_log ht.ne').const_sub c
  have hw := h1.sqrt hS.ne'
  set w := √(c - log t) with hwdef
  set a := √c with hadef
  have hw0 : 0 < w := Real.sqrt_pos.mpr hS
  have ha0 : 0 < a := Real.sqrt_pos.mpr hc
  have hw2 : w ^ 2 = c - log t := Real.sq_sqrt hS.le
  have ha2 : a ^ 2 = c := Real.sq_sqrt hc.le
  have hwa : w < a := by
    rw [hwdef, hadef]; exact Real.sqrt_lt_sqrt hS.le (by linarith)
  have hp : 0 < a + w := by linarith
  have hm : 0 < a - w := by linarith
  have d1 := (hasDerivAt_const t (2 : ℝ)).div ((hasDerivAt_const t c).mul hw)
    (by positivity : c * w ≠ 0)
  have d2 := ((hasDerivAt_const t a).add hw).log hp.ne'
  have d3 := ((hasDerivAt_const t a).sub hw).log hm.ne'
  have d4 := (d2.sub d3).div_const (c * a)
  have d5 := d1.sub d4
  convert d5 using 1
  · funext s
    simp only [F93, Pi.sub_apply, Pi.div_apply, Pi.mul_apply, Pi.add_apply, hadef]
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply]
  rw [← hwdef]
  have hlog : log t = c - w ^ 2 := by linarith
  rw [hlog]
  have hcw : 0 < c - w ^ 2 := by rw [← hlog]; exact hlt
  field_simp
  rw [← ha2] at hcw ⊢
  have hcw' : (a + w) * (a - w) = a ^ 2 - w ^ 2 := by ring
  field_simp
  ring

/-- `log (x + y) - log (x - y) = log k` when `x + y = k (x - y)`. -/
lemma log_ratio (x y k : ℝ) (hm : 0 < x - y) (hk : 0 < k) (h : x + y = k * (x - y)) :
    log (x + y) - log (x - y) = log k := by
  rw [h, Real.log_mul hk.ne' hm.ne']; ring

set_option maxHeartbeats 1000000 in
theorem integral93_eq (N : ℝ) (hN1 : 1 < N) :
    ∫ t in N ^ ((1 : ℝ) / 8)..N ^ ((1 : ℝ) / 3), integrand93 N t =
      K93 / (log N * √(log N)) := by
  have hN0 : 0 < N := by linarith
  set L := log N with hLdef
  have hL : 0 < L := Real.log_pos hN1
  set c := L / 2 with hc
  set z := N ^ ((1 : ℝ) / 8) with hzdef
  set y := N ^ ((1 : ℝ) / 3) with hydef
  have hz : z = exp (L / 8) := by rw [hzdef, rpow_def_of_pos hN0, ← hLdef]; ring_nf
  have hy : y = exp (L / 3) := by rw [hydef, rpow_def_of_pos hN0, ← hLdef]; ring_nf
  have hzy : z ≤ y := by rw [hz, hy]; exact exp_le_exp.mpr (by linarith)
  have facts := fun t (ht : t ∈ Set.uIcc z y) => interval_facts N t hN1 ht
  have hderiv : ∀ t ∈ Set.uIcc z y, HasDerivAt (F93 c) (integrand93 N t) t := by
    intro t ht
    have h := facts t ht
    have e : integrand93 N t = 1 / (t * log t * ((c - log t) * √(c - log t))) := by
      simp only [integrand93]
      rw [log_sqrt_div N t hN0 h.1]
    rw [e]
    exact hasDerivAt_F93 c t h.1 (by linarith) (by linarith)
  have hcont : ContinuousOn (integrand93 N) (Set.uIcc z y) := by
    have e : Set.EqOn (integrand93 N)
        (fun t => 1 / (t * log t * ((L / 2 - log t) * √(L / 2 - log t)))) (Set.uIcc z y) := by
      intro t ht
      simp only [integrand93]
      rw [log_sqrt_div N t hN0 (facts t ht).1]
    apply ContinuousOn.congr _ e
    apply ContinuousOn.div continuousOn_const
    · apply ContinuousOn.mul
      · exact continuousOn_id.mul (continuousOn_log.mono fun t ht => (facts t ht).1.ne')
      apply ContinuousOn.mul
      · exact continuousOn_const.sub (continuousOn_log.mono fun t ht => (facts t ht).1.ne')
      · exact Real.continuous_sqrt.comp_continuousOn (continuousOn_const.sub
          (continuousOn_log.mono fun t ht => (facts t ht).1.ne'))
    · intro t ht
      have h := facts t ht
      have hg : 0 < L / 2 - log t := by linarith
      have := Real.sqrt_pos.mpr hg
      have := h.1
      have : 0 < log t := by linarith
      positivity
  rw [integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have hly : log y = L / 3 := by rw [hy, Real.log_exp]
  have hlz : log z = L / 8 := by rw [hz, Real.log_exp]
  simp only [F93, hly, hlz]
  -- everything as multiples of r = √L
  set r := √L with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hL
  have hr2 : r ^ 2 = L := Real.sq_sqrt hL.le
  set α := √(1 / 2 : ℝ) with hα
  set β := √(1 / 6 : ℝ) with hβ
  set δ := √(3 / 8 : ℝ) with hδ
  set q3 := √(3 : ℝ) with hq3
  set q2 := √(2 : ℝ) with hq2
  have hq3s : q3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hq2s : q2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hq30 : 0 < q3 := by positivity
  have hq20 : 0 < q2 := by positivity
  have ec : √c = α * r := by
    rw [hc, show L / 2 = 1 / 2 * L by ring, Real.sqrt_mul (by norm_num)]
  have ey : √(c - L / 3) = β * r := by
    rw [hc, show L / 2 - L / 3 = 1 / 6 * L by ring, Real.sqrt_mul (by norm_num)]
  have ez : √(c - L / 8) = δ * r := by
    rw [hc, show L / 2 - L / 8 = 3 / 8 * L by ring, Real.sqrt_mul (by norm_num)]
  rw [ec, ey, ez]
  have hα0 : 0 < α := by positivity
  have hβ0 : 0 < β := by positivity
  have hαs : α ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hβs : β ^ 2 = 1 / 6 := Real.sq_sqrt (by norm_num)
  have hδs : δ ^ 2 = 3 / 8 := Real.sq_sqrt (by norm_num)
  -- α = √3 β and δ = (√3 / 2) α
  have hαβ : α = q3 * β := by
    rw [hα, hβ, hq3, ← Real.sqrt_mul (by norm_num)]; norm_num
  have hδα : δ = q3 / 2 * α := by
    rw [hδ, hα, hq3]
    rw [show (3 / 8 : ℝ) = (3 / 4) * (1 / 2) by norm_num, Real.sqrt_mul (by norm_num),
      show (3 / 4 : ℝ) = 3 / 2 ^ 2 by norm_num, Real.sqrt_div' _ (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have hk : 0 < 2 + q3 := by positivity
  have hq3lt : q3 < 2 := by nlinarith
  have l1 : log (α * r + β * r) - log (α * r - β * r) = log (2 + q3) := by
    apply log_ratio
    · rw [hαβ]; nlinarith [mul_pos hβ0 hr0]
    · exact hk
    · rw [hαβ]; linear_combination (-(β * r)) * hq3s
  have l2 : log (α * r + δ * r) - log (α * r - δ * r) = 2 * log (2 + q3) := by
    rw [← Real.log_rpow hk, show ((2 + q3) ^ (2:ℝ)) = (2 + q3) ^ 2 by norm_cast]
    apply log_ratio
    · rw [hδα]; nlinarith [mul_pos hα0 hr0]
    · positivity
    · rw [hδα]; linear_combination (α * r * (1 + q3 / 2)) * hq3s
  rw [l1, l2]
  -- the rational parts
  have h6 : √6 = q2 * q3 := by rw [hq2, hq3, ← Real.sqrt_mul (by norm_num)]; norm_num
  have h83 : √(8 / 3 : ℝ) * q3 = 2 * q2 := by
    rw [hq3, hq2, ← Real.sqrt_mul (by norm_num), show (8 / 3 * 3 : ℝ) = 2 ^ 2 * 2 by norm_num,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hαq : α * q2 = 1 := by
    rw [hα, hq2, ← Real.sqrt_mul (by norm_num)]; norm_num
  have h83' : √(8 / 3 : ℝ) = 2 * q2 / q3 := eq_div_of_mul_eq hq30.ne' h83
  simp only [K93, h6, h83']
  rw [← hq2]
  have hβ' : β = α / q3 := eq_div_of_mul_eq hq30.ne' (by rw [hαβ]; ring)
  rw [hβ', hδα]
  have hα' : α = 1 / q2 := eq_div_of_mul_eq hq20.ne' hαq
  rw [hα']
  generalize log (2 + q3) = ℓ
  clear_value r c α β δ q2 q3
  subst hc
  rw [← hr2]
  field_simp
  ring

/-- `6.98 < K93 < 7.19`. -/
theorem K93_bounds : (698 / 100 : ℝ) < K93 ∧ K93 < 719 / 100 := by
  have s6a : (2449 / 1000 : ℝ) < √6 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s6b : √6 < 24495 / 10000 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have s8a : (16329 / 10000 : ℝ) < √(8 / 3) := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s8b : √(8 / 3 : ℝ) < 16330 / 10000 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have s2a : (14142 / 10000 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2b : √2 < 14143 / 10000 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have s3a : (17320 / 10000 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s3b : √3 < 17321 / 10000 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hk : 0 < 2 + √3 := by positivity
  -- upper: log (2 + √3) < log 4 = 2 log 2
  have lu : log (2 + √3) < 13863 / 10000 := by
    have : log (2 + √3) < log 4 := Real.log_lt_log hk (by linarith)
    have h4 : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  -- lower: log (2 + √3) = log 4 + log ((2 + √3) / 4) ≥ log 4 + 1 - 4 / (2 + √3)
  have ll : (1314 / 1000 : ℝ) < log (2 + √3) := by
    have e : log (2 + √3) = log 4 + log ((2 + √3) / 4) := by
      rw [Real.log_div hk.ne' (by norm_num)]; ring
    have h1 := Real.one_sub_inv_le_log_of_pos (by positivity : 0 < (2 + √3) / 4)
    have h4 : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    have hinv : ((2 + √3) / 4)⁻¹ = 4 / (2 + √3) := by rw [inv_div]
    have hq : 4 / (2 + √3) < 10719 / 10000 := by
      rw [div_lt_iff₀ hk]; nlinarith
    rw [hinv] at h1
    linarith
  have hs2 : 0 < √2 := by positivity
  unfold K93
  constructor <;> nlinarith [mul_lt_mul_of_pos_left ll hs2, mul_lt_mul_of_pos_left lu hs2]

/-- The corrected Theorem 6.1 constant: (97)'s `298.87013 × 3.26599` replaced by
`298.87013 × K93`, keeping Yamada's extra `17.125` between (97) and Theorem 6.1. -/
def C6corr : ℝ := 9932507 / 10000 - 9761256 / 10000 + 29887013 / 100000 * K93

theorem C6corr_le : C6corr ≤ 2200 := by
  have := K93_bounds.2; unfold C6corr; linarith

theorem C6corr_gt : 2100 < C6corr := by
  have := K93_bounds.1; unfold C6corr; linarith

/-- **Yamada Theorem 1.1 with the corrected Theorem 6.1 constant.** CONDITIONAL ON (48),
Theorems 5.1, 7.1, `c₂ < 0.36309`, which C2Bound.lean proves, and Theorem 6.1 with `C6corr`
in place of the printed `993.2507`. -/
theorem yamada_of_section8_corr (h48 : Thm48) (h51 : Thm51) (h61 : Thm61C C6corr)
    (h71 : Thm71) (hc2 : C2Bound) : Yamada :=
  yamada_of_section8_C6 C6corr (C6corr_le.trans (by norm_num)) h48 h51 h61 h71 hc2

end LeanLab.ChenExplicit.Yamada
