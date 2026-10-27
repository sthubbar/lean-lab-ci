/-
P0044, Cai 2002: the constant of (4.4), `12.9897 ≤ 8/θ² (log(5.5θ-1) + ∫₂^{5.5θ-2} log(s-1)/s ·
log((5.5θ-1)/(s+1)) ds)` at θ = 0.95. Proof: with u = s - 1, bound log u below by a degree 16
polynomial from Mathlib's Taylor remainder around 1.6, bound log(4.225/(u+2)) below by a
nonnegative degree 11 polynomial in y = (2.225-u)/4.225, split off 1/(u+1), integrate exactly
and bound log(1.6125), log 1.6 and log 4.225 by series and Mathlib's log 2 bounds.
AI-written Lean code, Claude, run 20261018T2303Z-8776. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Cai2002.Integral414

open Finset Real intervalIntegral Set

namespace LeanLab.Cai2002

lemma log16_ge : 0.4700036 ≤ Real.log 1.6 := by
  have h := negLog_ge (x := 3 / 8) (by norm_num) (by norm_num) 20
  have e : Real.log (1 - 3 / 8) = -Real.log 1.6 := by
    rw [show (1 : ℝ) - 3 / 8 = (1.6)⁻¹ by norm_num, Real.log_inv]
  rw [e, neg_neg] at h
  refine le_trans ?_ h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma log16125_le : Real.log (3.225 / 2) ≤ 477785769707 / 1000000000000 := by
  have h := negLog_le (x := 49 / 129) (by norm_num) (by norm_num) 25
  have e : Real.log (1 - 49 / 129) = -Real.log (3.225 / 2) := by
    rw [show (1 : ℝ) - 49 / 129 = (3.225 / 2)⁻¹ by norm_num, Real.log_inv]
  rw [e, neg_neg] at h
  refine h.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma log4225_ge : 2 * 0.6931471803 + 10944979937 / 200000000000 ≤ Real.log 4.225 := by
  have h := negLog_ge (x := 9 / 169) (by norm_num) (by norm_num) 8
  have e : Real.log (1 - 9 / 169) = -Real.log 1.05625 := by
    rw [show (1 : ℝ) - 9 / 169 = (1.05625)⁻¹ by norm_num, Real.log_inv]
  rw [e, neg_neg] at h
  have e2 : Real.log 4.225 = 2 * Real.log 2 + Real.log 1.05625 := by
    rw [show (4.225 : ℝ) = 2 ^ 2 * 1.05625 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  rw [e2]
  have h2 := Real.log_two_gt_d9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

/-- Lower polynomial for `log u`, `u ∈ [1, 2.225]`, `v = u/1.6 - 1`. -/
noncomputable def Lf (u : ℝ) : ℝ :=
  let v := u / 1.6 - 1
  0.4700036 + (v - v ^ 2 / 2 + v ^ 3 / 3 - v ^ 4 / 4 + v ^ 5 / 5 - v ^ 6 / 6 + v ^ 7 / 7
    - v ^ 8 / 8 + v ^ 9 / 9 - v ^ 10 / 10 + v ^ 11 / 11 - v ^ 12 / 12 + v ^ 13 / 13 - v ^ 14 / 14
    + v ^ 15 / 15) - v ^ 16 / 0.609

/-- Lower polynomial for `log(4.225/(u+2))`, `y = (2.225-u)/4.225`. -/
noncomputable def Lg (u : ℝ) : ℝ :=
  let y := (2.225 - u) / 4.225
  (y + y ^ 2 / 2 + y ^ 3 / 3 + y ^ 4 / 4 + y ^ 5 / 5 + y ^ 6 / 6 + y ^ 7 / 7 + y ^ 8 / 8
    + y ^ 9 / 9 + y ^ 10 / 10) - y ^ 11 / 0.71

lemma log_ge_Lf {u : ℝ} (h1 : 1 ≤ u) (h2 : u ≤ 2.225) : Lf u ≤ Real.log u := by
  set v := u / 1.6 - 1 with hv
  have hvu : v ≤ 0.390625 := by rw [hv]; norm_num; linarith
  have hvl : -0.375 ≤ v := by rw [hv]; norm_num; linarith
  have habs : |v| ≤ 0.390625 := abs_le.mpr ⟨by linarith, hvu⟩
  have hu : u = 1.6 * (1 + v) := by rw [hv]; ring
  have hx : |(-v)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 15
  rw [abs_neg, sub_neg_eq_add] at h
  have hlo := (abs_le.mp h).1
  have hrem : |v| ^ (15 + 1) / (1 - |v|) ≤ v ^ 16 / 0.609 := by
    rw [show |v| ^ (15 + 1) = v ^ 16 by
      rw [pow_abs]; exact abs_of_nonneg (Even.pow_nonneg (by decide) v)]
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have e : ∑ i ∈ Finset.range 15, (-v) ^ (i + 1) / ((i : ℝ) + 1) =
      -(v - v ^ 2 / 2 + v ^ 3 / 3 - v ^ 4 / 4 + v ^ 5 / 5 - v ^ 6 / 6 + v ^ 7 / 7
        - v ^ 8 / 8 + v ^ 9 / 9 - v ^ 10 / 10 + v ^ 11 / 11 - v ^ 12 / 12 + v ^ 13 / 13
        - v ^ 14 / 14 + v ^ 15 / 15) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num; ring
  rw [e] at hlo
  have hc := log16_ge
  have hlog : Real.log u = Real.log 1.6 + Real.log (1 + v) := by
    rw [hu, Real.log_mul (by norm_num) (by linarith)]
  rw [hlog]
  unfold Lf
  simp only [← hv]
  linarith [hlo, hrem, hc]

lemma log_ge_Lg {u : ℝ} (h1 : 1 ≤ u) (h2 : u ≤ 2.225) : Lg u ≤ Real.log (4.225 / (u + 2)) := by
  set y := (2.225 - u) / 4.225 with hy
  have hy0 : 0 ≤ y := by rw [hy]; apply div_nonneg (by linarith) (by norm_num)
  have hy1 : y ≤ 0.29 := by rw [hy]; norm_num; linarith
  have h := negLog_ge hy0 (by linarith) 10
  have e : Real.log (1 - y) = -Real.log (4.225 / (u + 2)) := by
    rw [show 1 - y = (4.225 / (u + 2))⁻¹ by rw [hy]; field_simp; ring, Real.log_inv]
  rw [e, neg_neg] at h
  have hrem : y ^ (10 + 1) / (1 - y) ≤ y ^ 11 / 0.71 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  unfold Lg
  simp only [← hy]
  norm_num at h hrem ⊢
  linarith [h, hrem]

lemma Lg_nonneg {u : ℝ} (h1 : 1 ≤ u) (h2 : u ≤ 2.225) : 0 ≤ Lg u := by
  set y := (2.225 - u) / 4.225 with hy
  have hy0 : 0 ≤ y := by rw [hy]; apply div_nonneg (by linarith) (by norm_num)
  have hy1 : y ≤ 0.29 := by rw [hy]; norm_num; linarith
  unfold Lg
  simp only [← hy]
  have h10 : y ^ 10 ≤ 0.29 ^ 10 := pow_le_pow_left₀ hy0 hy1 10
  have h11 : y ^ 11 ≤ y * 0.29 ^ 10 := by
    rw [pow_succ']; exact mul_le_mul_of_nonneg_left h10 hy0
  have : 0 ≤ y ^ 2 / 2 + y ^ 3 / 3 + y ^ 4 / 4 + y ^ 5 / 5 + y ^ 6 / 6 + y ^ 7 / 7 + y ^ 8 / 8
    + y ^ 9 / 9 + y ^ 10 / 10 := by positivity
  norm_num at h11 this ⊢
  linarith

noncomputable def rC44 (k : ℕ) : ℝ := [(4659385146851493805904214341235291221183015970985628671 : ℝ) / 825385919720447950997202911265122375577265766400000, (-928332701518669105443757045471055855298526830566602547 : ℝ) / 165077183944089590199440582253024475115453153280000, (16620714376692257922755359743915054749751213944662757 : ℝ) / 3001403344437992549080737859145899547553693696000, (-13438380058071422956090593848620684250665591118879347 : ℝ) / 2539648983755224464606778188508068847930048512000, (157549764048241092900478846853821793371230931584817111 : ℝ) / 33015436788817918039888116450604895023090630656000, (-1040013656527873214105318707745575616636145348353507 : ℝ) / 264123494310543344319104931604839160184725045248, (58707056020486146444604996039899084831023195204015 : ℝ) / 20317191870041795716854225508064550783440388096, (-44203852009161565408903871357646338594511757887625 : ℝ) / 24011226755503940392645902873167196380429549568, (9069103151798229389544634733890298744759470962175 : ℝ) / 9107706700363563597210514882925488282231898112, (-117338844956156364670090017744586870372175358959075 : ℝ) / 264123494310543344319104931604839160184725045248, (40739865353174678429947247425405577871742314171875 : ℝ) / 264123494310543344319104931604839160184725045248, (-820512474682066287404761179393927783545166015625 : ℝ) / 24011226755503940392645902873167196380429549568, (-45531620016276705495310232665504578743896484375 : ℝ) / 24011226755503940392645902873167196380429549568, (1824142072675755342460656558365923357257080078125 : ℝ) / 264123494310543344319104931604839160184725045248, (-2840506224673790702965150481704720159912109375 : ℝ) / 634912245938806116151694547127017211982512128, (2139877882714855961576597990704040306549072265625 : ℝ) / 1056493977242173377276419726419356640738900180992, (-6072641865560272136929929579018979644775390625 : ℝ) / 8253859197204479509972029112651223755772657664, (919263800532203245004950266888317108154296875 : ℝ) / 4126929598602239754986014556325611877886328832, (-406545829612540390265848213397979736328125 : ℝ) / 7164808330906666241295164160287520621330432, (23700222994658720387161347194671630859375 : ℝ) / 1954038635701818065807772043714778351271936, (-723328380847820178299551486968994140625 : ℝ) / 335850390511249980060710820013477529124864, (7494616798287380454809665679931640625 : ℝ) / 23989313607946427147193630000962680651776, (-717493228419888055324554443359375 : ℝ) / 19877508908099549009275024858752221184, (290430925264610612392425537109375 : ℝ) / 90868612151312224042400113640010153984, (-33376420584666728973388671875 : ℝ) / 163825622868952326999519435649056768, (10822497308254241943359375 : ℝ) / 1300203356102796246027932028960768, (-23283064365386962890625 : ℝ) / 142209742073743339409305065667584].getD k 0

noncomputable def Rp44 (u : ℝ) : ℝ := ∑ k ∈ range 27, rC44 k * u ^ k

noncomputable def P1_44 : ℝ := (-1660310481871433106960446599400447561014199876319444061 : ℝ) / 293940854601299127848006734781026487028940800000000

lemma split44 (u : ℝ) : Lf u * Lg u = Rp44 u * (u + 1) + P1_44 := by
  simp only [Lf, Lg, Rp44, rC44, P1_44, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

lemma integral_Rp44 : ∫ u in (1 : ℝ)..2.225, Rp44 u =
    ∑ k ∈ range 27, rC44 k * (((2.225 : ℝ) ^ (k + 1) - (1 : ℝ) ^ (k + 1)) / (k + 1)) := by
  unfold Rp44
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul, integral_pow]
    all_goals norm_num
  · intro k _
    exact (continuous_const.mul (continuous_pow k)).intervalIntegrable _ _

lemma F44_cont : ContinuousOn (fun u : ℝ => Real.log u / (u + 1) * Real.log (4.225 / (u + 2)))
    (Icc 1 2.225) := by
  apply ContinuousOn.mul
  · apply ContinuousOn.div (ContinuousOn.log continuousOn_id _) (by fun_prop)
    · intro u hu; have : (1 : ℝ) ≤ u := hu.1; intro h'; linarith
    · intro u hu; simp only [id]; have : (1 : ℝ) ≤ u := hu.1; show u ≠ 0; intro h'; linarith
  · apply ContinuousOn.log (ContinuousOn.div continuousOn_const (by fun_prop) _)
    · intro u hu; have : (1 : ℝ) ≤ u := hu.1; apply ne_of_gt; apply div_pos (by norm_num); linarith
    · intro u hu; have : (1 : ℝ) ≤ u := hu.1; intro h'; linarith

lemma low44_cont : ContinuousOn (fun u : ℝ => Rp44 u + P1_44 * (u + 1)⁻¹) (Icc 1 2.225) := by
  apply ContinuousOn.add
  · apply Continuous.continuousOn; unfold Rp44; fun_prop
  · apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ (by fun_prop)
    intro u hu; have : (1 : ℝ) ≤ u := hu.1; intro h'; linarith

/-- (4.4) at θ = 0.95. The bound reached is 12.989775; the true value is 12.989776. -/
theorem eq44 : Eq44Const := by
  unfold Eq44Const
  simp only
  have e1 : (5.5 : ℝ) * 0.95 - 1 = 4.225 := by norm_num
  have e2 : (5.5 : ℝ) * 0.95 - 2 = 3.225 := by norm_num
  simp only [e1, e2]
  have hcv : ∫ s in (2 : ℝ)..3.225, Real.log (s - 1) / s * Real.log (4.225 / (s + 1)) =
      ∫ u in (1 : ℝ)..2.225, Real.log u / (u + 1) * Real.log (4.225 / (u + 2)) := by
    have := intervalIntegral.integral_comp_add_right
      (fun s : ℝ => Real.log (s - 1) / s * Real.log (4.225 / (s + 1))) (1 : ℝ) (a := 1) (b := 2.225)
    rw [show (1 : ℝ) + 1 = 2 by norm_num, show (2.225 : ℝ) + 1 = 3.225 by norm_num] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro u _
    simp only
    rw [show u + 1 - 1 = u by ring, show u + 1 + 1 = u + 2 by ring]
  rw [hcv]
  have hab : (1 : ℝ) ≤ 2.225 := by norm_num
  have hmono : ∫ u in (1 : ℝ)..2.225, (Rp44 u + P1_44 * (u + 1)⁻¹) ≤
      ∫ u in (1 : ℝ)..2.225, Real.log u / (u + 1) * Real.log (4.225 / (u + 2)) := by
    apply intervalIntegral.integral_mono_on hab (low44_cont.intervalIntegrable_of_Icc hab)
      (F44_cont.intervalIntegrable_of_Icc hab)
    intro u hu
    obtain ⟨h1, h2⟩ := hu
    have hu1 : 0 < u + 1 := by linarith
    have hsp := split44 u
    have hf := log_ge_Lf h1 h2
    have hg := log_ge_Lg h1 h2
    have hg0 := Lg_nonneg h1 h2
    have hl0 : 0 ≤ Real.log u := Real.log_nonneg h1
    have hprod : Lf u * Lg u ≤ Real.log u * Real.log (4.225 / (u + 2)) := by
      nlinarith [mul_nonneg hl0 (sub_nonneg.2 hg), mul_nonneg hg0 (sub_nonneg.2 hf)]
    have : Rp44 u + P1_44 * (u + 1)⁻¹ = Lf u * Lg u / (u + 1) := by
      rw [hsp]; field_simp
    rw [this, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hu1]
    exact hprod
  have hint : ∫ u in (1 : ℝ)..2.225, (Rp44 u + P1_44 * (u + 1)⁻¹) =
      (∫ u in (1 : ℝ)..2.225, Rp44 u) + P1_44 * Real.log (3.225 / 2) := by
    have iR : IntervalIntegrable Rp44 MeasureTheory.volume (1 : ℝ) 2.225 := by
      apply Continuous.intervalIntegrable; unfold Rp44; fun_prop
    have iI : IntervalIntegrable (fun u : ℝ => P1_44 * (u + 1)⁻¹) MeasureTheory.volume (1 : ℝ) 2.225 := by
      apply ContinuousOn.intervalIntegrable_of_Icc hab
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.inv₀ (by fun_prop)
      intro u hu; have : (1 : ℝ) ≤ u := hu.1; intro h'; linarith
    rw [intervalIntegral.integral_add iR iI, intervalIntegral.integral_const_mul]
    congr 2
    rw [intervalIntegral.integral_comp_add_right (fun x : ℝ => x⁻¹) (1 : ℝ),
      integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  rw [hint, integral_Rp44] at hmono
  have hP1 : P1_44 < 0 := by unfold P1_44; norm_num
  have hl := mul_le_mul_of_nonpos_left log16125_le hP1.le
  have h4 := log4225_ge
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, rC44] at hmono
  unfold P1_44 at hmono hl
  norm_num at hmono hl h4 ⊢
  nlinarith [hmono, hl, h4]

end LeanLab.Cai2002
