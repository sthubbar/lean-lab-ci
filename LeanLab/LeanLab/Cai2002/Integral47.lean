/-
P0044, Cai 2002: the constant of (4.7), `8/θ² (log((11θ-2)/(3.29θ-2)) + ∫₂^{5.5θ-2} log(s-1)/s ·
log((5.5θ-1)(5.5θ-1-s)/(s+1)) ds) ≤ 18.7347` at θ = 0.95. Proof as for (4.4) in Integral44.lean,
with upper polynomials: log u ≤ Uf u, and log(4.225(3.225-u)/(u+2)) ≤ log 4.225 + Uf(3.225-u)
- Lh(u+2), which is valid since that log is nonnegative on [1, 2.225].
AI-written Lean code, Claude, run 20261018T2303Z-8776. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Cai2002.Integral44

open Finset Real intervalIntegral Set

namespace LeanLab.Cai2002

lemma log16_le : Real.log 1.6 ≤ 470003630977 / 1000000000000 := by
  have h := negLog_le (x := 3 / 8) (by norm_num) (by norm_num) 20
  have e : Real.log (1 - 3 / 8) = -Real.log 1.6 := by
    rw [show (1 : ℝ) - 3 / 8 = (1.6)⁻¹ by norm_num, Real.log_inv]
  rw [e, neg_neg] at h
  refine h.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma log36_ge : 0.6931471803 + 587786664879 / 1000000000000 ≤ Real.log 3.6 := by
  have h := negLog_ge (x := 4 / 9) (by norm_num) (by norm_num) 30
  have e : Real.log (1 - 4 / 9) = -Real.log 1.8 := by
    rw [show (1 : ℝ) - 4 / 9 = (1.8)⁻¹ by norm_num, Real.log_inv]
  rw [e, neg_neg] at h
  have e2 : Real.log 3.6 = Real.log 2 + Real.log 1.8 := by
    rw [show (3.6 : ℝ) = 2 * 1.8 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [e2]
  have h2 := Real.log_two_gt_d9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

lemma log4225_le : Real.log 4.225 ≤ 2 * 0.6931471808 + 54724899693 / 1000000000000 := by
  have h := negLog_le (x := 9 / 169) (by norm_num) (by norm_num) 8
  have e : Real.log (1 - 9 / 169) = -Real.log 1.05625 := by
    rw [show (1 : ℝ) - 9 / 169 = (1.05625)⁻¹ by norm_num, Real.log_inv]
  rw [e, neg_neg] at h
  have e2 : Real.log 4.225 = 2 * Real.log 2 + Real.log 1.05625 := by
    rw [show (4.225 : ℝ) = 2 ^ 2 * 1.05625 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  rw [e2]
  have h2 := Real.log_two_lt_d9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

lemma log16125_le45 : Real.log (3.225 / 2) ≤ 477785769687790503 / 1000000000000000000 := by
  have h := negLog_le (x := 49 / 129) (by norm_num) (by norm_num) 45
  have e : Real.log (1 - 49 / 129) = -Real.log (3.225 / 2) := by
    rw [show (1 : ℝ) - 49 / 129 = (3.225 / 2)⁻¹ by norm_num, Real.log_inv]
  rw [e, neg_neg] at h
  refine h.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma logT1_le : Real.log (16900 / 2251) ≤ 3 * 0.6931471808 - 2540099267 / 40000000000 := by
  have h := negLog_ge (x := 277 / 4502) (by norm_num) (by norm_num) 10
  have e2 : Real.log (16900 / 2251) = 3 * Real.log 2 + Real.log (1 - 277 / 4502) := by
    rw [show (16900 : ℝ) / 2251 = 2 ^ 3 * (1 - 277 / 4502) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [e2]
  have h2 := Real.log_two_lt_d9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith

/-- Upper polynomial for `log w`, `w ∈ [1, 2.225]`, `v = w/1.6 - 1`. -/
noncomputable def Uf (w : ℝ) : ℝ :=
  let v := w / 1.6 - 1
  470003630977 / 1000000000000 + (v - v ^ 2 / 2 + v ^ 3 / 3 - v ^ 4 / 4 + v ^ 5 / 5 - v ^ 6 / 6
    + v ^ 7 / 7 - v ^ 8 / 8 + v ^ 9 / 9 - v ^ 10 / 10 + v ^ 11 / 11 - v ^ 12 / 12 + v ^ 13 / 13
    - v ^ 14 / 14 + v ^ 15 / 15) + v ^ 16 / 0.609

/-- Lower polynomial for `log x`, `x ∈ [3, 4.225]`, `v = x/3.6 - 1`. -/
noncomputable def Lh (x : ℝ) : ℝ :=
  let v := x / 3.6 - 1
  (0.6931471803 + 587786664879 / 1000000000000) + (v - v ^ 2 / 2 + v ^ 3 / 3 - v ^ 4 / 4
    + v ^ 5 / 5 - v ^ 6 / 6 + v ^ 7 / 7 - v ^ 8 / 8 + v ^ 9 / 9 - v ^ 10 / 10 + v ^ 11 / 11)
    - v ^ 12 / 0.826

lemma log_le_Uf {w : ℝ} (h1 : 1 ≤ w) (h2 : w ≤ 2.225) : Real.log w ≤ Uf w := by
  set v := w / 1.6 - 1 with hv
  have hvu : v ≤ 0.390625 := by rw [hv]; norm_num; linarith
  have hvl : -0.375 ≤ v := by rw [hv]; norm_num; linarith
  have habs : |v| ≤ 0.390625 := abs_le.mpr ⟨by linarith, hvu⟩
  have hw : w = 1.6 * (1 + v) := by rw [hv]; ring
  have hx : |(-v)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 15
  rw [abs_neg, sub_neg_eq_add] at h
  have hup := (abs_le.mp h).2
  have hrem : |v| ^ (15 + 1) / (1 - |v|) ≤ v ^ 16 / 0.609 := by
    rw [show |v| ^ (15 + 1) = v ^ 16 by
      rw [pow_abs]; exact abs_of_nonneg (Even.pow_nonneg (by decide) v)]
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have e : ∑ i ∈ Finset.range 15, (-v) ^ (i + 1) / ((i : ℝ) + 1) =
      -(v - v ^ 2 / 2 + v ^ 3 / 3 - v ^ 4 / 4 + v ^ 5 / 5 - v ^ 6 / 6 + v ^ 7 / 7
        - v ^ 8 / 8 + v ^ 9 / 9 - v ^ 10 / 10 + v ^ 11 / 11 - v ^ 12 / 12 + v ^ 13 / 13
        - v ^ 14 / 14 + v ^ 15 / 15) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num; ring
  rw [e] at hup
  have hc := log16_le
  have hlog : Real.log w = Real.log 1.6 + Real.log (1 + v) := by
    rw [hw, Real.log_mul (by norm_num) (by linarith)]
  rw [hlog]
  unfold Uf
  simp only [← hv]
  linarith [hup, hrem, hc]

lemma Lh_le_log {x : ℝ} (h1 : 3 ≤ x) (h2 : x ≤ 4.225) : Lh x ≤ Real.log x := by
  set v := x / 3.6 - 1 with hv
  have hvu : v ≤ 0.1737 := by rw [hv]; norm_num; linarith
  have hvl : -0.1737 ≤ v := by rw [hv]; norm_num; linarith
  have habs : |v| ≤ 0.1737 := abs_le.mpr ⟨hvl, hvu⟩
  have hxv : x = 3.6 * (1 + v) := by rw [hv]; ring
  have hx : |(-v)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 11
  rw [abs_neg, sub_neg_eq_add] at h
  have hlo := (abs_le.mp h).1
  have hrem : |v| ^ (11 + 1) / (1 - |v|) ≤ v ^ 12 / 0.826 := by
    rw [show |v| ^ (11 + 1) = v ^ 12 by
      rw [pow_abs]; exact abs_of_nonneg (Even.pow_nonneg (by decide) v)]
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have e : ∑ i ∈ Finset.range 11, (-v) ^ (i + 1) / ((i : ℝ) + 1) =
      -(v - v ^ 2 / 2 + v ^ 3 / 3 - v ^ 4 / 4 + v ^ 5 / 5 - v ^ 6 / 6 + v ^ 7 / 7
        - v ^ 8 / 8 + v ^ 9 / 9 - v ^ 10 / 10 + v ^ 11 / 11) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num; ring
  rw [e] at hlo
  have hc := log36_ge
  have hlog : Real.log x = Real.log 3.6 + Real.log (1 + v) := by
    rw [hxv, Real.log_mul (by norm_num) (by linarith)]
  rw [hlog]
  unfold Lh
  simp only [← hv]
  linarith [hlo, hrem, hc]

/-- Upper polynomial for `log(4.225 (3.225-u)/(u+2))` on `[1, 2.225]`. -/
noncomputable def Ug (u : ℝ) : ℝ :=
  (2 * 0.6931471808 + 54724899693 / 1000000000000) + Uf (3.225 - u) - Lh (u + 2)

lemma g47_le {u : ℝ} (h1 : 1 ≤ u) (h2 : u ≤ 2.225) :
    Real.log (4.225 * (3.225 - u) / (u + 2)) ≤ Ug u := by
  rw [Real.log_div (by nlinarith) (by linarith), Real.log_mul (by norm_num) (by linarith)]
  have a1 := log4225_le
  have a2 := log_le_Uf (w := 3.225 - u) (by linarith) (by linarith)
  have a3 := Lh_le_log (x := u + 2) (by linarith) (by linarith)
  unfold Ug
  linarith

lemma g47_nonneg {u : ℝ} (h1 : 1 ≤ u) (h2 : u ≤ 2.225) :
    0 ≤ Real.log (4.225 * (3.225 - u) / (u + 2)) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ (by linarith)]
  nlinarith

noncomputable def rC47 (k : ℕ) : ℝ := [(-47018152726240711345923493867955441621275016195594999617390551154634544482753 : ℝ) / 2851720046528953939374712484897965156360986606362200060723200000000000, (272705249552173218240793665626463258367929019879654965630204931182932401856249 : ℝ) / 16539976269867932848373332412408197906893722316900760352194560000000000, (-54540168747940518308835726036423281352976672945765887271798271532408273320293 : ℝ) / 3307995253973586569674666482481639581378744463380152070438912000000000, (3635493193312419596716287762952075105306397477557486913926658993370772044619 : ℝ) / 220533016931572437978311098832109305425249630892010138029260800000000, (-3632725657135816281109316208953457968653069810123945835341702612839541013323 : ℝ) / 220533016931572437978311098832109305425249630892010138029260800000000, (20697446555194454006180906347617657473152725526212277707836355761028349477 : ℝ) / 1260188668180413931304634850469196031001426462240057931595776000000, (-586145322510349361423383443399772033130195103074007247106374623758846231 : ℝ) / 36005390519440398037275281441977029457183613206858798045593600000, (5620872203469846914162382109991588678553172383083137333153572435337527163 : ℝ) / 352852827090515900765297758131374888680399409427216220846817280000, (-214942496380503756172754078081158871382597983683483673622162231589002931 : ℝ) / 14114113083620636030611910325254995547215976377088648833872691200, (2972551275424255012159193611817546691032520795678325405269643324228177021 : ℝ) / 211711696254309540459178654878824933208239645656329732508090368000, (-104275385669288850236480452740095769471553821198048708448008639434329093 : ℝ) / 8468467850172381618367146195152997328329585826253189300323614720, (17173495836663213497961961366642355080548800505059159428980181971788801 : ℝ) / 1693693570034476323673429239030599465665917165250637860064722944, (-1010118595781932832426445192499285932611994525965219090693864750752645 : ℝ) / 130284120771882794128725326079276881974301320403895220004978688, (120106224405381678248294311950786380433675580534189004514494921408529325 : ℝ) / 22018016410448192207754580107397793053656923148258292180841398272, (-77186908204272100102857109823192137080835564784234136911501125597099675 : ℝ) / 22018016410448192207754580107397793053656923148258292180841398272, (90082045607232650726370648197932831576452937143126284623126387928046875 : ℝ) / 44036032820896384415509160214795586107313846296516584361682796544, (-742013200655770120653457618298972911506864752839315170343170166015625 : ℝ) / 688063012826506006492330628356181032926778848383071630651293696, (21985533422114285120329825021828672255410197694780995549774169921875 : ℝ) / 43003938301656625405770664272261314557923678023941976915705856, (-2332691515850418136401449873347638804750212419074091510772705078125 : ℝ) / 10750984575414156351442666068065328639480919505985494228926464, (220522895851111506506964748208297834074334659904915248870849609375 : ℝ) / 2687746143853539087860666517016332159870229876496373557231616, (-4619262512374154544164669564336203780736977222488880157470703125 : ℝ) / 167984133990846192991291657313520759991889367281023347326976, (7102756856157737182189495162576987506906799796581268310546875 : ℝ) / 874917364535657255162977381841253958291090454588663267328, (-166689520167377530959000428530338355007008240222930908203125 : ℝ) / 79537942230514295923907034712841268935553677689878478848, (18643881893761613448018417492901826516199028491973876953125 : ℝ) / 39768971115257147961953517356420634467776838844939239424, (-111653799197211357452192124064691355867660045623779296875 : ℝ) / 1242780347351785873811047417388144827118026213904351232, (38928934702858162189772819010508199632167816162109375 : ℝ) / 2678405921016779900454843571957208679133677185138688, (-7711726073574332916363813031940162181854248046875 : ℝ) / 3962138936415354882329650254374569051972895244288, (7127931179271117914093800626166164875030517578125 : ℝ) / 33948326796104290696324503315891193922585943343104, (-515182465601153671741485595703125 : ℝ) / 29384220141452871791031173844566016, (976467298604547977447509765625 : ℝ) / 918256879420402243469724182642688, (-19135768525302410125732421875 : ℝ) / 459128439710201121734862091321344, (363797880709171295166015625 : ℝ) / 459128439710201121734862091321344].getD k 0

noncomputable def Rp47 (u : ℝ) : ℝ := ∑ k ∈ range 32, rC47 k * u ^ k

noncomputable def P1_47 : ℝ := (1664460478088438229899035431099653393958260765956524414247750023357107370398866582890913 : ℝ) / 100952003600268144826497390212452379802818129375614992384000000000000000000000000

lemma split47 (u : ℝ) : Uf u * Ug u = Rp47 u * (u + 1) + P1_47 := by
  simp only [Uf, Ug, Lh, Rp47, rC47, P1_47, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

lemma integral_Rp47 : ∫ u in (1 : ℝ)..2.225, Rp47 u =
    ∑ k ∈ range 32, rC47 k * (((2.225 : ℝ) ^ (k + 1) - (1 : ℝ) ^ (k + 1)) / (k + 1)) := by
  unfold Rp47
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul, integral_pow]
    all_goals norm_num
  · intro k _
    exact (continuous_const.mul (continuous_pow k)).intervalIntegrable _ _

lemma F47_cont : ContinuousOn
    (fun u : ℝ => Real.log u / (u + 1) * Real.log (4.225 * (3.225 - u) / (u + 2))) (Icc 1 2.225) := by
  apply ContinuousOn.mul
  · apply ContinuousOn.div (ContinuousOn.log continuousOn_id _) (by fun_prop)
    · intro u hu; have : (1 : ℝ) ≤ u := hu.1; intro h'; linarith
    · intro u hu; simp only [id]; have : (1 : ℝ) ≤ u := hu.1; show u ≠ 0; intro h'; linarith
  · apply ContinuousOn.log (ContinuousOn.div (by fun_prop) (by fun_prop) _)
    · intro u hu; have h1 : (1 : ℝ) ≤ u := hu.1; have h2 : u ≤ (2.225 : ℝ) := hu.2
      apply ne_of_gt; apply div_pos (by nlinarith) (by linarith)
    · intro u hu; have : (1 : ℝ) ≤ u := hu.1; intro h'; linarith

lemma up47_cont : ContinuousOn (fun u : ℝ => Rp47 u + P1_47 * (u + 1)⁻¹) (Icc 1 2.225) := by
  apply ContinuousOn.add
  · apply Continuous.continuousOn; unfold Rp47; fun_prop
  · apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ (by fun_prop)
    intro u hu; have : (1 : ℝ) ≤ u := hu.1; intro h'; linarith

/-- (4.7) at θ = 0.95. The bound reached is 18.734615; the true value is 18.734614. -/
theorem eq47 : Eq47Const := by
  unfold Eq47Const
  simp only
  have e1 : (5.5 : ℝ) * 0.95 - 1 = 4.225 := by norm_num
  have e2 : (5.5 : ℝ) * 0.95 - 2 = 3.225 := by norm_num
  have e3 : ((11 : ℝ) * 0.95 - 2) / (3.29 * 0.95 - 2) = 16900 / 2251 := by norm_num
  simp only [e1, e2, e3]
  have hcv : ∫ s in (2 : ℝ)..3.225, Real.log (s - 1) / s * Real.log (4.225 * (4.225 - s) / (s + 1)) =
      ∫ u in (1 : ℝ)..2.225, Real.log u / (u + 1) * Real.log (4.225 * (3.225 - u) / (u + 2)) := by
    have := intervalIntegral.integral_comp_add_right
      (fun s : ℝ => Real.log (s - 1) / s * Real.log (4.225 * (4.225 - s) / (s + 1))) (1 : ℝ)
      (a := 1) (b := 2.225)
    rw [show (1 : ℝ) + 1 = 2 by norm_num, show (2.225 : ℝ) + 1 = 3.225 by norm_num] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro u _
    simp only
    rw [show u + 1 - 1 = u by ring, show u + 1 + 1 = u + 2 by ring,
      show (4.225 : ℝ) - (u + 1) = 3.225 - u by ring]
  rw [hcv]
  have hab : (1 : ℝ) ≤ 2.225 := by norm_num
  have hmono : ∫ u in (1 : ℝ)..2.225, Real.log u / (u + 1) * Real.log (4.225 * (3.225 - u) / (u + 2))
      ≤ ∫ u in (1 : ℝ)..2.225, (Rp47 u + P1_47 * (u + 1)⁻¹) := by
    apply intervalIntegral.integral_mono_on hab (F47_cont.intervalIntegrable_of_Icc hab)
      (up47_cont.intervalIntegrable_of_Icc hab)
    intro u hu
    obtain ⟨h1, h2⟩ := hu
    have hu1 : 0 < u + 1 := by linarith
    have hsp := split47 u
    have hf := log_le_Uf h1 h2
    have hg := g47_le h1 h2
    have hg0 := g47_nonneg h1 h2
    have hl0 : 0 ≤ Real.log u := Real.log_nonneg h1
    have hprod : Real.log u * Real.log (4.225 * (3.225 - u) / (u + 2)) ≤ Uf u * Ug u := by
      nlinarith [mul_nonneg (hl0.trans hf) (sub_nonneg.2 hg), mul_nonneg hg0 (sub_nonneg.2 hf)]
    have : Rp47 u + P1_47 * (u + 1)⁻¹ = Uf u * Ug u / (u + 1) := by
      rw [hsp]; field_simp
    rw [this, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hu1]
    exact hprod
  have hint : ∫ u in (1 : ℝ)..2.225, (Rp47 u + P1_47 * (u + 1)⁻¹) =
      (∫ u in (1 : ℝ)..2.225, Rp47 u) + P1_47 * Real.log (3.225 / 2) := by
    have iR : IntervalIntegrable Rp47 MeasureTheory.volume (1 : ℝ) 2.225 := by
      apply Continuous.intervalIntegrable; unfold Rp47; fun_prop
    have iI : IntervalIntegrable (fun u : ℝ => P1_47 * (u + 1)⁻¹) MeasureTheory.volume (1 : ℝ) 2.225 := by
      apply ContinuousOn.intervalIntegrable_of_Icc hab
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.inv₀ (by fun_prop)
      intro u hu; have : (1 : ℝ) ≤ u := hu.1; intro h'; linarith
    rw [intervalIntegral.integral_add iR iI, intervalIntegral.integral_const_mul]
    congr 2
    rw [intervalIntegral.integral_comp_add_right (fun x : ℝ => x⁻¹) (1 : ℝ),
      integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  rw [hint, integral_Rp47] at hmono
  have hP1 : 0 < P1_47 := by unfold P1_47; norm_num
  have hl := mul_le_mul_of_nonneg_left log16125_le45 hP1.le
  have h4 := logT1_le
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, rC47] at hmono
  unfold P1_47 at hmono hl
  norm_num at hmono hl h4 ⊢
  nlinarith [hmono, hl, h4]

end LeanLab.Cai2002
