import Mathlib

/-!
Lower bound for the leaf integral behind index 0 of the Wu 2004 Section 10 display,
Wu 2004 arXiv 0705.1652, page 38 equations 10.2 and 10.3 and page 42.
The leaf statement is `leaf_explicit0` in `Feed1122_Decomp275b_values_explicit.lean`.

Method: with w = s/2 - 2, log of s - 2 is log 2 plus log of 1 + w, bounded below by a Taylor
partial sum minus 2 w^22. The reciprocals of s - 1 and of t are bounded below by even length
alternating geometric sums, which are nonnegative. All minorants are polynomials, integrated
exactly. log 3 is bounded below through log 2 plus log of 3/2. A python check with exact
fractions gives 13.47361349.., above 13.473613.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ChenDoubleSieve.Feed1122Explicit0

open Real Finset MeasureTheory intervalIntegral

theorem log_one_add_ge (w : ℝ) (h0 : -1/2 ≤ w) (h1 : w ≤ 1/2) :
    -(∑ i ∈ range 21, (-w) ^ (i + 1) / ((i : ℝ) + 1)) - 2 * w ^ 22 ≤ log (1 + w) := by
  have hx : |-w| < 1 := by rw [abs_lt]; constructor <;> linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 21
  have ha : |-w| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith
  have hp : |-w| ^ (21 + 1) = w ^ 22 := by
    rw [abs_neg, pow_abs]; exact abs_of_nonneg (Even.pow_nonneg ⟨11, rfl⟩ w)
  rw [hp] at h
  have hw0 : 0 ≤ w ^ 22 := Even.pow_nonneg ⟨11, rfl⟩ w
  have hr : w ^ 22 / (1 - |-w|) ≤ 2 * w ^ 22 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have := (abs_le.mp h).1
  rw [show (1 - -w) = 1 + w by ring] at this
  linarith

theorem log_three_ge : 6931471803 / 10000000000 +
    (-(∑ i ∈ range 40, (-(1/2:ℝ)) ^ (i + 1) / ((i : ℝ) + 1)) - 2 * (1/2:ℝ) ^ 41) ≤ log 3 := by
  have hx : |-(1/2:ℝ)| < 1 := by norm_num [abs_of_pos]
  have h := Real.abs_log_sub_add_sum_range_le hx 40
  have hab : |-(1/2:ℝ)| = 1/2 := by norm_num [abs_of_pos]
  rw [hab] at h
  have := (abs_le.mp h).1
  rw [show (1 - -(1/2:ℝ)) = 3/2 by norm_num] at this
  have e : log 3 = log 2 + log (3/2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_gt_d9
  have : (1/2:ℝ) ^ (40 + 1) / (1 - 1/2) = 2 * (1/2:ℝ) ^ 41 := by norm_num
  linarith

/-- Even length alternating geometric lower bound for 1/(1 + y), and its nonnegativity. -/
theorem inv_one_add_ge (y : ℝ) (k : ℕ) (hk : Even k) (hy : -1 < y) (hy1 : y < 1) :
    0 ≤ ∑ j ∈ range k, (-y) ^ j ∧ ∑ j ∈ range k, (-y) ^ j ≤ 1 / (1 + y) := by
  have hpos : 0 < 1 + y := by linarith
  have hne : (-y) ≠ 1 := by intro h; linarith
  have hg := geom_sum_eq hne k
  rw [hg]
  have hyk : (-y) ^ k = y ^ k := Even.neg_pow hk y
  rw [hyk]
  have hy0 : 0 ≤ y ^ k := Even.pow_nonneg hk y
  have e1 : (y ^ k - 1) / (-y - 1) = (1 - y ^ k) / (1 + y) := by
    rw [show (-y - 1) = -(1 + y) by ring, div_neg, ← neg_div]; ring_nf
  rw [e1]
  have hyk1 : y ^ k ≤ 1 := by
    rw [← Even.pow_abs hk]
    exact pow_le_one₀ (abs_nonneg _) (by rw [abs_le]; constructor <;> linarith)
  constructor
  · exact div_nonneg (by linarith) hpos.le
  · exact div_le_div_of_nonneg_right (by linarith) hpos.le

noncomputable def Nf (s : ℝ) : ℝ :=
  6931471803 / 10000000000 - (∑ i ∈ range 21, (-(s / 2 - 2)) ^ (i + 1) / ((i : ℝ) + 1)) -
    2 * (s / 2 - 2) ^ 22

noncomputable def Gf (s : ℝ) : ℝ :=
  1 / 3 * (∑ j ∈ range 14, (-(2 / 3 * (s / 2 - 2))) ^ j)

noncomputable def Rf (t : ℝ) : ℝ :=
  1 / 4 * (∑ j ∈ range 14, (-((t - 4) / 4)) ^ j)

theorem f_ge (s : ℝ) (h0 : 3 ≤ s) (h1 : s ≤ 5) :
    Nf s * Gf s ≤ log (s - 2) / (s - 1) := by
  have hl : Nf s ≤ log (s - 2) := by
    have e : s - 2 = 2 * (1 + (s / 2 - 2)) := by ring
    rw [e, Real.log_mul (by norm_num) (by linarith)]
    have := log_one_add_ge (s / 2 - 2) (by linarith) (by linarith)
    have := Real.log_two_gt_d9
    unfold Nf; linarith
  have hg : 0 ≤ Gf s ∧ Gf s ≤ 1 / (s - 1) := by
    have e : 1 / (s - 1) = 1 / 3 * (1 / (1 + 2 / 3 * (s / 2 - 2))) := by
      field_simp; ring
    rw [e]; unfold Gf
    obtain ⟨a, b⟩ := inv_one_add_ge (2 / 3 * (s / 2 - 2)) 14 ⟨7, rfl⟩ (by linarith) (by linarith)
    exact ⟨by positivity, mul_le_mul_of_nonneg_left b (by norm_num)⟩
  have hl0 : 0 ≤ log (s - 2) := Real.log_nonneg (by linarith)
  rw [div_eq_mul_one_div]
  calc Nf s * Gf s ≤ log (s - 2) * Gf s := mul_le_mul_of_nonneg_right hl hg.1
    _ ≤ _ := mul_le_mul_of_nonneg_left hg.2 hl0

theorem w_ge (t : ℝ) (h0 : 3 ≤ t) (h1 : t ≤ 5) : 0 ≤ Rf t ∧ Rf t ≤ 1 / t := by
  have e : 1 / t = 1 / 4 * (1 / (1 + (t - 4) / 4)) := by
    have ht : t ≠ 0 := by intro h; linarith
    rw [show (1:ℝ) + (t - 4) / 4 = t / 4 by ring]
    field_simp
  rw [e]; unfold Rf
  obtain ⟨a, b⟩ := inv_one_add_ge ((t - 4) / 4) 14 ⟨7, rfl⟩ (by linarith) (by linarith)
  exact ⟨by positivity, mul_le_mul_of_nonneg_left b (by norm_num)⟩

/-- A univariate polynomial as a coefficient list. -/
noncomputable def evalL (L : List (ℕ × ℝ)) (x : ℝ) : ℝ := (L.map fun e => e.2 * x ^ e.1).sum

noncomputable def primL (L : List (ℕ × ℝ)) (a x : ℝ) : ℝ :=
  (L.map fun e => e.2 * ((x ^ (e.1 + 1) - a ^ (e.1 + 1)) / ((e.1 : ℝ) + 1))).sum

theorem evalL_cont (L : List (ℕ × ℝ)) : Continuous fun x => evalL L x := by
  induction L with
  | nil => simp only [evalL, List.map_nil, List.sum_nil]; exact continuous_const
  | cons e L ih =>
    simp only [evalL, List.map_cons, List.sum_cons] at ih ⊢
    exact (by fun_prop : Continuous fun x : ℝ => e.2 * x ^ e.1).add ih

theorem integral_evalL (L : List (ℕ × ℝ)) (a b : ℝ) :
    ∫ x in a..b, evalL L x = primL L a b := by
  induction L with
  | nil => simp [evalL, primL]
  | cons e L ih =>
    simp only [evalL, primL, List.map_cons, List.sum_cons] at ih ⊢
    rw [intervalIntegral.integral_add, ih]
    · congr 1
      rw [intervalIntegral.integral_const_mul, integral_pow]
    · exact (by fun_prop : Continuous fun x : ℝ => e.2 * x ^ e.1).intervalIntegrable _ _
    · exact (evalL_cont L).intervalIntegrable _ _

noncomputable def pc : List (ℕ × ℝ) :=
  [(0, (-9425228824765048021275156518239 / 19882849962690000000000 : ℝ)),
  (1, (75877571054795336701322023335073 / 19882849962690000000000 : ℝ)),
  (2, (-99486023390866090251705506308853 / 6627616654230000000000 : ℝ)),
  (3, (763676337864586333656917023335073 / 19882849962690000000000 : ℝ)),
  (4, (-1427927749227013687934986115094799 / 19882849962690000000000 : ℝ)),
  (5, (230896381356732350804775753582793 / 2209205551410000000000 : ℝ)),
  (6, (-816070561740111878732382984231613 / 6627616654230000000000 : ℝ)),
  (7, (5595349398729352972065311553463693 / 46393316579610000000000 : ℝ)),
  (8, (-3096229049188913674239986724612119 / 30928877719740000000000 : ℝ)),
  (9, (19880083086350966441643198623755613 / 278359899477660000000000 : ℝ)),
  (10, (-616108494807180767587806192913483 / 13917994973883000000000 : ℝ)),
  (11, (2230388698721099389195978916135311 / 92786633159220000000000 : ℝ)),
  (12, (-5126268970387820274304467291538379 / 445375839164256000000000 : ℝ)),
  (13, (10877019393110316739972640466347239 / 2226879195821280000000000 : ℝ)),
  (14, (-206657797025999078902717 / 112060754657280 : ℝ)),
  (15, (435137789115414119861 / 700379716608 : ℝ)),
  (16, (-14913691296774873708641 / 79687647756288 : ℝ)),
  (17, (615388633219932481385407 / 12192210106712064 : ℝ)),
  (18, (-1338123060641378136701339 / 109729890960408576 : ℝ)),
  (19, (5502345778375846607076797 / 2084867928247762944 : ℝ)),
  (20, (-7105834717153134617806733 / 13899119521651752960 : ℝ)),
  (21, (25835121304323251192068873 / 291881509954686812160 : ℝ)),
  (22, (-3988674288455332536824233 / 291881509954686812160 : ℝ)),
  (23, (614416811268733930453 / 327588675594485760 : ℝ)),
  (24, (-22174194675532085501411 / 97293836651562270720 : ℝ)),
  (25, (215728400430488856439 / 8844894241051115520 : ℝ)),
  (26, (-6731853123815878787 / 2948298080350371840 : ℝ)),
  (27, (378390024913864889 / 2041129440242565120 : ℝ)),
  (28, (-26350458291804551 / 2041129440242565120 : ℝ)),
  (29, (517080633414643 / 680376480080855040 : ℝ)),
  (30, (-15142308134575 / 408225888048513024 : ℝ)),
  (31, (175397236837 / 120066437661327360 : ℝ)),
  (32, (-119030591 / 2668143059140608 : ℝ)),
  (33, (2088181 / 2106428730900480 : ℝ)),
  (34, (-751 / 52660718272512 : ℝ)),
  (35, (1 / 10030613004288 : ℝ))]

noncomputable def qc : List (ℕ × ℝ) :=
  [(0, (1576593968231951063965087330485115320227641 / 3908688674504653386547200000000000 : ℝ)),
  (1, (-28674530263691533799428327127878431389910443 / 7216040629854744713625600000000000 : ℝ)),
  (2, (140023299591575815088871415518587530103489963 / 7216040629854744713625600000000000 : ℝ)),
  (3, (-656768827230016416431054237805481460385842603 / 10496059097970537765273600000000000 : ℝ)),
  (4, (165471713414948784985268954234932615891420937 / 1104848326102161870028800000000000 : ℝ)),
  (5, (-1442960415599393001626031391875132754216580321 / 5088998350531169825587200000000000 : ℝ)),
  (6, (5092401256028409618513557733761007687036610043 / 11525084499732355193241600000000000 : ℝ)),
  (7, (-521561632336882418462708018631122574252704400811 / 895663709693485889303347200000000000 : ℝ)),
  (8, (3556594399462676554577061372735512002900354008491 / 5373982258160915335820083200000000000 : ℝ)),
  (9, (-435331794562435054085225381475766114789177641707 / 661413201004420349024010240000000000 : ℝ)),
  (10, (273934431024937664411581430138993964129704365262251 / 472910438718160549552167321600000000000 : ℝ)),
  (11, (-264906804090665536974981206150863568265299790952087 / 582043616883889907141129011200000000000 : ℝ)),
  (12, (63255900540519706246898748882502992949577633554105771 / 196730742506754788613701605785600000000000 : ℝ)),
  (13, (-2263036473428717791184883635341796344436568387931997611 / 11016921580378268162367289923993600000000000 : ℝ)),
  (14, (1237363123504669671257722328267567082002201 / 10378009242833308876800000000000 : ℝ)),
  (15, (-3930332343624471050123300492172421200693001 / 62268055456999853260800000000000 : ℝ)),
  (16, (16700289492833710730976118523507433616139 / 546211012780700467200000000000 : ℝ)),
  (17, (-461483413322072075089779916896456898901801 / 33964393885636283596800000000000 : ℝ)),
  (18, (518532092685114013904245155392961346984309 / 93402083185499779891200000000000 : ℝ)),
  (19, (-390289619338259540595270965023636636523909 / 186804166370999559782400000000000 : ℝ)),
  (20, (29637127512082717785042374362287360647629 / 40863411393656153702400000000000 : ℝ)),
  (21, (-1910960030597741386324747083410186244895841 / 8219383320323980630425600000000000 : ℝ)),
  (22, (141540066214126212747475258130145884396149 / 2054845830080995157606400000000000 : ℝ)),
  (23, (-25852667339947438606703506436669867192701 / 1369897220053996771737600000000000 : ℝ)),
  (24, (10238015952414737466069203378872145923 / 2140464406334369955840000000000 : ℝ)),
  (25, (-726287141362529955730208614555976121889 / 647587776752798473912320000000000 : ℝ)),
  (26, (945163735970700766157904300169623685823 / 3885526660516790843473920000000000 : ℝ)),
  (27, (-47107649886235731147997169763030190709 / 965633844625474647490560000000000 : ℝ)),
  (28, (31926418910582661437048122952767 / 3531460917487450139394048000 : ℝ)),
  (29, (-1029629176736278827073204895022241 / 665680382946384351275778048000 : ℝ)),
  (30, (5198033672339457509756854229518147 / 21301772254284299240824897536000 : ℝ)),
  (31, (-46814828218677583805952057715148479 / 1320709879765626552931143647232000 : ℝ)),
  (32, (11458624862211954169092040355684399 / 2421301446236982013707096686592000 : ℝ)),
  (33, (-431677878710340422059897793712607 / 745015829611379081140645134336000 : ℝ)),
  (34, (4399237761210509767673115045412319 / 67796440494635496383798707224576000 : ℝ)),
  (35, (-20265920782856938343515130800703 / 3058486037351977280472122130432000 : ℝ)),
  (36, (811826754114787925215054161533 / 1320709879765626552931143647232000 : ℝ)),
  (37, (-1089872145825304934738511609853 / 21131358076250024846898298355712000 : ℝ)),
  (38, (133700950354957789711554634193 / 34338456873906290376209734828032000 : ℝ)),
  (39, (-328151256663563208836816249 / 1248671159051137831862172175564800 : ℝ)),
  (40, (755790745555836739146239 / 48025813809659147379314314444800 : ℝ)),
  (41, (-3173001788909977190207 / 3831119050343179847922509414400 : ℝ)),
  (42, (2219814171803873741 / 58639577301171120121262899200 : ℝ)),
  (43, (-230432959055494733 / 155698188006557801701284249600 : ℝ)),
  (44, (6042116150803057 / 124558550405246241361027399680 : ℝ)),
  (45, (-17860357684289 / 13776060874312948353293352960 : ℝ)),
  (46, (81781561957 / 3013513316255957452282920960 : ℝ)),
  (47, (-12033391 / 28837448002449353610362880 : ℝ)),
  (48, (6221 / 1484280411890775553474560 : ℝ)),
  (49, (-1 / 48466299163780426235904 : ℝ))]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p_expand (s : ℝ) : Nf s * Gf s = evalL pc s := by
  simp only [Nf, Gf, evalL, pc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sum_range_succ, Finset.sum_range_zero]
  ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem q_expand (t : ℝ) : (2 + 2 * primL pc 3 t) * Rf t = evalL qc t := by
  simp only [Rf, primL, evalL, pc, qc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sum_range_succ, Finset.sum_range_zero]
  ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem value_ge : (13.473613 : ℝ) ≤ 4 * (2 * (6931471803 / 10000000000 +
    (-(∑ i ∈ range 40, (-(1/2:ℝ)) ^ (i + 1) / ((i : ℝ) + 1)) - 2 * (1/2:ℝ) ^ 41)) +
    primL qc 3 5) := by
  simp only [primL, qc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem fcont : ContinuousOn (fun s : ℝ => Real.log (s - 2) / (s - 1)) (Set.Icc 3 5) := by
  apply ContinuousOn.div
  · apply ContinuousOn.log (by fun_prop)
    intro s hs; exact ne_of_gt (by linarith [hs.1])
  · fun_prop
  · intro s hs; exact ne_of_gt (by linarith [hs.1])

theorem inner_ge (t : ℝ) (h0 : 3 ≤ t) (h1 : t ≤ 5) :
    0 ≤ (∫ s in (3:ℝ)..t, Real.log (s - 2) / (s - 1)) ∧
      primL pc 3 t ≤ (∫ s in (3:ℝ)..t, Real.log (s - 2) / (s - 1)) := by
  have hfi : IntervalIntegrable (fun s : ℝ => Real.log (s - 2) / (s - 1)) volume 3 t := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h0]
    exact fcont.mono (Set.Icc_subset_Icc le_rfl h1)
  constructor
  · apply intervalIntegral.integral_nonneg h0
    intro s hs
    exact div_nonneg (Real.log_nonneg (by linarith [hs.1])) (by linarith [hs.1])
  · rw [← integral_evalL]
    refine intervalIntegral.integral_mono_on h0 ((evalL_cont pc).intervalIntegrable _ _) hfi ?_
    intro s hs
    exact (p_expand s).symm.trans_le (f_ge s hs.1 (by linarith [hs.2]))

/-- Wu 2004 arXiv 0705.1652 page 38 equations 10.2 and 10.3 and page 42: the index 0 leaf
value is at least 13.473613. -/
theorem explicit0 :
    (13.473613 : ℝ) ≤ 4 * (2 * Real.log 3 + ∫ t in (3 : ℝ)..5,
      (2 + 2 * ∫ s in (3:ℝ)..t, Real.log (s - 2) / (s - 1)) / t) := by
  have hfi : IntervalIntegrable (fun s : ℝ => Real.log (s - 2) / (s - 1)) volume 3 5 :=
    (fcont.mono (by rw [Set.uIcc_of_le (by norm_num)])).intervalIntegrable
  have hprim : ContinuousOn (fun t => ∫ s in (3:ℝ)..t, Real.log (s - 2) / (s - 1))
      (Set.uIcc 3 5) := by
    have hon : IntegrableOn (fun s : ℝ => Real.log (s - 2) / (s - 1)) (Set.uIcc 3 5) volume := by
      rw [Set.uIcc_of_le (by norm_num)]; exact fcont.integrableOn_Icc
    exact intervalIntegral.continuousOn_primitive_interval hon
  have hint : IntervalIntegrable (fun t : ℝ =>
      (2 + 2 * ∫ s in (3:ℝ)..t, Real.log (s - 2) / (s - 1)) / t) volume 3 5 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (continuousOn_const.add (continuousOn_const.mul hprim))
      continuousOn_id
    intro t ht; rw [Set.uIcc_of_le (by norm_num)] at ht
    exact ne_of_gt (show (0:ℝ) < t by linarith [ht.1])
  have key : ∫ t in (3:ℝ)..5, evalL qc t ≤ (∫ t in (3:ℝ)..5,
      (2 + 2 * ∫ s in (3:ℝ)..t, Real.log (s - 2) / (s - 1)) / t) := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((evalL_cont qc).intervalIntegrable _ _) hint ?_
    intro t ht
    obtain ⟨hI0, hI⟩ := inner_ge t ht.1 ht.2
    obtain ⟨hR0, hR⟩ := w_ge t ht.1 ht.2
    rw [← q_expand, div_eq_mul_one_div]
    calc (2 + 2 * primL pc 3 t) * Rf t ≤
        (2 + 2 * ∫ s in (3:ℝ)..t, Real.log (s - 2) / (s - 1)) * Rf t :=
          mul_le_mul_of_nonneg_right (by linarith) hR0
      _ ≤ _ := mul_le_mul_of_nonneg_left hR (by linarith)
  rw [integral_evalL] at key
  have := value_ge
  have := log_three_ge
  linarith

end LeanLab.ChenDoubleSieve.Feed1122Explicit0
