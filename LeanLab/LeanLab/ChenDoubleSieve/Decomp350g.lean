import LeanLab.ChenDoubleSieve.Decomp350d
import LeanLab.ChenDoubleSieve.SigmaCertificate

/-!
A polynomial route to the elementary F13 numerical bound.
Source: https://arxiv.org/pdf/0705.1652, page 41 equation 10.12 and page 42.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set Finset MeasureTheory intervalIntegral
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task350
open Task275 Wu04Integral

/-- Ten terms of the positive logarithm series at the upper endpoint.
Source: page 42 finite quadrature, derived polynomial certificate data. -/
def logTaylor13 (t : ℝ) : ℝ :=
  ∑ j ∈ range 10, (1 - t / kappa2) ^ (j + 1) / (j + 1)

/-- This polynomial lies between zero and the logarithm on the printed range.
Source: page 42 finite quadrature, derived from the positive log series. -/
theorem logTaylor13_bounds {t : ℝ} (ht : t ∈ Icc kappa1 kappa2) :
    0 ≤ logTaylor13 t ∧ logTaylor13 t ≤ log (kappa2 / t) ∧ log (kappa2 / t) ≤ 1 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num [kappa1] : (0 : ℝ) < kappa1) ht.1
  have hk0 : (0 : ℝ) < kappa2 := by norm_num [kappa2]
  have hs0 : 0 ≤ 1 - t / kappa2 := by rw [sub_nonneg, div_le_one hk0]; exact ht.2
  have hs1 : 1 - t / kappa2 < 1 := by linarith [div_pos ht0 hk0]
  have hs := hasSum_pow_div_log_of_abs_lt_one (x := 1 - t / kappa2)
    (by rwa [abs_of_nonneg hs0])
  have hp : 0 ≤ logTaylor13 t := by
    unfold logTaylor13
    exact sum_nonneg (fun j hj => div_nonneg (pow_nonneg hs0 _) (by positivity))
  have hlo := Summable.sum_le_tsum (range 10)
    (fun j hj => div_nonneg (pow_nonneg hs0 (j + 1)) (by positivity)) hs.summable
  rw [hs.tsum_eq] at hlo
  have he : -log (1 - (1 - t / kappa2)) = log (kappa2 / t) := by
    rw [show 1 - (1 - t / kappa2) = t / kappa2 by ring,
      log_div ht0.ne' hk0.ne', log_div hk0.ne' ht0.ne']
    ring
  rw [he] at hlo
  refine ⟨hp, hlo, ?_⟩
  have hu := log_le_sub_one_of_pos (div_pos hk0 ht0)
  have hr : kappa2 / t ≤ 2 := by
    rw [div_le_iff₀ ht0]
    norm_num [kappa1, kappa2] at ht ⊢
    linarith [ht.1]
  linarith

/-- Replacing the log by its lower polynomial gives an upper F13 kernel.
Source: page 42 quadrature, derived one sided polynomial comparison. -/
theorem F13_kernel_upper {t : ℝ} (ht : t ∈ Icc kappa1 kappa2) :
    (log (kappa2 / t) ^ 2 - 2 * log (kappa2 / t) + 2) / t - 2 / kappa2 ≤
      (logTaylor13 t ^ 2 - 2 * logTaylor13 t + 2) / t - 2 / kappa2 := by
  have h := logTaylor13_bounds ht
  have hm := mul_nonneg (sub_nonneg.mpr h.2.1) (show 0 ≤ 2 - log (kappa2 / t) - logTaylor13 t by linarith)
  apply sub_le_sub_right
  apply div_le_div_of_nonneg_right _ (by norm_num [kappa1] at ht; linarith [ht.1])
  nlinarith

/-- Exact polynomial antiderivative for the first F13 interval.
Source: page 42 finite quadrature, derived certificate data. -/
def primitive13First (t : ℝ) : ℝ :=
  (280761 / 1000000 : ℝ) * (((((((((((((((((((((-778673707042391531071955440660322793857980468750 / 234163824247918203480671725250523 : ℝ) * t ^ 1 / 1 + (-778673707133050542029588787788298515776855468750 / 234163824247918203480671725250523 : ℝ) * t ^ 2 / 2) + (-778673705181781645168444007269396654169921875000 / 234163824247918203480671725250523 : ℝ) * t ^ 3 / 3) + (-778673739123769631443962966185284759521484375000 / 234163824247918203480671725250523 : ℝ) * t ^ 4 / 4) + (-778673248427778157191519027793262481689453125000 / 234163824247918203480671725250523 : ℝ) * t ^ 5 / 5) + (-778679242204351771272171102867603302001953125000 / 234163824247918203480671725250523 : ℝ) * t ^ 6 / 6) + (-778616903025990197322128326416015625000000000000 / 234163824247918203480671725250523 : ℝ) * t ^ 7 / 7) + (-2337509554415307765816562538146972656250000000000 / 702491472743754610442015175751569 : ℝ) * t ^ 8 / 8) + (-2324989334186341273001134395599365234375000000000 / 702491472743754610442015175751569 : ℝ) * t ^ 9 / 9) + (-2405022819519079738222062587738037109375000000000 / 702491472743754610442015175751569 : ℝ) * t ^ 10 / 10) + (-1974605096488153235986828804016113281250000000000 / 702491472743754610442015175751569 : ℝ) * t ^ 11 / 11) + (-3904491773975045653060078620910644531250000000000 / 702491472743754610442015175751569 : ℝ) * t ^ 12 / 12) + (460067309418270597234368324279785156250000000000 / 100355924677679230063145025107367 : ℝ) * t ^ 13 / 13) + (-2580388358441268792375922203063964843750000000000 / 100355924677679230063145025107367 : ℝ) * t ^ 14 / 14) + (4584568363497965037822723388671875000000000000000 / 100355924677679230063145025107367 : ℝ) * t ^ 15 / 15) + (-1176684236270375549793243408203125000000000000000 / 14336560668239890009020717872481 : ℝ) * t ^ 16 / 16) + (129148247651755809783935546875000000000000000000 / 1592951185359987778780079763609 : ℝ) * t ^ 17 / 17) + (-9094947017729282379150390625000000000000000000 / 176994576151109753197786640401 : ℝ) * t ^ 18 / 18) - (29979721 / 6350400 : ℝ) / t) + (-63554388091 / 184161600 : ℝ) * log t) - (3737633793818695255118235638991184425849151114608121 / 1123986356390007376707224281202510400 : ℝ) * log (1 - t))

/-- Exact polynomial antiderivative for the second F13 interval.
Source: page 42 finite quadrature, derived certificate data. -/
def primitive13Second (t : ℝ) : ℝ :=
  (280761 / 1000000 : ℝ) * (((((((((((((((((((((163453125 / 11774 : ℝ) * t ^ 1 / 1 + (-594875000000 / 1536507 : ℝ) * t ^ 2 / 2) + (17681152343750 / 2121843 : ℝ) * t ^ 3 / 3) + (-2973085937500000 / 20511149 : ℝ) * t ^ 4 / 4) + (11218200683593750000 / 5353409889 : ℝ) * t ^ 5 / 5) + (-64905883789062500000000 / 2535731817423 : ℝ) * t ^ 6 / 6) + (932230472564697265625000 / 3501724890727 : ℝ) * t ^ 7 / 7) + (-19423606872558593750000000000 / 8225551768317723 : ℝ) * t ^ 8 / 8) + (472379932403564453125000000000 / 26504555697912663 : ℝ) * t ^ 9 / 9) + (-1389980316162109375000000000000 / 12200509765705829 : ℝ) * t ^ 10 / 10) + (1951046288013458251953125000000000 / 3184333048849221369 : ℝ) * t ^ 11 / 11) + (-84564089775085449218750000000000000 / 30781886138875806567 : ℝ) * t ^ 12 / 12) + (147880055010318756103515625000000000000 / 14580353401114173710569 : ℝ) * t ^ 13 / 13) + (-16470476984977722167968750000000000000000 / 543638891098685619779787 : ℝ) * t ^ 14 / 14) + (375195668311789631843566894531250000000000 / 5255175947287294324537941 : ℝ) * t ^ 15 / 15) + (-6490154191851615905761718750000000000000000 / 50800034157110511803866763 : ℝ) * t ^ 16 / 16) + (2781234798021614551544189453125000000000000000 / 17047040033578941746754718041 : ℝ) * t ^ 17 / 17) + (-7275957614183425903320312500000000000000000000 / 54929351219309923406209647021 : ℝ) * t ^ 18 / 18) + (9094947017729282379150390625000000000000000000 / 176994576151109753197786640401 : ℝ) * t ^ 19 / 19) - (29979721 / 6350400 : ℝ) / t) + (-639125 / 1827 : ℝ) * log t)

/-- The first polynomial primitive has exactly the required rational derivative.
Source: page 42 finite quadrature, derived polynomial identity. -/
theorem primitive13First_deriv {t : ℝ} (ht0 : t ≠ 0) (ht1 : 1 - t ≠ 0) :
    HasDerivAt primitive13First
      (((280761 / 1000000 : ℝ) *
        ((logTaylor13 t ^ 2 - 2 * logTaylor13 t + 2) / t - 2 / kappa2)) /
          (t * (1 - t))) t := by
  have hd := ((((((((((((((((((((((((hasDerivAt_id t).pow 1).const_mul (-778673707042391531071955440660322793857980468750 / 234163824247918203480671725250523 : ℝ)).div_const 1).add ((((hasDerivAt_id t).pow 2).const_mul (-778673707133050542029588787788298515776855468750 / 234163824247918203480671725250523 : ℝ)).div_const 2)).add ((((hasDerivAt_id t).pow 3).const_mul (-778673705181781645168444007269396654169921875000 / 234163824247918203480671725250523 : ℝ)).div_const 3)).add ((((hasDerivAt_id t).pow 4).const_mul (-778673739123769631443962966185284759521484375000 / 234163824247918203480671725250523 : ℝ)).div_const 4)).add ((((hasDerivAt_id t).pow 5).const_mul (-778673248427778157191519027793262481689453125000 / 234163824247918203480671725250523 : ℝ)).div_const 5)).add ((((hasDerivAt_id t).pow 6).const_mul (-778679242204351771272171102867603302001953125000 / 234163824247918203480671725250523 : ℝ)).div_const 6)).add ((((hasDerivAt_id t).pow 7).const_mul (-778616903025990197322128326416015625000000000000 / 234163824247918203480671725250523 : ℝ)).div_const 7)).add ((((hasDerivAt_id t).pow 8).const_mul (-2337509554415307765816562538146972656250000000000 / 702491472743754610442015175751569 : ℝ)).div_const 8)).add ((((hasDerivAt_id t).pow 9).const_mul (-2324989334186341273001134395599365234375000000000 / 702491472743754610442015175751569 : ℝ)).div_const 9)).add ((((hasDerivAt_id t).pow 10).const_mul (-2405022819519079738222062587738037109375000000000 / 702491472743754610442015175751569 : ℝ)).div_const 10)).add ((((hasDerivAt_id t).pow 11).const_mul (-1974605096488153235986828804016113281250000000000 / 702491472743754610442015175751569 : ℝ)).div_const 11)).add ((((hasDerivAt_id t).pow 12).const_mul (-3904491773975045653060078620910644531250000000000 / 702491472743754610442015175751569 : ℝ)).div_const 12)).add ((((hasDerivAt_id t).pow 13).const_mul (460067309418270597234368324279785156250000000000 / 100355924677679230063145025107367 : ℝ)).div_const 13)).add ((((hasDerivAt_id t).pow 14).const_mul (-2580388358441268792375922203063964843750000000000 / 100355924677679230063145025107367 : ℝ)).div_const 14)).add ((((hasDerivAt_id t).pow 15).const_mul (4584568363497965037822723388671875000000000000000 / 100355924677679230063145025107367 : ℝ)).div_const 15)).add ((((hasDerivAt_id t).pow 16).const_mul (-1176684236270375549793243408203125000000000000000 / 14336560668239890009020717872481 : ℝ)).div_const 16)).add ((((hasDerivAt_id t).pow 17).const_mul (129148247651755809783935546875000000000000000000 / 1592951185359987778780079763609 : ℝ)).div_const 17)).add ((((hasDerivAt_id t).pow 18).const_mul (-9094947017729282379150390625000000000000000000 / 176994576151109753197786640401 : ℝ)).div_const 18)).sub ((hasDerivAt_const t (29979721 / 6350400 : ℝ)).div (hasDerivAt_id t) ht0)).add ((hasDerivAt_log ht0).const_mul (-63554388091 / 184161600 : ℝ))).sub (((hasDerivAt_log ht1).comp t ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))).const_mul (3737633793818695255118235638991184425849151114608121 / 1123986356390007376707224281202510400 : ℝ))).const_mul (280761 / 1000000 : ℝ)
  convert hd using 1 <;> first
  | rfl
  | (simp only [Pi.sub_apply, Pi.neg_apply, Pi.div_apply, Pi.add_apply, Pi.pow_apply, id_eq]
     norm_num [logTaylor13, kappa2, sum_range_succ]
     field_simp [ht0, ht1]
     <;> ring)

/-- The second polynomial primitive has exactly the required rational derivative.
Source: page 42 finite quadrature, derived polynomial identity. -/
theorem primitive13Second_deriv {t : ℝ} (ht0 : t ≠ 0) :
    HasDerivAt primitive13Second
      (((280761 / 1000000 : ℝ) *
        ((logTaylor13 t ^ 2 - 2 * logTaylor13 t + 2) / t - 2 / kappa2)) / t) t := by
  have hd := ((((((((((((((((((((((((hasDerivAt_id t).pow 1).const_mul (163453125 / 11774 : ℝ)).div_const 1).add ((((hasDerivAt_id t).pow 2).const_mul (-594875000000 / 1536507 : ℝ)).div_const 2)).add ((((hasDerivAt_id t).pow 3).const_mul (17681152343750 / 2121843 : ℝ)).div_const 3)).add ((((hasDerivAt_id t).pow 4).const_mul (-2973085937500000 / 20511149 : ℝ)).div_const 4)).add ((((hasDerivAt_id t).pow 5).const_mul (11218200683593750000 / 5353409889 : ℝ)).div_const 5)).add ((((hasDerivAt_id t).pow 6).const_mul (-64905883789062500000000 / 2535731817423 : ℝ)).div_const 6)).add ((((hasDerivAt_id t).pow 7).const_mul (932230472564697265625000 / 3501724890727 : ℝ)).div_const 7)).add ((((hasDerivAt_id t).pow 8).const_mul (-19423606872558593750000000000 / 8225551768317723 : ℝ)).div_const 8)).add ((((hasDerivAt_id t).pow 9).const_mul (472379932403564453125000000000 / 26504555697912663 : ℝ)).div_const 9)).add ((((hasDerivAt_id t).pow 10).const_mul (-1389980316162109375000000000000 / 12200509765705829 : ℝ)).div_const 10)).add ((((hasDerivAt_id t).pow 11).const_mul (1951046288013458251953125000000000 / 3184333048849221369 : ℝ)).div_const 11)).add ((((hasDerivAt_id t).pow 12).const_mul (-84564089775085449218750000000000000 / 30781886138875806567 : ℝ)).div_const 12)).add ((((hasDerivAt_id t).pow 13).const_mul (147880055010318756103515625000000000000 / 14580353401114173710569 : ℝ)).div_const 13)).add ((((hasDerivAt_id t).pow 14).const_mul (-16470476984977722167968750000000000000000 / 543638891098685619779787 : ℝ)).div_const 14)).add ((((hasDerivAt_id t).pow 15).const_mul (375195668311789631843566894531250000000000 / 5255175947287294324537941 : ℝ)).div_const 15)).add ((((hasDerivAt_id t).pow 16).const_mul (-6490154191851615905761718750000000000000000 / 50800034157110511803866763 : ℝ)).div_const 16)).add ((((hasDerivAt_id t).pow 17).const_mul (2781234798021614551544189453125000000000000000 / 17047040033578941746754718041 : ℝ)).div_const 17)).add ((((hasDerivAt_id t).pow 18).const_mul (-7275957614183425903320312500000000000000000000 / 54929351219309923406209647021 : ℝ)).div_const 18)).add ((((hasDerivAt_id t).pow 19).const_mul (9094947017729282379150390625000000000000000000 / 176994576151109753197786640401 : ℝ)).div_const 19)).sub ((hasDerivAt_const t (29979721 / 6350400 : ℝ)).div (hasDerivAt_id t) ht0)).add ((hasDerivAt_log ht0).const_mul (-639125 / 1827 : ℝ))).const_mul (280761 / 1000000 : ℝ)
  convert hd using 1 <;> first
  | rfl
  | (simp only [Pi.sub_apply, Pi.neg_apply, Pi.div_apply, Pi.add_apply, Pi.pow_apply, id_eq]
     norm_num [logTaylor13, kappa2, sum_range_succ]
     field_simp [ht0]
     <;> ring)

/-- The final scalar certificate expression.
Source: page 42 finite quadrature, derived exact endpoint expression. -/
def endpoint13 : ℝ := (-13245315056314412124614645233815589201625921350137271895627937666623219 / 107384506344655401952845422789644233650823561216000000000 : ℝ) + (-5947864518272417 / 8526000000000 : ℝ) * log ((6 / 5 : ℝ)) + (349793933862110232840750318746267976861944505362830220027 / 52036405388426267440149272277894000000000 : ℝ) * log ((55 / 54 : ℝ)) + (-478510331 / 609000 : ℝ) * log ((29 / 25 : ℝ))

/-- Exact rational arithmetic certifies the directed endpoint rounding.
Source: page 42 finite quadrature, derived rational certificate. -/
theorem endpoint13_certificate : (-13245315056314412124614645233815589201625921350137271895627937666623219 / 107384506344655401952845422789644233650823561216000000000 : ℚ) + (-5947864518272417 / 8526000000000 : ℚ) * logLowerQ 16 (6 / 5 : ℚ) + (349793933862110232840750318746267976861944505362830220027 / 52036405388426267440149272277894000000000 : ℚ) * logUpperQ 16 (55 / 54 : ℚ) + (-478510331 / 609000 : ℚ) * logLowerQ 16 (29 / 25 : ℚ) ≤ (2331 / 100000 : ℚ) := by
  decide +kernel

/-- The endpoint expression is below the printed F13 coefficient.
Source: page 42 final numerical display, derived rational log enclosures. -/
theorem endpoint13_upper : endpoint13 ≤ 0.023310 := by
  have h1 := (log_bounds 16 (y := (6 / 5 : ℝ)) (by norm_num)).1
  have h2 := (log_bounds 16 (y := (55 / 54 : ℝ)) (by norm_num)).2
  have h3 := (log_bounds 16 (y := (29 / 25 : ℝ)) (by norm_num)).1
  have hc0 := (Rat.cast_le (K := ℝ)).2 endpoint13_certificate
  have hc : (-13245315056314412124614645233815589201625921350137271895627937666623219 / 107384506344655401952845422789644233650823561216000000000 : ℝ) + (-5947864518272417 / 8526000000000 : ℝ) * logLower 16 (6 / 5 : ℝ) + (349793933862110232840750318746267976861944505362830220027 / 52036405388426267440149272277894000000000 : ℝ) * logUpper 16 (55 / 54 : ℝ) + (-478510331 / 609000 : ℝ) * logLower 16 (29 / 25 : ℝ) ≤ (2331 / 100000 : ℝ) := by
    convert hc0 using 1 <;> norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_neg, logLowerQ_cast, logUpperQ_cast]
  unfold endpoint13
  nlinarith

/-- Evaluate the full polynomial majorant by its two antiderivatives.
Source: page 42 finite quadrature, derived exact endpoint identity. -/
theorem polynomial_F13_endpoint :
    36 / 5 * (∫ t in kappa1..(1 / 10 : ℝ),
      ((280761 / 1000000 : ℝ) *
        ((logTaylor13 t ^ 2 - 2 * logTaylor13 t + 2) / t - 2 / kappa2)) /
          (t * (1 - t))) +
    8 * (∫ t in (1 / 10 : ℝ)..kappa2,
      ((280761 / 1000000 : ℝ) *
        ((logTaylor13 t ^ 2 - 2 * logTaylor13 t + 2) / t - 2 / kappa2)) / t)
      = endpoint13 := by
  have hk0 : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hk1 : kappa2 < (1 : ℝ) := by norm_num [kappa2]
  have hnum : ContinuousOn (fun t => (280761 / 1000000 : ℝ) *
      ((logTaylor13 t ^ 2 - 2 * logTaylor13 t + 2) / t - 2 / kappa2))
      (Icc kappa1 kappa2) := by
    have hpoly : Continuous logTaylor13 := by unfold logTaylor13; fun_prop
    exact continuousOn_const.mul
      ((((hpoly.continuousOn.pow 2).sub (hpoly.continuousOn.const_mul 2)).add continuousOn_const).div
        continuousOn_id (fun t ht => (hk0.trans_le ht.1).ne') |>.sub continuousOn_const)
  have hfirst : (∫ t in kappa1..(1 / 10 : ℝ),
      ((280761 / 1000000 : ℝ) *
        ((logTaylor13 t ^ 2 - 2 * logTaylor13 t + 2) / t - 2 / kappa2)) /
          (t * (1 - t))) = primitive13First (1 / 10) - primitive13First kappa1 := by
    apply integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le (by norm_num [kappa1] : kappa1 ≤ (1 / 10 : ℝ))] at ht
      exact primitive13First_deriv (by linarith [ht.1]) (by linarith [ht.2])
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num [kappa1] : kappa1 ≤ (1 / 10 : ℝ))]
      exact (hnum.div (by fun_prop) (fun t ht => mul_ne_zero (hk0.trans_le ht.1).ne'
        (by linarith [ht.2] : 1 - t ≠ 0))).mono
          (fun t ht => ⟨ht.1, ht.2.trans (by norm_num [kappa2])⟩)
  have hsecond : (∫ t in (1 / 10 : ℝ)..kappa2,
      ((280761 / 1000000 : ℝ) *
        ((logTaylor13 t ^ 2 - 2 * logTaylor13 t + 2) / t - 2 / kappa2)) / t) =
        primitive13Second kappa2 - primitive13Second (1 / 10) := by
    apply integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le (by norm_num [kappa2] : (1 / 10 : ℝ) ≤ kappa2)] at ht
      exact primitive13Second_deriv (by linarith [ht.1])
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num [kappa2] : (1 / 10 : ℝ) ≤ kappa2)]
      exact (hnum.div continuousOn_id (fun t ht => (hk0.trans_le ht.1).ne')).mono
        (fun t ht => ⟨(by norm_num [kappa1] : kappa1 ≤ (1 / 10 : ℝ)).trans ht.1, ht.2⟩)
  rw [hfirst, hsecond]
  have hL1 : log (6 / 5 : ℝ) = log (1 / 10 : ℝ) - log (1 / 12 : ℝ) := by
    rw [← log_div (by norm_num : (1 / 10 : ℝ) ≠ 0) (by norm_num : (1 / 12 : ℝ) ≠ 0)]
    congr 1
    norm_num
  have hL2 : log (55 / 54 : ℝ) = log (11 / 12 : ℝ) - log (9 / 10 : ℝ) := by
    rw [← log_div (by norm_num : (11 / 12 : ℝ) ≠ 0) (by norm_num : (9 / 10 : ℝ) ≠ 0)]
    congr 1
    norm_num
  have hL3 : log (29 / 25 : ℝ) = log (29 / 250 : ℝ) - log (1 / 10 : ℝ) := by
    rw [← log_div (by norm_num : (29 / 250 : ℝ) ≠ 0) (by norm_num : (1 / 10 : ℝ) ≠ 0)]
    congr 1
    norm_num
  unfold primitive13First primitive13Second endpoint13
  norm_num only [kappa1, kappa2, show (1 - (1 / 10 : ℝ)) = 9 / 10 by norm_num,
    show (1 - (1 / 12 : ℝ)) = 11 / 12 by norm_num]
  rw [hL1, hL2, hL3]
  ring

/-- The one dimensional F13 quadrature is certified without any analytic input.
Source: page 42 final display after page 41 equation 10.12. -/
theorem F13_elementary_upper_clean :
    36 / 5 * (∫ t in kappa1..(1 / 10 : ℝ),
      ((280761 / 1000000 : ℝ) *
        ((log (kappa2 / t) ^ 2 - 2 * log (kappa2 / t) + 2) / t - 2 / kappa2)) /
          (t * (1 - t))) +
    8 * (∫ t in (1 / 10 : ℝ)..kappa2,
      ((280761 / 1000000 : ℝ) *
        ((log (kappa2 / t) ^ 2 - 2 * log (kappa2 / t) + 2) / t - 2 / kappa2)) / t)
      ≤ 0.023310 := by
  have hk0 : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hk2 : (0 : ℝ) < kappa2 := by norm_num [kappa2]
  have hk1 : kappa2 < (1 : ℝ) := by norm_num [kappa2]
  have hL : ContinuousOn (fun t => log (kappa2 / t)) (Icc kappa1 kappa2) :=
    (continuousOn_const.div continuousOn_id (fun t ht => (hk0.trans_le ht.1).ne')).log
      (fun t ht => (div_pos hk2 (hk0.trans_le ht.1)).ne')
  have hLP : Continuous logTaylor13 := by unfold logTaylor13; fun_prop
  have hnumA : ContinuousOn (fun t => (280761 / 1000000 : ℝ) *
      ((log (kappa2 / t) ^ 2 - 2 * log (kappa2 / t) + 2) / t - 2 / kappa2))
      (Icc kappa1 kappa2) := by
    exact continuousOn_const.mul
      ((((hL.pow 2).sub (hL.const_mul 2)).add continuousOn_const).div
        continuousOn_id (fun t ht => (hk0.trans_le ht.1).ne') |>.sub continuousOn_const)
  have hnumP : ContinuousOn (fun t => (280761 / 1000000 : ℝ) *
      ((logTaylor13 t ^ 2 - 2 * logTaylor13 t + 2) / t - 2 / kappa2))
      (Icc kappa1 kappa2) := by
    exact continuousOn_const.mul
      ((((hLP.continuousOn.pow 2).sub (hLP.continuousOn.const_mul 2)).add continuousOn_const).div
        continuousOn_id (fun t ht => (hk0.trans_le ht.1).ne') |>.sub continuousOn_const)
  have hsub1 : Icc kappa1 (1 / 10 : ℝ) ⊆ Icc kappa1 kappa2 :=
    Icc_subset_Icc_right (by norm_num [kappa2])
  have hsub2 : Icc (1 / 10 : ℝ) kappa2 ⊆ Icc kappa1 kappa2 :=
    Icc_subset_Icc_left (by norm_num [kappa1])
  have hfirst :
      (∫ t in kappa1..(1 / 10 : ℝ),
        ((280761 / 1000000 : ℝ) *
          ((log (kappa2 / t) ^ 2 - 2 * log (kappa2 / t) + 2) / t - 2 / kappa2)) /
            (t * (1 - t))) ≤
      (∫ t in kappa1..(1 / 10 : ℝ),
        ((280761 / 1000000 : ℝ) *
          ((logTaylor13 t ^ 2 - 2 * logTaylor13 t + 2) / t - 2 / kappa2)) /
            (t * (1 - t))) := by
    apply integral_mono_on (by norm_num [kappa1])
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num [kappa1] : kappa1 ≤ (1 / 10 : ℝ))]
      exact (hnumA.div (by fun_prop) (fun t ht => mul_ne_zero
        (hk0.trans_le ht.1).ne' (by linarith [ht.2] : 1 - t ≠ 0))).mono hsub1
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num [kappa1] : kappa1 ≤ (1 / 10 : ℝ))]
      exact (hnumP.div (by fun_prop) (fun t ht => mul_ne_zero
        (hk0.trans_le ht.1).ne' (by linarith [ht.2] : 1 - t ≠ 0))).mono hsub1
    · intro t ht
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (F13_kernel_upper (hsub1 ht)) (by norm_num))
        (mul_nonneg (hk0.le.trans ht.1) (by linarith [ht.2]))
  have hsecond :
      (∫ t in (1 / 10 : ℝ)..kappa2,
        ((280761 / 1000000 : ℝ) *
          ((log (kappa2 / t) ^ 2 - 2 * log (kappa2 / t) + 2) / t - 2 / kappa2)) / t) ≤
      (∫ t in (1 / 10 : ℝ)..kappa2,
        ((280761 / 1000000 : ℝ) *
          ((logTaylor13 t ^ 2 - 2 * logTaylor13 t + 2) / t - 2 / kappa2)) / t) := by
    apply integral_mono_on (by norm_num [kappa2])
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num [kappa2] : (1 / 10 : ℝ) ≤ kappa2)]
      exact (hnumA.div continuousOn_id (fun t ht => (hk0.trans_le ht.1).ne')).mono hsub2
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num [kappa2] : (1 / 10 : ℝ) ≤ kappa2)]
      exact (hnumP.div continuousOn_id (fun t ht => (hk0.trans_le ht.1).ne')).mono hsub2
    · intro t ht
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (F13_kernel_upper (hsub2 ht)) (by norm_num)) (by linarith [ht.1])
  linarith only [hfirst, hsecond, polynomial_F13_endpoint, endpoint13_upper]

end LeanLab.ChenDoubleSieve.Task350
