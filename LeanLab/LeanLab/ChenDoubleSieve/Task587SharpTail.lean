import LeanLab.ChenDoubleSieve.Task587TailFiveFormula

/-!
A sharper derived Buchstab tail for Wu 2004 Lemma 2.10 page 9.
Source: https://arxiv.org/abs/0705.1652.
This bound is weaker than the printed 0.561522 bound and is proved from the delay equation.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set Finset MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional Wu04Buchstab

/-- One delay step converts an endpoint bound and a bound on the delayed values to an affine bound.
Wu 2004 Lemma 2.10 page 9, derived integration tool. -/
theorem delay_affine_upper {ω : ℝ → ℝ} (hω : IsBuchstab ω) {a u B C : ℝ}
    (ha : 2 ≤ a) (hau : a ≤ u) (hbase : ω a ≤ B)
    (hdelay : ∀ t ∈ Set.Icc a u, ω (t - 1) ≤ C) :
    u * ω u ≤ a * B + (u - a) * C := by
  have hc : ContinuousOn (fun t : ℝ => t * ω t) (Set.Icc a u) :=
    continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
  have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc a u) := by
    rw [uIcc_of_le hau]
    apply hω.1.comp (by fun_prop)
    intro t ht
    change 1 ≤ t - 1
    linarith [ht.1]
  have hf := integral_eq_sub_of_hasDerivAt_of_le hau hc
    (fun t ht => hω.2.2 t (by linarith [ht.1])) hci.intervalIntegrable
  have hi : (∫ t in a..u, ω (t - 1)) ≤ (u - a) * C := by
    have hm := integral_mono_on (μ := volume) hau hci.intervalIntegrable
      intervalIntegrable_const hdelay
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
  have hb := mul_le_mul_of_nonneg_left hbase (by linarith : 0 ≤ a)
  linarith

/-- Four exact logarithm enclosures prepare the short initial intervals.
Wu 2004 page 9, derived rational logarithm certificates. -/
theorem sharp_tail_log_certificates :
    log (2 : ℝ) ≤ 6932 / 10000 ∧ log (3 / 2 : ℝ) ≤ 406 / 1000 ∧
      log (5 / 2 : ℝ) ≤ 9164 / 10000 ∧ log (3 : ℝ) ≤ 1098613 / 1000000 := by
  constructor
  · apply (Wu04Integral.log_bounds 12 (y := 2) (by norm_num)).2.trans
    norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, sum_range_succ]
  constructor
  · apply (Wu04Integral.log_bounds 12 (y := (3 / 2 : ℝ)) (by norm_num)).2.trans
    norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, sum_range_succ]
  constructor
  · apply (Wu04Integral.log_bounds 12 (y := (5 / 2 : ℝ)) (by norm_num)).2.trans
    norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, sum_range_succ]
  · apply (Wu04Integral.log_bounds 12 (y := 3) (by norm_num)).2.trans
    norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, sum_range_succ]

/-- A scalar certificate at five halves supplies the value at seven halves.
Wu 2004 page 9, derived kernel checked endpoint certificate. -/
theorem J_five_halves_certificate : Burst9Psi2.jUpperSum (5 / 2) 128 ≤ (467 / 10000 : ℚ) := by
  decide +kernel

/-- A sharper endpoint certificate at three supplies the value at four.
Wu 2004 page 9, derived kernel checked endpoint certificate. -/
theorem J_three_sharp_certificate : Burst9Psi2.jUpperSum 3 128 ≤ (14723 / 100000 : ℚ) := by
  decide +kernel

/-- The exact scalar formula bounds omega at seven halves.
Wu 2004 Lemma 2.10 page 9, derived endpoint enclosure. -/
theorem buchstab_seven_halves_le {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    ω (7 / 2) ≤ (5609 / 10000 : ℝ) := by
  have hj := Burst9Psi2.J_upper_of_cert (by norm_num) (by norm_num) J_five_halves_certificate
  have hf := buchstab_three_four_formula hω (u := (7 / 2 : ℝ)) (by norm_num)
  have hl := sharp_tail_log_certificates.2.2.1
  norm_num at hj hf
  linarith

/-- The sharper scalar certificate bounds omega at four.
Wu 2004 Lemma 2.10 page 9, derived endpoint enclosure. -/
theorem buchstab_four_le_56147 {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    ω 4 ≤ (56147 / 100000 : ℝ) := by
  have hj := Burst9Psi2.J_upper_of_cert (by norm_num) (by norm_num) J_three_sharp_certificate
  have hf := buchstab_four_identity hω
  have hl := sharp_tail_log_certificates.2.2.2
  norm_num at hj
  linarith

/-- A logarithm tangent bounds the initial half interval.
Wu 2004 Lemma 2.10 page 9, derived local Buchstab enclosure. -/
theorem buchstab_two_five_halves_le {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : u ∈ Set.Icc (2 : ℝ) (5 / 2)) : ω u ≤ (563 / 1000 : ℝ) := by
  have hu2 := hu.1
  have hu5 := hu.2
  have hy : 0 < u - 1 := by linarith
  have ht := log_le_sub_one_of_pos (div_pos hy (by norm_num : (0 : ℝ) < 3 / 2))
  rw [log_div hy.ne' (by norm_num : (3 / 2 : ℝ) ≠ 0)] at ht
  have hl := sharp_tail_log_certificates.2.1
  rw [formula_two_three hω ⟨hu2, by linarith⟩, div_le_iff₀ (by linarith : 0 < u)]
  norm_num at ht
  linarith

/-- The value at three and the local delayed bound control the following half interval.
Wu 2004 Lemma 2.10 page 9, derived profile enclosure. -/
theorem buchstab_three_seven_halves_le {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : u ∈ Set.Icc (3 : ℝ) (7 / 2)) : ω u ≤ (5644 / 10000 : ℝ) := by
  have h3 : ω 3 ≤ (5644 / 10000 : ℝ) := by
    rw [formula_two_three hω (by norm_num : (3 : ℝ) ∈ Set.Icc 2 3)]
    norm_num
    linarith [sharp_tail_log_certificates.1]
  have hm := delay_affine_upper hω (by norm_num : (2 : ℝ) ≤ 3) hu.1 h3
    (fun t ht => buchstab_two_five_halves_le hω ⟨by linarith [ht.1], by linarith [ht.2, hu.2]⟩)
  have hmul : u * ω u ≤ u * (5644 / 10000) := by nlinarith [hu.1]
  exact (mul_le_mul_iff_right₀ (by linarith [hu.1] : 0 < u)).mp (by simpa [mul_comm] using hmul)

/-- The endpoint at seven halves controls omega up to four.
Wu 2004 Lemma 2.10 page 9, derived affine delay estimate. -/
theorem buchstab_seven_halves_four_le {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : u ∈ Set.Icc (7 / 2 : ℝ) 4) : ω u ≤ (5618 / 10000 : ℝ) := by
  have hm := delay_affine_upper hω (by norm_num : (2 : ℝ) ≤ 7 / 2) hu.1
    (buchstab_seven_halves_le hω)
    (fun t ht => buchstab_le_5671433 hω (by linarith [ht.1]))
  have hmul : u * ω u ≤ u * (5618 / 10000) := by nlinarith [hu.1, hu.2]
  exact (mul_le_mul_iff_right₀ (by linarith [hu.1] : 0 < u)).mp (by simpa [mul_comm] using hmul)

/-- The sharp value at four and the earlier profile bound control the next half interval.
Wu 2004 Lemma 2.10 page 9, derived affine delay estimate. -/
theorem buchstab_four_nine_halves_le {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : u ∈ Set.Icc (4 : ℝ) (9 / 2)) : ω u ≤ (5618 / 10000 : ℝ) := by
  have hm := delay_affine_upper hω (by norm_num : (2 : ℝ) ≤ 4) hu.1
    (buchstab_four_le_56147 hω)
    (fun t ht => buchstab_three_seven_halves_le hω ⟨by linarith [ht.1], by linarith [ht.2, hu.2]⟩)
  have hmul : u * ω u ≤ u * (5618 / 10000) := by nlinarith [hu.1, hu.2]
  exact (mul_le_mul_iff_right₀ (by linarith [hu.1] : 0 < u)).mp (by simpa [mul_comm] using hmul)

/-- A proved uniform tail bound starts at seven halves.
Wu 2004 Lemma 2.10 page 9, a weaker derived variant of its printed tail bound. -/
theorem buchstab_le_5618 {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : (7 / 2 : ℝ) ≤ u) : ω u ≤ (5618 / 10000 : ℝ) := by
  apply propagate_upper_from hω (a := (7 / 2 : ℝ)) (by norm_num) ?_ u hu
  intro t ht
  by_cases h : t ≤ 4
  · exact buchstab_seven_halves_four_le hω ⟨ht.1, h⟩
  · exact buchstab_four_nine_halves_le hω ⟨(lt_of_not_ge h).le, by linarith [ht.2]⟩

/-- The local profile and sharper tail improve the uniform cap after three.
Wu 2004 Lemma 2.10 page 9, derived elementary enclosure. -/
theorem buchstab_le_5644 {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : 3 ≤ u) : ω u ≤ (5644 / 10000 : ℝ) := by
  by_cases h : u ≤ (7 / 2 : ℝ)
  · exact buchstab_three_seven_halves_le hω ⟨hu, h⟩
  · exact (buchstab_le_5618 hω (le_of_not_ge h)).trans (by norm_num)

end LeanLab.ChenDoubleSieve.Task587
