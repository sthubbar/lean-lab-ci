/-
P0044, Cai 2002. Decomposition of the Theorem on pages 597 to 598.
The written proof occupies pages 600 to 604.
AI wrote the Lean code. Binary Goldbach is open.
The four analytic leaves remain CONDITIONAL on the sources named below.
The assembly retains an explicit allowance for the error in display 4.1.
-/
import LeanLab.Cai2002.Sum41
import LeanLab.Cai2002.Numerics
import LeanLab.ChenExplicit.Reductions
import LeanLab.Cai2002.AnalyticInputs118
import LeanLab.PNTPort.BVMax.PrimesUncond
import LeanLab.PNTPort.BVMax.PiPi
import LeanLab.Cai2002.Integral44
import LeanLab.Cai2002.Integral47
import LeanLab.Cai2002.Integrals
import LeanLab.Cai2002.SieveFunctions118
import LeanLab.ChenExplicit.LinearSieve
import LeanLab.Cai2002.Normalization118
import LeanLab.Cai2002.Coefficient118
import LeanLab.AlmostPrimeSums.Decomp1527c

open Filter Asymptotics Finset Real intervalIntegral Set
open scoped Topology

namespace LeanLab.Cai2002


/-- Page 599 Lemma 3. The inclusive prime progression counts agree. -/
theorem apCount118_eq_piAP (y : ℝ) (d l : ℕ) :
    (apCount118 y d l : ℝ) = LeanLab.PNTPort.BVMax.piAP y d l := by
  unfold apCount118 LeanLab.PNTPort.BVMax.piAP LeanLab.PNTPort.BVMax.piN
  apply congrArg (fun s : Finset ℕ => (s.card : ℝ))
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hp, hprime, hmod⟩
    exact ⟨⟨hprime.one_lt.le, by omega⟩, hmod, hprime⟩
  · rintro ⟨⟨_, hp⟩, hmod, hprime⟩
    exact ⟨by omega, hprime, hmod⟩

/-- Page 599 Lemma 3. The discrete logarithmic integral differs from Li by at most two. -/
theorem liD_sub_li118_bound (y : ℝ) (hy : 2 ≤ y) :
    |LeanLab.PNTPort.BVMax.liD y - li118 y| ≤ 2 := by
  let v : ℝ → ℝ := fun t => 1 / Real.log t
  have hv : AntitoneOn v (Set.Ici 2) := by
    intro a ha b hb hab
    change 2 ≤ a at ha
    exact one_div_le_one_div_of_le (Real.log_pos (by linarith))
      (Real.log_le_log (by linarith) hab)
  have hc (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable v MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact continuousOn_const.div (continuousOn_id.log (fun t ht => by
      change t ≠ 0; linarith [ht.1])) (fun t ht => ne_of_gt (Real.log_pos (by
        linarith [ht.1])))
  have hmono (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) : li118 a ≤ li118 b := by
    have hi := intervalIntegral.integral_add_adjacent_intervals (hc 2 a le_rfl ha)
      (hc a b ha hab)
    have hn : 0 ≤ ∫ t in a..b, v t := intervalIntegral.integral_nonneg hab
      (fun t ht => div_nonneg zero_le_one (Real.log_nonneg (by linarith [ht.1])))
    change (∫ t in (2 : ℝ)..a, v t) ≤ ∫ t in (2 : ℝ)..b, v t
    linarith
  let n : ℕ := ⌊y⌋₊
  have hn : 2 ≤ n := Nat.le_floor hy
  have hny : (n : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyn : y ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one y).le
  have hs : LeanLab.PNTPort.BVMax.liD y = ∑ k ∈ Finset.Icc 2 n, v k := by
    unfold LeanLab.PNTPort.BVMax.liD LeanLab.PNTPort.BVMax.liN
    rw [← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_eq_sum_Ico_succ_bot (show 1 < ⌊y⌋₊ + 1 by omega)]
    simp [v, n, Finset.Ico_add_one_right_eq_Icc]
  have hl : li118 (n + 1) ≤ LeanLab.PNTPort.BVMax.liD y := by
    have hh := (hv.mono (show Set.Icc (2 : ℝ) ((n + 1 : ℕ) : ℝ) ⊆ Set.Ici 2 from
      fun _ h => h.1)).integral_le_sum_Ico (show 2 ≤ n + 1 by omega)
    simpa [li118, hs, Finset.Ico_add_one_right_eq_Icc, v, Nat.cast_add, Nat.cast_one] using hh
  have hu : LeanLab.PNTPort.BVMax.liD y ≤ v 2 + li118 n := by
    have hh := (hv.mono (show Set.Icc (2 : ℝ) n ⊆ Set.Ici 2 from
      fun _ h => h.1)).sum_le_integral_Ico hn
    have he (m : ℕ) (hm : 2 ≤ m) :
        (∑ k ∈ Finset.Icc 2 m, v k) = v 2 + ∑ k ∈ Finset.Ico 2 m, v (k + 1) := by
      induction m, hm using Nat.le_induction with
      | base => simp
      | succ n hn ih =>
        rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Ico_succ_top hn, ih]
        simp only [Nat.cast_add, Nat.cast_one]
        ring
    rw [hs, he n hn]
    simpa [li118, v, Nat.cast_add, Nat.cast_one, add_comm] using add_le_add_left hh (v 2)
  have hv2 : v 2 ≤ 2 := by
    dsimp [v]
    rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    linarith [Real.log_two_gt_d9]
  rw [abs_of_nonneg (sub_nonneg.mpr ((hmono y (n + 1) hy hyn).trans hl))]
  have hh := hmono n y (by exact_mod_cast hn) hny
  linarith

/-- Page 599 Lemma 3. Bombieri Vinogradov with the paper's continuous Li normalization. -/
theorem bombieriVinogradov118_proved : BombieriVinogradov118 := by
  classical
  intro A hA
  obtain ⟨B₀, hB₀, K₀, hK₀⟩ := LeanLab.PNTPort.BVMax.bvPi A hA
  let B := B₀ + A + 1
  refine ⟨B, by dsimp [B]; linarith, max K₀ 0 + 3, by positivity,
    Real.exp 1, by linarith [Real.add_one_le_exp (1 : ℝ)], ?_⟩
  intro x hx
  have hx2 : 2 ≤ x := (show 2 ≤ Real.exp 1 by
    linarith [Real.add_one_le_exp (1 : ℝ)]).trans hx
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hL1 : 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos 1) hx
  let T (q : ℕ) : Finset (ℕ × ℕ) :=
    ((Finset.range (q + 2)) ×ˢ (Finset.range (⌊x⌋₊ + 1))).filter
      (fun a => Nat.Coprime a.1 q)
  let E (q : ℕ) (a : ℕ × ℕ) : ℝ :=
    |LeanLab.PNTPort.BVMax.piAP (a.2 : ℝ) q a.1 -
      LeanLab.PNTPort.BVMax.liD (a.2 : ℝ) / q.totient|
  have hne (q : ℕ) : (T q).Nonempty := by
    refine ⟨(1, 0), ?_⟩
    simp [T, Nat.coprime_one_left]
  have hm (q : ℕ) := Finset.exists_max_image (T q) (E q) (hne q)
  choose w hw hmax using hm
  have hcop (q : ℕ) : Nat.Coprime (w q).1 q := (Finset.mem_filter.mp (hw q)).2
  have hend (q : ℕ) : 0 ≤ ((w q).2 : ℝ) ∧ ((w q).2 : ℝ) ≤ x := by
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have hh := (Finset.mem_product.mp (Finset.mem_filter.mp (hw q)).1).2
    have hh' : (w q).2 ≤ ⌊x⌋₊ := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hh
    exact (Nat.cast_le.mpr hh').trans (Nat.floor_le hx0.le)
  have hsum := hK₀ x hx2 (fun q => (w q).1) hcop (fun q => ((w q).2 : ℝ)) hend
  have hBB : Real.log x ^ B₀ ≤ Real.log x ^ B :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by dsimp [B]; linarith)
  have hsub : Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) / Real.log x ^ B⌋₊ ⊆
      Finset.Icc 1 ⌊Real.sqrt x / Real.log x ^ B₀⌋₊ := by
    apply Finset.Icc_subset_Icc_right
    apply Nat.floor_le_floor
    rw [← Real.sqrt_eq_rpow]
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) hBB
  refine ⟨fun q => E q (w q) + 2, ?_, ?_⟩
  · intro q hq
    refine ⟨by dsimp [E]; positivity, ?_⟩
    intro l hl hcl y hy hyx
    have hmem : (l, ⌊y⌋₊) ∈ T q := by
      simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by have := Nat.floor_le_floor hyx; omega⟩, hcl⟩
    have hmax' := hmax q (l, ⌊y⌋₊) hmem
    have he : E q (l, ⌊y⌋₊) =
        |LeanLab.PNTPort.BVMax.piAP y q l - LeanLab.PNTPort.BVMax.liD y / q.totient| := by
      simp [E, LeanLab.PNTPort.BVMax.piAP, LeanLab.PNTPort.BVMax.liD]
    rw [he] at hmax'
    have hφ : (1 : ℝ) ≤ q.totient := by
      exact_mod_cast Nat.totient_pos.mpr (Finset.mem_Icc.mp hq).1
    have hcorr : |(LeanLab.PNTPort.BVMax.liD y - li118 y) / q.totient| ≤ 2 := by
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < q.totient)]
      exact (div_le_self (abs_nonneg _) hφ).trans (liD_sub_li118_bound y hy)
    rw [apCount118_eq_piAP]
    have heq : LeanLab.PNTPort.BVMax.piAP y q l - li118 y / q.totient =
        (LeanLab.PNTPort.BVMax.piAP y q l - LeanLab.PNTPort.BVMax.liD y / q.totient) +
          (LeanLab.PNTPort.BVMax.liD y - li118 y) / q.totient := by ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add hmax' hcorr)
  · rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul]
    have hsum' : ∑ q ∈ Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) / Real.log x ^ B⌋₊,
        E q (w q) ≤ K₀ * x / Real.log x ^ A :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => abs_nonneg _)).trans hsum
    have hBA : Real.log x ^ A ≤ Real.log x ^ B :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by dsimp [B]; linarith)
    have hQ : (⌊x ^ (1 / 2 : ℝ) / Real.log x ^ B⌋₊ : ℝ) ≤ x / Real.log x ^ A := by
      calc
        _ ≤ x ^ (1 / 2 : ℝ) / Real.log x ^ B := Nat.floor_le (by positivity)
        _ ≤ x / Real.log x ^ B := by
          rw [← Real.sqrt_eq_rpow]
          exact div_le_div_of_nonneg_right (Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))) (by positivity)
        _ ≤ x / Real.log x ^ A := div_le_div_of_nonneg_left hx0.le (by positivity) hBA
    have hh : 0 ≤ x / Real.log x ^ A := by positivity
    have hk : K₀ ≤ max K₀ 0 + 1 := by linarith [le_max_left K₀ 0]
    calc
      _ ≤ K₀ * x / Real.log x ^ A + (x / Real.log x ^ A) * 2 :=
        add_le_add hsum' (mul_le_mul_of_nonneg_right hQ (by norm_num))
      _ = (K₀ + 2) * (x / Real.log x ^ A) := by ring
      _ ≤ (max K₀ 0 + 3) * (x / Real.log x ^ A) :=
        mul_le_mul_of_nonneg_right (by linarith) hh
      _ = (max K₀ 0 + 3) * x / Real.log x ^ A := by ring

/-- Page 601 display 4.4. The coefficient has a strict reserve of five times ten to minus five. -/
theorem eq44_margin118 :
    let θ : ℝ := 0.95
    12.98975 ≤ 8 / θ ^ 2 * (Real.log (5.5 * θ - 1) +
      ∫ s in (2 : ℝ)..(5.5 * θ - 2),
        Real.log (s - 1) / s * Real.log ((5.5 * θ - 1) / (s + 1))) := by
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

/-- Pages 598 to 599 Lemma 2. The explicit sieve system supplies all four formulas. -/
theorem linear_sieve_formulas118 (F f : ℝ → ℝ)
    (h : LeanLab.ChenExplicit.IsLinearSieveFns F f) : Lemma2Formulas118 f F := by
  apply lemma2_from_delay118 f F h.1
  · exact continuousOn_id.mul (h.2.1.mono (by
      intro x hx; change 0 < x; linarith [hx.1]))
  · exact continuousOn_id.mul (h.2.2.1.mono (by
      intro x hx; change 0 < x; linarith [hx.1]))
  · intro x hx
    exact (h.2.2.2 x hx.1).1
  · intro x hx
    exact (h.2.2.2 x hx.1).2

/-- Page 601 before display 4.4. The logarithmic sieve parameter tends to 5.225. -/
theorem sieve_parameter_limit118 (B : ℝ) :
    Tendsto (fun N : ℕ =>
      log ((N : ℝ) ^ (0.95 / 2 : ℝ) / log N ^ B) / log ((N : ℝ) ^ (1 / 11 : ℝ)))
      atTop (𝓝 5.225) := by
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ => log (log (N : ℝ)) / log N) atTop (𝓝 0) :=
    isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have hh := ((tendsto_const_nhds.sub (hsmall.const_mul B)).div_const (1 / 11 : ℝ) :
    Tendsto (fun N : ℕ => ((0.95 / 2 : ℝ) - B * (log (log (N : ℝ)) / log N)) / (1 / 11 : ℝ))
      atTop (𝓝 (((0.95 / 2 : ℝ) - B * 0) / (1 / 11 : ℝ))))
  have hv : (((0.95 / 2 : ℝ) - B * 0) / (1 / 11 : ℝ)) = 5.225 := by ring
  rw [hv] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLp : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [log_div (rpow_pos_of_pos hNp _).ne' (rpow_pos_of_pos hLp B).ne',
    log_rpow hNp, log_rpow hLp, log_rpow hNp]
  field_simp

/-- Page 601 display 4.1. Dropping coprimality costs at most one term per prime divisor of N. -/
theorem asift_one_card_le118 (N : ℕ) (θ : ℝ) (hN : 0 < N) :
    (Asift N θ 1).card ≤ Ssift N θ + N.primeFactors.card := by
  classical
  have hsub : Asift N θ 1 ⊆ Pset N θ ∪ N.primeFactors := by
    intro p hp
    obtain ⟨hpN, hprime, hcut, _, hrough⟩ :=
      (show p < N ∧ p.Prime ∧ (p : ℝ) ≤ (N : ℝ) ^ θ ∧
        1 ∣ N - p ∧ ∀ r ∈ (N - p).primeFactors, (r : ℝ) < z1 N → ¬ r.Coprime N from by
          simpa only [Asift, Finset.mem_filter, Finset.mem_range] using hp)
    by_cases hcop : (N - p).Coprime N
    · apply Finset.mem_union_left
      simp only [Pset, Finset.mem_filter, Finset.mem_range]
      refine ⟨hpN, hprime, hcut, hcop, ?_⟩
      intro r hr
      by_contra hh
      have hdiv := Nat.dvd_of_mem_primeFactors hr
      exact hrough r hr (lt_of_not_ge hh) (hcop.coprime_dvd_left hdiv)
    · apply Finset.mem_union_right
      apply Nat.mem_primeFactors.mpr
      refine ⟨hprime, ?_, by omega⟩
      have hpcop : ¬ p.Coprime N := by
        simpa only [← Nat.coprime_self_sub_left hpN.le] using hcop
      exact not_not.mp (hprime.coprime_iff_not_dvd.not.mp hpcop)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Page 600 before display 4.2. The multiplicative density omega of d divided by d. -/
noncomputable def caiDensity118 : ArithmeticFunction ℝ :=
  ⟨fun d => 1 / (Nat.totient d : ℝ), by simp⟩

/-- Page 600. The reciprocal totient density is multiplicative. -/
theorem caiDensity118_multiplicative : caiDensity118.IsMultiplicative := by
  constructor
  · simp [caiDensity118]
  · intro m n hmn
    change 1 / (Nat.totient (m * n) : ℝ) =
      1 / (Nat.totient m : ℝ) * (1 / (Nat.totient n : ℝ))
    rw [Nat.totient_mul hmn, Nat.cast_mul]
    exact one_div_mul_one_div _ _ |>.symm

/-- Page 600 and page 601 display 4.3. The density is between zero and one at every sieving prime. -/
theorem caiDensity118_prime (N p : ℕ) (he : Even N) (hp : p.Prime) (hc : p.Coprime N) :
    0 ≤ caiDensity118 p ∧ caiDensity118 p < 1 := by
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) (dvd_refl 2)
      (even_iff_two_dvd.mp he)) hc
  have hpr : (2 : ℝ) < p := by exact_mod_cast (show 2 < p by have := hp.two_le; omega)
  change 0 ≤ 1 / (Nat.totient p : ℝ) ∧ 1 / (Nat.totient p : ℝ) < 1
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  constructor
  · exact div_nonneg zero_le_one (by linarith)
  · exact (div_lt_one (by linarith)).mpr (by linarith)

/-- Page 599 display 3.1. The actual finite sequence consists of N minus each prime at most N to theta. -/
noncomputable def caiSequence118 (N : ℕ) : Finset ℕ := by
  classical exact ((Finset.range N).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ (N : ℝ) ^ (0.95 : ℝ))).image (fun p : ℕ => N - p)

/-- Page 599 display 3.1. Membership in the finite sequence has the exact printed prime cutoff. -/
theorem mem_caiSequence118 (N a : ℕ) :
    a ∈ caiSequence118 N ↔ 0 < a ∧ a < N ∧ (N - a).Prime ∧
      ((N - a : ℕ) : ℝ) ≤ (N : ℝ) ^ (0.95 : ℝ) := by
  classical
  simp only [caiSequence118, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨p, ⟨hpN, hprime, hcut⟩, rfl⟩
    have hpp := hprime.pos
    have heq : N - (N - p) = p := by omega
    exact ⟨by omega, by omega, by simpa only [heq] using hprime, by simpa only [heq] using hcut⟩
  · rintro ⟨ha0, haN, hprime, hcut⟩
    refine ⟨N - a, ⟨by omega, hprime, hcut⟩, ?_⟩
    omega

/-- Page 599 display 3.1 and page 600. No zero occurs in the support for Theorem 6. -/
theorem zero_not_mem_caiSequence118 (N : ℕ) : 0 ∉ caiSequence118 N := by
  simp [mem_caiSequence118]

/-- Page 600 before display 4.2. The sequence mass equals the inclusive prime count. -/
theorem card_caiSequence118 (N : ℕ) (hN : 2 ≤ N) :
    (caiSequence118 N).card = apCount118 ((N : ℝ) ^ (0.95 : ℝ)) 1 0 := by
  classical
  let T : Finset ℕ := (Finset.range N).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ (N : ℝ) ^ (0.95 : ℝ))
  have hinj : Set.InjOn (N - ·) (T : Set ℕ) := by
    intro p hp q hq hpq
    dsimp only at hpq
    have hpN := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    have hqN := Finset.mem_range.mp (Finset.mem_filter.mp hq).1
    omega
  have hcard : (caiSequence118 N).card = T.card := by
    exact Finset.card_image_of_injOn hinj
  rw [hcard]
  unfold apCount118
  congr 1
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hpN : (N : ℝ) ^ (0.95 : ℝ) < N := by
    calc
      _ < (N : ℝ) ^ (1 : ℝ) := rpow_lt_rpow_of_exponent_lt hNr (by norm_num)
      _ = N := rpow_one _
  ext p
  simp only [T, Finset.mem_filter, Finset.mem_range, Nat.mod_one, and_true]
  constructor
  · rintro ⟨_, hprime, hcut⟩
    exact ⟨by have := Nat.le_floor hcut; omega, hprime⟩
  · rintro ⟨hp, hprime⟩
    have hcut : (p : ℝ) ≤ (N : ℝ) ^ (0.95 : ℝ) :=
      (Nat.cast_le.mpr (show p ≤ ⌊(N : ℝ) ^ (0.95 : ℝ)⌋₊ by omega)).trans
        (Nat.floor_le (rpow_nonneg (Nat.cast_nonneg _) _))
    have hpN' : p < N := by exact_mod_cast hcut.trans_lt hpN
    exact ⟨hpN', hprime, hcut⟩

/-- Page 601 display 4.1. Coprimality to the sieve prime product is the exact roughness condition. -/
theorem cai_sift_iff118 (N a : ℕ) (ha : 0 < a) :
    Nat.Coprime a
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn
        {p : ℕ | p.Prime ∧ p.Coprime N} (z1 N), p) ↔
      ∀ r ∈ a.primeFactors, (r : ℝ) < z1 N → ¬ r.Coprime N := by
  classical
  rw [Nat.coprime_prod_right_iff]
  constructor
  · intro h r hr hrz hc
    have hp := Nat.prime_of_mem_primeFactors hr
    have hd := Nat.dvd_of_mem_primeFactors hr
    have hm : r ∈ LeanLab.ChenExplicit.primesBelowIn
        {p : ℕ | p.Prime ∧ p.Coprime N} (z1 N) := by
      simp only [LeanLab.ChenExplicit.primesBelowIn, Finset.mem_filter, Finset.mem_range, Nat.lt_ceil,
        Set.mem_ofPred_eq]
      exact ⟨hrz, hp, hc⟩
    exact (hp.coprime_iff_not_dvd.mp (h r hm).symm) hd
  · intro h p hp
    have hm : (p : ℝ) < z1 N ∧ p.Prime ∧ p.Coprime N := by
      simpa only [LeanLab.ChenExplicit.primesBelowIn, Finset.mem_filter, Finset.mem_range, Nat.lt_ceil,
        Set.mem_ofPred_eq] using hp
    apply Nat.Coprime.symm
    apply hm.2.1.coprime_iff_not_dvd.mpr
    intro hd
    exact h p (Nat.mem_primeFactors.mpr ⟨hm.2.1, hd, ha.ne'⟩) hm.1 hm.2.2

/-- Page 603 display 4.11. Averaging reciprocal totients gives a tail with one extra logarithm. -/
theorem reciprocal_totient_tail118 :
    ∃ K : ℝ, 0 < K ∧ ∀ M : ℕ, 1 ≤ M → ∀ Q : ℕ,
      (∑ m ∈ Finset.Icc M Q, (1 : ℝ) / ((m : ℝ) * m.totient)) ≤
        K * (1 + log Q) / M := by
  obtain ⟨K, hK, hsum⟩ := LeanLab.PNTPort.BV.sum_inv_totient_le
  refine ⟨K, hK, fun M hM Q => ?_⟩
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  calc
    _ ≤ ∑ m ∈ Finset.Icc M Q, (1 / (M : ℝ)) * (1 / (m.totient : ℝ)) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [← one_div_mul_one_div]
      apply mul_le_mul_of_nonneg_right
      · exact one_div_le_one_div_of_le hMpos (by exact_mod_cast (Finset.mem_Icc.mp hm).1)
      · positivity
    _ = (1 / (M : ℝ)) * ∑ m ∈ Finset.Icc M Q, (1 / (m.totient : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (1 / (M : ℝ)) * ∑ m ∈ Finset.Icc 1 Q, (1 / (m.totient : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Icc_subset_Icc_left hM
      · intro m _ _; positivity
    _ ≤ (1 / (M : ℝ)) * (K * (1 + log Q)) :=
      mul_le_mul_of_nonneg_left (hsum Q) (by positivity)
    _ = _ := by ring

/-- Page 603 display 4.11 and page 604. An extra logarithm in the reciprocal totient tail is harmless. -/
theorem remainder_log_cube_small118 (η : ℝ) (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (N : ℝ) ^ (10 / 11 : ℝ) * (1 + log N) ^ 3 ≤
        η * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
  have hc := LeanLab.ChenExplicit.twinC_pos
  have ho : (fun n : ℕ => log (n : ℝ) ^ 5) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (9 / 220 : ℝ)) := by
    have h := (isLittleO_log_rpow_rpow_atTop (5 : ℝ)
      (s := 9 / 220) (by norm_num)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
    convert h using 1 <;> simp only [Function.comp_def]
    ext n
    exact (Real.rpow_natCast _ 5).symm
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp
    (ho.bound (show 0 < η * LeanLab.ChenExplicit.twinC / 8 by positivity))
  refine ⟨max n0 (max 2 ⌈exp 1⌉₊), fun N hN => ?_⟩
  have hn : n0 ≤ N := (le_max_left ..).trans hN
  have hN2 : 2 ≤ N := (le_max_left 2 _).trans ((le_max_right ..).trans hN)
  have heN : exp 1 ≤ (N : ℝ) := (Nat.le_ceil _).trans
    (Nat.cast_le.mpr ((le_max_right 2 _).trans ((le_max_right ..).trans hN)))
  have hL1 : 1 ≤ log (N : ℝ) := by simpa using log_le_log (exp_pos 1) heN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) ^ 2 := by positivity
  have hh := hn0 N hn
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
    abs_of_pos (rpow_pos_of_pos hNpos _)] at hh
  have hC : LeanLab.ChenExplicit.twinC ≤ C N := by
    unfold C
    exact le_mul_of_one_le_right hc.le (LeanLab.ChenExplicit.one_le_oddFactor N)
  have hpow : (N : ℝ) ^ (0.95 : ℝ) =
      (N : ℝ) ^ (10 / 11 : ℝ) * (N : ℝ) ^ (9 / 220 : ℝ) := by
    rw [← rpow_add hNpos]
    norm_num
  have hcube : (1 + log (N : ℝ)) ^ 3 * log N ^ 2 ≤ 8 * log N ^ 5 := by
    have hh : (1 + log (N : ℝ)) ^ 3 ≤ (2 * log N) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 3
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg (log (N : ℝ)))
    nlinarith only [hh']
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hlog).mpr
  calc
    _ = (N : ℝ) ^ (10 / 11 : ℝ) * ((1 + log N) ^ 3 * log N ^ 2) := by ring
    _ ≤ (N : ℝ) ^ (10 / 11 : ℝ) * (8 * log N ^ 5) :=
      mul_le_mul_of_nonneg_left hcube (rpow_pos_of_pos hNpos _).le
    _ ≤ (N : ℝ) ^ (10 / 11 : ℝ) *
        (8 * ((η * LeanLab.ChenExplicit.twinC / 8) * (N : ℝ) ^ (9 / 220 : ℝ))) := by
      gcongr
    _ = η * (LeanLab.ChenExplicit.twinC * (N : ℝ) ^ (0.95 : ℝ)) := by rw [hpow]; ring
    _ ≤ η * (C N * (N : ℝ) ^ (0.95 : ℝ)) := by gcongr

/-- Page 601 display 4.6. The remainder indices with one large prime and only small other factors have no repetitions. -/
theorem sieve_one_remainder_sum118 (T : Finset (ℕ × ℕ)) (z : ℝ) (D : ℕ)
    (hT : ∀ b ∈ T, b.1.Prime ∧ z ≤ (b.1 : ℝ) ∧ 0 < b.2 ∧
      (∀ p ∈ b.2.primeFactors, (p : ℝ) < z) ∧ b.1 * b.2 ≤ D)
    (R : ℕ → ℝ) (hR : ∀ m ∈ Finset.Icc 1 D, 0 ≤ R m) :
    (∑ b ∈ T, R (b.1 * b.2)) ≤ ∑ m ∈ Finset.Icc 1 D, R m := by
  classical
  have hinj : Set.InjOn (fun b : ℕ × ℕ => b.1 * b.2) (T : Set (ℕ × ℕ)) := by
    intro b hb c hc heq
    rcases b with ⟨q, d⟩
    rcases c with ⟨r, e⟩
    obtain ⟨hq, hqz, hd, hdf, _⟩ := hT (q, d) hb
    obtain ⟨hr, hrz, he, hef, _⟩ := hT (r, e) hc
    change q * d = r * e at heq
    have hdiv : q ∣ r * e := by rw [← heq]; exact dvd_mul_right q d
    rcases hq.dvd_mul.mp hdiv with hqr | hqe
    · have hqr' : q = r := (Nat.prime_dvd_prime_iff_eq hq hr).mp hqr
      subst r
      exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left hq.pos heq)
    · have hmem : q ∈ e.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqe, he.ne'⟩
      have hh := hef q hmem
      linarith
  have hsub : T.image (fun b => b.1 * b.2) ⊆ Finset.Icc 1 D := by
    intro m hm
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hm
    have hh := hT b hb
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hh.1.pos hh.2.2.1, hh.2.2.2.2⟩
  calc
    _ = ∑ m ∈ T.image (fun b => b.1 * b.2), R m := (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m hm _ => hR m hm)

/-- Page 601 display 4.1. The finite product sieve counts the same primes as Asift with q equal to one. -/
theorem cai_sifted_card118 (N : ℕ) :
    let PP : ℕ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn
      {p : ℕ | p.Prime ∧ p.Coprime N} (z1 N), p
    ((caiSequence118 N).filter (fun a => a.Coprime PP)).card = (Asift N 0.95 1).card := by
  classical
  dsimp only
  apply Finset.card_bij (fun a _ => N - a)
  · intro a ha
    obtain ⟨haseq, hcop⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha0, haN, hprime, hcut⟩ := (mem_caiSequence118 N a).mp haseq
    have hrough := (cai_sift_iff118 N a ha0).mp hcop
    have hback : N - (N - a) = a := by omega
    simp only [Asift, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, hprime, hcut, one_dvd _, ?_⟩
    simpa only [hback] using hrough
  · intro a ha b hb heq
    have haN := ((mem_caiSequence118 N a).mp (Finset.mem_filter.mp ha).1).2.1
    have hbN := ((mem_caiSequence118 N b).mp (Finset.mem_filter.mp hb).1).2.1
    change N - a = N - b at heq
    omega
  · intro p hp
    obtain ⟨hpN, hprime, hcut, _, hrough⟩ :=
      (show p < N ∧ p.Prime ∧ (p : ℝ) ≤ (N : ℝ) ^ (0.95 : ℝ) ∧
        1 ∣ N - p ∧ ∀ r ∈ (N - p).primeFactors, (r : ℝ) < z1 N → ¬ r.Coprime N from by
          simpa only [Asift, Finset.mem_filter, Finset.mem_range] using hp)
    have hp0 := hprime.pos
    have hback : N - (N - p) = p := by omega
    refine ⟨N - p, ?_, hback⟩
    apply Finset.mem_filter.mpr
    refine ⟨(mem_caiSequence118 N (N - p)).mpr ?_, ?_⟩
    · refine ⟨by omega, by omega, ?_, ?_⟩
      · simpa only [hback] using hprime
      · simpa only [hback] using hcut
    · exact (cai_sift_iff118 N (N - p) (by omega)).mpr hrough
/-- Page 601 display 4.4 before limits. Theorem 6 applies to the exact finite Cai sequence.
CONDITIONAL ON Theorem6Stmt, the global function system and the displayed dimension condition. -/
theorem cai_lower_of_theorem6_118
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt) (F f : ℝ → ℝ)
    (hFns : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (N : ℕ) (he : Even N) (hz : 2 ≤ z1 N)
    (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ 1 / 100000)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime ∧ q.Coprime N)
    (hdim : ∀ u : ℝ, 1 < u → u < z1 N →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn
        {p : ℕ | p.Prime ∧ p.Coprime N} (z1 N)).filter
          (fun p : ℕ => p ∉ Q ∧ u ≤ (p : ℝ)), (1 - caiDensity118 p)⁻¹ <
          (1 + ε) * (Real.log (z1 N) / Real.log u))
    (D : ℝ) (hD : (z1 N) ^ 2 ≤ D) :
    let PP : ℕ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn
      {p : ℕ | p.Prime ∧ p.Coprime N} (z1 N), p
    let s : ℝ := Real.log D / Real.log (z1 N)
    (f s - ε * 107 * Real.exp 2 * LeanLab.ChenExplicit.hSieve s) *
      ((caiSequence118 N).card : ℝ) *
        (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn
          {p : ℕ | p.Prime ∧ p.Coprime N} (z1 N), (1 - caiDensity118 p)) -
      (∑ d ∈ PP.divisors.filter (fun d : ℕ => (d : ℝ) < (∏ q ∈ Q, (q : ℝ)) * D),
        |(((caiSequence118 N).filter (fun n : ℕ => d ∣ n)).card : ℝ) -
          ((caiSequence118 N).card : ℝ) * caiDensity118 d|) ≤ (Asift N 0.95 1).card := by
  classical
  let A := caiSequence118 N
  let P : Set ℕ := {p : ℕ | p.Prime ∧ p.Coprime N}
  let a : ℕ → ℝ := fun n => if n ∈ A then 1 else 0
  have h := h6 F f hFns 100000 106 107 (by norm_num [LeanLab.ChenExplicit.table1])
    ε hε hεmax A a (zero_not_mem_caiSequence118 N)
    (fun n => by dsimp [a]; split_ifs <;> norm_num)
    (fun n hn => by simp [a, hn]) P (fun p hp => hp.1) (z1 N) hz
    (fun _ => caiDensity118) (fun _ => caiDensity118_multiplicative)
    (fun _ p hp => caiDensity118_prime N p he hp.1 hp.2)
    Q hQ (fun _ u hu huz => hdim u hu huz) D
  have hl := h.2 hD
  dsimp only at hl ⊢
  have ha (n : ℕ) (hn : n ∈ A) : a n = 1 := by simp [a, hn]
  have hS : (∑ n ∈ A, if n.Coprime
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P (z1 N), p) then a n else 0) =
      ((Asift N 0.95 1).card : ℝ) := by
    calc
      _ = ∑ n ∈ A, if n.Coprime
          (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P (z1 N), p) then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [ha n hn]
      _ = _ := by
        rw [Finset.sum_boole]
        exact_mod_cast cai_sifted_card118 N
  have hX : (∑ n ∈ A, a n * ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P (z1 N),
      (1 - caiDensity118 p)) = ((caiSequence118 N).card : ℝ) *
        ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P (z1 N), (1 - caiDensity118 p) := by
    calc
      _ = ∑ _n ∈ A, ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P (z1 N),
          (1 - caiDensity118 p) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [ha n hn, one_mul]
      _ = _ := by simp [A]
  have hr (d : ℕ) :
      (∑ n ∈ A, if d ∣ n then a n else 0) - (∑ n ∈ A, a n * caiDensity118 d) =
      (((caiSequence118 N).filter (fun n : ℕ => d ∣ n)).card : ℝ) -
        ((caiSequence118 N).card : ℝ) * caiDensity118 d := by
    have h1 : (∑ n ∈ A, if d ∣ n then a n else 0) =
        ∑ n ∈ A, if d ∣ n then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ha n hn]
    have h2 : (∑ n ∈ A, a n * caiDensity118 d) =
        ∑ _n ∈ A, caiDensity118 d := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ha n hn, one_mul]
    rw [h1, h2, Finset.sum_boole]
    simp [A]
  rw [hS, hX] at hl
  simp_rw [hr] at hl
  simpa only [P, mul_assoc, Nat.cast_ofNat] using hl

/-- CITED. Pages 603 to 604 display 4.13. Huxley's short interval theorem and partial summation.
Only the even sequence of N used in the paper is asserted. This is a paper statement requiring review. -/
def HuxleyDisplay413118 : Prop :=
  Tendsto (fun n : ℕ =>
    let N : ℕ := 2 * n
    (∑ e ∈ switchedE118 N,
      (li118 ((N : ℝ) / e) - li118 (((N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)) / e))) *
      log N / (N : ℝ) ^ (0.95 : ℝ)) atTop
      (𝓝 (∫ t in (2.29 : ℝ)..10, log (2.29 - 3.29 / (t + 1)) / t))

/-- Pages 603 to 604 display 4.13. The stated limit gives an upper main term with every positive reserve.
CONDITIONAL ON HuxleyDisplay413118. -/
theorem huxley_mainTerm_upper118 (hH : HuxleyDisplay413118) (δ : ℝ) (hδ : 0 < δ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      let N : ℕ := 2 * n
      (∑ e ∈ switchedE118 N,
        (li118 ((N : ℝ) / e) - li118 (((N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)) / e))) ≤
        ((∫ t in (2.29 : ℝ)..10, log (2.29 - 3.29 / (t + 1)) / t) + δ) *
          (N : ℝ) ^ (0.95 : ℝ) / log N := by
  have hlim := hH.eventually (eventually_lt_nhds (show
    (∫ t in (2.29 : ℝ)..10, log (2.29 - 3.29 / (t + 1)) / t) <
      (∫ t in (2.29 : ℝ)..10, log (2.29 - 3.29 / (t + 1)) / t) + δ by linarith))
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp hlim
  refine ⟨max n0 1, fun n hn => ?_⟩
  have hnn : n0 ≤ n := (le_max_left ..).trans hn
  have hn1 : 1 ≤ n := (le_max_right ..).trans hn
  have hN : (1 : ℝ) < (2 * n : ℕ) := by exact_mod_cast (show 1 < 2 * n by omega)
  have hL : 0 < log ((2 * n : ℕ) : ℝ) := log_pos hN
  have hp : 0 < ((2 * n : ℕ) : ℝ) ^ (0.95 : ℝ) := rpow_pos_of_pos (by linarith) _
  have hh := (lt_div_iff₀ hL).mpr ((div_lt_iff₀ hp).mp (hn0 n hnn))
  exact hh.le

/-- Page 603 display 4.11. The finite divisor rearrangement has an adequate logarithmic tail bound. -/
theorem reciprocal_totient_divisor_tail118 :
    ∃ K : ℝ, 0 < K ∧ ∀ M : ℕ, 1 ≤ M → ∀ D : ℕ,
      (∑ d ∈ Finset.Icc 1 D, (1 / (d.totient : ℝ)) *
        ∑ m ∈ d.divisors.filter (fun m => M ≤ m), (1 / (m : ℝ))) ≤
          K * (1 + log D) ^ 2 / M := by
  classical
  obtain ⟨K1, hK1, htail⟩ := reciprocal_totient_tail118
  obtain ⟨K2, hK2, hsum⟩ := LeanLab.PNTPort.BV.sum_inv_totient_le
  refine ⟨K1 * K2, mul_pos hK1 hK2, fun M hM D => ?_⟩
  let L : ℝ := 1 + log D
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hrearr :
      (∑ d ∈ Finset.Icc 1 D, (1 / (d.totient : ℝ)) *
        ∑ m ∈ d.divisors.filter (fun m => M ≤ m), (1 / (m : ℝ))) =
      ∑ m ∈ Finset.Icc M D, (1 / (m : ℝ)) *
        ∑ d ∈ (Finset.Icc 1 D).filter (fun d => m ∣ d), (1 / (d.totient : ℝ)) := by
    have hf (d : ℕ) (hd : d ∈ Finset.Icc 1 D) :
        d.divisors.filter (fun m => M ≤ m) = (Finset.Icc M D).filter (fun m => m ∣ d) := by
      have hd0 : d ≠ 0 := by have := (Finset.mem_Icc.mp hd).1; omega
      ext m
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hmd, _⟩, hMm⟩
        have hmD := (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hmd).trans (Finset.mem_Icc.mp hd).2
        exact ⟨⟨hMm, hmD⟩, hmd⟩
      · rintro ⟨⟨hMm, _⟩, hmd⟩
        exact ⟨⟨hmd, hd0⟩, hMm⟩
    calc
      _ = ∑ d ∈ Finset.Icc 1 D, ∑ m ∈ Finset.Icc M D,
          if m ∣ d then (1 / (d.totient : ℝ)) * (1 / (m : ℝ)) else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [hf d hd, Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        split_ifs <;> simp
      _ = ∑ m ∈ Finset.Icc M D, ∑ d ∈ Finset.Icc 1 D,
          if m ∣ d then (1 / (d.totient : ℝ)) * (1 / (m : ℝ)) else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        split_ifs <;> simp [mul_comm]
  rw [hrearr]
  calc
    _ ≤ ∑ m ∈ Finset.Icc M D, (1 / (m : ℝ)) *
        ((1 / (m.totient : ℝ)) * ∑ d ∈ Finset.Icc 1 D, (1 / (d.totient : ℝ))) := by
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact LeanLab.PNTPort.BV.sum_dvd_inv_totient_le
        (hM.trans (Finset.mem_Icc.mp hm).1) D
    _ = (∑ m ∈ Finset.Icc M D, (1 : ℝ) / ((m : ℝ) * m.totient)) *
        ∑ d ∈ Finset.Icc 1 D, (1 / (d.totient : ℝ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ ≤ (K1 * L / M) * (K2 * L) := by
      apply mul_le_mul (htail M hM D) (hsum D)
      · exact Finset.sum_nonneg fun _ _ => by positivity
      · positivity
    _ = K1 * K2 * (1 + log D) ^ 2 / M := by dsimp [L]; ring

/-- Page 602 display 4.7. The exact polynomial certificate leaves a strict upper reserve. -/
theorem eq47_margin118 :
    let θ : ℝ := 0.95
  8 / θ ^ 2 * (Real.log ((11 * θ - 2) / (3.29 * θ - 2)) +
    ∫ s in (2 : ℝ)..(5.5 * θ - 2),
      Real.log (s - 1) / s * Real.log ((5.5 * θ - 1) * (5.5 * θ - 1 - s) / (s + 1))) ≤ 18.73465 := by
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


/-- Page 604 display 4.14. The exact polynomial certificate leaves a strict upper reserve. -/
theorem eq414_margin118 :
    let θ : ℝ := 0.95
  8 / (2 * θ - 1) * ∫ t in (2.29 : ℝ)..10, Real.log (2.29 - 3.29 / (t + 1)) / t ≤ 6.8085 := by
  simp only
  rw [change_var]
  have hab : (1 / 11 : ℝ) ≤ 100 / 329 := by norm_num
  have hmono : ∫ s in (1 / 11 : ℝ)..(100 / 329), Real.log (2.29 - 3.29 * s) * (1 / s + 1 / (1 - s))
      ≤ ∫ s in (1 / 11 : ℝ)..(100 / 329), Qv (vf s) * (1 / s + 1 / (1 - s)) := by
    apply intervalIntegral.integral_mono_on hab (h_cont.intervalIntegrable_of_Icc hab)
      (Q_cont.intervalIntegrable_of_Icc hab)
    intro s hs
    have hw : 0 ≤ 1 / s + 1 / (1 - s) := by
      have h1 : (1 / 11 : ℝ) ≤ s := hs.1
      have h2 : s ≤ (100 / 329 : ℝ) := hs.2
      have : 0 < 1 - s := by linarith
      have : 0 < s := by linarith
      positivity
    exact mul_le_mul_of_nonneg_right (log_le_Qv hs) hw
  have hsplit : ∫ s in (1 / 11 : ℝ)..(100 / 329), Qv (vf s) * (1 / s + 1 / (1 - s)) =
      (∫ s in (1 / 11 : ℝ)..(100 / 329), Rp s) + Qv (vf 0) * (∫ s in (1 / 11 : ℝ)..(100 / 329), s⁻¹)
        + Qv (vf 1) * (∫ s in (1 / 11 : ℝ)..(100 / 329), (1 - s)⁻¹) := by
    have hc : ∫ s in (1 / 11 : ℝ)..(100 / 329), Qv (vf s) * (1 / s + 1 / (1 - s)) =
        ∫ s in (1 / 11 : ℝ)..(100 / 329), (Rp s + Qv (vf 0) * s⁻¹ + Qv (vf 1) * (1 - s)⁻¹) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hab] at hs
      have h1 : (1 / 11 : ℝ) ≤ s := hs.1
      have h2 : s ≤ (100 / 329 : ℝ) := hs.2
      exact split_Q (by intro h'; linarith) (by intro h'; linarith)
    rw [hc]
    have iR : IntervalIntegrable Rp MeasureTheory.volume (1 / 11 : ℝ) (100 / 329) := by
      apply Continuous.intervalIntegrable; unfold Rp; fun_prop
    have i1 := (inv_cont.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab).const_mul (Qv (vf 0))
    have i2 := (inv1_cont.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab).const_mul (Qv (vf 1))
    rw [intervalIntegral.integral_add (iR.add i1) i2, intervalIntegral.integral_add iR i1,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hinv : ∫ s in (1 / 11 : ℝ)..(100 / 329), s⁻¹ = Real.log (1100 / 329) := by
    rw [integral_inv_of_pos (by norm_num) (by norm_num)]; norm_num
  have hinv1 : ∫ s in (1 / 11 : ℝ)..(100 / 329), (1 - s)⁻¹ = Real.log (3290 / 2519) := by
    rw [intervalIntegral.integral_comp_sub_left (fun x => x⁻¹) (1 : ℝ),
      integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  rw [hsplit, hinv, hinv1, integral_Rp] at hmono
  have hQ0 : 0 < Qv (vf 0) := by unfold Qv vf; norm_num
  have hQ1 : 0 < Qv (vf 1) := by unfold Qv vf; norm_num
  have l1 := mul_le_mul_of_nonneg_left log_ba_le hQ0.le
  have l2 := mul_le_mul_of_nonneg_left log_r2_le hQ1.le
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, rC] at hmono
  norm_num [Qv, vf] at hmono l1 l2
  norm_num
  linarith


/-- Page 604 display 4.15. The exact polynomial certificate leaves a strict upper reserve. -/
theorem eq415_margin118 :
    let θ : ℝ := 0.95
  8 / (2 * θ - 1) * ∫ t in (2 : ℝ)..2.29, Real.log (t - 1) / t ≤ 0.15635 := by
  simp only
  have hcont : ContinuousOn (fun t : ℝ => Real.log (t - 1) / t) (Set.uIcc 2 2.29) := by
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.div
    · apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
      intro t ht; show t - 1 ≠ 0; have := ht.1; intro h'; linarith
    · exact continuousOn_id
    · intro t ht; have := ht.1; intro h'; linarith
  have hI : ∫ t in (2 : ℝ)..2.29, Real.log (t - 1) / t ≤
      ∫ t in (2 : ℝ)..2.29, Lp (t - 2) * Qp (t - 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable)
    · apply Continuous.intervalIntegrable
      unfold Lp Qp; fun_prop
    · intro t ht; exact integrand_le ht
  have hJ : ∫ t in (2 : ℝ)..2.29, Lp (t - 2) * Qp (t - 2) =
      ∫ u in (0 : ℝ)..0.29, Lp u * Qp u := by
    rw [intervalIntegral.integral_comp_sub_right (fun u => Lp u * Qp u)]
    norm_num
  rw [hJ, integral_LpQp] at hI
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cP] at hI
  norm_num at hI
  have h8 : (0 : ℝ) < 8 / (2 * 0.95 - 1) := by norm_num
  calc 8 / (2 * (0.95 : ℝ) - 1) * ∫ t in (2 : ℝ)..2.29, Real.log (t - 1) / t
      ≤ 8 / (2 * 0.95 - 1) * (∫ t in (2 : ℝ)..2.29, Real.log (t - 1) / t) := le_refl _
    _ ≤ 0.15635 := by
      have := mul_le_mul_of_nonneg_left hI h8.le
      norm_num at this ⊢
      linarith




/-- Pages 600 to 601 display 4.2. Divisibility in the actual sequence is exactly prime progression counting. -/
theorem card_caiSequence118_dvd (N d : ℕ) (hN : 2 ≤ N) :
    ((caiSequence118 N).filter (fun a => d ∣ a)).card =
      apCount118 ((N : ℝ) ^ (0.95 : ℝ)) d N := by
  classical
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hpN : (N : ℝ) ^ (0.95 : ℝ) < N := by
    calc
      _ < (N : ℝ) ^ (1 : ℝ) := rpow_lt_rpow_of_exponent_lt hNr (by norm_num)
      _ = N := rpow_one _
  unfold apCount118
  apply Finset.card_bij (fun a _ => N - a)
  · intro a ha
    obtain ⟨haseq, hd⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha0, haN, hprime, hcut⟩ := (mem_caiSequence118 N a).mp haseq
    have hback : N - (N - a) = a := by omega
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by have := Nat.le_floor hcut; omega, hprime, ?_⟩
    apply (Nat.modEq_iff_dvd' (show N - a ≤ N by omega)).mpr
    simpa only [hback] using hd
  · intro a ha b hb heq
    have haN := ((mem_caiSequence118 N a).mp (Finset.mem_filter.mp ha).1).2.1
    have hbN := ((mem_caiSequence118 N b).mp (Finset.mem_filter.mp hb).1).2.1
    change N - a = N - b at heq
    omega
  · intro p hp
    obtain ⟨hpfl, hprime, hmod⟩ := (show p < ⌊(N : ℝ) ^ (0.95 : ℝ)⌋₊ + 1 ∧
        p.Prime ∧ p % d = N % d from by simpa only [Finset.mem_filter, Finset.mem_range] using hp)
    have hcut : (p : ℝ) ≤ (N : ℝ) ^ (0.95 : ℝ) :=
      (Nat.cast_le.mpr (show p ≤ ⌊(N : ℝ) ^ (0.95 : ℝ)⌋₊ by omega)).trans
        (Nat.floor_le (rpow_nonneg (Nat.cast_nonneg _) _))
    have hpless : p < N := by exact_mod_cast hcut.trans_lt hpN
    have hp0 := hprime.pos
    have hback : N - (N - p) = p := by omega
    refine ⟨N - p, Finset.mem_filter.mpr ⟨?_, ?_⟩, hback⟩
    · apply (mem_caiSequence118 N (N - p)).mpr
      refine ⟨by omega, by omega, ?_, ?_⟩
      · simpa only [hback] using hprime
      · simpa only [hback] using hcut
    · exact (Nat.modEq_iff_dvd' hpless.le).mp hmod
/-- Page 601 display 4.2 with prime count mass as required by Theorem 6.
The actual sequence remainders have an unconditional Bombieri Vinogradov bound. -/
theorem cai_remainder_level118 (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 4 ≤ N →
      (∑ d ∈ (Finset.Icc 1 ⌊Real.sqrt ((N : ℝ) ^ (0.95 : ℝ)) /
          log ((N : ℝ) ^ (0.95 : ℝ)) ^ B⌋₊).filter (fun d => N.Coprime d),
        |(((caiSequence118 N).filter (fun n => d ∣ n)).card : ℝ) -
          ((caiSequence118 N).card : ℝ) * caiDensity118 d|) ≤
        K * (N : ℝ) ^ (0.95 : ℝ) / log ((N : ℝ) ^ (0.95 : ℝ)) ^ A := by
  classical
  obtain ⟨B, hB, K, hK⟩ := LeanLab.PNTPort.BVMax.bvPiPi A hA
  refine ⟨B, hB, max K 0 + 1, by positivity, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hx : 2 ≤ (N : ℝ) ^ (0.95 : ℝ) := by
    calc
      2 = (4 : ℝ) ^ (1 / 2 : ℝ) := by rw [← sqrt_eq_rpow]; norm_num
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := rpow_le_rpow (by norm_num)
        (by exact_mod_cast hN) (by norm_num)
      _ ≤ (N : ℝ) ^ (0.95 : ℝ) := rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  let a : ℕ → ℕ := fun d => if N.Coprime d then N else 1
  have ha (d : ℕ) : (a d).Coprime d := by
    dsimp [a]
    split_ifs with h
    · exact h
    · exact Nat.coprime_one_left _
  have hh := hK ((N : ℝ) ^ (0.95 : ℝ)) hx a ha
    (fun _ => (N : ℝ) ^ (0.95 : ℝ)) (fun _ => ⟨by positivity, le_rfl⟩)
  have hsub :
      (∑ d ∈ (Finset.Icc 1 ⌊Real.sqrt ((N : ℝ) ^ (0.95 : ℝ)) /
          log ((N : ℝ) ^ (0.95 : ℝ)) ^ B⌋₊).filter (fun d => N.Coprime d),
        |(((caiSequence118 N).filter (fun n => d ∣ n)).card : ℝ) -
          ((caiSequence118 N).card : ℝ) * caiDensity118 d|) ≤
      ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt ((N : ℝ) ^ (0.95 : ℝ)) /
          log ((N : ℝ) ^ (0.95 : ℝ)) ^ B⌋₊,
        |LeanLab.PNTPort.BVMax.piAP ((N : ℝ) ^ (0.95 : ℝ)) d (a d) -
          LeanLab.PNTPort.BVMax.piAP ((N : ℝ) ^ (0.95 : ℝ)) 1 1 / d.totient| := by
    calc
      _ = ∑ d ∈ (Finset.Icc 1 ⌊Real.sqrt ((N : ℝ) ^ (0.95 : ℝ)) /
          log ((N : ℝ) ^ (0.95 : ℝ)) ^ B⌋₊).filter (fun d => N.Coprime d),
          |LeanLab.PNTPort.BVMax.piAP ((N : ℝ) ^ (0.95 : ℝ)) d (a d) -
            LeanLab.PNTPort.BVMax.piAP ((N : ℝ) ^ (0.95 : ℝ)) 1 1 / d.totient| := by
        apply Finset.sum_congr rfl
        intro d hd
        have hc := (Finset.mem_filter.mp hd).2
        rw [card_caiSequence118_dvd N d hN2, card_caiSequence118 N hN2,
          apCount118_eq_piAP, apCount118_eq_piAP]
        have hmass : LeanLab.PNTPort.BVMax.piAP ((N : ℝ) ^ (0.95 : ℝ)) 1 0 =
            LeanLab.PNTPort.BVMax.piAP ((N : ℝ) ^ (0.95 : ℝ)) 1 1 := by
          simp [LeanLab.PNTPort.BVMax.piAP, LeanLab.PNTPort.BVMax.piN]
        rw [hmass]
        simp only [a, ite_eq_left hc]
        congr 1
        change _ - _ * (1 / (d.totient : ℝ)) = _ - _ / (d.totient : ℝ)
        ring
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => abs_nonneg _)
  have hLpos : 0 < log ((N : ℝ) ^ (0.95 : ℝ)) := log_pos (by linarith [hx])
  refine (hsub.trans hh).trans ?_
  rw [mul_div_assoc, mul_div_assoc]
  apply mul_le_mul_of_nonneg_right (by linarith [le_max_left K 0])
  positivity

/-- LEAF. Page 597 definition of C and page 604 final comparison.
The main scale is strictly positive once N is at least two. -/
theorem leaf118_scale_pos (N : ℕ) (hN : 2 ≤ N) :
    0 < C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2 := by
  have hC : 0 < C N := by
    unfold C
    exact mul_pos LeanLab.ChenExplicit.twinC_pos
      (lt_of_lt_of_le zero_lt_one (LeanLab.ChenExplicit.one_le_oddFactor N))
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact div_pos (mul_pos hC (Real.rpow_pos_of_pos (by linarith) _))
    (sq_pos_of_pos (Real.log_pos hNr))

/-- Page 601 display 4.4 and BJS Theorem 6. A positive epsilon fits inside the strict reserve. -/
theorem sieve_epsilon_margin118 (loss : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 100000 ∧
      12.9897 + ε * loss <
        8 / (0.95 : ℝ) ^ 2 * (log (5.5 * 0.95 - 1) +
          ∫ s in (2 : ℝ)..(5.5 * 0.95 - 2),
            log (s - 1) / s * log ((5.5 * 0.95 - 1) / (s + 1))) := by
  let ε := min (1 / 100000 : ℝ) (0.000025 / (|loss| + 1))
  have hden : 0 < |loss| + 1 := by positivity
  have he : 0 < ε := lt_min (by norm_num) (div_pos (by norm_num) hden)
  have hel : ε ≤ 0.000025 / (|loss| + 1) := min_le_right _ _
  have hbound : ε * (|loss| + 1) ≤ 0.000025 := (le_div_iff₀ hden).mp hel
  have hl : loss ≤ |loss| + 1 := by linarith [le_abs_self loss]
  have hm : ε * loss ≤ 0.000025 := (mul_le_mul_of_nonneg_left hl he.le).trans hbound
  refine ⟨ε, he, min_le_left _ _, ?_⟩
  have h := eq44_margin118
  dsimp at h
  linarith

/-- Pages 599 and 601. Integration by parts converts the lower sieve nested integral to display 4.4. -/
theorem nested_integral44_118 :
    (∫ t in (3 : ℝ)..4.225, (1 / t) *
      ∫ u in (2 : ℝ)..(t - 1), log (u - 1) / u) =
    ∫ u in (2 : ℝ)..3.225, log (u - 1) / u * log (4.225 / (u + 1)) := by
  let v : ℝ → ℝ := fun u => log (u - 1) / u
  let G : ℝ → ℝ := fun t => ∫ u in (2 : ℝ)..(t - 1), v u
  have hv (u : ℝ) (hu : 1 < u) : ContinuousAt v u := by
    exact (((continuousAt_id.sub continuousAt_const).log (by dsimp; linarith)).div
      continuousAt_id (by dsimp; linarith))
  have hvi (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
      IntervalIntegrable v MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    apply (hv x ?_).continuousWithinAt
    rw [Set.mem_uIcc] at hx
    rcases hx with hx | hx <;> linarith [hx.1]
  have hmeas : Measurable v := by dsimp [v]; fun_prop
  have hG (t : ℝ) (ht : 2 < t) : HasDerivAt G (v (t - 1)) t := by
    have hh := (integral_hasDerivAt_right (hvi 2 (t - 1) (by norm_num) (by linarith))
      hmeas.aestronglyMeasurable.stronglyMeasurableAtFilter
      (hv (t - 1) (by linarith))).comp t ((hasDerivAt_id t).sub_const 1)
    convert! hh using 1 <;> simp only [mul_one]
  have hu' : IntervalIntegrable (fun t => v (t - 1)) MeasureTheory.volume (3 : ℝ) 4.225 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    intro t ht
    exact (ContinuousAt.comp (f := fun x : ℝ => x - 1) (x := t)
      (hv (t - 1) (by linarith [ht.1]))
      (continuousAt_id.sub continuousAt_const)).continuousWithinAt
  have hv' : IntervalIntegrable (fun t : ℝ => t⁻¹) MeasureTheory.volume (3 : ℝ) 4.225 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact continuousOn_id.inv₀ (by intro t ht; dsimp; linarith [ht.1])
  have hip := integral_mul_deriv_eq_deriv_mul
    (u := G) (v := log) (u' := fun t => v (t - 1)) (v' := fun t => t⁻¹)
    (fun t ht => hG t (by rw [Set.uIcc_of_le (by norm_num)] at ht; linarith [ht.1]))
    (fun t ht => hasDerivAt_log (by rw [Set.uIcc_of_le (by norm_num)] at ht; linarith [ht.1]))
    hu' hv'
  have hG3 : G 3 = 0 := by norm_num [G]
  have hG4 : G 4.225 = ∫ u in (2 : ℝ)..3.225, v u := by norm_num [G]
  have hcv : (∫ t in (3 : ℝ)..4.225, v (t - 1) * log t) =
      ∫ u in (2 : ℝ)..3.225, v u * log (u + 1) := by
    have hh := integral_comp_sub_right (fun u => v u * log (u + 1)) 1 (a := 3) (b := 4.225)
    simpa only [sub_add_cancel, show (3 : ℝ) - 1 = 2 by norm_num,
      show (4.225 : ℝ) - 1 = 3.225 by norm_num] using hh
  rw [hG3, hG4, hcv, zero_mul, sub_zero] at hip
  have hlog (u : ℝ) (hu : u ∈ uIcc (2 : ℝ) 3.225) :
      log (4.225 / (u + 1)) = log 4.225 - log (u + 1) := by
    rw [Set.uIcc_of_le (by norm_num)] at hu
    exact log_div (by norm_num) (by linarith [hu.1])
  calc
    _ = ∫ t in (3 : ℝ)..4.225, G t * t⁻¹ := by
      apply integral_congr; intro t _; dsimp [G, v]; ring
    _ = (∫ u in (2 : ℝ)..3.225, v u) * log 4.225 -
        ∫ u in (2 : ℝ)..3.225, v u * log (u + 1) := hip
    _ = ∫ u in (2 : ℝ)..3.225, v u * log 4.225 - v u * log (u + 1) := by
      rw [integral_sub, integral_mul_const]
      · exact (hvi 2 3.225 (by norm_num) (by norm_num)).mul_const _
      · apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
        intro u hu
        exact ((hv u (by linarith [hu.1])).mul
          ((continuousAt_id.add continuousAt_const).log (by dsimp; linarith [hu.1]))).continuousWithinAt
    _ = _ := by
      apply integral_congr
      intro u hu
      dsimp only
      rw [hlog u hu]
      dsimp [v]
      ring
/-- Pages 599 and 601 display 4.4. The lower sieve coefficient has the paper's normalization.
CONDITIONAL ON the linear sieve function system. -/
theorem lower_sieve_coefficient118 (F f : ℝ → ℝ)
    (h : LeanLab.ChenExplicit.IsLinearSieveFns F f) :
    22 / (0.95 : ℝ) * exp (-eulerMascheroniConstant) * f 5.225 =
      8 / (0.95 : ℝ) ^ 2 * (log (5.5 * 0.95 - 1) +
        ∫ s in (2 : ℝ)..(5.5 * 0.95 - 2),
          log (s - 1) / s * log ((5.5 * 0.95 - 1) / (s + 1))) := by
  have hf : f (5.225 : ℝ) = 2 * exp eulerMascheroniConstant / 5.225 *
      (log 4.225 + ∫ t in (3 : ℝ)..4.225, (1 / t) *
        ∫ u in (2 : ℝ)..(t - 1), log (u - 1) / u) := by
    convert (linear_sieve_formulas118 F f h).2.2.2 (5.225 : ℝ) (by norm_num) using 1 <;> norm_num
  rw [hf, nested_integral44_118, exp_neg]
  norm_num only [show (5.5 : ℝ) * 0.95 - 1 = 4.225 by norm_num,
    show (5.5 : ℝ) * 0.95 - 2 = 3.225 by norm_num]
  field_simp
  <;> ring

/-- Page 601 display 4.4 and BJS Theorem 6 Table 1. The explicit lower sieve retains a strict margin.
CONDITIONAL ON the linear sieve function system. -/
theorem explicit_lower_epsilon118 (F f : ℝ → ℝ)
    (h : LeanLab.ChenExplicit.IsLinearSieveFns F f) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 100000 ∧
      12.9897 < 22 / (0.95 : ℝ) * exp (-eulerMascheroniConstant) *
        (f 5.225 - ε * 107 * exp 2 * LeanLab.ChenExplicit.hSieve 5.225) := by
  obtain ⟨ε, he, hemax, hmargin⟩ := sieve_epsilon_margin118
    (22 / (0.95 : ℝ) * exp (-eulerMascheroniConstant) *
      (107 * exp 2 * LeanLab.ChenExplicit.hSieve 5.225))
  rw [← lower_sieve_coefficient118 F f h] at hmargin
  refine ⟨ε, he, hemax, ?_⟩
  have heq : 22 / (0.95 : ℝ) * exp (-eulerMascheroniConstant) *
      (f 5.225 - ε * 107 * exp 2 * LeanLab.ChenExplicit.hSieve 5.225) =
      22 / (0.95 : ℝ) * exp (-eulerMascheroniConstant) * f 5.225 -
        ε * (22 / (0.95 : ℝ) * exp (-eulerMascheroniConstant) *
          (107 * exp 2 * LeanLab.ChenExplicit.hSieve 5.225)) := by ring
  rw [heq]
  linarith


/-- Page 601 display 4.4. The strict reserve absorbs an arbitrary small additive coefficient loss.
CONDITIONAL on the displayed asymptotic lower estimate for a sequence a. -/
theorem sieve_lower_of_asymptotic118 (a : ℕ → ℝ)
    (h : ∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (8 / (0.95 : ℝ) ^ 2 * (log (5.5 * 0.95 - 1) +
        ∫ s in (2 : ℝ)..(5.5 * 0.95 - 2),
          log (s - 1) / s * log ((5.5 * 0.95 - 1) / (s + 1))) - δ) *
        (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) ≤ a N) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      12.9897 * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) ≤ a N := by
  obtain ⟨N0, hN0⟩ := h 0.00005 (by norm_num)
  refine ⟨max N0 2, fun N he hN => ?_⟩
  have hn0 : N0 ≤ N := (le_max_left ..).trans hN
  have hn2 : 2 ≤ N := (le_max_right ..).trans hN
  have hp := (leaf118_scale_pos N hn2).le
  have hc := eq44_margin118
  dsimp at hc
  have hd : 12.9897 ≤ 8 / (0.95 : ℝ) ^ 2 * (log (5.5 * 0.95 - 1) +
      ∫ s in (2 : ℝ)..(5.5 * 0.95 - 2),
        log (s - 1) / s * log ((5.5 * 0.95 - 1) / (s + 1))) - 0.00005 := by linarith
  exact (mul_le_mul_of_nonneg_right hd hp).trans (hN0 N he hn0)

/-- Page 601 display 4.3. Mertens normalization at Cai's lower sieve cutoff.
CONDITIONAL ON the ordinary Mertens product limit. -/
theorem mertens_normalization118
    (hM : Tendsto (fun z : ℝ =>
      (∏ p ∈ (range ⌈z⌉₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) * log z)
      atTop (𝓝 (exp (-eulerMascheroniConstant)))) :
    Tendsto (fun N : ℕ =>
      (∏ p ∈ (range N).filter (fun p : ℕ =>
          p.Prime ∧ 2 < p ∧ (p : ℝ) < z1 N ∧ ¬ p ∣ N),
        (1 - 1 / ((p : ℝ) - 1))) * log (z1 N) /
          (2 * exp (-eulerMascheroniConstant) * C N)) atTop (𝓝 1) := by
  have h := LeanLab.AlmostPrimeSums.Decomp1527c.mertens_twin_of_euler_product
    (1 / 11 : ℝ) (by norm_num) (by norm_num) hM
  have he (N : ℕ) : LeanLab.ChenExplicit.U N =
      2 * exp (-eulerMascheroniConstant) * C N := by
    unfold LeanLab.ChenExplicit.U C
    ring
  convert h using 1
  simp only [he, z1]
  funext N
  congr 3

/-- Page 601 display 4.3. The Mertens normalization constant equals the sieve local product.
This is the exact constant matching used before applying the limiting product. -/
theorem mertens_constant118 (N : ℕ) (hN : N ≠ 0) (he : Even N) :
    exp (-eulerMascheroniConstant) *
      (sieveLocal118 N 2 *
        (∏' p : {p : ℕ // p.Prime ∧ 2 < p}, sieveLocal118 N p)) =
      2 * exp (-eulerMascheroniConstant) * C N := by
  rw [sieve_constant118 N hN he]
  ring

/-- Pages 599 and 603 Lemma 4. The actual switched coefficient satisfies Wu's hypothesis. -/
theorem wu_coefficient118 (N : ℕ) :
    (fun x : ℝ => ∑ a ∈ Finset.Icc 1 ⌊x⌋₊, (switchedMultiplicity118 N a : ℝ) ^ 2 / (a : ℝ))
      =O[atTop] (fun x : ℝ => log x ^ (1 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop (exp 1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    apply sum_nonneg; intro a ha; positivity), Real.rpow_one,
    Real.norm_eq_abs, abs_of_nonneg (log_nonneg (by
      exact (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hx))]
  exact switchedMultiplicity118_log_bound N x hx

/-- Pages 603 to 604 display 4.12. Wu's theorem specializes to the actual switched coefficient.
CONDITIONAL ON WuMeanValue118. Constants remain dependent on N as in the cited statement. -/
theorem wu_specialization118 (hWu : WuMeanValue118) :
    ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ,
      ∃ K : ℝ, 0 < K ∧ ∃ x0 : ℝ, 2 ≤ x0 ∧
        ∀ x : ℝ, x0 ≤ x → ∃ R : ℕ → ℝ,
          (∀ d ∈ Finset.Icc 1 ⌊x ^ (0.95 - 1 / 2 : ℝ) / log x ^ B⌋₊,
            0 ≤ R d ∧ ∀ l : ℕ, l < d → Nat.Coprime l d →
              ∀ h : ℝ, 0 ≤ h → h ≤ x ^ (0.95 : ℝ) →
                ∀ z : ℝ, x / 2 ≤ z → z ≤ x →
                  |∑ a ∈ (Finset.Icc 1 ⌊x ^ (2 / 3 : ℝ)⌋₊).filter (fun a => Nat.Coprime a d),
                    (switchedMultiplicity118 N a : ℝ) * shortError118 z h a d l| ≤ R d) ∧
          (∑ d ∈ Finset.Icc 1 ⌊x ^ (0.95 - 1 / 2 : ℝ) / log x ^ B⌋₊, R d) ≤
            K * x ^ (0.95 : ℝ) / log x ^ (5 : ℝ) := by
  obtain ⟨B, hB, hrest⟩ := hWu 1 (by norm_num) 5 (by norm_num)
  refine ⟨B, hB, fun N => ?_⟩
  exact hrest (fun a => (switchedMultiplicity118 N a : ℝ)) (wu_coefficient118 N)
    0.95 (2 / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Page 603 display 4.12. A rowwise eventual bound does not give a uniform diagonal estimate.
This is a quantifier obstruction for the current WuMeanValue118 interface, not a paper counterexample. -/
theorem wu_uniformity_obstruction118 :
    ∃ E : ℕ → ℝ → ℝ,
      (∀ N : ℕ, ∀ᶠ x : ℝ in atTop, E N x = 0) ∧
      (∀ N : ℕ, E N (N : ℝ) = (N : ℝ) ^ (0.95 : ℝ)) ∧
      ¬ ∃ K x0 : ℝ, 0 < K ∧ 2 ≤ x0 ∧ ∀ N : ℕ, x0 ≤ (N : ℝ) →
        E N (N : ℝ) ≤ K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 5 := by
  let E : ℕ → ℝ → ℝ := fun N x => if x ≤ (N : ℝ) then x ^ (0.95 : ℝ) else 0
  refine ⟨E, ?_, ?_, ?_⟩
  · intro N
    filter_upwards [eventually_gt_atTop (N : ℝ)] with x hx
    simp [E, not_le.mpr hx]
  · intro N
    simp [E]
  · rintro ⟨K, x0, hK, hx0, hbound⟩
    have hlog : Tendsto (fun N : ℕ => log (N : ℝ) ^ 5) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 5 ≠ 0)).comp
        (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    obtain ⟨N, hNx0, hNK, hN2⟩ :=
      ((tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop x0)).and
        ((hlog.eventually (eventually_gt_atTop K)).and
          (eventually_ge_atTop (2 : ℕ)))).exists
    have hp : 0 < (N : ℝ) ^ (0.95 : ℝ) :=
      rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
    have hl : 0 < log (N : ℝ) ^ 5 := pow_pos (log_pos (by
      exact_mod_cast (show 1 < N by omega))) _
    have hb := hbound N hNx0
    simp only [E, le_refl, ite_true] at hb
    have hc := (le_div_iff₀ hl).mp hb
    have hd : log (N : ℝ) ^ 5 ≤ K := by
      apply (mul_le_mul_iff_right₀ hp).mp
      simpa only [mul_comm] using hc
    exact (not_lt_of_ge hd) hNK

/-- LEAF. Page 601 display 4.1 with the explicit loss already proved in Sum41.
This is the weighted sieve reduction, before any analytic estimates. -/
theorem leaf118_weighted (N : ℕ) (hN : 177147 ≤ N) :
    (Ssift N 0.95 : ℝ) - (S1 N 0.95 : ℝ) / 2 - (S2 N 0.95 : ℝ) / 2 -
      (S3 N 0.95 : ℝ) - 3 * (N : ℝ) ^ (10 / 11 : ℝ) ≤ (S N 0.95 : ℝ) := by
  exact eq41_printed N 0.95 hN

/-- LEAF. Pages 601 and 604, absorption of the error in display 4.1.
The exponent 10/11 is smaller than 0.95 and C has a uniform positive lower bound. -/
theorem leaf118_loss :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      3 * (N : ℝ) ^ (10 / 11 : ℝ) ≤
        0.05 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
  have hc := LeanLab.ChenExplicit.twinC_pos
  have ho : (fun n : ℕ => Real.log (n : ℝ) ^ 2) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (9 / 220 : ℝ)) := by
    have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (s := 9 / 220) (by norm_num)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, Real.rpow_two] using h
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp
    (ho.bound (show 0 < 0.05 * LeanLab.ChenExplicit.twinC / 3 by positivity))
  refine ⟨max n0 2, fun N hN => ?_⟩
  have hn : n0 ≤ N := (le_max_left ..).trans hN
  have hN2 : 2 ≤ N := (le_max_right ..).trans hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log (N : ℝ) ^ 2 := sq_pos_of_pos (Real.log_pos hNr)
  have hh := hn0 N hn
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hNpos _)] at hh
  have hC : LeanLab.ChenExplicit.twinC ≤ C N := by
    unfold C
    exact le_mul_of_one_le_right hc.le (LeanLab.ChenExplicit.one_le_oddFactor N)
  have hpow : (N : ℝ) ^ (0.95 : ℝ) =
      (N : ℝ) ^ (10 / 11 : ℝ) * (N : ℝ) ^ (9 / 220 : ℝ) := by
    rw [← Real.rpow_add hNpos]
    norm_num
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hlog).mpr
  calc
    3 * (N : ℝ) ^ (10 / 11 : ℝ) * Real.log (N : ℝ) ^ 2 ≤
        3 * (N : ℝ) ^ (10 / 11 : ℝ) *
          ((0.05 * LeanLab.ChenExplicit.twinC / 3) * (N : ℝ) ^ (9 / 220 : ℝ)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = 0.05 * (LeanLab.ChenExplicit.twinC * (N : ℝ) ^ (0.95 : ℝ)) := by
      rw [hpow]
      ring
    _ ≤ 0.05 * (C N * (N : ℝ) ^ (0.95 : ℝ)) := by
      gcongr

/-- LEAF. Page 601 display 4.4, including its sufficiently large threshold.
External inputs: Iwaniec, Rosser's sieve, 1981, pages 203 to 230;
Pan and Pan, Goldbach Conjecture, 1992, pages 175 to 176, Lemmas 2 and 3 here.
The integral constant alone is already proved in Integral44. -/
theorem leaf118_sieve_lower :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      12.9897 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) ≤
        (Ssift N 0.95 : ℝ) := by
  -- ATTEMPT lower 4: Using exact? directly without unformalized inputs is guaranteed to fail as the paper relies on external sieves.
  sorry

/-- LEAF. Page 602 display 4.7, including its sufficiently large threshold.
External inputs: Iwaniec's linear sieve and the Pan and Pan Bombieri theorem,
Lemmas 1 to 3 here. The integral constant alone is already proved in Integral47. -/
theorem leaf118_sieve_one :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (S1 N 0.95 : ℝ) ≤
        18.7347 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
  -- ATTEMPT one 4: Bounded search without the linear sieve inputs fails.
  sorry

/-- LEAF. Page 604 display 4.14, including its sufficiently large threshold.
External inputs: Iwaniec's linear sieve, Wu 1993, Quart. J. Math. 44,
pages 109 to 128, and Huxley's short interval prime number theorem in display 4.13.
The integral constant alone is already proved in Integral414. -/
theorem leaf118_sieve_two :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (S2 N 0.95 : ℝ) ≤
        6.8086 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
  -- ATTEMPT two 4: Linear sieve, Wu and Huxley unformalized.
  sorry

/-- LEAF. Page 604 display 4.15, including its sufficiently large threshold.
External inputs: the same switching, linear sieve, Wu mean value theorem and
Huxley short interval theorem as display 4.14.
The integral constant alone is already proved in Integrals. -/
theorem leaf118_sieve_three :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (S3 N 0.95 : ℝ) ≤
        0.1564 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
  -- ATTEMPT three 4: Linear sieve, Wu and Huxley unformalized.
  sorry

/-- The exact cited MainTheorem, assembled from the leaves.
CONDITIONAL on the four analytic leaves. No sorry occurs in this assembly. -/
theorem main_theorem_decomp118 : MainTheorem := by
  obtain ⟨n0, h0⟩ := leaf118_loss
  obtain ⟨n1, h1⟩ := leaf118_sieve_lower
  obtain ⟨n2, h2⟩ := leaf118_sieve_one
  obtain ⟨n3, h3⟩ := leaf118_sieve_two
  obtain ⟨n4, h4⟩ := leaf118_sieve_three
  refine ⟨max 177147 (max n0 (max n1 (max n2 (max n3 n4)))), ?_⟩
  intro N he hN
  have hcut : 177147 ≤ N := (le_max_left ..).trans hN
  have hrest := (le_max_right ..).trans hN
  have hn0 : n0 ≤ N := (le_max_left ..).trans hrest
  have hrest := (le_max_right ..).trans hrest
  have hn1 : n1 ≤ N := (le_max_left ..).trans hrest
  have hrest := (le_max_right ..).trans hrest
  have hn2 : n2 ≤ N := (le_max_left ..).trans hrest
  have hrest := (le_max_right ..).trans hrest
  have hn3 : n3 ≤ N := (le_max_left ..).trans hrest
  have hn4 : n4 ≤ N := (le_max_right ..).trans hrest
  have hp := leaf118_scale_pos N (by omega)
  have hw := leaf118_weighted N hcut
  have hl := h0 N hn0
  have hs := h1 N he hn1
  have hs1 := h2 N he hn2
  have hs2 := h3 N he hn3
  have hs3 := h4 N he hn4
  have htarget :
      0.01 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) < (S N 0.95 : ℝ) := by
    linarith
  simpa only [mul_div_assoc, mul_assoc] using htarget

end LeanLab.Cai2002
