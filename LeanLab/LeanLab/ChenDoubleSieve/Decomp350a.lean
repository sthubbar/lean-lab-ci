import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.BuchstabTail
import LeanLab.ChenDoubleSieve.Decomp350f
import LeanLab.ChenDoubleSieve.Decomp350k

/-!
Shared finite numerical preparation for Wu 2004 equation 10.12.
Source: https://arxiv.org/pdf/0705.1652, pages 9, 41 and 42.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set MeasureTheory intervalIntegral
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task350
open Task275 Wu04Functional

/-- Positivity follows from the initial values and the delay equation.
Source: page 9 Lemma 2.10, derived helper. -/
theorem buchstab_nonneg {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : 1 ≤ u) : 0 ≤ ω u := by
  have step : ∀ n : ℕ, ∀ v : ℝ, 1 ≤ v → v ≤ (n : ℝ) + 2 → 0 ≤ ω v := by
    intro n
    induction n with
    | zero =>
      intro v hv hv2
      rw [hω.2.1 v hv (by simpa using hv2)]
      positivity
    | succ n ih =>
      intro v hv hvmax
      by_cases hsmall : v ≤ (n : ℝ) + 2
      · exact ih v hv hsmall
      let b : ℝ := n + 2
      have hb : 2 ≤ b := by dsimp [b]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hbv : b ≤ v := (lt_of_not_ge hsmall).le
      have hwb : 0 ≤ ω b := ih b (by linarith) le_rfl
      have hc : ContinuousOn (fun t : ℝ => t * ω t) (Icc b v) :=
        continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
      have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc b v) := by
        rw [uIcc_of_le hbv]
        apply hω.1.comp (by fun_prop)
        intro t ht
        change 1 ≤ t - 1
        linarith [ht.1]
      have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hbv hc
        (fun t ht => hω.2.2 t (by linarith [ht.1])) hci.intervalIntegrable
      have hi : 0 ≤ ∫ t in b..v, ω (t - 1) := by
        apply intervalIntegral.integral_nonneg hbv
        intro t ht
        apply ih (t - 1) (by linarith [ht.1])
        push_cast at hvmax
        linarith [ht.2]
      have hm : 0 ≤ v * ω v := by nlinarith
      exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hm) (by linarith : 0 < v)
  exact step ⌈u⌉₊ u hu (by linarith [Nat.le_ceil u])

/-- A compact interval of length one controls the whole later Buchstab tail.
Source: page 9 defining delay equation, derived helper. -/
theorem propagate_upper_from {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {a c : ℝ} (ha : 2 ≤ a)
    (hbase : ∀ u ∈ Icc a (a + 1), ω u ≤ c) :
    ∀ u : ℝ, a ≤ u → ω u ≤ c := by
  have step : ∀ n : ℕ, ∀ u : ℝ, a ≤ u → u ≤ (n : ℝ) + a + 1 → ω u ≤ c := by
    intro n
    induction n with
    | zero => intro u hu humax; exact hbase u ⟨hu, by simpa using humax⟩
    | succ n ih =>
      intro u hu humax
      by_cases hsmall : u ≤ (n : ℝ) + a + 1
      · exact ih u hu hsmall
      let b : ℝ := n + a + 1
      have hb : a + 1 ≤ b := by dsimp [b]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hbu : b ≤ u := (lt_of_not_ge hsmall).le
      have hwb : ω b ≤ c := ih b (by linarith) le_rfl
      have hc : ContinuousOn (fun t : ℝ => t * ω t) (Icc b u) :=
        continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
      have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc b u) := by
        rw [uIcc_of_le hbu]
        apply hω.1.comp (by fun_prop)
        intro t ht
        change 1 ≤ t - 1
        linarith [ht.1]
      have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hbu hc
        (fun t ht => hω.2.2 t (by linarith [ht.1])) hci.intervalIntegrable
      have hi : (∫ t in b..u, ω (t - 1)) ≤ (u - b) * c := by
        have hm := intervalIntegral.integral_mono_on (μ := volume) hbu
          hci.intervalIntegrable intervalIntegrable_const (fun t ht =>
            ih (t - 1) (by linarith [ht.1]) (by
              push_cast at humax
              linarith [ht.2]))
        simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
      have hw : b * ω b ≤ b * c := mul_le_mul_of_nonneg_left hwb (by linarith)
      have hm : u * ω u ≤ u * c := by nlinarith
      exact (mul_le_mul_iff_right₀ (by linarith : 0 < u)).mp (by simpa [mul_comm] using hm)
  intro u hu
  exact step ⌈u⌉₊ u hu (by linarith [Nat.le_ceil u])

/-- LEAF. Wu 2004 page 9 Lemma 2.10 and page 42 numerical computation.
The final half of the compact strip follows from a finite Bernstein certificate.
This contains no fourfold integral and no coefficient evaluation. -/
theorem buchstab_four_to_four_half {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    ∀ u ∈ Icc (4 : ℝ) (9 / 2), ω u ≤ 280761 / 500000 := by
  exact buchstab_four_to_four_half_clean hω

/-- The full compact sharp bound follows from the proved first half and one leaf.
Both halves have clean finite proofs. -/
theorem buchstab_compact_upper {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    ∀ u ∈ Icc (7 / 2 : ℝ) (9 / 2), ω u ≤ 280761 / 500000 := by
  intro u hu
  by_cases h4 : u ≤ 4
  · exact buchstab_seven_halves_to_four hω ⟨hu.1, h4⟩
  · exact buchstab_four_to_four_half hω u ⟨(lt_of_not_ge h4).le, hu.2⟩

/-- The global sharp tail follows from the compact numerical leaf.
The compact bound has a clean finite proof. -/
theorem buchstab_tail_upper {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : 7 / 2 ≤ u) : ω u ≤ 280761 / 500000 := by
  apply propagate_upper_from hω (a := 7 / 2) (by norm_num) _ u hu
  norm_num only [show (7 / 2 + 1 : ℝ) = 9 / 2 by norm_num]
  exact buchstab_compact_upper hω

/-- A nonnegative integrand needs no separate integrability proof to compare it
with an integrable majorant. Source: page 42 domination step, derived helper. -/
theorem interval_integral_le_of_nonneg {a b : ℝ} {f g : ℝ → ℝ}
    (hab : a ≤ b) (hf : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hg : IntervalIntegrable g volume a b)
    (hfg : ∀ t ∈ Icc a b, f t ≤ g t) :
    (∫ t in a..b, f t) ≤ ∫ t in a..b, g t := by
  simp only [intervalIntegral.integral_of_le hab]
  exact MeasureTheory.integral_mono_of_nonneg
    ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ (fun t ht => hf t ⟨ht.1.le, ht.2⟩)))
    hg.1
    ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ (fun t ht => hfg t ⟨ht.1.le, ht.2⟩)))

/-- The constant Buchstab majorant after evaluating the fourth integral.
Source: page 41 equation 10.12 and page 42, derived exact logarithmic integral. -/
def logMajorant (c : ℝ) (lower last : ℝ → ℝ) (a b : ℝ) (weight : ℝ → ℝ) : ℝ :=
  ∫ t1 in a..b,
    (∫ t2 in t1..kappa2,
      (∫ t3 in t2..kappa2, c * log (last t3 / lower t3) / t3) / t2 ^ 2) / weight t1

/-- Domination reduces a fourfold Buchstab integral to three logarithmic integrals.
Source: page 42 use of Lemma 2.10 in the numerical computation. -/
theorem fourfold_le_logMajorant {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {c a b : ℝ} {lower last weight : ℝ → ℝ}
    (hab : a ≤ b) (ha : kappa1 ≤ a) (hb : b ≤ kappa2)
    (hl : ContinuousOn lower (Icc kappa1 kappa2))
    (hr : ContinuousOn last (Icc kappa1 kappa2))
    (hw : ContinuousOn weight (Icc kappa1 kappa2))
    (hlpos : ∀ t ∈ Icc kappa1 kappa2, 0 < lower t)
    (hlr : ∀ t ∈ Icc kappa1 kappa2, lower t ≤ last t)
    (hwpos : ∀ t ∈ Icc kappa1 kappa2, 0 < weight t)
    (harg : ∀ t1 ∈ Icc a b, ∀ t2 ∈ Icc t1 kappa2,
      ∀ t3 ∈ Icc t2 kappa2, ∀ t4 ∈ Icc (lower t3) (last t3),
      (7 / 2 : ℝ) ≤ (1 - t1 - t2 - t3 - t4) / t2)
    (hc : ∀ u : ℝ, 7 / 2 ≤ u → ω u ≤ c) :
    fourfold ω last a b lower weight ≤ logMajorant c lower last a b weight := by
  have hk : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hlog : ContinuousOn (fun t => c * log (last t / lower t) / t)
      (Icc kappa1 kappa2) := by
    apply ContinuousOn.div _ continuousOn_id (fun t ht => ne_of_gt (hk.trans_le ht.1))
    apply continuousOn_const.mul
    apply ContinuousOn.log (hr.div hl (fun t ht => (hlpos t ht).ne'))
    intro t ht
    exact (div_pos ((hlpos t ht).trans_le (hlr t ht)) (hlpos t ht)).ne'
  have hP : ContinuousOn (fun t2 => ∫ t3 in t2..kappa2,
      c * log (last t3 / lower t3) / t3) (Icc kappa1 kappa2) := by
    have hh := continuousOn_primitive_interval_left (μ := volume)
      (a := kappa1) (b := kappa2) (by
        rw [uIcc_of_le (by norm_num [kappa1, kappa2])]
        exact hlog.integrableOn_Icc)
    rwa [uIcc_of_le (by norm_num [kappa1, kappa2])] at hh
  have hQ : ContinuousOn (fun t2 => (∫ t3 in t2..kappa2,
      c * log (last t3 / lower t3) / t3) / t2 ^ 2) (Icc kappa1 kappa2) :=
    hP.div (by fun_prop) (fun t ht => pow_ne_zero _ (ne_of_gt (hk.trans_le ht.1)))
  have hR : ContinuousOn (fun t1 => ∫ t2 in t1..kappa2,
      (∫ t3 in t2..kappa2, c * log (last t3 / lower t3) / t3) / t2 ^ 2)
      (Icc kappa1 kappa2) := by
    have hh := continuousOn_primitive_interval_left (μ := volume)
      (a := kappa1) (b := kappa2) (by
        rw [uIcc_of_le (by norm_num [kappa1, kappa2])]
        exact hQ.integrableOn_Icc)
    rwa [uIcc_of_le (by norm_num [kappa1, kappa2])] at hh
  have hsub : ∀ t1 ∈ Icc a b, t1 ∈ Icc kappa1 kappa2 :=
    fun _ ht => ⟨ha.trans ht.1, ht.2.trans hb⟩
  have hinner0 : ∀ t1 ∈ Icc a b, ∀ t2 ∈ Icc t1 kappa2,
      ∀ t3 ∈ Icc t2 kappa2,
      0 ≤ ∫ t4 in lower t3..last t3, ω ((1 - t1 - t2 - t3 - t4) / t2) / t4 := by
    intro t1 ht1 t2 ht2 t3 ht3
    have ht3k : t3 ∈ Icc kappa1 kappa2 := ⟨(hsub t1 ht1).1.trans (ht2.1.trans ht3.1), ht3.2⟩
    apply intervalIntegral.integral_nonneg (hlr t3 ht3k)
    intro t4 ht4
    exact div_nonneg (buchstab_nonneg hω (by linarith [harg t1 ht1 t2 ht2 t3 ht3 t4 ht4]))
      ((hlpos t3 ht3k).le.trans ht4.1)
  have hinner : ∀ t1 ∈ Icc a b, ∀ t2 ∈ Icc t1 kappa2,
      ∀ t3 ∈ Icc t2 kappa2,
      (∫ t4 in lower t3..last t3, ω ((1 - t1 - t2 - t3 - t4) / t2) / t4)
        ≤ c * log (last t3 / lower t3) := by
    intro t1 ht1 t2 ht2 t3 ht3
    have ht3k : t3 ∈ Icc kappa1 kappa2 := ⟨(hsub t1 ht1).1.trans (ht2.1.trans ht3.1), ht3.2⟩
    have hlow := hlpos t3 ht3k
    have hlast := hlow.trans_le (hlr t3 ht3k)
    calc
      _ ≤ ∫ t4 in lower t3..last t3, c / t4 := by
        apply interval_integral_le_of_nonneg (hlr t3 ht3k)
        · intro t4 ht4
          exact div_nonneg (buchstab_nonneg hω (by linarith [harg t1 ht1 t2 ht2 t3 ht3 t4 ht4]))
            (hlow.le.trans ht4.1)
        · apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le (hlr t3 ht3k)]
          exact continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt (hlow.trans_le ht.1))
        · intro t4 ht4
          exact div_le_div_of_nonneg_right (hc _ (harg t1 ht1 t2 ht2 t3 ht3 t4 ht4))
            (hlow.le.trans ht4.1)
      _ = c * log (last t3 / lower t3) := by
        simp_rw [div_eq_mul_inv]
        rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hlow hlast]
        rfl
  unfold fourfold logMajorant
  apply interval_integral_le_of_nonneg hab
  · intro t1 ht1
    apply div_nonneg _ (hwpos t1 (hsub t1 ht1)).le
    apply intervalIntegral.integral_nonneg (hsub t1 ht1).2
    intro t2 ht2
    apply div_nonneg _ (sq_nonneg _)
    apply intervalIntegral.integral_nonneg ht2.2
    intro t3 ht3
    exact div_nonneg (hinner0 t1 ht1 t2 ht2 t3 ht3)
      (hk.le.trans ((hsub t1 ht1).1.trans (ht2.1.trans ht3.1)))
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact (hR.div hw (fun t ht => (hwpos t ht).ne')).mono (fun t ht => hsub t ht)
  · intro t1 ht1
    apply div_le_div_of_nonneg_right _ (hwpos t1 (hsub t1 ht1)).le
    apply interval_integral_le_of_nonneg (hsub t1 ht1).2
    · intro t2 ht2
      apply div_nonneg _ (sq_nonneg _)
      apply intervalIntegral.integral_nonneg ht2.2
      intro t3 ht3
      exact div_nonneg (hinner0 t1 ht1 t2 ht2 t3 ht3)
        (hk.le.trans ((hsub t1 ht1).1.trans (ht2.1.trans ht3.1)))
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (hsub t1 ht1).2]
      exact hQ.mono (fun t ht => ⟨(hsub t1 ht1).1.trans ht.1, ht.2⟩)
    · intro t2 ht2
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply interval_integral_le_of_nonneg ht2.2
      · intro t3 ht3
        exact div_nonneg (hinner0 t1 ht1 t2 ht2 t3 ht3)
          (hk.le.trans ((hsub t1 ht1).1.trans (ht2.1.trans ht3.1)))
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le ht2.2]
        exact hlog.mono (fun t ht => ⟨(hsub t1 ht1).1.trans (ht2.1.trans ht.1), ht.2⟩)
      · intro t3 ht3
        exact div_le_div_of_nonneg_right (hinner t1 ht1 t2 ht2 t3 ht3)
          (hk.le.trans ((hsub t1 ht1).1.trans (ht2.1.trans ht3.1)))

end LeanLab.ChenDoubleSieve.Task350
