/-
P0069 page 9 display 2.11, quantitative finite nonunit peak diagnostics.
These do not establish the full asymptotic hypotheses or refute the paper.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561j
namespace LeanLab.BHP1997.Decomp561k
open Classical Complex AddCircle Finset Decomp561j

/-- P0069 page 9 display 2.11, auxiliary variation bound for a Fourier phase. -/
theorem fourier_nat_sub_one_le561 (m : ℕ) (t : ℝ) :
    ‖@fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ)) - 1‖ ≤
      2 * Real.pi * (m : ℝ) * |t| := by
  have he : @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ)) =
      Complex.exp (Complex.I * ((2 * Real.pi * (m : ℝ) * t : ℝ) : ℂ)) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [he]
  simpa [abs_mul, abs_of_nonneg Real.pi_pos.le] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (m : ℝ) * t))

/-- P0069 page 9 display 2.11, auxiliary quantitative finite nonunit peak.
The deviation from the even support cardinality is bounded by its first moment.
This does not prove the uniform arithmetic premises of the proposed diagnostic. -/
theorem even_phase_deviation561 (S : Finset ℕ) (a t : ℝ) :
    ‖(∑ m ∈ S, evenPhaseCoeff561 a m *
        @fourier 1 (-(m : ℤ)) ((a + t : ℝ) : AddCircle (1 : ℝ))) -
        ((S.filter Even).card : ℂ)‖ ≤
      2 * Real.pi * |t| * ∑ m ∈ S.filter Even, (m : ℝ) := by
  have he (m : ℕ) :
      @fourier 1 (m : ℤ) (a : AddCircle (1 : ℝ)) *
      @fourier 1 (-(m : ℤ)) ((a + t : ℝ) : AddCircle (1 : ℝ)) =
      @fourier 1 (m : ℤ) ((-t : ℝ) : AddCircle (1 : ℝ)) := by
    simp only [fourier_coe_apply, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hs : (∑ m ∈ S, evenPhaseCoeff561 a m *
        @fourier 1 (-(m : ℤ)) ((a + t : ℝ) : AddCircle (1 : ℝ))) =
      ∑ m ∈ S.filter Even, @fourier 1 (m : ℤ) ((-t : ℝ) : AddCircle (1 : ℝ)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases h : Even m
    · simp only [evenPhaseCoeff561, h, ite_true, he]
    · simp [evenPhaseCoeff561, h]
  rw [hs]
  have hc : ((S.filter Even).card : ℂ) = ∑ _m ∈ S.filter Even, (1 : ℂ) := by simp
  rw [hc, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ m ∈ S.filter Even,
        ‖@fourier 1 (m : ℤ) ((-t : ℝ) : AddCircle (1 : ℝ)) - 1‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ S.filter Even, 2 * Real.pi * (m : ℝ) * |t| := by
      apply Finset.sum_le_sum
      intro m hm
      simpa only [abs_neg] using fourier_nat_sub_one_le561 m (-t)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m hm; ring

/-- P0069 page 9 display 2.11, auxiliary lower bound near the finite nonunit peak.
For support bounded by 2Y and phase distance with 4 pi Y times distance at most
one half, the polynomial norm is at least half the even support cardinality.
This is a local finite estimate, not the full asymptotic counterexample. -/
theorem even_phase_near_peak561 (S : Finset ℕ) (a t Y : ℝ)
    (_hY : 0 ≤ Y) (hS : ∀ m ∈ S.filter Even, (m : ℝ) ≤ 2 * Y)
    (ht : 4 * Real.pi * Y * |t| ≤ 1 / 2) :
    ((S.filter Even).card : ℝ) / 2 ≤
      ‖∑ m ∈ S, evenPhaseCoeff561 a m *
        @fourier 1 (-(m : ℤ)) ((a + t : ℝ) : AddCircle (1 : ℝ))‖ := by
  have hs : (∑ m ∈ S.filter Even, (m : ℝ)) ≤
      ((S.filter Even).card : ℝ) * (2 * Y) := by
    calc
      _ ≤ ∑ _m ∈ S.filter Even, 2 * Y := Finset.sum_le_sum hS
      _ = _ := by simp
  have hd := even_phase_deviation561 S a t
  have hh : 2 * Real.pi * |t| * (∑ m ∈ S.filter Even, (m : ℝ)) ≤
      ((S.filter Even).card : ℝ) / 2 := by
    calc
      _ ≤ 2 * Real.pi * |t| * (((S.filter Even).card : ℝ) * (2 * Y)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = (4 * Real.pi * Y * |t|) * ((S.filter Even).card : ℝ) := by ring
      _ ≤ (1 / 2) * ((S.filter Even).card : ℝ) :=
        mul_le_mul_of_nonneg_right ht (by positivity)
      _ = _ := by ring
  have hn := norm_sub_norm_le
    (((S.filter Even).card : ℂ))
    (∑ m ∈ S, evenPhaseCoeff561 a m *
        @fourier 1 (-(m : ℤ)) ((a + t : ℝ) : AddCircle (1 : ℝ)))
  rw [norm_sub_rev] at hn
  simp only [Complex.norm_natCast] at hn
  linarith

open MeasureTheory Set

/-- P0069 page 9 display 2.11, auxiliary finite peak energy lower bound.
A symmetric phase interval of radius r inside the quantitative peak has energy
at least r times the square of the even support cardinality divided by two.
The statement does not assert that this interval lies in the minor arcs. -/
theorem even_phase_peak_energy561 (S : Finset ℕ) (a Y r : ℝ)
    (hY : 0 ≤ Y) (hr : 0 ≤ r)
    (hS : ∀ m ∈ S.filter Even, (m : ℝ) ≤ 2 * Y)
    (hphase : 4 * Real.pi * Y * r ≤ 1 / 2) :
    r * ((S.filter Even).card : ℝ) ^ 2 / 2 ≤
      ∫ t in (-r)..r, ‖∑ m ∈ S, evenPhaseCoeff561 a m *
        @fourier 1 (-(m : ℤ)) ((a + t : ℝ) : AddCircle (1 : ℝ))‖ ^ 2 := by
  have hf : Continuous (fun t : ℝ => ‖∑ m ∈ S, evenPhaseCoeff561 a m *
        @fourier 1 (-(m : ℤ)) ((a + t : ℝ) : AddCircle (1 : ℝ))‖ ^ 2) := by
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro m hm
    exact continuous_const.mul
      (((map_continuous (fourier (T := (1 : ℝ)) (-(m : ℤ)))).comp
        (AddCircle.continuous_mk' 1)).comp (continuous_const.add continuous_id))
  have hp (t : ℝ) (ht : t ∈ Icc (-r) r) :
      ((S.filter Even).card : ℝ) ^ 2 / 4 ≤
      ‖∑ m ∈ S, evenPhaseCoeff561 a m *
        @fourier 1 (-(m : ℤ)) ((a + t : ℝ) : AddCircle (1 : ℝ))‖ ^ 2 := by
    have habs : |t| ≤ r := abs_le.mpr ⟨ht.1, ht.2⟩
    have ht' : 4 * Real.pi * Y * |t| ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left habs (by positivity)).trans hphase
    have hn := even_phase_near_peak561 S a t Y hY hS ht'
    have hn2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((S.filter Even).card : ℝ) / 2) hn 2
    nlinarith
  have hi := intervalIntegral.integral_mono_on (by linarith : -r ≤ r)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ((S.filter Even).card : ℝ) ^ 2 / 4) volume (-r) r)
    (hf.intervalIntegrable (-r) r) hp
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  nlinarith

/-- P0069 page 9 display 2.11, auxiliary size of the finite nonunit support.
For Y at least 4, at least Y over 4 of the integers in J are even. -/
theorem even_support_card_lower561 (Y : ℝ) (hY : 4 ≤ Y) :
    Y / 4 ≤ (((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter Even).card : ℝ) := by
  let S := Finset.Ioc ⌊Y / 2⌋₊ ⌊Y⌋₊
  have hi : Function.Injective (fun n : ℕ => 2 * n) := by intro m n h; dsimp at h; omega
  have hsub : S.image (fun n => 2 * n) ⊆
      (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter Even := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have hn' := Finset.mem_Ioc.mp hn
    have hlo : Y / 2 < (n : ℝ) := Nat.lt_of_floor_lt hn'.1
    have hhi : (n : ℝ) ≤ Y := (show (n : ℝ) ≤ (⌊Y⌋₊ : ℝ) by exact_mod_cast hn'.2).trans (Nat.floor_le (by linarith))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, ⟨n, by omega⟩⟩
    · apply (Nat.floor_lt (by linarith : (0 : ℝ) ≤ Y)).mpr
      push_cast
      linarith
    · apply (Nat.le_floor_iff (by linarith : (0 : ℝ) ≤ 2 * Y)).mpr
      push_cast
      linarith
  have hcard : ⌊Y⌋₊ - ⌊Y / 2⌋₊ ≤
      ((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter Even).card := by
    calc
      _ = (S.image (fun n => 2 * n)).card := by
        rw [Finset.card_image_of_injective S hi]
        simp [S]
      _ ≤ _ := Finset.card_le_card hsub
  have hmono : ⌊Y / 2⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_mono (by linarith)
  have hc : ((⌊Y⌋₊ - ⌊Y / 2⌋₊ : ℕ) : ℝ) ≤
      (((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter Even).card : ℝ) := by exact_mod_cast hcard
  rw [Nat.cast_sub hmono] at hc
  have h1 := Nat.sub_one_lt_floor Y
  have h2 := Nat.floor_le (by linarith : (0 : ℝ) ≤ Y / 2)
  linarith

/-- P0069 page 9 display 2.11, auxiliary linear energy of the actual short support.
The even supported phase has energy at least Y over 512 pi in a neighborhood
of radius 1 over 16 pi Y. No minor arc containment is assumed or concluded.
The uniform arithmetic hypotheses of the candidate remain separate. -/
theorem even_short_interval_energy561 (Y a : ℝ) (hY : 4 ≤ Y) :
    Y / (512 * Real.pi) ≤
      ∫ t in (-(1 / (16 * Real.pi * Y)))..(1 / (16 * Real.pi * Y)),
        ‖∑ m ∈ Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊, evenPhaseCoeff561 a m *
          @fourier 1 (-(m : ℤ)) ((a + t : ℝ) : AddCircle (1 : ℝ))‖ ^ 2 := by
  have hY0 : 0 < Y := by linarith
  let S := Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊
  let r : ℝ := 1 / (16 * Real.pi * Y)
  have hr : 0 < r := by dsimp [r]; positivity
  have hS : ∀ m ∈ S.filter Even, (m : ℝ) ≤ 2 * Y := by
    intro m hm
    have hm' := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).2
    exact (show (m : ℝ) ≤ (⌊2 * Y⌋₊ : ℝ) by exact_mod_cast hm').trans
      (Nat.floor_le (by positivity))
  have hphase : 4 * Real.pi * Y * r ≤ 1 / 2 := by
    have he : 4 * Real.pi * Y * r = 1 / 4 := by
      dsimp [r]
      field_simp [hY0.ne', Real.pi_ne_zero]; ring
    rw [he]
    norm_num
  have he := even_phase_peak_energy561 S a Y r hY0.le hr.le hS hphase
  have hc := even_support_card_lower561 Y hY
  have hs : (Y / 4) ^ 2 ≤ ((S.filter Even).card : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hc 2
  calc
    _ = r * (Y / 4) ^ 2 / 2 := by
      dsimp [r]
      field_simp [hY0.ne', Real.pi_ne_zero]; ring
    _ ≤ r * ((S.filter Even).card : ℝ) ^ 2 / 2 := by gcongr
    _ ≤ _ := he

end LeanLab.BHP1997.Decomp561k
