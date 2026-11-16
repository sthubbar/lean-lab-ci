import LeanLab.ChenDoubleSieve.Task587TailFiveData

/-!
A smaller unbounded Buchstab tail for Wu 2004 Lemma 2.10 page 9.
Source: https://arxiv.org/abs/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- Certified scalar panels bound the delay integral from three to four.
Wu 2004 Lemma 2.10 page 9, derived exact quadrature. -/
theorem integral_omega_three_four {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    (∫ u in (3 : ℝ)..4, ω u) ≤ (5625 / 10000 : ℝ) := by
  let x : ℕ → ℝ := fun j => (tailFiveNode j : ℝ)
  have hx (j : ℕ) : x j = 3 + (j : ℝ) / 192 := by simp [x, tailFiveNode]
  have hxp (j : ℕ) (hj : j < 192) : 3 ≤ x j ∧ x j ≤ x (j + 1) ∧ x (j + 1) ≤ 4 := by
    have hj' : ((j + 1 : ℕ) : ℝ) ≤ 192 := by exact_mod_cast (Nat.succ_le_iff.mpr hj)
    push_cast at hj'
    rw [hx, hx]
    push_cast
    constructor
    · linarith [Nat.cast_nonneg (α := ℝ) j]
    · constructor <;> linarith
  have hi (j : ℕ) (hj : j < 192) : IntervalIntegrable ω volume (x j) (x (j + 1)) := by
    apply ContinuousOn.intervalIntegrable
    apply hω.1.mono
    rw [uIcc_of_le (hxp j hj).2.1]
    intro t ht
    change 1 ≤ t
    linarith [(hxp j hj).1, ht.1]
  have hp (j : ℕ) (hj : j < 192) : (∫ u in x j..x (j + 1), ω u) ≤
      ((tailFiveCapQ (tailFiveNode j) (tailFiveNode (j + 1)) : ℚ) : ℝ) / 192 := by
    have hm := integral_mono_on (μ := volume) (hxp j hj).2.1 (hi j hj)
      intervalIntegrable_const (fun u hu => buchstab_le_tailFiveCap hω
        (a := tailFiveNode j) (b := tailFiveNode (j + 1))
        (by
          have h : (3 : ℝ) ≤ (tailFiveNode j : ℝ) := (hxp j hj).1
          exact_mod_cast h)
        (by
          have h : (tailFiveNode j : ℝ) ≤ (tailFiveNode (j + 1) : ℝ) := (hxp j hj).2.1
          exact_mod_cast h)
        (by
          have h : (tailFiveNode (j + 1) : ℝ) ≤ (4 : ℝ) := (hxp j hj).2.2
          exact_mod_cast h) hu)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hm
    have hd : x (j + 1) - x j = (1 / 192 : ℝ) := by
      rw [hx, hx]
      push_cast
      ring
    rw [hd] at hm
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hm
  have he := intervalIntegral.sum_integral_adjacent_intervals hi
  have hx0 : x 0 = 3 := by simp [hx]
  have hxm : x 192 = 4 := by norm_num [hx]
  rw [hx0, hxm] at he
  have hs : (∑ j ∈ range 192,
      ((tailFiveCapQ (tailFiveNode j) (tailFiveNode (j + 1)) : ℚ) : ℝ) / 192) ≤
      (5625 / 10000 : ℝ) := by
    have h' : (tailFiveSum : ℝ) ≤ ((5625 / 10000 : ℚ) : ℝ) := by
      exact_mod_cast tailFive_certificate
    have h : (tailFiveSum : ℝ) ≤ (5625 / 10000 : ℝ) := by norm_num at h' ⊢; exact h'
    simpa only [tailFiveSum, Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] using h
  rw [← he]
  exact (sum_le_sum fun j hj => hp j (mem_range.mp hj)).trans hs

/-- The certified scalar delay integral gives a rational bound at five.
Wu 2004 Lemma 2.10 page 9, derived enclosure. -/
theorem buchstab_five_le_5617 {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    ω 5 ≤ (5617 / 10000 : ℝ) := by
  have hc : ContinuousOn (fun t : ℝ => t * ω t) (Set.Icc 4 5) :=
    continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
  have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc 4 5) := by
    rw [uIcc_of_le (by norm_num : (4 : ℝ) ≤ 5)]
    apply hω.1.comp (by fun_prop)
    intro t ht
    change 1 ≤ t - 1
    linarith [ht.1]
  have hf := integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (4 : ℝ) ≤ 5) hc
    (fun t ht => hω.2.2 t (by linarith [ht.1])) hci.intervalIntegrable
  have he : (∫ t in (4 : ℝ)..5, ω (t - 1)) = ∫ t in (3 : ℝ)..4, ω t := by
    rw [integral_comp_sub_right ω]
    norm_num
  rw [he] at hf
  have hi := integral_omega_three_four hω
  have h4 := buchstab_four_le_5615 hω
  linarith

/-- The smaller cap holds on the next unit interval.
Wu 2004 Lemma 2.10 page 9, derived method-of-steps bound. -/
theorem buchstab_five_six_le {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : u ∈ Set.Icc (5 : ℝ) 6) : ω u ≤ (562 / 1000 : ℝ) := by
  have hc : ContinuousOn (fun t : ℝ => t * ω t) (Set.Icc 5 u) :=
    continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
  have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc 5 u) := by
    rw [uIcc_of_le hu.1]
    apply hω.1.comp (by fun_prop)
    intro t ht
    change 1 ≤ t - 1
    linarith [ht.1]
  have hf := integral_eq_sub_of_hasDerivAt_of_le hu.1 hc
    (fun t ht => hω.2.2 t (by linarith [ht.1])) hci.intervalIntegrable
  have hi : (∫ t in (5 : ℝ)..u, ω (t - 1)) ≤ (u - 5) * (563 / 1000) := by
    have hm := integral_mono_on (μ := volume) hu.1 hci.intervalIntegrable
      intervalIntegrable_const (fun t ht => buchstab_le_563 hω (by linarith [ht.1]))
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
  have h5 := buchstab_five_le_5617 hω
  have hm : u * ω u ≤ u * (562 / 1000) := by nlinarith [hu.2]
  exact (mul_le_mul_iff_right₀ (by linarith [hu.1] : 0 < u)).mp (by simpa [mul_comm] using hm)

/-- The smaller cap propagates to the whole unbounded tail after five.
Wu 2004 Lemma 2.10 page 9, derived uniform bound. -/
theorem buchstab_le_562 {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : 5 ≤ u) : ω u ≤ (562 / 1000 : ℝ) :=
  propagate_upper_from hω (by norm_num)
    (fun u hu => buchstab_five_six_le hω (by norm_num at hu; exact hu)) u hu

end LeanLab.ChenDoubleSieve.Task587
