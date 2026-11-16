import LeanLab.ChenDoubleSieve.BuchstabTail
import LeanLab.ChenDoubleSieve.Burst9Psi2Panels

/-!
Tail tools for the certified integrals of Wu 2004 Lemma 5.2 page 26.
Source: https://arxiv.org/abs/0705.1652, Lemma 2.10 page 9.
AI wrote the Lean code. Binary Goldbach is open.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional Wu04Buchstab

/-- The delay equation propagates a bound from any unit interval above two.
Wu 2004 Lemma 2.10 page 9, derived method of steps. -/
theorem propagate_upper_from {ω : ℝ → ℝ} (hω : IsBuchstab ω) {a c : ℝ}
    (ha : 2 ≤ a) (hbase : ∀ u ∈ Icc a (a + 1), ω u ≤ c) :
    ∀ u : ℝ, a ≤ u → ω u ≤ c := by
  have step : ∀ n : ℕ, ∀ u : ℝ, a ≤ u → u ≤ a + 1 + n → ω u ≤ c := by
    intro n
    induction n with
    | zero =>
      intro u hu hmax
      exact hbase u ⟨hu, by simpa using hmax⟩
    | succ n ih =>
      intro u hu hmax
      by_cases hs : u ≤ a + 1 + n
      · exact ih u hu hs
      let b : ℝ := a + 1 + n
      have hb : a + 1 ≤ b := by dsimp [b]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hbu : b ≤ u := (lt_of_not_ge hs).le
      have hwb := ih b (by linarith) le_rfl
      have hcont : ContinuousOn (fun t : ℝ => t * ω t) (Icc b u) :=
        continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
      have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc b u) := by
        rw [uIcc_of_le hbu]
        apply hω.1.comp (by fun_prop)
        intro t ht
        change 1 ≤ t - 1
        linarith [ht.1]
      have hf := integral_eq_sub_of_hasDerivAt_of_le hbu hcont
        (fun t ht => hω.2.2 t (by linarith [ht.1])) hci.intervalIntegrable
      have hi : (∫ t in b..u, ω (t - 1)) ≤ (u - b) * c := by
        have hm := integral_mono_on (μ := volume) hbu hci.intervalIntegrable
          intervalIntegrable_const (fun t ht => ih (t - 1) (by linarith [ht.1]) (by
            dsimp [b] at hbu
            push_cast at hmax
            linarith [ht.2]))
        simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
      have hl : b * ω b ≤ b * c := mul_le_mul_of_nonneg_left hwb (by linarith)
      have hm : u * ω u ≤ u * c := by linarith
      exact (mul_le_mul_iff_right₀ (by linarith : 0 < u)).mp (by simpa [mul_comm] using hm)
  intro u hu
  exact step ⌈u - a⌉₊ u hu (by linarith [Nat.le_ceil (u - a)])

/-- The value at four is one logarithm and one scalar J integral.
Wu 2004 Lemma 2.10 page 9, derived exact delay identity. -/
theorem buchstab_four_identity {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    4 * ω 4 = 1 + log 3 + J 2 3 := by
  have hc : ContinuousOn (fun t : ℝ => t * ω t) (Icc 3 4) :=
    continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
  have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc 3 4) := by
    rw [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)]
    apply hω.1.comp (by fun_prop)
    intro t ht
    change 1 ≤ t - 1
    linarith [ht.1]
  have hf := integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (3 : ℝ) ≤ 4) hc
    (fun t ht => hω.2.2 t (by linarith [ht.1])) hci.intervalIntegrable
  have he : (∫ t in (3 : ℝ)..4, ω (t - 1)) =
      ∫ t in (2 : ℝ)..3, (1 + log (t - 1)) / t := by
    rw [integral_comp_sub_right ω]
    norm_num
    apply integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] at ht
    exact formula_two_three hω ht
  have hi1 : IntervalIntegrable (fun t : ℝ => 1 / t) volume 2 3 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    rw [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] at ht
    exact (show 0 < t from lt_of_lt_of_le (by norm_num) ht.1).ne'
  have hi2 := Wu04Panels.J_integrable (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≤ 3)
  have hj : (∫ t in (2 : ℝ)..3, (1 + log (t - 1)) / t) =
      log 3 - log 2 + J 2 3 := by
    simp_rw [add_div]
    rw [integral_add hi1 hi2]
    simp only [one_div, integral_inv_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 3), J]
    rw [log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  have h3 := formula_two_three hω (u := 3) (by norm_num)
  norm_num at h3
  rw [he, hj] at hf
  linarith

/-- A kernel checked panel certificate bounds the scalar integral at three.
Wu 2004 page 26, derived endpoint certificate. -/
theorem J_three_certificate : Burst9Psi2.jUpperSum 3 128 ≤ (148 / 1000 : ℚ) := by
  decide +kernel

/-- The value at four has a strict rational enclosure.
Wu 2004 Lemma 2.10 page 9, derived numerical bound. -/
theorem buchstab_four_le {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    ω 4 ≤ (562 / 1000 : ℝ) := by
  have hj := Burst9Psi2.J_upper_of_cert (by norm_num) (by norm_num) J_three_certificate
  have hl := (Wu04Integral.log_bounds 12 (y := 3) (by norm_num)).2
  have hl3 : log (3 : ℝ) ≤ (1099 / 1000 : ℝ) := by
    apply hl.trans
    norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, sum_range_succ]
  have hf := buchstab_four_identity hω
  norm_num at hj
  linarith

/-- A sharper upper bound holds on the next unit interval.
Wu 2004 Lemma 2.10 page 9, derived from the bound at four. -/
theorem buchstab_four_five_le {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : u ∈ Set.Icc (4 : ℝ) 5) : ω u ≤ (563 / 1000 : ℝ) := by
  have hc : ContinuousOn (fun t : ℝ => t * ω t) (Icc 4 u) :=
    continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
  have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc 4 u) := by
    rw [uIcc_of_le hu.1]
    apply hω.1.comp (by fun_prop)
    intro t ht
    change 1 ≤ t - 1
    linarith [ht.1]
  have hf := integral_eq_sub_of_hasDerivAt_of_le hu.1 hc
    (fun t ht => hω.2.2 t (by linarith [ht.1])) hci.intervalIntegrable
  have hi : (∫ t in (4 : ℝ)..u, ω (t - 1)) ≤ (u - 4) * (566 / 1000) := by
    have hm := integral_mono_on (μ := volume) hu.1 hci.intervalIntegrable
      intervalIntegrable_const (fun t ht => buchstab_le_566 hω (by linarith [ht.1]))
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
  have h4 := buchstab_four_le hω
  have hm : u * ω u ≤ u * (563 / 1000) := by nlinarith [hu.2]
  exact (mul_le_mul_iff_right₀ (by linarith [hu.1] : 0 < u)).mp (by simpa [mul_comm] using hm)

/-- The smaller cap holds on the entire unbounded tail.
Wu 2004 Lemma 2.10 page 9, derived bound for the I2 quadrature tail. -/
theorem buchstab_le_563 {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : 4 ≤ u) : ω u ≤ (563 / 1000 : ℝ) :=
  propagate_upper_from hω (by norm_num) (fun u hu => buchstab_four_five_le hω (by norm_num at hu; exact hu)) u hu

end LeanLab.ChenDoubleSieve.Task587
