/-
Actual eta2 moments behind Helfgott, arXiv:1312.7748v2, Section 7.2.
AI wrote this Lean code, OpenAI Codex, task31, 2026-10-22.
Binary Goldbach remains open.
-/
import LeanLab.Helfgott2013.EtaTwo

open Real MeasureTheory Set
open scoped Interval

namespace LeanLab.Helfgott2013.EtaTwoMoments
open EtaTwo

/-- Polynomial logarithmic antiderivative on a positive interval. -/
theorem integral_pow_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (k : ℕ) (c : ℝ) :
    (∫ t in a..b, t ^ k * (Real.log t + c)) =
      b ^ (k + 1) * ((Real.log b + c) / (k + 1) - 1 / (k + 1 : ℝ) ^ 2) -
        a ^ (k + 1) * ((Real.log a + c) / (k + 1) - 1 / (k + 1 : ℝ) ^ 2) := by
  have hpos : ∀ t ∈ uIcc a b, 0 < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact ha.trans_le ht.1
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  have hd : ∀ t ∈ uIcc a b,
      HasDerivAt (fun t : ℝ => t ^ (k + 1) *
        ((Real.log t + c) / (k + 1) - 1 / (k + 1 : ℝ) ^ 2))
        (t ^ k * (Real.log t + c)) t := by
    intro t ht
    have h := ((hasDerivAt_pow (k + 1) t).mul
      ((((Real.hasDerivAt_log (hpos t ht).ne').add_const c).div_const (k + 1)).sub_const
        (1 / (k + 1 : ℝ) ^ 2)))
    have htne : t ≠ 0 := (hpos t ht).ne'
    convert h using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, one_mul]
    field_simp [htne, hk, pow_succ]
    <;> ring
  have hc : ContinuousOn (fun t : ℝ => t ^ k * (Real.log t + c)) (uIcc a b) :=
    (continuousOn_id.pow k).mul ((Real.continuousOn_log.mono
      (fun t ht => (hpos t ht).ne')).add_const c)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable

#print axioms integral_pow_log

/-- All nonnegative integer moments of the actual eta2 profile on its support. -/
theorem etaTwo_moment_compact (k : ℕ) :
    (∫ t in (1 / 4 : ℝ)..1, etaTwo t * t ^ k) =
      (2 * (1 - (1 / 2 : ℝ) ^ (k + 1)) / (k + 1)) ^ 2 := by
  have hc : ContinuousOn (fun t : ℝ => etaTwo t * t ^ k) (Icc (1 / 4 : ℝ) 1) :=
    continuousOn_etaTwo.mul (continuousOn_id.pow k)
  have hi : IntervalIntegrable (fun t : ℝ => etaTwo t * t ^ k) volume (1 / 4) 1 :=
    hc.intervalIntegrable_of_Icc (by norm_num)
  have hi1 : IntervalIntegrable (fun t : ℝ => etaTwo t * t ^ k) volume (1 / 4) (1 / 2) :=
    hi.mono_set (by norm_num [uIcc_of_le]; intro x hx; constructor <;> linarith [hx.1, hx.2])
  have hi2 : IntervalIntegrable (fun t : ℝ => etaTwo t * t ^ k) volume (1 / 2) 1 :=
    hi.mono_set (by norm_num [uIcc_of_le]; intro x hx; constructor <;> linarith [hx.1, hx.2])
  have lh : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have lq : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
    rw [show (1 / 4 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    norm_num
  have hleft : (∫ t in (1 / 4 : ℝ)..(1 / 2), etaTwo t * t ^ k) =
      4 * ∫ t in (1 / 4 : ℝ)..(1 / 2), t ^ k * (Real.log t + 2 * Real.log 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    dsimp only
    rw [etaTwo_on_support ⟨ht.1, by linarith [ht.2]⟩, if_pos ht.2]
    ring
  have hright : (∫ t in (1 / 2 : ℝ)..1, etaTwo t * t ^ k) =
      -4 * ∫ t in (1 / 2 : ℝ)..1, t ^ k * (Real.log t + 0) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    dsimp only
    rw [etaTwo_on_support ⟨by linarith [ht.1], ht.2⟩]
    by_cases hm : t ≤ 1 / 2
    · have he : t = 1 / 2 := by linarith [ht.1]
      subst t
      rw [if_pos (by norm_num), lh]
      ring
    · rw [if_neg hm]
      ring
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hleft, hright,
    integral_pow_log (by norm_num) (by norm_num),
    integral_pow_log (by norm_num) (by norm_num), lh, lq, Real.log_one]
  have hq : (1 / 4 : ℝ) ^ (k + 1) = ((1 / 2 : ℝ) ^ (k + 1)) ^ 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hq, one_pow]
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

#print axioms etaTwo_moment_compact

/-- The exact moment formula on the positive half line. -/
theorem etaTwo_moment (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), etaTwo t * t ^ k) =
      (2 * (1 - (1 / 2 : ℝ) ^ (k + 1)) / (k + 1)) ^ 2 := by
  have hs : ∀ t : ℝ, t ∉ Icc (1 / 4 : ℝ) 1 → etaTwo t * t ^ k = 0 := by
    intro t ht
    rw [etaTwo_eq_zero ht]
    simp
  have hp : ∀ t : ℝ, t ∉ Ioi (0 : ℝ) → etaTwo t * t ^ k = 0 := by
    intro t ht
    apply hs
    simp only [mem_Ioi, not_lt] at ht
    intro hmem
    linarith [hmem.1]
  calc
    _ = ∫ t : ℝ, etaTwo t * t ^ k := setIntegral_eq_integral_of_forall_compl_eq_zero hp
    _ = ∫ t in Icc (1 / 4 : ℝ) 1, etaTwo t * t ^ k :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hs).symm
    _ = ∫ t in (1 / 4 : ℝ)..1, etaTwo t * t ^ k := by
      rw [intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]
    _ = _ := etaTwo_moment_compact k

#print axioms etaTwo_moment

/-- The mass and first two moments actually used in Section 7.2. -/
theorem etaTwo_first_three_moments :
    (∫ t in Ioi (0 : ℝ), etaTwo t) = 1 ∧
      (∫ t in Ioi (0 : ℝ), etaTwo t * t) = 9 / 16 ∧
        (∫ t in Ioi (0 : ℝ), etaTwo t * t ^ 2) = 49 / 144 := by
  have h0 := etaTwo_moment 0
  have h1 := etaTwo_moment 1
  have h2 := etaTwo_moment 2
  norm_num at h0 h1 h2
  exact ⟨h0, h1, h2⟩

#print axioms etaTwo_first_three_moments

/-- The antiderivative for the inverse weighted eta2 mass. -/
theorem integral_log_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (c : ℝ) :
    (∫ t in a..b, (Real.log t + c) / t) =
      ((Real.log b + c) ^ 2 - (Real.log a + c) ^ 2) / 2 := by
  have hpos : ∀ t ∈ uIcc a b, 0 < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact ha.trans_le ht.1
  have hd : ∀ t ∈ uIcc a b,
      HasDerivAt (fun t : ℝ => (Real.log t + c) ^ 2 / 2)
        ((Real.log t + c) / t) t := by
    intro t ht
    have h := (((Real.hasDerivAt_log (hpos t ht).ne').add_const c).pow 2).div_const 2
    convert h using 1 <;> ring
  have hc : ContinuousOn (fun t : ℝ => (Real.log t + c) / t) (uIcc a b) :=
    ((Real.continuousOn_log.mono (fun t ht => (hpos t ht).ne')).add_const c).div
      continuousOn_id (fun t ht => (hpos t ht).ne')
  convert intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable using 1 <;> ring

#print axioms integral_log_div

/-- The inverse weighted eta2 mass on its compact support. -/
theorem etaTwo_div_moment_compact :
    (∫ t in (1 / 4 : ℝ)..1, etaTwo t / t) = 4 * Real.log 2 ^ 2 := by
  have hc : ContinuousOn (fun t : ℝ => etaTwo t / t) (Icc (1 / 4 : ℝ) 1) :=
    continuousOn_etaTwo.div continuousOn_id (by
      intro t ht
      linarith [ht.1])
  have hi : IntervalIntegrable (fun t : ℝ => etaTwo t / t) volume (1 / 4) 1 :=
    hc.intervalIntegrable_of_Icc (by norm_num)
  have hi1 : IntervalIntegrable (fun t : ℝ => etaTwo t / t) volume (1 / 4) (1 / 2) :=
    hi.mono_set (by norm_num [uIcc_of_le]; intro x hx; constructor <;> linarith [hx.1, hx.2])
  have hi2 : IntervalIntegrable (fun t : ℝ => etaTwo t / t) volume (1 / 2) 1 :=
    hi.mono_set (by norm_num [uIcc_of_le]; intro x hx; constructor <;> linarith [hx.1, hx.2])
  have lh : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have lq : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
    rw [show (1 / 4 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    norm_num
  have hleft : (∫ t in (1 / 4 : ℝ)..(1 / 2), etaTwo t / t) =
      2 * Real.log 2 ^ 2 := by
    calc
      _ = ∫ t in (1 / 4 : ℝ)..(1 / 2), 4 * ((Real.log t + 2 * Real.log 2) / t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num)] at ht
        dsimp only
        rw [etaTwo_on_support ⟨ht.1, by linarith [ht.2]⟩, if_pos ht.2]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          integral_log_div (by norm_num) (by norm_num), lh, lq]
        ring
  have hright : (∫ t in (1 / 2 : ℝ)..1, etaTwo t / t) =
      2 * Real.log 2 ^ 2 := by
    calc
      _ = ∫ t in (1 / 2 : ℝ)..1, -4 * ((Real.log t + 0) / t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num)] at ht
        dsimp only
        rw [etaTwo_on_support ⟨by linarith [ht.1], ht.2⟩]
        by_cases hm : t ≤ 1 / 2
        · have he : t = 1 / 2 := by linarith [ht.1]
          subst t
          rw [if_pos (by norm_num), lh]
          ring
        · rw [if_neg hm]
          ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          integral_log_div (by norm_num) (by norm_num), Real.log_one, lh]
        ring
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hleft, hright]
  ring

#print axioms etaTwo_div_moment_compact

end LeanLab.Helfgott2013.EtaTwoMoments
