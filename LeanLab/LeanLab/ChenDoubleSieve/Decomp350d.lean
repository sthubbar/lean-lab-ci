import LeanLab.ChenDoubleSieve.Decomp350a

/-!
Exact scalar reductions for the finite F13 computation.
Source: https://arxiv.org/pdf/0705.1652, page 41 equation 10.12 and page 42.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Task350
open Task275

/-- Integrate the logarithmic inner kernel exactly.
Source: page 41 equation 10.12, derived elementary antiderivative. -/
theorem integral_log_ratio_div {a k : ℝ} (ha : 0 < a) (hak : a ≤ k) :
    (∫ t in a..k, log (k / t) / t) = log (k / a) ^ 2 / 2 := by
  have hk := ha.trans_le hak
  have hc : ContinuousOn (fun t => -(log k - log t) ^ 2 / 2) (Icc a k) := by
    exact ((continuousOn_const.sub (continuousOn_id.log
      (fun t ht => (ha.trans_le ht.1).ne'))).pow 2).neg.div_const 2
  have hi : IntervalIntegrable (fun t => log (k / t) / t) volume a k := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hak]
    apply ContinuousOn.div _ continuousOn_id (fun t ht => ne_of_gt (ha.trans_le ht.1))
    apply ContinuousOn.log
    · exact continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt (ha.trans_le ht.1))
    · intro t ht
      exact (div_pos hk (ha.trans_le ht.1)).ne'
  have hd : ∀ t ∈ Ioo a k,
      HasDerivAt (fun x => -(log k - log x) ^ 2 / 2) (log (k / t) / t) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans ht.1)
    have hh := (((hasDerivAt_const t (log k)).sub (hasDerivAt_log ht0)).pow 2).neg.div_const 2
    convert hh using 1 <;> first
    | rfl
    | (simp only [Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, id_eq,
        Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_sub]
       rw [log_div hk.ne' ht0]
       field_simp [ht0]
       <;> ring)
  have he := integral_eq_sub_of_hasDerivAt_of_le hak hc hd hi
  rw [log_div hk.ne' ha.ne']
  convert he using 1 <;> ring

/-- Integrate the squared logarithm over the squared denominator exactly.
Source: page 41 equation 10.12, derived elementary antiderivative. -/
theorem integral_log_ratio_sq_div_sq {a k : ℝ} (ha : 0 < a) (hak : a ≤ k) :
    (∫ t in a..k, log (k / t) ^ 2 / t ^ 2) =
      (log (k / a) ^ 2 - 2 * log (k / a) + 2) / a - 2 / k := by
  have hk := ha.trans_le hak
  let A : ℝ → ℝ := fun t => -((log k - log t) ^ 2 - 2 * (log k - log t) + 2) / t
  have hc : ContinuousOn A (Icc a k) := by
    dsimp [A]
    exact ((((continuousOn_const.sub (continuousOn_id.log
      (fun t ht => (ha.trans_le ht.1).ne'))).pow 2).sub
      ((continuousOn_const.sub (continuousOn_id.log
        (fun t ht => (ha.trans_le ht.1).ne'))).const_mul 2)).add continuousOn_const).neg.div
      continuousOn_id (fun t ht => (ha.trans_le ht.1).ne')
  have hi : IntervalIntegrable (fun t => log (k / t) ^ 2 / t ^ 2) volume a k := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hak]
    apply ContinuousOn.div _ (by fun_prop)
      (fun t ht => pow_ne_zero _ (ne_of_gt (ha.trans_le ht.1)))
    apply ContinuousOn.pow
    apply ContinuousOn.log
    · exact continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt (ha.trans_le ht.1))
    · intro t ht
      exact (div_pos hk (ha.trans_le ht.1)).ne'
  have hd : ∀ t ∈ Ioo a k, HasDerivAt A (log (k / t) ^ 2 / t ^ 2) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans ht.1)
    have hL := (hasDerivAt_const t (log k)).sub (hasDerivAt_log ht0)
    have hP := (((hL.pow 2).sub (hL.const_mul 2)).add_const 2).neg
    have hh := hP.div (hasDerivAt_id t) ht0
    convert hh using 1 <;> first
    | rfl
    | (simp only [A, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, id_eq,
        Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_sub]
       rw [log_div hk.ne' ht0]
       field_simp [ht0]
       <;> ring)
  have he := integral_eq_sub_of_hasDerivAt_of_le hak hc hd hi
  dsimp [A] at he
  rw [log_div hk.ne' ha.ne']
  convert he using 1 <;> ring

/-- The F13 threefold majorant is exactly a single elementary integral.
Source: page 41 equation 10.12, derived exact reduction. -/
theorem logMajorant13_eq {c a b : ℝ} (hab : a ≤ b)
    (ha : kappa1 ≤ a) (hb : b ≤ kappa2) (weight : ℝ → ℝ) :
    logMajorant c id (fun _ => kappa2) a b weight =
      ∫ t in a..b,
        (c / 2 * ((log (kappa2 / t) ^ 2 - 2 * log (kappa2 / t) + 2) / t -
          2 / kappa2)) / weight t := by
  unfold logMajorant
  apply integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num [kappa1] : (0 : ℝ) < kappa1) (ha.trans ht.1)
  have htk : t ≤ kappa2 := ht.2.trans hb
  dsimp only
  congr 1
  calc
    _ = ∫ t2 in t..kappa2, (c / 2) * (log (kappa2 / t2) ^ 2 / t2 ^ 2) := by
      apply integral_congr
      intro t2 ht2
      rw [uIcc_of_le htk] at ht2
      have ht20 := ht0.trans_le ht2.1
      have he : (∫ t3 in t2..kappa2, c * log (kappa2 / id t3) / t3) =
          c * (log (kappa2 / t2) ^ 2 / 2) := by
        rw [show (fun t3 => c * log (kappa2 / id t3) / t3) =
          (fun t3 => c * (log (kappa2 / t3) / t3)) by funext t3; dsimp; ring,
          intervalIntegral.integral_const_mul, integral_log_ratio_div ht20 ht2.2]
      dsimp only
      rw [he]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_log_ratio_sq_div_sq ht0 htk]

end LeanLab.ChenDoubleSieve.Task350
