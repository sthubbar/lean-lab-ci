/-
AI wrote this Lean code for CODEX task51.
P0074 pages 7 and 8, Lemma 3.1 with an explicit absolute constant.
The analytic existence bundles and ShortSecondMoment remain separate inputs.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.FractionGeometry

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
open LeanLab.PNTPort.LargeSieve
attribute [local instance] Classical.propDecidable

/-- The nonnearest fractions together cost at most Q cubed. -/
theorem interval_farey_remainder_le {Q : ℕ} (hQ : 0 < Q) (α t H : ℝ)
    {p0 : ℕ × ℕ} (hp0 : p0 ∈ farey Q)
    (hnear : ∀ p ∈ farey Q, dist0 (α - fareyPt p0) ≤ dist0 (α - fareyPt p)) :
    ‖∑ p ∈ (farey Q).erase p0, fareyCoeff p *
      ∑ n ∈ shortInterval t H, LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * (α - fareyPt p))‖ ≤ (Q : ℝ) ^ 3 := by
  have hb := weighted_farey_sum_le (Q := Q) (Finset.erase_subset p0 (farey Q))
    (fun p => ∑ n ∈ shortInterval t H, LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * (α - fareyPt p)))
    (sq_nonneg (Q : ℝ)) (fun p hp => interval_bound_off_nearest hQ α t H hp0 hnear
      (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp))
  exact hb.trans_eq (by ring)

/-- A matching reduced fraction contributes its coefficient times H with error at most 2Q cubed. -/
theorem lemma31_matching {Q : ℕ} (hQ : 0 < Q) {p0 : ℕ × ℕ}
    (hp0 : p0 ∈ farey Q) (t H : ℝ) (hH : 0 ≤ H) :
    ‖(∑ n ∈ shortInterval t H, (LamQ Q n : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * fareyPt p0)) -
      fareyCoeff p0 * (H : ℂ)‖ ≤ 2 * (Q : ℝ) ^ 3 := by
  have hnear : ∀ p ∈ farey Q,
      dist0 (fareyPt p0 - fareyPt p0) ≤ dist0 (fareyPt p0 - fareyPt p) := by
    intro p hp
    simpa [dist0] using dist0_nonneg (fareyPt p0 - fareyPt p)
  have hr := interval_farey_remainder_le hQ (fareyPt p0) t H hp0 hnear
  have hcount : ‖fareyCoeff p0 * (((shortInterval t H).card : ℂ) - H)‖ ≤ 1 := by
    rw [norm_mul]
    have hc : ‖(((shortInterval t H).card : ℂ) - H)‖ ≤ 1 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact shortInterval_card_error hH
    exact (mul_le_mul (fareyCoeff_norm_le_one hp0) hc (norm_nonneg _) zero_le_one).trans_eq
      (by ring)
  rw [shortInterval_LamQ_expansion]
  change ‖(∑ p ∈ farey Q, fareyCoeff p *
      ∑ n ∈ shortInterval t H, LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * (fareyPt p0 - fareyPt p))) -
        fareyCoeff p0 * (H : ℂ)‖ ≤ _
  rw [← Finset.sum_erase_add _ _ hp0]
  simp only [sub_self, mul_zero, e_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hid : ∀ A c : ℂ, A + c * ((shortInterval t H).card : ℂ) - c * H =
      A + c * (((shortInterval t H).card : ℂ) - H) := by intros; ring
  rw [hid]
  apply (norm_add_le _ _).trans
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ3 : (1 : ℝ) ≤ (Q : ℝ) ^ 3 := one_le_pow₀ hQ1
  linarith

/-- A rational frequency distinct from a Farey point has a denominator product bound. -/
theorem interval_bound_distinct_farey {Q R : ℕ} {p p' : ℕ × ℕ}
    (hp : p ∈ farey Q) (hp' : p' ∈ farey R) (hne : p ≠ p') (t H : ℝ) :
    ‖∑ n ∈ shortInterval t H, LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * (fareyPt p - fareyPt p'))‖ ≤
      (p.1 : ℝ) * p'.1 := by
  have hp1 : (0 : ℝ) < p.1 := by exact_mod_cast (mem_farey.mp hp).1
  have hp2 : (0 : ℝ) < p'.1 := by exact_mod_cast (mem_farey.mp hp').1
  have hs := farey_product_separation hp hp' hne
  have hd : 0 < dist0 (fareyPt p - fareyPt p') := lt_of_lt_of_le (by positivity) hs
  apply (shortInterval_exp_sum_le t H _ hd).trans
  apply (div_le_iff₀ (by positivity : 0 < 2 * dist0 (fareyPt p - fareyPt p'))).mpr
  have hscaled := (div_le_iff₀ (mul_pos hp1 hp2)).mp hs
  nlinarith only [hscaled]

/-- A denominator above Q gives the qQ plus Q cubed branch. -/
theorem lemma31_nonmatching {Q R : ℕ} (hQ : 0 < Q) {p' : ℕ × ℕ}
    (hp' : p' ∈ farey R) (hqQ : Q < p'.1) (t H : ℝ) :
    ‖∑ n ∈ shortInterval t H, (LamQ Q n : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * fareyPt p')‖ ≤
      (p'.1 : ℝ) * Q + (Q : ℝ) ^ 3 := by
  obtain ⟨p0, hp0, hnear⟩ := exists_nearest_farey hQ (fareyPt p')
  have hr := interval_farey_remainder_le hQ (fareyPt p') t H hp0 hnear
  have hne : p' ≠ p0 := by
    intro h
    have := (mem_farey.mp hp0).2.1
    rw [← h] at this
    omega
  have hg := interval_bound_distinct_farey hp' hp0 hne t H
  have hpQ : (p0.1 : ℝ) ≤ Q := by exact_mod_cast (mem_farey.mp hp0).2.1
  have hp1 : (0 : ℝ) ≤ p'.1 := by positivity
  have hn : ‖fareyCoeff p0 *
      ∑ n ∈ shortInterval t H, LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * (fareyPt p' - fareyPt p0))‖ ≤
        (p'.1 : ℝ) * Q := by
    rw [norm_mul]
    exact (mul_le_mul (fareyCoeff_norm_le_one hp0) hg (norm_nonneg _)
      zero_le_one).trans (by simpa using mul_le_mul_of_nonneg_left hpQ hp1)
  rw [shortInterval_LamQ_expansion]
  change ‖∑ p ∈ farey Q, fareyCoeff p *
    ∑ n ∈ shortInterval t H, LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * (fareyPt p' - fareyPt p))‖ ≤ _
  rw [← Finset.sum_erase_add _ _ hp0]
  exact (norm_add_le _ _).trans (by linarith)

/-- The full Lemma 3.1 holds with absolute constant two. -/
theorem lemma31_proved : Lemma31 := by
  refine ⟨2, by norm_num, ?_⟩
  intro Q q r H t hQ hq hr hH ht
  obtain ⟨a, haq, hac, he⟩ := normalize_numerator hq r hr
  have hp : (q, a) ∈ farey q := mem_farey.mpr ⟨hq, le_rfl, haq, hac⟩
  have hsum : (∑ n ∈ shortInterval t H, (LamQ Q n : ℂ) * LeanLab.PNTPort.LargeSieve.e ((r : ℝ) * n / q)) =
      ∑ n ∈ shortInterval t H, (LamQ Q n : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * fareyPt (q, a)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [he n]
    rfl
  rw [hsum]
  by_cases hqQ : q ≤ Q
  · rw [if_pos hqQ, if_pos hqQ]
    have hpQ : (q, a) ∈ farey Q := mem_farey.mpr ⟨hq, hqQ, haq, hac⟩
    have hc : ((ArithmeticFunction.moebius q : ℝ) * H / q.totient : ℂ) =
        fareyCoeff (q, a) * (H : ℂ) := by
      simp only [fareyCoeff, Complex.ofReal_div, Complex.ofReal_mul,
        Complex.ofReal_intCast, Complex.ofReal_natCast]
      ring
    rw [hc]
    exact lemma31_matching hQ hpQ t H hH.le
  · rw [if_neg hqQ, if_neg hqQ, sub_zero]
    have hb := lemma31_nonmatching hQ hp (by omega) t H
    have hn : (0 : ℝ) ≤ (q : ℝ) * Q + (Q : ℝ) ^ 3 := by positivity
    exact hb.trans (by dsimp at *; linarith)

#print axioms interval_farey_remainder_le
#print axioms lemma31_matching
#print axioms interval_bound_distinct_farey
#print axioms lemma31_nonmatching
#print axioms lemma31_proved
end LeanLab.Grimmelt2019.MainTerm
