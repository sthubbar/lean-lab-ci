import Mathlib

/-!
Certified upper bound for the logarithmic integral term of index 8 in `integralTerms` of
Decomp275b, the sum of the two weighted pieces of Wu 2004 Section 10, equation 10.11 and 10.12,
https://arxiv.org/pdf/0705.1652, page 41, whose numerical evaluation enters the final display
on page 42. Here kappa1 = 1/12 and sigma1 = 41/125 are written as literals.
Method: the integrand is log of 84/41 times 1 - 125 t/84, so the logarithm is at most a
certified upper bound for log of 84/41 minus a partial sum of the series of minus log of 1 - x.
The weight equals 1/t plus a rational function bounded above by an explicit polynomial.
The 1/t part integrates to a logarithm of a rational, the rest is integrated exactly.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ChenDoubleSieve.Feed1122LogIntF9

open Real Finset MeasureTheory intervalIntegral

/-- Series coefficient. -/
noncomputable def a (k : ℕ) : ℝ := (125 / 84 : ℝ) ^ (k + 1) / ((k : ℝ) + 1)

/-- Partial sum of the series of minus log of 1 - 125 t/84. -/
noncomputable def S (n : ℕ) (t : ℝ) : ℝ := ∑ k ∈ range n, a k * t ^ (k + 1)

theorem partial_le_neglog (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    ∑ i ∈ range n, x ^ (i + 1) / ((i : ℝ) + 1) ≤ -log (1 - x) := by
  have hx : |x| < 1 := by rw [abs_of_nonneg h0]; exact h1
  exact sum_le_hasSum (range n) (fun i _ => by positivity)
    (Real.hasSum_pow_div_log_of_abs_lt_one hx)

theorem neglog_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    -log (1 - x) ≤ ∑ i ∈ range n, x ^ (i + 1) / ((i : ℝ) + 1) + x ^ (n + 1) / (1 - x) := by
  have hx : |x| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_of_nonneg h0] at h
  have := (abs_le.mp h).1
  linarith

theorem arg_eq (t : ℝ) :
    1 / (41 / 125 : ℝ) - 1 - t / (41 / 125) = 84 / 41 * (1 - 125 / 84 * t) := by ring

theorem log_arg_le (Lh : ℝ) (hL : log (84 / 41) ≤ Lh) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 43 / 125) (n : ℕ) :
    log (1 / (41 / 125 : ℝ) - 1 - t / (41 / 125)) ≤ Lh - S n t := by
  have hx0 : 0 ≤ 125 / 84 * t := by positivity
  have hx1 : 125 / 84 * t < 1 := by linarith
  rw [arg_eq, Real.log_mul (by norm_num) (by linarith)]
  have h := partial_le_neglog (125 / 84 * t) hx0 hx1 n
  have hS : S n t = ∑ i ∈ range n, (125 / 84 * t) ^ (i + 1) / ((i : ℝ) + 1) := by
    unfold S
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [a, mul_pow]
    ring
  linarith

theorem log_arg_nonneg (t : ℝ) (ht1 : t ≤ 43 / 125) :
    0 ≤ log (1 / (41 / 125 : ℝ) - 1 - t / (41 / 125)) := by
  rw [arg_eq]
  apply Real.log_nonneg
  linarith

theorem int_le (lo hi Lh : ℝ) (n : ℕ) (g W : ℝ → ℝ) (hlo : 0 < lo) (hle : lo ≤ hi)
    (hhi : hi ≤ 43 / 125) (hL : log (84 / 41) ≤ Lh)
    (hgc : ContinuousOn g (Set.Icc lo hi)) (hWc : Continuous W)
    (hg : ∀ t ∈ Set.Icc lo hi, 0 ≤ g t ∧ g t ≤ t⁻¹ + W t) :
    ∫ t in lo..hi, log (1 / (41 / 125 : ℝ) - 1 - t / (41 / 125)) * g t ≤
      ∫ t in lo..hi, (Lh - S n t) * (t⁻¹ + W t) := by
  have hsub : Set.Icc lo hi ⊆ {0}ᶜ := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (lt_of_lt_of_le hlo ht.1)
  refine intervalIntegral.integral_mono_on hle ?_ ?_ ?_
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hle]
    apply ContinuousOn.mul _ hgc
    apply ContinuousOn.log (by fun_prop)
    intro t ht
    rw [arg_eq]
    have : t ≤ 43 / 125 := le_trans ht.2 hhi
    apply ne_of_gt
    nlinarith
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hle]
    apply ContinuousOn.mul
    · exact (by unfold S; fun_prop : Continuous fun t => Lh - S n t).continuousOn
    · exact ContinuousOn.add (continuousOn_inv₀.mono hsub) hWc.continuousOn
  · intro t ht
    have ht0 : 0 ≤ t := le_trans hlo.le ht.1
    have ht1 : t ≤ 43 / 125 := le_trans ht.2 hhi
    have hl := log_arg_le Lh hL t ht0 ht1 n
    have hl0 := log_arg_nonneg t ht1
    obtain ⟨hg0, hgW⟩ := hg t ht
    calc log (1 / (41 / 125 : ℝ) - 1 - t / (41 / 125)) * g t ≤ (Lh - S n t) * g t :=
          mul_le_mul_of_nonneg_right hl hg0
      _ ≤ (Lh - S n t) * (t⁻¹ + W t) := mul_le_mul_of_nonneg_left hgW (le_trans hl0 hl)

/-- Polynomial majorant of the weight minus 1/t. -/
noncomputable def Wp (b : ℕ → ℝ) (C : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ range m, b j * t ^ j + C * t ^ m

/-- The polynomial part of the majorant. -/
noncomputable def P (n : ℕ) (b : ℕ → ℝ) (C : ℝ) (m : ℕ) (Lh t : ℝ) : ℝ :=
  -(∑ k ∈ range n, a k * t ^ k) + (∑ j ∈ range m, Lh * b j * t ^ j) + Lh * C * t ^ m -
    (∑ k ∈ range n, ∑ j ∈ range m, a k * b j * t ^ (k + j + 1)) -
    ∑ k ∈ range n, a k * C * t ^ (k + m + 1)

theorem expand (n : ℕ) (b : ℕ → ℝ) (C : ℝ) (m : ℕ) (Lh t : ℝ) (ht : t ≠ 0) :
    (Lh - S n t) * (t⁻¹ + Wp b C m t) = Lh * t⁻¹ + P n b C m Lh t := by
  have h1 : S n t * t⁻¹ = ∑ k ∈ range n, a k * t ^ k := by
    unfold S
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [pow_succ]
    field_simp
  have h2 : S n t * (∑ j ∈ range m, b j * t ^ j) =
      ∑ k ∈ range n, ∑ j ∈ range m, a k * b j * t ^ (k + j + 1) := by
    unfold S
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  have h3 : S n t * (C * t ^ m) = ∑ k ∈ range n, a k * C * t ^ (k + m + 1) := by
    unfold S
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have h4 : Lh * (∑ j ∈ range m, b j * t ^ j) = ∑ j ∈ range m, Lh * b j * t ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  unfold P Wp
  linear_combination -h1 - h2 - h3 + h4

theorem isum (lo hi : ℝ) (f : ℕ → ℝ) (e : ℕ → ℕ) (s : Finset ℕ) :
    ∫ t in lo..hi, ∑ k ∈ s, f k * t ^ (e k) =
      ∑ k ∈ s, f k * ((hi ^ (e k + 1) - lo ^ (e k + 1)) / ((e k : ℝ) + 1)) := by
  rw [intervalIntegral.integral_finsetSum
    (fun k _ => (by fun_prop : Continuous fun t : ℝ => f k * t ^ (e k)).intervalIntegrable _ _)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [intervalIntegral.integral_const_mul, integral_pow]

theorem integral_P (n : ℕ) (b : ℕ → ℝ) (C : ℝ) (m : ℕ) (Lh lo hi : ℝ) :
    ∫ t in lo..hi, P n b C m Lh t =
      -(∑ k ∈ range n, a k * ((hi ^ (k + 1) - lo ^ (k + 1)) / ((k : ℝ) + 1))) +
      (∑ j ∈ range m, Lh * b j * ((hi ^ (j + 1) - lo ^ (j + 1)) / ((j : ℝ) + 1))) +
      Lh * C * ((hi ^ (m + 1) - lo ^ (m + 1)) / ((m : ℝ) + 1)) -
      (∑ k ∈ range n, ∑ j ∈ range m, a k * b j *
        ((hi ^ (k + j + 1 + 1) - lo ^ (k + j + 1 + 1)) / (((k + j + 1 : ℕ) : ℝ) + 1))) -
      ∑ k ∈ range n, a k * C *
        ((hi ^ (k + m + 1 + 1) - lo ^ (k + m + 1 + 1)) / (((k + m + 1 : ℕ) : ℝ) + 1)) := by
  have c : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable f volume lo hi :=
    fun f hf => hf.intervalIntegrable _ _
  unfold P
  rw [intervalIntegral.integral_sub (c _ (by fun_prop)) (c _ (by fun_prop)),
    intervalIntegral.integral_sub (c _ (by fun_prop)) (c _ (by fun_prop)),
    intervalIntegral.integral_add (c _ (by fun_prop)) (c _ (by fun_prop)),
    intervalIntegral.integral_add (c _ (by fun_prop)) (c _ (by fun_prop)),
    intervalIntegral.integral_neg]
  rw [isum lo hi a (fun k => k) (range n), isum lo hi (fun j => Lh * b j) (fun j => j) (range m),
    isum lo hi (fun k => a k * C) (fun k => k + m + 1) (range n),
    intervalIntegral.integral_const_mul, integral_pow]
  rw [intervalIntegral.integral_finsetSum
    (fun k _ => c _ (by fun_prop))]
  congr 2
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [isum lo hi (fun j => a k * b j) (fun j => k + j + 1) (range m)]

theorem bound_piece (lo hi Lh : ℝ) (n : ℕ) (g : ℝ → ℝ) (b : ℕ → ℝ) (C : ℝ) (m : ℕ)
    (hlo : 0 < lo) (hle : lo ≤ hi) (hhi : hi ≤ 43 / 125) (hL : log (84 / 41) ≤ Lh)
    (hgc : ContinuousOn g (Set.Icc lo hi))
    (hg : ∀ t ∈ Set.Icc lo hi, 0 ≤ g t ∧ g t ≤ t⁻¹ + Wp b C m t) :
    ∫ t in lo..hi, log (1 / (41 / 125 : ℝ) - 1 - t / (41 / 125)) * g t ≤
      Lh * log (hi / lo) + ∫ t in lo..hi, P n b C m Lh t := by
  have h := int_le lo hi Lh n g (Wp b C m) hlo hle hhi hL hgc
    (by unfold Wp; fun_prop) hg
  have hsub : Set.uIcc lo hi ⊆ {0}ᶜ := by
    rw [Set.uIcc_of_le hle]
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (lt_of_lt_of_le hlo ht.1)
  have he : ∫ t in lo..hi, (Lh - S n t) * (t⁻¹ + Wp b C m t) =
      ∫ t in lo..hi, (Lh * t⁻¹ + P n b C m Lh t) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    exact expand n b C m Lh t (by simpa using hsub ht)
  rw [he, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    integral_inv_of_pos hlo (lt_of_lt_of_le hlo hle)] at h
  · exact h
  · exact (ContinuousOn.mul continuousOn_const (continuousOn_inv₀.mono hsub)).intervalIntegrable
  · exact (by unfold P; fun_prop : Continuous (P n b C m Lh)).intervalIntegrable _ _

/-- Weight bound on the first piece. -/
theorem weight1 (t : ℝ) (ht : t ∈ Set.Icc (1 / 12 : ℝ) (1 / 10)) :
    0 ≤ 1 / (t * (1 - t) ^ 2) ∧
      1 / (t * (1 - t) ^ 2) ≤ t⁻¹ + Wp (fun j => (j : ℝ) + 2) (800 / 81) 6 t := by
  obtain ⟨h0, h1⟩ := ht
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < 1 - t := by linarith
  constructor
  · positivity
  have hsplit : 1 / (t * (1 - t) ^ 2) = t⁻¹ + (2 - t) / (1 - t) ^ 2 := by
    field_simp
    ring
  rw [hsplit]
  apply add_le_add le_rfl
  rw [div_le_iff₀ (by positivity)]
  unfold Wp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  have hk : 0 ≤ t ^ 6 * (800 / 81 * (1 - t) ^ 2 - 8 + 7 * t) :=
    mul_nonneg (by positivity) (by nlinarith)
  nlinarith [hk]

/-- Weight bound on the second piece. -/
theorem weight2 (t : ℝ) (ht : t ∈ Set.Icc (1 / 10 : ℝ) (41 / 125)) :
    0 ≤ 1 / (t * (1 - t)) ∧
      1 / (t * (1 - t)) ≤ t⁻¹ + Wp (fun _ => (1 : ℝ)) (125 / 84) 13 t := by
  obtain ⟨h0, h1⟩ := ht
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < 1 - t := by linarith
  constructor
  · positivity
  have hsplit : 1 / (t * (1 - t)) = t⁻¹ + 1 / (1 - t) := by
    field_simp
    ring
  rw [hsplit]
  apply add_le_add le_rfl
  rw [div_le_iff₀ ht1]
  unfold Wp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have hk : 0 ≤ t ^ 13 * (125 / 84 * (1 - t) - 1) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith [hk]

theorem logL_le : log (84 / 41) ≤ 35862236619 / 50000000000 := by
  have e : (84 / 41 : ℝ) = 2 / (1 - 1 / 42) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num)]
  have h := neglog_le (1 / 42) (by norm_num) (by norm_num) 8
  have h2 := Real.log_two_lt_d9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h h2 ⊢
  linarith

theorem log1_le : log ((1 / 10) / (1 / 12) : ℝ) ≤ 113950973 / 625000000 := by
  have e : ((1 / 10) / (1 / 12) : ℝ) = (1 - 1 / 6)⁻¹ := by norm_num
  rw [e, Real.log_inv]
  have h := neglog_le (1 / 6) (by norm_num) (by norm_num) 14
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith

theorem log2_le : log ((41 / 125) / (1 / 10) : ℝ) ≤ 7424021393 / 6250000000 := by
  have e : ((41 / 125) / (1 / 10) : ℝ) = 2 * (2 * (1 - 9 / 50)) := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  have h := partial_le_neglog (9 / 50) (by norm_num) (by norm_num) 14
  have h2 := Real.log_two_lt_d9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h h2 ⊢
  linarith

/-- Wu 2004 page 41 equations 10.11 and 10.12 and page 42 final display: the index 8 term of
`integralTerms` in Decomp275b, with kappa1 = 1/12 and sigma1 = 41/125, is at most 5.161945. -/
theorem logint_F9 :
    36 / 5 * (∫ t in (1 / 12 : ℝ)..(1 / 10 : ℝ),
      log (1 / (41 / 125 : ℝ) - 1 - t / (41 / 125)) / (t * (1 - t) ^ 2)) +
      8 * ∫ t in (1 / 10 : ℝ)..(41 / 125 : ℝ),
        log (1 / (41 / 125 : ℝ) - 1 - t / (41 / 125)) / (t * (1 - t)) ≤ 5.161945 := by
  set Lh : ℝ := 35862236619 / 50000000000 with hLh
  have hL : log (84 / 41) ≤ Lh := logL_le
  have e1 : ∫ t in (1 / 12 : ℝ)..(1 / 10 : ℝ),
      log (1 / (41 / 125 : ℝ) - 1 - t / (41 / 125)) / (t * (1 - t) ^ 2) =
      ∫ t in (1 / 12 : ℝ)..(1 / 10 : ℝ),
      log (1 / (41 / 125 : ℝ) - 1 - t / (41 / 125)) * (1 / (t * (1 - t) ^ 2)) :=
    intervalIntegral.integral_congr (fun t _ => div_eq_mul_one_div _ _)
  have e2 : ∫ t in (1 / 10 : ℝ)..(41 / 125 : ℝ),
      log (1 / (41 / 125 : ℝ) - 1 - t / (41 / 125)) / (t * (1 - t)) =
      ∫ t in (1 / 10 : ℝ)..(41 / 125 : ℝ),
      log (1 / (41 / 125 : ℝ) - 1 - t / (41 / 125)) * (1 / (t * (1 - t))) :=
    intervalIntegral.integral_congr (fun t _ => div_eq_mul_one_div _ _)
  have h1 := bound_piece (1 / 12) (1 / 10) Lh 7 (fun t => 1 / (t * (1 - t) ^ 2))
    (fun j => (j : ℝ) + 2) (800 / 81) 6 (by norm_num) (by norm_num) (by norm_num) hL
    (by
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro t ht
      have : 0 < t := by linarith [ht.1]
      have : 0 < 1 - t := by linarith [ht.2]
      positivity)
    weight1
  have h2 := bound_piece (1 / 10) (41 / 125) Lh 19 (fun t => 1 / (t * (1 - t)))
    (fun _ => (1 : ℝ)) (125 / 84) 13 (by norm_num) (by norm_num) (by norm_num) hL
    (by
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro t ht
      have : 0 < t := by linarith [ht.1]
      have : 0 < 1 - t := by linarith [ht.2]
      positivity)
    weight2
  rw [integral_P] at h1 h2
  have hm1 : Lh * log ((1 / 10) / (1 / 12) : ℝ) ≤ Lh * (113950973 / 625000000) :=
    mul_le_mul_of_nonneg_left log1_le (by rw [hLh]; norm_num)
  have hm2 : Lh * log ((41 / 125) / (1 / 10) : ℝ) ≤ Lh * (7424021393 / 6250000000) :=
    mul_le_mul_of_nonneg_left log2_le (by rw [hLh]; norm_num)
  rw [e1, e2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, a] at h1 h2
  rw [hLh] at h1 h2 hm1 hm2
  norm_num at h1 h2 hm1 hm2 ⊢
  linarith

/-- The same bound in the form left by `simp only [integralTerms, Matrix.cons_val]` followed by
`norm_num [kappa1, sigma1]` on the index 8 term of Decomp275b. -/
theorem logint_F9_normed :
    36 / 5 * (∫ t in (1 / 12 : ℝ)..(1 / 10 : ℝ),
      log (84 / 41 - t / (41 / 125)) / (t * (1 - t) ^ 2)) +
      8 * ∫ t in (1 / 10 : ℝ)..(41 / 125 : ℝ),
        log (84 / 41 - t / (41 / 125)) / (t * (1 - t)) ≤ 1032389 / 200000 := by
  have h := logint_F9
  norm_num at h
  exact h

end LeanLab.ChenDoubleSieve.Feed1122LogIntF9
