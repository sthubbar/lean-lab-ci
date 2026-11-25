import Mathlib

/-!
Certified upper bound for the logarithmic integral F10 of Wu 2004 Section 10,
equation 10.12, https://arxiv.org/pdf/0705.1652, page 41, whose printed value
appears in the final display on page 42. It is index 9 of `integralTerms` in
`Decomp275b.lean`, with sigma2 = 141/500 and kappa2 = 29/250.
The logarithm splits as log of 359/141 plus log of 1 - c t with c = 500/359.
The second logarithm is bounded above by minus its Taylor partial sum plus the Mathlib
remainder bound, the weight 1 over t times 1 - t splits as 1/t + 1/(1 - t), and
1/(1 - t) is bounded above by a geometric partial sum plus a remainder.
The resulting majorant is integrated exactly, and the constants log 2, log of 359/141
and log of 141/58 are certified by the same series lemma.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ChenDoubleSieve.Feed1122LogIntF10

open Real Finset MeasureTheory intervalIntegral

/-- Upper bound for minus log of 1 - x from the Mathlib series remainder. -/
theorem neg_log_one_sub_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    -log (1 - x) ≤ (∑ i ∈ range n, x ^ (i + 1) / ((i : ℝ) + 1)) + x ^ (n + 1) / (1 - x) := by
  have hx : |x| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_of_nonneg h0] at h
  have := (abs_le.mp h).1
  linarith

/-- Upper bound for log of 1 - x from the Mathlib series remainder. -/
theorem log_one_sub_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    log (1 - x) ≤ -(∑ i ∈ range n, x ^ (i + 1) / ((i : ℝ) + 1)) + x ^ (n + 1) / (1 - x) := by
  have hx : |x| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_of_nonneg h0] at h
  have := (abs_le.mp h).2
  linarith

/-- Taylor coefficient of minus log of 1 - c t, with c = 500/359. -/
noncomputable def lc (i : ℕ) : ℝ := (500 / 359 : ℝ) ^ (i + 1) / ((i : ℝ) + 1)

/-- Remainder coefficient. -/
noncomputable def rr (N : ℕ) : ℝ := 359 / 218 * (500 / 359 : ℝ) ^ (N + 1)

/-- Polynomial upper bound for the logarithm. -/
noncomputable def P (A : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  A - (∑ i ∈ range N, lc i * t ^ (i + 1)) + rr N * t ^ (N + 1)

/-- Geometric upper bound for 1/(1 - t). -/
noncomputable def G (k : ℕ) (t : ℝ) : ℝ := (∑ j ∈ range k, t ^ j) + 500 / 359 * t ^ k

/-- The polynomial part of the majorant, expanded into monomials. -/
noncomputable def Poly (A : ℝ) (N k : ℕ) (t : ℝ) : ℝ :=
  (∑ i ∈ range N, (-lc i) * t ^ i) + rr N * t ^ N + (∑ j ∈ range k, A * t ^ j) +
    A * (500 / 359) * t ^ k + (∑ i ∈ range N, ∑ j ∈ range k, (-lc i) * t ^ (i + 1 + j)) +
    (∑ i ∈ range N, (-lc i * (500 / 359)) * t ^ (i + 1 + k)) +
    (∑ j ∈ range k, rr N * t ^ (N + 1 + j)) + rr N * (500 / 359) * t ^ (N + 1 + k)

theorem poly_eq (A : ℝ) (N k : ℕ) (t : ℝ) :
    Poly A N k t = ((∑ i ∈ range N, (-lc i) * t ^ i) + rr N * t ^ N) + P A N t * G k t := by
  have e1 : (∑ i ∈ range N, ∑ j ∈ range k, (-lc i) * t ^ (i + 1 + j)) =
      -((∑ i ∈ range N, lc i * t ^ (i + 1)) * ∑ j ∈ range k, t ^ j) := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [pow_add]; ring
  have e2 : (∑ i ∈ range N, (-lc i * (500 / 359)) * t ^ (i + 1 + k)) =
      -((∑ i ∈ range N, lc i * t ^ (i + 1)) * (500 / 359 * t ^ k)) := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pow_add]; ring
  have e3 : (∑ j ∈ range k, rr N * t ^ (N + 1 + j)) =
      rr N * t ^ (N + 1) * ∑ j ∈ range k, t ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [pow_add]; ring
  have e4 : (∑ j ∈ range k, A * t ^ j) = A * ∑ j ∈ range k, t ^ j := by
    rw [Finset.mul_sum]
  have e5 : t ^ (N + 1 + k) = t ^ (N + 1) * t ^ k := pow_add _ _ _
  unfold Poly P G
  rw [e1, e2, e3, e4, e5]
  ring

/-- The 1/t part of the logarithm bound. -/
theorem P_div (A : ℝ) (N : ℕ) (t : ℝ) (ht : t ≠ 0) :
    P A N t / t = A * t⁻¹ + ((∑ i ∈ range N, (-lc i) * t ^ i) + rr N * t ^ N) := by
  have h : P A N t = A + t * ((∑ i ∈ range N, (-lc i) * t ^ i) + rr N * t ^ N) := by
    unfold P
    rw [mul_add, Finset.mul_sum]
    have : (∑ i ∈ range N, t * ((-lc i) * t ^ i)) = -∑ i ∈ range N, lc i * t ^ (i + 1) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [this]; ring
  rw [h]
  field_simp

/-- Pointwise logarithm bound on the interval. -/
theorem log_le_P (A : ℝ) (hA : log (359 / 141) ≤ A) (N : ℕ) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 141 / 500) :
    log (1 / (141 / 500 : ℝ) - 1 - t / (141 / 500)) ≤ P A N t := by
  set x : ℝ := 500 / 359 * t with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 141 / 359 := by rw [hxdef]; linarith
  have harg : 1 / (141 / 500 : ℝ) - 1 - t / (141 / 500) = 359 / 141 * (1 - x) := by
    rw [hxdef]; ring
  have hpos : 0 < 1 - x := by linarith
  rw [harg, Real.log_mul (by norm_num) hpos.ne']
  have h := log_one_sub_le x hx0 (by linarith) N
  have hsum : (∑ i ∈ range N, x ^ (i + 1) / ((i : ℝ) + 1)) = ∑ i ∈ range N, lc i * t ^ (i + 1) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hxdef, lc, mul_pow]; ring
  have hrem : x ^ (N + 1) / (1 - x) ≤ rr N * t ^ (N + 1) := by
    rw [div_le_iff₀ hpos, rr, hxdef, mul_pow]
    have hp : 0 ≤ (500 / 359 : ℝ) ^ (N + 1) * t ^ (N + 1) := by positivity
    have : (359 / 218 : ℝ) * (1 - 500 / 359 * t) ≥ 1 := by linarith
    nlinarith
  rw [hsum] at h
  unfold P
  set S := ∑ i ∈ range N, lc i * t ^ (i + 1)
  have hA' := hA
  linarith [h, hrem, hA']

/-- Geometric bound for 1/(1 - t) on the interval. -/
theorem inv_le_G (k : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 141 / 500) :
    1 / (1 - t) ≤ G k t := by
  have hpos : 0 < 1 - t := by linarith
  have hg : (∑ j ∈ range k, t ^ j) * (1 - t) = 1 - t ^ k := by
    have := geom_sum_mul t k
    linarith [this]
  rw [div_le_iff₀ hpos, G, add_mul, hg]
  have hp : 0 ≤ t ^ k := pow_nonneg ht0 k
  have : 0 ≤ t ^ k * (500 / 359 * (1 - t) - 1) := mul_nonneg hp (by linarith)
  nlinarith

/-- The majorant of the integrand. -/
noncomputable def M (A : ℝ) (N k : ℕ) (t : ℝ) : ℝ := A * t⁻¹ + Poly A N k t

theorem integrand_le (A : ℝ) (hA : log (359 / 141) ≤ A) (N k : ℕ) (t : ℝ)
    (ht0 : 29 / 250 ≤ t) (ht1 : t ≤ 141 / 500) :
    log (1 / (141 / 500 : ℝ) - 1 - t / (141 / 500)) / (t * (1 - t)) ≤ M A N k t := by
  have htp : 0 < t := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hL := log_le_P A hA N t htp.le ht1
  have hG := inv_le_G k t htp.le ht1
  have hlog0 : 0 ≤ log (1 / (141 / 500 : ℝ) - 1 - t / (141 / 500)) := by
    apply Real.log_nonneg
    have : t / (141 / 500 : ℝ) ≤ 1 := by rw [div_le_one (by norm_num)]; exact ht1
    have : (1 : ℝ) / (141 / 500) = 500 / 141 := by norm_num
    linarith
  set L := log (1 / (141 / 500 : ℝ) - 1 - t / (141 / 500))
  have hsplit : L / (t * (1 - t)) = L / t + L * (1 / (1 - t)) := by
    field_simp; ring
  have hPt : L / t ≤ P A N t / t := div_le_div_of_nonneg_right hL htp.le
  have hinv0 : 0 ≤ 1 / (1 - t) := by positivity
  have hP2 : L * (1 / (1 - t)) ≤ P A N t * G k t :=
    mul_le_mul hL hG hinv0 (le_trans hlog0 hL)
  rw [hsplit, M, poly_eq, P_div A N t htp.ne'] at *
  linarith

/-- Exact integral of a monomial sum. -/
theorem int_sum (a b : ℝ) (n : ℕ) (f : ℕ → ℝ) (e : ℕ → ℕ) :
    ∫ t in a..b, ∑ i ∈ range n, f i * t ^ e i =
      ∑ i ∈ range n, f i * ((b ^ (e i + 1) - a ^ (e i + 1)) / ((e i : ℝ) + 1)) := by
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [intervalIntegral.integral_const_mul, integral_pow]
  · intro i _
    exact (by fun_prop : Continuous fun t : ℝ => f i * t ^ e i).intervalIntegrable _ _

/-- Exact integral of a double monomial sum. -/
theorem int_sum2 (a b : ℝ) (n k : ℕ) (f : ℕ → ℝ) (e : ℕ → ℕ → ℕ) :
    ∫ t in a..b, ∑ i ∈ range n, ∑ j ∈ range k, f i * t ^ e i j =
      ∑ i ∈ range n, ∑ j ∈ range k,
        f i * ((b ^ (e i j + 1) - a ^ (e i j + 1)) / ((e i j : ℝ) + 1)) := by
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    exact int_sum a b k (fun _ => f i) (e i)
  · intro i _
    exact (by fun_prop : Continuous fun t : ℝ =>
      ∑ j ∈ range k, f i * t ^ e i j).intervalIntegrable _ _

/-- Exact integral of the polynomial part. -/
theorem integral_Poly (a b A : ℝ) (N k : ℕ) :
    ∫ t in a..b, Poly A N k t =
      (∑ i ∈ range N, (-lc i) * ((b ^ (i + 1) - a ^ (i + 1)) / ((i : ℝ) + 1))) +
      rr N * ((b ^ (N + 1) - a ^ (N + 1)) / ((N : ℝ) + 1)) +
      (∑ j ∈ range k, A * ((b ^ (j + 1) - a ^ (j + 1)) / ((j : ℝ) + 1))) +
      A * (500 / 359) * ((b ^ (k + 1) - a ^ (k + 1)) / ((k : ℝ) + 1)) +
      (∑ i ∈ range N, ∑ j ∈ range k, (-lc i) *
        ((b ^ (i + 1 + j + 1) - a ^ (i + 1 + j + 1)) / (((i + 1 + j : ℕ) : ℝ) + 1))) +
      (∑ i ∈ range N, (-lc i * (500 / 359)) *
        ((b ^ (i + 1 + k + 1) - a ^ (i + 1 + k + 1)) / (((i + 1 + k : ℕ) : ℝ) + 1))) +
      (∑ j ∈ range k, rr N *
        ((b ^ (N + 1 + j + 1) - a ^ (N + 1 + j + 1)) / (((N + 1 + j : ℕ) : ℝ) + 1))) +
      rr N * (500 / 359) *
        ((b ^ (N + 1 + k + 1) - a ^ (N + 1 + k + 1)) / (((N + 1 + k : ℕ) : ℝ) + 1)) := by
  unfold Poly
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_add]
  · have h1 := int_sum a b N (fun i => -lc i) (fun i => i)
    have h3 := int_sum a b k (fun _ => A) (fun j => j)
    have h5 := int_sum2 a b N k (fun i => -lc i) (fun i j => i + 1 + j)
    have h6 := int_sum a b N (fun i => -lc i * (500 / 359)) (fun i => i + 1 + k)
    have h7 := int_sum a b k (fun _ => rr N) (fun j => N + 1 + j)
    rw [h1, h3, h5, h6, h7]
    simp only [intervalIntegral.integral_const_mul, integral_pow]
  all_goals
    apply Continuous.intervalIntegrable
    fun_prop

/-- Certified upper bound for log 2 + minus log of 1 - x. -/
theorem log_two_sub_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    log 2 - log (1 - x) ≤
      0.6931471808 + (∑ i ∈ range n, x ^ (i + 1) / ((i : ℝ) + 1)) + x ^ (n + 1) / (1 - x) := by
  have := neg_log_one_sub_le x h0 h1 n
  have := Real.log_two_lt_d9
  linarith

theorem log_359_141_le : log (359 / 141 : ℝ) ≤ 934562498351 / 1000000000000 := by
  have he : log (359 / 141 : ℝ) = log 2 - log (1 - 77 / 359) := by
    rw [show (1 - 77 / 359 : ℝ) = (359 / 282)⁻¹ by norm_num, Real.log_inv,
      show (359 / 141 : ℝ) = 2 * (359 / 282) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [he]
  refine le_trans (log_two_sub_le (77 / 359) (by norm_num) (by norm_num) 18) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem log_141_58_le : log (141 / 58 : ℝ) ≤ 111039610009 / 125000000000 := by
  have he : log (141 / 58 : ℝ) = log 2 - log (1 - 25 / 141) := by
    rw [show (1 - 25 / 141 : ℝ) = (141 / 116)⁻¹ by norm_num, Real.log_inv,
      show (141 / 58 : ℝ) = 2 * (141 / 116) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [he]
  refine le_trans (log_two_sub_le (25 / 141) (by norm_num) (by norm_num) 18) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- The integral is at most the integral of the majorant. -/
theorem integral_le_M (A : ℝ) (hA : log (359 / 141) ≤ A) (N k : ℕ) :
    ∫ t in (29 / 250 : ℝ)..(141 / 500 : ℝ),
        log (1 / (141 / 500 : ℝ) - 1 - t / (141 / 500)) / (t * (1 - t)) ≤
      ∫ t in (29 / 250 : ℝ)..(141 / 500 : ℝ), M A N k t := by
  have hab : (29 / 250 : ℝ) ≤ 141 / 500 := by norm_num
  refine intervalIntegral.integral_mono_on hab ?_ ?_ ?_
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.div
    · apply ContinuousOn.log (by fun_prop)
      intro t ht
      have : t / (141 / 500 : ℝ) ≤ 1 := by rw [div_le_one (by norm_num)]; exact ht.2
      have : (1 : ℝ) / (141 / 500) = 500 / 141 := by norm_num
      linarith
    · fun_prop
    · intro t ht
      have h0 : 0 < t := by linarith [ht.1]
      have h1 : 0 < 1 - t := by linarith [ht.2]
      positivity
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    unfold M Poly
    apply ContinuousOn.add
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.inv₀ continuousOn_id
      intro t ht
      have : 0 < t := by linarith [ht.1]
      exact this.ne'
    · fun_prop
  · intro t ht
    exact integrand_le A hA N k t ht.1 ht.2

theorem integral_M (A : ℝ) (N k : ℕ) :
    ∫ t in (29 / 250 : ℝ)..(141 / 500 : ℝ), M A N k t =
      A * log (141 / 58) + ∫ t in (29 / 250 : ℝ)..(141 / 500 : ℝ), Poly A N k t := by
  unfold M
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    integral_inv_of_pos (by norm_num) (by norm_num)]
  · norm_num
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ continuousOn_id
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have : 0 < t := by linarith [ht.1]
    exact this.ne'
  · apply Continuous.intervalIntegrable
    unfold Poly
    fun_prop

/-- Wu 2004 page 41 equation 10.12 and page 42 final display: the value of F10 is at most
5.468377. Here sigma2 = 141/500 and kappa2 = 29/250. -/
theorem logint_F10 :
    8 * ∫ t in (29 / 250 : ℝ)..(141 / 500 : ℝ),
        Real.log (1 / (141 / 500 : ℝ) - 1 - t / (141 / 500)) / (t * (1 - t)) ≤ 5.468377 := by
  have hA := log_359_141_le
  have hL := log_141_58_le
  have h := integral_le_M _ hA 20 11
  rw [integral_M, integral_Poly] at h
  have hlog : (934562498351 / 1000000000000 : ℝ) * log (141 / 58) ≤
      934562498351 / 1000000000000 * (111039610009 / 125000000000) :=
    mul_le_mul_of_nonneg_left hL (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, lc, rr] at h
  norm_num at h hlog ⊢
  linarith

end LeanLab.ChenDoubleSieve.Feed1122LogIntF10
