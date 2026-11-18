import LeanLab.HelfgottMajor.SPLIT_book_count_band_very_low_mult_le

/-!
# Split of `very_low_real_zero_card_le_one`

The target bounds by one the number of strip zeros of one primitive `L`-function whose
imaginary part vanishes, on the band `1 ≤ T`, `q * T ≤ 2πe`. Two features of the band matter.
The height enters only through `T ≥ 1`, which puts every real part in the open unit interval
below the truncation height, so the truncation itself is invisible. And the band bounds the
conductor, `q ≤ 2πe`, so only the finitely many `L`-functions of conductor at most seventeen
are consulted.

The count is cut along the character into three cases, each stated for a real argument instead
of for a finite set of points of the complex plane, and each keeping the band:

* `very_low_real_zero_modulus_one`: the conductor is one, so the `L`-function is the zeta
  function, which has no zero on the open unit interval of the real axis; the count is zero.
* `very_low_real_zero_real_valued`: the character takes real values and the conductor is at
  least two; two real arguments of the open unit interval at which the `L`-function vanishes
  are equal, so at most one point is counted.
* `very_low_real_zero_not_real_valued`: the character takes a value with non-zero imaginary
  part and the conductor is at least two; then the open unit interval carries no zero at all,
  and nothing is counted.

The transfer from the finite set of points to the real line is elementary and is carried out
below instead of being left as a leaf: a strip zero with vanishing imaginary part is the
coercion of its real part, so two such zeros with equal real parts coincide, and a finite set
whose elements are pairwise equal has at most one element.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-! ## The real paired series -/

/-- Each paired term is positive. -/
private lemma pairTerm_pos {a b x : ℝ} (ha : 0 < a) (hab : a < b) (hx : 0 < x) :
    0 < a ^ (-x) - b ^ (-x) := by
  have h : b ^ (-x) < a ^ (-x) := Real.rpow_lt_rpow_of_neg ha hab (by linarith)
  linarith

/-- Mean value bound for `t ↦ t ^ (-x)` on `[a, a+1]`: one paired term is at most `x a^{-x-1}`. -/
private lemma pairTerm_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    a ^ (-x) - (a + 1) ^ (-x) ≤ x * a ^ (-x - 1) := by
  have hmem_a : a ∈ Set.Icc a (a + 1) := ⟨le_rfl, by linarith⟩
  have hmem_b : a + 1 ∈ Set.Icc a (a + 1) := ⟨by linarith, le_rfl⟩
  have hderiv : ∀ t ∈ Set.Icc a (a + 1), DifferentiableAt ℝ (fun t : ℝ => t ^ (-x)) t := by
    intro t ht
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_of_lt_of_le ha ht.1)))).differentiableAt
  have hbound : ∀ t ∈ Set.Icc a (a + 1),
      ‖deriv (fun t : ℝ => t ^ (-x)) t‖ ≤ x * a ^ (-x - 1) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    have hd : deriv (fun t : ℝ => t ^ (-x)) t = -x * t ^ (-x - 1) :=
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht0))).deriv
    have hle : t ^ (-x - 1) ≤ a ^ (-x - 1) := Real.rpow_le_rpow_of_nonpos ha ht.1 (by linarith)
    rw [hd, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hx,
      abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    exact mul_le_mul_of_nonneg_left hle hx.le
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hderiv hbound (convex_Icc a (a + 1))
    hmem_a hmem_b
  have hnorm : ‖(a + 1 : ℝ) - a‖ = 1 := by norm_num
  rw [hnorm, mul_one] at h
  have hneg : (a + 1) ^ (-x) - a ^ (-x) ≤ 0 := by
    have hlt := Real.rpow_lt_rpow_of_neg ha (by linarith : a < a + 1) (by linarith : -x < 0)
    linarith
  rw [Real.norm_eq_abs, abs_of_nonpos hneg, neg_sub] at h
  exact h

/-- The shifted power series is summable past exponent minus one. -/
private lemma summable_one_add_rpow {p : ℝ} (hp : p < -1) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ p) := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ p) := (Real.summable_nat_rpow (p := p)).mpr hp
  have h2 := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ p) 1).mpr h
  simpa [Nat.cast_add, Nat.cast_one] using h2

set_option maxHeartbeats 1000000 in
/-- The paired series is summable for positive real exponent. -/
private lemma summable_pairTerm (x : ℝ) (hx : 0 < x) :
    Summable (fun k : ℕ => (2 * (k : ℝ) + 1) ^ (-x) - (2 * (k : ℝ) + 1 + 1) ^ (-x)) := by
  have hb : Summable (fun k : ℕ => x * (((k : ℝ) + 1) ^ (-x - 1))) :=
    (summable_one_add_rpow (p := -x - 1) (by linarith)).mul_left x
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hb
  · exact (pairTerm_pos (a := 2 * (k : ℝ) + 1) (b := 2 * (k : ℝ) + 1 + 1) (x := x)
      (by positivity) (by linarith) hx).le
  · have h1 := pairTerm_le (a := 2 * (k : ℝ) + 1) (x := x) (by positivity) hx
    have h2 : (2 * (k : ℝ) + 1) ^ (-x - 1) ≤ ((k : ℝ) + 1) ^ (-x - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have h3 : x * (2 * (k : ℝ) + 1) ^ (-x - 1) ≤ x * ((k : ℝ) + 1) ^ (-x - 1) :=
      mul_le_mul_of_nonneg_left h2 hx.le
    linarith

set_option maxHeartbeats 1000000 in
/-- The sum of the paired series is positive. -/
private lemma pairTsum_pos (x : ℝ) (hx : 0 < x) :
    0 < ∑' k : ℕ, ((2 * (k : ℝ) + 1) ^ (-x) - (2 * (k : ℝ) + 1 + 1) ^ (-x)) := by
  refine Summable.tsum_pos (summable_pairTerm x hx) (fun k => ?_) 0 ?_
  · exact (pairTerm_pos (a := 2 * (k : ℝ) + 1) (b := 2 * (k : ℝ) + 1 + 1) (x := x)
      (by positivity) (by linarith) hx).le
  · simpa using pairTerm_pos (a := 1) (b := 1 + 1) (x := x) (by norm_num) (by norm_num) hx

/-! ## The same series with the exponent allowed to be complex -/

/-- Mean value bound for `t ↦ (t : ℂ) ^ (-s)` on a real interval of positive numbers. -/
private lemma cpow_sub_cpow_norm_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {s : ℂ}
    (hs : 0 < s.re) :
    ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) * (b - a) := by
  have hsne : (-s) ≠ 0 := by
    intro h
    have : s.re = 0 := by simpa using congrArg Complex.re h
    linarith
  have hmem_a : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hmem_b : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hderiv : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun t : ℝ => (t : ℂ) ^ (-s)) t := by
    intro t ht
    exact (hasDerivAt_ofReal_cpow_const (ne_of_gt (lt_of_lt_of_le ha ht.1)) hsne).differentiableAt
  have hbound : ∀ t ∈ Set.Icc a b,
      ‖deriv (fun t : ℝ => (t : ℂ) ^ (-s)) t‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    have hd : deriv (fun t : ℝ => (t : ℂ) ^ (-s)) t = (-s) * (t : ℂ) ^ (-s - 1) :=
      (hasDerivAt_ofReal_cpow_const (ne_of_gt ht0) hsne).deriv
    have hnorm : ‖(t : ℂ) ^ (-s - 1)‖ = t ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [Complex.neg_re, Complex.sub_re, Complex.one_re]
    have hle : t ^ (-s.re - 1) ≤ a ^ (-s.re - 1) :=
      Real.rpow_le_rpow_of_nonpos ha ht.1 (by linarith)
    rw [hd, norm_mul, norm_neg, hnorm]
    exact mul_le_mul_of_nonneg_left hle (norm_nonneg s)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hderiv hbound (convex_Icc a b) hmem_a hmem_b
  have hnorm : ‖b - a‖ = b - a := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [hnorm] at h
  rw [norm_sub_rev]
  exact h

set_option maxHeartbeats 1000000 in
/-- The paired differences form an absolutely convergent series in every half plane `Re s > 0`. -/
private lemma summable_cpow_pair {s : ℂ} (hs : 0 < s.re) :
    Summable (fun k : ℕ =>
      ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-s))) := by
  have hb : Summable (fun k : ℕ => ‖s‖ * (((k : ℝ) + 1) ^ (-s.re - 1))) :=
    (summable_one_add_rpow (p := -s.re - 1) (by linarith)).mul_left ‖s‖
  refine Summable.of_norm_bounded hb (fun k => ?_)
  have h := cpow_sub_cpow_norm_le (a := 2 * (k : ℝ) + 1) (b := 2 * (k : ℝ) + 1 + 1) (s := s)
    (by positivity) (by linarith) hs
  have h2 : (2 * (k : ℝ) + 1) ^ (-s.re - 1) ≤ ((k : ℝ) + 1) ^ (-s.re - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have hb' : (2 * (k : ℝ) + 1 + 1 : ℝ) - (2 * (k : ℝ) + 1) = 1 := by ring
  rw [hb', mul_one] at h
  have h3 : ‖s‖ * (2 * (k : ℝ) + 1) ^ (-s.re - 1) ≤ ‖s‖ * ((k : ℝ) + 1) ^ (-s.re - 1) :=
    mul_le_mul_of_nonneg_left h2 (norm_nonneg s)
  linarith

set_option maxHeartbeats 4000000 in
/-- `F` is analytic on the half plane `Re s > 0`. -/
private lemma analyticAt_eta (s₀ : ℂ) (hs₀ : 0 < s₀.re) :
    AnalyticAt ℂ (fun s : ℂ => ∑' k : ℕ,
      ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-s))) s₀ := by
  set ρ : ℝ := min (s₀.re / 2) 1 with hρdef
  have hρpos : 0 < ρ := lt_min (by linarith) one_pos
  have hρle : ρ ≤ s₀.re / 2 := min_le_left _ _
  have hρle1 : ρ ≤ 1 := min_le_right _ _
  set U : Set ℂ := Metric.ball s₀ ρ with hUdef
  have hu : Summable (fun k : ℕ => (‖s₀‖ + 1) * (((k : ℝ) + 1) ^ (-s₀.re / 2 - 1))) :=
    (summable_one_add_rpow (p := -s₀.re / 2 - 1) (by linarith)).mul_left (‖s₀‖ + 1)
  have hbound : ∀ (k : ℕ) (w : ℂ), w ∈ U →
      ‖(((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-w) - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-w)‖
        ≤ (‖s₀‖ + 1) * (((k : ℝ) + 1) ^ (-s₀.re / 2 - 1)) := by
    intro k w hw
    have hdist : ‖w - s₀‖ < ρ := by
      simpa [U, Metric.mem_ball, dist_eq_norm] using hw
    have hwnorm : ‖w‖ ≤ ‖s₀‖ + 1 := by
      have h := norm_sub_norm_le w s₀
      linarith
    have hwre : s₀.re / 2 ≤ w.re := by
      have h1 : |w.re - s₀.re| ≤ ‖w - s₀‖ := Complex.abs_re_le_norm (w - s₀)
      have h2 : -(w.re - s₀.re) ≤ |w.re - s₀.re| := neg_le_abs _
      linarith
    have hwre0 : 0 < w.re := lt_of_lt_of_le (by linarith) hwre
    have h1 := cpow_sub_cpow_norm_le (a := 2 * (k : ℝ) + 1) (b := 2 * (k : ℝ) + 1 + 1)
      (s := w) (by positivity) (by linarith) hwre0
    have h2 : (2 * (k : ℝ) + 1) ^ (-w.re - 1) ≤ ((k : ℝ) + 1) ^ (-w.re - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have h3 : ((k : ℝ) + 1) ^ (-w.re - 1) ≤ ((k : ℝ) + 1) ^ (-s₀.re / 2 - 1) := by
      refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
      linarith
    have hb' : (2 * (k : ℝ) + 1 + 1 : ℝ) - (2 * (k : ℝ) + 1) = 1 := by ring
    rw [hb', mul_one] at h1
    calc ‖(((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-w)
          - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-w)‖
        ≤ ‖w‖ * (2 * (k : ℝ) + 1) ^ (-w.re - 1) := h1
      _ ≤ (‖s₀‖ + 1) * ((k : ℝ) + 1) ^ (-w.re - 1) := by
          refine mul_le_mul hwnorm h2 (by positivity) (by positivity)
      _ ≤ (‖s₀‖ + 1) * ((k : ℝ) + 1) ^ (-s₀.re / 2 - 1) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have hdiff : ∀ k : ℕ, DifferentiableOn ℂ
      (fun w : ℂ => (((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-w)
        - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-w)) U := by
    intro k w _
    refine DifferentiableAt.differentiableWithinAt ?_
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-w)) w :=
      (differentiableAt_id.neg).const_cpow
        (Or.inl (by simp only [ne_eq, Complex.ofReal_eq_zero]; positivity))
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-w)) w :=
      (differentiableAt_id.neg).const_cpow
        (Or.inl (by simp only [ne_eq, Complex.ofReal_eq_zero]; positivity))
    exact h1.sub h2
  have hd := differentiableOn_tsum_of_summable_norm hu hdiff Metric.isOpen_ball hbound
  exact hd.analyticAt (Metric.ball_mem_nhds s₀ hρpos)

/-- The paired series is analytic on the half plane `Re s > 0`. -/
private lemma analyticOnNhd_eta :
    AnalyticOnNhd ℂ (fun s : ℂ => ∑' k : ℕ,
      ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-s)))
      {s : ℂ | 0 < s.re} :=
  fun s hs => analyticAt_eta s hs

/-! ## `ζ` as a real series for `x > 1` -/

set_option maxHeartbeats 1000000 in
/-- For real `x > 1` the zeta function is the real Dirichlet series. -/
private lemma zeta_eq_ofReal_tsum {x : ℝ} (hx : 1 < x) :
    riemannZeta (x : ℂ) = (((∑' n : ℕ, ((n : ℝ) + 1) ^ (-x)) : ℝ) : ℂ) := by
  have hs : 1 < (x : ℂ).re := by simpa using hx
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  refine Eq.trans (tsum_congr fun n => ?_) (Complex.ofReal_tsum _).symm
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, one_div, ← Complex.cpow_neg]
  rw [show (-(x : ℂ)) = ((-x : ℝ) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_cpow hpos.le]

set_option maxHeartbeats 1000000 in
/-- The odd part of the shifted power series is summable past exponent one. -/
private lemma summable_odd_rpow {x : ℝ} (hx : 1 < x) :
    Summable (fun k : ℕ => (2 * (k : ℝ) + 1) ^ (-x)) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (summable_one_add_rpow (p := -x) (by linarith))
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

set_option maxHeartbeats 1000000 in
/-- The even part of the shifted power series is summable past exponent one. -/
private lemma summable_even_rpow {x : ℝ} (hx : 1 < x) :
    Summable (fun k : ℕ => (2 * (k : ℝ) + 1 + 1) ^ (-x)) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (summable_one_add_rpow (p := -x) (by linarith))
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

set_option maxHeartbeats 2000000 in
/-- Regrouping `ζ x` into odd and even parts: the paired series is `(1 - 2^{1-x}) ζ x`. -/
private lemma pair_identity_real {x : ℝ} (hx : 1 < x) :
    (∑' k : ℕ, ((2 * (k : ℝ) + 1) ^ (-x) - (2 * (k : ℝ) + 1 + 1) ^ (-x)))
      = (1 - (2 : ℝ) ^ (1 - x)) * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-x) := by
  have hf : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-x)) :=
    summable_one_add_rpow (p := -x) (by linarith)
  have hA : Summable (fun k : ℕ => (((2 * k : ℕ) : ℝ) + 1) ^ (-x)) :=
    (summable_odd_rpow (x := x) hx).congr fun k => by norm_num
  have hB : Summable (fun k : ℕ => (((2 * k + 1 : ℕ) : ℝ) + 1) ^ (-x)) :=
    (summable_even_rpow (x := x) hx).congr fun k => by norm_num
  have hZ : (∑' n : ℕ, ((n : ℝ) + 1) ^ (-x))
      = (∑' k : ℕ, (2 * (k : ℝ) + 1) ^ (-x))
        + (∑' k : ℕ, (2 * (k : ℝ) + 1 + 1) ^ (-x)) := by
    rw [← tsum_even_add_odd hA hB]
    congr 1
    · exact tsum_congr fun k => by norm_num
    · exact tsum_congr fun k => by norm_num
  have hB' : (∑' k : ℕ, (2 * (k : ℝ) + 1 + 1) ^ (-x))
      = (2 : ℝ) ^ (-x) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-x)) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by
      rw [show (2 * (k : ℝ) + 1 + 1) = 2 * ((k : ℝ) + 1) by ring,
        Real.mul_rpow (by norm_num) (by positivity)]
  have hsub : (∑' k : ℕ, ((2 * (k : ℝ) + 1) ^ (-x) - (2 * (k : ℝ) + 1 + 1) ^ (-x)))
      = (∑' k : ℕ, (2 * (k : ℝ) + 1) ^ (-x))
        - ∑' k : ℕ, (2 * (k : ℝ) + 1 + 1) ^ (-x) :=
    Summable.tsum_sub (summable_odd_rpow hx) (summable_even_rpow hx)
  have ha : (∑' k : ℕ, (2 * (k : ℝ) + 1) ^ (-x))
      = (∑' n : ℕ, ((n : ℝ) + 1) ^ (-x)) - (∑' k : ℕ, (2 * (k : ℝ) + 1 + 1) ^ (-x)) := by
    linarith [hZ]
  have h2 : (2 : ℝ) ^ (1 - x) = 2 * 2 ^ (-x) := by
    rw [show (1 : ℝ) - x = 1 + (-x) by ring, Real.rpow_add (by norm_num)]
    norm_num
  rw [hsub, ha, hB', h2]
  ring

/-! ## The complex series at a real point -/

set_option maxHeartbeats 1000000 in
/-- At a real point each term of the complex paired series is the coercion of the real one. -/
private lemma eta_complex_term_eq (t : ℝ) (k : ℕ) :
    ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-(t : ℂ)) - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-(t : ℂ)))
      = (((2 * (k : ℝ) + 1) ^ (-t) - (2 * (k : ℝ) + 1 + 1) ^ (-t) : ℝ) : ℂ) := by
  have hexp : (-(t : ℂ)) = ((-t : ℝ) : ℂ) := by push_cast; ring
  rw [hexp, ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_cpow (by positivity),
    ← Complex.ofReal_sub]

set_option maxHeartbeats 1000000 in
/-- At a real point the complex paired series is the coercion of the sum of the real ones. -/
private lemma eta_complex_tsum_eq (t : ℝ) :
    (∑' k : ℕ,
        ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-(t : ℂ)) - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-(t : ℂ))))
      = ((∑' k : ℕ, ((2 * (k : ℝ) + 1) ^ (-t) - (2 * (k : ℝ) + 1 + 1) ^ (-t)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun k => eta_complex_term_eq t k

/-! ## The identity `F = (1 - 2^{1-s}) ζ` -/

set_option maxHeartbeats 1000000 in
/-- `s ↦ (1 - 2^{1-s}) ζ s` is analytic away from the pole of `ζ`. -/
private lemma analyticOnNhd_zetaMul :
    AnalyticOnNhd ℂ (fun s : ℂ => (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s)
      {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  intro s hs
  refine DifferentiableOn.analyticAt ?_ (isOpen_compl_singleton.mem_nhds hs.2)
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  have hb : DifferentiableAt ℂ (fun s : ℂ => (2 : ℂ) ^ ((1 : ℂ) - s)) z :=
    ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id).const_cpow
      (Or.inl (by norm_num))
  exact ((differentiableAt_const (c := (1 : ℂ))).sub hb).mul (differentiableAt_riemannZeta hz)

set_option maxHeartbeats 2000000 in
/-- The paired series equals `(1 - 2^{1-s}) ζ s` on `Re s > 1`. -/
private lemma eta_eq_zetaMul_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ,
        ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-s)))
      = (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s := by
  have hU : IsPreconnected {s : ℂ | 1 < s.re} := (convex_halfSpace_re_gt 1).isPreconnected
  have hF : AnalyticOnNhd ℂ (fun s : ℂ => ∑' k : ℕ,
      ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s)
        - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-s))) {s : ℂ | 1 < s.re} :=
    analyticOnNhd_eta.mono fun z hz => by simp only [Set.mem_ofPred_eq] at hz ⊢; linarith
  have hH : AnalyticOnNhd ℂ (fun s : ℂ => (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s)
      {s : ℂ | 1 < s.re} :=
    analyticOnNhd_zetaMul.mono fun z hz => by
      simp only [Set.mem_ofPred_eq] at hz ⊢
      refine ⟨by linarith, ?_⟩
      intro hc
      rw [hc] at hz
      norm_num at hz
  have hreal : ∀ t : ℝ, 1 < t →
      (∑' k : ℕ,
          ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-(t : ℂ))
            - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-(t : ℂ))))
      = (1 - (2 : ℂ) ^ ((1 : ℂ) - (t : ℂ))) * riemannZeta (t : ℂ) := by
    intro t ht
    have h2 : (((2 : ℝ) ^ (1 - t) : ℝ) : ℂ) = (2 : ℂ) ^ ((1 : ℂ) - (t : ℂ)) := by
      have hbase : ((2 : ℂ)) = (((2 : ℝ)) : ℂ) := by norm_num
      rw [hbase, show ((1 : ℂ) - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2) (1 - t)
    rw [eta_complex_tsum_eq t, zeta_eq_ofReal_tsum ht, pair_identity_real ht,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, h2]
  have hnot : ¬ (∀ᶠ z in 𝓝[≠] (2 : ℂ),
      (∑' k : ℕ,
          ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-z)
            - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-z)))
      ≠ (1 - (2 : ℂ) ^ ((1 : ℂ) - z)) * riemannZeta z) := by
    intro hev
    have hev' : {z : ℂ | (∑' k : ℕ,
          ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-z)
            - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-z)))
        ≠ (1 - (2 : ℂ) ^ ((1 : ℂ) - z)) * riemannZeta z} ∈ 𝓝[≠] (2 : ℂ) := hev
    rw [Metric.mem_nhdsWithin_iff] at hev'
    obtain ⟨ε, hε, hsub⟩ := hev'
    have ht1 : (1 : ℝ) < 2 + ε / 2 := by linarith
    have hne : ((2 + ε / 2 : ℝ) : ℂ) ≠ 2 := by
      have h : (2 + ε / 2 : ℝ) ≠ 2 := by linarith
      intro hc
      exact h (by exact_mod_cast hc)
    have hdist : ((2 + ε / 2 : ℝ) : ℂ) ∈ Metric.ball (2 : ℂ) ε := by
      have hnorm : ‖((2 + ε / 2 : ℝ) : ℂ) - 2‖ = ε / 2 := by
        have hsub : ((2 + ε / 2 : ℝ) : ℂ) - 2 = (((ε / 2 : ℝ)) : ℂ) := by
          push_cast
          ring
        rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      rw [Metric.mem_ball, dist_eq_norm, hnorm]
      linarith
    exact hsub ⟨hdist, hne⟩ (hreal (2 + ε / 2) ht1)
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ),
      (∑' k : ℕ,
          ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-z)
            - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-z)))
      = (1 - (2 : ℂ) ^ ((1 : ℂ) - z)) * riemannZeta z := by
    have := Filter.not_eventually.mp hnot
    simpa [not_ne_iff] using this
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hF hH hU (by norm_num) hfreq hs

set_option maxHeartbeats 4000000 in
/-- The paired series equals `(1 - 2^{1-s}) ζ s` at every real point `0 < σ < 1`. -/
private lemma eta_eq_zetaMul_of_real (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    (∑' k : ℕ,
        ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-(σ : ℂ))
          - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-(σ : ℂ))))
      = (1 - (2 : ℂ) ^ ((1 : ℂ) - (σ : ℂ))) * riemannZeta (σ : ℂ) := by
  set V : Set ℂ := {s : ℂ | σ / 2 < s.re ∧ 0 < s.im} with hV
  have hVconv : Convex ℝ V := (convex_halfSpace_re_gt (σ / 2)).inter (convex_halfSpace_im_gt 0)
  have hF : AnalyticOnNhd ℂ (fun s : ℂ => ∑' k : ℕ,
      ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s)
        - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-s))) V :=
    analyticOnNhd_eta.mono fun z hz => by
      simp only [hV, Set.mem_ofPred_eq] at hz ⊢
      linarith [hz.1]
  have hH : AnalyticOnNhd ℂ (fun s : ℂ => (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s) V :=
    analyticOnNhd_zetaMul.mono fun z hz => by
      simp only [hV, Set.mem_ofPred_eq] at hz ⊢
      refine ⟨by linarith [hz.1], ?_⟩
      intro hc
      rw [hc] at hz
      norm_num at hz
  have hz₀ : (((2 : ℝ)) : ℂ) + Complex.I ∈ V := by
    simp only [hV, Set.mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    constructor <;> linarith
  have hev : (fun s : ℂ => ∑' k : ℕ,
        ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s)
          - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-s)))
      =ᶠ[𝓝 ((((2 : ℝ)) : ℂ) + Complex.I)]
        (fun s : ℂ => (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s) := by
    refine Filter.eventually_of_mem ?_ fun z hz => eta_eq_zetaMul_of_one_lt_re hz
    exact (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
  have hEqOn : EqOn (fun s : ℂ => ∑' k : ℕ,
      ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s)
        - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-s)))
      (fun s : ℂ => (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s) V :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hF hH hVconv.isPreconnected hz₀ hev
  set u : ℕ → ℂ := fun n => (σ : ℂ) + Complex.I * ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) with hu
  have hmem : ∀ n : ℕ, u n ∈ V := by
    intro n
    have hre : (u n).re = σ := by
      simp only [hu, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add]
    have him : (u n).im = 1 / ((n : ℝ) + 1) := by
      simp only [hu, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, one_mul, mul_zero, add_zero, zero_add]
    refine ⟨?_, ?_⟩
    · rw [hre]; linarith
    · rw [him]; positivity
  have hseq : Tendsto u atTop (𝓝 ((σ : ℂ))) := by
    have hcont : Continuous fun t : ℝ => (σ : ℂ) + Complex.I * ((t : ℝ) : ℂ) := by fun_prop
    have h1 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) := by
      simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have h2 : Tendsto (fun n : ℕ => (σ : ℂ) + Complex.I * (((1 / ((n : ℝ) + 1) : ℝ)) : ℂ))
        atTop (𝓝 ((σ : ℂ) + Complex.I * ((0 : ℝ) : ℂ))) :=
      hcont.tendsto 0 |>.comp h1
    simpa only [hu, Complex.ofReal_zero, mul_zero, add_zero] using h2
  have hFcont : ContinuousAt (fun s : ℂ => ∑' k : ℕ,
      ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s)
        - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-s))) (σ : ℂ) :=
    (analyticAt_eta (σ : ℂ) (by simpa using h0)).continuousAt
  have hHcont : ContinuousAt
      (fun s : ℂ => (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s) (σ : ℂ) := by
    have hs1 : (σ : ℂ) ≠ 1 := by
      intro hc
      have h2 : σ = 1 := by exact_mod_cast hc
      linarith
    have hb : DifferentiableAt ℂ (fun s : ℂ => (2 : ℂ) ^ ((1 : ℂ) - s)) (σ : ℂ) :=
      ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id).const_cpow
        (Or.inl (by norm_num))
    exact (((differentiableAt_const (c := (1 : ℂ))).sub hb).mul
      (differentiableAt_riemannZeta hs1)).continuousAt
  have hlim1 : Tendsto (fun n : ℕ => (∑' k : ℕ,
        ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-(u n))
          - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-(u n)))))
      atTop (𝓝 (∑' k : ℕ,
        ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-(σ : ℂ))
          - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-(σ : ℂ))))) :=
    hFcont.tendsto.comp hseq
  have hlim2 : Tendsto (fun n : ℕ => (1 - (2 : ℂ) ^ ((1 : ℂ) - (u n))) * riemannZeta (u n))
      atTop (𝓝 ((1 - (2 : ℂ) ^ ((1 : ℂ) - (σ : ℂ))) * riemannZeta (σ : ℂ))) :=
    hHcont.tendsto.comp hseq
  have hsame : ∀ n : ℕ, (∑' k : ℕ,
        ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-(u n))
          - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-(u n))))
      = (1 - (2 : ℂ) ^ ((1 : ℂ) - (u n))) * riemannZeta (u n) :=
    fun n => hEqOn (hmem n)
  rw [funext hsame] at hlim1
  exact tendsto_nhds_unique hlim1 hlim2

set_option maxHeartbeats 1000000 in
/-- `ζ` has no zero at a real point of the open unit interval. -/
theorem riemannZeta_ne_zero_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  intro hz
  have hval := eta_eq_zetaMul_of_real σ h0 h1
  have hpos : 0 < ∑' k : ℕ, ((2 * (k : ℝ) + 1) ^ (-σ) - (2 * (k : ℝ) + 1 + 1) ^ (-σ)) :=
    pairTsum_pos σ h0
  have hFne : (∑' k : ℕ,
      ((((2 * (k : ℝ) + 1 : ℝ)) : ℂ) ^ (-(σ : ℂ))
        - (((2 * (k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-(σ : ℂ)))) ≠ 0 := by
    intro h
    rw [eta_complex_tsum_eq σ] at h
    exact hpos.ne' (Complex.ofReal_eq_zero.mp h)
  refine hFne ?_
  rw [hval, hz, mul_zero]

/-- LEAF. Case of conductor one. On the band `1 ≤ T`, `q * T ≤ 2πe`, if the conductor is one
then the `L`-function is the zeta function, and the strip carries no zero of vanishing
imaginary part: the count of such zeros is empty. Nothing is assumed about zeros off the real
axis, and the statement is only about the one `L`-function of conductor one. -/
theorem very_low_real_zero_modulus_one (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) (hq : q = 1) :
    ∀ ρ ∈ stripZeros χ T, ρ.im = 0 → False := by
  intro ρ hρ him
  subst hq
  simp only [stripZeros, Set.mem_ofPred_eq] at hρ
  obtain ⟨hL, h0, h1, _⟩ := hρ
  have hcast : ρ = ((ρ.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hL' : DirichletCharacter.LFunction χ ((ρ.re : ℝ) : ℂ) = 0 := by
    rw [← hcast]
    exact hL
  rw [DirichletCharacter.LFunction_modOne_eq] at hL'
  exact riemannZeta_ne_zero_of_mem_Ioo h0 h1 hL'

/-- LEAF. Case of a real valued character of conductor at least two. On the band `1 ≤ T`,
`q * T ≤ 2πe`, a primitive character taking only real values has at most one zero of the open
unit interval of the real axis: two real arguments there at which the `L`-function vanishes
are equal. The band is kept, so only conductors at most `2πe` are concerned. The multiplicity of
a zero and the position of the zeros off the real axis are not part of the statement. -/
theorem very_low_real_zero_real_valued (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    ∀ σ₁ σ₂ : ℝ, 0 < σ₁ → σ₁ < 1 → 0 < σ₂ → σ₂ < 1 →
      DirichletCharacter.LFunction χ (σ₁ : ℂ) = 0 →
      DirichletCharacter.LFunction χ (σ₂ : ℂ) = 0 → σ₁ = σ₂ := by
  sorry

/-- LEAF. Case of a character that is not real valued, of conductor at least two. On the band
`1 ≤ T`, `q * T ≤ 2πe`, a primitive character taking a value with non-zero imaginary part has
no zero at all on the open unit interval of the real axis: every real argument there at which
the `L`-function vanishes gives a contradiction. Nothing is assumed about zeros off the real
axis. -/
theorem very_low_real_zero_not_real_valued (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1)
    (hval : ∃ a : ZMod q, (χ a).im ≠ 0) :
    ∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction χ (σ : ℂ) = 0 → False := by
  sorry

/-- A point of the plane with vanishing imaginary part is the coercion of its real part. -/
private lemma eq_ofReal_re_of_im_eq_zero {ρ : ℂ} (him : ρ.im = 0) :
    ρ = ((ρ.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [him]

/-- A finite set of points all of whose elements are equal has at most one element, applied to
the strip zeros of vanishing imaginary part: two of them have the same real part, by the three
cases of the character, and then they coincide. -/
private lemma card_filter_im_eq_zero_le_one (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    ∀ ρ₁ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => ρ.im = 0),
      ∀ ρ₂ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => ρ.im = 0), ρ₁ = ρ₂ := by
  classical
  intro ρ₁ h₁ ρ₂ h₂
  obtain ⟨h₁s, him₁⟩ := Finset.mem_filter.mp h₁
  obtain ⟨h₂s, him₂⟩ := Finset.mem_filter.mp h₂
  have hmem₁ : ρ₁ ∈ stripZeros χ T := (stripZeros_finite χ T).mem_toFinset.mp h₁s
  have hmem₂ : ρ₂ ∈ stripZeros χ T := (stripZeros_finite χ T).mem_toFinset.mp h₂s
  have hcast₁ : ρ₁ = ((ρ₁.re : ℝ) : ℂ) := eq_ofReal_re_of_im_eq_zero him₁
  have hcast₂ : ρ₂ = ((ρ₂.re : ℝ) : ℂ) := eq_ofReal_re_of_im_eq_zero him₂
  have hL₁ : DirichletCharacter.LFunction χ ((ρ₁.re : ℝ) : ℂ) = 0 := by
    rw [← hcast₁]
    exact hmem₁.1
  have hL₂ : DirichletCharacter.LFunction χ ((ρ₂.re : ℝ) : ℂ) = 0 := by
    rw [← hcast₂]
    exact hmem₂.1
  have h0₁ : 0 < ρ₁.re := hmem₁.2.1
  have hlt₁ : ρ₁.re < 1 := hmem₁.2.2.1
  have h0₂ : 0 < ρ₂.re := hmem₂.2.1
  have hlt₂ : ρ₂.re < 1 := hmem₂.2.2.1
  by_cases hq : q = 1
  · exact (very_low_real_zero_modulus_one (q := q) χ hχ hT hband hq ρ₁ hmem₁ him₁).elim
  · by_cases hreal : ∀ a : ZMod q, (χ a).im = 0
    · have hre : ρ₁.re = ρ₂.re :=
        very_low_real_zero_real_valued (q := q) χ hχ hT hband hreal ρ₁.re ρ₂.re h0₁ hlt₁ h0₂ hlt₂ hL₁ hL₂
      rw [hcast₁, hcast₂, hre]
    · have hval : ∃ a : ZMod q, (χ a).im ≠ 0 := by
        by_contra h
        exact hreal fun a => by
          by_contra ha
          exact h ⟨a, ha⟩
      exact (very_low_real_zero_not_real_valued (q := q) χ hχ hT hband hval ρ₁.re h0₁ hlt₁ hL₁).elim

/-- Assembly: on the band `1 ≤ T`, `q * T ≤ 2πe`, the strip zeros of a primitive character
with vanishing imaginary part number at most one. Any two of them are equal by the three cases
of the character, and a finite set with pairwise equal elements has at most one element. -/
theorem very_low_real_zero_card_le_one_split (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    ((stripZeros_finite χ T).toFinset.filter (fun ρ => ρ.im = 0)).card ≤ 1 := by
  rw [Finset.card_le_one]
  exact card_filter_im_eq_zero_le_one χ hχ hT hband

end LeanLab.HelfgottMajor.ZeroCount1623
