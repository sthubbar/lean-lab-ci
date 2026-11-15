/-
P0069 Baker, Harman and Pintz 1997, page 3 condition iii display 1.8, and page 53.
A necessary condition for the OPEN leaf upper_short_coefficient of DecompC165dBase312.
If a coefficient b1 satisfies condition iii with density v and dominates the raw page 53
weight on J, then every prefix sum and every window sum of the raw weight over J is at most
the count of the summation range times v / log Y, up to Y L^(-A) for every A.
Nothing here proves or refutes the leaf. The leaf stays OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165dBase312

namespace LeanLab.BHP1997.Upper312Route
open Classical Complex DecompC165b DecompC165d

/-- P0069 Baker Harman Pintz 1997, page 3, condition iii, display 1.8, read at q = 1 and the
trivial character, where delta is 1 and chi(m) is 1. The complex norm in 1.8 is then the absolute
value of a real centered prefix sum over J. The constant is also at least e, so that
log x is at least 1 on the range. PROVED. AI wrote the Lean code. Goldbach is open.
Plain math: `|Σ_{m ∈ J, m ≤ t} (b(m) - v / log Y)| ≤ C Y L^(-A)` for x ≥ C, t ≤ 2Y. -/
theorem short_distribution_real_prefix {ε v : ℝ} {b : ℝ → ℕ → ℝ}
    (hdist : Task308.ShortDistribution ε v b) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, Real.exp 1 ≤ C ∧ ∀ x : ℝ, C ≤ x →
      ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            (b x m - v / Real.log (x ^ (11 / 20 + ε)))| ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C0, hC0⟩ := hdist A hA
  refine ⟨max C0 (Real.exp 1), le_max_right _ _, fun x hx t ht => ?_⟩
  have hxC : C0 ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hlog1 : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hlogA : (1 : ℝ) ≤ Real.log x ^ A := Real.one_le_rpow hlog1 hA.le
  have hh := hC0 x hxC 1 le_rfl (by simpa using hlogA) 1 t ht
  have hδ : Thm2.delta (1 : DirichletCharacter ℂ 1) = 1 := by simp [Thm2.delta]
  have he : (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      ((b x m : ℂ) * (1 : DirichletCharacter ℂ 1) (m : ZMod 1) -
        Thm2.delta (1 : DirichletCharacter ℂ 1) * v / Real.log (x ^ (11 / 20 + ε)))) =
      ((∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (b x m - v / Real.log (x ^ (11 / 20 + ε))) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun m _ => ?_
    have h1 : (m : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [h1, map_one, hδ]
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs] at hh
  refine hh.trans ?_
  have hY : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg hx0.le _
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (by linarith) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hY) hL

/-- P0069 Baker Harman Pintz 1997, page 3, condition iii, display 1.8 at the trivial character,
and page 53, "so that rho(m) <= b1(m)". If b1 satisfies condition iii with density v and
dominates the raw page 53 weight on J for large x, then each prefix sum of the raw weight
over J is at most the number of terms times v / log Y, up to Y L^(-A).
This is a necessary condition for any b1 as in the OPEN leaf upper_short_coefficient.
PROVED. AI wrote the Lean code. Goldbach is open.
Plain math: `Σ_{m ∈ J, m ≤ t} raw(m) ≤ #{m ∈ J, m ≤ t} v / log Y + C Y L^(-A)`. -/
theorem upper_majorant_prefix_le {ε v : ℝ} {b1 : ℝ → ℕ → ℝ}
    (hdist : Task308.ShortDistribution ε v b1)
    (hmaj : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x,
      upperRawWeight ε (x ^ (11 / 20 + ε)) m ≤ b1 x m) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            upperRawWeight ε (x ^ (11 / 20 + ε)) m ≤
          (((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)).card : ℝ) * v /
              Real.log (x ^ (11 / 20 + ε)) +
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C, hCe, hC⟩ := short_distribution_real_prefix hdist A hA
  obtain ⟨X, hX⟩ := hmaj
  refine ⟨max C X, fun x hx t ht => ?_⟩
  have hxC : C ≤ x := (le_max_left _ _).trans hx
  have hxX : X ≤ x := (le_max_right _ _).trans hx
  have hxe : Real.exp 1 ≤ x := hCe.trans hxC
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hlog1 : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hY : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg hx0.le _
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (by linarith) _
  have hconst : C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) ≤
      max C X * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hY) hL
  have h1 := (le_abs_self _).trans (hC x hxC t ht)
  have hsum : ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        upperRawWeight ε (x ^ (11 / 20 + ε)) m ≤
      ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t), b1 x m :=
    Finset.sum_le_sum fun m hm => hX x hxX m (Finset.mem_filter.mp hm).1
  have hsplit : ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (b1 x m - v / Real.log (x ^ (11 / 20 + ε))) =
      ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t), b1 x m -
        (((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)).card : ℝ) * v /
          Real.log (x ^ (11 / 20 + ε)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsplit] at h1
  linarith

/-- P0069 Baker Harman Pintz 1997, page 3, condition iii, display 1.8 at the trivial character,
and page 53, "so that rho(m) <= b1(m)". The window form of upper_majorant_prefix_le, from two
applications of the two-sided prefix estimate 1.8, at t and at s. If b1 satisfies condition iii
with density v and dominates the raw page 53 weight on J for large x, then each window sum of
the raw weight over J is at most the number of terms times v / log Y, up to 2 C Y L^(-A).
This is a necessary condition for any b1 as in the OPEN leaf upper_short_coefficient.
PROVED. AI wrote the Lean code. Goldbach is open.
Plain math: `Σ_{m ∈ J, s < m ≤ t} raw(m) ≤ #{m ∈ J, s < m ≤ t} v / log Y + 2 C Y L^(-A)`. -/
theorem upper_majorant_window_le {ε v : ℝ} {b1 : ℝ → ℕ → ℝ}
    (hdist : Task308.ShortDistribution ε v b1)
    (hmaj : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x,
      upperRawWeight ε (x ^ (11 / 20 + ε)) m ≤ b1 x m) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      ∀ s t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => s < (m : ℝ) ∧ (m : ℝ) ≤ t),
            upperRawWeight ε (x ^ (11 / 20 + ε)) m ≤
          (((rightInterval ε x).filter
              (fun m : ℕ => s < (m : ℝ) ∧ (m : ℝ) ≤ t)).card : ℝ) * v /
              Real.log (x ^ (11 / 20 + ε)) +
            2 * C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C, hCe, hC⟩ := short_distribution_real_prefix hdist A hA
  obtain ⟨X, hX⟩ := hmaj
  refine ⟨max C X, fun x hx s t ht => ?_⟩
  have hxC : C ≤ x := (le_max_left _ _).trans hx
  have hxX : X ≤ x := (le_max_right _ _).trans hx
  have hxe : Real.exp 1 ≤ x := hCe.trans hxC
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hlog1 : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hY : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg hx0.le _
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (by linarith) _
  have hC0 : 0 ≤ C := (Real.exp_pos 1).le.trans hCe
  have hR0 : 0 ≤ C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_nonneg (mul_nonneg hC0 hY) hL
  have hconst : C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) ≤
      max C X * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hY) hL
  by_cases hst : s ≤ t
  · have e1 : ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)).filter
        (fun m : ℕ => (m : ℝ) ≤ s) =
        (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ s) := by
      ext m
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hJ, _⟩, hs⟩
        exact ⟨hJ, hs⟩
      · rintro ⟨hJ, hs⟩
        exact ⟨⟨hJ, hs.trans hst⟩, hs⟩
    have e2 : ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)).filter
        (fun m : ℕ => ¬ (m : ℝ) ≤ s) =
        (rightInterval ε x).filter (fun m : ℕ => s < (m : ℝ) ∧ (m : ℝ) ≤ t) := by
      ext m
      simp only [Finset.mem_filter, not_le]
      constructor
      · rintro ⟨⟨hJ, htm⟩, hs⟩
        exact ⟨hJ, hs, htm⟩
      · rintro ⟨hJ, hs, htm⟩
        exact ⟨⟨hJ, htm⟩, hs⟩
    have hdecomp := Finset.sum_filter_add_sum_filter_not
      ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
      (fun m : ℕ => (m : ℝ) ≤ s)
      (fun m : ℕ => b1 x m - v / Real.log (x ^ (11 / 20 + ε)))
    rw [e1, e2] at hdecomp
    have hT := (le_abs_self _).trans (hC x hxC t ht)
    have hS := (neg_abs_le _).trans' (neg_le_neg (hC x hxC s (hst.trans ht)))
    have hsum : ∑ m ∈ (rightInterval ε x).filter
          (fun m : ℕ => s < (m : ℝ) ∧ (m : ℝ) ≤ t),
          upperRawWeight ε (x ^ (11 / 20 + ε)) m ≤
        ∑ m ∈ (rightInterval ε x).filter
          (fun m : ℕ => s < (m : ℝ) ∧ (m : ℝ) ≤ t), b1 x m :=
      Finset.sum_le_sum fun m hm => hX x hxX m (Finset.mem_filter.mp hm).1
    have hsplit : ∑ m ∈ (rightInterval ε x).filter
          (fun m : ℕ => s < (m : ℝ) ∧ (m : ℝ) ≤ t),
          (b1 x m - v / Real.log (x ^ (11 / 20 + ε))) =
        ∑ m ∈ (rightInterval ε x).filter
          (fun m : ℕ => s < (m : ℝ) ∧ (m : ℝ) ≤ t), b1 x m -
          (((rightInterval ε x).filter
            (fun m : ℕ => s < (m : ℝ) ∧ (m : ℝ) ≤ t)).card : ℝ) * v /
            Real.log (x ^ (11 / 20 + ε)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hsplit] at hdecomp
    linarith
  · have hempty : (rightInterval ε x).filter
        (fun m : ℕ => s < (m : ℝ) ∧ (m : ℝ) ≤ t) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro m _ hm
      exact hst (hm.1.le.trans hm.2)
    rw [hempty]
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_mul, zero_div,
      zero_add]
    linarith

/-- P0069 Baker Harman Pintz 1997, page 3, condition iii, display 1.8 at the trivial character,
and page 53, "so that rho(m) <= b1(m)", with the page 53 density
v1 = omega(1/c4)/c4 + deleted integral. The hypothesis is the conclusion of the OPEN leaf
upper_short_coefficient of DecompC165dBase312, copied verbatim. If any b1 as in that leaf
exists, then each prefix sum of the raw page 53 weight over J is at most the number of terms
times v1 / log Y, up to Y L^(-A). So this prefix bound for the raw weight is NECESSARY for
the leaf. This theorem does not prove the leaf, which stays OPEN.
PROVED. AI wrote the Lean code. Goldbach is open.
Plain math: `Σ_{m ∈ J, m ≤ t} raw(m) ≤ #{m ∈ J, m ≤ t} v1 / log Y + C Y L^(-A)`. -/
theorem upper_short_coefficient_prefix_necessary {ω : ℝ → ℝ} {B ε : ℝ}
    (h : ∃ b1 : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) b1 ∧
      Task308.ShortMeanSquare ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) b1 ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x,
        upperRawWeight ε (x ^ (11 / 20 + ε)) m ≤ b1 x m) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            upperRawWeight ε (x ^ (11 / 20 + ε)) m ≤
          (((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)).card : ℝ) *
              (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
                upperDeletedIntegral ω ε) /
              Real.log (x ^ (11 / 20 + ε)) +
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  obtain ⟨b1, -, hdist, -, hmaj⟩ := h
  exact upper_majorant_prefix_le hdist hmaj

end LeanLab.BHP1997.Upper312Route
