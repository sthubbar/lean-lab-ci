/-
Kumchev and Liu 2007, P0088, page 11 Lemma 3.4 and page 15, the paragraph
after display 52. Leaves for the two open declarations
`leaf_interior_left_half` and `leaf_interior_right_half` of
`SPLIT_lemma34_second_sum_dyadic`.

The reduction `leaf_interior_left_half_of_core` of `InteriorHalvesAux` already
cuts each leaf down to its core: eps below 1/6 and H below Y (log X)^(A/2),
Y = windowY X eps. Here each core is cut once more, at H = x, where x = Y / 4
on the left half and x = Y / 2 on the right half, so that the t range is the
dyadic range [x, 2 x] of Lemma 3.4.

* H at most x: Lemma 3.4 of page 11 with x, y = H, (m, k) = (p, m / p) and
  z = z1 = Y^(1/6 + eps/2), as the paper applies it on page 15. One HARD leaf
  per half states that instance with the hypotheses of Lemma 3.4 written with
  L = log x. Three MEDIUM leaves check those hypotheses from the hypotheses of
  the parent for large X: the size of the window, the comparison of the sieve
  cutoff z0 with x^(1/4) L^(-2B), and the range of z1. The transfer of the
  condition on alpha to display 41 is proved here.
* H between x and Y (log X)^(A/2): this band is outside the hypothesis
  y at most x of Lemma 3.4; one HARD leaf per half.

The assembly proves both parent statements from the leaves, byte identical.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.InteriorHalvesAux

namespace LeanLab.KumchevLiu2007.Eq33RouteD

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 11 Lemma 3.4 applied on page 15 to the second sum of display 52,
with x = Y / 4, y = H, (m, k) = (p, m / p), a_p the indicator of the primes of one
dyadic block between z1 and z0, and z = w, on the left half [Y / 4, Y / 2] of the t window,
which is the range [x, 2 x] of the lemma. The hypotheses are those of
Lemma 3.4 with L = log x: x^(1/2) at most y at most x, display 41, M at most
x^(1/4) L^(-2B) and 2 at most z at most y x^(-1/2) L^(-2B).
Class HARD. -/
theorem leaf_left_half_lemma34_instance (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ Y z1 z0 w H α : ℝ, ∀ q : ℕ, ∀ a : ℤ, ∀ M : ℝ,
        x0 ≤ Y / 4 → Real.sqrt (Y / 4) ≤ H → H ≤ Y / 4 →
        IsCoprime a (q : ℤ) → Real.log (Y / 4) ^ B ≤ (q : ℝ) →
        (q : ℝ) ≤ H / Real.log (Y / 4) ^ B →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        1 ≤ M → M ≤ (Y / 4) ^ (1 / 4 : ℝ) * (Real.log (Y / 4) ^ B) ^ (-2 : ℤ) →
        2 ≤ w → w ≤ H / Real.sqrt (Y / 4) * (Real.log (Y / 4) ^ B) ^ (-2 : ℤ) →
        (∫ t in (Y / 4)..(Y / 2),
          ‖∑ m ∈ (squareWindow (Y)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                z1 ≤ (p : ℝ) ∧
                (p : ℝ) < z0 ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (w) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log (Y / 4) ^ A := by
  sorry

/-- LEAF: the band of H between x = Y / 4 and Y (log X)^(A/2), Y = windowY X eps,
on the left half [Y / 4, Y / 2] of the t window, for eps below 1/6. This band lies in the
written H range of the parent but outside the hypothesis y at most x of
P0088 page 11 Lemma 3.4 as applied on page 15; it needs a reduction to
y at most x, for example by cutting the short interval into pieces of length
at most x and using the Cauchy Schwarz inequality, with B large enough that
q stays below x L^(-B') for the B' of Lemma 3.4.
Class HARD. -/
theorem leaf_left_half_band (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        windowY X ε / 4 < H →
        H < windowY X ε * Real.log X ^ (A / 2) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: P0088 page 11 Lemma 3.4 applied on page 15 to the second sum of display 52,
with x = Y / 2, y = H, (m, k) = (p, m / p), a_p the indicator of the primes of one
dyadic block between z1 and z0, and z = w, on the right half [Y / 2, Y] of the t window,
which is the range [x, 2 x] of the lemma. The hypotheses are those of
Lemma 3.4 with L = log x: x^(1/2) at most y at most x, display 41, M at most
x^(1/4) L^(-2B) and 2 at most z at most y x^(-1/2) L^(-2B). On this half t + H may pass Y, so the sum keeps the summation
condition m^2 below Y, which Lemma 3.4 removes with the variant
U at most mk below U' of Lemma 3.3 of page 10.
Class HARD. -/
theorem leaf_right_half_lemma34_instance (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ Y z1 z0 w H α : ℝ, ∀ q : ℕ, ∀ a : ℤ, ∀ M : ℝ,
        x0 ≤ Y / 2 → Real.sqrt (Y / 2) ≤ H → H ≤ Y / 2 →
        IsCoprime a (q : ℤ) → Real.log (Y / 2) ^ B ≤ (q : ℝ) →
        (q : ℝ) ≤ H / Real.log (Y / 2) ^ B →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        1 ≤ M → M ≤ (Y / 2) ^ (1 / 4 : ℝ) * (Real.log (Y / 2) ^ B) ^ (-2 : ℤ) →
        2 ≤ w → w ≤ H / Real.sqrt (Y / 2) * (Real.log (Y / 2) ^ B) ^ (-2 : ℤ) →
        (∫ t in (Y / 2)..(Y),
          ‖∑ m ∈ (squareWindow (Y)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                z1 ≤ (p : ℝ) ∧
                (p : ℝ) < z0 ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (w) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log (Y / 2) ^ A := by
  sorry

/-- LEAF: the band of H between x = Y / 2 and Y (log X)^(A/2), Y = windowY X eps,
on the right half [Y / 2, Y] of the t window, for eps below 1/6. This band lies in the
written H range of the parent but outside the hypothesis y at most x of
P0088 page 11 Lemma 3.4 as applied on page 15; it needs a reduction to
y at most x, for example by cutting the short interval into pieces of length
at most x and using the Cauchy Schwarz inequality, with B large enough that
q stays below x L^(-B') for the B' of Lemma 3.4.
Class HARD. -/
theorem leaf_right_half_band (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        windowY X ε / 2 < H →
        H < windowY X ε * Real.log X ^ (A / 2) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in (windowY X ε / 2)..(windowY X ε),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry
/-- LEAF: P0088 page 15, the size of the window Y = windowY X eps = X^(7/12 + eps/2)
of display 34 against x = Y / c, c between 2 and 4, for large X: x passes any
given x0, L = log x is positive, at most log X and at least half of log X, and
x^(1/2) is at most H for H at least X^(7/18 + eps). These are the conditions
x sufficiently large and x^(1/2) at most y of Lemma 3.4 of page 11, and the
comparison of L^(-A) with (log X)^(-A).
Class MEDIUM. -/
theorem leaf_window_basic (A ε c x0 : ℝ) (hA : 0 ≤ A) (hε : 0 < ε) (hε6 : ε < 1 / 6)
    (hc2 : 2 ≤ c) (hc4 : c ≤ 4) :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X → X ^ (7 / 18 + ε) ≤ H →
      x0 ≤ windowY X ε / c ∧ 0 < Real.log (windowY X ε / c) ∧
      Real.log (windowY X ε / c) ≤ Real.log X ∧ Real.sqrt (windowY X ε / c) ≤ H ∧
      Real.log X ^ A ≤ (2 : ℝ) ^ A * Real.log (windowY X ε / c) ^ A := by
  have he2 : (2 : ℝ) ≤ Real.exp 24 := by
    have := Real.add_one_le_exp (24 : ℝ); linarith
  refine ⟨max (Real.exp 24) (16 * x0 ^ 2 + 1), he2.trans (le_max_left _ _),
    fun X H hX hH => ?_⟩
  have hXe : Real.exp 24 ≤ X := (le_max_left _ _).trans hX
  have hXx : 16 * x0 ^ 2 + 1 ≤ X := (le_max_right _ _).trans hX
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) (he2.trans hXe)
  have hX1 : 1 ≤ X := by linarith
  have hL24 : 24 ≤ Real.log X := by
    rw [← Real.log_exp 24]; exact Real.log_le_log (Real.exp_pos 24) hXe
  set L := Real.log X with hLdef
  set a : ℝ := 7 / 12 + ε / 2 with ha
  have hY : windowY X ε = X ^ a := rfl
  have hYpos : 0 < windowY X ε := by rw [hY]; exact Real.rpow_pos_of_pos hX0 a
  have hc0 : 0 < c := by linarith
  have hlogY : Real.log (windowY X ε) = a * L := by rw [hY, Real.log_rpow hX0]
  have hlogc : Real.log c < 2 := by
    have h4 : Real.log c ≤ Real.log 4 := Real.log_le_log hc0 hc4
    have : Real.log 4 < 2 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have h1 := Real.exp_one_gt_d9
      nlinarith
    linarith
  have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  set l := Real.log (windowY X ε / c) with hldef
  have hl : l = a * L - Real.log c := by
    rw [hldef, Real.log_div hYpos.ne' hc0.ne', hlogY]
  have hlpos : 0 < l := by rw [hl]; nlinarith
  have hlL : l ≤ L := by rw [hl]; nlinarith
  have hl2 : L ≤ 2 * l := by rw [hl]; nlinarith
  -- Y is at least sqrt X
  have hYsq : Real.sqrt X ≤ windowY X ε := by
    rw [Real.sqrt_eq_rpow, hY]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by rw [ha]; linarith)
  have hx0 : x0 ≤ windowY X ε / c := by
    have h1 : 4 * |x0| ≤ Real.sqrt X := by
      rw [show 4 * |x0| = Real.sqrt ((4 * |x0|) ^ 2) by
        rw [Real.sqrt_sq (by positivity)]]
      apply Real.sqrt_le_sqrt
      have : (4 * |x0|) ^ 2 = 16 * x0 ^ 2 := by rw [mul_pow, sq_abs]; norm_num
      linarith
    rw [le_div_iff₀ hc0]
    have : x0 * c ≤ |x0| * 4 := by
      calc x0 * c ≤ |x0| * c := mul_le_mul_of_nonneg_right (le_abs_self x0) hc0.le
        _ ≤ |x0| * 4 := mul_le_mul_of_nonneg_left hc4 (abs_nonneg x0)
    linarith
  have hsqH : Real.sqrt (windowY X ε / c) ≤ H := by
    refine le_trans ?_ hH
    have h1 : Real.sqrt (windowY X ε / c) ≤ Real.sqrt (windowY X ε) :=
      Real.sqrt_le_sqrt (div_le_self hYpos.le (by linarith))
    refine h1.trans ?_
    rw [Real.sqrt_eq_rpow, hY, ← Real.rpow_mul hX0.le]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by rw [ha]; linarith)
  refine ⟨hx0, hlpos, hlL, hsqH, ?_⟩
  rw [← Real.mul_rpow (by norm_num) hlpos.le]
  exact Real.rpow_le_rpow (by linarith) hl2 hA

/-- LEAF: P0088 page 15, the remark after display 52 that the choice of z0 in
display 34 is set by the hypothesis on M in Lemma 3.4: for B at least one and
large X, the sieve cutoff z0 = Y^(1/4) (log X)^(-2B) is at most
x^(1/4) L^(-2B) with x = Y / c, c between 2 and 4, and L = log x.
Class MEDIUM. -/
theorem leaf_window_cutoff (B ε c : ℝ) (hB : 1 ≤ B) (hε : 0 < ε) (hε6 : ε < 1 / 6)
    (hc2 : 2 ≤ c) (hc4 : c ≤ 4) :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤
        (windowY X ε / c) ^ (1 / 4 : ℝ) * (Real.log (windowY X ε / c) ^ B) ^ (-2 : ℤ) := by
  have he2 : (2 : ℝ) ≤ Real.exp 4 := by
    have := Real.add_one_le_exp (4 : ℝ); linarith
  refine ⟨Real.exp 4, he2, fun X hX => ?_⟩
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) (he2.trans hX)
  have hL4 : 4 ≤ Real.log X := by
    rw [← Real.log_exp 4]; exact Real.log_le_log (Real.exp_pos 4) hX
  set L := Real.log X with hLdef
  set a : ℝ := 7 / 12 + ε / 2 with ha
  have hY : windowY X ε = X ^ a := rfl
  have hYpos : 0 < windowY X ε := by rw [hY]; exact Real.rpow_pos_of_pos hX0 a
  have hc0 : 0 < c := by linarith
  have hlogY : Real.log (windowY X ε) = a * L := by rw [hY, Real.log_rpow hX0]
  have hlogc : Real.log c < 2 := by
    have h4 : Real.log c ≤ Real.log 4 := Real.log_le_log hc0 hc4
    have : Real.log 4 < 2 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.add_one_le_exp (2 : ℝ)
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have h1 := Real.exp_one_gt_d9
      nlinarith
    linarith
  have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  set l := Real.log (windowY X ε / c) with hldef
  have hl : l = a * L - Real.log c := by
    rw [hldef, Real.log_div hYpos.ne' hc0.ne', hlogY]
  have hlpos : 0 < l := by rw [hl]; nlinarith
  have hlL : l ≤ (2 / 3) * L := by rw [hl]; nlinarith
  have hB0 : 0 ≤ B := by linarith
  have hLpos : 0 < L := by linarith
  have hlB : l ^ B ≤ (2 / 3) * L ^ B := by
    have h1 : l ^ B ≤ ((2 / 3) * L) ^ B := Real.rpow_le_rpow hlpos.le hlL hB0
    rw [Real.mul_rpow (by norm_num) hLpos.le] at h1
    have h2 : ((2 : ℝ) / 3) ^ B ≤ ((2 : ℝ) / 3) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hB
    rw [Real.rpow_one] at h2
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hLpos.le B))
  have hlBpos : 0 < l ^ B := Real.rpow_pos_of_pos hlpos B
  have hLBpos : 0 < L ^ B := Real.rpow_pos_of_pos hLpos B
  have hc4' : c ^ (1 / 4 : ℝ) ≤ 2 := by
    have h := Real.rpow_le_rpow hc0.le (show c ≤ 16 by linarith) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have h16 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  have hcpos : 0 < c ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hYq : 0 < windowY X ε ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hYpos _
  rw [Real.div_rpow hYpos.le hc0.le, zpow_neg, zpow_neg, zpow_two, zpow_two]
  rw [div_mul_eq_mul_div, le_div_iff₀ hcpos]
  have hsq : l ^ B * l ^ B ≤ (4 / 9) * (L ^ B * L ^ B) := by nlinarith
  have hinv : (4 / 9 : ℝ)⁻¹ * (L ^ B * L ^ B)⁻¹ ≤ (l ^ B * l ^ B)⁻¹ := by
    rw [← mul_inv]
    exact inv_anti₀ (by positivity) hsq
  calc windowY X ε ^ (1 / 4 : ℝ) * (L ^ B * L ^ B)⁻¹ * c ^ (1 / 4 : ℝ)
      ≤ windowY X ε ^ (1 / 4 : ℝ) * (L ^ B * L ^ B)⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left hc4' (by positivity)
    _ ≤ windowY X ε ^ (1 / 4 : ℝ) * ((4 / 9 : ℝ)⁻¹ * (L ^ B * L ^ B)⁻¹) := by
        have : (0 : ℝ) ≤ windowY X ε ^ (1 / 4 : ℝ) * (L ^ B * L ^ B)⁻¹ := by positivity
        nlinarith
    _ ≤ windowY X ε ^ (1 / 4 : ℝ) * (l ^ B * l ^ B)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hYq.le

/-- LEAF: P0088 page 15, the note after display 52 that the condition on
theta2 ensures z1 at most H Y^(-1/2) L^(-2B): for eps below 1/6, large X and
H at least X^(7/18 + eps), the rough cutoff z1 = Y^(1/6 + eps/2) is at least 2
and at most H x^(-1/2) L^(-2B) with x = Y / c, c between 2 and 4, L = log x.
Class MEDIUM. -/
theorem leaf_window_rough (B ε c : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hε6 : ε < 1 / 6)
    (hc2 : 2 ≤ c) (hc4 : c ≤ 4) :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X → X ^ (7 / 18 + ε) ≤ H →
      2 ≤ windowY X ε ^ (1 / 6 + ε / 2) ∧
      windowY X ε ^ (1 / 6 + ε / 2) ≤
        H / Real.sqrt (windowY X ε / c) * (Real.log (windowY X ε / c) ^ B) ^ (-2 : ℤ) := by
  have hev1 : ∀ᶠ X : ℝ in Filter.atTop, ‖Real.log X ^ (2 * B)‖ ≤ 1 * ‖X ^ (ε / 3)‖ :=
    (isLittleO_log_rpow_rpow_atTop (2 * B) (by linarith : 0 < ε / 3)).bound one_pos
  have hev2 : ∀ᶠ X : ℝ in Filter.atTop, 2 ≤ X ^ (7 / 72 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 72)).eventually_ge_atTop 2
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.1
    (hev1.and (hev2.and (Filter.eventually_ge_atTop (Real.exp 4))))
  have he2 : (2 : ℝ) ≤ Real.exp 4 := by
    have := Real.add_one_le_exp (4 : ℝ); linarith
  refine ⟨max X1 (Real.exp 4), he2.trans (le_max_right _ _), fun X H hX hH => ?_⟩
  obtain ⟨k1, k2, hXe⟩ := hX1 X ((le_max_left _ _).trans hX)
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) (he2.trans hXe)
  have hX1' : 1 ≤ X := by linarith
  have hL4 : 4 ≤ Real.log X := by
    rw [← Real.log_exp 4]; exact Real.log_le_log (Real.exp_pos 4) hXe
  set L := Real.log X with hLdef
  set a : ℝ := 7 / 12 + ε / 2 with ha
  have hY : windowY X ε = X ^ a := rfl
  have hYpos : 0 < windowY X ε := by rw [hY]; exact Real.rpow_pos_of_pos hX0 a
  have hc0 : 0 < c := by linarith
  have hlogY : Real.log (windowY X ε) = a * L := by rw [hY, Real.log_rpow hX0]
  have hlogc : Real.log c < 2 := by
    have h4 : Real.log c ≤ Real.log 4 := Real.log_le_log hc0 hc4
    have : Real.log 4 < 2 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have h1 := Real.exp_one_gt_d9
      nlinarith
    linarith
  have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  set l := Real.log (windowY X ε / c) with hldef
  have hl : l = a * L - Real.log c := by
    rw [hldef, Real.log_div hYpos.ne' hc0.ne', hlogY]
  have hlpos : 0 < l := by rw [hl]; nlinarith
  have hlL : l ≤ L := by rw [hl]; nlinarith
  have hLpos : 0 < L := by linarith
  set b : ℝ := 1 / 6 + ε / 2 with hb
  have hYb : windowY X ε ^ b = X ^ (a * b) := by rw [hY, ← Real.rpow_mul hX0.le]
  constructor
  · rw [hYb]
    refine k2.trans (Real.rpow_le_rpow_of_exponent_le hX1' ?_)
    rw [ha, hb]; nlinarith
  · -- the log factor
    have hlog2 : (l ^ B) ^ 2 ≤ X ^ (ε / 3) := by
      have e1 : (l ^ B) ^ 2 = l ^ (2 * B) := by
        rw [mul_comm, Real.rpow_mul hlpos.le, Real.rpow_two]
      have e2 : l ^ (2 * B) ≤ L ^ (2 * B) := Real.rpow_le_rpow hlpos.le hlL (by linarith)
      have e3 : L ^ (2 * B) ≤ X ^ (ε / 3) := by
        have h := k1
        rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hLpos.le _),
          Real.norm_of_nonneg (Real.rpow_nonneg hX0.le _)] at h
        exact h
      rw [e1]; exact e2.trans e3
    have hsq : Real.sqrt (windowY X ε / c) ≤ X ^ (a / 2) := by
      have h1 : Real.sqrt (windowY X ε / c) ≤ Real.sqrt (windowY X ε) :=
        Real.sqrt_le_sqrt (div_le_self hYpos.le (by linarith))
      refine h1.trans (le_of_eq ?_)
      rw [Real.sqrt_eq_rpow, hY, ← Real.rpow_mul hX0.le]; ring_nf
    have hsqpos : 0 < Real.sqrt (windowY X ε / c) := Real.sqrt_pos.2 (div_pos hYpos hc0)
    have hlBpos : 0 < (l ^ B) ^ 2 := by positivity
    have hexp : X ^ (a * b) * X ^ (a / 2) * X ^ (ε / 3) ≤ H := by
      rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
      refine le_trans (Real.rpow_le_rpow_of_exponent_le hX1' ?_) hH
      rw [ha, hb]; nlinarith
    have hprod : windowY X ε ^ b * Real.sqrt (windowY X ε / c) * (l ^ B) ^ 2 ≤ H := by
      rw [hYb]
      refine le_trans ?_ hexp
      have p1 : 0 ≤ X ^ (a * b) := Real.rpow_nonneg hX0.le _
      have p2 : 0 ≤ X ^ (a / 2) := Real.rpow_nonneg hX0.le _
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsq p1) hlog2 hlBpos.le (by positivity)
    rw [zpow_neg, zpow_two, ← pow_two, div_mul_eq_mul_div, le_div_iff₀ hsqpos,
      ← div_eq_mul_inv, le_div_iff₀ hlBpos]
    exact hprod

/-- P0088 page 10 display 41 from the hypothesis on alpha of the parent, with
L = log X replaced by any smaller positive l: l^B at most q at most H l^(-B)
and |alpha - a / q| below q^(-2). -/
theorem display41_transfer {l L B H α : ℝ} {q : ℕ} {a : ℤ} (hl : 0 < l) (hlL : l ≤ L)
    (hB : 0 ≤ B) (hqP : L ^ B < (q : ℝ)) (hqQ : (q : ℝ) ≤ H / L ^ B)
    (hclose : |(q : ℝ) * α - a| < (H / L ^ B)⁻¹) :
    l ^ B ≤ (q : ℝ) ∧ (q : ℝ) ≤ H / l ^ B ∧
      |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 := by
  have hlB : l ^ B ≤ L ^ B := Real.rpow_le_rpow hl.le hlL hB
  have hlpos : 0 < l ^ B := Real.rpow_pos_of_pos hl B
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le hlpos (hlB.trans hqP.le)
  have hqn : 0 < q := by exact_mod_cast hq0
  have hLpos : 0 < L ^ B := lt_of_lt_of_le hlpos hlB
  have hHL : 0 < H / L ^ B := lt_of_lt_of_le hq0 hqQ
  have hH : 0 ≤ H := by
    by_contra hneg
    push Not at hneg
    linarith [div_neg_of_neg_of_pos hneg hLpos]
  refine ⟨hlB.trans hqP.le, hqQ.trans (div_le_div_of_nonneg_left hH hlpos hlB), ?_⟩
  exact display41_of_minor hqn hqQ hclose

/-- The core of `leaf_interior_left_half`, eps below 1/6 and H below
Y (log X)^(A/2), from the leaves: the Lemma 3.4 instance with x = Y / 4 for
H at most x, and the band leaf above x. -/
theorem core_interior_left_half_from_leaves (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        H < windowY X ε * Real.log X ^ (A / 2) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := leaf_left_half_lemma34_instance A hA
  obtain ⟨B2, hB2, h2⟩ := leaf_left_half_band A hA
  refine ⟨max (max B1 B2) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun B hB ε hε hε6 => ?_⟩
  have hBB1 : B1 ≤ B := (le_max_left _ _).trans ((le_max_left _ _).trans hB)
  have hBB2 : B2 ≤ B := (le_max_right _ _).trans ((le_max_left _ _).trans hB)
  have hB1' : 1 ≤ B := (le_max_right _ _).trans hB
  obtain ⟨C1, x0, hC1, hx0, k1⟩ := h1 B hBB1
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B hBB2 ε hε hε6
  obtain ⟨X3, hX3, k3⟩ := leaf_window_basic A ε 4 x0 hA.le hε hε6 (by norm_num) (by norm_num)
  obtain ⟨X4, hX4, k4⟩ := leaf_window_cutoff B ε 4 hB1' hε hε6 (by norm_num) (by norm_num)
  obtain ⟨X5, hX5, k5⟩ := leaf_window_rough B ε 4 (by linarith) hε hε6 (by norm_num)
    (by norm_num)
  have hCpos : 0 < max ((2 : ℝ) ^ A * C1) C2 := lt_of_lt_of_le hC2 (le_max_right _ _)
  refine ⟨max ((2 : ℝ) ^ A * C1) C2, max (max X2 X3) (max X4 X5), hCpos,
    hX2.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro X H hX hHl hHu hHband α q a hcop hqP hqQ hclose M hM htop hlow
  have hX2' : X2 ≤ X := ((le_max_left _ _).trans (le_max_left _ _)).trans hX
  have hX3' : X3 ≤ X := ((le_max_right _ _).trans (le_max_left _ _)).trans hX
  have hX4' : X4 ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hX5' : X5 ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hX1 : 1 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX1
  have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hL A
  have hq : (0 : ℝ) ≤ H ^ 2 / Real.log X ^ A := div_nonneg (sq_nonneg _) hLA.le
  have hkey : ∀ c : ℝ, c * H ^ 2 / Real.log X ^ A = c * (H ^ 2 / Real.log X ^ A) :=
    fun c => by ring
  by_cases hHx : H ≤ windowY X ε / 4
  · obtain ⟨hx0Y, hlpos, hlL, hsq, hpowA⟩ := k3 X H hX3' hHl
    have hz0 := k4 X hX4'
    obtain ⟨hw2, hwH⟩ := k5 X H hX5' hHl
    obtain ⟨hq1, hq2, hq3⟩ := display41_transfer hlpos hlL (by linarith : (0 : ℝ) ≤ B)
      hqP hqQ hclose
    have e := k1 (windowY X ε) (windowY X ε ^ (1 / 6 + ε / 2))
      (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ))
      (windowY X ε ^ (1 / 6 + ε / 2)) H α q a M hx0Y hsq hHx hcop hq1 hq2 hq3 hM
      (htop.le.trans hz0) hw2 hwH
    have hlA : 0 < Real.log (windowY X ε / 4) ^ A := Real.rpow_pos_of_pos hlpos A
    have hstep : C1 * H ^ 2 / Real.log (windowY X ε / 4) ^ A ≤
        ((2 : ℝ) ^ A * C1) * H ^ 2 / Real.log X ^ A := by
      rw [div_le_div_iff₀ hlA hLA]
      have hm := mul_le_mul_of_nonneg_left hpowA (mul_nonneg hC1.le (sq_nonneg H))
      calc C1 * H ^ 2 * Real.log X ^ A
          ≤ C1 * H ^ 2 * ((2 : ℝ) ^ A * Real.log (windowY X ε / 4) ^ A) := hm
        _ = (2 : ℝ) ^ A * C1 * H ^ 2 * Real.log (windowY X ε / 4) ^ A := by ring
    rw [hkey] at hstep ⊢
    exact e.trans (hstep.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq))
  · push Not at hHx
    have e := k2 X H hX2' hHl hHu hHx hHband α q a hcop hqP hqQ hclose M hM htop hlow
    rw [hkey] at e ⊢
    exact e.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hq)

/-- `leaf_interior_left_half` of `SPLIT_lemma34_second_sum_dyadic`, with
exactly its statement, from the leaves of this file through the proved
reduction `leaf_interior_left_half_of_core`. -/
theorem leaf_interior_left_half_from_leaves (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A :=
  leaf_interior_left_half_of_core A (core_interior_left_half_from_leaves A hA)

/-- The core of `leaf_interior_right_half`, eps below 1/6 and H below
Y (log X)^(A/2), from the leaves: the Lemma 3.4 instance with x = Y / 2 for
H at most x, and the band leaf above x. -/
theorem core_interior_right_half_from_leaves (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        H < windowY X ε * Real.log X ^ (A / 2) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in (windowY X ε / 2)..(windowY X ε),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := leaf_right_half_lemma34_instance A hA
  obtain ⟨B2, hB2, h2⟩ := leaf_right_half_band A hA
  refine ⟨max (max B1 B2) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun B hB ε hε hε6 => ?_⟩
  have hBB1 : B1 ≤ B := (le_max_left _ _).trans ((le_max_left _ _).trans hB)
  have hBB2 : B2 ≤ B := (le_max_right _ _).trans ((le_max_left _ _).trans hB)
  have hB1' : 1 ≤ B := (le_max_right _ _).trans hB
  obtain ⟨C1, x0, hC1, hx0, k1⟩ := h1 B hBB1
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B hBB2 ε hε hε6
  obtain ⟨X3, hX3, k3⟩ := leaf_window_basic A ε 2 x0 hA.le hε hε6 (by norm_num) (by norm_num)
  obtain ⟨X4, hX4, k4⟩ := leaf_window_cutoff B ε 2 hB1' hε hε6 (by norm_num) (by norm_num)
  obtain ⟨X5, hX5, k5⟩ := leaf_window_rough B ε 2 (by linarith) hε hε6 (by norm_num)
    (by norm_num)
  have hCpos : 0 < max ((2 : ℝ) ^ A * C1) C2 := lt_of_lt_of_le hC2 (le_max_right _ _)
  refine ⟨max ((2 : ℝ) ^ A * C1) C2, max (max X2 X3) (max X4 X5), hCpos,
    hX2.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro X H hX hHl hHu hHband α q a hcop hqP hqQ hclose M hM htop hlow
  have hX2' : X2 ≤ X := ((le_max_left _ _).trans (le_max_left _ _)).trans hX
  have hX3' : X3 ≤ X := ((le_max_right _ _).trans (le_max_left _ _)).trans hX
  have hX4' : X4 ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hX5' : X5 ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hX1 : 1 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX1
  have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hL A
  have hq : (0 : ℝ) ≤ H ^ 2 / Real.log X ^ A := div_nonneg (sq_nonneg _) hLA.le
  have hkey : ∀ c : ℝ, c * H ^ 2 / Real.log X ^ A = c * (H ^ 2 / Real.log X ^ A) :=
    fun c => by ring
  by_cases hHx : H ≤ windowY X ε / 2
  · obtain ⟨hx0Y, hlpos, hlL, hsq, hpowA⟩ := k3 X H hX3' hHl
    have hz0 := k4 X hX4'
    obtain ⟨hw2, hwH⟩ := k5 X H hX5' hHl
    obtain ⟨hq1, hq2, hq3⟩ := display41_transfer hlpos hlL (by linarith : (0 : ℝ) ≤ B)
      hqP hqQ hclose
    have e := k1 (windowY X ε) (windowY X ε ^ (1 / 6 + ε / 2))
      (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ))
      (windowY X ε ^ (1 / 6 + ε / 2)) H α q a M hx0Y hsq hHx hcop hq1 hq2 hq3 hM
      (htop.le.trans hz0) hw2 hwH
    have hlA : 0 < Real.log (windowY X ε / 2) ^ A := Real.rpow_pos_of_pos hlpos A
    have hstep : C1 * H ^ 2 / Real.log (windowY X ε / 2) ^ A ≤
        ((2 : ℝ) ^ A * C1) * H ^ 2 / Real.log X ^ A := by
      rw [div_le_div_iff₀ hlA hLA]
      have hm := mul_le_mul_of_nonneg_left hpowA (mul_nonneg hC1.le (sq_nonneg H))
      calc C1 * H ^ 2 * Real.log X ^ A
          ≤ C1 * H ^ 2 * ((2 : ℝ) ^ A * Real.log (windowY X ε / 2) ^ A) := hm
        _ = (2 : ℝ) ^ A * C1 * H ^ 2 * Real.log (windowY X ε / 2) ^ A := by ring
    rw [hkey] at hstep ⊢
    exact e.trans (hstep.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq))
  · push Not at hHx
    have e := k2 X H hX2' hHl hHu hHx hHband α q a hcop hqP hqQ hclose M hM htop hlow
    rw [hkey] at e ⊢
    exact e.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hq)

/-- `leaf_interior_right_half` of `SPLIT_lemma34_second_sum_dyadic`, with
exactly its statement, from the leaves of this file through the proved
reduction `leaf_interior_right_half_of_core`. -/
theorem leaf_interior_right_half_from_leaves (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in (windowY X ε / 2)..(windowY X ε),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A :=
  leaf_interior_right_half_of_core A (core_interior_right_half_from_leaves A hA)

#print axioms leaf_interior_left_half_from_leaves
#print axioms leaf_interior_right_half_from_leaves

end LeanLab.KumchevLiu2007.Eq33RouteD
