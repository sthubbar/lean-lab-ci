/- AI-written Lean code by OpenAI Codex, task362, 2026-11-05. Binary Goldbach is open. -/
import LeanLab.Tchudakov1938.Decomp362a
import LeanLab.Tchudakov1938.Decomp362d
import LeanLab.Tchudakov1938.Decomp362e

namespace LeanLab.Tchudakov1938.Decomp362b
open Finset Filter
open LeanLab.Tchudakov1938.Tail113

/-- P0064, page 29, inequality 5. The small-divisor sum before its absolute constant. -/
noncomputable def smallDivisorSum (m : ℕ) (xi : ℝ) : ℝ :=
  ∑ d ∈ m.divisors.filter (fun d : ℕ => (d : ℝ) ≤ xi), (1 / (d : ℝ)) *
    ∑' k : ℕ, (Real.log ((d : ℝ) * (k + (⌊xi / d⌋₊ + 1) : ℕ)))^2 /
      ((k + (⌊xi / d⌋₊ + 1) : ℕ) : ℝ)^2

/-- P0064, page 29, inequality 5. The large-divisor sum before its absolute constant. -/
noncomputable def largeDivisorSum (m : ℕ) (xi : ℝ) : ℝ :=
  ∑ d ∈ m.divisors.filter (fun d : ℕ => xi < (d : ℝ)),
    ((Real.log d)^2 + Real.log d + 1) / (d : ℝ)

/-- LEAF. P0064, page 29, inequality 5. The gcd regrouping and the full convergent inner sums
bound the coefficient tail by the two divisor ranges. The cutoff is explicit and large. -/
theorem tail_le_divisor_split :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ xi : ℝ, Real.exp 2 ≤ xi →
      ‖tailSeries m ⌊xi⌋₊‖ ≤ C * (smallDivisorSum m xi + largeDivisorSum m xi) := by
  exact Decomp362e.divisor_split

/-- LEAF. P0064, page 29, inequality 6, the inner-series estimate after combining logarithms.
The positive lower bound on xi keeps the endpoint logarithms from vanishing. -/
theorem small_divisor_term_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ xi : ℝ, Real.exp 2 ≤ xi → ∀ d : ℕ, 0 < d → (d : ℝ) ≤ xi →
      (1 / (d : ℝ)) *
        (∑' k : ℕ, (Real.log ((d : ℝ) * (k + (⌊xi / d⌋₊ + 1) : ℕ)))^2 /
          ((k + (⌊xi / d⌋₊ + 1) : ℕ) : ℝ)^2) ≤ C * (Real.log xi)^2 / xi := by
  exact Decomp362d.inner_bound

/-- LEAF. P0064, page 29, inequality 6, final divisor-count bound.
The small-divisor contribution is bounded by the divisor count times log squared xi over xi. -/
theorem small_divisor_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ xi : ℝ, Real.exp 2 ≤ xi →
      smallDivisorSum m xi ≤ C * (m.divisors.card : ℝ) * (Real.log xi)^2 / xi := by
  obtain ⟨C, hC, ht⟩ := small_divisor_term_bound
  refine ⟨C, hC, fun m _ xi hxi => ?_⟩
  have hx0 : 0 < xi := (Real.exp_pos 2).trans_le hxi
  unfold smallDivisorSum
  calc _ ≤ ∑ _d ∈ m.divisors.filter (fun d : ℕ => (d : ℝ) ≤ xi), C * (Real.log xi)^2 / xi := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hdm, hdx⟩ := Finset.mem_filter.mp hd
        exact ht xi hxi d (Nat.pos_of_mem_divisors hdm) hdx
    _ = ((m.divisors.filter (fun d : ℕ => (d : ℝ) ≤ xi)).card : ℝ) *
        (C * (Real.log xi)^2 / xi) := by simp
    _ ≤ (m.divisors.card : ℝ) * (C * (Real.log xi)^2 / xi) := by
      apply mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Finset.card_filter_le _ _)) (by positivity)
    _ = _ := by ring

/-- LEAF. P0064, page 29, inequality 7. A term beyond xi is at most three log squared xi over xi. -/
theorem large_divisor_term_bound (x y : ℝ) (hx : Real.exp 2 ≤ x) (hxy : x ≤ y) :
    ((Real.log y)^2 + Real.log y + 1) / y ≤ 3 * (Real.log x)^2 / x := by
  have hx0 : 0 < x := (Real.exp_pos 2).trans_le hx
  have hy0 : 0 < y := hx0.trans_le hxy
  have hlx : 2 ≤ Real.log x := by
    rw [← Real.log_exp 2]
    exact Real.log_le_log (Real.exp_pos 2) hx
  have hly : 0 ≤ Real.log y := (by linarith : 0 ≤ Real.log x).trans
    (Real.log_le_log hx0 hxy)
  have hsq : (Real.log y)^2 / y ≤ (Real.log x)^2 / x := by
    have h := Real.log_div_sqrt_antitoneOn hx (hx.trans hxy) hxy
    have hh := pow_le_pow_left₀ (div_nonneg hly (Real.sqrt_nonneg y)) h 2
    simpa only [div_pow, Real.sq_sqrt hx0.le, Real.sq_sqrt hy0.le] using hh
  have hlin : Real.log y / y ≤ Real.log x / x := by
    have he : Real.exp 1 ≤ x := (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hx
    exact Real.log_div_self_antitoneOn he (he.trans hxy) hxy
  have hinv : 1 / y ≤ 1 / x := one_div_le_one_div_of_le hx0 hxy
  have h1 : Real.log x / x ≤ (Real.log x)^2 / x := by
    apply div_le_div_of_nonneg_right _ hx0.le
    nlinarith
  have h2 : 1 / x ≤ (Real.log x)^2 / x := by
    apply div_le_div_of_nonneg_right _ hx0.le
    nlinarith
  rw [add_div, add_div]
  calc _ ≤ (Real.log x)^2 / x + (Real.log x)^2 / x + (Real.log x)^2 / x :=
      add_le_add (add_le_add hsq (hlin.trans h1)) (hinv.trans h2)
    _ = _ := by ring

/-- LEAF. P0064, page 29, inequality 7, first divisor-count bound.
The large-divisor contribution has the same scale. -/
theorem large_divisor_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ xi : ℝ, Real.exp 2 ≤ xi →
      largeDivisorSum m xi ≤ C * (m.divisors.card : ℝ) * (Real.log xi)^2 / xi := by
  refine ⟨3, by norm_num, fun m _ xi hxi => ?_⟩
  have hx0 : 0 < xi := (Real.exp_pos 2).trans_le hxi
  unfold largeDivisorSum
  calc (∑ d ∈ m.divisors.filter (fun d : ℕ => xi < (d : ℝ)),
        ((Real.log d)^2 + Real.log d + 1) / (d : ℝ))
      ≤ ∑ _d ∈ m.divisors.filter (fun d : ℕ => xi < (d : ℝ)), 3 * (Real.log xi)^2 / xi := by
        apply Finset.sum_le_sum
        intro d hd
        exact large_divisor_term_bound xi d hxi (Finset.mem_filter.mp hd).2.le
    _ = ((m.divisors.filter (fun d : ℕ => xi < (d : ℝ))).card : ℝ) *
        (3 * (Real.log xi)^2 / xi) := by simp
    _ ≤ (m.divisors.card : ℝ) * (3 * (Real.log xi)^2 / xi) := by
      apply mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Finset.card_filter_le _ _)) (by positivity)
    _ = _ := by ring

/-- P0064, page 29, inequalities 5 to 7. Assembly from the proved divisor leaves. -/
theorem divisor_tail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ xi : ℝ, Real.exp 2 ≤ xi →
      ‖tailSeries m ⌊xi⌋₊‖ ≤ C * (m.divisors.card : ℝ) * (Real.log xi)^2 / xi := by
  obtain ⟨C, hC, ht⟩ := tail_le_divisor_split
  obtain ⟨A, hA, hs⟩ := small_divisor_bound
  obtain ⟨B, hB, hl⟩ := large_divisor_bound
  refine ⟨C * (A + B), by positivity, fun m hm xi hxi => ?_⟩
  calc ‖tailSeries m ⌊xi⌋₊‖ ≤ C * (smallDivisorSum m xi + largeDivisorSum m xi) := ht m hm xi hxi
    _ ≤ C * (A * (m.divisors.card : ℝ) * (Real.log xi)^2 / xi +
        B * (m.divisors.card : ℝ) * (Real.log xi)^2 / xi) :=
      mul_le_mul_of_nonneg_left (add_le_add (hs m hm xi hxi) (hl m hm xi hxi)) hC.le
    _ = _ := by ring

/-- P0064, page 29, inequality 8. The divisor leaves imply the cited uniform tail input. -/
theorem uniform_tail : uniformTailStatement := by
  obtain ⟨C, hC, ht⟩ := divisor_tail_bound
  intro M hM
  have hcut : ∀ᶠ x : ℝ in atTop, Real.exp 2 ≤ Real.log x ^ (M + 6) :=
    ((tendsto_rpow_atTop (by linarith : 0 < M + 6)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop _
  have hsmall : ∀ᶠ x : ℝ in atTop,
      (C * (M + 6)^2) * ((Real.log (Real.log x))^2 / Real.log x) < 1 / 4 := by
    have h := Decomp362a.loglog_scale_tendsto.const_mul (C * (M + 6)^2)
    have h0 : Tendsto (fun x : ℝ => (C * (M + 6)^2) *
        ((Real.log (Real.log x))^2 / Real.log x)) atTop (nhds 0) := by simpa using h
    exact h0.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    (hcut.and (hsmall.and (eventually_gt_atTop (1 : ℝ))))
  refine ⟨max 3 X, le_max_left _ _, fun x hx m hm _ hdiv => ?_⟩
  obtain ⟨hxi, hsm, hx1⟩ := hX x ((le_max_right _ _).trans hx)
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hpow : 0 < Real.log x ^ (M + 6) := Real.rpow_pos_of_pos hlog _
  have heq : Real.log (Real.log x ^ (M + 6)) = (M + 6) * Real.log (Real.log x) :=
    Real.log_rpow hlog _
  calc ‖tailSeries m ⌊Real.log x ^ (M + 6)⌋₊‖
      ≤ C * (m.divisors.card : ℝ) * (Real.log (Real.log x ^ (M + 6)))^2 /
        (Real.log x ^ (M + 6)) := ht m hm _ hxi
    _ ≤ C * (Real.log x ^ (M + 6) / Real.log x) *
        (Real.log (Real.log x ^ (M + 6)))^2 / (Real.log x ^ (M + 6)) := by
      gcongr
    _ = (C * (M + 6)^2) * ((Real.log (Real.log x))^2 / Real.log x) := by
      rw [heq]
      field_simp [ne_of_gt hpow, ne_of_gt hlog]
    _ ≤ 1 / 4 := hsm.le

/-- P0064, pages 29 and 30, inequalities 3, 4 and 8.
Exact statement of DecompJ578.partial_sum_bound_lower, using the proved divisor leaves. -/
theorem partial_sum_bound_lower (M : ℝ) (hM : 0 < M) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
    ∀ m : ℕ, 0 < m → Even m →
      (m.divisors.card : ℝ) ≤ Real.log x ^ (M + 6) / Real.log x →
      c < ‖partialSeries m ⌊Real.log x ^ (M + 6)⌋₊‖ := by
  exact lemma4_truncation_of_uniformTail uniform_tail M hM

end LeanLab.Tchudakov1938.Decomp362b
