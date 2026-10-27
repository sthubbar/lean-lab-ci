/- AI-written Lean code by OpenAI Codex, task113, 2026-10-26. Binary Goldbach is open. -/
import LeanLab.Tchudakov1938.Positive113
namespace LeanLab.Tchudakov1938.Tail113
open LeanLab.Tchudakov1938.Decomp113 LeanLab.Tchudakov1938.Euler113 LeanLab.Tchudakov1938.Positive113
open Finset Filter
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- P0064, page 29, inequality 4. The truncated sum includes the zero term of the zero extension. -/
noncomputable def partialSeries (m Q : ℕ) : ℂ := ∑ q ∈ Finset.range (Q + 1), coefficientNat m q
/-- P0064, page 29, inequality 4. The tail starts at Q plus one. -/
noncomputable def tailSeries (m Q : ℕ) : ℂ := ∑' k : ℕ, coefficientNat m (k + (Q + 1))

/-- P0064, page 29, inequality 4. The partial sum and tail add to the full series. -/
theorem partial_add_tail (m : ℕ) (hm : 0 < m) (Q : ℕ) :
    partialSeries m Q + tailSeries m Q = ∑' q : ℕ+, coefficient m q := by
  rw [tsum_positive_eq_nat m hm]
  exact ((summable_norm_iff).mp (summable_norm_coefficientNat m hm)).sum_add_tsum_nat_add (Q + 1)

/-- CONDITIONAL ON the tail bound from paper inequality 8. P0064, page 29, inequality 4. A tail norm at most one quarter gives a partial sum norm at least one quarter. -/
theorem partial_lower_of_tail (m : ℕ) (hm : 0 < m) (heven : Even m) (Q : ℕ)
    (htail : ‖tailSeries m Q‖ ≤ (1 / 4 : ℝ)) :
    (1 / 4 : ℝ) ≤ ‖partialSeries m Q‖ := by
  have htotal := singular_series_lower m hm heven
  have hnorm := norm_add_le (partialSeries m Q) (tailSeries m Q)
  have H : partialSeries m Q + tailSeries m Q = ∑' q : ℕ+, coefficient m q := by
    rw [tsum_positive_eq_nat m hm]
    exact ((summable_norm_iff).mp (summable_norm_coefficientNat m hm)).sum_add_tsum_nat_add (Q + 1)
  rw [H] at hnorm
  have hre := Complex.re_le_norm (∑' q : ℕ+, coefficient m q)
  linarith

/-- P0064, page 29, the Euler product is real. The complex encoding has zero imaginary part. -/
theorem singular_series_im_zero (m : ℕ) (hm : 0 < m) :
    (∑' q : ℕ+, coefficient m q).im = 0 := by
  rw [tsum_positive_eq_nat m hm]
  have H : Tendsto (fun s : Finset Nat.Primes => ∏ p ∈ s, (1 + coefficientNat m p.val))
      atTop (nhds (∑' q : ℕ, coefficientNat m q)) := hasProd_local m hm
  have hi := (Complex.continuous_im.tendsto (∑' q : ℕ, coefficientNat m q)).comp H
  have hz : (Complex.im ∘ fun s : Finset Nat.Primes => ∏ p ∈ s, (1 + coefficientNat m p.val)) =
      fun _ => (0 : ℝ) := by
    funext s
    simp only [Function.comp_apply]
    simp_rw [local_eq_complex]
    rw [← Complex.ofReal_prod, Complex.ofReal_im]
  rw [hz] at hi
  exact tendsto_nhds_unique hi tendsto_const_nhds

/-- P0064, page 29, absolute convergence gives convergence of partial sums for fixed positive m. -/
theorem partial_tendsto (m : ℕ) (hm : 0 < m) : Tendsto (partialSeries m) atTop
    (nhds (∑' q : ℕ+, coefficient m q)) := by
  rw [tsum_positive_eq_nat m hm]
  exact ((summable_norm_iff).mp (summable_norm_coefficientNat m hm)).tendsto_sum_tsum_nat.comp
    (tendsto_add_atTop_nat 1)

/-- P0064, page 29, absolute convergence makes the tail tend to zero for each fixed positive m. -/
theorem tail_tendsto (m : ℕ) (hm : 0 < m) : Tendsto (tailSeries m) atTop (nhds 0) := by
  have hp : Tendsto (partialSeries m) atTop (nhds (∑' q : ℕ+, coefficient m q)) := by
    rw [tsum_positive_eq_nat m hm]
    exact ((summable_norm_iff).mp (summable_norm_coefficientNat m hm)).tendsto_sum_tsum_nat.comp
      (tendsto_add_atTop_nat 1)
  have he (Q : ℕ) : (∑' q : ℕ+, coefficient m q) - partialSeries m Q = tailSeries m Q := by
    have H := partial_add_tail m hm Q
    linear_combination -H
  simpa only [sub_self, Function.comp_apply, he] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∑' q : ℕ+, coefficient m q) atTop
      (nhds (∑' q : ℕ+, coefficient m q))).sub hp

/-- P0064, page 29, a fixed-index consequence of absolute convergence. The threshold depends on m. -/
theorem tail_eventually_small (m : ℕ) (hm : 0 < m) :
    ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q → ‖tailSeries m Q‖ ≤ (1 / 4 : ℝ) := by
  have hv := (tail_tendsto m hm).norm.eventually
    (eventually_lt_nhds (by norm_num : ‖(0 : ℂ)‖ < (1 / 4 : ℝ)))
  obtain ⟨Q₀, hQ⟩ := eventually_atTop.mp hv
  exact ⟨Q₀, fun Q h => (hQ Q h).le⟩

/-- P0064, pages 29 and 30, a fixed-index consequence of positivity and convergence. The threshold depends on m. -/
theorem partial_eventually_lower (m : ℕ) (hm : 0 < m) (heven : Even m) :
    ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q → (1 / 4 : ℝ) ≤ ‖partialSeries m Q‖ := by
  obtain ⟨Q₀, hQ⟩ := tail_eventually_small m hm
  exact ⟨Q₀, fun Q h => partial_lower_of_tail m hm heven Q (hQ Q h)⟩

/-- P0064, page 29, audit of the crude comparison from inequality 2. Replacing the gcd by a growing index does not give a uniform tail estimate; x divided by any fixed logarithmic power diverges. -/
theorem crude_scale_diverges (A : ℝ) : Tendsto (fun x : ℝ => x / Real.log x ^ A) atTop atTop := by
  have h := (isLittleO_log_rpow_rpow_atTop A (s := 1) (by norm_num)).tendsto_div_nhds_zero
  simp only [Real.rpow_one] at h
  have hp : ∀ᶠ x : ℝ in atTop, 0 < Real.log x ^ A / x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.rpow_pos_of_pos (Real.log_pos hx) A) (by linarith)
  have ht : Tendsto (fun x : ℝ => Real.log x ^ A / x) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨h, hp⟩
  simpa only [Function.comp_def, inv_div] using tendsto_inv_nhdsGT_zero.comp ht

/-- CITED. P0064, page 29, inequality 8 after the choice of c0 on page 27.
This uniform tail estimate remains an unproved input. -/
def uniformTailStatement : Prop :=
  ∀ M : ℝ, 0 < M → ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
    ∀ m : ℕ, 0 < m → Even m →
      (m.divisors.card : ℝ) ≤ Real.log x ^ (M + 6) / Real.log x →
      ‖tailSeries m ⌊Real.log x ^ (M + 6)⌋₊‖ ≤ (1 / 4 : ℝ)

/-- CITED. P0064, Lemma 4 part 4, pages 28 to 30.
The constants depend on M and the cutoff is xi equal to log x to power M plus six. -/
def lemma4TruncationStatement : Prop :=
  ∀ M : ℝ, 0 < M → ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
    ∀ m : ℕ, 0 < m → Even m →
      (m.divisors.card : ℝ) ≤ Real.log x ^ (M + 6) / Real.log x →
      c < ‖partialSeries m ⌊Real.log x ^ (M + 6)⌋₊‖

/-- CONDITIONAL ON uniformTailStatement. P0064, pages 29 and 30, inequalities 4 and 8.
The truncation conclusion follows from the uniform tail input and proved full positivity. -/
theorem lemma4_truncation_of_uniformTail (h : uniformTailStatement) : lemma4TruncationStatement := by
  intro M hM
  obtain ⟨X₀, hX₀, htail⟩ := h M hM
  refine ⟨1 / 8, by norm_num, X₀, hX₀, fun x hx m hm heven hτ => ?_⟩
  have H := partial_lower_of_tail m hm heven ⌊Real.log x ^ (M + 6)⌋₊ (htail x hx m hm heven hτ)
  exact lt_of_lt_of_le (by norm_num : (1 / 8 : ℝ) < 1 / 4) H

end LeanLab.Tchudakov1938.Tail113
