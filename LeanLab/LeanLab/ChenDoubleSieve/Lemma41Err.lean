import LeanLab.ChenDoubleSieve.Lemma41

/-!
# Wu 2004 Lemma 4.1 with an explicit remainder

P0036 J. Wu 2004, Section 4, Lemma 4.1. Unit U-5401, CLOUD 20261019T1014Z-cloud22.
AI wrote the Lean code.

For `A ⊆ {0, …, N}`, as Wu's `A = {N - p : p ≤ N}` is, the error term `E` of `lemma41_exact`
satisfies `E ≤ ω(d) (N/(d w) + 1)` for `d ≥ 1`, `w > 0`; summed against weights `σ(d) ≥ 0`
this is `lemma41_explicit`:
`2 Σ σ(d) S(A_d; P(dN), z_d) ≤ Σ σ(d) (Ω₁ - Ω₂ + Ω₃) + Σ σ(d) ω(d) (N/(d w_d) + 1)`.
With Wu's `σ ∈ U_k(N)`, `ω(d) ≤ k`, `w_d = d̲^{1/s'} ≥ W_k^{1/10}`, `Σ σ(d)/d ≪ 1`, and
`Σ σ(d) ≤ Q`, the remainder is `≪ k N^{1 - δ^{1+k}/10} + k N^{1/2}`, Wu's `O(N^{1-η})`; that last
step uses Wu's (3.5), a Mertens type bound, and is not formalized here.
Binary Goldbach is OPEN.
-/

open Finset

noncomputable section
open scoped Classical

namespace LeanLab.ChenDoubleSieve.Wu41

/-- Multiples of `m ≥ 1` in a subset of `{0, …, N}`: at most `N/m + 1`. -/
lemma card_dvd_le {A : Finset ℕ} {N : ℕ} (hA : A ⊆ range (N + 1)) {m : ℕ} (hm : 1 ≤ m) :
    (#{a ∈ A | m ∣ a} : ℝ) ≤ N / m + 1 := by
  have hsub : {a ∈ A | m ∣ a} ⊆ insert 0 {x ∈ Ioc 0 N | m ∣ x} := by
    intro a ha
    rw [mem_filter] at ha
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h]; exact mem_insert_self _ _
    · apply mem_insert_of_mem
      have := mem_range.1 (hA ha.1)
      rw [mem_filter, mem_Ioc]; exact ⟨⟨h, by omega⟩, ha.2⟩
  have h1 := card_le_card hsub
  have h2 := card_insert_le 0 {x ∈ Ioc 0 N | m ∣ x}
  rw [Nat.Ioc_filter_dvd_card_eq_div] at h2
  have h3 : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
  have h4 : (#{a ∈ A | m ∣ a} : ℝ) ≤ ((N / m : ℕ) : ℝ) + 1 := by exact_mod_cast h1.trans h2
  linarith

lemma S_le_card_dvd (A : Finset ℕ) (e D : ℕ) (y : ℝ) : S A e D y ≤ #{a ∈ A | e ∣ a} := by
  unfold S
  apply card_le_card
  intro a ha
  rw [mem_filter] at ha ⊢
  exact ⟨ha.1, ha.2.1⟩

/-- `E ≤ ω(d) (N/(d w) + 1)`. -/
theorem err_le {A : Finset ℕ} {N : ℕ} (hA : A ⊆ range (N + 1)) {d : ℕ} (hd : 1 ≤ d)
    {w z : ℝ} (hw : 0 < w) :
    (Err A d N w z : ℝ) ≤ (d.primeFactors.card : ℝ) * (N / (d * w) + 1) := by
  unfold Err
  push_cast
  have hterm : ∀ p ∈ {p ∈ PS N w z | p ∣ d},
      (S A (d * p) (d * N) w : ℝ) ≤ N / (d * w) + 1 := by
    intro p hp
    rw [mem_filter, mem_PS] at hp
    obtain ⟨⟨hpr, hwp, -, -⟩, -⟩ := hp
    have hdp : 1 ≤ d * p := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) hpr.ne_zero)
    have h1 : (S A (d * p) (d * N) w : ℝ) ≤ #{a ∈ A | d * p ∣ a} := by
      exact_mod_cast S_le_card_dvd A (d * p) (d * N) w
    have h2 := card_dvd_le hA hdp
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have h3 : (N : ℝ) / ((d * p : ℕ) : ℝ) ≤ N / (d * w) := by
      push_cast
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hwp hd'.le
    linarith
  calc ∑ p ∈ {p ∈ PS N w z | p ∣ d}, (S A (d * p) (d * N) w : ℝ)
      ≤ ∑ p ∈ {p ∈ PS N w z | p ∣ d}, ((N : ℝ) / (d * w) + 1) := sum_le_sum hterm
    _ = (#{p ∈ PS N w z | p ∣ d} : ℝ) * (N / (d * w) + 1) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (d.primeFactors.card : ℝ) * (N / (d * w) + 1) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have : {p ∈ PS N w z | p ∣ d} ⊆ d.primeFactors := by
        intro p hp
        rw [mem_filter, mem_PS] at hp
        exact Nat.mem_primeFactors.2 ⟨hp.1.1, hp.2, by omega⟩
      exact_mod_cast card_le_card this

/-- **Wu 2004 Lemma 4.1 with an explicit remainder**, for `A ⊆ {0, …, N}`, weights `σ ≥ 0` on a
finite set `D` of `d ≥ 1`, and `0 < w d ≤ z d`. -/
theorem lemma41_explicit {A : Finset ℕ} {N : ℕ} (hA : A ⊆ range (N + 1)) (D : Finset ℕ)
    (hD : ∀ d ∈ D, 1 ≤ d) (σ : ℕ → ℝ) (hσ : ∀ d ∈ D, 0 ≤ σ d) (w z : ℕ → ℝ)
    (hw : ∀ d ∈ D, 0 < w d) (hwz : ∀ d ∈ D, w d ≤ z d) :
    2 * ∑ d ∈ D, σ d * S A d (d * N) (z d) ≤
      ∑ d ∈ D, σ d * ((Ω₁ A d N (w d) : ℝ) - Ω₂ A d N (w d) (z d) + Ω₃ A d N (w d) (z d))
        + ∑ d ∈ D, σ d * ((d.primeFactors.card : ℝ) * (N / (d * w d) + 1)) := by
  refine (lemma41_weighted A N D σ hσ w z hwz).trans ?_
  rw [← sum_add_distrib]
  refine sum_le_sum fun d hd => ?_
  have := err_le hA (hD d hd) (z := z d) (hw d hd)
  nlinarith [hσ d hd]

end LeanLab.ChenDoubleSieve.Wu41
