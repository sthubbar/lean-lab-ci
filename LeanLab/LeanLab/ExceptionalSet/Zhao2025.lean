/-
P0040 Zhao 2025, arXiv 2511.05631v2, read from the LaTeX source, unit U-5044. The final step of the
proof of Theorem 1.2 in the case `λ_{1,1} ∈ [0.60, 0.62]`, display (4.13): with `S_i = R_i + T_i`,
`∑ S_i² = ∑ R_i² + ∑ T_i (2 R_i + T_i) ≤ max R · ∑ R + T' (2 ∑ R + ∑ T) + 2 (T'' - T')(2 max R + T'')`,
where `T'` bounds `T_i` for `i ≥ 3` and `T''` bounds `T_1, T_2`.

PROVED: `case_combination`, that inequality for any finite family; `case4_printed`, the printed
inputs 0.3, 0.581, 0.0927, 7.63, 0.1001 give 0.99968 < 1; `case4_stated_fails`, with the 0.101
that (4.10) states in place of 0.1001 the same right side is above 1, so (4.10) and (4.13) are
inconsistent as printed; `case4_recomputed`, the lab's recomputed inputs from gen/zhao_*.py,
0.2994, 0.5798, 0.09271, 7.6235, 0.10022, give below 0.9985, so the proof's case survives.
The inputs themselves come from Python, numerical certificates, not theorems.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.ExceptionalSet.Zhao2025
open Finset

/-- The combination step of (4.13), for a finite family `s` with an exceptional part `A` of at
most two indices. -/
theorem case_combination (s A : Finset ℕ) (hA : A ⊆ s) (hA2 : A.card ≤ 2) (R T : ℕ → ℝ)
    {Rm Tm Tm' : ℝ} (hR0 : ∀ i ∈ s, 0 ≤ R i) (hRm : ∀ i ∈ s, R i ≤ Rm) (hT0 : ∀ i ∈ s, 0 ≤ T i)
    (hTm : ∀ i ∈ s, i ∉ A → T i ≤ Tm) (hTm' : ∀ i ∈ A, T i ≤ Tm') (hTT : Tm ≤ Tm') (hRm0 : 0 ≤ Rm) (hTm'0 : 0 ≤ Tm') :
    ∑ i ∈ s, (R i + T i) ^ 2 ≤
      Rm * ∑ i ∈ s, R i + Tm * (2 * ∑ i ∈ s, R i + ∑ i ∈ s, T i) + 2 * ((Tm' - Tm) * (2 * Rm + Tm')) := by
  -- the excess of each term over `Rm R + Tm (2R + T)`
  set ex : ℕ → ℝ := fun i => (R i + T i) ^ 2 - (Rm * R i + Tm * (2 * R i + T i)) with hex
  have hex_out : ∀ i ∈ s, i ∉ A → ex i ≤ 0 := by
    intro i hi hiA
    have h1 := hR0 i hi; have h2 := hRm i hi; have h3 := hT0 i hi; have h4 := hTm i hi hiA
    simp only [hex]; nlinarith [mul_le_mul_of_nonneg_left h2 h1, mul_le_mul_of_nonneg_right h4 (by linarith : (0:ℝ) ≤ 2 * R i + T i)]
  have hex_in : ∀ i ∈ A, ex i ≤ (Tm' - Tm) * (2 * Rm + Tm') := by
    intro i hiA
    have hi := hA hiA
    have h1 := hR0 i hi; have h2 := hRm i hi; have h3 := hT0 i hi; have h4 := hTm' i hiA
    simp only [hex]
    have hRR : R i ^ 2 ≤ Rm * R i := by nlinarith
    rcases le_total (T i) Tm with h | h
    · have : T i * (2 * R i + T i) ≤ Tm * (2 * R i + T i) :=
        mul_le_mul_of_nonneg_right h (by linarith)
      have : 0 ≤ (Tm' - Tm) * (2 * Rm + Tm') := mul_nonneg (by linarith) (by linarith)
      nlinarith
    · have : (T i - Tm) * (2 * R i + T i) ≤ (Tm' - Tm) * (2 * Rm + Tm') :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
      nlinarith
  have hsplit : ∑ i ∈ s, ex i = ∑ i ∈ A, ex i + ∑ i ∈ s \ A, ex i := by
    rw [← sum_union disjoint_sdiff, union_sdiff_of_subset hA]
  have hout : ∑ i ∈ s \ A, ex i ≤ 0 :=
    sum_nonpos (fun i hi => by rw [mem_sdiff] at hi; exact hex_out i hi.1 hi.2)
  have hin : ∑ i ∈ A, ex i ≤ A.card * ((Tm' - Tm) * (2 * Rm + Tm')) := by
    have := sum_le_sum hex_in
    rwa [sum_const, nsmul_eq_mul] at this
  have hc0 : 0 ≤ (Tm' - Tm) * (2 * Rm + Tm') := mul_nonneg (by linarith) (by linarith)
  have hcard : (A.card : ℝ) * ((Tm' - Tm) * (2 * Rm + Tm')) ≤ 2 * ((Tm' - Tm) * (2 * Rm + Tm')) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hA2) hc0
  have hsum : ∑ i ∈ s, (R i + T i) ^ 2 =
      ∑ i ∈ s, ex i + (Rm * ∑ i ∈ s, R i + Tm * (2 * ∑ i ∈ s, R i + ∑ i ∈ s, T i)) := by
    calc ∑ i ∈ s, (R i + T i) ^ 2 = ∑ i ∈ s, (ex i + (Rm * R i + Tm * (2 * R i + T i))) :=
          sum_congr rfl (fun i _ => by simp only [hex]; ring)
      _ = _ := by simp only [sum_add_distrib, ← mul_sum]
  linarith

/-- (4.13) with the inputs the paper uses: below 1, the printed 0.9996. -/
theorem case4_printed :
    (0.3 : ℝ) * 0.581 + 0.0927 * (2 * 0.581 + 7.63) + 2 * ((0.1001 - 0.0927) * (2 * 0.3 + 0.1001)) < 1 := by
  norm_num

/-- With the `max T_i ≤ 0.101` that (4.10) states, the same right side exceeds 1. -/
theorem case4_stated_fails :
    1 < (0.3 : ℝ) * 0.581 + 0.0927 * (2 * 0.581 + 7.63) + 2 * ((0.101 - 0.0927) * (2 * 0.3 + 0.101)) := by
  norm_num

/-- With the lab's recomputed inputs, gen/zhao_density.out, zhao_R2scan.out, zhao_Rsum.out,
zhao_check.out: below 0.9985. -/
theorem case4_recomputed :
    (0.2994 : ℝ) * 0.5798 + 0.09271 * (2 * 0.5798 + 7.6235) +
      2 * ((0.10022 - 0.09271) * (2 * 0.2994 + 0.10022)) < 0.9985 := by
  norm_num

/-- Section 4, case `[0.40, 0.60]`, (4.7) as it must read: `0.157 · 0.457`, not `0.157 · 0.557`. -/
theorem case3_corrected :
    (0.157 : ℝ) * 0.457 + 0.0704 * (2 * 0.457 + 6.33) < 0.5818 ∧
      0.5974 < (0.157 : ℝ) * 0.557 + 0.0704 * (2 * 0.457 + 6.33) := by
  constructor <;> norm_num

end LeanLab.ExceptionalSet.Zhao2025
