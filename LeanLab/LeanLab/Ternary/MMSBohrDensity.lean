/-
P0028, https://arxiv.org/abs/1610.02017, Lemma 4.3 item 3, page 10.
Smoothing preserves progression density for a small positive density margin.
The averaging set and its displacement bound are explicit hypotheses.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSShiftDensity

namespace LeanLab.Ternary.MMS
open Finset

/-- Lemma 4.3 item 3 for any nonempty averaging set with sufficiently short differences. -/
theorem intSmooth_denseOnAPs {N : ℕ} {η ε δ : ℝ} {f : ℕ → ℝ}
    (hd : DenseOnAPs N η ε f) (hη : 0 ≤ η)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 6) (hδ : 0 ≤ δ)
    (B : Finset ℤ) (hB : B.Nonempty)
    (hshort : ∀ a ∈ B, ∀ b ∈ B, |((a - b : ℤ) : ℝ)| ≤ δ * N) :
    DenseOnAPs N (η + δ / ε) (ε / 2)
      (fun n => intSmooth B (intervalLift N f) n) := by
  intro P hP hlen
  have hc : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  have hpos : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hηN : 0 ≤ η * N := mul_nonneg hη hN
  have hδN : 0 ≤ δ * N := mul_nonneg hδ hN
  have hid : ε * ((η + δ / ε) * N) = ε * (η * N) + δ * N := by
    field_simp
    <;> ring
  have hshort' : δ * N ≤ ε * P.card := by
    have hm := mul_le_mul_of_nonneg_left hlen hε.le
    rw [hid] at hm
    nlinarith
  have hlen' : η * N + δ * N ≤ P.card := by
    have hquot : δ ≤ δ / ε := (le_div_iff₀ hε).mpr (by nlinarith)
    have hm := mul_le_mul_of_nonneg_right hquot hN
    nlinarith
  have hinner (a : ℤ) (ha : a ∈ B) (b : ℤ) (hb : b ∈ B) :
      (1 / 3 + ε / 2) * P.card ≤
        ∑ n ∈ P, intervalLift N f ((n : ℤ) + a - b) := by
    have hs := hshort a ha b hb
    simpa only [add_sub_assoc] using
      sum_intervalLift_shift_lower hP hd hε hε1 (a - b)
        (hs.trans hshort') (by linarith)
  have hsum : (∑ n ∈ P, ∑ a ∈ B, ∑ b ∈ B,
      intervalLift N f ((n : ℤ) + a - b)) =
      ∑ a ∈ B, ∑ b ∈ B, ∑ n ∈ P, intervalLift N f ((n : ℤ) + a - b) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    rw [sum_comm]
  rw [avg, le_div_iff₀ hpos]
  simp_rw [intSmooth_apply]
  rw [← mul_sum, hsum]
  calc (1 / 3 + ε / 2) * P.card =
        (1 / (B.card : ℝ) ^ 2) *
          (∑ a ∈ B, ∑ b ∈ B, (1 / 3 + ε / 2) * P.card) := by
            simp only [sum_const, nsmul_eq_mul]
            field_simp
            <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_le_sum fun a ha => sum_le_sum fun b hb => hinner a ha b hb) (by positivity)

end LeanLab.Ternary.MMS
