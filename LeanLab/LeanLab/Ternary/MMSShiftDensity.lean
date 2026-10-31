/-
P0028, https://arxiv.org/abs/1610.02017, Lemma 4.3 item 3, page 10.
Finite sum transport for clipped shifts of arithmetic progressions.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSShiftAP
import LeanLab.Ternary.MMSIntervalLift
import LeanLab.Ternary.MMSLemma43Arithmetic

namespace LeanLab.Ternary.MMS
open Finset

/-- The zero extension transports the whole progression sum to its clipped right shift. -/
theorem sum_intervalLift_right {N t : ℕ} {P : Finset ℕ} (f : ℕ → ℝ)
    (hP : P ⊆ Icc 1 N) :
    (∑ n ∈ P, intervalLift N f ((n : ℤ) + t)) = ∑ n ∈ shiftRightIn N t P, f n := by
  rw [shiftRightIn, sum_image]
  · rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    have hn1 := (mem_Icc.mp (hP hn)).1
    rw [← Nat.cast_add, intervalLift_apply_nat]
    by_cases hnt : n + t ≤ N
    · simp [hnt, mem_Icc, show 1 ≤ n + t by omega]
    · simp [hnt, mem_Icc]
  · intro a ha b hb hab
    change a + t = b + t at hab
    omega

/-- The zero extension transports the whole progression sum to its clipped left shift. -/
theorem sum_intervalLift_left {N t : ℕ} {P : Finset ℕ} (f : ℕ → ℝ)
    (hP : P ⊆ Icc 1 N) :
    (∑ n ∈ P, intervalLift N f ((n : ℤ) - t)) = ∑ n ∈ shiftLeftIn t P, f n := by
  rw [shiftLeftIn, sum_image]
  · rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    have hnN := (mem_Icc.mp (hP hn)).2
    by_cases hnt : t < n
    · have htn : t ≤ n := hnt.le
      rw [← Int.ofNat_sub htn, intervalLift_apply_nat]
      simp [hnt, mem_Icc, show 1 ≤ n - t by omega, show n - t ≤ N by omega]
    · simp only [hnt, ite_false]
      by_cases he : n = t
      · subst n
        rw [sub_self]
        simpa using intervalLift_apply_nat N f 0
      · exact intervalLift_apply_neg N f _ (by omega)
  · intro a ha b hb hab
    change a - t = b - t at hab
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    omega

/-- A right shift loses at most its displacement from the progression density bound. -/
theorem sum_intervalLift_right_lower {N t : ℕ} {P : Finset ℕ} {f : ℕ → ℝ}
    {η ε : ℝ} (hP : IsAPIn N P) (hd : DenseOnAPs N η ε f) (hε : 0 ≤ ε)
    (ht : t < P.card) (hlen : η * N + t ≤ P.card) :
    (1 / 3 + ε) * ((P.card : ℝ) - t) ≤
      ∑ n ∈ P, intervalLift N f ((n : ℤ) + t) := by
  have hsub : P ⊆ Icc 1 N := by
    obtain ⟨a, d, L, hd, hL, he, hIn⟩ := hP
    exact fun n hn => mem_Icc.mpr (hIn n hn)
  have hc := shiftRightIn_card (t := t) hsub
  have hne : (shiftRightIn N t P).Nonempty := card_pos.mp (by omega)
  have hc' : P.card ≤ (shiftRightIn N t P).card + t := by omega
  have hcr : (P.card : ℝ) ≤ (shiftRightIn N t P).card + t := by exact_mod_cast hc'
  have hd' := hd _ (shiftRightIn_isAP hP hne) (by linarith : η * N ≤ _)
  have hpos : (0 : ℝ) < (shiftRightIn N t P).card := by exact_mod_cast hne.card_pos
  rw [avg, le_div_iff₀ hpos] at hd'
  rw [sum_intervalLift_right f hsub]
  exact (mul_le_mul_of_nonneg_left (by linarith :
    (P.card : ℝ) - t ≤ (shiftRightIn N t P).card) (by linarith)).trans hd'

/-- A left shift loses at most its displacement from the progression density bound. -/
theorem sum_intervalLift_left_lower {N t : ℕ} {P : Finset ℕ} {f : ℕ → ℝ}
    {η ε : ℝ} (hP : IsAPIn N P) (hd : DenseOnAPs N η ε f) (hε : 0 ≤ ε)
    (ht : t < P.card) (hlen : η * N + t ≤ P.card) :
    (1 / 3 + ε) * ((P.card : ℝ) - t) ≤
      ∑ n ∈ P, intervalLift N f ((n : ℤ) - t) := by
  have hsub : P ⊆ Icc 1 N := by
    obtain ⟨a, d, L, hd, hL, he, hIn⟩ := hP
    exact fun n hn => mem_Icc.mpr (hIn n hn)
  have hc := shiftLeftIn_card (t := t) hsub
  have hne : (shiftLeftIn t P).Nonempty := card_pos.mp (by omega)
  have hc' : P.card ≤ (shiftLeftIn t P).card + t := by omega
  have hcr : (P.card : ℝ) ≤ (shiftLeftIn t P).card + t := by exact_mod_cast hc'
  have hd' := hd _ (shiftLeftIn_isAP hP hne) (by linarith : η * N ≤ _)
  have hpos : (0 : ℝ) < (shiftLeftIn t P).card := by exact_mod_cast hne.card_pos
  rw [avg, le_div_iff₀ hpos] at hd'
  rw [sum_intervalLift_left f hsub]
  exact (mul_le_mul_of_nonneg_left (by linarith :
    (P.card : ℝ) - t ≤ (shiftLeftIn t P).card) (by linarith)).trans hd'

/-- Every sufficiently short signed shift preserves half of a small density margin. -/
theorem sum_intervalLift_shift_lower {N : ℕ} {P : Finset ℕ} {f : ℕ → ℝ}
    {η ε : ℝ} (hP : IsAPIn N P) (hd : DenseOnAPs N η ε f)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 6) (s : ℤ)
    (hshort : |(s : ℝ)| ≤ ε * P.card)
    (hlen : η * N + |(s : ℝ)| ≤ P.card) :
    (1 / 3 + ε / 2) * P.card ≤ ∑ n ∈ P, intervalLift N f ((n : ℤ) + s) := by
  have hpos : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hlt : |(s : ℝ)| < P.card := by nlinarith
  have hloss := lemma43_density_loss hε hε1 (abs_nonneg (s : ℝ)) hshort
  by_cases hs : 0 ≤ s
  · lift s to ℕ using hs with t
    have habs : |((t : ℤ) : ℝ)| = (t : ℝ) := by simp
    rw [habs] at hlt hlen hloss
    have ht : t < P.card := by exact_mod_cast hlt
    exact hloss.trans (sum_intervalLift_right_lower hP hd hε.le ht hlen)
  · obtain ⟨t, ht⟩ : ∃ t : ℕ, s = -(t : ℤ) := ⟨s.natAbs, by omega⟩
    subst s
    have habs : |((-(t : ℤ) : ℤ) : ℝ)| = (t : ℝ) := by simp
    rw [habs] at hlt hlen hloss
    have ht : t < P.card := by exact_mod_cast hlt
    simpa only [sub_eq_add_neg] using
      hloss.trans (sum_intervalLift_left_lower hP hd hε.le ht hlen)

end LeanLab.Ternary.MMS
