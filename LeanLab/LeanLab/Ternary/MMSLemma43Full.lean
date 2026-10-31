/-
P0028, https://arxiv.org/abs/1610.02017, Lemma 4.3, pages 8 to 10.
A quarter size shift scale preserves density throughout the full epsilon range.
This proves the existing Lemma43 statement without an additional analytic input.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSLargeSpectrum
namespace LeanLab.Ternary.MMS
open Finset

theorem lemma43_density_loss_quarter {ε L D : ℝ} (_hε : 0 < ε) (hε1 : ε ≤ 1)
    (_hL : 0 ≤ L) (hD : 0 ≤ D) (hDL : D ≤ ε / 4 * L) :
    (1 / 3 + ε / 2) * L ≤ (1 / 3 + ε) * (L - D) := by
  have hED : ε * D ≤ D := mul_le_of_le_one_left hD hε1
  nlinarith [mul_nonneg _hε.le _hL]

theorem sum_intervalLift_shift_lower_general {N : ℕ} {P : Finset ℕ} {f : ℕ → ℝ}
    {η ε : ℝ} (hP : IsAPIn N P) (hd : DenseOnAPs N η ε f)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℤ)
    (hshort : |(s : ℝ)| ≤ ε / 4 * P.card)
    (hlen : η * N + |(s : ℝ)| ≤ P.card) :
    (1 / 3 + ε / 2) * P.card ≤ ∑ n ∈ P, intervalLift N f ((n : ℤ) + s) := by
  have hpos : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hlt : |(s : ℝ)| < P.card := by nlinarith
  have hloss := lemma43_density_loss_quarter hε hε1 hpos.le (abs_nonneg (s : ℝ)) hshort
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

theorem intSmooth_denseOnAPs_general {N : ℕ} {η ε δ : ℝ} {f : ℕ → ℝ}
    (hd : DenseOnAPs N η ε f) (hη : 0 ≤ η)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ)
    (B : Finset ℤ) (hB : B.Nonempty)
    (hshort : ∀ a ∈ B, ∀ b ∈ B, |((a - b : ℤ) : ℝ)| ≤ δ * N) :
    DenseOnAPs N (η + 4 * δ / ε) (ε / 2)
      (fun n => intSmooth B (intervalLift N f) n) := by
  intro P hP hlen
  have hc : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  have hpos : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hηN : 0 ≤ η * N := mul_nonneg hη hN
  have hid : ε * ((η + 4 * δ / ε) * N) = ε * (η * N) + 4 * δ * N := by
    field_simp
  have hshort' : δ * N ≤ ε / 4 * P.card := by
    have hm := mul_le_mul_of_nonneg_left hlen hε.le
    rw [hid] at hm
    nlinarith
  have hlen' : η * N + δ * N ≤ P.card := by
    have hquot : δ ≤ 4 * δ / ε := (le_div_iff₀ hε).mpr (by nlinarith)
    have hm := mul_le_mul_of_nonneg_right hquot hN
    nlinarith
  have hinner (a : ℤ) (ha : a ∈ B) (b : ℤ) (hb : b ∈ B) :
      (1 / 3 + ε / 2) * P.card ≤
        ∑ n ∈ P, intervalLift N f ((n : ℤ) + a - b) := by
    have hs := hshort a ha b hb
    simpa only [add_sub_assoc] using
      sum_intervalLift_shift_lower_general hP hd hε hε1 (a - b)
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
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_le_sum fun a ha => sum_le_sum fun b hb => hinner a ha b hb) (by positivity)

theorem lemma43_general_density {ε K q δ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : 0 ≤ K) (hq : 0 < q) (hδ : 0 < δ) :
    ∃ C ≥ (0 : ℝ), ∀ η : ℝ, 0 < η → η < 1 → ∀ N : ℕ, 1 ≤ N → ∀ f : ℕ → ℝ,
      Prop31Hyp N η ε K q f → ∃ g h : ℤ →₀ ℝ, Lemma43Data N η ε K q δ C f g h := by
  obtain ⟨k, hnet⟩ := exists_large_spectrum_net K q (δ / 4) hK hq (by positivity)
  obtain ⟨κ, hκ, hset⟩ := exists_bohr_set_of_frequency_net (δ / 4) (by positivity) k
  refine ⟨1 / κ, by positivity, ?_⟩
  intro η hη hη1 N hN f hf
  obtain ⟨R, hR, hcover⟩ := hnet N (by omega) η ε f hf hη1.le
  obtain ⟨B, hB, hsize, hshort, hphase⟩ :=
    hset N (by omega) R {γ | δ / 4 * N ≤ ‖fhat N f γ‖} hR hcover
  refine ⟨intSmooth B (intervalLift N f), intervalLift N f - intSmooth B (intervalLift N f),
    by abel, prop31Hyp_smooth_bounds hf hη.le B hB κ hκ hsize, ?_, ?_, ?_, ?_⟩
  · intro γ
    have hu := prop31Hyp_uniform_bound hf hη1.le (by positivity : 0 ≤ δ / 4) B hB hphase γ
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith
  · have hd := intSmooth_denseOnAPs_general hf.2.1 hη.le hε hε1
      (by positivity : 0 ≤ δ / 4) B hB hshort
    have he : η + 4 * (δ / 4) / ε = η + δ / ε := by ring
    rwa [he] at hd
  · exact (intSmooth_restriction_bounds B hB _ hq.le).1.trans
      (by simpa only [intLq_intervalLift] using hf.2.2.2)
  · exact (intSmooth_restriction_bounds B hB _ hq.le).2.trans
      (by simpa only [intLq_intervalLift] using hf.2.2.2)

theorem lemma43_proved : Lemma43 := by
  intro ε hε hε1 K q hK hq _ δ hδ _
  exact lemma43_general_density hε hε1.le (by linarith) (by linarith) hδ
end LeanLab.Ternary.MMS
