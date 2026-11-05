import LeanLab.RamareSaouter2003.Decomp290a
import LeanLab.RamareSaouter2003.Decomp359a

/-!
P0099 p. 19, the near bounds after display 13, summed in display 15.
The number of near indices is separated from the already proved term estimate.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp359f

open Real Smooth L3Zeta Decomp290c

/-- LEAF. P0099 pp. 19 and 20, the factor 2N of T in display 15.
The finite band contains exactly the positive and negative ordinate indices.
There are no real zeros in the open strip, as already proved in Decomp1531b.
This leaf counts indices only and contains no smoothing term. -/
theorem near_band_card (T : ℝ) (hT : 0 ≤ T) :
    (((Decomp359a.ordinate_band_finite T).toFinset).card : ℝ) = 2 * L1Zeta.NZr T := by
  classical
  let s := (Decomp359a.ordinate_band_finite T).toFinset
  let p := L1Zeta.A T
  let n := s.filter (fun i => ¬ 0 < gZ i)
  have hs (i : ZI) : i ∈ s ↔ |gZ i| ≤ T := by simp [s]
  have hg0 (i : ZI) : gZ i ≠ 0 := by
    intro hh
    obtain ⟨hz, hb0, hb1⟩ := mem_strip i.1
    have hn := Decomp1531b.riemannZeta_ne_zero_of_real hb0 hb1
    have hc : (((i.1 : ℂ)).re : ℂ) = (i.1 : ℂ) := by
      apply Complex.ext
      · simp
      · simpa [gZ] using hh.symm
    apply hn
    rw [hc]
    exact hz
  have hp : s.filter (fun i => 0 < gZ i) = p := by
    ext i
    simp only [Finset.mem_filter, hs, L1Zeta.mem_A, p]
    constructor
    · rintro ⟨ha, hpos⟩
      exact ⟨hpos, (le_abs_self (gZ i)).trans ha⟩
    · rintro ⟨hpos, hle⟩
      exact ⟨by simpa [abs_of_pos hpos] using hle, hpos⟩
  have hnp : n.image σZ ⊆ p := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨his, hnot⟩ := Finset.mem_filter.mp hi
    have hneg : gZ i < 0 := lt_of_le_of_ne (not_lt.mp hnot) (hg0 i)
    have hab := (hs i).mp his
    change σZ i ∈ L1Zeta.A T
    rw [L1Zeta.mem_A, L1Zeta.gZ_σ_neg]
    exact ⟨by linarith, by simpa [abs_of_neg hneg] using hab⟩
  have hpn : p.image σZ ⊆ n := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hpos, hle⟩ := L1Zeta.mem_A.mp hi
    apply Finset.mem_filter.mpr
    constructor
    · apply (hs _).mpr
      rw [gZ_σ, abs_of_pos hpos]
      exact hle
    · rw [L1Zeta.gZ_σ_neg]
      linarith
  have hnpCard : n.card ≤ p.card := by
    rw [← Finset.card_image_of_injective n σZ_injective]
    exact Finset.card_le_card hnp
  have hpnCard : p.card ≤ n.card := by
    rw [← Finset.card_image_of_injective p σZ_injective]
    exact Finset.card_le_card hpn
  have hpartition := Finset.card_filter_add_card_filter_not (s := s) (fun i => 0 < gZ i)
  rw [hp] at hpartition
  change p.card + n.card = s.card at hpartition
  have hcard : s.card = 2 * p.card := by omega
  change (s.card : ℝ) = 2 * (p.card : ℝ)
  exact_mod_cast hcard

/-- The exact near_sum_le target of Decomp290a.
P0099 p. 19, the near bounds after display 13. CONDITIONAL ON near_band_card. -/
theorem near_sum_le (hRH : RHUpTo 3300000000) (m : ℕ) (X u T : ℝ)
    (hm : 2 ≤ m) (hX : 10 ^ 12 ≤ X) (hu : 0 < u)
    (hmu : (m : ℝ) * u ≤ 0.0001) (hT : 1000 ≤ T) (hTT : T ≤ 3300000000) :
    nearSum m X u T ≤ 2 * L1Zeta.NZr T *
      (u * (1 + m * u) * √X * ∫ t in (0 : ℝ)..1, fm m t) := by
  classical
  let s := (Decomp359a.ordinate_band_finite T).toFinset
  let B := u * (1 + m * u) * √X * ∫ t in (0 : ℝ)..1, fm m t
  have hB : 0 ≤ B := by
    have := (Decomp1531a.integral_fm_pos m).le
    dsimp [B]
    positivity
  have hu_small : u ≤ 0.0001 := by
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hs (i : ZI) : i ∈ s ↔ |gZ i| ≤ T := by simp [s]
  have hzero (i : ZI) (hi : i ∉ s) :
      (if |gZ i| ≤ T then (zeroTerm m X u i).re else 0) = 0 := by
    simp [show ¬ |gZ i| ≤ T from fun hh => hi ((hs i).mpr hh)]
  rw [nearSum, tsum_eq_sum hzero]
  calc
    _ ≤ ∑ _i ∈ s, B := by
      apply Finset.sum_le_sum
      intro i hi
      have hband := (hs i).mp hi
      have hcrit := bZ_half hRH i (hband.trans hTT)
      have hterm := Decomp1531a.near_zero_term_le hcrit hm hu.le hu_small
        (by linarith : 0 < X)
      simpa only [if_pos hband] using (Complex.re_le_norm (zeroTerm m X u i)).trans hterm
    _ = (s.card : ℝ) * B := by simp [nsmul_eq_mul]
    _ = _ := by rw [show (s.card : ℝ) = 2 * L1Zeta.NZr T from near_band_card T (by linarith)]

end LeanLab.RamareSaouter2003.Decomp359f

#print axioms LeanLab.RamareSaouter2003.Decomp359f.near_band_card
#print axioms LeanLab.RamareSaouter2003.Decomp359f.near_sum_le
