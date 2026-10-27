/-
P0083, page 489, equation 37. Quantitative coefficient sum and tail bounds.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.WeightedPower
import LeanLab.Perelli1996.WeightedConvergence

namespace LeanLab.Perelli1996.Section3
open Finset Real Polynomial

/-- The first error sum in equation 37 saves every positive power loss. -/
theorem weighted_roots_partial_bound (F : ℤ[X]) (hF : Admissible F) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 1 ≤ D →
      ∑ d ∈ Icc 1 D, arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ) ≤
        C * (D : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := weighted_roots_power_bound F hF (show 0 < ε / 2 by positivity)
  let p : ℝ := -1 - ε / 2
  have hp : p < -1 := by dsimp [p]; linarith
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ p) := Real.summable_nat_rpow.mpr hp
  let T := ∑' n : ℕ, (n : ℝ) ^ p
  have hT : 0 < T := by
    have hh := hs.sum_le_tsum ({1} : Finset ℕ) (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) p)
    norm_num at hh
    dsimp [T]
    linarith
  refine ⟨C * T, mul_pos hC hT, fun D hD => ?_⟩
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hterm (d : ℕ) (hd : d ∈ Icc 1 D) :
      arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ) ≤
        C * (D : ℝ) ^ ε * (d : ℝ) ^ p := by
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
    have hc := mul_le_mul_of_nonneg_right (hb d hd1) hdR.le
    rw [div_mul_cancel₀ _ hdR.ne'] at hc
    have hid : (d : ℝ) ^ (-2 + ε / 2) * d = (d : ℝ) ^ (-1 + ε / 2) := by
      rw [← Real.rpow_add_one hdR.ne']
      congr 1
      ring
    have hdDpow : (d : ℝ) ^ ε ≤ (D : ℝ) ^ ε :=
      Real.rpow_le_rpow hdR.le (by exact_mod_cast hdD) hε.le
    calc arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ)
        ≤ C * ((d : ℝ) ^ (-2 + ε / 2) * d) := by nlinarith only [hc]
      _ = C * ((d : ℝ) ^ p * (d : ℝ) ^ ε) := by
        rw [hid, ← Real.rpow_add hdR]
        congr 2
        dsimp [p]
        ring
      _ ≤ C * ((d : ℝ) ^ p * (D : ℝ) ^ ε) := by gcongr
      _ = _ := by ring
  calc (∑ d ∈ Icc 1 D, arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ))
      ≤ ∑ d ∈ Icc 1 D, C * (D : ℝ) ^ ε * (d : ℝ) ^ p := Finset.sum_le_sum hterm
    _ = C * (D : ℝ) ^ ε * ∑ d ∈ Icc 1 D, (d : ℝ) ^ p := by rw [Finset.mul_sum]
    _ ≤ C * (D : ℝ) ^ ε * T := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hs.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) p)
    _ = (C * T) * (D : ℝ) ^ ε := by ring

/-- The second error sum in equation 37 has every exponent above minus one. -/
theorem weighted_roots_tail_bound (F : ℤ[X]) (hF : Admissible F) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 1 ≤ D →
      (∑' d : {d : ℕ // D < d},
        arithmeticFactor d.1 * ((Roots.rootResidues F d.1).card : ℝ) / d.1) ≤
        C * (D : ℝ) ^ (-1 + ε) := by
  obtain ⟨C, hC, hb⟩ := weighted_roots_power_bound F hF (show 0 < ε / 2 by positivity)
  let p : ℝ := -1 - ε / 2
  have hp : p < -1 := by dsimp [p]; linarith
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ p) := Real.summable_nat_rpow.mpr hp
  let T := ∑' n : ℕ, (n : ℝ) ^ p
  have hT : 0 < T := by
    have hh := hs.sum_le_tsum ({1} : Finset ℕ) (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) p)
    norm_num at hh
    dsimp [T]
    linarith
  refine ⟨C * T, mul_pos hC hT, fun D hD => ?_⟩
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hterm (d : {d : ℕ // D < d}) :
      arithmeticFactor d.1 * ((Roots.rootResidues F d.1).card : ℝ) / d.1 ≤
        C * (D : ℝ) ^ (-1 + ε) * (d.1 : ℝ) ^ p := by
    have hd1 : 1 ≤ d.1 := by have := d.2; omega
    have hdR : (0 : ℝ) < d.1 := by exact_mod_cast hd1
    have hpow : (d.1 : ℝ) ^ (-1 + ε) ≤ (D : ℝ) ^ (-1 + ε) :=
      Real.rpow_le_rpow_of_nonpos hDR (by exact_mod_cast d.2.le) (by linarith)
    calc arithmeticFactor d.1 * ((Roots.rootResidues F d.1).card : ℝ) / d.1
        ≤ C * (d.1 : ℝ) ^ (-2 + ε / 2) := hb d.1 hd1
      _ = C * ((d.1 : ℝ) ^ p * (d.1 : ℝ) ^ (-1 + ε)) := by
        rw [← Real.rpow_add hdR]
        congr 2
        dsimp [p]
        ring
      _ ≤ C * ((d.1 : ℝ) ^ p * (D : ℝ) ^ (-1 + ε)) := by gcongr
      _ = _ := by ring
  have hss := (summable_weighted_roots F hF).subtype (fun d => D < d)
  have hps := hs.subtype (fun d => D < d)
  calc (∑' d : {d : ℕ // D < d}, arithmeticFactor d.1 * ((Roots.rootResidues F d.1).card : ℝ) / d.1)
      ≤ ∑' d : {d : ℕ // D < d}, C * (D : ℝ) ^ (-1 + ε) * (d.1 : ℝ) ^ p :=
      hss.tsum_le_tsum hterm (hps.mul_left _)
    _ = C * (D : ℝ) ^ (-1 + ε) * (∑' d : {d : ℕ // D < d}, (d.1 : ℝ) ^ p) := by rw [tsum_mul_left]
    _ ≤ C * (D : ℝ) ^ (-1 + ε) * T := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hs.tsum_subtype_le _ (fun d : ℕ => D < d) (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) p)
    _ = (C * T) * (D : ℝ) ^ (-1 + ε) := by ring

end LeanLab.Perelli1996.Section3
