/-
P0083 Perelli 1996, page 485, display 25, arguing as in Perelli and Pintz 1993 Section 5.
ROUTE BURST S79 burst-20261122 split of Char1122.leaf_good_character_mean.
Gallagher's lemma, PP1993 equation 21, is PROVED here at the length L = ⌊qQ/2⌋ through
Character632.character_gallagher_reduction; the short interval variance of the good characters,
PP1993 equations 22 through 26 with the density estimate 21 of Perelli, is the new LEAF.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Bad1122
import LeanLab.Perelli1996.Character632
import LeanLab.Perelli1996.Dens1123

namespace LeanLab.Perelli1996.Good1122
open Finset Real Polynomial MeasureTheory
open LeanLab.Perelli1996.Decomp88 LeanLab.Perelli1996.Decomp582a LeanLab.Perelli1996.Char1122
open scoped ArithmeticFunction.vonMangoldt
noncomputable section

attribute [local instance] Classical.propDecidable

/-- PP1993 equation 21, Gallagher's lemma, at the explicit length L = ⌊qQ/2⌋ for qQ ≥ 2:
∫_{|η| ≤ 1/(qQ)} |W(χ,η)|² ≤ 4π²/(qQ)² ∑_m |∑_{m-L < n ≤ m} (Λ(n)χ(n) - δ_χ)|². -/
theorem gallagher_floor (M q : ℕ) [NeZero q] (Q : ℝ) (hQ : 0 < Q) (horder : 2 ≤ (q : ℝ) * Q)
    (χ : DirichletCharacter ℂ q) :
    (∫ η in (-(1 / ((q : ℝ) * Q)))..(1 / ((q : ℝ) * Q)), ‖twistedRemainder M χ η‖ ^ 2) ≤
      (4 * Real.pi ^ 2 / ((q : ℝ) * Q) ^ 2) *
        ∑ m ∈ range (M + 1 + ⌊(q : ℝ) * Q / 2⌋₊),
          ‖LeanLab.PNTPort.Gallagher.win
            (fun n => (Λ n : ℂ) * χ n - (if χ = 1 then 1 else 0)) (M + 1) ⌊(q : ℝ) * Q / 2⌋₊ m‖ ^ 2 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqQ : 0 < (q : ℝ) * Q := mul_pos hq0 hQ
  set L : ℕ := ⌊(q : ℝ) * Q / 2⌋₊ with hLdef
  have hL1 : 1 ≤ L := by
    apply Nat.le_floor
    norm_num
    linarith
  have hL : 0 < L := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hfloor : (q : ℝ) * Q / 2 < (L : ℝ) + 1 := Nat.lt_floor_add_one _
  have hLlow : (q : ℝ) * Q / 4 ≤ (L : ℝ) := by
    by_cases hsmall : (q : ℝ) * Q ≤ 4
    · have hL1R : (1 : ℝ) ≤ L := by exact_mod_cast hL1
      linarith
    · linarith
  have hLup : (L : ℝ) ≤ (q : ℝ) * Q / 2 := Nat.floor_le (by positivity)
  have hrad : 1 / ((q : ℝ) * Q) ≤ 1 / (2 * (L : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have heq : (fun η => ‖twistedRemainder M χ η‖ ^ 2) =
      (fun η => ‖(∑ n ∈ range (M + 1), (Λ n : ℂ) * χ n * Kernel.e ((n : ℝ) * η)) -
        (if χ = 1 then (1 : ℂ) else 0) * Kernel.T 0 (M + 1) η‖ ^ 2) := by
    funext η; unfold twistedRemainder; split_ifs <;> simp
  have hc : Continuous (fun η : ℝ => ‖twistedRemainder M χ η‖ ^ 2) :=
    ((continuous_twistedRemainder M χ).norm).pow 2
  have hi : (∫ η in (-(1 / ((q : ℝ) * Q)))..(1 / ((q : ℝ) * Q)), ‖twistedRemainder M χ η‖ ^ 2) ≤
      ∫ η in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ‖twistedRemainder M χ η‖ ^ 2 := by
    apply intervalIntegral.integral_mono_interval (neg_le_neg hrad)
      (by linarith [one_div_pos.mpr hqQ]) hrad
    · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
    · exact hc.intervalIntegrable _ _
  have hcoeff : (Real.pi / (2 * L)) ^ 2 ≤ 4 * Real.pi ^ 2 / ((q : ℝ) * Q) ^ 2 := by
    have hh : Real.pi / (2 * L) ≤ 2 * Real.pi / ((q : ℝ) * Q) := by
      apply (div_le_div_iff₀ (by positivity) hqQ).mpr
      have hp := mul_le_mul_of_nonneg_left hLlow (show 0 ≤ 4 * Real.pi by positivity)
      nlinarith
    have hs := pow_le_pow_left₀ (show 0 ≤ Real.pi / (2 * L) by positivity) hh 2
    convert hs using 1 <;> ring
  have hg := character_gallagher_reduction M L q hL χ (if χ = 1 then 1 else 0)
  rw [← heq] at hg
  exact hi.trans (hg.trans
    (mul_le_mul_of_nonneg_right hcoeff (Finset.sum_nonneg (fun _ _ => sq_nonneg _))))

/-- LEAF: Page 485 display 25, arguing as in Perelli and Pintz 1993 Section 5 equations 22
through 26: after Gallagher's lemma, the truncated explicit formula for the good characters,
the short interval smoothing and the density estimate 21 give, for B ≥ B₀,
q/φ(q) ∑_{χ good} 4π²/(qQ)² ∑_m |∑_{m-L < n ≤ m} (Λ(n)χ(n) - δ_χ)|² ≪ N L^(-B)
with L = ⌊qQ/2⌋. Class HARD. CONDITIONAL ON display 21 through hDensity. -/
theorem leaf_good_short_variance (F : ℤ[X]) (hF : Admissible F)
    (C d : ℝ) (hC : 0 < C) (hd : 0 < d) (hDensity : DensityInput C d)
    (c : ℝ) (hc : 0 < c) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ ε B : ℝ, 0 < ε → B₀ ≤ B →
    ∃ C' N₀ : ℝ, 0 < C' ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ fareyOrder F N H B →
        (q : ℝ) / q.totient * ∑ χ : DirichletCharacter ℂ q,
          (if goodCharacter B ε N χ then
            (4 * Real.pi ^ 2 / ((q : ℝ) * fareyOrder F N H B) ^ 2) *
              ∑ m ∈ range (⌊c * N⌋₊ + 1 + ⌊(q : ℝ) * fareyOrder F N H B / 2⌋₊),
                ‖LeanLab.PNTPort.Gallagher.win
                  (fun n => (Λ n : ℂ) * χ n - (if χ = 1 then 1 else 0)) (⌊c * N⌋₊ + 1)
                  ⌊(q : ℝ) * fareyOrder F N H B / 2⌋₊ m‖ ^ 2
          else 0) ≤ C' * N * Real.log N ^ (-B) := by
  sorry

/-- Page 485 display 25, the exact statement of Char1122.leaf_good_character_mean,
proved from gallagher_floor and the LEAF leaf_good_short_variance.
CONDITIONAL ON display 21 and leaf_good_short_variance. -/
theorem good_character_mean_of_split (F : ℤ[X]) (hF : Admissible F)
    (C d : ℝ) (hC : 0 < C) (hd : 0 < d) (hDensity : DensityInput C d)
    (c : ℝ) (hc : 0 < c) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ ε B : ℝ, 0 < ε → B₀ ≤ B →
    ∃ C' N₀ : ℝ, 0 < C' ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ fareyOrder F N H B →
        goodEnergy B ε N ⌊c * N⌋₊ q (fareyOrder F N H B) ≤ C' * N * Real.log N ^ (-B) := by
  obtain ⟨B₀, hB₀, hall⟩ := leaf_good_short_variance F hF C d hC hd hDensity c hc
  refine ⟨B₀, hB₀, ?_⟩
  intro ε B hε hBB
  have hB : 0 < B := hB₀.trans_le hBB
  obtain ⟨C1, N1, hC1, hN1, hv⟩ := hall ε B hε hBB
  obtain ⟨NA, hNA, harc⟩ := arc_parameters F hF ε B hε hB
  refine ⟨C1, max N1 NA, hC1, hN1.trans (le_max_left _ _), ?_⟩
  intro N H hN hH hHu q _ hqQ
  have hQ2 : 2 ≤ fareyOrder F N H B := (harc N H ((le_max_right _ _).trans hN) hH).2
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have horder : 2 ≤ (q : ℝ) * fareyOrder F N H B := by nlinarith
  refine le_trans ?_ (hv N H ((le_max_left _ _).trans hN) hH hHu q hqQ)
  unfold goodEnergy
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro χ _
  by_cases hg : goodCharacter B ε N χ
  · rw [if_pos hg, if_pos hg]
    exact gallagher_floor _ q _ (by linarith) horder χ
  · rw [if_neg hg, if_neg hg]

/-- Pages 484 and 485 displays 16 through 25, the same statement as
Char1122.leaf_character_of_split, with display 24 from Bad1122.bad_character_removal_of_split and display 25
from good_character_mean_of_split. The exact statement of
Decomp88.leaf_character, restricted to B ≥ B₀, CONDITIONAL ON display 21 through Dens1123.leaf_zero_density_of_split1123, burst S110, leaf_good_short_variance and the two
Bad1122 LEAFs, for B at least the B₀ of leaf_good_character_mean.
The assembly itself has no sorry. -/
theorem leaf_character_of_split3 (F : ℤ[X]) (hF : Admissible F)
    (c : ℝ) (hc : 0 < c) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ ε B : ℝ, 0 < ε → B₀ ≤ B →
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ fareyOrder F N H B →
      ∀ a : ℤ, Nat.Coprime a.natAbs q →
      (∫ η in (-(1 / ((q : ℝ) * fareyOrder F N H B)))..
        (1 / ((q : ℝ) * fareyOrder F N H B)),
        ‖characterRemainder ⌊c * N⌋₊ q a η‖ ^ 2) ≤ C * N * Real.log N ^ (-B) := by
  obtain ⟨CD, d, hCD, hd, hDensity⟩ := Dens1123.leaf_zero_density_of_split1123
  obtain ⟨B₀, hB₀, h25all⟩ := good_character_mean_of_split F hF CD d hCD hd hDensity c hc
  refine ⟨B₀, hB₀, ?_⟩
  intro ε B hε hBB
  have hB : 0 < B := hB₀.trans_le hBB
  obtain ⟨C1, N1, hC1, hN1, h24⟩ :=
    Bad1122.bad_character_removal_of_split F hF CD d hCD hd hDensity c hc ε B hε hB
  obtain ⟨C2, N2, hC2, hN2, h25⟩ := h25all ε B hε hBB
  refine ⟨C1 * (C2 + 1), max N1 N2, by positivity, hN1.trans (le_max_left _ _), ?_⟩
  intro N H hN hH hHu q hq hqQ a hcop
  haveI : NeZero q := ⟨hq.ne'⟩
  have hb := h24 N H ((le_max_left _ _).trans hN) hH hHu q hqQ a hcop
  have hg := h25 N H ((le_max_right _ _).trans hN) hH hHu q hqQ
  have hN0 : 0 < N := by linarith [hN1.trans ((le_max_left N1 N2).trans hN)]
  have hP : 0 ≤ N * Real.log N ^ (-B) := by
    have : 0 < Real.log N := Real.log_pos (by linarith [hN1.trans ((le_max_left N1 N2).trans hN)])
    positivity
  calc _ ≤ C1 * (goodEnergy B ε N ⌊c * N⌋₊ q (fareyOrder F N H B) +
          N * Real.log N ^ (-B)) := hb
    _ ≤ C1 * (C2 * N * Real.log N ^ (-B) + N * Real.log N ^ (-B)) := by gcongr
    _ = C1 * (C2 + 1) * N * Real.log N ^ (-B) := by ring

end
end LeanLab.Perelli1996.Good1122
