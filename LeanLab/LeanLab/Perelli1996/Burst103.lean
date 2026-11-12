/-
P0083 Perelli 1996, pages 481 through 486. ROUTE BURST 3 wiring file.
Theorem 1 reassembled with the pointwise major arc step taken from Decomp320a,
where it is PROVED from Decomp320a.leaf_finite_major, itself PROVED through
ArcModel320, and the proved arithmetic tail Decomp320a.leaf_singular_tail.
Decomp103.lean is claimed by another agent, so nothing there is edited; this file
proves copies of Decomp103.major and Decomp88.theorem1 under new names.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Decomp88
import LeanLab.Perelli1996.Decomp320a

namespace LeanLab.Perelli1996.Burst103
open Finset Real Polynomial MeasureTheory
open scoped ArithmeticFunction.vonMangoldt
open LeanLab.Perelli1996.Decomp88 LeanLab.Perelli1996.Decomp103

noncomputable section

/-- Equation 4 of page 481, same statement as Decomp103.major.
CONDITIONAL ON Decomp103.leaf_nair_mean only. -/
theorem major_of_split (F : ℤ[X]) (hF : Admissible F) (c : ℝ) (hc : 0 < c) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ A ε B : ℝ, 0 < A → 0 < ε → 0 < B →
      ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      (∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n).toNat ≤ ⌊c * N⌋₊) →
      majorError F ⌊c * N⌋₊ N H B ≤
        C * H * N ^ 2 * (Real.log N ^ (-2 * B + d) + Real.log N ^ (-A)) := by
  obtain ⟨d, hd, hmean⟩ := leaf_nair_mean F hF
  refine ⟨d, hd, ?_⟩
  intro A ε B hA hε hB
  obtain ⟨CP, NP, hCP, hNP, hpoint⟩ := Decomp320a.leaf_major_pointwise F hF c hc A ε B hA hε hB
  obtain ⟨CM, NM, hCM, hNM, hmean⟩ := hmean ε hε
  refine ⟨CP * (CM + 2), max NP NM, by positivity, hNP.trans (le_max_left _ _), ?_⟩
  intro N H hN hH hHu hcut
  have hNP' := (le_max_left NP NM).trans hN
  have hNM' := (le_max_right NP NM).trans hN
  have hN3 := hNP.trans hNP'
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hexp : 0 ≤ 1 / (3 * (F.natDegree : ℝ)) + ε := by positivity
  have hH1 : 1 ≤ H := (Real.one_le_rpow (by linarith) hexp).trans hH
  have hcard : ((win F N H).card : ℝ) ≤ 2 * H :=
    (card_win_le F hN0.le (by linarith)).trans (by linarith)
  have hsum := Finset.sum_le_sum (hpoint N H hNP' hH hHu hcut)
  have hm := hmean N H hNM' hH hHu
  unfold majorError
  calc
    _ ≤ ∑ n ∈ win F N H, CP * N ^ 2 *
        (Real.log N ^ (-2 * B) * majorWeight (Fv F n).toNat N ^ 2 + Real.log N ^ (-A)) := hsum
    _ = CP * N ^ 2 * (Real.log N ^ (-2 * B) *
        (∑ n ∈ win F N H, majorWeight (Fv F n).toNat N ^ 2) +
        ((win F N H).card : ℝ) * Real.log N ^ (-A)) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ CP * N ^ 2 * (Real.log N ^ (-2 * B) * (CM * H * Real.log N ^ d) +
        (2 * H) * Real.log N ^ (-A)) := by gcongr
    _ = CP * CM * H * N ^ 2 * Real.log N ^ (-2 * B + d) +
        2 * CP * H * N ^ 2 * Real.log N ^ (-A) := by
      rw [show Real.log N ^ (-2 * B) * (CM * H * Real.log N ^ d) =
        CM * H * (Real.log N ^ (-2 * B) * Real.log N ^ d) by ring,
        ← Real.rpow_add hL]
      ring
    _ ≤ _ := by
      have h1 : CP * CM ≤ CP * (CM + 2) := by nlinarith
      have h2 : 2 * CP ≤ CP * (CM + 2) := by nlinarith
      rw [mul_add]
      gcongr


/-- Theorem 1, page 478, same assembly as Decomp88.theorem1 with the major arc step
from major_of_split. CONDITIONAL ON Decomp103.leaf_nair_mean,
Decomp103b.leaf_differencing and Decomp88.leaf_character. -/
theorem theorem1_of_split : LeanLab.Perelli1996.Theorem1 := by
  intro F hF A ε hA hε
  obtain ⟨c, Nc, hc, hNc, hcut⟩ := leaf_cutoff F hF
  obtain ⟨d, hd, hmajor⟩ := major_of_split F hF c hc
  let k : ℝ := F.natDegree
  let K : ℝ := Section2.weylExponent F
  have hk : 1 ≤ k := by dsimp [k]; exact_mod_cast hF.1
  have hK : 1 ≤ K := by
    dsimp [K, Section2.weylExponent]
    exact one_le_pow₀ (by norm_num)
  let B := 8 * K * (A + 2) + 4 * k ^ 2 + d + A + 1
  obtain ⟨hB, heM, heR, _, _, _⟩ := Section2.parameter_choice hA.le hd hk hK
  change 0 < B at hB
  change -2 * B + d ≤ -A at heM
  change -(B - 4 * k ^ 2 - 16 * K) / (8 * K) ≤ -A at heR
  have heL : -B / 2 + 1 ≤ -A := by
    dsimp [B]
    have hKA := mul_nonneg (show 0 ≤ K by linarith) hA.le
    have hk2 : 0 ≤ k ^ 2 := sq_nonneg k
    nlinarith
  obtain ⟨CM, NM, hCM, hNM, hM⟩ := hmajor A ε B hA hε hB
  obtain ⟨CR, NR, hCR, hNR, hR⟩ :=
    leaf_minor_reduction F hF (leaf_weyl F) c hc ε B hε hB
  obtain ⟨CL, NL, hCL, hNL, hL⟩ :=
    leaf_local_mass F hF c hc ε B hε hB (leaf_character F hF c hc ε B hε hB)
  refine ⟨4 * CM + 2 * CR * (CL + 1), max (Real.exp 1) (max Nc (max NM (max NR NL))), ?_⟩
  intro N H hN hH hHu
  have hNcN : Nc ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hNMN : NM ≤ N := le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN))
  have hNRN : NR ≤ N := le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)))
  have hNLN : NL ≤ N := le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)))
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity : 0 < Real.exp 1)
    (le_trans (le_max_left _ _) hN)
  have hH0 : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hH
  have hlog : 1 ≤ Real.log N := by
    have := Real.log_le_log (Real.exp_pos 1) (le_trans (le_max_left _ _) hN)
    simpa using this
  have hlog0 : 0 < Real.log N := by linarith
  have hcutN := hcut N H hNcN hH0.le hHu
  have hmajorN := hM N H hNMN hH hHu hcutN
  have hminorN := hR N H hNRN hH hHu hcutN
  have hlocalN := hL N H hNLN hH hHu
  have hpowM := Real.rpow_le_rpow_of_exponent_le hlog heM
  have hpowR := Real.rpow_le_rpow_of_exponent_le hlog heR
  have hpowL := Real.rpow_le_rpow_of_exponent_le hlog heL
  have hmain : majorError F ⌊c * N⌋₊ N H B ≤
      2 * CM * H * N ^ 2 * Real.log N ^ (-A) := by
    calc _ ≤ CM * H * N ^ 2 * (Real.log N ^ (-2 * B + d) + Real.log N ^ (-A)) := hmajorN
      _ ≤ CM * H * N ^ 2 * (Real.log N ^ (-A) + Real.log N ^ (-A)) := by gcongr
      _ = _ := by ring
  have hminor : minorError F ⌊c * N⌋₊ N H B ≤
      CR * (CL + 1) * H * N ^ 2 * Real.log N ^ (-A) := by
    calc _ ≤ CR * H * N * Real.log N ^ (B / 2 + 1) *
          localMass ⌊c * N⌋₊ N B (fareyOrder F N H B) +
        CR * H * N ^ 2 * Real.log N ^ (-(B - 4 * k ^ 2 - 16 * K) / (8 * K)) := hminorN
      _ ≤ CR * H * N * Real.log N ^ (B / 2 + 1) * (CL * N * Real.log N ^ (-B)) +
        CR * H * N ^ 2 * Real.log N ^ (-(B - 4 * k ^ 2 - 16 * K) / (8 * K)) := by gcongr
      _ = CR * CL * H * N ^ 2 * Real.log N ^ (-B / 2 + 1) +
        CR * H * N ^ 2 * Real.log N ^ (-(B - 4 * k ^ 2 - 16 * K) / (8 * K)) := by
        rw [show CR * H * N * Real.log N ^ (B / 2 + 1) * (CL * N * Real.log N ^ (-B)) =
          CR * CL * H * N ^ 2 * (Real.log N ^ (B / 2 + 1) * Real.log N ^ (-B)) by ring]
        rw [← Real.rpow_add hlog0]
        congr 3
        ring
      _ ≤ CR * CL * H * N ^ 2 * Real.log N ^ (-A) +
        CR * H * N ^ 2 * Real.log N ^ (-A) := by gcongr
      _ = _ := by ring
  have hs := leaf_split F ⌊c * N⌋₊ N H B (fun n hn => (hcutN n hn).2)
  calc _ ≤ 2 * majorError F ⌊c * N⌋₊ N H B + 2 * minorError F ⌊c * N⌋₊ N H B := hs
    _ ≤ 2 * (2 * CM * H * N ^ 2 * Real.log N ^ (-A)) +
      2 * (CR * (CL + 1) * H * N ^ 2 * Real.log N ^ (-A)) := by gcongr
    _ = _ := by ring

end
end LeanLab.Perelli1996.Burst103
