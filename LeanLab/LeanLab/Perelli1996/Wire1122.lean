/-
P0083 Perelli 1996, pages 478 through 486. ROUTE BURST S79 burst-20261122 wiring file.
Theorem 1 reassembled exactly as Burst103.theorem1_of_split, with the character
estimate of pages 484 and 485 taken from the Char1122 split.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Burst103
import LeanLab.Perelli1996.Good1122

namespace LeanLab.Perelli1996.Wire1122
open Finset Real Polynomial MeasureTheory
open scoped ArithmeticFunction.vonMangoldt
open LeanLab.Perelli1996.Decomp88 LeanLab.Perelli1996.Decomp103 LeanLab.Perelli1996.Burst103

noncomputable section

/-- Theorem 1, page 478, the assembly of Burst103.theorem1_of_split copied with one change:
the character step is Good1122.leaf_character_of_split3 instead of Decomp88.leaf_character,
and the assembly runs with A replaced by max A B₀, since that split holds for B ≥ B₀.
CONDITIONAL ON Decomp103.leaf_nair_mean, Diff1122.leaf_weyl_differencing,
Decomp582a.leaf_zero_density, Bad1122.leaf_bad_modulus_large,
Bad1122.leaf_character_expansion and Good1122.leaf_good_short_variance. -/
theorem theorem1_of_split : LeanLab.Perelli1996.Theorem1 := by
  intro F hF A₀ ε hA₀ hε
  obtain ⟨c, Nc, hc, hNc, hcut⟩ := leaf_cutoff F hF
  obtain ⟨d, hd, hmajor⟩ := major_of_split F hF c hc
  -- Burst S79: the character step holds for B ≥ B₀; run the assembly with A = max A₀ B₀,
  -- so B > A ≥ B₀, and weaken L^(-A) to L^(-A₀) at the end.
  obtain ⟨B₀, hB₀, hchar⟩ := Good1122.leaf_character_of_split3 F hF c hc
  set A := max A₀ B₀ with hAdef
  have hA : 0 < A := hA₀.trans_le (le_max_left _ _)
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
    leaf_local_mass F hF c hc ε B hε hB (hchar ε B hε (by
      have hkA : 0 ≤ 8 * K * (A + 2) := by positivity
      have : B₀ ≤ A := le_max_right _ _
      dsimp [B]; nlinarith [sq_nonneg k]))
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
    _ = (4 * CM + 2 * CR * (CL + 1)) * H * N ^ 2 * Real.log N ^ (-A) := by ring
    _ ≤ _ := by
      have hAA : -A ≤ -A₀ := neg_le_neg (le_max_left _ _)
      gcongr

end
end LeanLab.Perelli1996.Wire1122
