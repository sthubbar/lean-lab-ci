/-
Assemblies for the exact sealed Decomp413a targets.
PP1993 pages 44 to 48, https://doi.org/10.1112/jlms/s2-47.1.41.
These results are CONDITIONAL ON the smaller OPEN leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp489b
import LeanLab.Languasco2004.Decomp489c
import LeanLab.Languasco2004.Decomp489d

namespace LeanLab.Languasco2004.Decomp489e
open Finset Real MeasureTheory Decomp279b Decomp413a Decomp489a Decomp489b Decomp489c Decomp489d
noncomputable section

/-- Pages 43 and 44: a fixed threshold makes the chosen window at least 16.
This is only exponent arithmetic, with no prime estimate. -/
theorem window_at_least_sixteen {N η : ℝ} (hN : (16 : ℝ) ^ 36 ≤ N) (hη : 0 < η) :
    16 ≤ windowLength N η := by
  have hN1 : 1 ≤ N := (by norm_num : (1 : ℝ) ≤ 16 ^ 36).trans hN
  have hroot : (16 : ℝ) ≤ N ^ (1 / 36 : ℝ) := by
    rw [show (1 / 36 : ℝ) = (36 : ℝ)⁻¹ by norm_num,
      Real.le_rpow_inv_iff_of_pos (by norm_num) (by linarith : 0 ≤ N) (by norm_num : (0 : ℝ) < 36)]
    simpa using hN
  exact hroot.trans (Real.rpow_le_rpow_of_exponent_le hN1
    (by unfold lengthExponent; nlinarith : (1 / 36 : ℝ) ≤ lengthExponent η))

/-- The exact sealed local_mass_bound statement, assembled from the rational
principal, bad character, good character and geometry leaves.
CONDITIONAL ON those leaves and the four cited analytic inputs. -/
theorem local_mass_bound_from_leaves :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℝ, N₀ ≤ N → ∀ ξ : ℝ,
      localMass N (localization N η) (windowLength N η) (arcExponent η A) ξ ≤
        C * localization N η / Real.log N ^ (2 * A + 3) := by
  obtain ⟨ep, hep, hp⟩ := principal_arc_bound
  obtain ⟨er, her, hr⟩ := remainder_to_good zero_free_input density_input
  obtain ⟨eg, heg, hg⟩ := good_character_envelope density_input gallagher_input explicit_formula_input Decomp489f.dyadic_input
  obtain ⟨NF, hF⟩ := farey_local_reduction
  refine ⟨min ep (min er eg), lt_min hep (lt_min her heg), ?_⟩
  intro η A hη hsmall hA
  obtain ⟨CP, NP, hCP, hP⟩ := hp η A hη (hsmall.trans_le (min_le_left _ _)) hA
  obtain ⟨CR, NR, hCR, hR⟩ := hr η A hη
    (hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hA
  obtain ⟨CG, NG, hCG, hG⟩ := hg η A hη
    (hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hA
  refine ⟨4 * (CP + CR * (2 * CG + 1)),
    max (max (max NG NR) (max NP NF)) (max (Real.exp 1) ((16 : ℝ) ^ 36)), by positivity, ?_⟩
  intro N hN ξ
  obtain ⟨hleft, hright⟩ := max_le_iff.mp hN
  obtain ⟨hGN, hPF⟩ := max_le_iff.mp hleft
  obtain ⟨hNG, hNR⟩ := max_le_iff.mp hGN
  obtain ⟨hNP, hNF⟩ := max_le_iff.mp hPF
  obtain ⟨hNe, hN16⟩ := max_le_iff.mp hright
  have hN0 : 0 < N := (Real.exp_pos 1).trans_le hNe
  have hL : 0 < Real.log N := by
    have := Real.log_le_log (Real.exp_pos 1) hNe
    rw [Real.log_exp] at this
    linarith
  have hY : 0 < localization N η := Real.rpow_pos_of_pos hN0 _
  let V : ℝ := localization N η / Real.log N ^ (2 * A + 3)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hgood : ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ fareyOrder (windowLength N η) →
      goodEnergy q N (localization N η) (windowLength N η) (arcExponent η A) ≤ 2 * CG * V := by
    intro q hq hqQ
    have hgq := hG N hNG (localization N η / Real.log N ^ (2 * A + 23)) (by positivity)
      (fun σ _ hs => density_power_saving hNe hη hA hs) q hq hqQ
    rw [log_power_cancellation hL] at hgq
    dsimp [V]
    nlinarith [hgq]
  have hrem := hR N hNR (2 * CG * V) (by positivity) hgood
  have hmaj := hP N hNP
  have hB : 0 ≤ arcExponent η A := by unfold arcExponent; positivity
  have hlocal := hF N (localization N η) (windowLength N η) (arcExponent η A)
    (CP * V) (CR * ((2 * CG + 1) * V)) hNF hY
    (window_at_least_sixteen hN16 hη) hB (by positivity) (by positivity)
    (by intro q hq hqQ; simpa [V, mul_div_assoc] using hmaj q hq hqQ)
    (by
      intro q a hq hqQ ha haq hcop
      have ht := hrem q a hq hqQ ha haq hcop
      convert ht using 1 <;> dsimp [V] <;> ring) ξ
  convert hlocal using 1 <;> dsimp [V] <;> ring

/-- The exact sealed coefficient_energy statement, with its elementary weight
summation separated from the short interval and Fourier operator inputs.
CONDITIONAL ON short_mangoldt_input and short_coefficient_operator. -/
theorem coefficient_energy_from_leaves :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ D N₀ : ℝ, 0 < D ∧ ∀ N : ℝ, N₀ ≤ N → ∀ K : ℝ, 0 ≤ K →
      (∀ ξ : ℝ, kernelMass N (localization N η) (windowLength N η) (arcExponent η A) ξ ≤ K) →
      (∑ m ∈ window N η,
        ‖minorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m‖ ^ 2) ^ 2 ≤
        D * (localization N η * Real.log N) ^ 3 * K := by
  obtain ⟨C, NC, hC, hshort⟩ := short_mangoldt_input (1 / 2) (by norm_num)
  refine ⟨1 / 12, by norm_num, ?_⟩
  intro η A hη hsmall _
  refine ⟨C ^ 2 * (Real.log 4 + 4), max NC (max 2 ((16 : ℝ) ^ 36)), by positivity, ?_⟩
  intro N hN K hK hk
  obtain ⟨hNC, hNrest⟩ := max_le_iff.mp hN
  obtain ⟨hN2, hN16⟩ := max_le_iff.mp hNrest
  have hN1 : 1 ≤ N := by linarith
  have hNp : 0 < N := by linarith
  have hL : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hY : 0 ≤ localization N η := (Real.rpow_pos_of_pos hNp _).le
  have hYN : localization N η ≤ N := by
    calc localization N η ≤ N ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = N := Real.rpow_one N
  have hNY : N ^ (1 / 2 : ℝ) ≤ localization N η :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hf := firstWeight_of_mangoldt hN1 (hshort N (localization N η) hNC hNY hYN)
  have hs := secondWeight_bound hN1 hY hYN
  have hf0 : 0 ≤ firstWeight N (localization N η) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs0 : 0 ≤ secondWeight (localization N η) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hf2 := pow_le_pow_left₀ hf0 hf 2
  have hw : firstWeight N (localization N η) ^ 2 * secondWeight (localization N η) ≤
      (C * localization N η * Real.log N) ^ 2 *
        ((Real.log 4 + 4) * localization N η * Real.log N) :=
    mul_le_mul hf2 hs hs0 (sq_nonneg _)
  have hb := short_coefficient_operator N (localization N η) (windowLength N η)
    (arcExponent η A) K (window_at_least_sixteen hN16 hη) hK hk
  have hfinal := hb.trans (mul_le_mul_of_nonneg_right hw hK)
  convert hfinal using 1 <;> first | rfl | ring

#print axioms window_at_least_sixteen
#print axioms local_mass_bound_from_leaves
#print axioms coefficient_energy_from_leaves
end
end LeanLab.Languasco2004.Decomp489e
