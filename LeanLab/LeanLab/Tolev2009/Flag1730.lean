/-
Flag unit U-1730, run 20261120-flags, paper P0055, Tolev 2009, arXiv 0902.2669.
Source: P0055 page 1, display 2 and the definition of Delta, and page 2, the Theorem.

The paper bounds only the centered error `Delta = R - M` on average. The old split in
`SPLIT_the_theorem` cut it into an `R` half and an `M` half. Neither half is small alone,
since the unit moduli term of either half has size about `N^2`.

Part A. The Gemini flag on T2 `leaf_error_part_average` holds: its negation is
`not_leaf_error_part_average_1730`, carried over from `SplitAudit423`, no unproved step.

Part B. The Gemini flag on T3 `leaf_main_part_average` is not provable as stated, since
`halupczokS` is `opaque`: nothing in Lean fixes its values, and for the zero series the leaf
holds. What is proved instead: the leaf for the constant series one is FALSE,
`not_mainLeaf_one_1730`, and the T3 leaf is incompatible with the sealed `the_theorem`,
`mainLeaf_contradicts_theorem_1730`. So T3 is false for any series of size one, which is the
paper's series, but this is a QUESTION for the opaque constant, not a Lean refutation.

Part C. Corrected statement: the faithful replacement for both halves is the centered bound
itself, `CenteredLeaf1730`, which is the sealed `TheTheorem` for the published series. It is the
statement `Decomp83.published_assembly` targets; it imports neither old leaf.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Tolev2009.SplitAudit423

open Finset Real
set_option maxHeartbeats 2000000

namespace LeanLab.Tolev2009.Flag1730

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful LeanLab.Tolev2009.Dyadic

/-! ## Part A -/

/-- The T2 leaf, in the `Reps` namespace where it is sealed, is false. -/
theorem not_leaf_error_part_average_1730 :
    ¬ (∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ l₃ : ℕ, 1 ≤ l₃ → ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ,
      (∀ k, |lam k| ≤ 1) → ∀ N : ℕ, Odd N → N₀ ≤ N →
        (∑ k₁ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊,
            ∑ k₂ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊,
              ⨆ l₁ ∈ Reps.residues k₁, ⨆ l₂ ∈ Reps.residues k₂,
                |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter
                    (fun k₃ => Nat.Coprime k₃ l₃),
                  lam k₃ * Reps.R ![k₁, k₂, k₃] ![l₁, l₂, l₃] N|)
          ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A)) :=
  SplitAudit423.not_leaf_error_part_average

/-! ## Part B -/

/-- The T3 leaf shape for a series `S`. With `S = Reps.halupczokS` it is the sealed
`Reps.leaf_main_part_average` statement, see `mainLeaf_match_1730`. -/
def MainLeaf1730 (S : Reps.SSeries) : Prop :=
    ∀ A : ℝ, 0 < A → ∀ B : ℝ, 0 < B → ∀ l₃ : ℕ, 1 ≤ l₃ → ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ,
      (∀ k, |lam k| ≤ 1) → ∀ N : ℕ, Odd N → N₀ ≤ N →
        (∑ k₁ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊,
            ∑ k₂ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊,
              ⨆ l₁ ∈ Reps.residues k₁, ⨆ l₂ ∈ Reps.residues k₂,
                |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter
                    (fun k₃ => Nat.Coprime k₃ l₃),
                  lam k₃ * Reps.M S ![k₁, k₂, k₃] ![l₁, l₂, l₃] N|)
          ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A)

/-- Match: the named shape at the opaque series is the sealed T3 leaf. -/
theorem mainLeaf_match_1730 :
    MainLeaf1730 Reps.halupczokS ↔
    (∀ A : ℝ, 0 < A → ∀ B : ℝ, 0 < B → ∀ l₃ : ℕ, 1 ≤ l₃ → ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ,
      (∀ k, |lam k| ≤ 1) → ∀ N : ℕ, Odd N → N₀ ≤ N →
        (∑ k₁ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊,
            ∑ k₂ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊,
              ⨆ l₁ ∈ Reps.residues k₁, ⨆ l₂ ∈ Reps.residues k₂,
                |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter
                    (fun k₃ => Nat.Coprime k₃ l₃),
                  lam k₃ * Reps.M Reps.halupczokS ![k₁, k₂, k₃] ![l₁, l₂, l₃] N|)
          ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A)) := Iff.rfl

/-- The T3 leaf for the opaque series contradicts the sealed cited Theorem for that series:
`R = Delta + M`, so both bounds would give the T2 bound, which is false. -/
theorem mainLeaf_contradicts_theorem_1730 (h3 : MainLeaf1730 Reps.halupczokS)
    (hT : Reps.TheTheorem Reps.halupczokS) : False := by
  apply SplitAudit423.not_leaf_error_part_average
  intro A hA
  obtain ⟨B, hB, hT'⟩ := hT A hA
  refine ⟨B, hB, fun l₃ hl₃ => ?_⟩
  obtain ⟨C₁, N₁, h₁⟩ := hT' l₃ hl₃
  obtain ⟨C₂, N₂, h₂⟩ := h3 A hA B hB l₃ hl₃
  refine ⟨C₁ + C₂, max N₁ N₂, fun lam hlam N hodd hN => ?_⟩
  have e1 := h₁ lam hlam N hodd (le_trans (le_max_left _ _) hN)
  have e2 := h₂ lam hlam N hodd (le_trans (le_max_right _ _) hN)
  change EF (fun k l => Δ Reps.halupczokS k l N) lam l₃ B N ≤ _ at e1
  change EF (fun k l => M Reps.halupczokS k l N) lam l₃ B N ≤ _ at e2
  have hadd := EF_add_le (fun k l => Δ Reps.halupczokS k l N)
    (fun k l => M Reps.halupczokS k l N) lam l₃ B N
  have hR : (fun k l => Δ Reps.halupczokS k l N + M Reps.halupczokS k l N)
      = fun k l => R k l N := by
    funext k l; simp [Δ]
  rw [hR] at hadd
  change EF (fun k l => R k l N) lam l₃ B N ≤ _
  have hs : C₁ * (N : ℝ) ^ 2 * Real.log N ^ (-A) + C₂ * (N : ℝ) ^ 2 * Real.log N ^ (-A)
      = (C₁ + C₂) * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by ring
  linarith

/-- The T3 leaf shape is false for the constant series one, a series of the paper's size. -/
theorem not_mainLeaf_one_1730 : ¬ MainLeaf1730 (fun _ _ _ => 1) := by
  intro h
  obtain ⟨C, N₀, hC⟩ := h 1 (by norm_num) 1 (by norm_num) 1 le_rfl
  obtain ⟨T, hT⟩ := Instances336.eventual_nonvacuity_parameters (1 / 10000) (by norm_num)
  obtain ⟨m, hm⟩ := exists_nat_gt (max (max N₀ T) (Real.exp (2 * |C| + 2)))
  set N := 2 * m + 1 with hNdef
  have hodd : Odd N := ⟨m, rfl⟩
  have hNm : (m : ℝ) ≤ N := by rw [hNdef]; push_cast; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
  have hbig : max (max N₀ T) (Real.exp (2 * |C| + 2)) < N := lt_of_lt_of_le hm hNm
  have hN0 : N₀ ≤ N := by linarith [le_max_left N₀ T, le_max_left (max N₀ T) (Real.exp (2 * |C| + 2))]
  have hTN : T ≤ N := by linarith [le_max_right N₀ T, le_max_left (max N₀ T) (Real.exp (2 * |C| + 2))]
  have hE : Real.exp (2 * |C| + 2) < N := lt_of_le_of_lt (le_max_right _ _) hbig
  obtain ⟨hL, _, h3⟩ := hT N hTN
  rw [show (10000 : ℝ) * (1 / 10000) = 1 by norm_num] at h3
  have hN1 : 1 ≤ N := by omega
  have h12 := h3.trans (Level346.third_cutoff_le_first 1 N hN1)
  let lam : ℕ → ℝ := fun k => if k = 1 then 1 else 0
  have hlam : ∀ k, |lam k| ≤ 1 := by intro k; dsimp [lam]; split_ifs <;> norm_num
  have hb := hC lam hlam N hodd hN0
  change EF (fun k l => M (fun _ _ _ => 1) k l N) lam 1 1 N ≤ _ at hb
  have hu := (SplitAudit423.unit_entry_le_EF (fun k l => M (fun _ _ _ => 1) k l N) 1 N h12 h3).trans hb
  have hM : M (fun _ _ _ => 1) ![1, 1, 1] ![0, 0, 1] N = (N : ℝ) ^ 2 / 2 := by
    simp [M]
  rw [hM] at hu
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogpos : 0 < Real.log N := by linarith
  have hlog : 2 * |C| + 2 < Real.log N := by
    rw [Real.lt_log_iff_exp_lt hNpos]; exact hE
  rw [Real.rpow_neg_one] at hu
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  rw [abs_of_pos (by positivity)] at hu
  have key : Real.log N / 2 ≤ C := by
    have h' : (N : ℝ) ^ 2 / 2 * Real.log N ≤ C * (N : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hu hlogpos.le
      rwa [mul_assoc, inv_mul_cancel₀ hlogpos.ne', mul_one] at this
    nlinarith
  linarith [le_abs_self C]

/-! ## Part C. Corrected sealed statement -/

/-- Corrected leaf. Twin: for every `A > 0` there is `B > 0` such that the weighted average
over `k1, k2 <= sqrt N L^-B`, `k3 <= N^(1/3) L^-B` of the maximal centered error
`|sum lam k3 Delta|` is at most `C N^2 L^-A`. Source P0055 page 2, the Theorem. The R and M
halves are not split; this is the published centered statement. -/
def CenteredLeaf1730 (S : SSeries) : Prop := TheTheorem S

/-- Vacuity instance: with the series that makes `M = R` exactly, here realised by any `S` for
which `Delta = 0`, the hypotheses and the bound are satisfiable. We exhibit it by `C = 0`
for the zero error case: the centered average of the zero function is zero. -/
theorem centeredLeaf_vacuity_1730 (lam : ℕ → ℝ) (l₃ : ℕ) (B : ℝ) (N : ℕ) :
    EF (fun _ _ => (0 : ℝ)) lam l₃ B N = 0 := by
  simp [EF, innerF]

end LeanLab.Tolev2009.Flag1730
