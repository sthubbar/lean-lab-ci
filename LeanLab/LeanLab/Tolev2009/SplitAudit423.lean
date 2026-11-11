/-
AI wrote this Lean code. Codex task423.
Binary Goldbach is open.
This audits the old separate prime count split against the definition of R.
It does not assert an error in Tolev 2009.
-/
import LeanLab.Tolev2009.Convolution423
import LeanLab.Tolev2009.Decomp423a
import LeanLab.Tolev2009.SPLIT_the_theorem

open Finset Real
set_option maxHeartbeats 2000000
namespace LeanLab.Tolev2009.SplitAudit423
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful LeanLab.Tolev2009.Dyadic

/-- Isolate a unit modulus entry of the averaged error with a bounded indicator weight.
Source context: Tolev 2009 page 4, the definition of the weighted average. -/
theorem unit_entry_le_EF (F : (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℝ) (B : ℝ) (N : ℕ)
    (h12 : 1 ≤ cutoff B N) (h3 : 1 ≤ cutoff3 B N) :
    |F ![1, 1, 1] ![0, 0, 1]| ≤
      EF F (fun k => if k = 1 then 1 else 0) 1 B N := by
  classical
  let lam : ℕ → ℝ := fun k => if k = 1 then 1 else 0
  have hm : 1 ∈ Icc 1 (cutoff B N) := mem_Icc.mpr ⟨le_rfl, h12⟩
  have hk : 1 ∈ (Icc 1 (cutoff3 B N)).filter (fun k => Nat.Coprime k 1) := by
    simp [h3]
  have hr : 0 ∈ residues 1 := by norm_num [residues]
  have hs := le_iSup2 (residues 1) (residues 1)
    (fun l₁ l₂ => |∑ k ∈ (Icc 1 (cutoff3 B N)).filter (fun k => Nat.Coprime k 1),
      lam k * F ![1, 1, k] ![l₁, l₂, 1]|)
    (fun _ _ => abs_nonneg _) hr hr
  have he : |F ![1, 1, 1] ![0, 0, 1]| ≤ innerF F lam 1 (cutoff3 B N) 1 1 := by
    have hsum : (∑ k ∈ (Icc 1 (cutoff3 B N)).filter (fun k => Nat.Coprime k 1),
        lam k * F ![1, 1, k] ![0, 0, 1]) = F ![1, 1, 1] ![0, 0, 1] := by
      simp [lam, hk, h3, Finset.sum_ite_eq']
    rw [hsum] at hs
    exact hs
  have hrow : innerF F lam 1 (cutoff3 B N) 1 1 ≤
      ∑ k₂ ∈ Icc 1 (cutoff B N), innerF F lam 1 (cutoff3 B N) 1 k₂ :=
    single_le_sum (f := fun k₂ => innerF F lam 1 (cutoff3 B N) 1 k₂)
      (fun k _ => innerF_nonneg F lam 1 (cutoff3 B N) 1 k) hm
  have htotal : (∑ k₂ ∈ Icc 1 (cutoff B N), innerF F lam 1 (cutoff3 B N) 1 k₂) ≤
      ∑ k₁ ∈ Icc 1 (cutoff B N), ∑ k₂ ∈ Icc 1 (cutoff B N),
        innerF F lam 1 (cutoff3 B N) k₁ k₂ :=
    single_le_sum (f := fun k₁ => ∑ k₂ ∈ Icc 1 (cutoff B N),
      innerF F lam 1 (cutoff3 B N) k₁ k₂)
      (fun k _ => sum_nonneg (fun j _ => innerF_nonneg F lam 1 (cutoff3 B N) k j)) hm
  simpa only [EF, cutoff, cutoff3, lam] using he.trans (hrow.trans htotal)

/-- The exact old separate prime count leaf is false.
The paper estimates the centered error instead. This is a formalization audit. -/
theorem not_leaf_error_part_average :
    ¬ (
∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ l₃ : ℕ, 1 ≤ l₃ → ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ,
      (∀ k, |lam k| ≤ 1) → ∀ N : ℕ, Odd N → N₀ ≤ N →
        (∑ k₁ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊,
            ∑ k₂ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊,
              ⨆ l₁ ∈ residues k₁, ⨆ l₂ ∈ residues k₂,
                |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter
                    (fun k₃ => Nat.Coprime k₃ l₃),
                  lam k₃ * R ![k₁, k₂, k₃] ![l₁, l₂, l₃] N|)
          ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A)
    ) := by
  intro hsplit
  obtain ⟨B, hB, hBnd⟩ := hsplit 1 (by norm_num)
  obtain ⟨C, N₀, hC⟩ := hBnd 1 (by norm_num)
  obtain ⟨T, hT⟩ := Instances336.eventual_nonvacuity_parameters (B / 10000) (by positivity)
  apply Convolution423.uncentered_count_no_log_saving
  refine ⟨C, max N₀ T, ?_⟩
  intro N hodd hN
  obtain ⟨hL, _, h3⟩ := hT N ((le_max_right _ _).trans hN)
  rw [show (10000 : ℝ) * (B / 10000) = B by ring] at h3
  have hN1 : 1 ≤ N := by
    by_contra hh
    have hz : N = 0 := by omega
    norm_num [hz] at hL
  have h12 := h3.trans (Level346.third_cutoff_le_first B N hN1)
  let lam : ℕ → ℝ := fun k => if k = 1 then 1 else 0
  have hlam : ∀ k, |lam k| ≤ 1 := by intro k; dsimp [lam]; split_ifs <;> norm_num
  have hb := hC lam hlam N hodd ((le_max_left _ _).trans hN)
  change EF (fun k l => LeanLab.Tolev2009.R k l N) lam 1 B N ≤
    C * (N : ℝ) ^ 2 * Real.log N ^ (-(1 : ℝ)) at hb
  have hu := (unit_entry_le_EF (fun k l => LeanLab.Tolev2009.R k l N) B N h12 h3).trans hb
  have heq : LeanLab.Tolev2009.R ![1, 1, 1] ![0, 0, 1] N =
      LeanLab.Tolev2009.R (fun _ => 1) (fun _ => 0) N := by rfl
  rw [heq, abs_of_nonneg (R_nonneg _ _ _)] at hu
  simpa only [Real.rpow_neg_one, div_eq_mul_inv] using hu

end LeanLab.Tolev2009.SplitAudit423
