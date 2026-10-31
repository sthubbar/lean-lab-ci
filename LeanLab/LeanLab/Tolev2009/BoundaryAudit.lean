/-
Implementation audit for task40.
AI wrote the Lean code. Binary Goldbach is open.
These are elementary facts about the natural interval used in Vblk.
They are not a claim about an error in Tolev 2009.
Source: Displays14to16.lean, definition Vblk, and Faithful.lean, definition EF.
Paper comparison for display 10 is blocked by source access.
Status: CLAIMED. No Lean toolchain is available in this run.
-/
import LeanLab.Tolev2009.Displays14to16

open Finset

namespace LeanLab.Tolev2009.BoundaryAudit

/-- The natural block used by Vblk excludes modulus one. -/
theorem one_not_mem_nat_block (K : ℕ) : 1 ∉ Ioc K (2 * K) := by
  simp only [mem_Ioc]
  omega

/-- A nonnegative weight supported at modulus one vanishes on every such block. -/
theorem singleton_weight_block (K : ℕ) :
    ∑ k ∈ Ioc K (2 * K), (if k = 1 then (1 : ℝ) else 0) = 0 := by
  apply sum_eq_zero
  intro k hk
  have hne : k ≠ 1 := by
    intro h
    subst k
    exact one_not_mem_nat_block K hk
  simp [hne]

/-- The same weight has total mass one on the initial interval. -/
theorem singleton_weight_initial :
    ∑ k ∈ Icc 1 1, (if k = 1 then (1 : ℝ) else 0) = 1 := by
  norm_num

end LeanLab.Tolev2009.BoundaryAudit
