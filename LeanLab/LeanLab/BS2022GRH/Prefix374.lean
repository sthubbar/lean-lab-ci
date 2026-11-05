/- AI wrote this Lean code for CODEX task374. Goldbach is open.
Finite residue algebra for the single endpoint leaf on journal p. 1224. -/
import LeanLab.BS2022GRH.DecompC164a
import Mathlib.NumberTheory.DirichletCharacter.Bounds

namespace LeanLab.BS2022GRH.Prefix374
open Real Finset Classical
noncomputable section

/-- Expand a finite character sum by residue classes, journal p. 1224 before display 13. -/
theorem residue_expansion (S : Finset ℕ) (r : ℕ) (hr : 0 < r)
    (χ : DirichletCharacter ℂ r) :
    (∑ p ∈ S, χ p) = ∑ a ∈ range r,
      χ a * ((S.filter (fun p => p % r = a)).card : ℂ) := by
  have hm : ∀ p ∈ S, p % r ∈ range r := fun p _ => mem_range.mpr (Nat.mod_lt p hr)
  have hs := Finset.sum_fiberwise_of_maps_to' hm (fun a : ℕ => χ a)
  simpa only [sum_const, nsmul_eq_mul, mul_comm, ZMod.natCast_mod] using hs.symm

/-- A nonprincipal character sums to zero over the reduced residues, journal p. 1224. -/
theorem reduced_residue_cancellation (r : ℕ) (hr : 0 < r)
    (χ : DirichletCharacter ℂ r) (hχ : χ ≠ 1) :
    (∑ a ∈ (range r).filter (fun a => Nat.Coprime a r), χ a) = 0 := by
  haveI : NeZero r := ⟨hr.ne'⟩
  have hfull : (∑ a ∈ range r, χ a) = ∑ a : ZMod r, χ a := by
    apply Finset.sum_bij (s := range r) (t := (univ : Finset (ZMod r)))
      (fun (a : ℕ) _ => (a : ZMod r))
    · intro a ha
      exact mem_univ _
    · intro a ha b hb heq
      have h := (ZMod.natCast_eq_natCast_iff' a b r).mp heq
      simpa only [Nat.mod_eq_of_lt (mem_range.mp ha), Nat.mod_eq_of_lt (mem_range.mp hb)] using h
    · intro a ha
      exact ⟨a.val, mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
    · intro a ha
      rfl
  calc
    (∑ a ∈ (range r).filter (fun a => Nat.Coprime a r), χ a) = ∑ a ∈ range r, χ a := by
      apply sum_subset (filter_subset _ _)
      intro a ha hn
      have hc : ¬ Nat.Coprime a r := by
        simpa only [mem_filter, ha, true_and] using hn
      apply MulChar.map_nonunit
      simpa only [ZMod.isUnit_iff_coprime] using hc
    _ = ∑ a : ZMod r, χ a := hfull
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

/-- Center every residue count by a common main term before taking norms, journal p. 1224.
CONDITIONAL ON the explicit progression errors supplied as hbound. No analytic input is hidden. -/
theorem norm_sum_of_residue_errors (S : Finset ℕ) (r : ℕ) (hr : 0 < r)
    (χ : DirichletCharacter ℂ r) (hχ : χ ≠ 1) (M B : ℝ)
    (hbound : ∀ a ∈ (range r).filter (fun a => Nat.Coprime a r),
      |(((S.filter (fun p => p % r = a)).card : ℝ)) - M| ≤ B) :
    ‖∑ p ∈ S, χ p‖ ≤ r.totient * B := by
  let A := (range r).filter (fun a => Nat.Coprime a r)
  have hred : (∑ p ∈ S, χ p) = ∑ a ∈ A,
      χ a * ((S.filter (fun p => p % r = a)).card : ℂ) := by
    rw [residue_expansion S r hr χ]
    symm
    apply sum_subset (filter_subset _ _)
    intro a ha hn
    have hnc : ¬ Nat.Coprime a r := by
      simpa only [A, mem_filter, ha, true_and] using hn
    have hz : χ (a : ZMod r) = 0 := MulChar.map_nonunit χ (by
      simpa only [ZMod.isUnit_iff_coprime] using hnc)
    rw [hz, zero_mul]
  have hcenter : (∑ p ∈ S, χ p) = ∑ a ∈ A,
      χ a * (((S.filter (fun p => p % r = a)).card : ℂ) - (M : ℂ)) := by
    rw [hred]
    simp only [mul_sub, sum_sub_distrib, ← sum_mul,
      reduced_residue_cancellation r hr χ hχ, zero_mul, sub_zero, A]
  rw [hcenter]
  apply (norm_sum_le _ _).trans
  calc
    (∑ a ∈ A, ‖χ a * (((S.filter (fun p => p % r = a)).card : ℂ) - (M : ℂ))‖)
        ≤ ∑ _a ∈ A, B := by
      apply sum_le_sum
      intro a ha
      rw [norm_mul]
      have he : ‖((S.filter (fun p => p % r = a)).card : ℂ) - (M : ℂ)‖ =
          |((S.filter (fun p => p % r = a)).card : ℝ) - M| := by
        rw [show ((S.filter (fun p => p % r = a)).card : ℂ) - (M : ℂ) =
          (((S.filter (fun p => p % r = a)).card : ℝ) - M : ℝ) by push_cast; rfl]
        exact Complex.norm_real _
      rw [he]
      exact (mul_le_of_le_one_left (abs_nonneg _) (χ.norm_le_one _)).trans (hbound a ha)
    _ = r.totient * B := by
      simp only [sum_const, nsmul_eq_mul]
      have hc : A.card = r.totient := by
        simp only [A, Nat.totient_eq_card_coprime, Nat.coprime_comm]
      rw [hc]

end
end LeanLab.BS2022GRH.Prefix374
#print axioms LeanLab.BS2022GRH.Prefix374.residue_expansion
#print axioms LeanLab.BS2022GRH.Prefix374.reduced_residue_cancellation
#print axioms LeanLab.BS2022GRH.Prefix374.norm_sum_of_residue_errors
