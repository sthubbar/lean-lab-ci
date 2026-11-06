import LeanLab.Ricci1937.Decomp338p

/-!
Ricci 1937, additive mixed CRT count.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary additive mixed CRT discrepancy for first memoir pages 75 and 88.
The high factor can be translated independently. This includes either sign of the Z gap.
Second memoir pages 106, 107 and 115. -/
lemma decomp338_mixed_add_periodic_remainder (h k N d e : ℕ)
    (hd : 0 < d) (he : 0 < e) (hde : Nat.Coprime d e) :
    |(#{m ∈ range N | d ∣ m * (m + h) ∧ e ∣ m + k} : ℝ) -
      (cnt h d : ℝ) * N / (d * e)| ≤ cnt h d := by
  let Q : ℕ → Prop := fun m => (-(m : ZMod d)) * ((h : ZMod d) - (-(m : ZMod d))) = 0 ∧ (m : ZMod e) + k = 0
  have hperiod : Function.Periodic Q (d * e) := by
    intro m
    simp [Q, rootPred, Nat.cast_add, Nat.cast_mul]
  have : NeZero d := ⟨hd.ne'⟩
  have : NeZero e := ⟨he.ne'⟩
  have : NeZero (d * e) := ⟨(Nat.mul_pos hd he).ne'⟩
  let E := ZMod.chineseRemainder hde
  have hcast (m : ℕ) : E (m : ZMod (d * e)) = ((m : ZMod d), (m : ZMod e)) := by
    rw [map_natCast]
    rfl
  have hcnt : #{m ∈ range (d * e) | Q m} = cnt h d := by
    rw [card_zmod_roots, Fintype.card_subtype]
    refine Finset.card_bij (fun (m : ℕ) _ => -(m : ZMod d)) ?_ ?_ ?_
    · intro m hm
      simp only [mem_filter, mem_range] at hm
      exact mem_filter.mpr ⟨mem_univ _, hm.2.1⟩
    · intro a ha b hb hab
      obtain ⟨haI, haQ⟩ := mem_filter.mp ha
      obtain ⟨hbI, hbQ⟩ := mem_filter.mp hb
      have hab' : (a : ZMod d) = (b : ZMod d) := neg_injective hab
      have heq : E (a : ZMod (d * e)) = E (b : ZMod (d * e)) := by
        rw [hcast, hcast]
        apply Prod.ext hab'
        exact add_right_cancel (haQ.2.trans hbQ.2.symm)
      have hz := congrArg ZMod.val (E.injective heq)
      simpa [ZMod.val_cast_of_lt (mem_range.mp haI),
        ZMod.val_cast_of_lt (mem_range.mp hbI)] using hz
    · intro z hz
      have hzroot := (mem_filter.mp hz).2
      let y := E.symm (-z, -(k : ZMod e))
      have hy : E (y.val : ZMod (d * e)) = (-z, -(k : ZMod e)) := by
        rw [ZMod.natCast_zmod_val]
        exact E.apply_symm_apply _
      rw [hcast] at hy
      obtain ⟨hy1, hy2⟩ := Prod.ext_iff.mp hy
      dsimp only at hy1 hy2
      refine ⟨y.val, mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt y), ?_⟩, ?_⟩
      · change (-(y.val : ZMod d)) * ((h : ZMod d) - (-(y.val : ZMod d))) = 0 ∧ (y.val : ZMod e) + k = 0
        constructor
        · simpa only [hy1, neg_neg] using hzroot
        · rw [hy2]
          simp
      · rw [hy1]
        simp
  have hdiv (m : ℕ) : d ∣ m * (m + h) ↔ (-(m : ZMod d)) * ((h : ZMod d) - (-(m : ZMod d))) = 0 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    constructor
    · intro hx
      linear_combination (-1 : ZMod d) * hx
    · intro hx
      linear_combination (-1 : ZMod d) * hx
  have hhigh (m : ℕ) : e ∣ m + k ↔ (m : ZMod e) + k = 0 := by
    simpa only [Nat.cast_add] using (ZMod.natCast_eq_zero_iff (m + k) e).symm
  have heq : #{m ∈ range N | d ∣ m * (m + h) ∧ e ∣ m + k} = #{m ∈ range N | Q m} := by
    congr 1
    apply filter_congr
    intro m hm
    change (d ∣ m * (m + h) ∧ e ∣ m + k) ↔
      ((-(m : ZMod d)) * ((h : ZMod d) - (-(m : ZMod d))) = 0 ∧ (m : ZMod e) + k = 0)
    rw [← hdiv m, ← hhigh m]
  rw [heq, ← hcnt]
  simpa only [Nat.cast_mul] using count_periodic_approx Q (Nat.mul_pos hd he) hperiod N

end
end LeanLab.Ricci1937
