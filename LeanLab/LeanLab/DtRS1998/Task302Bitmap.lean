/-
AI wrote this Lean code for CODEX task302.
P0037 Section 5.2 page 212 and Table 2 page 214.
Active candidates may lie above the original interval base.
The block check is CONDITIONAL ON the supplied bitmap and list membership.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Certificate294

namespace LeanLab.DtRS1998.Task302.Bitmap

open LeanLab.Verifications.Top50.Bits

/-- A local bitmap certifies one block using members of a shared global list.
P0037 Section 5.2 page 212, derived finite sieve assembly.
CONDITIONAL ON the supplied bitmap and candidate membership. -/
theorem block_of_bitmap {B start count lo W : ℕ} (qs Ds : List ℕ)
    (h2 : 2 ≤ lo) (hW : lo + W ≤ B2)
    (hlo : ∀ d ∈ Ds, lo ≤ d)
    (hD : ∀ d ∈ Ds, d ≤ B + 2 * start ∧ B + 2 * start - d ∈ qs)
    (hcover : wem 0 0 (2 * (count - 1)) &&&
      gmR (wpm2 lo W) (Ds.map (fun d => d - lo)) = wem 0 0 (2 * (count - 1))) :
    (List.range count).all (fun t =>
      qs.any (fun q => decide
        (q ≤ B + 2 * (start + t) ∧ (B + 2 * (start + t) - q).Prime))) = true := by
  apply List.all_eq_true.mpr
  intro t ht
  have ht' := List.mem_range.mp ht
  have hbound : 2 * t ≤ 2 * (count - 1) := by omega
  obtain ⟨d, hd, hp⟩ := Certificate294.offset_window
    (x0 := 0) (x1 := 2 * (count - 1)) (Ds := Ds) h2 hW
    (fun d hd => by simpa using hlo d hd)
    (by simpa only [Nat.zero_add, Nat.sub_zero] using hcover)
    (x := 2 * t) (Nat.zero_le _) hbound (by simp)
  obtain ⟨hdB, hdqs⟩ := hD d hd
  apply List.any_eq_true.mpr
  refine ⟨B + 2 * start - d, hdqs, decide_eq_true ?_⟩
  constructor
  · omega
  · convert hp using 1 <;> omega

#print axioms block_of_bitmap

/-- The active candidate 7 is above base 6 and covers the block 12, 14.
P0037 Section 5.2 page 212, a nonempty local bitmap instance. -/
theorem bitmap_block_instance :
    (List.range 2).all (fun t =>
      ([3, 7] : List ℕ).any (fun q => decide
        (q ≤ 6 + 2 * (3 + t) ∧ (6 + 2 * (3 + t) - q).Prime))) = true := by
  apply block_of_bitmap (B := 6) (start := 3) (count := 2)
    (lo := 2) (W := 6) [3, 7] [5] (by decide) (by decide)
  · intro d hd
    rcases List.mem_singleton.mp hd with rfl
    decide
  · intro d hd
    rcases List.mem_singleton.mp hd with rfl
    decide
  · decide +kernel

#print axioms bitmap_block_instance

end LeanLab.DtRS1998.Task302.Bitmap
