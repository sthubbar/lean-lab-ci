/-
AI wrote this Lean code for CODEX task294.
P0037 page 207, the shifted prime sieve, and Section 5.1 page 211.
These lemmas connect checked bitmap windows to the sealed certificate format.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Shift

namespace LeanLab.DtRS1998.Certificate294

open LeanLab.DtRS1998 LeanLab.Verifications.Top50.Bits

/-- P0037 page 207. An accepted shifted bitmap supplies a prime difference.
This is CONDITIONAL ON the supplied bitmap equality. -/
theorem offset_window {x0 x1 lo W : ℕ} {Ds : List ℕ}
    (h2 : 2 ≤ lo) (hW : lo + W ≤ B2)
    (hlo : ∀ d ∈ Ds, lo ≤ x0 + d)
    (h : wem 0 0 (x1 - x0) &&& gmR (wpm2 lo W) (Ds.map (fun d => x0 + d - lo)) =
      wem 0 0 (x1 - x0))
    {x : ℕ} (hx0 : x0 ≤ x) (hx1 : x ≤ x1) (he : 2 ∣ x - x0) :
    ∃ d ∈ Ds, (x + d).Prime := by
  have hbit := testBit_wem (lo := 0) (A := 0) (B := x1 - x0)
    (n := x - x0) le_rfl (Nat.zero_le _) (by omega) (by simpa using he)
  rw [Nat.sub_zero, ← h, Nat.testBit_and, Bool.and_eq_true] at hbit
  obtain ⟨s, hs, hp⟩ := of_gmR _ _ _ hbit.2
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hs
  have hprime := prime_of_wpm2 h2 hW hp
  have hl := hlo d hd
  refine ⟨d, hd, ?_⟩
  convert hprime using 1 <;> omega

/-- P0037 page 207. Prime differences for every even offset give the
Boolean certificate for the corresponding large prime candidates.
This is CONDITIONAL ON the supplied offset witnesses. -/
theorem offsets_certificate {B L : ℕ} {Ds : List ℕ}
    (hD : ∀ d ∈ Ds, d ≤ B)
    (hcover : ∀ x, x ≤ L → 2 ∣ x → ∃ d ∈ Ds, (x + d).Prime) :
    (List.range (L / 2 + 1)).all (fun j =>
      (Ds.map (fun d => B - d)).any (fun q =>
        decide (q ≤ B + 2 * j ∧ (B + 2 * j - q).Prime))) = true := by
  apply List.all_eq_true.mpr
  intro j hj
  have hjL := List.mem_range.mp hj
  obtain ⟨d, hd, hp⟩ := hcover (2 * j) (by omega) (dvd_mul_right 2 j)
  apply List.any_eq_true.mpr
  refine ⟨B - d, List.mem_map.mpr ⟨d, hd, rfl⟩, ?_⟩
  apply decide_eq_true
  have hdB := hD d hd
  constructor
  · omega
  · convert hp using 1 <;> omega

#print axioms offset_window
#print axioms offsets_certificate

end LeanLab.DtRS1998.Certificate294
