import LeanLab.LiuWang2002.Cover368

/-!
Shared power computations in bounded primorial certificates.
Source Schoenfeld page 356, display 5.1 star, derived proof data.
The width is evaluated before its two powers are used.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task368

/-- Evaluate the interval width before computing its powers. This
retains the same composite witnesses and both exact ratio bounds.
Derived executable data for page 356, display 5.1 star. -/
def fastCheckpointCheck (S n r : ℕ) : List (List ℕ × ℕ) → Bool
  | [] => true
  | (ds, s) :: rest =>
    match ds.length with
    | 0 => coverCheck n ds &&
      decide (r * coverProduct n ds * 25 < S * 68) &&
      decide (r * coverProduct n ds * 25 ^ 0 ≤ s * 68 ^ 0) &&
      fastCheckpointCheck S n s rest
    | k + 1 => coverCheck n ds &&
      decide (r * coverProduct n ds * 25 < S * 68) &&
      decide (r * coverProduct n ds * 25 ^ (k + 1) ≤ s * 68 ^ (k + 1)) &&
      fastCheckpointCheck S (n + (k + 1)) s rest

/-- The evaluated width implementation has the original one step
ratio predicate. Derived identity for page 356, display 5.1 star. -/
theorem fastCheckpointCheck_step (S n r s : ℕ) (ds : List ℕ)
    (rest : List (List ℕ × ℕ)) :
    fastCheckpointCheck S n r ((ds, s) :: rest) =
      (coverCheck n ds &&
      decide (r * coverProduct n ds * 25 < S * 68) &&
      decide (r * coverProduct n ds * 25 ^ ds.length ≤ s * 68 ^ ds.length) &&
      fastCheckpointCheck S (n + ds.length) s rest) := by
  cases hl : ds.length <;> simp only [fastCheckpointCheck, hl, Nat.add_zero]

/-- Both Boolean checkers are equal for every list, scale and initial
state. No new trust input is introduced by the evaluation order.
Derived identity for page 356, display 5.1 star. -/
theorem fastCheckpointCheck_eq (cs : List (List ℕ × ℕ)) (S n r : ℕ) :
    fastCheckpointCheck S n r cs = coverCheckpointCheck S n r cs := by
  induction cs generalizing n r with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨ds, s⟩ := c
    rw [fastCheckpointCheck_step, coverCheckpointCheck_step, ih]

end LeanLab.LiuWang2002.Task368
#print axioms LeanLab.LiuWang2002.Task368.fastCheckpointCheck_step
#print axioms LeanLab.LiuWang2002.Task368.fastCheckpointCheck_eq
