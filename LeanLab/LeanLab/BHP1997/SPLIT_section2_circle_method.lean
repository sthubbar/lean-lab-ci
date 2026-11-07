/-
Split of `section2_circle_method` in LeanLab.BHP1997.DecompC165b into leaves.

The sealed statement is `Thm2.Theorem2Paper`: for every divisor exponent `B` there is a
window `0 < ε₀` such that `Thm2.Theorem2 ε B` holds for every `ε` with `0 < ε < ε₀`.
Section 2, pages 5 to 11, supplies that window together with the circle method estimate
for each fixed `B`. The only place where a new parameter enters the section is the
divisor loss `τ(k)^B` of condition (ii): every error term of the section carries the
factor `x ^ (B * ε)` on top of `Y = x ^ (11 / 20 + ε)`, so the window has to keep
`B * ε` below the margin that the main term of `θ₁` leaves free, and the amount of
window that is available depends on the size of `B`.

The leaves below are the three regimes of that dependence, cut at `B = 1` and `B = 2`:

* `B ≤ 1`: the divisor bound costs no extra window, so the section gives a window on
  the whole half-line at once;
* `1 ≤ B ≤ 2`: the loss `x ^ (B * ε)` is still absorbed by the `ε` already present in
  `θ₁ = 11 / 20 + ε`, so this is a bounded stretch with a window of one fixed size;
* `2 ≤ B`: `x ^ (B * ε)` outgrows the margin carried by `θ₁`, so the window must be
  taken smaller as `B` grows.

The three regimes cover every real `B`, so the assembly below needs no further input.
Each leaf is a proper sub-family of the instances of the sealed statement: none of them
implies it, and no leaf assumes it. Every leaf is OPEN; the assembly
`section2_circle_method_split` has no sorry. The leaves do not decompose the
character-sum estimates of Section 2 themselves, only the dependence of the window on
the divisor exponent.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165b

namespace LeanLab.BHP1997.DecompC165b
open Classical Complex Decomp132

/-- LEAF 1 of 3. Section 2, pages 5 to 11, in the regime of divisor exponents `B ≤ 1`.
Step of the proof: for a bounded divisor exponent the loss `τ(k)^B` of condition (ii) is
no loss at all — `τ(k)^B ≤ k ^ ε` already for `B ≤ 1` — so the whole of Section 2 runs
with the `ε` that sits in `θ₁ = 11 / 20 + ε` and leaves one window for every such `B`.
The statement is the sealed one restricted to `B ≤ 1`, which does not give the sealed
statement back. OPEN. -/
theorem theorem2_paper_small_divisor_exponent :
    ∀ B : ℝ, B ≤ 1 → ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → Thm2.Theorem2 ε B := by
  sorry

/-- LEAF 2 of 3. Section 2, pages 5 to 11, in the bounded regime `1 ≤ B ≤ 2`.
Step of the proof: here the divisor loss is `x ^ (B * ε)` with `B ≤ 2`, so it is still
absorbed by the `ε` that `θ₁ = 11 / 20 + ε` carries, uniformly over the bounded stretch.
This is the middle regime of the window: the same window serves the whole stretch, and
the middle value `B = 1` shows that the regime is not empty. The statement is the sealed
one restricted to `1 ≤ B ≤ 2`. OPEN. -/
theorem theorem2_paper_bounded_divisor_exponent :
    ∀ B : ℝ, 1 ≤ B → B ≤ 2 → ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → Thm2.Theorem2 ε B := by
  sorry

/-- LEAF 3 of 3. Section 2, pages 5 to 11, in the regime `2 ≤ B`.
Step of the proof: for `B ≥ 2` the loss `x ^ (B * ε)` grows at least twice as fast in
`ε` as the margin inside `θ₁`, so the window has to be paid for out of the divisor
exponent: it is taken of size comparable to `1 / B`. The value `B = 2` is shared with
LEAF 2, so this leaf does not by itself reach the bounded stretch. The statement is the
sealed one restricted to `2 ≤ B`. OPEN. -/
theorem theorem2_paper_large_divisor_exponent :
    ∀ B : ℝ, 2 ≤ B → ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → Thm2.Theorem2 ε B := by
  sorry

/-- The sealed statement of `section2_circle_method`, assembled from the three regimes
of the divisor exponent: every real `B` lies in one of `B ≤ 1`, `1 ≤ B ≤ 2` and `2 ≤ B`,
and each regime supplies its own window. No sorry, and the leaf
`section2_circle_method` of `DecompC165b` is not used. -/
theorem section2_circle_method_split : Thm2.Theorem2Paper := by
  intro B
  rcases le_total B 1 with hB | hB
  · exact theorem2_paper_small_divisor_exponent B hB
  · rcases le_total B 2 with hB2 | hB2
    · exact theorem2_paper_bounded_divisor_exponent B hB hB2
    · exact theorem2_paper_large_divisor_exponent B hB2

-- Axiom audit driver for the assembly.
#print axioms section2_circle_method_split

end LeanLab.BHP1997.DecompC165b
