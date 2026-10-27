/-
P0038 Shao 2012, Corollary 1.5 for every odd prime modulus, by Cauchy-Davenport.
AI-written Lean code, Claude, 2026-10-16, run 20261016T2303Z-22954, unit U-0091.
-/
import LeanLab.DensityGoldbach.Statements

open Finset
open scoped Pointwise

namespace LeanLab.DensityGoldbach

/-- **Corollary 1.5 for an odd prime `p`**: `A ⊆ Z_p^*` with `|A| > 5/8 (p - 1)` has
`A + A + A = Z_p`. Cauchy-Davenport gives `|A + A + A| ≥ min p (3|A| - 2) = p`. -/
theorem cor15_prime (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) : Cor15 p := by
  have hp : p.Prime := Fact.out
  intro A _ hcard x
  rw [Nat.totient_prime hp] at hcard
  have h1 : 1 ≤ p := hp.one_lt.le
  have h8 : 5 * p ≤ 8 * #A + 4 := by
    have : (5 : ℝ) / 8 * ((p - 1 : ℕ) : ℝ) < #A := hcard
    rw [Nat.cast_sub h1] at this
    have : (5 * p : ℝ) < 8 * #A + 5 := by push_cast at this ⊢; linarith
    have : 5 * p < 8 * #A + 5 := by exact_mod_cast this
    omega
  have hA : A.Nonempty := by
    rw [← card_pos]; omega
  have hAA : (A + A).Nonempty := hA.add hA
  have c1 := ZMod.cauchy_davenport hp hA hA
  have c2 := ZMod.cauchy_davenport hp hAA hA
  have hbig : p ≤ #(A + A + A) := by
    have : p ≤ #A + #A + #A - 2 := by omega
    rcases le_total p (#A + #A - 1) with h | h
    · rw [min_eq_left h] at c1
      have : min p (#(A + A) + #A - 1) = p := min_eq_left (by omega)
      omega
    · rw [min_eq_right h] at c1
      have : min p (#(A + A) + #A - 1) = p := min_eq_left (by omega)
      omega
  have huniv : A + A + A = univ := by
    apply eq_univ_of_card
    rw [ZMod.card]
    exact le_antisymm (by simpa [ZMod.card] using card_le_univ (A + A + A)) hbig
  have hx : x ∈ A + A + A := by rw [huniv]; exact mem_univ x
  obtain ⟨y, hy, c, hc, rfl⟩ := mem_add.1 hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hy
  exact ⟨a, ha, b, hb, c, hc, rfl⟩

end LeanLab.DensityGoldbach
