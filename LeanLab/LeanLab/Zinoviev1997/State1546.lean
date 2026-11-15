/-
AI wrote this Lean code. Codex task575, 2026-11-15.
Prerequisites moved verbatim to Decomp575a for the acyclic supply split.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.Decomp575a

namespace LeanLab.Zinoviev1997.State1546
open Complex MeasureTheory

/-- LEAF. The absolute error form of Proposition 1.4, pp. 339 to 341.
The missing inputs are character orthogonality with explicit psi errors, Abel summation,
and the Schoenfeld 1976 estimates of reference 4 for the cases q = 1 and q = 2.
The modulus range must be checked throughout the integral, not only at its upper endpoint. -/
theorem prop14_error_bound (hG : LeanLab.DERZ1997.GRH) {q l : ℕ}
    (hq : 1 ≤ q) (hl : Nat.Coprime l q) {x : ℝ} (hx : 10 ^ 9 ≤ x)
    (hqx : (q : ℝ) ≤ x ^ (0.37 : ℝ)) :
    |(piMod x q l : ℝ) - zinLi x / (Nat.totient q : ℝ)| ≤
      1.3 * Real.sqrt x * Real.log x + 10 ^ 8 := by
  sorry

/-- LEAF. Unit U-1546. Proposition 1.4, p. 339: under GRH, for `q ≥ 1`, `(l, q) = 1`,
`x ≥ 10⁹` and `q ≤ x^0.37`, there are `|θ₁| ≤ 1`, `|θ₂| ≤ 1` with
`π(x; q, l) = Li(x)/φ(q) + 1.3 θ₁ √x ln x + θ₂ 10⁸`. -/
theorem prop14 (hG : LeanLab.DERZ1997.GRH) {q l : ℕ} (hq : 1 ≤ q) (hl : Nat.Coprime l q)
    {x : ℝ} (hx : 10 ^ 9 ≤ x) (hqx : (q : ℝ) ≤ x ^ (0.37 : ℝ)) :
    ∃ θ₁ θ₂ : ℝ, |θ₁| ≤ 1 ∧ |θ₂| ≤ 1 ∧
      (piMod x q l : ℝ) = zinLi x / (Nat.totient q : ℝ)
        + 1.3 * θ₁ * Real.sqrt x * Real.log x + θ₂ * 10 ^ 8 := by
  let E : ℝ := 1.3 * Real.sqrt x * Real.log x
  let F : ℝ := 10 ^ 8
  let r : ℝ := (piMod x q l : ℝ) - zinLi x / (Nat.totient q : ℝ)
  let θ : ℝ := r / (E + F)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hEF : 0 < E + F := by dsimp [E, F]; positivity
  have hr : |r| ≤ E + F := prop14_error_bound hG hq hl hx hqx
  have hθ : |θ| ≤ 1 := by
    dsimp [θ]
    rw [abs_div, abs_of_pos hEF, div_le_one hEF]
    exact hr
  have he : r = E*θ + F*θ := by
    dsimp [θ]
    field_simp [hEF.ne']
    <;> ring
  refine ⟨θ, θ, hθ, hθ, ?_⟩
  calc
    (piMod x q l : ℝ) = zinLi x / (Nat.totient q : ℝ) + r := by dsimp [r]; ring
    _ = zinLi x / (Nat.totient q : ℝ) + (E*θ + F*θ) := by rw [← he]
    _ = _ := by dsimp [E, F]; ring

end LeanLab.Zinoviev1997.State1546
