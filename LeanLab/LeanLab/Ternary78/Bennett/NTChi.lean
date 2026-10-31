import Mathlib

namespace LeanLab.Ternary78.Bennett
open Real

/-- Theorem 1.1 of Bennett, Martin, O'Bryant, Rechnitzer 2021, Math. Comp. 90,
"Counting zeros of Dirichlet L-functions", arXiv 2005.02989, page 2. CITED, not proved here.

`N q χ T` stands for the zero count `N(T, χ)`, the number of zeros `ρ = β + iγ` of `L(s, χ)`
with `0 < β < 1` and `|γ| ≤ T`, counted with multiplicity. Mathlib has no such count, so it
is a parameter: anything that uses this Prop is CONDITIONAL ON it, for the true zero count.
The paper's `q` is the conductor, so `χ` is primitive mod `q`. Only the case `ℓ > 1.567` is
stated; the paper's companion claim `N(T, χ) = 0` for `ℓ ≤ 1.567` is omitted.

Review 2026-10-22, Claude: replaced `def NTChi := sorry` by the parameter `N`, added
`χ.IsPrimitive`, dropped the unused `x₀`. -/
def BennettThm1_1 (N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ) (Q : ℕ) : Prop :=
  ∀ (q : ℕ) [NeZero q], q ≤ Q → 1 < q → ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
  ∀ (T : ℝ), 5 / 7 ≤ T →
    let l := Real.log (q * (T + 2) / (2 * Real.pi));
    1.567 < l →
    |(N q χ T : ℝ) - (T / Real.pi * Real.log (q * T / (2 * Real.pi * Real.exp 1)) - (χ (-1) : ℂ).re / 4)|
    ≤ 0.22737 * l + 2 * Real.log (1 + l) - 0.5

end LeanLab.Ternary78.Bennett
