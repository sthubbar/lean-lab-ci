import LeanLab.LanguascoPintzZaccagnini2007.IwaniecCells1122

/-!
A split of the leaf `iwaniec_display14_15_1122` of `SPLIT_iwaniec_no_zero_open_strip481_steps`
into its two printed displays, page 102 of H. Iwaniec, On zeros of Dirichlet's L series,
Invent. Math. 23, 1974, 97 to 104, read on the page image of `papers/Iwaniec1974.pdf`:
* display (14), the 3-4-1 inequality for log derivatives at `σ > 1`;
* display (15), the lower bound for `Re L'/L (σ, χ₀)`.
The assembly in `SPLIT_iwaniec_no_zero_open_strip481_steps` is real algebra.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- LEAF: Iwaniec 1974 page 102, display (14) of the proof of Lemma 11.
Class: MEDIUM.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 102, display (14):
for `σ > 1`,
`3 Re L'/L (σ, χ₀) + 4 Re L'/L (σ + it, χ) + Re L'/L (σ + 2it, χ²) ≤ 0`,
from `-L'/L (s, χ) = Σ Λ(n) χ(n) n^(-s)` and `3 + 4 cos φ + cos 2φ ≥ 0`. Here `χ₀` is the
principal character `1` modulo `q`. -/
theorem iwaniec_display14_1122 (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (γ σ : ℝ) (hσ : 1 < σ) :
    3 * (logDeriv (Lfun481 (1 : DirichletCharacter ℂ q)) (σ : ℂ)).re +
      4 * (logDeriv (Lfun481 χ) ((σ : ℂ) + (γ : ℂ) * Complex.I)).re +
      (logDeriv (Lfun481 (χ ^ 2)) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re ≤ 0 := by
  sorry

/-- LEAF: Iwaniec 1974 page 102, display (15) of the proof of Lemma 11.
Class: MEDIUM.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 102, display (15):
`Re L'/L (σ, χ₀) ≥ -1/(σ - 1) - 2 log 5l` for `σ > 1`, from `|ζ'/ζ (σ) + 1/(σ - 1)| < 3` and
`|L'/L (σ, χ₀) - ζ'/ζ (σ)| ≤ Σ_{p ∣ q} log p / (p^σ - 1) < 2 log log 3d`. Here `l` is taken at
any height `γ`, since `log 3d ≤ l` for every `γ`. -/
theorem iwaniec_display15_1122 (q : ℕ) (hq : 3 ≤ q) (γ l σ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3))) (hσ : 1 < σ) :
    -(1 / (σ - 1)) - 2 * Real.log (5 * l) ≤
      (logDeriv (Lfun481 (1 : DirichletCharacter ℂ q)) (σ : ℂ)).re := by
  sorry

end

end LeanLab.LPZ2007
