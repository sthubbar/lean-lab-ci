import LeanLab.HelfgottMajor.Decomp454c
import LeanLab.HelfgottMajor.Decomp269b
import LeanLab.HelfgottMajor.ZeroCount1623

/-!
Finite unit shells and conditional convergence for the actual high zero mass.
Source P0014 page 38 display 4.26 and page 41 displays 4.33 to 4.35.
The sharp integral bound remains OPEN in the sealed Decomp269c file.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp454d
open Real Decomp269a Decomp269b ZeroCount1623

/-- The high zero index in P0014 Lemma 4.5 on pages 40 and 41.
Multiplicity is retained in the weights rather than in the index.
-/
abbrev TailZero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :=
  {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}

/-- Every unit shell of actual high zeros is finite without a zero count input.
This is the local finiteness prerequisite for the use of display 4.26 on page 38.
-/
theorem tail_shell_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (n : ℕ) :
    {ρ : TailZero χ T | ⌊|ρ.val.im|⌋₊ = n}.Finite := by
  apply ((stripZeros_finite χ ((n : ℝ) + 1)).preimage
    (f := Subtype.val) Subtype.val_injective.injOn).subset
  intro ρ hρ
  refine ⟨ρ.property.1, ρ.property.2.1, ρ.property.2.2.1, ?_⟩
  have h := Nat.lt_floor_add_one |ρ.val.im|
  rw [hρ] at h
  exact h.le

/-- Exponential multiplicity weights are summable under a polynomial shell count.
CONDITIONAL ON hcount, a weaker convergence input than the density bound in display 4.35.
Source P0014 pages 38 and 41, displays 4.26 and 4.33.
-/
theorem tail_exp_summable_of_shell_count {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T C a : ℝ) (ha : 0 < a)
    (hcount : ∀ n : ℕ,
      (∑' ρ : {ρ : TailZero χ T // ⌊|ρ.val.im|⌋₊ = n},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val.val : ℝ)) ≤
          C * ((n : ℝ) + 1) ^ 2) :
    Summable (fun ρ : TailZero χ T =>
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        exp (-a * |ρ.val.im|)) := by
  exact Decomp454c.summable_exp_real_of_shell_count
    (fun ρ : TailZero χ T => |ρ.val.im|)
    (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ))
    C a ha (fun _ => Nat.cast_nonneg _) (fun _ => abs_nonneg _)
    (tail_shell_finite χ T) hcount

/-- The convergence half of the sealed high tail leaf follows from coarse count and decay.
CONDITIONAL ON hcount and hdecay. The precise density inequality is a separate obligation.
Source P0014 page 41, displays 4.33 to 4.35.
-/
theorem tail_mass_summable_of_shell_count {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T C a B : ℝ) (ha : 0 < a)
    (hcount : ∀ n : ℕ,
      (∑' ρ : {ρ : TailZero χ T // ⌊|ρ.val.im|⌋₊ = n},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val.val : ℝ)) ≤
          C * ((n : ℝ) + 1) ^ 2)
    (hdecay : ∀ ρ : TailZero χ T,
      ‖gaussianMellin δ ρ.val‖ ≤ B * exp (-a * |ρ.val.im|)) :
    Summable (fun ρ : TailZero χ T => mellinMassTerm χ δ ρ.val) := by
  apply ((tail_exp_summable_of_shell_count χ T C a ha hcount).mul_left B).of_norm_bounded
  intro ρ
  rw [Real.norm_of_nonneg (by unfold mellinMassTerm; positivity)]
  have h := mul_le_mul_of_nonneg_left (hdecay ρ)
    (Nat.cast_nonneg (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val) :
      (0 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ))
  dsimp only [mellinMassTerm]
  nlinarith [h]

end LeanLab.HelfgottMajor.Decomp454d
