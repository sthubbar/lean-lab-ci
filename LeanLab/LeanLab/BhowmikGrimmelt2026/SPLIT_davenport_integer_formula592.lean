/-
Davenport chapter 19, second edition, pages 117 and 118.
The sharp integer formula is kept separate from its elementary zero sum estimates.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.RouteCount508
import LeanLab.BhowmikGrimmelt2026.DavenportLeaves636

namespace LeanLab.BhowmikGrimmelt2026

/-- LEAF: Davenport second edition page 117 displays 4 and 6 and page 118 formula for b.
The half weighted integer character sum plus the strict height zero sum minus the low
reciprocal sum has the displayed uniform residual. No hypothesis T at most n is used.
This is the cited character contour and regularized constant input. -/
theorem davenport_integer_half_formula592 :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      ∀ n : ℕ, 2 ≤ n →
      ‖((∑ m ∈ Finset.range n,
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
          (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) +
        (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
          (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ‖ ≤
        D * ((n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 +
          Real.log q + Real.log n) := by
  exact Davenport636.formula636

/-- CONDITIONAL on davenport_integer_half_formula592.
Davenport page 117: the proved half weight endpoint bound converts the cited half
weighted formula to the sharp integer formula. The statement is unchanged. -/
theorem davenport_integer_formula592 :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      ∀ n : ℕ, 2 ≤ n →
      ‖(∑ m ∈ Finset.range (n + 1),
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
        (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
          (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ‖ ≤
        D * ((n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 +
          Real.log q + Real.log n) := by
  obtain ⟨D, hD, hhalf⟩ := davenport_integer_half_formula592
  refine ⟨D + 1, by linarith, ?_⟩
  intro q _ χ hprim hχ T hT Z hzeros n hn
  let P : ℂ := ∑ m ∈ Finset.range (n + 1),
    (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)
  let P₀ : ℂ := (∑ m ∈ Finset.range n,
    (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
    (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)
  let E : ℝ := (n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 + Real.log q + Real.log n
  have hendpoint : ‖P - P₀‖ ≤ Real.log n / 2 := sharp_half_weight_error541 χ n
  have hf := hhalf q χ hprim hχ T hT Z hzeros n hn
  change ‖P₀ + (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
    (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
    ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ‖ ≤ D * E at hf
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hT0 : 0 < T := by linarith
  have hbudget : Real.log n ≤ E := by
    have hnonneg : 0 ≤ (n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 := by positivity
    dsimp [E]
    linarith
  change ‖P + (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
    (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
    ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ‖ ≤ (D + 1) * E
  have heq : P + (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
      (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
      (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ) =
      (P - P₀) + (P₀ + (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
      (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
      (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ)) := by ring
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add hendpoint hf).trans (by nlinarith))

end LeanLab.BhowmikGrimmelt2026
