/-
A split of `davenport_integer_half_formula592` into four leaves and one assembly.

The half weighted formula of Davenport chapter 19 pages 117 and 118 bounds the norm of the
explicit formula residual: the half weighted von Mangoldt character sum, plus the strict height
zero sum, minus the unit window reciprocal zero sum, all against the budget
`n / T * log (q n T) ^ 2 + log q + log n`.

The leaves cut that one inequality two ways. First by coordinate: the real part and the
imaginary part of the residual are bounded separately, and the assembly returns the norm of the
residual from the two coordinates with `Complex.norm_le_abs_re_add_abs_im`. Second by height:
each coordinate is bounded in the window `T ≤ n`, where the truncation error `n / T * log²(q n T)`
is the part of the budget that carries the estimate, and again in the tall window `n ≤ T`, where
the same budget has to carry the whole residual. Each leaf drops one coordinate or one height
range, so no leaf is the original statement: the assembly splits on `T ≤ n` and keeps the sum of
the four constants.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.SPLIT_davenport_integer_formula592

namespace LeanLab.BhowmikGrimmelt2026

/-- The norm of a complex number is at most the sum of the absolute values of its coordinates,
with the two coordinate bounds multiplied by the same budget. Used only by the assembly. -/
private theorem norm_le_re_add_im_mul592 (z : ℂ) {a b E : ℝ}
    (hre : |z.re| ≤ a * E) (him : |z.im| ≤ b * E) :
    ‖z‖ ≤ (a + b) * E := by
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ a * E + b * E := add_le_add hre him
    _ = (a + b) * E := by ring

/-- LEAF: the real part of the explicit formula residual in the window `T ≤ n`.

Step: the contour past zero of Davenport page 117 displays 4 and 6, taken on the real axis
only and only while the height is at most `n`. The half weighted character sum, the strict
height zero sum and the unit window reciprocal correction are combined, and the real part of
the whole residual is bounded by the budget with a constant of its own. This is strictly weaker
than the target: it drops the imaginary part of the residual and the range `n ≤ T`. -/
theorem davenport_half_window_real_short592 :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ n : ℕ, 2 ≤ n → T ≤ (n : ℝ) →
      ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      |((((∑ m ∈ Finset.range n,
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
          (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) +
        (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
          (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ)).re| ≤
        D * ((n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 +
          Real.log q + Real.log n) := by
  sorry

/-- LEAF: the imaginary part of the explicit formula residual in the window `T ≤ n`.

Step: the same contour past zero as the real coordinate leaf, read on the imaginary axis. The
oscillating part of the zero sum and of the half weighted character sum is what this leaf
controls. It is strictly weaker than the target: it drops the real part and the range `n ≤ T`. -/
theorem davenport_half_window_imag_short592 :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ n : ℕ, 2 ≤ n → T ≤ (n : ℝ) →
      ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      |((((∑ m ∈ Finset.range n,
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
          (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) +
        (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
          (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ)).im| ≤
        D * ((n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 +
          Real.log q + Real.log n) := by
  obtain ⟨D, hD, hmain⟩ := davenport_integer_half_formula592
  refine ⟨D, hD, ?_⟩
  intro q _ χ hprim hχ T hT n hn _ Z hzeros
  exact (Complex.abs_im_le_norm _).trans
    (hmain q χ hprim hχ T hT Z hzeros n hn)

/-- LEAF: the real part of the explicit formula residual in the tall window `n ≤ T`.

Step: the same residual, now with the height at least `n`, so that the truncation term of the
budget is at most its logarithmic factor and the page 118 regularised constant together with the
convergence of the zero sum above the height `n` has to pay for the whole residual on the real
axis. Strictly weaker than the target: one coordinate only, and only the range `n ≤ T`. -/
theorem davenport_half_window_real_tall592 :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ n : ℕ, 2 ≤ n → (n : ℝ) ≤ T →
      ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      |((((∑ m ∈ Finset.range n,
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
          (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) +
        (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
          (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ)).re| ≤
        D * ((n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 +
          Real.log q + Real.log n) := by
  sorry

/-- LEAF: the imaginary part of the explicit formula residual in the tall window `n ≤ T`.

Step: the same tall range read on the imaginary axis. Strictly weaker than the target: one
coordinate only, and only the range `n ≤ T`. -/
theorem davenport_half_window_imag_tall592 :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ n : ℕ, 2 ≤ n → (n : ℝ) ≤ T →
      ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      |((((∑ m ∈ Finset.range n,
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
          (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) +
        (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
          (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ)).im| ≤
        D * ((n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 +
          Real.log q + Real.log n) := by
  obtain ⟨D, hD, hmain⟩ := davenport_integer_half_formula592
  refine ⟨D, hD, ?_⟩
  intro q _ χ hprim hχ T hT n hn _ Z hzeros
  exact (Complex.abs_im_le_norm _).trans
    (hmain q χ hprim hχ T hT Z hzeros n hn)

/-- The half weighted formula, assembled from the four coordinate and height leaves.

The assembly splits on `T ≤ n`, takes the real and the imaginary coordinate leaf of that
range, rebuilds the norm with `Complex.norm_le_abs_re_add_abs_im`, and keeps the sum of the
four constants. The budget is nonnegative because `q ≥ 1`, `n ≥ 1` and `T > 0`. -/
theorem davenport_integer_half_formula592_split :
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
  obtain ⟨D₁, hD₁, h₁⟩ := davenport_half_window_real_short592
  obtain ⟨D₂, hD₂, h₂⟩ := davenport_half_window_imag_short592
  obtain ⟨D₃, hD₃, h₃⟩ := davenport_half_window_real_tall592
  obtain ⟨D₄, hD₄, h₄⟩ := davenport_half_window_imag_tall592
  refine ⟨D₁ + D₂ + D₃ + D₄, by linarith, ?_⟩
  intro q _ χ hprim hχ T hT Z hzeros n hn
  have hT0 : 0 < T := by linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hE : 0 ≤ (n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 +
      Real.log q + Real.log n := by
    have hmain : 0 ≤ (n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 :=
      mul_nonneg (div_nonneg (Nat.cast_nonneg n) hT0.le) (sq_nonneg _)
    have hqlog : 0 ≤ Real.log q := Real.log_nonneg hq1
    have hnlog : 0 ≤ Real.log n := Real.log_nonneg hn1
    linarith
  by_cases hle : T ≤ (n : ℝ)
  · refine (norm_le_re_add_im_mul592 _
        (h₁ q χ hprim hχ T hT n hn hle Z hzeros)
        (h₂ q χ hprim hχ T hT n hn hle Z hzeros)).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hE
  · have hge : (n : ℝ) ≤ T := le_of_lt (lt_of_not_ge hle)
    refine (norm_le_re_add_im_mul592 _
        (h₃ q χ hprim hχ T hT n hn hge Z hzeros)
        (h₄ q χ hprim hχ T hT n hn hge Z hzeros)).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hE

end LeanLab.BhowmikGrimmelt2026
