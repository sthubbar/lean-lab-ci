/-
AI wrote this Lean code for CODEX task03.
P0074, page 13, the error after the Ramanujan character expansion.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.RamanujanSharp

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The Ramanujan test has window error at most φ times sqrt φ times E. -/
theorem ram_window_error {q : ℕ} [NeZero q] {W : Finset ℤ} {ω : ℤ → ℝ} {M E : ℝ}
    (hE : 0 ≤ E) (hχ : CharacterEquidist W q ω M E) (n : ℤ)
    (hrough : ∀ m ∈ W, Int.gcd m q ≠ 1 → ω m = 0) :
    |(∑ m ∈ W, ω m * ram q (n - m)) -
      M / q.totient * (ArithmeticFunction.moebius q : ℝ) * ram q n| ≤
        (q.totient : ℝ) * Real.sqrt q.totient * E := by
  classical
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  let f : (ZMod q)ˣ → ℂ := fun u => (ram q (n - (u : ZMod q).val) : ℂ) / q.totient
  have hf : ∀ u, ‖f u‖ ≤ 1 := by
    intro u
    calc
      ‖f u‖ = |ram q (n - (u : ZMod q).val)| / (q.totient : ℝ) := by
        simp [f, norm_div, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1 := (div_le_one hφ).mpr (abs_ram_le q _)
  have ht := unitMass_test_bound hE hχ f hf
  have hs1 : (∑ u : (ZMod q)ˣ, unitMass W ω u * f u) =
      ((∑ m ∈ W, ω m * ram q (n - m) : ℝ) : ℂ) / q.totient := by
    dsimp only [f]
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, unitMass_ram_sum W ω n hrough]
  have hs2 : (∑ u : (ZMod q)ˣ, f u) =
      (((ArithmeticFunction.moebius q : ℝ) * ram q n : ℝ) : ℂ) / q.totient := by
    dsimp only [f]
    rw [← Finset.sum_div, ← Complex.ofReal_sum, sum_units_ram]
  rw [hs1, hs2] at ht
  have heq : ((∑ m ∈ W, ω m * ram q (n - m) : ℝ) : ℂ) / q.totient -
      (M : ℂ) / q.totient *
        ((((ArithmeticFunction.moebius q : ℝ) * ram q n : ℝ) : ℂ) / q.totient) =
      ((((∑ m ∈ W, ω m * ram q (n - m)) -
        M / q.totient * (ArithmeticFunction.moebius q : ℝ) * ram q n) /
          (q.totient : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hφ] at ht
  have h := (div_le_iff₀ hφ).mp ht
  nlinarith only [h]

/-- Including the Möbius and totient coefficient leaves error at most sqrt q times E. -/
theorem ram_term_error {q : ℕ} [NeZero q] {W : Finset ℤ} {ω : ℤ → ℝ} {M E : ℝ}
    (hE : 0 ≤ E) (hχ : CharacterEquidist W q ω M E) (n : ℤ)
    (hrough : ∀ m ∈ W, Int.gcd m q ≠ 1 → ω m = 0) :
    |(ArithmeticFunction.moebius q : ℝ) / q.totient *
        (∑ m ∈ W, ω m * ram q (n - m)) -
      M * ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * ram q n)| ≤
        Real.sqrt q * E := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hμ : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
  have hd : (ArithmeticFunction.moebius q : ℝ) / q.totient *
        (∑ m ∈ W, ω m * ram q (n - m)) -
      M * ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * ram q n) =
      (ArithmeticFunction.moebius q : ℝ) / q.totient *
        ((∑ m ∈ W, ω m * ram q (n - m)) -
          M / q.totient * (ArithmeticFunction.moebius q : ℝ) * ram q n) := by ring
  rw [hd, abs_mul, abs_div, abs_of_pos hφ]
  calc
    _ ≤ (1 / (q.totient : ℝ)) * ((q.totient : ℝ) * Real.sqrt q.totient * E) :=
      mul_le_mul (div_le_div_of_nonneg_right hμ hφ.le)
        (ram_window_error hE hχ n hrough) (abs_nonneg _) (by positivity)
    _ = Real.sqrt q.totient * E := by field_simp
    _ ≤ Real.sqrt q * E := mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le q)) hE

#print axioms ram_window_error
#print axioms ram_term_error
end LeanLab.Grimmelt2019.MainTerm
