/-
AI wrote this Lean code. Goldbach is open.
Source: Li 2024 v4, page 10, equations 19 to 21.
The reciprocal change of variables cancels the extra sieve integral.
This identity assumes a differential relation and does not prove a sieve input.
-/
import Mathlib

namespace LeanLab.Li2024.SieveIntegrals

open Real intervalIntegral

theorem reciprocal_sieve_identity {G g : ℝ → ℝ} {D k₀ k : ℝ}
    (hD : 0 < D) (hk₀ : 0 < k₀) (hk : k₀ ≤ k)
    (hG : ∀ s, 0 < s → HasDerivAt G (g (s - 1)) s)
    (hint : IntervalIntegrable (fun u => g (D / u - 1) / u ^ 2)
      MeasureTheory.volume (1 / k) (1 / k₀)) :
    (∫ u in (1 / k)..(1 / k₀), g (D / u - 1) / u ^ 2) =
      (G (k * D) - G (k₀ * D)) / D := by
  have hkpos : 0 < k := hk₀.trans_le hk
  have hab : 1 / k ≤ 1 / k₀ := one_div_le_one_div_of_le hk₀ hk
  have hderiv : ∀ u ∈ Set.uIcc (1 / k) (1 / k₀),
      HasDerivAt (fun u => -G (D / u) / D) (g (D / u - 1) / u ^ 2) u := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    have hu0 : 0 < u := (one_div_pos.mpr hkpos).trans_le hu.1
    have hd := (((hG (D / u) (div_pos hD hu0)).comp u
      ((hasDerivAt_const u D).div (hasDerivAt_id u) hu0.ne')).neg).div_const D
    convert hd using 1
    · rfl
    · field_simp
      ring
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  have h₀ : D / (1 / k₀) = k₀ * D := by field_simp
  have h₁ : D / (1 / k) = k * D := by field_simp
  rw [h₀, h₁]
  ring

end LeanLab.Li2024.SieveIntegrals

#print axioms LeanLab.Li2024.SieveIntegrals.reciprocal_sieve_identity
