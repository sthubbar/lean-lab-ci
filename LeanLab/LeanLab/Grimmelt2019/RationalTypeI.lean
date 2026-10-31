/-
AI wrote this Lean code for CODEX task51.
P0074 page 11, the unscaled rational Type I sum.
The rational harmonic estimate is the lab's unconditional sum_G_div_le.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.TypeIBound
import LeanLab.PNTPort.Vinogradov.Count

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
open LeanLab.PNTPort.LargeSieve
attribute [local instance] Classical.propDecidable

/-- The closed-interval cap is the existing Vinogradov G function at length H plus one. -/
theorem geomCap_eq_G (L θ : ℝ) : geomCap L θ = LeanLab.PNTPort.Vinogradov.G (L + 1) θ := rfl

/-- Every divisor cap is controlled by a single rational harmonic sum with endpoint budget D. -/
theorem divisor_cap_sum_le {q : ℕ} (hq : 0 < q) {r : ℤ} (hr : Int.gcd r q = 1)
    {α : ℝ} (hα : |α - (r : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (D : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    (∑ d ∈ Finset.Icc 1 D, geomCap (H / d) ((d : ℝ) * α)) ≤
      12 * ((H + D) / q + D + q) * (1 + Real.log q + Real.log D) := by
  have hc : IsCoprime r (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hr
  apply le_trans ?_ (LeanLab.PNTPort.Vinogradov.sum_G_div_le hq hc hα D (by positivity))
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hdD : (d : ℝ) ≤ D := by exact_mod_cast (Finset.mem_Icc.mp hd).2
  rw [geomCap_eq_G, mul_comm (d : ℝ) α]
  apply LeanLab.PNTPort.Vinogradov.G_mono
  rw [div_add', div_le_div_iff_of_pos_right hdpos] <;> linarith

/-- The rational divisor Fourier sum has an explicit denominator-saving bound. -/
theorem divisorWeight_rational_le {q : ℕ} (hq : 0 < q) {r : ℤ} (hr : Int.gcd r q = 1)
    {α : ℝ} (hα : |α - (r : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (D : ℕ) (weights : ℕ → ℝ) (t H : ℝ) (hH : 0 ≤ H)
    (hw : ∀ d ∈ Finset.Icc 1 D, |weights d| ≤ 1) :
    ‖∑ n ∈ shortInterval t H, (divisorWeight D weights n : ℂ) *
      LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ ≤
      12 * ((H + D) / q + D + q) * (1 + Real.log q + Real.log D) :=
  (divisorWeight_typeI D weights t H α hH hw).trans (divisor_cap_sum_le hq hr hα D hH)

/-- Absorbing the endpoint budget costs a factor two but leaves H divided by q. -/
theorem divisorWeight_rational_simple_le {q : ℕ} (hq : 0 < q) {r : ℤ}
    (hr : Int.gcd r q = 1) {α : ℝ}
    (hα : |α - (r : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (D : ℕ) (weights : ℕ → ℝ) (t H : ℝ) (hH : 0 ≤ H)
    (hw : ∀ d ∈ Finset.Icc 1 D, |weights d| ≤ 1) :
    ‖∑ n ∈ shortInterval t H, (divisorWeight D weights n : ℂ) *
      LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ ≤
      24 * (H / q + D + q) * (1 + Real.log q + Real.log D) := by
  apply (divisorWeight_rational_le hq hr hα D weights t H hH hw).trans
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqR : (0 : ℝ) < q := by linarith
  have hD : (0 : ℝ) ≤ D := by positivity
  have hdq : (D : ℝ) / q ≤ D := (div_le_self hD hqr)
  have hhq : 0 ≤ H / (q : ℝ) := by positivity
  have hlog : 0 ≤ 1 + Real.log q + Real.log D := by
    linarith [Real.log_natCast_nonneg q, Real.log_natCast_nonneg D]
  rw [add_div]
  nlinarith only [hdq, hhq, hD, hqR, hlog]

#print axioms geomCap_eq_G
#print axioms divisor_cap_sum_le
#print axioms divisorWeight_rational_le
#print axioms divisorWeight_rational_simple_le
end LeanLab.Grimmelt2019.MainTerm
