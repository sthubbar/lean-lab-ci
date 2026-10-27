import Mathlib

/-!
Ricci 1937, page 83: a positive power saving absorbs the sieve remainder.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
open Filter Real Asymptotics
noncomputable section

/-- A positive power saving is smaller than x over log x. -/
lemma ricci_power_isLittleO_div_log {κ : ℝ} (hκ : 0 < κ) :
    (fun x : ℝ => x ^ (1 - κ)) =o[atTop] (fun x => x / Real.log x) := by
  have hlog := isLittleO_log_rpow_atTop hκ
  have hprod := hlog.mul_isBigO (isBigO_refl (fun x : ℝ => x ^ (1 - κ)) atTop)
  have hprod' : (fun x : ℝ => Real.log x * x ^ (1 - κ)) =o[atTop] (fun x => x) := by
    apply hprod.congr' (Eventually.of_forall fun _ => rfl)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_add hx]
    norm_num
  apply (isLittleO_mul_iff_isLittleO_div (f := Real.log)
    (g := fun x : ℝ => x ^ (1 - κ)) (h := fun x : ℝ => x) ?_).mp hprod'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (Real.log_pos hx).ne'

/-- Any fixed coefficient on the saved power is eventually below half a main term. -/
theorem ricci_power_error_absorb {κ a : ℝ} (hκ : 0 < κ) (ha : 0 < a) (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, A * (n : ℝ) ^ (1 - κ) ≤ (a / 2) * n / Real.log n := by
  have hsmall := ((ricci_power_isLittleO_div_log hκ).const_mul_left A).natCast_atTop
  filter_upwards [hsmall.def (by positivity : (0 : ℝ) < a / 2), eventually_ge_atTop 2]
    with n hn hn2
  have hnR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hdivpos : 0 < (n : ℝ) / Real.log n := div_pos (by linarith) (Real.log_pos hnR)
  calc
    A * (n : ℝ) ^ (1 - κ) ≤ |A * (n : ℝ) ^ (1 - κ)| := le_abs_self _
    _ ≤ (a / 2) * |(n : ℝ) / Real.log n| := by simpa only [Real.norm_eq_abs] using hn
    _ = (a / 2) * n / Real.log n := by rw [abs_of_pos hdivpos]; ring

/-- The final lower estimate on page 83 after a sieve estimate has supplied the main term. -/
theorem ricci_lower_of_main_error {B : ℕ → ℝ} {a κ : ℝ}
    (ha : 0 < a) (hκ : 0 < κ) (A : ℝ)
    (hbound : ∀ᶠ n : ℕ in atTop,
      a * n / Real.log n - A * (n : ℝ) ^ (1 - κ) < B n) :
    ∃ b : ℝ, 0 < b ∧ ∃ N : ℕ, ∀ n : ℕ, N < n → b * n / Real.log n < B n := by
  have hevent : ∀ᶠ n : ℕ in atTop, (a / 2) * n / Real.log n < B n := by
    filter_upwards [hbound, ricci_power_error_absorb hκ ha A] with n hb he
    have heq : a * n / Real.log n = 2 * ((a / 2) * n / Real.log n) := by ring
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  exact ⟨a / 2, by positivity, N, fun n hn => hN n (by omega)⟩

example : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ ((1 : ℝ) / 2) ≤ n / Real.log n := by
  convert ricci_power_error_absorb (κ := (1 : ℝ) / 2) (a := 2)
    (by norm_num) (by norm_num) 1 using 1
  norm_num

end
end LeanLab.Ricci1937
