import LeanLab.Ternary.Feed1122Decomp581bS145e

namespace LeanLab.Ternary.MMS.Task581.Feed1122
open Finset MeasureTheory

/-- The normalized least prime exponent alpha, log p one over log x. MMS arXiv 1610.02017v2 p. 11 bottom display; new definition, needed to state the Buchstab integral identity. -/
noncomputable def s145f_alpha (x : ℝ) (p : ℕ × ℕ × ℕ) : ℝ := Real.log p.1 / Real.log x

/-- The normalized cofactor exponent theta, log of x over d over log x. MMS arXiv 1610.02017v2 p. 11 bottom display; new definition, needed to state the Buchstab integral identity. -/
noncomputable def s145f_theta (x : ℝ) (p : ℕ × ℕ × ℕ) : ℝ :=
  Real.log (x / tripleProduct p) / Real.log x

section S145_s145f_buchstab_integral_identity
open Finset MeasureTheory

theorem s145g_image (α θ : ℝ) (hα : 0 < α) (h2 : 2 * α ≤ θ) :
    (fun s : ℝ => θ / s - 1) '' Set.Icc α (θ / 2) = Set.Icc 1 (θ / α - 1) := by
  have hθ : 0 < θ := by linarith
  ext v
  constructor
  · rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
    have hs : 0 < s := by linarith
    constructor
    · have : 2 ≤ θ / s := by rw [le_div_iff₀ hs]; linarith
      linarith
    · have : θ / s ≤ θ / α := div_le_div_of_nonneg_left hθ.le hα hs1
      linarith
  · rintro ⟨hv1, hv2⟩
    have hv : 0 < v + 1 := by linarith
    refine ⟨θ / (v + 1), ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ hv]
      have : v + 1 ≤ θ / α := by linarith
      rw [le_div_iff₀ hα] at this; linarith
    · rw [div_le_div_iff₀ hv (by norm_num)]; nlinarith
    · field_simp; ring

theorem s145f_buchstab_integral_identity_s145 (α θ : ℝ) (hα : 1 / 10 ≤ α) (h2 : 2 * α ≤ θ)
    (hθ : θ ≤ 1) :
    (∫ s in α..θ / 2, Task571.buchstabModel ((θ - s) / s) / s ^ 2) =
      Task571.buchstabModel (θ / α) / α - 1 / θ := by
  have hαp : 0 < α := by linarith
  have hθp : 0 < θ := by linarith
  set w := Task571.buchstabModel with hw
  have hS : MeasurableSet (Set.Icc α (θ / 2)) := measurableSet_Icc
  have hder : ∀ x ∈ Set.Icc α (θ / 2),
      HasDerivWithinAt (fun s : ℝ => θ / s - 1) (-θ / x ^ 2) (Set.Icc α (θ / 2)) x := by
    intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h := ((hasDerivAt_inv hx0).const_mul θ).sub_const 1
    have h' : HasDerivAt (fun s : ℝ => θ / s - 1) (-θ / x ^ 2) x := by
      convert h using 1
      · ext s; simp [div_eq_mul_inv]
      · field_simp
    exact h'.hasDerivWithinAt
  have hinj : Set.InjOn (fun s : ℝ => θ / s - 1) (Set.Icc α (θ / 2)) := by
    intro a ha b hb hab
    have ha0 : 0 < a := by linarith [ha.1]
    have hb0 : 0 < b := by linarith [hb.1]
    simp only at hab
    have : θ / a = θ / b := by linarith
    field_simp at this
    nlinarith
  have key := integral_image_eq_integral_abs_deriv_smul hS hder hinj w
  rw [s145g_image α θ hαp h2] at key
  have hle1 : α ≤ θ / 2 := by linarith
  have hL : (∫ s in α..θ / 2, w ((θ - s) / s) / s ^ 2) =
      ∫ x in Set.Icc α (θ / 2), w (θ / x - 1) / x ^ 2 := by
    rw [intervalIntegral.integral_of_le hle1, ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    simp only
    congr 2
    field_simp
  have hR : (∫ x in Set.Icc α (θ / 2), |-θ / x ^ 2| • w (θ / x - 1)) =
      θ * ∫ x in Set.Icc α (θ / 2), w (θ / x - 1) / x ^ 2 := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    simp only [smul_eq_mul]
    rw [abs_div, abs_neg, abs_of_pos hθp, abs_of_pos (by positivity : (0:ℝ) < x ^ 2)]
    ring
  have hu2 : 2 ≤ θ / α := by rw [le_div_iff₀ hαp]; linarith
  have hu10 : θ / α ≤ 10 := by rw [div_le_iff₀ hαp]; linarith
  have hrec : θ / α * w (θ / α) = 1 + ∫ x in Set.Icc 1 (θ / α - 1), w x := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    rcases eq_or_lt_of_le hu2 with he | hlt
    · rw [← he]
      have : w 2 = 1 / 2 := by
        rw [hw]; unfold Task571.buchstabModel; rw [Task571.buchstabStage, if_pos le_rfl]
      rw [this]; norm_num
    · rw [hw, Task571.buchstabModel_recursion hlt hu10]
      have : θ / α ≠ 0 := by positivity
      field_simp
  rw [hL]
  have hI : (∫ x in Set.Icc α (θ / 2), w (θ / x - 1) / x ^ 2) =
      (∫ x in Set.Icc 1 (θ / α - 1), w x) / θ := by
    rw [key, hR]; field_simp
  rw [hI]
  have : (∫ x in Set.Icc 1 (θ / α - 1), w x) = θ / α * w (θ / α) - 1 := by linarith
  rw [this]
  field_simp

end S145_s145f_buchstab_integral_identity

/-- Proved by S145, formerly a LEAF: MMS arXiv 1610.02017v2 p. 11 bottom display, Buchstab integral identity:
for 1/10 ≤ alpha and 2 alpha ≤ theta ≤ 1, so theta over alpha is at most 10 where the
eight stage model agrees with Buchstab's omega, the integral from alpha to theta over 2
of omega of theta minus s over s, over s squared, is omega of theta over alpha over alpha
minus 1 over theta, from u omega u derivative omega of u minus 1. Class MEDIUM. -/
theorem s145f_buchstab_integral_identity (α θ : ℝ) (hα : 1 / 10 ≤ α) (h2 : 2 * α ≤ θ)
    (hθ : θ ≤ 1) :
    (∫ s in α..θ / 2, Task571.buchstabModel ((θ - s) / s) / s ^ 2) =
      Task571.buchstabModel (θ / α) / α - 1 / θ := by
  exact s145f_buchstab_integral_identity_s145 α θ hα h2 hθ

/-- LEAF: MMS arXiv 1610.02017v2 p. 11 bottom display, uniform prime quadrature: with s
equal to log q over log x, d times the least prime main term is within eps of the integral
from alpha to theta over 2 of omega of theta minus s over s, over s squared, the sum being
empty when theta is below 2 alpha, uniformly over primeTriples, by Mertens windows; also
records the ranges of alpha and theta. Class MEDIUM. -/
theorem s145f_uniform_prime_quadrature :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ p ∈ primeTriples x,
      0 < Real.log x ∧ 1 / 10 ≤ s145f_alpha x p ∧ 0 < s145f_theta x p ∧
        s145f_theta x p ≤ 1 ∧
      |(tripleProduct p : ℝ) * s145e_leastPrimeMain x p -
          (if 2 * s145f_alpha x p ≤ s145f_theta x p then
            (∫ s in s145f_alpha x p..s145f_theta x p / 2,
              Task571.buchstabModel ((s145f_theta x p - s) / s) / s ^ 2) else 0)| ≤ ε := by
  sorry

theorem s145e_buchstab_prime_sum_of_s145f_leaves :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ p ∈ primeTriples x,
      |s145e_leastPrimeMain x p - (cofactorModel x p - Real.log x /
            ((tripleProduct p : ℝ) * Real.log (x / tripleProduct p)))| ≤
        ε / tripleProduct p := by
  intro ε hε
  obtain ⟨X, hX⟩ := s145f_uniform_prime_quadrature ε hε
  refine ⟨X, fun x hx p hp => ?_⟩
  obtain ⟨hlx, hα, hθ0, hθ1, hB⟩ := hX x hx p hp
  have hd : (0 : ℝ) < tripleProduct p := by exact_mod_cast tripleProduct_pos hp
  set α := s145f_alpha x p with hαdef
  set θ := s145f_theta x p with hθdef
  have hαpos : 0 < α := by linarith
  have hlp : Real.log p.1 = α * Real.log x := by
    rw [hαdef, s145f_alpha]; field_simp
  have hL : Real.log (x / tripleProduct p) = θ * Real.log x := by
    rw [hθdef, s145f_theta]; field_simp
  have hlp0 : Real.log p.1 ≠ 0 := by rw [hlp]; positivity
  have hL0 : Real.log (x / tripleProduct p) ≠ 0 := by rw [hL]; positivity
  have hu : Real.log (x / tripleProduct p) / Real.log p.1 = θ / α := by
    rw [hL, hlp]; field_simp
  have hT : (tripleProduct p : ℝ) * (cofactorModel x p - Real.log x /
            ((tripleProduct p : ℝ) * Real.log (x / tripleProduct p))) =
      Task571.buchstabModel (θ / α) / α - 1 / θ := by
    unfold cofactorModel
    rw [hu, hL, hlp]
    field_simp
  have hI : Task571.buchstabModel (θ / α) / α - 1 / θ =
      (if 2 * α ≤ θ then
        (∫ s in α..θ / 2, Task571.buchstabModel ((θ - s) / s) / s ^ 2) else 0) := by
    split_ifs with h2
    · exact (s145f_buchstab_integral_identity α θ hα h2 hθ1).symm
    · have hle : θ / α ≤ 2 := by
        rw [div_le_iff₀ hαpos]; linarith
      have hm : Task571.buchstabModel (θ / α) = 1 / (θ / α) := by
        unfold Task571.buchstabModel
        rw [Task571.buchstabStage, if_pos hle]
      rw [hm]
      field_simp
      ring
  rw [← hI, ← hT] at hB
  have : s145e_leastPrimeMain x p - (cofactorModel x p - Real.log x /
            ((tripleProduct p : ℝ) * Real.log (x / tripleProduct p))) =
      ((tripleProduct p : ℝ) * s145e_leastPrimeMain x p - (tripleProduct p : ℝ) *
        (cofactorModel x p - Real.log x /
            ((tripleProduct p : ℝ) * Real.log (x / tripleProduct p)))) / tripleProduct p := by
    field_simp
  rw [this, abs_div, abs_of_pos hd]
  exact div_le_div_of_nonneg_right hB hd.le

end LeanLab.Ternary.MMS.Task581.Feed1122
