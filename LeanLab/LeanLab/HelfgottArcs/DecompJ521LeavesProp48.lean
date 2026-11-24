/-
P0014 page 57, Theorem 1.2, the intermediate estimate split along the paper's proof:
the corrected Proposition 4.8 at T0 = 10^8/q, the zero hypothesis from the GRH input, and the
numerical reduction of the exponential tail through the proved bound B1 of HelfgottMajor.Assembly.
AI wrote the Lean code for burst-20261122 S92. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Statements
import LeanLab.HelfgottArcs.MajorAssembly

namespace LeanLab.HelfgottArcs.DecompJ521LeavesProp48
open Real

/-- The error term err_{eta,chi} of P0014 Proposition 4.8, display 4.52, for t^2 e^{-t^2/2},
with the repaired coefficient 5.056 in place of 5.053 as in MajorAssembly. The factor
e^{-0.1065 T0^2/(pi delta)^2} is read as its limit 0 at delta = 0. -/
noncomputable def errT2 (q T0 δ x : ℝ) : ℝ :=
  T0 * log (q * T0 / (2 * π)) * (3.5 * exp (-0.1598 * T0) +
      0.64 * (if δ = 0 then 0 else exp (-0.1065 * (T0 / (π * |δ|)) ^ 2))) +
    (1.22 * √T0 * log (q * T0) + 5.056 * √T0 + 1.423 * log q + 37.19) / √x +
    (3 + 11 * |δ|) / x + (log q + 6) * (1 + 6 * |δ|) / (x * √x)

/-- LEAF: P0014 page 46 Proposition 4.8, the explicit formula for t^2 e^{-t^2/2} with error
err_{eta,chi}, from Lemmas 4.1, 4.4 and 4.7, with the repaired coefficient 5.056. Class HARD.
P0014 display 4.51 and 4.52. -/
theorem prop_4_8 (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T0 : ℝ) (hT0 : max (4 * π ^ 2 * |δ|) 100 ≤ T0)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T0 → s.re = 1 / 2) :
    MajorShape etaT2 χ δ x (errT2 q T0 δ x) := by
  sorry

/-- The exponential tail of display 4.52 at T0 = 10^8/q, page 57: at most 4.269e-14/q. -/
theorem tail_le {q δ : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 300000) (hδ : |δ| ≤ 4 * 300000 / q) :
    1e8 / q * log (q * (1e8 / q) / (2 * π)) * (3.5 * exp (-0.1598 * (1e8 / q)) +
      0.64 * (if δ = 0 then 0 else exp (-0.1065 * ((1e8 / q) / (π * |δ|)) ^ 2))) ≤
      4.269e-14 / q := by
  have hq0 : 0 < q := by linarith
  have hT : (1000 : ℝ) / 3 ≤ 1e8 / q := by
    rw [le_div_iff₀ hq0]
    nlinarith
  have hqT : q * (1e8 / q) / (2 * π) = 1e8 / (2 * π) := by field_simp
  rw [hqT]
  have hL0 : 0 ≤ log (1e8 / (2 * π)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith [Real.pi_lt_four]
  have hcore : log (1e8 / (2 * π)) * (3.5 * exp (-0.1598 * (1e8 / q)) +
      0.64 * (if δ = 0 then 0 else exp (-0.1065 * ((1e8 / q) / (π * |δ|)) ^ 2))) ≤
        4.269e-22 := by
    by_cases h0 : δ = 0
    · rw [if_pos h0]
      have hb := LeanLab.HelfgottMajor.B1 (u := 1000) hT (by
        rw [div_le_iff₀ (by positivity)]; nlinarith [pi_gt_three])
      have he : 0 ≤ exp (-0.1065 * (1000 : ℝ) ^ 2) := (exp_pos _).le
      nlinarith [mul_nonneg hL0 he]
    · rw [if_neg h0]
      apply LeanLab.HelfgottMajor.B1 hT
      have hd0 : 0 < |δ| := abs_pos.mpr h0
      have hdq : |δ| * q ≤ 1.2e6 := by
        have := (le_div_iff₀ hq0).mp hδ
        norm_num at this ⊢; linarith
      have hp := pi_pos
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : π * (|δ| * q) ≤ π * 1.2e6 := mul_le_mul_of_nonneg_left hdq hp.le
      rw [div_mul_eq_mul_div, le_div_iff₀ hq0]
      nlinarith
  have hT0 : 0 ≤ 1e8 / q := by positivity
  have hh := mul_le_mul_of_nonneg_left hcore hT0
  rw [mul_assoc]
  refine hh.trans (le_of_eq ?_)
  field_simp
  norm_num

/-- Numerical reduction of errT2 at T0 = 10^8/q to the page 57 intermediate bound. -/
theorem errT2_le {q δ x : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 300000) (hδ : |δ| ≤ 4 * 300000 / q) :
    errT2 q (1e8 / q) δ x ≤
      4.269e-14 / q +
        (1.22 * √(1e8 / q) * log (q * (1e8 / q)) + 5.056 * √(1e8 / q) +
          1.423 * log q + 37.19) / √x +
        (3 + 11 * |δ|) / x + (log q + 6) * (1 + 6 * |δ|) / (x * √x) := by
  have h := tail_le hq1 hq hδ
  unfold errT2
  linarith

/-- The zero hypothesis of Proposition 4.8 at T0 = 10^8/q from the GRH input, page 57. -/
theorem zeros_of_input (hG : HelfgottInput) (q : ℕ) [NeZero q] (hq : q ≤ 300000)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 10 ^ 8 / (q : ℝ) → s.re = 1 / 2 := by
  intro s hs h0 h1 him
  refine hG q χ hχ s hs h0 h1 ?_
  by_cases he : Even q
  · exact Or.inr ⟨he, by omega, him.trans (le_max_left _ _)⟩
  · exact Or.inl ⟨he, hq, him⟩

/-- The exact parent `DecompJ521.major_1_2_leaf` statement from the leaves. -/
theorem major_1_2_leaf_of_leaves (hG : HelfgottInput) (x : ℝ) (hx : 10 ^ 8 ≤ x) (q : ℕ)
    [NeZero q] (hq : q ≤ 300000) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ : ℝ)
    (hδ : |δ| ≤ 4 * 300000 / q) :
    MajorShape etaT2 χ δ x
      (4.269e-14 / q +
        (1.22 * √(1e8 / q) * log (q * (1e8 / q)) + 5.056 * √(1e8 / q) +
          1.423 * log q + 37.19) / √x +
        (3 + 11 * |δ|) / x + (log q + 6) * (1 + 6 * |δ|) / (x * √x)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqr : (q : ℝ) ≤ 300000 := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : max (4 * π ^ 2 * |δ|) 100 ≤ 1e8 / (q : ℝ) := by
    apply max_le
    · have hp : π ^ 2 < 10 := by nlinarith [pi_lt_d2, pi_pos]
      have h1 : |δ| * q ≤ 1.2e6 := by
        have := (le_div_iff₀ hq0).mp hδ
        norm_num at this ⊢; linarith
      rw [le_div_iff₀ hq0]
      nlinarith [abs_nonneg δ, sq_nonneg π]
    · rw [le_div_iff₀ hq0]; nlinarith
  have hz := zeros_of_input hG q hq χ hχ
  have hp := prop_4_8 x (by linarith) q χ hχ δ (1e8 / q) hT0 (by
    intro s hs h0 h1 him
    exact hz s hs h0 h1 (by norm_num at him ⊢; exact him))
  exact hp.trans (mul_le_mul_of_nonneg_right (errT2_le hq1 hqr hδ) (by linarith))

end LeanLab.HelfgottArcs.DecompJ521LeavesProp48
