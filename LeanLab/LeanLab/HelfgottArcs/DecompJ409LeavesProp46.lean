/-
P0014 page 57, Theorem 1.1, the intermediate estimate split along the paper's proof:
Proposition 4.6 at T0 = 10^8/q, the zero hypothesis from the GRH input, and the numerical
reduction of err_{eta,chi} through the proved bounds A1 to A56 of HelfgottMajor.Assembly.
AI wrote the Lean code for burst-20261122 S92. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Statements
import LeanLab.HelfgottArcs.MajorAssembly

namespace LeanLab.HelfgottArcs.DecompJ409LeavesProp46
open Real

/-- The error term err_{eta,chi} of P0014 Proposition 4.6, display 4.43, for the Gaussian. -/
noncomputable def errGauss (q T0 δ x : ℝ) : ℝ :=
  log (q * T0 / (2 * π)) * (4.329 * exp (-0.1598 * T0) +
      0.802 * |δ| * exp (-0.1065 * (T0 / (π * |δ|)) ^ 2)) +
    (2.337 * √T0 * log (q * T0) + 21.817 * √T0 + 2.85 * log q + 74.38) / √x +
    (3 * log q + 14 * |δ| + 17) / x + (log q + 6) * (1 + 5 * |δ|) / (x * √x)

/-- LEAF: P0014 page 43 Proposition 4.6, the explicit formula for the Gaussian weight with
error err_{eta,chi}, from Lemmas 4.4 and 4.5 and the norms 4.42. Class HARD. P0014 display
4.43. -/
theorem prop_4_6 (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T0 : ℝ) (hT0 : max (4 * π ^ 2 * |δ|) 100 ≤ T0)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T0 → s.re = 1 / 2) :
    MajorShape etaHeart χ δ x (errGauss q T0 δ x) := by
  sorry

/-- The zero hypothesis of Proposition 4.6 at T0 = 10^8/q from the GRH input, page 57. -/
theorem zeros_of_input (hG : HelfgottInput) (q : ℕ) [NeZero q] (hq : q ≤ 300000)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 10 ^ 8 / (q : ℝ) → s.re = 1 / 2 := by
  intro s hs h0 h1 him
  refine hG q χ hχ s hs h0 h1 ?_
  by_cases he : Even q
  · exact Or.inr ⟨he, by omega, him.trans (le_max_left _ _)⟩
  · exact Or.inl ⟨he, hq, him⟩

/-- MajorShape is monotone in its bound. -/
theorem majorShape_mono {q : ℕ} {η : ℝ → ℝ} {χ : DirichletCharacter ℂ q} {δ x B B' : ℝ}
    (hx : 0 ≤ x) (hB : B ≤ B') (h : MajorShape η χ δ x B) : MajorShape η χ δ x B' :=
  h.trans (mul_le_mul_of_nonneg_right hB hx)

/-- Numerical reduction of err_{eta,chi} at T0 = 10^8/q to the page 57 intermediate bound. -/
theorem errGauss_le {q δ x : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 300000)
    (hδ : |δ| ≤ 4 * 300000 / q) (hx : 10 ^ 8 ≤ x) :
    errGauss q (1e8 / q) δ x ≤
      5.281e-22 + (648662 / √q + 111) / √x + (55 + 1.7e7 / q) / x +
        (19 + 1.2e8 / q) / (x * √x) := by
  have hq0 : 0 < q := by linarith
  have hx0 : 0 < x := by linarith
  set d := |δ| with hdd
  have hd0 : 0 ≤ d := abs_nonneg δ
  have hd : d ≤ 1.2e6 / q := by rw [hdd]; norm_num at hδ ⊢; exact hδ
  have hT : (1000 : ℝ) / 3 ≤ 1e8 / q := by
    rw [le_div_iff₀ hq0]
    nlinarith
  have hd1 : d ≤ 1.2e6 := by
    have hdq := (le_div_iff₀ hq0).mp hd
    nlinarith
  have hqT : q * (1e8 / q) / (2 * π) = 1e8 / (2 * π) := by field_simp
  have hlog0 : 0 ≤ log (1e8 / (2 * π)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith [Real.pi_lt_four]
  have he1 := LeanLab.HelfgottMajor.A1 hT
  have hterm : d * (0.802 * exp (-0.1065 * ((1e8 / q) / (π * d)) ^ 2)) ≤
      d * 4.3166e-33 := by
    rcases eq_or_lt_of_le hd0 with h | h
    · rw [← h]; simp
    · apply mul_le_mul_of_nonneg_left _ hd0
      apply LeanLab.HelfgottMajor.A2
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hdq : d * q ≤ 1.2e6 := by
        have := (le_div_iff₀ hq0).mp hd
        linarith
      have hp := pi_pos
      have : π * (d * q) ≤ π * 1.2e6 := mul_le_mul_of_nonneg_left hdq hp.le
      rw [div_mul_eq_mul_div, le_div_iff₀ hq0]
      nlinarith
  have he : log (1e8 / (2 * π)) * (4.329 * exp (-0.1598 * (1e8 / q)) +
      0.802 * d * exp (-0.1065 * ((1e8 / q) / (π * d)) ^ 2)) ≤ 5.281e-22 := by
    have hinner : 4.329 * exp (-0.1598 * (1e8 / q)) +
        0.802 * d * exp (-0.1065 * ((1e8 / q) / (π * d)) ^ 2) ≤
          3.184e-23 + 1.2e6 * 4.3166e-33 := by
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hinner hlog0
    obtain ⟨a, b, c⟩ := LeanLab.HelfgottMajor.A3
    nlinarith
  have hq' : q ≤ 3e5 := by norm_num at *; exact hq
  have hz := div_le_div_of_nonneg_right (LeanLab.HelfgottMajor.A4 hq1 hq') (sqrt_nonneg x)
  obtain ⟨ha, hb⟩ := LeanLab.HelfgottMajor.A56 hq1 hq' hd0 hd
  have ha' := div_le_div_of_nonneg_right ha hx0.le
  have hb' := div_le_div_of_nonneg_right hb (show 0 ≤ x * √x by positivity)
  unfold errGauss
  rw [hqT, ← hdd]
  linarith

/-- The exact parent `DecompJ409.major_1_1_leaf` statement from the leaves. -/
theorem major_1_1_leaf_of_leaves (hG : HelfgottInput) (x : ℝ) (hx : 10 ^ 8 ≤ x) (q : ℕ)
    [NeZero q] (hq : q ≤ 300000) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ : ℝ)
    (hδ : |δ| ≤ 4 * 300000 / q) :
    MajorShape etaHeart χ δ x
      (5.281e-22 + (648662 / √q + 111) / √x + (55 + 1.7e7 / q) / x +
        (19 + 1.2e8 / q) / (x * √x)) := by
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
  have hp := prop_4_6 x (by linarith) q χ hχ δ (1e8 / q) hT0 (by
    intro s hs h0 h1 him
    exact hz s hs h0 h1 (by norm_num at him ⊢; exact him))
  exact majorShape_mono (by linarith) (errGauss_le hq1 hqr hδ hx) hp

end LeanLab.HelfgottArcs.DecompJ409LeavesProp46
