/-
burst-20261122 S124, step feed1122-DecompJ521-p2. P0014 Proposition 4.8, page 46, displays 4.51
and 4.52, for η(t) = t^2 e^(-t^2/2), split along its proof on page 46: Lemma 4.1 with the norms of
display 4.50, Lemma 4.4 as applied on page 46, and Lemma 4.7 on page 45, then the arithmetic of
page 46. The zero sums are written with G_δ(ρ) = F_δ(ρ + 2), display 4.44, where F_δ is the lab
Mellin transform SplitGaussian123.gaussianMellin of e^(-t^2/2) e(δt).
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.DecompJ521LeavesProp48
import LeanLab.HelfgottMajor.Gamma503
import LeanLab.HelfgottMajor.Lemma41Terms

namespace LeanLab.HelfgottArcs.DecompJ521LeavesProp48S124Prop48
open Real
open LeanLab.HelfgottArcs LeanLab.HelfgottMajor LeanLab.HelfgottArcs.DecompJ521LeavesProp48

/-- A zero contribution G_δ(ρ) x^ρ for η(t) = t^2 e^(-t^2/2), with G_δ(s) = F_δ(s + 2) by
P0014 display 4.44 on page 44, counted with analytic multiplicity as in display 4.1. -/
noncomputable def zeroTermT2 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x : ℝ) (ρ : ℂ) : ℂ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ •
    (SplitGaussian123.gaussianMellin δ (ρ + 2) * (x : ℂ) ^ ρ)

/-- The sum of display 4.1 over the non-trivial zeros of height at most T, P0014 page 46, the
part bounded by Lemma 4.4. -/
noncomputable def lowZerosT2 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x T : ℝ) : ℂ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, zeroTermT2 χ δ x ρ.val

/-- The sum of display 4.1 over the non-trivial zeros of height above T, P0014 page 46, the
part bounded by Lemma 4.7. -/
noncomputable def highZerosT2 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x T : ℝ) : ℂ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, zeroTermT2 χ δ x ρ.val

/-- LEAF: P0014 Lemma 4.1, page 31, displays 4.1 to 4.3, for η(t) = t^2 e^(-t^2/2) as applied on
page 46. Since η(0) = 0 the residue R is O*(c0) with c0 of display 4.3 at the norms of display
4.50, and the contour error is (log q + 6.01)(|η'|₂ + 2π abs δ |η|₂) x^(-1/2) with
|η'|₂² = 7√π/16 and |η|₂² = 3√π/8. Class HARD. QUESTION: for an even primitive χ with q above 1,
L'/L has a pole at s = 0 and G_δ(0) = F_δ(2) need not vanish, so the residue there is G_δ(0),
of norm at most 1; check that c0 covers it, as the lab found a missing term for the Gaussian. -/
theorem lemma_4_1_t2 (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ) :
    ∃ R : ℂ, ‖R‖ ≤ Lemma41Terms.c0 1.48469 1.72169 1.07791 1.54568 |δ| ∧
      ‖Schi etaT2 χ δ x - (if q = 1 then fhat etaT2 (-δ) * x else 0) +
        lowZerosT2 χ δ x T + highZerosT2 χ δ x T + R‖ ≤
        (log q + 6.01) * (√(7 * √π / 16) + 2 * π * |δ| * √(3 * √π / 8)) / √x := by
  sorry

/-- LEAF: P0014 Lemma 4.4, display 4.29 on page 39, with the norms of display 4.50, as applied
on page 46 in the proof of Proposition 4.8: the zeros up to T, all on the critical line, give at
most (1.22 sqrt T log qT + 5.056 sqrt T + 1.423 log q + 37.19) sqrt x. The page prints 5.053 and
37.188; 5.056 is the lab repair recorded in MajorAssembly and DecompJ521LeavesProp48.errT2.
Class HARD. -/
theorem lemma_4_4_t2 (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖lowZerosT2 χ δ x T‖ ≤
      (1.22 * √T * log (q * T) + 5.056 * √T + 1.423 * log q + 37.19) * √x := by
  sorry

/-- LEAF: P0014 Lemma 4.7, page 45, as used on page 46: the zeros above T contribute at most
T log(qT/2π)(3.5 e^(-0.1598 T) + 0.64 e^(-0.1065 T²/(πδ)²)) x, the last exponential read as its
limit 0 at δ = 0. Class HARD. -/
theorem lemma_4_7 (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖highZerosT2 χ δ x T‖ ≤
      T * log (q * T / (2 * π)) * (3.5 * exp (-0.1598 * T) +
        0.64 * (if δ = 0 then 0 else exp (-0.1065 * (T / (π * |δ|)) ^ 2))) * x := by
  sorry

/-- PROVED. The arithmetic of page 46: residue at most 2.138 + 10.99 abs δ and contour error
with 0.881 + 5.123 abs δ fit in (3 + 11 abs δ) + (log q + 6)(1 + 6 abs δ) x^(-1/2). -/
theorem budget_t2 {L d s : ℝ} (hL : 0 ≤ L) (hd : 0 ≤ d) (hs : 1 ≤ s) :
    (L + 6.01) * (0.881 + 5.123 * d) / s + (2.138 + 10.99 * d) ≤
      (L + 6) * (1 + 6 * d) / s + (3 + 11 * d) := by
  have hs0 : 0 < s := by linarith
  have key : (L + 6.01) * (0.881 + 5.123 * d) / s - (L + 6) * (1 + 6 * d) / s ≤
      0.862 + 0.01 * d := by
    rw [← sub_div, div_le_iff₀ hs0]
    nlinarith [mul_nonneg hd hL, mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 0.862 + 0.01 * d)]
  linarith

/-- The exact parent `prop_4_8` statement from the leaves. -/
theorem prop_4_8_of_leaves (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T0 : ℝ) (hT0 : max (4 * π ^ 2 * |δ|) 100 ≤ T0)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T0 → s.re = 1 / 2) :
    MajorShape etaT2 χ δ x (errT2 q T0 δ x) := by
  unfold MajorShape errT2
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < sqrt x := sqrt_pos.mpr hx0
  have hs1 : 1 ≤ sqrt x := one_le_sqrt.mpr hx
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hL : 0 ≤ log (q : ℝ) := log_nonneg hq1
  obtain ⟨R, hR, hE⟩ := lemma_4_1_t2 x hx q χ hχ δ T0
  have hLz := lemma_4_4_t2 x hx q χ hχ δ T0 hT0 hzeros
  have hHz := lemma_4_7 x hx q χ hχ δ T0 hT0 hzeros
  have hc0 := Lemma41Terms.c0_t2 (abs_nonneg δ)
  have hn := Lemma41Terms.lemma41_t2 (abs_nonneg δ)
  have hE' : (log q + 6.01) * (√(7 * √π / 16) + 2 * π * |δ| * √(3 * √π / 8)) / √x ≤
      (log q + 6.01) * (0.881 + 5.123 * |δ|) / √x :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by linarith)) hs0.le
  have hb := budget_t2 hL (abs_nonneg δ) hs1
  have htri : ‖Schi etaT2 χ δ x -
      (if q = 1 then fhat etaT2 (-δ) * x else 0)‖ ≤
      ‖Schi etaT2 χ δ x - (if q = 1 then fhat etaT2 (-δ) * x else 0) +
        lowZerosT2 χ δ x T0 + highZerosT2 χ δ x T0 + R‖ +
        ‖lowZerosT2 χ δ x T0‖ + ‖highZerosT2 χ δ x T0‖ + ‖R‖ := by
    calc
      _ = ‖(Schi etaT2 χ δ x - (if q = 1 then fhat etaT2 (-δ) * x else 0) +
          lowZerosT2 χ δ x T0 + highZerosT2 χ δ x T0 + R) -
          lowZerosT2 χ δ x T0 - highZerosT2 χ δ x T0 - R‖ := by congr 1; abel
      _ ≤ _ := (norm_sub_le _ _).trans (by
        gcongr
        exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _))
  have hsq : sqrt x * sqrt x = x := mul_self_sqrt hx0.le
  set H := T0 * log (q * T0 / (2 * π)) * (3.5 * exp (-0.1598 * T0) +
      0.64 * (if δ = 0 then 0 else exp (-0.1065 * (T0 / (π * |δ|)) ^ 2))) with hH
  set A := 1.22 * √T0 * log (q * T0) + 5.056 * √T0 + 1.423 * log q + 37.19 with hA
  have heq : (H + A / √x + (3 + 11 * |δ|) / x + (log q + 6) * (1 + 6 * |δ|) / (x * √x)) * x =
      H * x + A * √x + (3 + 11 * |δ|) + (log q + 6) * (1 + 6 * |δ|) / √x := by
    generalize hroot : sqrt x = s at hsq hs0
    have hsne : s ≠ 0 := hs0.ne'
    rw [← hsq]
    field_simp
  rw [heq]
  linarith

end LeanLab.HelfgottArcs.DecompJ521LeavesProp48S124Prop48
