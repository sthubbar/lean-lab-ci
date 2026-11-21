import LeanLab.HelfgottMajor.Prep1121ContourRect

/-!
PREP deepening 2026-11-21, session CLAUDE-prep1121 HM-contour-p2. Pieces for the HARD leaf
`Prep1121ContourRect.rect_cut_origin`.

P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 33, display 4.7:
the shift of the line of integration crosses s = 0, where for even χ the integrand has a double
pole, and the paper keeps the residue there as the circle integral R. The PNTPort residue
formula `RectangleIntegral'_eq_sumResiduesIn` covers simple poles only, so the standard
argument, Ahlfors ch. 4 and Davenport ch. 17, is split as follows. Subtract the principal part
P(s) = Σ_{k < N} a_k s^(-(k+1)) of f at 0. Then f - P has no pole at 0 and the same simple poles
and residues as f elsewhere, so the PNTPort formula applies to it; its circle integral about 0
vanishes; and the rectangle integral of P over 2πi and the circle integral of P over 2πi are
both a_0, since s^(-(k+1)) has a primitive off 0 for k ≥ 1.

The final result `rect_cut_origin_of_pieces` has the exact statement of
`Prep1121ContourRect.rect_cut_origin` and no sorry of its own. Generic complex analysis, no
L-function. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121DCtCut
open Real MeasureTheory Set Filter
open scoped Topology Interval

/-- The principal part Σ_{k < N} a_k s^(-(k+1)) at s = 0, a finite Laurent polynomial. -/
local notation "PP" N "," a => fun s : ℂ => ∑ k ∈ Finset.range N, a k * s ^ (-((k : ℤ) + 1))

/-- LEAF: Ahlfors ch. 4 §3.2, the Laurent principal part at a pole, used at s = 0 on P0014
page 33, display 4.7. A function meromorphic at 0 differs from some finite Laurent polynomial
Σ_{k < N} a_k s^(-(k+1)) by a function meromorphic at 0 with no pole there. MEDIUM: write
f = s^n h with h analytic, `meromorphicOrderAt_eq_int_iff`, and take the first -n Taylor
coefficients of h, `HasFPowerSeriesAt`. -/
theorem principal_part_at_origin {f : ℂ → ℂ} (hf : MeromorphicAt f 0) :
    ∃ (N : ℕ) (a : ℕ → ℂ), MeromorphicAt (f - PP N, a) 0 ∧
      0 ≤ meromorphicOrderAt (f - PP N, a) 0 := by
  sorry

/-- PROVED. A finite Laurent polynomial in s^(-1) is holomorphic off 0. -/
theorem principal_differentiableAt (N : ℕ) (a : ℕ → ℂ) {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (PP N, a) s := by
  have h := DifferentiableAt.sum (u := Finset.range N)
    (A := fun k (t : ℂ) => a k * t ^ (-((k : ℤ) + 1))) (x := s)
    (fun k _ => (differentiableAt_zpow.mpr (Or.inl hs)).const_mul _)
  convert h using 1
  funext t
  simp only [Finset.sum_apply]

/-- LEAF: Cauchy's theorem for a removable singularity, P0014 page 33, display 4.7: g
holomorphic on the closed punctured disc of radius r about 0 and with no pole at 0 has circle
integral 0. EASY: g agrees off 0 with a function continuous on the closed disc and holomorphic
inside, `circleIntegral.integral_eq_zero_of_differentiable_on_off_countable` with the
countable set {0}; the circle integral only sees values on the circle. -/
theorem circle_removable {g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (Metric.closedBall 0 r \ {0})) (hm : MeromorphicAt g 0)
    (h0 : 0 ≤ meromorphicOrderAt g 0) : circleIntegral g 0 r = 0 := by
  sorry

/-- PROVED. P0014 page 33, display 4.7, the circle integral of the principal part:
∮ s^(-(k+1)) ds over |s| = r is 2πi for k = 0 and 0 for k ≥ 1, from
`circleIntegral.integral_sub_zpow_of_ne` and `circleIntegral.integral_sub_center_inv`, with
linearity over the finite sum. -/
theorem circle_integral_principal (N : ℕ) (a : ℕ → ℂ) {r : ℝ} (hr : 0 < r) :
    circleIntegral (PP N, a) 0 r =
      2 * π * Complex.I * ∑ k ∈ Finset.range N, if k = 0 then a k else 0 := by
  have hsph : ∀ s ∈ Metric.sphere (0 : ℂ) r, s ≠ 0 := by
    intro s hs h0
    rw [h0, mem_sphere_iff_norm, sub_zero, norm_zero] at hs
    linarith
  have hint : ∀ M : ℕ, CircleIntegrable (PP M, a) 0 r := fun M =>
    ContinuousOn.circleIntegrable hr.le (fun s hs =>
      (principal_differentiableAt M a (hsph s hs)).continuousAt.continuousWithinAt)
  have hti : ∀ k : ℕ, CircleIntegrable (fun s : ℂ => a k * s ^ (-((k : ℤ) + 1))) 0 r :=
    fun k => ContinuousOn.circleIntegrable hr.le (fun s hs =>
      ((differentiableAt_zpow.mpr (Or.inl (hsph s hs))).const_mul (a k)
        ).continuousAt.continuousWithinAt)
  have hterm : ∀ k : ℕ, circleIntegral (fun s : ℂ => a k * s ^ (-((k : ℤ) + 1))) 0 r =
      2 * π * Complex.I * (if k = 0 then a k else 0) := by
    intro k
    rw [circleIntegral.integral_const_mul]
    rcases eq_or_ne k 0 with rfl | hk
    · have h := circleIntegral.integral_sub_center_inv (0 : ℂ) hr.ne'
      simp only [sub_zero] at h
      simp only [Nat.cast_zero, zero_add, zpow_neg_one, if_true, h]
      ring
    · have h := circleIntegral.integral_sub_zpow_of_ne (n := -((k : ℤ) + 1))
        (by omega) (0 : ℂ) 0 r
      simp only [sub_zero] at h
      rw [h, if_neg hk]
      ring
  induction N with
  | zero => simp [circleIntegral]
  | succ n ih =>
    have hsplit : (PP (n + 1), a) = fun s : ℂ =>
        (∑ k ∈ Finset.range n, a k * s ^ (-((k : ℤ) + 1))) + a n * s ^ (-((n : ℤ) + 1)) := by
      funext s; rw [Finset.sum_range_succ]
    rw [hsplit, circleIntegral.integral_add (hint n) (hti n), ih, hterm n,
      Finset.sum_range_succ]
    ring

/-- LEAF: P0014 page 33, display 4.7, the rectangle integral of the principal part, for a
rectangle with 0 strictly inside: the normalized rectangle integral of s^(-(k+1)) is 1 for
k = 0 and 0 for k ≥ 1. MEDIUM: for k = 0, `RectanglePullToNhdOfPole` and the residue 1 of
1/s, or the explicit side integrals of 1/s; for k ≥ 1, s^(-k)/(-k) is a primitive on the
border, so each side is a difference of values and the four differences cancel. -/
theorem rect_integral_principal (N : ℕ) (a : ℕ → ℂ) {z w : ℂ} {r : ℝ} (hr : 0 < r)
    (hzr : z.re < -r) (hzi : z.im < -r) (hwr : r < w.re) (hwi : r < w.im) :
    RectangleIntegral' (PP N, a) z w = ∑ k ∈ Finset.range N, if k = 0 then a k else 0 := by
  sorry

/-- LEAF: P0014 page 33, display 4.7, linearity of the rectangle integral: subtracting the
principal part splits the rectangle integral. MEDIUM: P is continuous on the border, which
avoids 0; f has no pole on the border, so along each side it agrees off a finite set with a
continuous function, as in the private `intervalIntegral_congr_ae_of_codiscreteWithin_along_path`
of ResidueCalcOnRectangles; then `intervalIntegral.integral_sub` on the four sides. -/
theorem rect_integral_add_principal {f : ℂ → ℂ} {z w : ℂ} {r : ℝ} (hr : 0 < r)
    (hzr : z.re < -r) (hzi : z.im < -r) (hwr : r < w.re) (hwi : r < w.im)
    (hmero : MeromorphicOn f (Complex.Rectangle z w))
    (hbd : Disjoint (RectangleBorder z w) {p | meromorphicOrderAt f p < 0}) (N : ℕ)
    (a : ℕ → ℂ) :
    RectangleIntegral' f z w =
      RectangleIntegral' (f - PP N, a) z w + RectangleIntegral' (PP N, a) z w := by
  sorry

/-- LEAF: P0014 page 33, display 4.7, the residue formula for f - P. With the principal part at
0 removed, f - P is meromorphic on the rectangle with finitely many poles, none on the border,
all simple, and its poles and residues are those of f away from 0. MEDIUM: apply
`RectangleIntegral'_eq_sumResiduesIn` to f - P; off 0, P is analytic, so the order of f - P
equals that of f where f has a pole and (s - p)P(s) → 0 gives equal residues;
`sumResiduesIn_inter_eq_of_set_eq` for the index sets. -/
theorem rect_residue_sub_principal {f : ℂ → ℂ} {z w : ℂ} {r : ℝ} (hr : 0 < r)
    (hzr : z.re < -r) (hzi : z.im < -r) (hwr : r < w.re) (hwi : r < w.im)
    (hmero : MeromorphicOn f (Complex.Rectangle z w))
    (hbd : Disjoint (RectangleBorder z w) {p | meromorphicOrderAt f p < 0})
    (hfin : (Complex.Rectangle z w ∩ {p | meromorphicOrderAt f p < 0}).Finite)
    (hsimple : HasSimplePolesOn f (Complex.Rectangle z w \ {0})) (N : ℕ) (a : ℕ → ℂ)
    (hPm : MeromorphicAt (f - PP N, a) 0) (hP0 : 0 ≤ meromorphicOrderAt (f - PP N, a) 0) :
    RectangleIntegral' (f - PP N, a) z w =
      sumResiduesIn f ((Complex.Rectangle z w ∩ {p | meromorphicOrderAt f p < 0}) \ {0}) := by
  sorry

/-- PROVED. Points of the closed disc of radius r about 0 lie in the rectangle when
z.re < -r, z.im < -r, r < w.re and r < w.im. -/
theorem closedBall_subset_rect {z w : ℂ} {r : ℝ} (hzr : z.re < -r) (hzi : z.im < -r)
    (hwr : r < w.re) (hwi : r < w.im) : Metric.closedBall (0 : ℂ) r ⊆ Complex.Rectangle z w := by
  intro s hs
  have hn : ‖s‖ ≤ r := by simpa using hs
  have h1 : |s.re| ≤ r := (Complex.abs_re_le_norm s).trans hn
  have h2 : |s.im| ≤ r := (Complex.abs_im_le_norm s).trans hn
  rw [abs_le] at h1 h2
  refine ⟨?_, ?_⟩
  · simp only [mem_preimage]
    rw [Set.uIcc_of_le (by linarith)]
    exact ⟨by linarith, by linarith⟩
  · simp only [mem_preimage]
    rw [Set.uIcc_of_le (by linarith)]
    exact ⟨by linarith, by linarith⟩

/-- Assembly, no sorry of its own: the exact statement of
`Prep1121ContourRect.rect_cut_origin`. P0014 page 33, display 4.7. -/
theorem rect_cut_origin_of_pieces {f : ℂ → ℂ} {z w : ℂ} {r : ℝ} (hr : 0 < r) (hzr : z.re < -r)
    (hzi : z.im < -r) (hwr : r < w.re) (hwi : r < w.im)
    (hmero : MeromorphicOn f (Complex.Rectangle z w))
    (hbd : Disjoint (RectangleBorder z w) {p | meromorphicOrderAt f p < 0})
    (hfin : (Complex.Rectangle z w ∩ {p | meromorphicOrderAt f p < 0}).Finite)
    (hsimple : HasSimplePolesOn f (Complex.Rectangle z w \ {0}))
    (hdisc : DifferentiableOn ℂ f (Metric.closedBall 0 r \ {0})) :
    RectangleIntegral' f z w =
      (2 * π * Complex.I)⁻¹ * circleIntegral f 0 r +
        sumResiduesIn f ((Complex.Rectangle z w ∩ {p | meromorphicOrderAt f p < 0}) \ {0}) := by
  have h0R : (0 : ℂ) ∈ Complex.Rectangle z w :=
    closedBall_subset_rect hzr hzi hwr hwi (Metric.mem_closedBall_self hr.le)
  obtain ⟨N, a, hPm, hP0⟩ := principal_part_at_origin (hmero 0 h0R)
  set P : ℂ → ℂ := PP N, a with hPdef
  have hPd : DifferentiableOn ℂ P (Metric.closedBall 0 r \ {0}) := fun s hs =>
    (principal_differentiableAt N a (by simpa only [mem_singleton_iff] using hs.2)
      ).differentiableWithinAt
  have hsph : Metric.sphere (0 : ℂ) r ⊆ Metric.closedBall 0 r \ {0} := by
    intro s hs
    refine ⟨Metric.sphere_subset_closedBall hs, ?_⟩
    intro h0
    rw [mem_singleton_iff] at h0
    rw [h0, mem_sphere_iff_norm, sub_zero, norm_zero] at hs
    linarith
  have hfc : CircleIntegrable f 0 r :=
    ContinuousOn.circleIntegrable hr.le (hdisc.continuousOn.mono hsph)
  have hPc : CircleIntegrable P 0 r :=
    ContinuousOn.circleIntegrable hr.le (hPd.continuousOn.mono hsph)
  have hcirc : circleIntegral f 0 r = circleIntegral (f - P) 0 r + circleIntegral P 0 r := by
    have h := circleIntegral.integral_sub hfc hPc
    have heq : (fun s => f s - P s) = f - P := rfl
    rw [heq] at h
    rw [h]; ring
  have hgz : circleIntegral (f - P) 0 r = 0 :=
    circle_removable hr (hdisc.sub hPd) hPm hP0
  rw [rect_integral_add_principal hr hzr hzi hwr hwi hmero hbd N a,
    rect_residue_sub_principal hr hzr hzi hwr hwi hmero hbd hfin hsimple N a hPm hP0,
    rect_integral_principal N a hr hzr hzi hwr hwi, hcirc, hgz,
    circle_integral_principal N a hr]
  have hI : (2 * π * Complex.I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) Complex.I_ne_zero
  field_simp
  ring

end LeanLab.HelfgottMajor.Prep1121DCtCut

#print axioms LeanLab.HelfgottMajor.Prep1121DCtCut.principal_differentiableAt
#print axioms LeanLab.HelfgottMajor.Prep1121DCtCut.closedBall_subset_rect
#print axioms LeanLab.HelfgottMajor.Prep1121DCtCut.circle_integral_principal
#print axioms LeanLab.HelfgottMajor.Prep1121DCtCut.rect_cut_origin_of_pieces
