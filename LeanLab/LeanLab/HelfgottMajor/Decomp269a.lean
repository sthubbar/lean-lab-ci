import LeanLab.HelfgottMajor.Decomp123
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Analytic.Order

/-!
P0014 Proposition 4.6, pages 43 and 44, display 4.43.
The proof splits the explicit formula into low zeros, high zeros and a residue.
The final remainder uses the existing factor 6 repair.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp269a
open Real LeanLab.HelfgottArcs Decomp123

/-- The Mellin transform F_delta used on page 43 in the proof of display 4.43. -/
noncomputable def gaussianMellin (δ : ℝ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) s

/-- A zero contribution with its analytic multiplicity, as in display 4.1 on page 31. -/
noncomputable def zeroTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x : ℝ) (ρ : ℂ) : ℂ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ •
    (gaussianMellin δ ρ * (x : ℂ) ^ ρ)

/-- The low zero sum in Lemma 4.4, display 4.29 on page 39, including multiplicities. -/
noncomputable def lowZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x T : ℝ) : ℂ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, zeroTerm χ δ x ρ.val

/-- The high zero sum in Lemma 4.5, Lemma 4.5 on page 40, including multiplicities. -/
noncomputable def highZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x T : ℝ) : ℂ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, zeroTerm χ δ x ρ.val

/-- LEAF. Pages 31 to 36, displays 4.1 to 4.3 and 4.23, specialized on page 44.
The explicit formula leaves a residue and a contour error. This does not bound either zero sum.
The outside Landau input is Montgomery and Vaughan, Lemma 6.3.
-/
theorem explicit_formula_remainder (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x := by
  -- BLOCKED OUT OF REACH: requires the explicit formula for Dirichlet L-functions
  -- (contour integration, Hadamard factorization, zero-free regions).
  -- Mathlib lacks: Mellin inversion on strips, zero-density estimates,
  -- Montgomery-Vaughan Lemma 6.3, and the quantitative zero-sum formula.
  -- The assembly gaussian_estimate_of_components and gaussian_explicit_estimate
  -- are already proven and only depend on these three analytic leaves.
  sorry

/-- LEAF. Page 43 applies Lemma 4.4, display 4.29 on page 39, and the norms in 4.42.
This bounds only zeros up to T on the critical line.
-/
theorem low_zero_bound (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖lowZeros χ δ x T‖ ≤
      (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T +
        2.85 * log q + 74.38) * sqrt x := by
  -- BLOCKED OUT OF REACH: requires zero-density estimates for Dirichlet L-functions
  -- and bounds on the Gaussian Mellin transform on the critical line.
  -- Mathlib lacks: zero-counting functions N_q(T), zero-free regions,
  -- and the Montgomery-Vaughan zero-density input.
  -- The decomposition into very_low_mass_bound and middle_mass_bound in Decomp269b
  -- reduces this to the quantitative Mellin sum bound hbudget, which is also open.
  sorry

/-- LEAF. Pages 40 to 43, Lemma 4.5, display 4.35 and its use in Proposition 4.6.
This bounds only the zeros above T. The source zero hypothesis is retained.
-/
theorem high_zero_bound (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖highZeros χ δ x T‖ ≤
      log (q * T / (2 * π)) *
        (4.329 * exp (-0.1598 * T) +
          0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) * x := by
  -- BLOCKED OUT OF REACH: requires exponential decay estimates for the Gaussian Mellin
  -- transform and zero-free regions for Dirichlet L-functions above height T.
  -- Mathlib lacks: steepest-descent estimates for the shifted Gaussian,
  -- zero-free region bounds (e.g., Re(s) > 1 - 1/(c log(q|Im(s)|))),
  -- and the quantitative zero-counting in dyadic annuli.
  -- The decomposition in Decomp269c reduces this to tail_mass_integral,
  -- exp_integral_bound, and gaussian_integral_bound, all of which are also open.
  sorry

/-- LEAF. Page 44, the last arithmetic step with the existing factor 6 repair.
The extra 0.01 in the contour coefficient is absorbed into the residue budget for x at least 1.
-/
theorem contour_residue_budget (q δ x : ℝ) (hx : 1 ≤ x) (hδ : 0 ≤ δ) :
    (log q + 6.01) * (1 + 6 * δ) / sqrt x + 3 * log q + 13.347 * δ + 16.695 ≤
      (log q + 6) * (1 + 6 * δ) / sqrt x + 3 * log q + 14 * δ + 17 := by
  have h := div_le_self (show 0 ≤ (0.01 : ℝ) * (1 + 6 * δ) by positivity)
    (one_le_sqrt.mpr hx)
  have hr := Lemma41Terms.repaired_R hδ
  have he : (log q + 6.01) * (1 + 6 * δ) / sqrt x =
      (log q + 6) * (1 + 6 * δ) / sqrt x + 0.01 * (1 + 6 * δ) / sqrt x := by ring
  rw [he]
  linarith

/-- The norm and arithmetic assembly of Proposition 4.6, pages 43 and 44.
CONDITIONAL ON hformula, hL and hH. This proves no analytic component by itself.
-/
theorem gaussian_estimate_of_components (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hformula : ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x)
    (hL : ‖lowZeros χ δ x T‖ ≤
      (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T +
        2.85 * log q + 74.38) * sqrt x)
    (hH : ‖highZeros χ δ x T‖ ≤
      log (q * T / (2 * π)) *
        (4.329 * exp (-0.1598 * T) +
          0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) * x) :
    MajorShape etaHeart χ δ x (gaussianError q δ x T) := by
  obtain ⟨R, hR, hE⟩ := hformula
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < sqrt x := sqrt_pos.mpr hx0
  have hbudget := contour_residue_budget (q : ℝ) |δ| x hx (abs_nonneg δ)
  have htri : ‖Schi etaHeart χ δ x -
      (if q = 1 then fhat etaHeart (-δ) * x else 0)‖ ≤
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ +
        ‖lowZeros χ δ x T‖ + ‖highZeros χ δ x T‖ + ‖R‖ := by
    calc
      _ = ‖(Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
          lowZeros χ δ x T + highZeros χ δ x T + R) -
          lowZeros χ δ x T - highZeros χ δ x T - R‖ := by congr 1; abel
      _ ≤ _ := (norm_sub_le _ _).trans (by
        gcongr
        exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _))
  unfold MajorShape Decomp123.gaussianError
  have heq :
      (log (q * T / (2 * π)) *
          (4.329 * exp (-0.1598 * T) +
            0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) +
        (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) /
          sqrt x + (3 * log q + 14 * |δ| + 17) / x +
        (log q + 6) * (1 + 6 * |δ|) / (x * sqrt x)) * x =
      log (q * T / (2 * π)) *
          (4.329 * exp (-0.1598 * T) +
            0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) * x +
        (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) *
          sqrt x + (3 * log q + 14 * |δ| + 17) +
        (log q + 6) * (1 + 6 * |δ|) / sqrt x := by
    generalize hroot : sqrt x = s
    have hxx : x = s ^ 2 := by rw [← hroot, sq_sqrt hx0.le]
    have hsne : s ≠ 0 := by rw [← hroot]; exact hs0.ne'
    rw [hxx]
    field_simp [hsne]
  rw [heq]
  linarith

/-- Proposition 4.6 with exactly the statement of Decomp123.gaussian_explicit_estimate.
The assembly has no sorry. The three analytic leaves remain OPEN.
-/
theorem gaussian_explicit_estimate (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    MajorShape etaHeart χ δ x (gaussianError q δ x T) := by
  exact gaussian_estimate_of_components x hx q χ δ T
    (explicit_formula_remainder x hx q χ hχ δ T hT hzeros)
    (low_zero_bound x hx q χ hχ δ T hT hzeros)
    (high_zero_bound x hx q χ hχ δ T hT hzeros)

end LeanLab.HelfgottMajor.Decomp269a
