import LeanLab.DERZ1997.Decomp1529a
import LeanLab.DERZ1997.Decomp576b
import LeanLab.DERZ1997.Decomp576c
import LeanLab.DERZ1997.Decomp576d

/-!
Independent supply for primitive_argument_bound370.
The target file is not imported and remains sealed.
Trudgian https://arxiv.org/abs/1206.1844v4 pages 4 to 9.
The split retains real-part powers, Backlund pairing and the right limit.
The constants 6, 1.5 and 0.7 are derived loose budgets, not printed constants.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.DERZ1997.Decomp576a
open Complex Filter Topology MeasureTheory Set Decomp1529a
open scoped ComplexConjugate

/-- Signed horizontal L-function argument divided by pi.
Trudgian page 4, the segment C3 preceding display 2.7, with right endpoint 2.
-/
noncomputable def horizontal576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) : ℝ :=
  (∫ σ in (2 : ℝ)..(1 / 2 : ℝ),
    logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * I)).im / Real.pi

/-- Signed vertical L-function argument divided by pi.
Trudgian page 4, the segment C2 at real part 2.
-/
noncomputable def vertical576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) : ℝ :=
  (I * ∫ t in (-T)..T,
    logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (t : ℂ) * I)).im / Real.pi

/-- The three-segment signed contour argument.
Trudgian page 3 display 2.3 and page 4 segment description.
This is the expanded argument370 definition, without a target-file import.
-/
noncomputable def argument576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) : ℝ :=
  (1 / Real.pi) *
    ((∫ σ in (1 / 2 : ℝ)..2,
      logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) - (T : ℂ) * I)) +
     I * (∫ t in (-T)..T,
      logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (t : ℂ) * I)) +
     (∫ σ in (2 : ℝ)..(1 / 2 : ℝ),
      logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * I))).im

/-- The holomorphic real-part power construction.
Trudgian page 4, display 2.7. Conjugating both the argument and the value gives
an entire second summand for a nonprincipal character.
-/
noncomputable def realPartPower576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  (DirichletCharacter.LFunction χ (s + (T : ℂ) * I) ^ N +
    starRingEnd ℂ (DirichletCharacter.LFunction χ
      (starRingEnd ℂ s + (T : ℂ) * I) ^ N)) / 2

/-- Jensen's mean-log difference divided by twice the power and log-radius.
Trudgian page 7, display 4.3. The fixed parameters are eta equal to one quarter
and p equal to negative one twenty-eighth, so the radius is nine sevenths
and its ratio to the base radius is twelve sevenths, as in page 9 display 4.12.
-/
noncomputable def jensenMass576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) (N : ℕ) : ℝ :=
  ((1 / (2 * Real.pi)) * (∫ φ in (0 : ℝ)..2 * Real.pi,
      Real.log ‖realPartPower576 χ T N
        ((5 / 4 : ℂ) + (9 / 7 : ℂ) * Complex.exp ((φ : ℂ) * I))‖) -
    Real.log ‖realPartPower576 χ T N (5 / 4 : ℂ)‖) /
      (2 * (N : ℝ) * Real.log (12 / 7 : ℝ))

/-- On the real line the analytic power function is the real part of L to that power.
Trudgian page 4, display 2.7.
-/
theorem realPartPower_real576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T σ : ℝ) (N : ℕ) :
    realPartPower576 χ T N (σ : ℂ) =
      (((DirichletCharacter.LFunction χ ((σ : ℂ) + (T : ℂ) * I) ^ N).re : ℝ) : ℂ) := by
  unfold realPartPower576
  rw [Complex.conj_ofReal]
  exact (Complex.re_eq_add_conj _).symm

/-- The real-part power function is entire for a nonprincipal character.
Trudgian page 7, the sentence after display 4.2.
-/
theorem realPartPower_differentiable576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (T : ℝ) (N : ℕ) :
    Differentiable ℂ (realPartPower576 χ T N) := by
  let f : ℂ → ℂ := fun s => DirichletCharacter.LFunction χ (s + (T : ℂ) * I) ^ N
  have hf : Differentiable ℂ f :=
    ((DirichletCharacter.differentiable_LFunction hne).comp
      (differentiable_id.add_const ((T : ℂ) * I))).pow N
  intro s
  have hconj : DifferentiableAt ℂ (fun s => conj (f (conj s))) s := by
    simpa [Function.comp_def] using (hf (conj s)).conj_conj
  change DifferentiableAt ℂ (fun s => (f s + conj (f (conj s))) / 2) s
  exact ((hf s).add hconj).div_const 2

/-- The norm of the analytic real-part power is bounded by the larger shifted norm.
Trudgian pages 7 and 8, displays 4.5 and 4.7, before logarithmic integration.
Both shifted values are retained for complex characters.
-/
theorem realPartPower_norm576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) (N : ℕ) (s : ℂ) :
    ‖realPartPower576 χ T N s‖ ≤
      (max ‖DirichletCharacter.LFunction χ (s + (T : ℂ) * I)‖
        ‖DirichletCharacter.LFunction χ (conj s + (T : ℂ) * I)‖) ^ N := by
  let a := DirichletCharacter.LFunction χ (s + (T : ℂ) * I)
  let b := DirichletCharacter.LFunction χ (conj s + (T : ℂ) * I)
  have h1 : ‖a‖ ^ N ≤ (max ‖a‖ ‖b‖) ^ N :=
    pow_le_pow_left₀ (norm_nonneg a) (le_max_left _ _) N
  have h2 : ‖b‖ ^ N ≤ (max ‖a‖ ‖b‖) ^ N :=
    pow_le_pow_left₀ (norm_nonneg b) (le_max_right _ _) N
  change ‖(a ^ N + conj (b ^ N)) / 2‖ ≤ (max ‖a‖ ‖b‖) ^ N
  rw [norm_div]
  norm_num only [norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have htri := norm_add_le (a ^ N) (conj (b ^ N))
  simp only [norm_pow, RCLike.norm_conj] at htri
  linarith

/-- The contour is the bottom variation, vertical variation and top variation.
Trudgian pages 3 and 4, display 2.3 and the oriented segment description.
-/
theorem argument_segments576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    argument576 χ T = -horizontal576 χ (-T) + vertical576 χ T + horizontal576 χ T := by
  unfold argument576 horizontal576 vertical576
  simp only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg]
  rw [intervalIntegral.integral_symm (a := (2 : ℝ)) (b := 1 / 2)]
  simp only [Complex.add_im, Complex.neg_im]
  ring

/-- LEAF. Backlund pairing turns the real-part power Jensen mass into a horizontal
signed argument bound. Trudgian pages 4 to 7, displays 2.7, 2.8, 3.9 and 4.2 to 4.3.
The geometric product inputs are proved in Decomp576b. The loose additive budget
1.5 covers the Gamma reflection error and moving the right endpoint to 2.
No assertion about a right limit or the other contour segments is made here.
-/
theorem horizontal_of_jensen576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {T : ℝ} (hT : 1 ≤ |T|)
    (hgood : ∀ σ ∈ Icc (1 / 2 : ℝ) 2,
      DirichletCharacter.LFunction χ ((σ : ℂ) + (T : ℂ) * I) ≠ 0)
    (N : ℕ → ℕ) (hN : StrictMono N)
    (hcentre : Tendsto (fun k =>
      (DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + (T : ℂ) * I) ^ N k).re /
        ‖DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + (T : ℂ) * I)‖ ^ N k)
      atTop (𝓝 1))
    {B : ℝ} (hB : ∀ ε > 0, ∀ᶠ k in atTop, jensenMass576 χ T (N k) ≤ B + ε) :
    |horizontal576 χ T| ≤ B + 1.5 := by
  sorry

/-- LEAF. Rademacher's convexity estimate in the symmetric strip.
Trudgian page 8, display 4.6, citing Rademacher Theorem 3.
This is a modulus bound only, with no Jensen count or contour argument.
-/
theorem primitive_convexity576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) (s : ℂ)
    (hs0 : -η ≤ s.re) (hs1 : s.re ≤ 1 + η) :
    ‖DirichletCharacter.LFunction χ s‖ ≤
      ((q : ℝ) * ‖s + 1‖ / (2 * Real.pi)) ^ ((1 + η - s.re) / 2) *
        (riemannZeta ((1 + η : ℝ) : ℂ)).re := by
  sorry

/-- LEAF. Convexity bounds the mean log on the real-part power Jensen circle.
Trudgian pages 7 to 9, displays 4.4 to 4.9 and 4.12, at eta equal to one quarter
and p equal to negative one twenty-eighth. The derived budget 6 is deliberately
loose. This is an estimate for Jensen mass, not for zeros of L or its argument.
-/
theorem jensen_mass_bound576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {T : ℝ} (hT : 1 ≤ |T|) (N : ℕ → ℕ) (hN : StrictMono N)
    (hcentre : Tendsto (fun k =>
      (DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + (T : ℂ) * I) ^ N k).re /
        ‖DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + (T : ℂ) * I)‖ ^ N k)
      atTop (𝓝 1))
    (hconv : ∀ (η : ℝ), 0 < η → η ≤ 1 / 2 → ∀ (s : ℂ),
      -η ≤ s.re → s.re ≤ 1 + η →
      ‖DirichletCharacter.LFunction χ s‖ ≤
        ((q : ℝ) * ‖s + 1‖ / (2 * Real.pi)) ^ ((1 + η - s.re) / 2) *
          (riemannZeta ((1 + η : ℝ) : ℂ)).re) :
    ∀ ε > 0, ∀ᶠ k in atTop,
      jensenMass576 χ T (N k) ≤ 0.25 * Real.log ((q : ℝ) * |T|) + 6 + ε := by
  sorry

/-- The vertical signed variation is bounded by the absolutely convergent
Euler-product logarithm. Trudgian page 4, the bound for C2 before display 2.7.
At real part 2, twice log zeta of 2 divided by pi is less than the loose budget 0.7.
-/
theorem vertical_bound576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {T : ℝ} (hT : 1 ≤ T) :
    |vertical576 χ T| ≤ 0.7 := by
  exact (Decomp576d.vertical_half_bound576 χ T).trans (by norm_num)


/-! ### Helpers for the right limit of the contour argument
Trudgian pages 3 to 9, displays 2.3, 2.8, 4.2 to 4.12. These are the tube
bounds, the Poisson kernel limits and the dominated convergence steps used
to pass the three segment integrals to the right limit. -/

namespace Decomp576aWip

open Filter Topology MeasureTheory intervalIntegral Set Complex
open LeanLab.DERZ1997.Decomp1529a LeanLab.DERZ1997.Decomp576a

/-! ### Poisson kernel integrals on an interval -/

/-- Antiderivative of a shifted Poisson kernel. -/
private lemma hasDerivAt_arctan_shift {eps c : ℝ} (heps : eps ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.arctan ((y - c) / eps)) (eps / ((x - c) ^ 2 + eps ^ 2)) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y - c) / eps) (1 / eps) x := by
    simpa using ((hasDerivAt_id x).sub_const c).div_const eps
  have h2 : HasDerivAt (fun y : ℝ => Real.arctan ((y - c) / eps))
      (1 / (1 + ((x - c) / eps) ^ 2) * (1 / eps)) x := by
    simpa [Function.comp_def] using (Real.hasDerivAt_arctan ((x - c) / eps)).comp x h1
  have h3 : eps / ((x - c) ^ 2 + eps ^ 2) = 1 / (1 + ((x - c) / eps) ^ 2) * (1 / eps) := by
    field_simp
    ring
  rw [h3]
  exact h2

/-- The Poisson kernel integrates to the difference of two arctangents. -/
theorem integral_kernel_interval {a b c eps : ℝ} (heps : eps ≠ 0) :
    (∫ σ in a..b, eps / ((σ - c) ^ 2 + eps ^ 2))
      = Real.arctan ((b - c) / eps) - Real.arctan ((a - c) / eps) := by
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => Real.arctan ((y - c) / eps)) (eps / ((x - c) ^ 2 + eps ^ 2)) x :=
    fun x _ => hasDerivAt_arctan_shift heps x
  have hcont : Continuous fun x : ℝ => eps / ((x - c) ^ 2 + eps ^ 2) := by
    have hbase : Continuous fun x : ℝ => (x - c) ^ 2 + eps ^ 2 := by fun_prop
    refine Continuous.div continuous_const hbase ?_
    intro x
    have hpos : 0 < (x - c) ^ 2 + eps ^ 2 := by positivity
    exact hpos.ne'
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)

/-- `x / eps` tends to `+∞` as `eps` tends to zero from above, for `x > 0`. -/
theorem tendsto_div_eps_atTop {x : ℝ} (hx : 0 < x) :
    Tendsto (fun eps : ℝ => x / eps) (𝓝[>] (0 : ℝ)) atTop := by
  have hinv : Tendsto (fun eps : ℝ => eps⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
  have hmul : Tendsto (fun eps : ℝ => x * eps⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    (tendsto_const_mul_atTop_of_pos (f := fun eps : ℝ => eps⁻¹) hx).mpr hinv
  simpa [div_eq_mul_inv] using hmul

/-- `x / eps` tends to `-∞` as `eps` tends to zero from below, for `x > 0`. -/
theorem tendsto_div_eps_atBot {x : ℝ} (hx : 0 < x) :
    Tendsto (fun eps : ℝ => x / eps) (𝓝[<] (0 : ℝ)) atBot := by
  have hinv : Tendsto (fun eps : ℝ => eps⁻¹) (𝓝[<] (0 : ℝ)) atBot := tendsto_inv_nhdsLT_zero
  have hmul : Tendsto (fun eps : ℝ => x * eps⁻¹) (𝓝[<] (0 : ℝ)) atBot :=
    (tendsto_const_mul_atBot_of_pos (f := fun eps : ℝ => eps⁻¹) hx).mpr hinv
  simpa [div_eq_mul_inv] using hmul

/-- The signed full kernel has limit `-m * π` when the pole is strictly inside. -/
theorem tendsto_pole_integral_interior {a b c m : ℝ} (hac : a < c) (hcb : c < b) :
    Tendsto (fun eps : ℝ => ∫ σ in a..b, -(m * (eps / ((σ - c) ^ 2 + eps ^ 2))))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(m * Real.pi))) := by
  have hbc : 0 < b - c := by linarith
  have hca : 0 < c - a := by linarith
  have h1 : Tendsto (fun eps : ℝ => Real.arctan ((b - c) / eps))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
      (tendsto_div_eps_atTop hbc)
  have h2p : Tendsto (fun eps : ℝ => Real.arctan ((c - a) / eps))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
      (tendsto_div_eps_atTop hca)
  have h2 : Tendsto (fun eps : ℝ => Real.arctan ((a - c) / eps))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(Real.pi / 2))) := by
    have heq : (fun eps : ℝ => Real.arctan ((a - c) / eps))
        = (fun eps : ℝ => -Real.arctan ((c - a) / eps)) := by
      funext eps
      rw [show a - c = -(c - a) by ring, neg_div, Real.arctan_neg]
    rw [heq]
    exact h2p.neg
  have h3 : Tendsto
      (fun eps : ℝ => -(m * (Real.arctan ((b - c) / eps) - Real.arctan ((a - c) / eps))))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(m * (Real.pi / 2 - -(Real.pi / 2))))) :=
    ((h1.sub h2).const_mul m).neg
  have h4 : -(m * (Real.pi / 2 - -(Real.pi / 2))) = -(m * Real.pi) := by ring
  rw [h4] at h3
  refine Tendsto.congr' ?_ h3
  filter_upwards [self_mem_nhdsWithin] with eps heps
  have hpos : 0 < eps := heps
  rw [show (fun σ : ℝ => -(m * (eps / ((σ - c) ^ 2 + eps ^ 2))))
      = (fun σ : ℝ => (-m) * (eps / ((σ - c) ^ 2 + eps ^ 2))) from by funext σ; ring]
  rw [intervalIntegral.integral_const_mul, integral_kernel_interval hpos.ne']
  ring

/-- The signed half kernel has limit `-m * π / 2` at the left endpoint. -/
theorem tendsto_pole_integral_edge_left {a b m : ℝ} (hab : a < b) :
    Tendsto (fun eps : ℝ => ∫ σ in a..b, -(m * (eps / ((σ - a) ^ 2 + eps ^ 2))))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(m * (Real.pi / 2)))) := by
  have hba : 0 < b - a := by linarith
  have h1 : Tendsto (fun eps : ℝ => Real.arctan ((b - a) / eps))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
      (tendsto_div_eps_atTop hba)
  have h2 : Tendsto (fun eps : ℝ => Real.arctan ((a - a) / eps)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hzero : (fun eps : ℝ => Real.arctan ((a - a) / eps)) = fun _ => (0 : ℝ) := by
      funext eps
      simp
    rw [hzero]
    exact tendsto_const_nhds
  have h3 : Tendsto
      (fun eps : ℝ => -(m * (Real.arctan ((b - a) / eps) - Real.arctan ((a - a) / eps))))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(m * (Real.pi / 2 - 0)))) :=
    ((h1.sub h2).const_mul m).neg
  have h4 : -(m * (Real.pi / 2 - 0)) = -(m * (Real.pi / 2)) := by ring
  rw [h4] at h3
  refine Tendsto.congr' ?_ h3
  filter_upwards [self_mem_nhdsWithin] with eps heps
  have hpos : 0 < eps := heps
  rw [show (fun σ : ℝ => -(m * (eps / ((σ - a) ^ 2 + eps ^ 2))))
      = (fun σ : ℝ => (-m) * (eps / ((σ - a) ^ 2 + eps ^ 2))) from by funext σ; ring]
  rw [intervalIntegral.integral_const_mul, integral_kernel_interval hpos.ne']
  ring

/-- The signed full kernel has limit `m * π` from below when the pole is strictly inside. -/
theorem tendsto_pole_integral_interior_left {a b c m : ℝ} (hac : a < c) (hcb : c < b) :
    Tendsto (fun eps : ℝ => ∫ σ in a..b, -(m * (eps / ((σ - c) ^ 2 + eps ^ 2))))
      (𝓝[<] (0 : ℝ)) (𝓝 (m * Real.pi)) := by
  have hbc : 0 < b - c := by linarith
  have hca : 0 < c - a := by linarith
  have h1 : Tendsto (fun eps : ℝ => Real.arctan ((b - c) / eps))
      (𝓝[<] (0 : ℝ)) (𝓝 (-(Real.pi / 2))) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp
      (tendsto_div_eps_atBot hbc)
  have h2p : Tendsto (fun eps : ℝ => Real.arctan ((c - a) / eps))
      (𝓝[<] (0 : ℝ)) (𝓝 (-(Real.pi / 2))) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp
      (tendsto_div_eps_atBot hca)
  have h2 : Tendsto (fun eps : ℝ => Real.arctan ((a - c) / eps))
      (𝓝[<] (0 : ℝ)) (𝓝 (Real.pi / 2)) := by
    have heq : (fun eps : ℝ => Real.arctan ((a - c) / eps))
        = (fun eps : ℝ => -Real.arctan ((c - a) / eps)) := by
      funext eps
      rw [show a - c = -(c - a) by ring, neg_div, Real.arctan_neg]
    rw [heq]
    simpa using h2p.neg
  have h3 : Tendsto
      (fun eps : ℝ => -(m * (Real.arctan ((b - c) / eps) - Real.arctan ((a - c) / eps))))
      (𝓝[<] (0 : ℝ)) (𝓝 (-(m * (-(Real.pi / 2) - Real.pi / 2)))) :=
    ((h1.sub h2).const_mul m).neg
  have h4 : -(m * (-(Real.pi / 2) - Real.pi / 2)) = m * Real.pi := by ring
  rw [h4] at h3
  refine Tendsto.congr' ?_ h3
  filter_upwards [self_mem_nhdsWithin] with eps heps
  have hne : eps ≠ 0 := heps.ne
  rw [show (fun σ : ℝ => -(m * (eps / ((σ - c) ^ 2 + eps ^ 2))))
      = (fun σ : ℝ => (-m) * (eps / ((σ - c) ^ 2 + eps ^ 2))) from by funext σ; ring]
  rw [intervalIntegral.integral_const_mul, integral_kernel_interval hne]
  ring

/-- The signed half kernel has limit `m * π / 2` from below at the left endpoint. -/
theorem tendsto_pole_integral_edge_left' {a b m : ℝ} (hab : a < b) :
    Tendsto (fun eps : ℝ => ∫ σ in a..b, -(m * (eps / ((σ - a) ^ 2 + eps ^ 2))))
      (𝓝[<] (0 : ℝ)) (𝓝 (m * (Real.pi / 2))) := by
  have hba : 0 < b - a := by linarith
  have h1 : Tendsto (fun eps : ℝ => Real.arctan ((b - a) / eps))
      (𝓝[<] (0 : ℝ)) (𝓝 (-(Real.pi / 2))) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp
      (tendsto_div_eps_atBot hba)
  have h2 : Tendsto (fun eps : ℝ => Real.arctan ((a - a) / eps)) (𝓝[<] (0 : ℝ)) (𝓝 0) := by
    have hzero : (fun eps : ℝ => Real.arctan ((a - a) / eps)) = fun _ => (0 : ℝ) := by
      funext eps
      simp
    rw [hzero]
    exact tendsto_const_nhds
  have h3 : Tendsto
      (fun eps : ℝ => -(m * (Real.arctan ((b - a) / eps) - Real.arctan ((a - a) / eps))))
      (𝓝[<] (0 : ℝ)) (𝓝 (-(m * (-(Real.pi / 2) - 0)))) :=
    ((h1.sub h2).const_mul m).neg
  have h4 : -(m * (-(Real.pi / 2) - 0)) = m * (Real.pi / 2) := by ring
  rw [h4] at h3
  refine Tendsto.congr' ?_ h3
  filter_upwards [self_mem_nhdsWithin] with eps heps
  have hne : eps ≠ 0 := heps.ne
  rw [show (fun σ : ℝ => -(m * (eps / ((σ - a) ^ 2 + eps ^ 2))))
      = (fun σ : ℝ => (-m) * (eps / ((σ - a) ^ 2 + eps ^ 2))) from by funext σ; ring]
  rw [intervalIntegral.integral_const_mul, integral_kernel_interval hne]
  ring

/-- The imaginary part of a model pole on a horizontal line is a shifted Poisson kernel. -/
theorem im_model_pole576 {m : ℝ} (ρ : ℂ) (x t : ℝ) :
    ((m : ℂ) / (((x : ℂ) + (t : ℂ) * I) - ρ)).im
      = -(m * ((t - ρ.im) / ((x - ρ.re) ^ 2 + (t - ρ.im) ^ 2))) := by
  have hre : (((x : ℂ) + (t : ℂ) * I) - ρ).re = x - ρ.re := by simp
  have him : (((x : ℂ) + (t : ℂ) * I) - ρ).im = t - ρ.im := by simp
  rw [Complex.div_im, hre, him, Complex.normSq_apply, hre, him]
  simp only [Complex.ofReal_im, Complex.ofReal_re, zero_mul]
  field_simp
  ring

/-- The imaginary part of an interval integral is the integral of the imaginary parts. -/
theorem intervalIntegral_im {f : ℝ → ℂ} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x).im = ∫ x in a..b, (f x).im := by
  have h := Complex.imCLM.intervalIntegral_comp_comm (μ := volume) (f := f) (a := a) (b := b) hf
  simpa using h.symm

/-- The real part of an interval integral is the integral of the real parts. -/
theorem intervalIntegral_re {f : ℝ → ℂ} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x).re = ∫ x in a..b, (f x).re := by
  have h := Complex.reCLM.intervalIntegral_comp_comm (μ := volume) (f := f) (a := a) (b := b) hf
  simpa using h.symm


/-- The logarithmic derivative near an isolated zero, with the vanishing order
carried as a natural number. -/
theorem exists_logDeriv_factor576' {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (hfin : analyticOrderAt f ρ ≠ ⊤) :
    ∃ (n : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] ρ, logDeriv f z = (n : ℂ) / (z - ρ) + logDeriv g z := by
  have hnv : ¬ ∀ᶠ z in 𝓝 ρ, f z = 0 := fun hzero =>
    hfin (analyticOrderAt_eq_top.mpr hzero)
  obtain ⟨n, g, hg, hg0, hfeq⟩ := AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff hf |>.mpr hnv
  have hsmul : f =ᶠ[𝓝 ρ] (fun z => (z - ρ) ^ n * g z) := by
    filter_upwards [hfeq] with z hz
    simpa [smul_eq_mul] using hz
  refine ⟨n, g, hg, hg0, ?_⟩
  obtain ⟨U, hU, hUeq⟩ := Filter.eventually_iff_exists_mem.mp hsmul
  have hUnb : interior U ∈ 𝓝 ρ := interior_mem_nhds.mpr hU
  have hUeq' : ∀ z ∈ interior U, f z = (z - ρ) ^ n * g z :=
    fun z hz => hUeq z (interior_subset hz)
  have hgne : ∀ᶠ z in 𝓝 ρ, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  have hgdiff : ∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ g z :=
    hg.eventually_analyticAt.mono fun _ hw => hw.differentiableAt
  filter_upwards [nhdsWithin_le_nhds hUnb, nhdsWithin_le_nhds hgne,
    nhdsWithin_le_nhds hgdiff, self_mem_nhdsWithin] with z hzU hgz hgdz hzρ
  have hval : f z = (z - ρ) ^ n * g z := hUeq' z hzU
  have heqNear : f =ᶠ[𝓝 z] (fun w => (w - ρ) ^ n * g w) :=
    Filter.eventually_of_mem (isOpen_interior.mem_nhds hzU) hUeq'
  have hpow : logDeriv (fun w : ℂ => (w - ρ) ^ n) z = (n : ℂ) / (z - ρ) := by
    have hd : DifferentiableAt ℂ (fun w : ℂ => w - ρ) z := differentiableAt_id.sub_const ρ
    have hp := logDeriv_fun_pow (f := fun w : ℂ => w - ρ) (x := z) hd n
    have hid : logDeriv (fun w : ℂ => w - ρ) z = 1 / (z - ρ) := by
      simp [logDeriv_apply]
    rw [hp, hid, mul_one_div]
  have hprod : logDeriv (fun w : ℂ => (w - ρ) ^ n * g w) z
      = (n : ℂ) / (z - ρ) + logDeriv g z := by
    have hmul' : logDeriv (fun w : ℂ => (w - ρ) ^ n * g w) z
        = logDeriv (fun w : ℂ => (w - ρ) ^ n) z + logDeriv g z :=
      logDeriv_mul (f := fun w : ℂ => (w - ρ) ^ n) (g := g) z
        (pow_ne_zero n (sub_ne_zero.mpr hzρ)) hgz
        ((differentiableAt_id.sub_const ρ).pow n) hgdz
    rw [hmul', hpow]
  have hfl : logDeriv f z = logDeriv (fun w : ℂ => (w - ρ) ^ n * g w) z := by
    simp only [logDeriv_apply]
    rw [Filter.EventuallyEq.deriv_eq heqNear, hval]
  rw [hfl, hprod]

/-! ### Continuity of a parameter integral on a tube -/

/-- The horizontal slice of a jointly continuous tube integrand is continuous. -/
theorem continuousOn_slice_of_continuousOn {F : ℝ → ℝ → ℝ} {a b T δ t : ℝ}
    (ht : |t - T| < δ)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc (T - δ) (T + δ) ×ˢ uIcc a b)) :
    ContinuousOn (F t) (uIcc a b) := by
  have ht1 := (abs_lt.mp ht).1
  have ht2 := (abs_lt.mp ht).2
  have hg : ContinuousOn (fun σ : ℝ => (t, σ)) (uIcc a b) := by fun_prop
  have hmaps : MapsTo (fun σ : ℝ => (t, σ)) (uIcc a b)
      (Icc (T - δ) (T + δ) ×ˢ uIcc a b) := by
    intro σ hσ
    exact ⟨⟨by linarith, by linarith⟩, hσ⟩
  have h := hcont.comp hg hmaps
  simpa [Function.comp_def] using h

/-- If the integrand is jointly continuous on a tube around the segment, the
parameter integral is continuous at the base height. -/
theorem continuousAt_integral_of_continuousOn {F : ℝ → ℝ → ℝ} {a b T δ : ℝ} (hδ : 0 < δ)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Icc (T - δ) (T + δ) ×ˢ uIcc a b)) :
    ContinuousAt (fun t : ℝ => ∫ σ in a..b, F t σ) T := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn hcont
  have hnear : ∀ᶠ t : ℝ in 𝓝 T, |t - T| < δ := by
    filter_upwards [Metric.ball_mem_nhds T hδ] with t ht
    rw [Metric.mem_ball, Real.dist_eq] at ht
    exact ht
  refine intervalIntegral.continuousAt_of_dominated_interval
    (F := fun (t : ℝ) (σ : ℝ) => F t σ) (x₀ := T) (bound := fun _ => C) (a := a) (b := b)
    (μ := volume) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [hnear] with t ht
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    exact (continuousOn_slice_of_continuousOn ht hcont).mono Set.uIoc_subset_uIcc
  · filter_upwards [hnear] with t ht
    have ht1 := (abs_lt.mp ht).1
    have ht2 := (abs_lt.mp ht).2
    refine Eventually.of_forall fun σ hσ => ?_
    exact hC (t, σ) ⟨⟨by linarith, by linarith⟩, Set.uIoc_subset_uIcc hσ⟩
  · refine Eventually.of_forall fun σ hσ => ?_
    have hmem : (T, σ) ∈ Icc (T - δ) (T + δ) ×ˢ uIcc a b :=
      ⟨⟨by linarith, by linarith⟩, Set.uIoc_subset_uIcc hσ⟩
    have hpair : Tendsto (fun x : ℝ => (x, σ)) (𝓝 T)
        (𝓝[Icc (T - δ) (T + δ) ×ˢ uIcc a b] (T, σ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨(by fun_prop : ContinuousAt (fun x : ℝ => (x, σ)) T).tendsto, ?_⟩
      filter_upwards [hnear] with x hx
      exact ⟨⟨by linarith [(abs_lt.mp hx).1], by linarith [(abs_lt.mp hx).2]⟩,
        Set.uIoc_subset_uIcc hσ⟩
    have hcomp : ContinuousAt ((fun p : ℝ × ℝ => F p.1 p.2) ∘ (fun x : ℝ => (x, σ))) T :=
      Filter.Tendsto.comp (hcont.continuousWithinAt hmem) hpair
    exact hcomp


/-! ### The remainder after subtracting the model poles -/

/-- A continuous function is bounded on a neighbourhood of its centre. -/
theorem exists_bound_nhds_of_continuousAt {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (h : ContinuousAt F p) :
    ∃ U ∈ 𝓝 p, ∃ C : ℝ, ∀ q ∈ U, ‖F q‖ ≤ C := by
  obtain ⟨eps, heps, hball⟩ := (Metric.continuousAt_iff.mp h) 1 one_pos
  refine ⟨Metric.ball p eps, Metric.ball_mem_nhds p heps, ‖F p‖ + 1, fun q hq => ?_⟩
  have h1 : dist (F q) (F p) < 1 := hball hq
  have h2 : ‖F q‖ - ‖F p‖ ≤ ‖F q - F p‖ := norm_sub_norm_le _ _
  have h3 : dist (F q) (F p) = ‖F q - F p‖ := dist_eq_norm _ _
  rw [h3] at h1
  linarith

/-- Away from the finite zero list the subtracted remainder is continuous. -/
theorem continuousAt_remainder {a b T δ : ℝ} (hab : a ≤ b)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (s : Finset ℂ) (ord : ℂ → ℕ) (R : ℝ × ℝ → ℝ)
    (hcover : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → |z.im - T| ≤ δ → f z = 0 → z ∈ s)
    (hR : ∀ p : ℝ × ℝ, R p = (logDeriv f ((p.1 : ℂ) + (p.2 : ℂ) * I)).im -
      ∑ ρ ∈ s, (((ord ρ : ℂ) / (((p.1 : ℂ) + (p.2 : ℂ) * I) - ρ)).im))
    {p : ℝ × ℝ} (hp1 : p.1 ∈ uIcc a b) (hp2 : p.2 ∈ Icc (T - δ) (T + δ))
    (hpz : ((p.1 : ℂ) + (p.2 : ℂ) * I) ∉ (s : Set ℂ)) :
    ContinuousAt R p := by
  rw [uIcc_of_le hab] at hp1
  have him : (((p.1 : ℂ) + (p.2 : ℂ) * I)).im = p.2 := by simp
  have hfz : f ((p.1 : ℂ) + (p.2 : ℂ) * I) ≠ 0 := by
    intro h0
    refine hpz (hcover _ (by simpa using hp1.1) (by simpa using hp1.2) ?_ h0)
    rw [him, abs_le]
    exact ⟨by linarith [hp2.1], by linarith [hp2.2]⟩
  have hld : ContinuousAt (logDeriv f) ((p.1 : ℂ) + (p.2 : ℂ) * I) := by
    have hd : ContinuousAt (deriv f) ((p.1 : ℂ) + (p.2 : ℂ) * I) :=
      ((hf.analyticAt _).deriv).continuousAt
    have hc : ContinuousAt f ((p.1 : ℂ) + (p.2 : ℂ) * I) := hf.continuous.continuousAt
    simpa [logDeriv] using hd.div hc hfz
  have hzfun : ContinuousAt (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) p := by fun_prop
  have hcomp : ContinuousAt (fun p : ℝ × ℝ => logDeriv f ((p.1 : ℂ) + (p.2 : ℂ) * I)) p := by
    have hcomp' : ContinuousAt ((fun z : ℂ => logDeriv f z) ∘
        (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I)) p :=
      ContinuousAt.comp hld hzfun
    simpa [Function.comp_def] using hcomp'
  have h1 : ContinuousAt (fun p : ℝ × ℝ => (logDeriv f ((p.1 : ℂ) + (p.2 : ℂ) * I)).im) p := by
    have h2' : ContinuousAt ((fun z : ℂ => (logDeriv f z).im) ∘
        (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I)) p :=
      ContinuousAt.comp (Complex.continuous_im.continuousAt.comp hld) hzfun
    simpa [Function.comp_def] using h2'
  have h2 : ContinuousAt (fun p : ℝ × ℝ =>
      ∑ ρ ∈ s, (((ord ρ : ℂ) / (((p.1 : ℂ) + (p.2 : ℂ) * I) - ρ)).im)) p := by
    refine tendsto_finsetSum s ?_
    intro ρ hρ
    have hne : ((p.1 : ℂ) + (p.2 : ℂ) * I) - ρ ≠ 0 := by
      intro h0
      have hz : ((p.1 : ℂ) + (p.2 : ℂ) * I) = ρ := sub_eq_zero.mp h0
      exact hpz (by rw [hz]; exact hρ)
    have hsub : ContinuousAt (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * I) - ρ) p := by fun_prop
    have hdiv : ContinuousAt (fun p : ℝ × ℝ =>
        ((ord ρ : ℂ) / (((p.1 : ℂ) + (p.2 : ℂ) * I) - ρ))) p := by
      have hcomp' : ContinuousAt ((fun z : ℂ => ((ord ρ : ℂ)) / z) ∘
          (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * I) - ρ)) p :=
        ContinuousAt.comp (continuousAt_const.div continuousAt_id hne) hsub
      simpa [Function.comp_def] using hcomp'
    have hfin : ContinuousAt ((fun z : ℂ => z.im) ∘
        (fun p : ℝ × ℝ => ((ord ρ : ℂ) / (((p.1 : ℂ) + (p.2 : ℂ) * I) - ρ)))) p :=
      ContinuousAt.comp Complex.continuous_im.continuousAt hdiv
    exact hfin
  have hgoal : R = fun p : ℝ × ℝ => (logDeriv f ((p.1 : ℂ) + (p.2 : ℂ) * I)).im -
      ∑ ρ ∈ s, (((ord ρ : ℂ) / (((p.1 : ℂ) + (p.2 : ℂ) * I) - ρ)).im) := funext hR
  rw [hgoal]
  exact h1.sub h2

/-- At a zero of the list the subtracted remainder is locally bounded: the model
pole of that zero cancels and only the zero-free factor survives. -/
theorem locallyBounded_remainder_at_zero
    (f : ℂ → ℂ) (s : Finset ℂ) (ord : ℂ → ℕ) (g : ℂ → ℂ → ℂ) (R : ℝ × ℝ → ℝ)
    (hR : ∀ p : ℝ × ℝ, R p = (logDeriv f ((p.1 : ℂ) + (p.2 : ℂ) * I)).im -
      ∑ ρ ∈ s, (((ord ρ : ℂ) / (((p.1 : ℂ) + (p.2 : ℂ) * I) - ρ)).im))
    {ρ : ℂ} (hρ : ρ ∈ s)
    (hfac : AnalyticAt ℂ (g ρ) ρ ∧ (g ρ) ρ ≠ 0 ∧
      (∀ᶠ z in 𝓝[≠] ρ, logDeriv f z = (ord ρ : ℂ) / (z - ρ) + logDeriv (g ρ) z)) :
    ∃ U ∈ 𝓝 ((ρ.re, ρ.im) : ℝ × ℝ), ∃ C : ℝ, ∀ q ∈ U, ‖R q‖ ≤ C := by
  classical
  obtain ⟨hgan, hgne, hfacq⟩ := hfac
  set A : ℂ → ℝ := fun z => (logDeriv (g ρ) z).im -
    ∑ μ ∈ s.erase ρ, (((ord μ : ℂ) / (z - μ)).im) with hA
  have hAcont : ContinuousAt A ρ := by
    have hld : ContinuousAt (logDeriv (g ρ)) ρ := by
      have hd : ContinuousAt (deriv (g ρ)) ρ := hgan.deriv.continuousAt
      have hc : ContinuousAt (g ρ) ρ := hgan.continuousAt
      simpa [logDeriv] using hd.div hc hgne
    have hsum : ContinuousAt (fun z : ℂ => ∑ μ ∈ s.erase ρ, (((ord μ : ℂ) / (z - μ)).im)) ρ := by
      refine tendsto_finsetSum _ ?_
      intro μ hμ
      have hne : ρ - μ ≠ 0 := by
        intro h0
        exact (Finset.ne_of_mem_erase hμ) (sub_eq_zero.mp h0).symm
      exact Complex.continuous_im.continuousAt.comp
        (continuousAt_const.div (by fun_prop : ContinuousAt (fun z : ℂ => z - μ) ρ) hne)
    exact (Complex.continuous_im.continuousAt.comp hld).sub hsum
  obtain ⟨epsA, hepsA, hballA⟩ : ∃ epsA > 0, ∀ w : ℂ, dist w ρ < epsA → ‖A w‖ ≤ ‖A ρ‖ + 1 := by
    obtain ⟨eps, heps, hb⟩ := (Metric.continuousAt_iff.mp hAcont) 1 one_pos
    refine ⟨eps, heps, fun w hw => ?_⟩
    have h1 : dist (A w) (A ρ) < 1 := hb hw
    have h2 : ‖A w‖ - ‖A ρ‖ ≤ ‖A w - A ρ‖ := norm_sub_norm_le _ _
    have h3 : dist (A w) (A ρ) = ‖A w - A ρ‖ := dist_eq_norm _ _
    rw [h3] at h1
    linarith
  have hVmem : Metric.ball ρ epsA ∈ 𝓝 ρ := Metric.ball_mem_nhds ρ hepsA
  have hCV : ∀ w ∈ Metric.ball ρ epsA, ‖A w‖ ≤ ‖A ρ‖ + 1 := hballA
  obtain ⟨W, hW, hWeq⟩ := Filter.eventually_iff_exists_mem.mp hfacq
  obtain ⟨W0, hW0mem, hW0sub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hW
  refine ⟨{q : ℝ × ℝ | (q.1 : ℂ) + (q.2 : ℂ) * I ∈ Metric.ball ρ epsA ∩ W0}, ?_,
    max (‖A ρ‖ + 1) ‖R (ρ.re, ρ.im)‖, ?_⟩
  · have hcont : ContinuousAt (fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * I) (ρ.re, ρ.im) := by
      fun_prop
    have hpt : ((ρ.re : ℂ) + (ρ.im : ℂ) * I) = ρ := by
      apply Complex.ext <;> simp
    have hmem : Metric.ball ρ epsA ∩ W0 ∈ 𝓝 ρ := Filter.inter_mem hVmem hW0mem
    exact hcont.preimage_mem_nhds (by rwa [hpt])
  · intro q hq
    have hqV : (q.1 : ℂ) + (q.2 : ℂ) * I ∈ Metric.ball ρ epsA := hq.1
    have hAb : ‖A ((q.1 : ℂ) + (q.2 : ℂ) * I)‖ ≤ ‖A ρ‖ + 1 := hCV _ hqV
    by_cases hz : (q.1 : ℂ) + (q.2 : ℂ) * I = ρ
    · have hq1 : q.1 = ρ.re := by simpa using congrArg Complex.re hz
      have hq2 : q.2 = ρ.im := by simpa using congrArg Complex.im hz
      have hqeq : q = (ρ.re, ρ.im) := Prod.ext hq1 hq2
      rw [hqeq]
      exact le_max_right _ _
    · have hzW : (q.1 : ℂ) + (q.2 : ℂ) * I ∈ W := by
        refine hW0sub ⟨hq.2, ?_⟩
        simpa using hz
      have hseq := hWeq _ hzW
      have herase : ∑ μ ∈ s, (((ord μ : ℂ) / ((q.1 : ℂ) + (q.2 : ℂ) * I - μ)).im)
          = (((ord ρ : ℂ) / ((q.1 : ℂ) + (q.2 : ℂ) * I - ρ)).im)
            + ∑ μ ∈ s.erase ρ, (((ord μ : ℂ) / ((q.1 : ℂ) + (q.2 : ℂ) * I - μ)).im) :=
        (Finset.add_sum_erase s
          (fun μ => (((ord μ : ℂ) / ((q.1 : ℂ) + (q.2 : ℂ) * I - μ)).im)) hρ).symm
      have hRq : R q = A ((q.1 : ℂ) + (q.2 : ℂ) * I) := by
        rw [hR q, hseq, Complex.add_im, herase]
        simp only [hA]
        ring
      rw [hRq]
      exact hAb.trans (le_max_left _ _)

/-- Locally bounded on a compact set implies bounded. -/
theorem exists_bound_of_locallyBounded {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    {F : ℝ × ℝ → ℝ}
    (h : ∀ p ∈ K, ∃ U : Set (ℝ × ℝ), IsOpen U ∧ p ∈ U ∧ ∃ C : ℝ, ∀ q ∈ U, ‖F q‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ‖F p‖ ≤ C := by
  classical
  have h' : ∀ p : K, ∃ (U : Set (ℝ × ℝ)) (_ : IsOpen U) (_ : (p : ℝ × ℝ) ∈ U) (C : ℝ),
      ∀ q ∈ U, ‖F q‖ ≤ C := fun p => by
    obtain ⟨U, hUo, hpm, C, hC⟩ := h p.1 p.2
    exact ⟨U, hUo, hpm, C, hC⟩
  choose U hUo hmem C hC using h'
  have hcover : K ⊆ ⋃ p : K, U p := fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUo hcover
  refine ⟨t.sum fun p => max 0 (C p), Finset.sum_nonneg fun p _ => le_max_left _ _, fun p hp => ?_⟩
  obtain ⟨i, hit, hpi⟩ := Set.mem_iUnion₂.mp (ht hp)
  exact (hC i p hpi).trans ((le_max_right 0 (C i)).trans
    (Finset.single_le_sum (f := fun p => max 0 (C p)) (fun p _ => le_max_left _ _) hit))

/-- The subtracted remainder of the logarithmic derivative is bounded on the tube. -/
theorem exists_bound_tube_remainder
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) {a b T δ : ℝ} (hab : a ≤ b)
    (s : Finset ℂ) (ord : ℂ → ℕ) (g : ℂ → ℂ → ℂ)
    (hcover : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → |z.im - T| ≤ δ → f z = 0 → z ∈ s)
    (hfac : ∀ ρ ∈ s, AnalyticAt ℂ (g ρ) ρ ∧ (g ρ) ρ ≠ 0 ∧
      (∀ᶠ z in 𝓝[≠] ρ, logDeriv f z = (ord ρ : ℂ) / (z - ρ) + logDeriv (g ρ) z)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (T - δ) (T + δ), ∀ σ ∈ uIcc a b,
      ‖(logDeriv f ((σ : ℂ) + (t : ℂ) * I)).im -
        ∑ ρ ∈ s, (((ord ρ : ℂ) / (((σ : ℂ) + (t : ℂ) * I) - ρ)).im)‖ ≤ C := by
  classical
  let R : ℝ × ℝ → ℝ := fun p => (logDeriv f ((p.1 : ℂ) + (p.2 : ℂ) * I)).im -
    ∑ ρ ∈ s, (((ord ρ : ℂ) / (((p.1 : ℂ) + (p.2 : ℂ) * I) - ρ)).im)
  have hRq : ∀ p : ℝ × ℝ, R p = (logDeriv f ((p.1 : ℂ) + (p.2 : ℂ) * I)).im -
      ∑ ρ ∈ s, (((ord ρ : ℂ) / (((p.1 : ℂ) + (p.2 : ℂ) * I) - ρ)).im) := fun p => rfl
  have hloc : ∀ p ∈ (uIcc a b ×ˢ Icc (T - δ) (T + δ)), ∃ U : Set (ℝ × ℝ),
      IsOpen U ∧ p ∈ U ∧ ∃ C : ℝ, ∀ q ∈ U, ‖R q‖ ≤ C := by
    intro p hp
    by_cases hz : ∃ ρ ∈ s, (p.1 : ℂ) + (p.2 : ℂ) * I = ρ
    · obtain ⟨ρ, hρs, hρeq⟩ := hz
      obtain ⟨U, hU, C', hC'⟩ := locallyBounded_remainder_at_zero f s ord g R hRq hρs
        (hfac ρ hρs)
      have hp1 : p.1 = ρ.re := by simpa using congrArg Complex.re hρeq
      have hp2 : p.2 = ρ.im := by simpa using congrArg Complex.im hρeq
      have hpeq : p = (ρ.re, ρ.im) := Prod.ext hp1 hp2
      have hU' : U ∈ 𝓝 p := by rw [hpeq]; exact hU
      exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hU', C',
        fun q hq => hC' q (interior_subset hq)⟩
    · push_neg at hz
      obtain ⟨U, hU, C', hC'⟩ := exists_bound_nhds_of_continuousAt
        (continuousAt_remainder hab f hf s ord R hcover hRq hp.1 hp.2
          (fun hmem => hz _ hmem rfl))
      exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hU, C',
        fun q hq => hC' q (interior_subset hq)⟩
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_locallyBounded (isCompact_uIcc.prod isCompact_Icc)
    (F := R) hloc
  exact ⟨C, hC0, fun t ht σ hσ => hC (σ, t) ⟨hσ, ht⟩⟩


/-- The Poisson kernel identity for a natural-number pole weight. -/
theorem im_model_pole_nat576 (m : ℕ) (ρ : ℂ) (x t : ℝ) :
    (((m : ℂ)) / (((x : ℂ) + (t : ℂ) * I) - ρ)).im
      = -(((m : ℝ)) * ((t - ρ.im) / ((x - ρ.re) ^ 2 + (t - ρ.im) ^ 2))) := by
  have hcast : ((m : ℂ)) = (((m : ℝ)) : ℂ) := by norm_cast
  rw [hcast, im_model_pole576]

/-! ### Horizontal argument integral: existence of the one-sided limit -/

/-- Dominated convergence for interval integrals along an arbitrary filter. -/
theorem tendsto_integral_of_dominated {F : ℝ → ℝ → ℝ} {G : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (l : Filter ℝ) [l.IsCountablyGenerated]
    (hmeas : ∀ᶠ t in l, AEStronglyMeasurable (F t) (volume.restrict (Ioc a b)))
    (hbound : ∀ᶠ t in l, ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioc a b → ‖F t σ‖ ≤ C)
    (hlim : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioc a b → Tendsto (fun t => F t σ) l (𝓝 (G σ))) :
    Tendsto (fun t : ℝ => ∫ σ in a..b, F t σ) l (𝓝 (∫ σ in a..b, G σ)) := by
  have hmain : Tendsto (fun t : ℝ => ∫ σ, F t σ ∂(volume.restrict (Ioc a b))) l
      (𝓝 (∫ σ, G σ ∂(volume.restrict (Ioc a b)))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioc a b)) (l := l) (bound := fun _ : ℝ => C) hmeas ?_
      (integrable_const C) ?_
    · filter_upwards [hbound] with t ht
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc (p := fun σ : ℝ => ‖F t σ‖ ≤ C)]
      exact ht
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc
        (p := fun σ : ℝ => Tendsto (fun t => F t σ) l (𝓝 (G σ)))]
      exact hlim
  have hgoal : Tendsto (fun t : ℝ => ∫ σ in a..b, F t σ) l (𝓝 (∫ σ in a..b, G σ)) := by
    simpa [intervalIntegral.integral_of_le hab] using hmain
  exact hgoal

/-- For an entire function whose zeros in a tube are listed in `s`, the imaginary
part of the horizontal logarithmic-derivative integral has a one-sided limit at
`T`, along any filter contained in `𝓝 T` whose heights stay in the tube. -/
theorem exists_limit_horizontal_im
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) {a b T δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (s : Finset ℂ) (ord : ℂ → ℕ) (g : ℂ → ℂ → ℂ)
    (hcover : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → |z.im - T| ≤ δ → f z = 0 → z ∈ s)
    (hfac : ∀ ρ ∈ s, AnalyticAt ℂ (g ρ) ρ ∧ (g ρ) ρ ≠ 0 ∧
      (∀ᶠ z in 𝓝[≠] ρ, logDeriv f z = (ord ρ : ℂ) / (z - ρ) + logDeriv (g ρ) z))
    (l : Filter ℝ) [l.IsCountablyGenerated] (hlT : l ≤ 𝓝 T)
    (htube : ∀ᶠ t in l, |t - T| < δ)
    (hpole : ∀ ρ ∈ s, ∃ A : ℝ, Tendsto (fun t : ℝ => ∫ σ in a..b,
        -(((ord ρ : ℝ)) * ((t - ρ.im) / ((σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2)))) l (𝓝 A)) :
    ∃ A : ℝ, Tendsto (fun t : ℝ => ∫ σ in a..b,
        (logDeriv f ((σ : ℂ) + (t : ℂ) * I)).im) l (𝓝 A) := by
  classical
  let R : ℝ × ℝ → ℝ := fun p => (logDeriv f ((p.1 : ℂ) + (p.2 : ℂ) * I)).im -
    ∑ ρ ∈ s, (((ord ρ : ℂ) / (((p.1 : ℂ) + (p.2 : ℂ) * I) - ρ)).im)
  have hRq : ∀ p : ℝ × ℝ, R p = (logDeriv f ((p.1 : ℂ) + (p.2 : ℂ) * I)).im -
      ∑ ρ ∈ s, (((ord ρ : ℂ) / (((p.1 : ℂ) + (p.2 : ℂ) * I) - ρ)).im) := fun p => rfl
  obtain ⟨C, hC0, hC⟩ := exists_bound_tube_remainder f hf hab s ord g hcover hfac
  have hderiv_cont : Continuous (deriv f) := by
    rw [continuous_iff_continuousAt]
    intro z
    exact ((hf.analyticAt z).deriv).continuousAt
  have hld_meas : Measurable (logDeriv f) := by
    simpa [logDeriv] using hderiv_cont.measurable.div hf.continuous.measurable
  have hRmeas : ∀ t : ℝ, Measurable (fun σ : ℝ => R (σ, t)) := by
    intro t
    have hzfun : Measurable (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * I) := by fun_prop
    have h1 : Measurable (fun σ : ℝ => (logDeriv f ((σ : ℂ) + (t : ℂ) * I)).im) :=
      Complex.continuous_im.measurable.comp (hld_meas.comp hzfun)
    have h2 : Measurable (fun σ : ℝ =>
        ∑ ρ ∈ s, (((ord ρ : ℂ) / (((σ : ℂ) + (t : ℂ) * I) - ρ)).im)) := by
      refine Finset.measurable_sum _ ?_
      intro ρ hρ
      have hsub : Measurable (fun σ : ℝ => ((σ : ℂ) + (t : ℂ) * I) - ρ) := by fun_prop
      exact Complex.continuous_im.measurable.comp (measurable_const.div hsub)
    have heq : (fun σ : ℝ => R (σ, t)) = fun σ : ℝ =>
        (logDeriv f ((σ : ℂ) + (t : ℂ) * I)).im -
          ∑ ρ ∈ s, (((ord ρ : ℂ) / (((σ : ℂ) + (t : ℂ) * I) - ρ)).im) := by
      funext σ
      rw [hRq]
    rw [heq]
    exact h1.sub h2
  set B : Finset ℝ := (s.filter (fun ρ => ρ.im = T)).image (fun ρ => ρ.re) with hB
  have haeB : ∀ᵐ σ : ℝ ∂(volume : Measure ℝ), σ ∉ (B : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa using B.finite_toSet.measure_zero (volume : Measure ℝ)
  have hRlim : Tendsto (fun t : ℝ => ∫ σ in a..b, R (σ, t)) l
      (𝓝 (∫ σ in a..b, R (σ, T))) := by
    refine tendsto_integral_of_dominated (C := C) hab l ?_ ?_ ?_
    · filter_upwards with t
      exact (hRmeas t).aestronglyMeasurable
    · filter_upwards [htube] with t ht
      refine Eventually.of_forall fun σ hσ => ?_
      have htmem : t ∈ Icc (T - δ) (T + δ) := by
        rw [abs_lt] at ht
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact hC t htmem σ ((Set.Ioc_subset_Icc_self.trans Set.Icc_subset_uIcc) hσ)
    · filter_upwards [haeB] with σ hσB hσ
      have hzmem : ((σ : ℂ) + (T : ℂ) * I) ∉ (s : Set ℂ) := by
        intro hmem
        apply hσB
        refine Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr ⟨hmem, by simp⟩, ?_⟩
        simp
      have hcont2 : ContinuousAt R (σ, T) :=
        continuousAt_remainder hab f hf s ord R hcover hRq
          ((Set.Ioc_subset_Icc_self.trans Set.Icc_subset_uIcc) hσ)
          ⟨by linarith, by linarith⟩ hzmem
      have hpair : ContinuousAt (fun t : ℝ => (σ, t)) T := by fun_prop
      exact ((hcont2.comp hpair).mono_left hlT)
  have hEx : ∀ ρ : ℂ, ∃ A : ℝ, ρ ∈ s → Tendsto (fun t : ℝ => ∫ σ in a..b,
      -(((ord ρ : ℝ)) * ((t - ρ.im) / ((σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2)))) l (𝓝 A) := by
    intro ρ
    by_cases hρ : ρ ∈ s
    · obtain ⟨A, hA₀⟩ := hpole ρ hρ
      exact ⟨A, fun _ => hA₀⟩
    · exact ⟨0, fun h => absurd h hρ⟩
  choose A hA using hEx
  have hpoles : Tendsto (fun t : ℝ => ∑ ρ ∈ s, ∫ σ in a..b,
      -(((ord ρ : ℝ)) * ((t - ρ.im) / ((σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2)))) l
      (𝓝 (∑ ρ ∈ s, A ρ)) :=
    tendsto_finsetSum s fun ρ hρ => hA ρ hρ
  refine ⟨(∫ σ in a..b, R (σ, T)) + ∑ ρ ∈ s, A ρ, (hRlim.add hpoles).congr' ?_⟩
  filter_upwards [htube] with t ht
  have htmem : t ∈ Icc (T - δ) (T + δ) := by
    rw [abs_lt] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hpolecont : ∀ ρ ∈ s, Continuous fun σ : ℝ =>
      -(((ord ρ : ℝ)) * ((t - ρ.im) / ((σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2))) := by
    intro ρ hρ
    by_cases hcase : t - ρ.im = 0
    · simpa [hcase] using continuous_const
    · have hsq : 0 < (t - ρ.im) ^ 2 := by
        rcases lt_or_gt_of_ne hcase with h | h
        · nlinarith
        · nlinarith
      refine Continuous.neg (continuous_const.mul (Continuous.div continuous_const ?_ ?_))
      · fun_prop
      · intro σ
        have h1 : 0 ≤ (σ - ρ.re) ^ 2 := sq_nonneg _
        exact (by linarith : 0 < (σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2).ne'
  have hRbound : ∀ σ ∈ uIcc a b, ‖R (σ, t)‖ ≤ C := fun σ hσ => hC t htmem σ hσ
  have hRleft : IntegrableOn (fun σ : ℝ => R (σ, t)) (Ioc a b) volume := by
    refine Integrable.of_bound
      ((hRmeas t).aestronglyMeasurable (μ := volume.restrict (Ioc a b))) C ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with σ hσ
    exact hRbound σ ((Set.Ioc_subset_Icc_self.trans Set.Icc_subset_uIcc) hσ)
  have hRright : IntegrableOn (fun σ : ℝ => R (σ, t)) (Ioc b a) volume := by
    refine Integrable.of_bound
      ((hRmeas t).aestronglyMeasurable (μ := volume.restrict (Ioc b a))) C ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with σ hσ
    refine hRbound σ ?_
    rw [uIcc_of_le hab]
    exact ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hRint : IntervalIntegrable (fun σ : ℝ => R (σ, t)) volume a b := ⟨hRleft, hRright⟩
  have hpoleInt : ∀ ρ ∈ s, IntervalIntegrable (fun σ : ℝ =>
      -(((ord ρ : ℝ)) * ((t - ρ.im) / ((σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2)))) volume a b :=
    fun ρ hρ => (hpolecont ρ hρ).continuousOn.intervalIntegrable
  have hpoint : ∀ σ : ℝ, R (σ, t) + ∑ ρ ∈ s,
      -(((ord ρ : ℝ)) * ((t - ρ.im) / ((σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2)))
      = (logDeriv f ((σ : ℂ) + (t : ℂ) * I)).im := by
    intro σ
    have herase : ∀ ρ ∈ s, -(((ord ρ : ℝ)) * ((t - ρ.im) / ((σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2)))
        = (((ord ρ : ℂ) / (((σ : ℂ) + (t : ℂ) * I) - ρ)).im) := by
      intro ρ hρ
      rw [im_model_pole_nat576]
    rw [hRq (σ, t), Finset.sum_congr rfl herase]
    ring
  have hsumcont : Continuous (fun σ : ℝ => ∑ ρ ∈ s,
      -(((ord ρ : ℝ)) * ((t - ρ.im) / ((σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2)))) := by
    refine continuous_finsetSum (s := s)
      (f := fun ρ σ => -(((ord ρ : ℝ)) * ((t - ρ.im) / ((σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2)))) ?_
    intro ρ hρ
    exact hpolecont ρ hρ
  have hsumInt : IntervalIntegrable (fun σ : ℝ => ∑ ρ ∈ s,
      -(((ord ρ : ℝ)) * ((t - ρ.im) / ((σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2)))) volume a b :=
    hsumcont.continuousOn.intervalIntegrable
  have hsplit : (∫ σ in a..b, (logDeriv f ((σ : ℂ) + (t : ℂ) * I)).im)
      = (∫ σ in a..b, R (σ, t)) + ∑ ρ ∈ s, ∫ σ in a..b,
        -(((ord ρ : ℝ)) * ((t - ρ.im) / ((σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2))) := by
    have h1 : (∫ σ in a..b, (logDeriv f ((σ : ℂ) + (t : ℂ) * I)).im)
        = ∫ σ in a..b, (R (σ, t) + ∑ ρ ∈ s,
          -(((ord ρ : ℝ)) * ((t - ρ.im) / ((σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2)))) := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      rw [hpoint σ]
    rw [h1, intervalIntegral.integral_add hRint hsumInt, intervalIntegral.integral_finsetSum hpoleInt]
  rw [hsplit]
  try ring


/-! ### The symmetric vertical integral -/

/-- The symmetric vertical integral converges as the height tends to `T`. -/
theorem tendsto_interval_symmetric {g : ℝ → ℝ} {C T : ℝ} (hT : 1 ≤ T) (hC : 0 ≤ C)
    (hcont : ContinuousOn g (uIcc (-(T + 1)) (T + 1)))
    (hbound : ∀ τ ∈ uIcc (-(T + 1)) (T + 1), ‖g τ‖ ≤ C) :
    Tendsto (fun t : ℝ => ∫ τ in (-t)..t, g τ) (𝓝[>] T) (𝓝 (∫ τ in (-T)..T, g τ)) := by
  have hle : ∀ᶠ t : ℝ in 𝓝[>] T, T < t ∧ t < T + 1 := by
    filter_upwards [Ioo_mem_nhdsGT (by linarith : T < T + 1), self_mem_nhdsWithin]
      with t ht htT
    exact ⟨htT, ht.2⟩
  have hwide : -(T + 1) ≤ T + 1 := by linarith
  have hmem_wide : ∀ x : ℝ, x ∈ uIcc (-(T + 1)) (T + 1) ↔ -(T + 1) ≤ x ∧ x ≤ T + 1 := by
    intro x
    rw [uIcc_of_le hwide]
    rfl
  have hinter : ∀ a b : ℝ, -(T + 1) ≤ a → -(T + 1) ≤ b → a ≤ T + 1 → b ≤ T + 1 →
      IntervalIntegrable g volume a b := by
    intro a b ha hb ha' hb'
    refine ContinuousOn.intervalIntegrable ?_
    refine hcont.mono ?_
    intro x hx
    rw [hmem_wide]
    have hlow : -(T + 1) ≤ x := by
      rcases le_total a b with h | h
      · rw [uIcc_of_le h] at hx; linarith [hx.1]
      · rw [uIcc_of_ge h] at hx; linarith [hx.1]
    have hhigh : x ≤ T + 1 := by
      rcases le_total a b with h | h
      · rw [uIcc_of_le h] at hx; linarith [hx.2]
      · rw [uIcc_of_ge h] at hx; linarith [hx.2]
    exact ⟨hlow, hhigh⟩
  have hsplit : (fun t : ℝ => ∫ τ in (-t)..t, g τ) =ᶠ[𝓝[>] T]
      (fun t : ℝ => (∫ τ in (-t)..(-T), g τ) + (∫ τ in (-T)..T, g τ) + (∫ τ in T..t, g τ)) := by
    filter_upwards [hle] with t ht
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hinter (-t) (-T) (by linarith [ht.2]) (by linarith [hT])
        (by linarith [ht.1]) (by linarith [hT]))
      (hinter (-T) T (by linarith [hT]) (by linarith [hT])
        (by linarith [hT]) (by linarith [hT]))
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hinter (-t) T (by linarith [ht.2]) (by linarith [hT])
        (by linarith [ht.1]) (by linarith [hT]))
      (hinter T t (by linarith [hT]) (by linarith [hT])
        (by linarith [hT]) (by linarith [ht.2]))
    linarith [h1, h2]
  have hsmall : Tendsto (fun t : ℝ => C * |t - T|) (𝓝[>] T) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t - T) (𝓝[>] T) (𝓝 0) := by
      have h2 : Tendsto (fun t : ℝ => t - T) (𝓝 T) (𝓝 (T - T)) :=
        (continuousAt_id.sub continuousAt_const).tendsto
      rw [sub_self] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun t : ℝ => |t - T|) (𝓝[>] T) (𝓝 0) := by
      have h4 : Tendsto (fun t : ℝ => |t - T|) (𝓝[>] T) (𝓝 |(0 : ℝ)|) :=
        (continuous_abs.tendsto 0).comp h1
      simpa using h4
    have h5 : Tendsto (fun t : ℝ => C * |t - T|) (𝓝[>] T) (𝓝 (C * 0)) := h3.const_mul C
    simpa using h5
  have hzeroleft : Tendsto (fun t : ℝ => ∫ τ in (-t)..(-T), g τ) (𝓝[>] T) (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' ?_ ?_ hsmall)
    · filter_upwards with t
      exact norm_nonneg _
    · filter_upwards [hle] with t ht
      have hb : ∀ τ ∈ uIoc (-t) (-T), ‖g τ‖ ≤ C := by
        intro τ hτ
        refine hbound τ ?_
        rw [hmem_wide]
        rw [uIoc_of_le (by linarith [ht.1] : -t ≤ -T)] at hτ
        exact ⟨by linarith [hτ.1, ht.2], by linarith [hτ.2, hT]⟩
      have hb' := intervalIntegral.norm_integral_le_of_norm_le_const hb
      have habs : |(-T) - (-t)| = |t - T| := by
        rw [show -T - -t = t - T by ring]
      rwa [habs] at hb'
  have hzeroright : Tendsto (fun t : ℝ => ∫ τ in T..t, g τ) (𝓝[>] T) (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' ?_ ?_ hsmall)
    · filter_upwards with t
      exact norm_nonneg _
    · filter_upwards [hle] with t ht
      have hb : ∀ τ ∈ uIoc T t, ‖g τ‖ ≤ C := by
        intro τ hτ
        refine hbound τ ?_
        rw [hmem_wide]
        rw [uIoc_of_le (by linarith [ht.1] : T ≤ t)] at hτ
        exact ⟨by linarith [hτ.1, hT], by linarith [hτ.2, ht.2]⟩
      exact intervalIntegral.norm_integral_le_of_norm_le_const hb
  have hmiddle : Tendsto (fun _ : ℝ => ∫ τ in (-T)..T, g τ) (𝓝[>] T)
      (𝓝 (∫ τ in (-T)..T, g τ)) := tendsto_const_nhds
  exact Tendsto.congr' hsplit.symm (by
    have h := (hzeroleft.add hmiddle).add hzeroright
    simpa only [zero_add, add_zero] using h)


/-- Transport of a limit along the height reflection. -/
theorem tendsto_reflect_iff {F : ℝ → ℝ} {A T : ℝ} :
    Tendsto F (Filter.map (fun t : ℝ => -t) (𝓝[>] T)) (𝓝 A) ↔
      Tendsto (fun t : ℝ => F (-t)) (𝓝[>] T) (𝓝 A) := by
  constructor
  · intro h
    exact h.comp (Filter.tendsto_map (f := fun t : ℝ => -t))
  · intro h
    show Filter.map F (Filter.map (fun t : ℝ => -t) (𝓝[>] T)) ≤ 𝓝 A
    rw [Filter.map_map]
    exact h

/-- Negation maps the right filter at `T` to the left filter at `-T`. -/
theorem tendsto_neg_nhdsGT {T : ℝ} :
    Tendsto (fun t : ℝ => -t) (𝓝[>] T) (𝓝[<] (-T)) := by
  have h1 : Tendsto (fun t : ℝ => -t) (𝓝 T) (𝓝 (-T)) :=
    (continuousAt_id.neg).tendsto
  refine tendsto_nhdsWithin_iff.mpr ⟨h1.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  have h2 : T < t := ht
  show -t < -T
  linarith

/-- The right limit of the three-segment contour argument at a positive height. -/
theorem exists_argument_limit576 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) {T : ℝ} (hT : 1 ≤ T) :
    ∃ A : ℝ, Tendsto (argument576 χ) (𝓝[>] T) (𝓝 A) := by
  classical
  have hLdiff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hne
  have hLcont : Continuous (DirichletCharacter.LFunction χ) := hLdiff.continuous
  have hderiv_cont : Continuous (deriv (DirichletCharacter.LFunction χ)) := by
    rw [continuous_iff_continuousAt]
    intro z
    exact ((hLdiff.analyticAt z).deriv).continuousAt
  set s : Finset ℂ := ((LZeros_finite χ (T + 2)).toFinset).filter (fun ρ => 1 / 2 ≤ ρ.re) with hsdef
  have hs_mem : ∀ ρ ∈ s, ρ ∈ (LZeros_finite χ (T + 2)).toFinset :=
    fun ρ hρ => (Finset.mem_filter.mp hρ).1
  have hs_zero : ∀ ρ ∈ s, DirichletCharacter.LFunction χ ρ = 0 :=
    fun ρ hρ => ((LZeros_finite χ (T + 2)).mem_toFinset.mp (hs_mem ρ hρ)).1
  have hs_re : ∀ ρ ∈ s, 1 / 2 ≤ ρ.re := fun ρ hρ => (Finset.mem_filter.mp hρ).2
  have hs_re1 : ∀ ρ ∈ s, ρ.re < 1 :=
    fun ρ hρ => ((LZeros_finite χ (T + 2)).mem_toFinset.mp (hs_mem ρ hρ)).2.2.1
  have hnotop : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
      analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ := by
    intro ρ hρ htop
    have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 ρ] 0 := analyticOrderAt_eq_top.mp htop
    have hAn : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
      fun z _ => hLdiff.analyticAt z
    have heq : DirichletCharacter.LFunction χ 2 = 0 := by
      have h := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (Set.mem_univ ρ) hev
      simpa using h (Set.mem_univ (2 : ℂ))
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by norm_num) heq
  have hex : ∀ ρ : ℂ, ∃ (m : ℕ) (g : ℂ → ℂ), ρ ∈ s →
      (AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
        ∀ᶠ z in 𝓝[≠] ρ, logDeriv (DirichletCharacter.LFunction χ) z
          = (m : ℂ) / (z - ρ) + logDeriv g z) := by
    intro ρ
    by_cases hρ : ρ ∈ s
    · obtain ⟨m, g, h1, h2, h3⟩ :=
        exists_logDeriv_factor576' (hLdiff.analyticAt ρ) (hnotop ρ (hs_zero ρ hρ))
      exact ⟨m, g, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun _ => 1, fun h => absurd h hρ⟩
  choose m gm hm using hex
  have hcover : ∀ (S : ℝ), |S| ≤ T → ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → |z.im - S| ≤ 1 / 2 →
      DirichletCharacter.LFunction χ z = 0 → z ∈ s := by
    intro S hS z hz1 hz2 hzim hz0
    have him2 : |z.im| ≤ T + 2 := by
      have h1 : z.im = (z.im - S) + S := by ring
      have h2 : |(z.im - S) + S| ≤ |z.im - S| + |S| := abs_add_le _ _
      rw [h1]
      linarith
    refine Finset.mem_filter.mpr ⟨?_, hz1⟩
    refine (LZeros_finite χ (T + 2)).mem_toFinset.mpr ⟨hz0, by linarith, ?_, him2⟩
    by_contra hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne)
      (not_lt.mp hge) hz0
  have hshift_plus : Tendsto (fun t : ℝ => t - T) (𝓝[>] T) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h1 : Tendsto (fun t : ℝ => t - T) (𝓝 T) (𝓝 (T - T)) :=
        (continuousAt_id.sub continuousAt_const).tendsto
      rw [sub_self] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have h1 : T < t := ht
      have h2 : (0 : ℝ) < t - T := by linarith
      exact h2
  have hshift_minus : Tendsto (fun h : ℝ => h + T) (𝓝[<] (-T)) (𝓝[<] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h1 : Tendsto (fun h : ℝ => h + T) (𝓝 (-T)) (𝓝 (-T + T)) :=
        (continuousAt_id.add continuousAt_const).tendsto
      rw [neg_add_cancel] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      have h1 : h < -T := hh
      have h2 : h + T < 0 := by linarith
      exact h2
  have hpole_plus : ∀ ρ ∈ s, ∃ A : ℝ, Tendsto (fun t : ℝ => ∫ σ in (1 / 2 : ℝ)..2,
      -(((m ρ : ℝ)) * ((t - ρ.im) / ((σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2))))
      (𝓝[>] T) (𝓝 A) := by
    intro ρ hρ
    by_cases him : ρ.im = T
    · have hker : ∃ W : ℝ, Tendsto (fun eps : ℝ => ∫ σ in (1 / 2 : ℝ)..2,
          -(((m ρ : ℝ)) * (eps / ((σ - ρ.re) ^ 2 + eps ^ 2)))) (𝓝[>] (0 : ℝ)) (𝓝 W) := by
        rcases lt_or_eq_of_le (hs_re ρ hρ) with hlt | heq
        · exact ⟨_, tendsto_pole_integral_interior hlt (by linarith [hs_re1 ρ hρ])⟩
        · rw [← heq]
          exact ⟨_, tendsto_pole_integral_edge_left (by norm_num)⟩
      obtain ⟨W, hW⟩ := hker
      refine ⟨W, ?_⟩
      have h := hW.comp hshift_plus
      simpa [him, Function.comp_def] using h
    · set dd : ℝ := |T - ρ.im| with hdd
      have hddpos : 0 < dd := by
        rw [hdd, abs_pos]
        exact sub_ne_zero.mpr (Ne.symm him)
      have hδ'pos : 0 < min (1 / 2 : ℝ) (dd / 2) := lt_min (by norm_num) (by positivity)
      have hcont : ContinuousOn (fun p : ℝ × ℝ => -(((m ρ : ℝ)) *
          ((p.1 - ρ.im) / ((p.2 - ρ.re) ^ 2 + (p.1 - ρ.im) ^ 2))))
          (Icc (T - min (1 / 2 : ℝ) (dd / 2)) (T + min (1 / 2 : ℝ) (dd / 2)) ×ˢ
            uIcc (1 / 2 : ℝ) 2) := by
        refine ContinuousOn.neg (ContinuousOn.mul continuousOn_const ?_)
        refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
        intro p hp
        have hlt : |p.1 - T| ≤ min (1 / 2 : ℝ) (dd / 2) := by
          rw [abs_le]
          exact ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
        have hge : dd / 2 ≤ |p.1 - ρ.im| := by
          have h2 : |T - ρ.im| ≤ |p.1 - ρ.im| + |p.1 - T| := by
            have heq : T - ρ.im = (p.1 - ρ.im) - (p.1 - T) := by ring
            rw [heq]
            exact abs_sub _ _
          have h3 : min (1 / 2 : ℝ) (dd / 2) ≤ dd / 2 := min_le_right _ _
          rw [hdd] at *
          linarith
        have hpos : 0 < |p.1 - ρ.im| := by linarith [hddpos]
        have hsq : 0 < (p.1 - ρ.im) ^ 2 := by rw [← sq_abs]; exact pow_pos hpos 2
        have hsq2 : 0 ≤ (p.2 - ρ.re) ^ 2 := sq_nonneg _
        exact (by linarith : 0 < (p.2 - ρ.re) ^ 2 + (p.1 - ρ.im) ^ 2).ne'
      exact ⟨_, (continuousAt_integral_of_continuousOn hδ'pos hcont).tendsto.mono_left
        nhdsWithin_le_nhds⟩
  have hpole_minus : ∀ ρ ∈ s, ∃ A : ℝ, Tendsto (fun h : ℝ => ∫ σ in (1 / 2 : ℝ)..2,
      -(((m ρ : ℝ)) * ((h - ρ.im) / ((σ - ρ.re) ^ 2 + (h - ρ.im) ^ 2))))
      (Filter.map (fun t : ℝ => -t) (𝓝[>] T)) (𝓝 A) := by
    intro ρ hρ
    by_cases him : ρ.im = -T
    · have hker : ∃ W : ℝ, Tendsto (fun eps : ℝ => ∫ σ in (1 / 2 : ℝ)..2,
          -(((m ρ : ℝ)) * (eps / ((σ - ρ.re) ^ 2 + eps ^ 2)))) (𝓝[<] (0 : ℝ)) (𝓝 W) := by
        rcases lt_or_eq_of_le (hs_re ρ hρ) with hlt | heq
        · exact ⟨_, tendsto_pole_integral_interior_left hlt (by linarith [hs_re1 ρ hρ])⟩
        · rw [← heq]
          exact ⟨_, tendsto_pole_integral_edge_left' (by norm_num)⟩
      obtain ⟨W, hW⟩ := hker
      have hleft : Tendsto (fun h : ℝ => ∫ σ in (1 / 2 : ℝ)..2,
          -(((m ρ : ℝ)) * ((h + T) / ((σ - ρ.re) ^ 2 + (h + T) ^ 2))))
          (𝓝[<] (-T)) (𝓝 W) := by
        have h := hW.comp hshift_minus
        simpa [Function.comp_def] using h
      refine ⟨W, ?_⟩
      rw [tendsto_reflect_iff]
      have h := hleft.comp (tendsto_neg_nhdsGT (T := T))
      simpa [him, Function.comp_def] using h
    · set dd : ℝ := |-T - ρ.im| with hdd
      have hddpos : 0 < dd := by
        rw [hdd, abs_pos, sub_ne_zero]
        exact Ne.symm him
      have hδ'pos : 0 < min (1 / 2 : ℝ) (dd / 2) := lt_min (by norm_num) (by positivity)
      have hcont : ContinuousOn (fun p : ℝ × ℝ => -(((m ρ : ℝ)) *
          ((p.1 - ρ.im) / ((p.2 - ρ.re) ^ 2 + (p.1 - ρ.im) ^ 2))))
          (Icc (-T - min (1 / 2 : ℝ) (dd / 2)) (-T + min (1 / 2 : ℝ) (dd / 2)) ×ˢ
            uIcc (1 / 2 : ℝ) 2) := by
        refine ContinuousOn.neg (ContinuousOn.mul continuousOn_const ?_)
        refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
        intro p hp
        have hlt : |p.1 - -T| ≤ min (1 / 2 : ℝ) (dd / 2) := by
          rw [abs_le]
          exact ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
        have hge : dd / 2 ≤ |p.1 - ρ.im| := by
          have h2 : |-T - ρ.im| ≤ |p.1 - ρ.im| + |p.1 - -T| := by
            have heq : -T - ρ.im = (p.1 - ρ.im) - (p.1 - -T) := by ring
            rw [heq]
            exact abs_sub _ _
          have h3 : min (1 / 2 : ℝ) (dd / 2) ≤ dd / 2 := min_le_right _ _
          rw [hdd] at *
          linarith
        have hpos : 0 < |p.1 - ρ.im| := by linarith [hddpos]
        have hsq : 0 < (p.1 - ρ.im) ^ 2 := by rw [← sq_abs]; exact pow_pos hpos 2
        have hsq2 : 0 ≤ (p.2 - ρ.re) ^ 2 := sq_nonneg _
        exact (by linarith : 0 < (p.2 - ρ.re) ^ 2 + (p.1 - ρ.im) ^ 2).ne'
      have hlT : Filter.map (fun t : ℝ => -t) (𝓝[>] T) ≤ 𝓝 (-T) :=
        (tendsto_neg_nhdsGT (T := T)).mono_right nhdsWithin_le_nhds
      exact ⟨_, (continuousAt_integral_of_continuousOn hδ'pos hcont).tendsto.mono_left hlT⟩
  have htube_plus : ∀ᶠ t : ℝ in 𝓝[>] T, |t - T| < 1 / 2 := by
    filter_upwards [Ioo_mem_nhdsGT (by linarith : T < T + 1 / 2), self_mem_nhdsWithin]
      with t ht htT
    rw [abs_lt]
    exact ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
  have htube_minus : ∀ᶠ h : ℝ in Filter.map (fun t : ℝ => -t) (𝓝[>] T), |h - -T| < 1 / 2 := by
    rw [Filter.eventually_map]
    filter_upwards [Ioo_mem_nhdsGT (by linarith : T < T + 1 / 2), self_mem_nhdsWithin]
      with t ht htT
    rw [abs_lt]
    exact ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
  obtain ⟨Aplus, hAplus⟩ := exists_limit_horizontal_im (DirichletCharacter.LFunction χ) hLdiff
    (a := 1 / 2) (b := 2) (T := T) (δ := 1 / 2) (by norm_num) (by norm_num) s m gm
    (hcover T (abs_le.mpr ⟨by linarith, le_refl T⟩)) (fun ρ hρ => hm ρ hρ) (𝓝[>] T) nhdsWithin_le_nhds
    htube_plus hpole_plus
  obtain ⟨Aminus, hAminus⟩ := exists_limit_horizontal_im (DirichletCharacter.LFunction χ) hLdiff
    (a := 1 / 2) (b := 2) (T := -T) (δ := 1 / 2) (by norm_num) (by norm_num) s m gm
    (hcover (-T) (abs_le.mpr ⟨by linarith, by linarith⟩)) (fun ρ hρ => hm ρ hρ)
    (Filter.map (fun t : ℝ => -t) (𝓝[>] T))
    ((tendsto_neg_nhdsGT (T := T)).mono_right nhdsWithin_le_nhds) htube_minus hpole_minus
  have hminus' : Tendsto (fun t : ℝ => ∫ σ in (1 / 2 : ℝ)..2,
      (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) - (t : ℂ) * I)).im)
      (𝓝[>] T) (𝓝 Aminus) := by
    rw [tendsto_reflect_iff] at hAminus
    simpa [Complex.ofReal_neg, sub_eq_add_neg, neg_mul, mul_neg] using hAminus
  have hplus' : Tendsto (fun t : ℝ => ∫ σ in (2 : ℝ)..(1 / 2),
      (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * I)).im)
      (𝓝[>] T) (𝓝 (-Aplus)) := by
    refine Tendsto.congr' (Eventually.of_forall fun t : ℝ => ?_) (hAplus.neg)
    dsimp only
    rw [intervalIntegral.integral_symm (a := (1 / 2 : ℝ)) (b := (2 : ℝ))]
  have hvert : Tendsto (fun t : ℝ => ∫ τ in (-t)..t,
      (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (τ : ℂ) * I)).re) (𝓝[>] T)
      (𝓝 (∫ τ in (-T)..T,
        (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (τ : ℂ) * I)).re)) := by
    have hne2 : ∀ τ : ℝ, DirichletCharacter.LFunction χ ((2 : ℂ) + (τ : ℂ) * I) ≠ 0 := by
      intro τ h0
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by norm_num) h0
    have hldcont : Continuous (fun τ : ℝ =>
        logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (τ : ℂ) * I)) := by
      refine Continuous.div (hderiv_cont.comp (by fun_prop)) (hLcont.comp (by fun_prop)) ?_
      intro τ
      exact hne2 τ
    have hcont_re : ContinuousOn (fun τ : ℝ =>
        (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (τ : ℂ) * I)).re)
        (uIcc (-(T + 1)) (T + 1)) := (Complex.continuous_re.comp hldcont).continuousOn
    obtain ⟨C0, hC0⟩ := (isCompact_uIcc).exists_bound_of_continuousOn hcont_re
    exact tendsto_interval_symmetric (g := fun τ : ℝ =>
      (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (τ : ℂ) * I)).re) hT
      (le_max_right C0 0) hcont_re (fun τ hτ => (hC0 τ hτ).trans (le_max_left C0 0))
  set Vh : Finset ℝ := (s.image (fun ρ => |ρ.im|)).filter (fun x => T < x) with hVh
  set V2 : Finset ℝ := Vh.image (fun x => (x - T) / 2) with hV2
  set δ0 : ℝ := if h : V2.Nonempty then min (1 / 2) (V2.min' h) else 1 / 2 with hδ0
  have hδ0pos : 0 < δ0 := by
    rw [hδ0]
    split_ifs with h
    · refine lt_min (by norm_num) ?_
      obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp (V2.min'_mem h)
      have hx' := Finset.mem_filter.mp hx
      rw [← hxeq]
      linarith [hx'.2]
    · norm_num
  have hδ0le_half : δ0 ≤ 1 / 2 := by
    rw [hδ0]
    split_ifs with h
    · exact min_le_left _ _
    · norm_num
  have hδ0le : ∀ x ∈ V2, δ0 ≤ x := by
    intro x hx
    rw [hδ0]
    split_ifs with h
    · exact (min_le_right _ _).trans (V2.min'_le x hx)
    · exact absurd ⟨x, hx⟩ h
  have hgood : ∀ᶠ t : ℝ in 𝓝[>] T,
      (∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → z.im = t →
        DirichletCharacter.LFunction χ z ≠ 0) ∧
      (∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → z.im = -t →
        DirichletCharacter.LFunction χ z ≠ 0) ∧
      T < t ∧ t < T + δ0 := by
    have hnear : ∀ᶠ t : ℝ in 𝓝[>] T, t < T + δ0 := by
      filter_upwards [Ioo_mem_nhdsGT (by linarith : T < T + δ0)] with t ht
      exact ht.2
    filter_upwards [hnear, self_mem_nhdsWithin] with t ht htT
    have ht1 : T < t := htT
    have htpos : 0 < t := by linarith
    have hzmem : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → |z.im| = t →
        DirichletCharacter.LFunction χ z ≠ 0 := by
      intro z hz1 hz2 hzim hz0
      have him : |z.im| ≤ T + 2 := by rw [hzim]; linarith
      have hzs : z ∈ s := by
        refine Finset.mem_filter.mpr ⟨?_, hz1⟩
        refine (LZeros_finite χ (T + 2)).mem_toFinset.mpr ⟨hz0, by linarith, ?_, him⟩
        by_contra hge
        exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne)
          (not_lt.mp hge) hz0
      have hV : |z.im| ∈ Vh := Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨z, hzs, rfl⟩, by rw [hzim]; exact htT⟩
      have h2 : (|z.im| - T) / 2 ∈ V2 := Finset.mem_image.mpr ⟨_, hV, rfl⟩
      have h3 := hδ0le _ h2
      rw [hzim] at h3
      linarith
    refine ⟨?_, ?_, htT, ht⟩
    · intro z hz1 hz2 hzim
      exact hzmem z hz1 hz2 (by rw [hzim, abs_of_pos htpos])
    · intro z hz1 hz2 hzim
      exact hzmem z hz1 hz2 (by rw [hzim, abs_neg, abs_of_pos htpos])
  have hident : argument576 χ =ᶠ[𝓝[>] T] fun t : ℝ => (1 / Real.pi) *
      ((∫ σ in (1 / 2 : ℝ)..2,
        (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) - (t : ℂ) * I)).im)
       + (∫ τ in (-t)..t,
        (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (τ : ℂ) * I)).re)
       + (∫ σ in (2 : ℝ)..(1 / 2),
        (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * I)).im)) := by
    filter_upwards [hgood] with t ht
    obtain ⟨hg1, hg2, ht1, ht2⟩ := ht
    have hI1 : IntervalIntegrable (fun σ : ℝ =>
        logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) - (t : ℂ) * I)) volume (1 / 2) 2 := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div
        (hderiv_cont.comp_continuousOn (by fun_prop)) (hLcont.comp_continuousOn (by fun_prop)) ?_
      intro σ hσ
      rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hσ
      have hre : (((σ : ℂ) - (t : ℂ) * I)).re = σ := by simp
      have him : (((σ : ℂ) - (t : ℂ) * I)).im = -t := by simp
      have hne := hg2 _ (by rw [hre]; exact hσ.1) (by rw [hre]; exact hσ.2) him
      simpa [logDeriv] using hne
    have hI3 : IntervalIntegrable (fun σ : ℝ =>
        logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * I)) volume 2 (1 / 2) := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div
        (hderiv_cont.comp_continuousOn (by fun_prop)) (hLcont.comp_continuousOn (by fun_prop)) ?_
      intro σ hσ
      rw [uIcc_comm, uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hσ
      have hre : (((σ : ℂ) + (t : ℂ) * I)).re = σ := by simp
      have him : (((σ : ℂ) + (t : ℂ) * I)).im = t := by simp
      have hne := hg1 _ (by rw [hre]; exact hσ.1) (by rw [hre]; exact hσ.2) him
      simpa [logDeriv] using hne
    have hI2 : IntervalIntegrable (fun τ : ℝ =>
        logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (τ : ℂ) * I)) volume (-t) t := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div
        (hderiv_cont.comp_continuousOn (by fun_prop)) (hLcont.comp_continuousOn (by fun_prop)) ?_
      intro τ hτ
      have hne2 : DirichletCharacter.LFunction χ ((2 : ℂ) + (τ : ℂ) * I) ≠ 0 := by
        intro h0
        exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by norm_num) h0
      simpa [logDeriv] using hne2
    unfold argument576
    simp only [Complex.add_im, Complex.I_mul_im]
    rw [intervalIntegral_im hI1, intervalIntegral_re hI2, intervalIntegral_im hI3]
    try ring
  have hsum : Tendsto (fun t : ℝ =>
      (∫ σ in (1 / 2 : ℝ)..2,
        (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) - (t : ℂ) * I)).im)
      + (∫ τ in (-t)..t,
        (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (τ : ℂ) * I)).re)
      + (∫ σ in (2 : ℝ)..(1 / 2),
        (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * I)).im))
      (𝓝[>] T) (𝓝 (Aminus + (∫ τ in (-T)..T,
        (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (τ : ℂ) * I)).re) + (-Aplus))) :=
    (hminus'.add hvert).add hplus'
  exact ⟨(1 / Real.pi) * (Aminus + (∫ τ in (-T)..T,
      (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (τ : ℂ) * I)).re) + (-Aplus)),
    Tendsto.congr' hident.symm (hsum.const_mul (1 / Real.pi))⟩

end Decomp576aWip

/-- LEAF. The contour argument has a finite limit from above at every positive
cutoff. Trudgian page 1 inclusive height convention and page 3 display 2.3.
This is endpoint regularity only and gives no bound for the limit.
-/
theorem argument_right_limit576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {T : ℝ} (hT : 1 ≤ T) :
    ∃ A : ℝ, Tendsto (argument576 χ) (𝓝[>] T) (𝓝 A) := by
  exact Decomp576aWip.exists_argument_limit576 χ hne hT

/-- At heights tending down to T, neither horizontal segment contains a zero.
Trudgian page 1 inclusive cutoff and page 3 contour, using the proved zero finiteness.
-/
theorem eventually_good_height576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) {T : ℝ} (hT : 1 ≤ T) :
    ∀ᶠ (t : ℝ) in 𝓝[>] T, ∀ σ ∈ Icc (1 / 2 : ℝ) 2,
      DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I) ≠ 0 ∧
      DirichletCharacter.LFunction χ ((σ : ℂ) - (t : ℂ) * I) ≠ 0 := by
  classical
  let H : Finset ℝ := (LZeros_finite χ (T + 1)).toFinset.image (fun ρ => |ρ.im|)
  have hev : ∀ᶠ (t : ℝ) in 𝓝[>] T, ∀ s ∈ H, t ≠ s := by
    rw [Filter.eventually_all_finset]
    intro s hs
    by_cases h : T = s
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact ne_of_gt (h ▸ ht)
    · exact eventually_ne_nhdsWithin h
  filter_upwards [hev, Ioo_mem_nhdsGT (show T < T + 1 by linarith)] with t ht htime
  intro σ hσ
  have ht0 : 0 < t := by linarith [htime.1]
  have nozero {z : ℂ} (hzre : z.re = σ) (hzim : |z.im| = t) :
      DirichletCharacter.LFunction χ z ≠ 0 := by
    by_cases hσ1 : 1 ≤ σ
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne)
        (by rw [hzre]; exact hσ1)
    · intro hz
      have hzmem : z ∈ LZeros χ (T + 1) := by
        refine ⟨hz, ?_, ?_, ?_⟩
        · rw [hzre]; linarith [hσ.1]
        · rw [hzre]; exact lt_of_not_ge hσ1
        · rw [hzim]; exact htime.2.le
      have hm : t ∈ H := by
        apply Finset.mem_image.mpr
        exact ⟨z, (LZeros_finite χ (T + 1)).mem_toFinset.mpr hzmem, hzim⟩
      exact ht t hm rfl
  constructor
  · apply nozero
    · simp
    · simp [abs_of_pos ht0]
  · apply nozero
    · simp
    · simp [abs_of_pos ht0]

/-- A single good horizontal segment has the derived loose budget.
Trudgian pages 4 to 9, displays 2.8, 3.9 and 4.2 to 4.12.
CONDITIONAL ON horizontal_of_jensen576 and jensen_mass_bound576.
-/
theorem horizontal_bound576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {T : ℝ} (hT : 1 ≤ |T|)
    (hgood : ∀ σ ∈ Icc (1 / 2 : ℝ) 2,
      DirichletCharacter.LFunction χ ((σ : ℂ) + (T : ℂ) * I) ≠ 0) :
    |horizontal576 χ T| ≤ 0.25 * Real.log ((q : ℝ) * |T|) + 7.5 := by
  have hz : DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + (T : ℂ) * I) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by norm_num)
  obtain ⟨N, hN, hcentre⟩ := Decomp576c.rosser_power_sequence576 hz
  have hm := jensen_mass_bound576 χ hχ hne hT N hN hcentre
    (fun η hη0 hη1 s hs0 hs1 => primitive_convexity576 χ hχ hne hη0 hη1 s hs0 hs1)
  have h := horizontal_of_jensen576 χ hχ hne hT hgood N hN hcentre hm
  convert h using 1 <;> ring

/-- The good-height contour bound adds the two horizontal budgets and the vertical budget.
Trudgian pages 3 to 9, displays 2.3 and 4.12.
CONDITIONAL ON the two power-Jensen leaves and vertical_bound576.
-/
theorem argument_good_bound576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {T : ℝ} (hT : 1 ≤ T)
    (hgood : ∀ σ ∈ Icc (1 / 2 : ℝ) 2,
      DirichletCharacter.LFunction χ ((σ : ℂ) + (T : ℂ) * I) ≠ 0 ∧
      DirichletCharacter.LFunction χ ((σ : ℂ) - (T : ℂ) * I) ≠ 0) :
    |argument576 χ T| ≤ 0.5 * Real.log ((q : ℝ) * T) + 15.7 := by
  have ht0 : 0 < T := by linarith
  have hplus := horizontal_bound576 χ hχ hne
    (by simpa [abs_of_pos ht0] using hT) (fun σ hσ => (hgood σ hσ).1)
  have hminus := horizontal_bound576 χ hχ hne
    (T := -T) (by simpa [abs_of_pos ht0] using hT) (by
      intro σ hσ
      simpa only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] using (hgood σ hσ).2)
  have hv := vertical_bound576 χ hT
  rw [argument_segments576]
  have htri := (abs_add_le (-horizontal576 χ (-T) + vertical576 χ T)
    (horizontal576 χ T)).trans
      (add_le_add (abs_add_le (-horizontal576 χ (-T)) (vertical576 χ T)) (le_refl _))
  simp only [abs_neg] at htri
  simp only [abs_of_pos ht0, abs_neg] at hplus hminus
  linarith

/-- The argument estimate passes to any genuine finite right limit.
Trudgian page 1 inclusive cutoff and pages 4 to 9, displays 2.8 and 4.12.
CONDITIONAL ON the three power-Jensen inputs. The convergence premise can be
supplied by the existing primitive_count_identity370 when integrating the supply.
-/
theorem argument_bound_of_limit576 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {T : ℝ} (hT : 1 ≤ T)
    {A : ℝ} (hA : Tendsto (argument576 χ) (𝓝[>] T) (𝓝 A)) :
    |Filter.limUnder (𝓝[>] T) (argument576 χ)| ≤ 0.5 * Real.log (q * T) + 15.7 := by
  have hq : 0 < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have ht0 : 0 < T := by linarith
  have hbudget : Tendsto (fun t : ℝ => 0.5 * Real.log ((q : ℝ) * t) + 15.7)
      (𝓝[>] T) (𝓝 (0.5 * Real.log ((q : ℝ) * T) + 15.7)) := by
    have hc : ContinuousAt (fun t : ℝ => 0.5 * Real.log ((q : ℝ) * t) + 15.7) T := by
      have hmul : ContinuousAt (fun t : ℝ => (q : ℝ) * t) T :=
        continuousAt_const.mul continuousAt_id
      exact (continuousAt_const.mul (hmul.log (mul_ne_zero hq.ne' ht0.ne'))).add continuousAt_const
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hbound : |A| ≤ 0.5 * Real.log ((q : ℝ) * T) + 15.7 := by
    apply le_of_tendsto_of_tendsto hA.abs hbudget
    filter_upwards [eventually_good_height576 χ hne hT, self_mem_nhdsWithin] with t ht htT
    exact argument_good_bound576 χ hχ hne (hT.trans (le_of_lt htT)) ht
  rw [hA.limUnder_eq]
  exact hbound


/-- The exact independent supply for primitive_argument_bound370, with the contour
expanded through argument576. Trudgian pages 4 to 9, displays 2.8 and 4.12.
CONDITIONAL ON the four smaller analytic leaves above. No zero-count estimate is used.
-/
theorem primitive_argument_bound576 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {T : ℝ} (hT : 1 ≤ T) :
    |Filter.limUnder (𝓝[>] T) (argument576 χ)| ≤ 0.5 * Real.log (q * T) + 15.7 := by
  obtain ⟨A, hA⟩ := argument_right_limit576 χ hχ hne hT
  exact argument_bound_of_limit576 χ hχ hne hT hA

end LeanLab.DERZ1997.Decomp576a
