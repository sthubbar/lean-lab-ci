import Mathlib
import LeanLab.ExceptionalSet.BrudernPerelli1998
import LeanLab.ExceptionalSet.State1539

/-!
Decomposition of Theorem 1 of P0082, Brüdern and Perelli 1998, repaired in unit U-1610.
Source: journal pages 357 display (6), 365 Lemma 8, 366 end of section 5.
The old leaves `leaf_dyadic_split`, `leaf_dyadic_sum` and `leaf_dyadic_sum_exp` were false and
`leaf_minor_bound`, `leaf_major_bound` were proved of two definitions equal to `0`; the old
`leaf_dyadic_bound` was Theorem 1 itself in dyadic form, so the old assembly was circular with the
sorry `BrudernPerelli1998.brudernPerelli`. Refutations are in `Audit1610`.
`leaf_dyadic_bound` is now an assembly from the major arc leaf, the minor arc leaf, the Fourier
identity leaf and the dissection leaf. Nothing here uses `brudernPerelli`.
-/

namespace LeanLab.ExceptionalSet.DecompJ200

open Real Finset Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998
open LeanLab.ExceptionalSet.U1539 (Sp majorArcs Kfun nu calE eC)

attribute [local instance] Classical.propDecidable

/-- Number of exceptions in the dyadic block `[M, 2M)`. Half open, so that the blocks at
`M = 2 ^ j` partition the positive integers, `n = 1` included. -/
noncomputable def Eγ_dyadic (γ : ℝ) (M : ℕ) : ℕ :=
  ((Finset.Ico M (2 * M)).filter (fun n => ¬ Solvable γ n)).card

/-- The dyadic indices `2 ^ j ≤ N`, `j ≤ log₂ N`. -/
noncomputable def dyadicIdx (N : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log 2 N + 1)).image (fun j => 2 ^ j)

/-- The window of section 5, p. 366: `n ≤ 2N` with `X/2 < ν_n ≤ X`, `X = F(N)`. -/
noncomputable def window (γ : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range (2 * N + 1)).filter (fun n => F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N)

/-- The integral over the major arcs `𝔑` in (6) at `v = F(n)`, with `X = F(N)`, `P = X^{6δ}`,
`Δ = ℰ^{-1/8}`, `ℰ = exp(κ (log N)^{3-2γ})`, pp. 357 and 365. -/
noncomputable def majorInt (γ δ κ : ℝ) (N n : ℕ) : ℂ :=
  ∫ α in majorArcs (F γ N ^ (6 * δ)) (F γ N),
    Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 * (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)
      * eC (-(α * F γ n))

/-- The integral over the minor arcs `𝔫 = ℝ \ 𝔑` in (6), same parameters. -/
noncomputable def minorInt (γ δ κ : ℝ) (N n : ℕ) : ℂ :=
  ∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ,
    Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 * (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)
      * eC (-(α * F γ n))

/-- The `n` of the window where the major arc integral misses `c₀ X ℰ^{-1/10}`, Lemma 8 p. 365. -/
noncomputable def Eγ_major_block (γ δ κ c₀ : ℝ) (N : ℕ) : ℕ :=
  ((window γ N).filter (fun n =>
    (majorInt γ δ κ N n).re < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card

/-- The `n` of the window where the minor arc integral exceeds `X ℰ^{-1/3}`, p. 366. -/
noncomputable def Eγ_minor_block (γ δ κ : ℝ) (N : ℕ) : ℕ :=
  ((window γ N).filter (fun n =>
    F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) < ‖minorInt γ δ κ N n‖)).card

/-- The members of a set `Bad` of integers lying in the window of `N`. -/
noncomputable def blockCount (γ : ℝ) (Bad : ℕ → Prop) (N : ℕ) : ℕ :=
  ((window γ N).filter Bad).card

/-- The members of a set `Bad` of integers lying in the block `[M, 2M)`. -/
noncomputable def dyadicCount (Bad : ℕ → Prop) (M : ℕ) : ℕ :=
  ((Finset.Ico M (2 * M)).filter Bad).card

/-- LEAF page 354: Trivial bound on dyadic exceptions. -/
theorem leaf_dyadic_trivial (γ : ℝ) (M : ℕ) :
    Eγ_dyadic γ M ≤ M := by
  unfold Eγ_dyadic
  have h : (Finset.Ico M (2 * M)).card = M := by
    rw [Nat.card_Ico]
    omega
  calc (Finset.Ico M (2 * M)).filter (fun n => ¬ Solvable γ n) |>.card
    _ ≤ (Finset.Ico M (2 * M)).card := Finset.card_filter_le _ _
    _ = M := h

open MeasureTheory intervalIntegral

/-- `∫_0^1 (1-t) cos (θ t) = (1 - cos θ)/θ²` for `θ ≠ 0`. -/
theorem integral_one_sub_mul_cos {θ : ℝ} (hθ : θ ≠ 0) :
    ∫ t in (0:ℝ)..1, (1 - t) * Real.cos (θ * t) = (1 - Real.cos θ) / θ ^ 2 := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => (1 - t) * Real.sin (θ * t) / θ - Real.cos (θ * t) / θ ^ 2)
        ((1 - t) * Real.cos (θ * t)) t := by
    intro t _
    have hsin : HasDerivAt (fun t : ℝ => Real.sin (θ * t)) (Real.cos (θ * t) * θ) t := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_sin (θ * t)).comp t ((hasDerivAt_id t).const_mul θ)
    have hcos : HasDerivAt (fun t : ℝ => Real.cos (θ * t)) (-(Real.sin (θ * t) * θ)) t := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_cos (θ * t)).comp t ((hasDerivAt_id t).const_mul θ)
    have h1m : HasDerivAt (fun t : ℝ => (1:ℝ) - t) (-1) t := by
      simpa [Pi.sub_def] using (hasDerivAt_const (x := t) (1:ℝ)).sub (hasDerivAt_id t)
    have ha : HasDerivAt (fun t : ℝ => (1 - t) * Real.sin (θ * t))
        ((-1) * Real.sin (θ * t) + (1 - t) * (Real.cos (θ * t) * θ)) t := h1m.mul hsin
    have hb : HasDerivAt (fun t : ℝ => (1 - t) * Real.sin (θ * t) / θ)
        (((-1) * Real.sin (θ * t) + (1 - t) * (Real.cos (θ * t) * θ)) / θ) t := ha.div_const θ
    have hc : HasDerivAt (fun t : ℝ => Real.cos (θ * t) / θ ^ 2)
        ((-(Real.sin (θ * t) * θ)) / θ ^ 2) t := hcos.div_const (θ ^ 2)
    have h := hb.sub hc
    convert h using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun t : ℝ => (1 - t) * Real.cos (θ * t)) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp
  field_simp
  ring



/-- `∫_0^1 (1-t) sin (θ t) = 1/θ - sin θ/θ²` for `θ ≠ 0`. -/
theorem integral_one_sub_mul_sin {θ : ℝ} (hθ : θ ≠ 0) :
    ∫ t in (0:ℝ)..1, (1 - t) * Real.sin (θ * t) = 1 / θ - Real.sin θ / θ ^ 2 := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => -((1 - t) * Real.cos (θ * t) / θ) - Real.sin (θ * t) / θ ^ 2)
        ((1 - t) * Real.sin (θ * t)) t := by
    intro t _
    have hsin : HasDerivAt (fun t : ℝ => Real.sin (θ * t)) (Real.cos (θ * t) * θ) t := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_sin (θ * t)).comp t ((hasDerivAt_id t).const_mul θ)
    have hcos : HasDerivAt (fun t : ℝ => Real.cos (θ * t)) (-(Real.sin (θ * t) * θ)) t := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_cos (θ * t)).comp t ((hasDerivAt_id t).const_mul θ)
    have h1m : HasDerivAt (fun t : ℝ => (1:ℝ) - t) (-1) t := by
      simpa [Pi.sub_def] using (hasDerivAt_const (x := t) (1:ℝ)).sub (hasDerivAt_id t)
    have ha : HasDerivAt (fun t : ℝ => (1 - t) * Real.cos (θ * t))
        ((-1) * Real.cos (θ * t) + (1 - t) * (-(Real.sin (θ * t) * θ))) t := h1m.mul hcos
    have hb : HasDerivAt (fun t : ℝ => -((1 - t) * Real.cos (θ * t) / θ))
        (-(((-1) * Real.cos (θ * t) + (1 - t) * (-(Real.sin (θ * t) * θ))) / θ)) t :=
      (ha.div_const θ).neg
    have hc : HasDerivAt (fun t : ℝ => Real.sin (θ * t) / θ ^ 2)
        ((Real.cos (θ * t) * θ) / θ ^ 2) t := hsin.div_const (θ ^ 2)
    have h := hb.sub hc
    convert h using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun t : ℝ => (1 - t) * Real.sin (θ * t)) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp
  field_simp
  ring



/-- The triangle `max 0 (1 - |t|)`, the transform of `sinc²(π ·)`. -/
lemma tri_even (t : ℝ) : (fun x : ℝ => max 0 (1 - |x|)) (-t) = (fun x : ℝ => max 0 (1 - |x|)) t := by
  simp

lemma tri_eq_one_sub_abs {t : ℝ} (h : t ∈ Set.Icc (-1 : ℝ) 1) : (fun x : ℝ => max 0 (1 - |x|)) t = 1 - |t| := by
  have h1 : |t| ≤ 1 := abs_le.mpr h
  show max 0 (1 - |t|) = 1 - |t|
  exact max_eq_right (by linarith)

lemma tri_eq_one_sub {t : ℝ} (h : t ∈ Set.Icc (0 : ℝ) 1) : (fun x : ℝ => max 0 (1 - |x|)) t = 1 - t := by
  rw [tri_eq_one_sub_abs (Set.mem_Icc.mpr ⟨by linarith [h.1], h.2⟩), abs_of_nonneg h.1]

lemma continuous_tri : Continuous (fun x : ℝ => max 0 (1 - |x|)) := by
  have : (fun x : ℝ => max 0 (1 - |x|)) = fun t : ℝ => max 0 (1 - |t|) := rfl
  rw [this]
  fun_prop

/-- The `[-1,0]` half of a symmetric integrand, by `t ↦ -t`. -/
lemma integral_neg_half (g : ℝ → ℝ) :
    ∫ t in (-1:ℝ)..0, g t = ∫ t in (0:ℝ)..1, g (-t) := by
  have h := intervalIntegral.integral_comp_neg (a := (-1:ℝ)) (b := 0) (f := fun t => g (-t))
  simpa using h

/-- `∫_{-1}^1 (fun x : ℝ => max 0 (1 - |x|)) · cos (θ ·) = 2 (1 - cos θ)/θ²` for `θ ≠ 0`. -/
theorem tri_mul_cos_integral {θ : ℝ} (hθ : θ ≠ 0) :
    ∫ t in (-1:ℝ)..1, (fun x : ℝ => max 0 (1 - |x|)) t * Real.cos (θ * t) = 2 * (1 - Real.cos θ) / θ ^ 2 := by
  have hpos : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => (fun x : ℝ => max 0 (1 - |x|)) t * Real.cos (θ * t)) volume a b := by
    intro a b; exact (continuous_tri.mul (by fun_prop : Continuous fun t : ℝ => Real.cos (θ*t))).intervalIntegrable _ _
  have hhalf : ∫ t in (0:ℝ)..1, (fun x : ℝ => max 0 (1 - |x|)) t * Real.cos (θ * t) = (1 - Real.cos θ) / θ ^ 2 := by
    rw [show ∫ t in (0:ℝ)..1, (fun x : ℝ => max 0 (1 - |x|)) t * Real.cos (θ * t)
        = ∫ t in (0:ℝ)..1, (1 - t) * Real.cos (θ * t) from
      intervalIntegral.integral_congr (fun t ht => by
        rw [tri_eq_one_sub (Set.mem_Icc.mpr ⟨by simpa using ht.1, by simpa using ht.2⟩)])]
    exact integral_one_sub_mul_cos hθ
  have hneg : ∫ t in (-1:ℝ)..0, (fun x : ℝ => max 0 (1 - |x|)) t * Real.cos (θ * t) = (1 - Real.cos θ) / θ ^ 2 := by
    rw [integral_neg_half (fun t => (fun x : ℝ => max 0 (1 - |x|)) t * Real.cos (θ * t))]
    have : ∀ t : ℝ, (fun x : ℝ => max 0 (1 - |x|)) (-t) * Real.cos (θ * (-t)) = (fun x : ℝ => max 0 (1 - |x|)) t * Real.cos (θ * t) := by
      intro t; rw [tri_even, mul_neg, Real.cos_neg]
    rw [show (fun t => (fun x : ℝ => max 0 (1 - |x|)) (-t) * Real.cos (θ * (-t))) = (fun t => (fun x : ℝ => max 0 (1 - |x|)) t * Real.cos (θ * t)) from
      funext this, hhalf]
  have hadj := intervalIntegral.integral_add_adjacent_intervals (hpos (-1) 0) (hpos 0 1)
  rw [← hadj, hhalf, hneg]
  ring

/-- `∫_{-1}^1 (fun x : ℝ => max 0 (1 - |x|)) · sin (θ ·) = 0`. -/
theorem tri_mul_sin_integral (θ : ℝ) :
    ∫ t in (-1:ℝ)..1, (fun x : ℝ => max 0 (1 - |x|)) t * Real.sin (θ * t) = 0 := by
  have hpos : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => (fun x : ℝ => max 0 (1 - |x|)) t * Real.sin (θ * t)) volume a b := by
    intro a b; exact (continuous_tri.mul (by fun_prop : Continuous fun t : ℝ => Real.sin (θ*t))).intervalIntegrable _ _
  have hadj := intervalIntegral.integral_add_adjacent_intervals (hpos (-1) 0) (hpos 0 1)
  rw [← hadj]
  have hneg : ∫ t in (-1:ℝ)..0, (fun x : ℝ => max 0 (1 - |x|)) t * Real.sin (θ * t) =
      -∫ t in (0:ℝ)..1, (fun x : ℝ => max 0 (1 - |x|)) t * Real.sin (θ * t) := by
    rw [integral_neg_half (fun t => (fun x : ℝ => max 0 (1 - |x|)) t * Real.sin (θ * t))]
    have : ∀ t : ℝ, (fun x : ℝ => max 0 (1 - |x|)) (-t) * Real.sin (θ * (-t)) = -((fun x : ℝ => max 0 (1 - |x|)) t * Real.sin (θ * t)) := by
      intro t; rw [tri_even, mul_neg, Real.sin_neg]; ring
    rw [show (fun t => (fun x : ℝ => max 0 (1 - |x|)) (-t) * Real.sin (θ * (-t))) = (fun t => -((fun x : ℝ => max 0 (1 - |x|)) t * Real.sin (θ * t))) from
      funext this, intervalIntegral.integral_neg]
  rw [hneg]; ring



lemma integral_tri_one : ∫ t in (-1:ℝ)..1, (fun x : ℝ => max 0 (1 - |x|)) t = 1 := by
  have hcont : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => (fun x : ℝ => max 0 (1 - |x|)) t) volume a b := fun a b =>
    continuous_tri.intervalIntegrable _ _
  have hadj := intervalIntegral.integral_add_adjacent_intervals (hcont (-1) 0) (hcont 0 1)
  rw [← hadj]
  have hneg : ∫ t in (-1:ℝ)..0, (fun x : ℝ => max 0 (1 - |x|)) t = ∫ t in (0:ℝ)..1, (fun x : ℝ => max 0 (1 - |x|)) t := by
    rw [integral_neg_half (fun t => (fun x : ℝ => max 0 (1 - |x|)) t)]
    simp only [tri_even]
  have hhalf : ∫ t in (0:ℝ)..1, (fun x : ℝ => max 0 (1 - |x|)) t = 1 / 2 := by
    rw [show ∫ t in (0:ℝ)..1, (fun x : ℝ => max 0 (1 - |x|)) t = ∫ t in (0:ℝ)..1, (1 - t) from
      intervalIntegral.integral_congr (fun t ht => tri_eq_one_sub (Set.mem_Icc.mpr
        ⟨by simpa using ht.1, by simpa using ht.2⟩))]
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_id]
    simp
    norm_num
  rw [hneg, hhalf]; norm_num

/-- `∫_ℝ (fun x : ℝ => max 0 (1 - |x|)) · e(· ξ) = sinc²(π ξ)`, i.e. the triangle is the inverse transform of `sinc²`. -/
theorem tri_fourier_exp (ξ : ℝ) :
    ∫ t in (-1:ℝ)..1, (((fun x : ℝ => max 0 (1 - |x|)) t : ℝ) : ℂ) *
        Complex.exp (↑(2 * Real.pi * (t * ξ)) * Complex.I)
      = ((Real.sinc (Real.pi * ξ)) ^ 2 : ℂ) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have h : ∀ t : ℝ, (((fun x : ℝ => max 0 (1 - |x|)) t : ℝ) : ℂ) * Complex.exp (↑(2 * Real.pi * (t * 0)) * Complex.I)
        = (((fun x : ℝ => max 0 (1 - |x|)) t : ℝ) : ℂ) := by
      intro t; simp
    simp_rw [h]
    rw [intervalIntegral.integral_ofReal, integral_tri_one]
    simp [Real.sinc_zero]
  · set θ : ℝ := 2 * Real.pi * ξ with hθdef
    have hθ : θ ≠ 0 := by
      rw [hθdef]; exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hξ
    have hpt : ∀ t : ℝ, (((fun x : ℝ => max 0 (1 - |x|)) t : ℝ) : ℂ) * Complex.exp (↑(2 * Real.pi * (t * ξ)) * Complex.I)
        = (((fun x : ℝ => max 0 (1 - |x|)) t * Real.cos (θ * t) : ℝ) : ℂ) + (((fun x : ℝ => max 0 (1 - |x|)) t * Real.sin (θ * t) : ℝ) : ℂ) * Complex.I := by
      intro t
      have harg : (↑(2 * Real.pi * (t * ξ)) * Complex.I) = (↑(θ * t) : ℂ) * Complex.I := by
        rw [hθdef]; push_cast; ring
      rw [harg, Complex.exp_ofReal_mul_I, Complex.ofReal_cos]
      push_cast
      ring
    have hint1 : IntervalIntegrable (fun t : ℝ => (((fun x : ℝ => max 0 (1 - |x|)) t * Real.cos (θ * t) : ℝ) : ℂ)) volume (-1) 1 :=
      (Complex.continuous_ofReal.comp
        (continuous_tri.mul (by fun_prop : Continuous fun t : ℝ => Real.cos (θ * t)))).intervalIntegrable _ _
    have hint2 : IntervalIntegrable (fun t : ℝ => (((fun x : ℝ => max 0 (1 - |x|)) t * Real.sin (θ * t) : ℝ) : ℂ)) volume (-1) 1 :=
      (Complex.continuous_ofReal.comp
        (continuous_tri.mul (by fun_prop : Continuous fun t : ℝ => Real.sin (θ * t)))).intervalIntegrable _ _
    simp_rw [hpt]
    rw [intervalIntegral.integral_add hint1 (hint2.mul_const Complex.I),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal,
      tri_mul_cos_integral hθ, tri_mul_sin_integral]
    have hval : 2 * (1 - Real.cos θ) / θ ^ 2 = (Real.sin (Real.pi * ξ) / (Real.pi * ξ)) ^ 2 := by
      have hsin2 : Real.sin (Real.pi * ξ) ^ 2 = 1 - Real.cos (Real.pi * ξ) ^ 2 := Real.sin_sq _
      have hcos2 : Real.cos (2 * (Real.pi * ξ)) = 2 * Real.cos (Real.pi * ξ) ^ 2 - 1 :=
        Real.cos_two_mul _
      have hπξ : Real.pi * ξ ≠ 0 := mul_ne_zero Real.pi_ne_zero hξ
      rw [hθdef, show 2 * Real.pi * ξ = 2 * (Real.pi * ξ) by ring, hcos2]
      field_simp
      nlinarith [hsin2]
    rw [hval, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hξ)]
    simp only [Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_zero, zero_mul, add_zero]



lemma tri_eq_zero_of_one_lt_abs {t : ℝ} (h : 1 < |t|) : (fun x : ℝ => max 0 (1 - |x|)) t = 0 := by
  have : 1 - |t| < 0 := by linarith
  show max 0 (1 - |t|) = 0
  exact max_eq_left this.le

lemma tri_eq_zero_of_one_le_abs {t : ℝ} (h : 1 ≤ |t|) : (fun x : ℝ => max 0 (1 - |x|)) t = 0 := by
  have : 1 - |t| ≤ 0 := by linarith
  show max 0 (1 - |t|) = 0
  exact max_eq_left this

lemma integrable_tri : Integrable (fun t : ℝ => (((fun x : ℝ => max 0 (1 - |x|)) t : ℝ) : ℂ)) := by
  have hon : IntegrableOn (fun t : ℝ => (((fun x : ℝ => max 0 (1 - |x|)) t : ℝ) : ℂ)) (Set.Icc (-1:ℝ) 1) :=
    (Complex.continuous_ofReal.comp continuous_tri).integrableOn_Icc
  refine hon.integrable_of_forall_notMem_eq_zero (fun x hx => ?_)
  have h1 : 1 < |x| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [tri_eq_zero_of_one_lt_abs h1]
  simp

lemma integrable_sinc_sq : Integrable (fun ξ : ℝ => (Real.sinc (Real.pi * ξ)) ^ 2) := by
  have hg : Integrable (fun ξ : ℝ => 2 * (1 + ξ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul 2
  refine Integrable.mono' hg ((Real.continuous_sinc.comp (by fun_prop)).pow 2).aestronglyMeasurable ?_
  filter_upwards with ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  by_cases hle : |ξ| ≤ 1
  · have h1 : Real.sinc (Real.pi * ξ) ^ 2 ≤ 1 := by
      nlinarith [Real.neg_one_le_sinc (Real.pi * ξ), Real.sinc_le_one (Real.pi * ξ)]
    have h2 : 1 ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
      rw [show (2:ℝ) * (1 + ξ^2)⁻¹ = 2 / (1 + ξ^2) by ring]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [abs_nonneg ξ, sq_abs ξ, sq_nonneg ξ]
    linarith
  · have hgt : 1 < |ξ| := not_le.mp hle
    have hπ : (0:ℝ) < Real.pi := Real.pi_pos
    have hne : Real.pi * ξ ≠ 0 := by
      have hξ0 : ξ ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at hgt
        linarith
      exact mul_ne_zero Real.pi_ne_zero hξ0
    have habs : |Real.sinc (Real.pi * ξ)| ≤ |Real.pi * ξ|⁻¹ := by
      rw [Real.sinc_of_ne_zero hne, abs_div, div_le_iff₀ (abs_pos.mpr hne)]
      rw [inv_mul_cancel₀ (ne_of_gt (abs_pos.mpr hne))]
      exact Real.abs_sin_le_one _
    have h1 : Real.sinc (Real.pi * ξ) ^ 2 ≤ ((Real.pi * ξ) ^ 2)⁻¹ := by
      calc Real.sinc (Real.pi * ξ) ^ 2 = |Real.sinc (Real.pi * ξ)| ^ 2 := (sq_abs _).symm
        _ ≤ (|Real.pi * ξ|⁻¹) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
        _ = ((Real.pi * ξ) ^ 2)⁻¹ := by rw [inv_pow, sq_abs]
    have h2 : ((Real.pi * ξ) ^ 2)⁻¹ ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
      have hA : (0:ℝ) < (Real.pi * ξ) ^ 2 := by positivity
      have hB : (0:ℝ) < (1 + ξ ^ 2) / 2 := by positivity
      have key : (1 + ξ ^ 2) / 2 ≤ (Real.pi * ξ) ^ 2 := by
        have hπ2 : (1:ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
        have hξ2 : (1:ℝ) ≤ ξ ^ 2 := by nlinarith [abs_nonneg ξ, sq_abs ξ, sq_nonneg ξ]
        have hsq : (Real.pi * ξ) ^ 2 = Real.pi ^ 2 * ξ ^ 2 := by ring
        rw [hsq]; nlinarith
      calc ((Real.pi * ξ) ^ 2)⁻¹ ≤ ((1 + ξ ^ 2) / 2)⁻¹ := (inv_le_inv₀ hA hB).mpr key
        _ = 2 * (1 + ξ ^ 2)⁻¹ := by field_simp
    linarith



/-- `∫_{-1}^1 (fun x : ℝ => max 0 (1 - |x|)) · e(-· ξ) = sinc²(π ξ)`: the same integral with the opposite sign, by symmetry. -/
theorem tri_fourier_exp_neg (ξ : ℝ) :
    ∫ t in (-1:ℝ)..1, (((fun x : ℝ => max 0 (1 - |x|)) t : ℝ) : ℂ) *
        Complex.exp (-(↑(2 * Real.pi * (t * ξ)) * Complex.I))
      = ((Real.sinc (Real.pi * ξ)) ^ 2 : ℂ) := by
  have hsym := intervalIntegral.integral_comp_neg (a := (-1:ℝ)) (b := 1)
    (f := fun s : ℝ => (((fun x : ℝ => max 0 (1 - |x|)) s : ℝ) : ℂ) * Complex.exp (-(↑(2 * Real.pi * (s * ξ)) * Complex.I)))
  simp only [neg_neg] at hsym
  rw [← hsym]
  have hpt : ∀ x : ℝ, (((fun x : ℝ => max 0 (1 - |x|)) (-x) : ℝ) : ℂ) * Complex.exp (-(↑(2 * Real.pi * (-x * ξ)) * Complex.I))
      = (((fun x : ℝ => max 0 (1 - |x|)) x : ℝ) : ℂ) * Complex.exp (↑(2 * Real.pi * (x * ξ)) * Complex.I) := by
    intro x
    rw [tri_even]
    have he : -(↑(2 * Real.pi * (-x * ξ)) * Complex.I) = ↑(2 * Real.pi * (x * ξ)) * Complex.I := by
      push_cast; ring
    rw [he]
  simp only [hpt]
  exact tri_fourier_exp ξ

/-- The Fourier transform of the triangle is `sinc²(π ·)`, in Mathlib's convention. -/
theorem fourier_tri_apply (ξ : ℝ) :
    FourierTransform.fourier (fun t : ℝ => (((fun x : ℝ => max 0 (1 - |x|)) t : ℝ) : ℂ)) ξ = ((Real.sinc (Real.pi * ξ)) ^ 2 : ℂ) := by
  rw [fourier_eq]
  have hpt : ∀ v : ℝ, fourierChar (-(inner ℝ v ξ)) • (((fun x : ℝ => max 0 (1 - |x|)) v : ℝ) : ℂ)
      = (((fun x : ℝ => max 0 (1 - |x|)) v : ℝ) : ℂ) * Complex.exp (-(↑(2 * Real.pi * (v * ξ)) * Complex.I)) := by
    intro v
    rw [Circle.smul_def, Real.fourierChar_apply, Real.inner_apply, smul_eq_mul]
    have he : (↑(2 * Real.pi * -(v * ξ)) * Complex.I) = -(↑(2 * Real.pi * (v * ξ)) * Complex.I) := by
      push_cast; ring
    rw [he, mul_comm]
  simp_rw [hpt]
  have hzero : ∀ x ∉ Set.Ioc (-1:ℝ) 1,
      (((fun x : ℝ => max 0 (1 - |x|)) x : ℝ) : ℂ) * Complex.exp (-(↑(2 * Real.pi * (x * ξ)) * Complex.I)) = 0 := by
    intro x hx
    simp only [Set.mem_Ioc, not_and_or, not_lt] at hx
    have hx1 : 1 ≤ |x| := by
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [tri_eq_zero_of_one_le_abs hx1]
    simp
  have e1 : ∫ x : ℝ, (((fun x : ℝ => max 0 (1 - |x|)) x : ℝ) : ℂ) * Complex.exp (-(↑(2 * Real.pi * (x * ξ)) * Complex.I))
      = ∫ x in Set.Ioc (-1:ℝ) 1, (((fun x : ℝ => max 0 (1 - |x|)) x : ℝ) : ℂ) * Complex.exp
          (-(↑(2 * Real.pi * (x * ξ)) * Complex.I)) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  rw [e1, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  exact tri_fourier_exp_neg ξ

/-- The pointwise comparison `sinc²(π ξ) ≤ 2/(1 + ξ²)`. -/
lemma sinc_sq_le_two_inv (ξ : ℝ) :
    (Real.sinc (Real.pi * ξ)) ^ 2 ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
  by_cases hle : |ξ| ≤ 1
  · have h1 : Real.sinc (Real.pi * ξ) ^ 2 ≤ 1 := by
      nlinarith [Real.neg_one_le_sinc (Real.pi * ξ), Real.sinc_le_one (Real.pi * ξ)]
    have h2 : 1 ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
      rw [show (2:ℝ) * (1 + ξ^2)⁻¹ = 2 / (1 + ξ^2) by ring]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [abs_nonneg ξ, sq_abs ξ, sq_nonneg ξ]
    linarith
  · have hgt : 1 < |ξ| := not_le.mp hle
    have hne : Real.pi * ξ ≠ 0 := by
      refine mul_ne_zero Real.pi_ne_zero (fun h0 => ?_)
      rw [h0, abs_zero] at hgt; linarith
    have habs : |Real.sinc (Real.pi * ξ)| ≤ |Real.pi * ξ|⁻¹ := by
      rw [Real.sinc_of_ne_zero hne, abs_div, div_le_iff₀ (abs_pos.mpr hne)]
      rw [inv_mul_cancel₀ (ne_of_gt (abs_pos.mpr hne))]
      exact Real.abs_sin_le_one _
    have h1 : Real.sinc (Real.pi * ξ) ^ 2 ≤ ((Real.pi * ξ) ^ 2)⁻¹ := by
      calc Real.sinc (Real.pi * ξ) ^ 2 = |Real.sinc (Real.pi * ξ)| ^ 2 := (sq_abs _).symm
        _ ≤ (|Real.pi * ξ|⁻¹) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
        _ = ((Real.pi * ξ) ^ 2)⁻¹ := by rw [inv_pow, sq_abs]
    have h2 : ((Real.pi * ξ) ^ 2)⁻¹ ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
      have hA : (0:ℝ) < (Real.pi * ξ) ^ 2 := by positivity
      have hB : (0:ℝ) < (1 + ξ ^ 2) / 2 := by positivity
      have key : (1 + ξ ^ 2) / 2 ≤ (Real.pi * ξ) ^ 2 := by
        have hπ2 : (1:ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
        have hξ2 : (1:ℝ) ≤ ξ ^ 2 := by nlinarith [abs_nonneg ξ, sq_abs ξ, sq_nonneg ξ]
        have hsq : (Real.pi * ξ) ^ 2 = Real.pi ^ 2 * ξ ^ 2 := by ring
        rw [hsq]; nlinarith
      calc ((Real.pi * ξ) ^ 2)⁻¹ ≤ ((1 + ξ ^ 2) / 2)⁻¹ := (inv_le_inv₀ hA hB).mpr key
        _ = 2 * (1 + ξ ^ 2)⁻¹ := by field_simp
    linarith

lemma integrable_sinc_sq_complex :
    Integrable (fun ξ : ℝ => ((Real.sinc (Real.pi * ξ)) ^ 2 : ℂ)) := by
  have hg : Integrable (fun ξ : ℝ => 2 * (1 + ξ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul 2
  refine Integrable.mono' hg
    (((Complex.continuous_ofReal.comp Real.continuous_sinc).comp (by fun_prop : Continuous
      fun ξ : ℝ => Real.pi * ξ)).pow 2).aestronglyMeasurable ?_
  filter_upwards with ξ
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact sinc_sq_le_two_inv ξ

/-- Fourier inversion, with the function kept abstract so that the instance search is the generic
one: if `𝓕 f = sinc²(π ·)` then `∫ sinc²(π α) e(α t) dα = f t`. -/
theorem sinc_sq_integral_of_fourier_eq (f : ℝ → ℂ) (hcont : Continuous f)
    (hint : Integrable f volume)
    (hfour : FourierTransform.fourier f = fun ξ => ((Real.sinc (Real.pi * ξ)) ^ 2 : ℂ))
    (t : ℝ) :
    ∫ α : ℝ, ((Real.sinc (Real.pi * α)) ^ 2 : ℂ) *
        Complex.exp (↑(2 * Real.pi * (α * t)) * Complex.I) = f t := by
  have hsplit : Integrable (FourierTransform.fourier f) volume := by
    rw [hfour]
    exact integrable_sinc_sq_complex
  have hinv : FourierTransformInv.fourierInv (FourierTransform.fourier f) = f :=
    Continuous.fourierInv_fourier_eq hcont hint hsplit
  have hfin := congrFun hinv t
  rw [fourierInv_eq_fourier_neg (w := t),
    fourier_eq (f := FourierTransform.fourier f) (w := (-t))] at hfin
  have hpt : ∀ v : ℝ, fourierChar (-(inner ℝ v (-t))) • (FourierTransform.fourier f v)
      = Complex.exp (↑(2 * Real.pi * (v * t)) * Complex.I) * ((Real.sinc (Real.pi * v)) ^ 2 : ℂ) := by
    intro v
    rw [hfour, Circle.smul_def, Real.fourierChar_apply, Real.inner_apply, smul_eq_mul]
    have he : (↑(2 * Real.pi * -(v * -t)) * Complex.I) = (↑(2 * Real.pi * (v * t)) * Complex.I) := by
      push_cast; ring
    rw [he]
  simp_rw [hpt] at hfin
  have hswap : ∫ α : ℝ, ((Real.sinc (Real.pi * α)) ^ 2 : ℂ) *
        Complex.exp (↑(2 * Real.pi * (α * t)) * Complex.I)
      = ∫ α : ℝ, Complex.exp (↑(2 * Real.pi * (α * t)) * Complex.I) *
          ((Real.sinc (Real.pi * α)) ^ 2 : ℂ) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with α
    ring
  rw [hswap]
  exact hfin

/-- Fourier inversion in the form needed: the `sinc²(π ·)` integral over `ℝ` is the triangle. -/
theorem sinc_sq_fourier_integral (t : ℝ) :
    ∫ α : ℝ, ((Real.sinc (Real.pi * α)) ^ 2 : ℂ) *
        Complex.exp (↑(2 * Real.pi * (α * t)) * Complex.I) = (((fun x : ℝ => max 0 (1 - |x|)) t : ℝ) : ℂ) :=
  sinc_sq_integral_of_fourier_eq (fun s : ℝ => (((fun x : ℝ => max 0 (1 - |x|)) s : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp continuous_tri) integrable_tri (funext fourier_tri_apply) t





/-- `eC` agrees with the exponential used in the inversion statement. -/
lemma eC_eq (x : ℝ) :
    LeanLab.ExceptionalSet.U1539.eC x = Complex.exp (↑(2 * Real.pi * x) * Complex.I) := by
  unfold LeanLab.ExceptionalSet.U1539.eC
  congr 1
  push_cast
  ring

/-- The scaled `sinc²` integral: substituting `β = c α`. -/
theorem sinc_sq_scale {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ∫ α : ℝ, ((Real.sinc (Real.pi * (c * α))) ^ 2 : ℂ) *
        Complex.exp (↑(2 * Real.pi * (α * t)) * Complex.I) = c⁻¹ * (((fun x : ℝ => max 0 (1 - |x|)) (t / c) : ℝ) : ℂ) := by
  have harg : ∀ α : ℝ, ((c * α) * (t / c)) = α * t := by
    intro α; field_simp
  have hrw : ∀ α : ℝ, ((Real.sinc (Real.pi * (c * α))) ^ 2 : ℂ) *
      Complex.exp (↑(2 * Real.pi * (α * t)) * Complex.I)
      = (fun β : ℝ => ((Real.sinc (Real.pi * β)) ^ 2 : ℂ) *
        Complex.exp (↑(2 * Real.pi * (β * (t / c))) * Complex.I)) (c * α) := by
    intro α; simp only [harg]
  have hmain := MeasureTheory.Measure.integral_comp_mul_left
    (fun β : ℝ => ((Real.sinc (Real.pi * β)) ^ 2 : ℂ) *
      Complex.exp (↑(2 * Real.pi * (β * (t / c))) * Complex.I)) c
  conv_lhs => arg 2; ext α; rw [hrw α]
  rw [hmain]
  rw [abs_of_pos (inv_pos.mpr hc), Complex.real_smul, sinc_sq_fourier_integral]

/-- The `sinc²` integrand times an exponential is integrable. -/
lemma integrable_sinc_sq_mul_exp {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    Integrable (fun α : ℝ => ((Real.sinc (Real.pi * (c * α))) ^ 2 : ℂ) *
      Complex.exp (↑(2 * Real.pi * (α * t)) * Complex.I)) := by
  have hmeas : AEStronglyMeasurable (fun α : ℝ => ((Real.sinc (Real.pi * (c * α))) ^ 2 : ℂ) *
      Complex.exp (↑(2 * Real.pi * (α * t)) * Complex.I)) volume := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  have hcont : Continuous (fun α : ℝ => ((Real.sinc (Real.pi * c * α)) ^ 2 : ℂ)) := by
    fun_prop
  have hbase : Integrable (fun α : ℝ => ((Real.sinc (Real.pi * (c * α))) ^ 2 : ℂ)) := by
    have h := integrable_sinc_sq_complex.comp_mul_left' (R := c) hc
    simpa using h
  refine Integrable.mono hbase hmeas (Filter.Eventually.of_forall (fun α => ?_))
  rw [norm_mul]
  have he : ‖Complex.exp (↑(2 * Real.pi * (α * t)) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [he, mul_one]



open LeanLab.ExceptionalSet.U1539 (Kfun eC)

/-- The `sinc²(π ·)` factor against `eC`: the inversion value. -/
lemma sinc_sq_eC_integral (t : ℝ) :
    ∫ α : ℝ, ((Real.sinc (Real.pi * α)) ^ 2 : ℂ) * eC (α * t) = (((fun x : ℝ => max 0 (1 - |x|)) t : ℝ) : ℂ) := by
  have hpt : ∀ α : ℝ, ((Real.sinc (Real.pi * α)) ^ 2 : ℂ) * eC (α * t)
      = ((Real.sinc (Real.pi * α)) ^ 2 : ℂ) * Complex.exp (↑(2 * Real.pi * (α * t)) * Complex.I) := by
    intro α; rw [eC_eq]
  simp_rw [hpt]
  exact sinc_sq_fourier_integral t

/-- The scaled factor against `eC`. -/
lemma sinc_sq_eC_integral_scale {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ∫ α : ℝ, ((Real.sinc (Real.pi * (c * α))) ^ 2 : ℂ) * eC (α * t)
      = ((c⁻¹ : ℝ) : ℂ) * (((fun x : ℝ => max 0 (1 - |x|)) (t / c) : ℝ) : ℂ) := by
  have hpt : ∀ α : ℝ, ((Real.sinc (Real.pi * (c * α))) ^ 2 : ℂ) * eC (α * t)
      = ((Real.sinc (Real.pi * (c * α))) ^ 2 : ℂ) *
          Complex.exp (↑(2 * Real.pi * (α * t)) * Complex.I) := by
    intro α; rw [eC_eq]
  simp_rw [hpt]
  exact sinc_sq_scale hc t

lemma integrable_sinc_sq_eC (t : ℝ) :
    Integrable (fun α : ℝ => ((Real.sinc (Real.pi * α)) ^ 2 : ℂ) * eC (α * t)) := by
  have hpt : (fun α : ℝ => ((Real.sinc (Real.pi * α)) ^ 2 : ℂ) * eC (α * t))
      = (fun α : ℝ => ((Real.sinc (Real.pi * (1 * α))) ^ 2 : ℂ) *
          Complex.exp (↑(2 * Real.pi * (α * t)) * Complex.I)) := by
    funext α; rw [eC_eq]; norm_num
  rw [hpt]
  exact integrable_sinc_sq_mul_exp one_ne_zero t

lemma integrable_sinc_sq_eC_scale {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    Integrable (fun α : ℝ => ((Real.sinc (Real.pi * (c * α))) ^ 2 : ℂ) * eC (α * t)) := by
  have hpt : (fun α : ℝ => ((Real.sinc (Real.pi * (c * α))) ^ 2 : ℂ) * eC (α * t))
      = (fun α : ℝ => ((Real.sinc (Real.pi * (c * α))) ^ 2 : ℂ) *
          Complex.exp (↑(2 * Real.pi * (α * t)) * Complex.I)) := by
    funext α; rw [eC_eq]
  rw [hpt]
  exact integrable_sinc_sq_mul_exp hc t

/-- The transform of the paper's kernel `Kfun Δ` on the real line. -/
theorem Kfun_fourier {Δ t : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∫ α : ℝ, ((Kfun Δ α : ℝ) : ℂ) * eC (α * t)
      = (Δ⁻¹ : ℂ) * (((fun x : ℝ => max 0 (1 - |x|)) t : ℝ) : ℂ)
        - (((Δ⁻¹ * (1 - Δ) ^ 2) : ℝ) : ℂ) *
            ((1 - Δ)⁻¹ * (((fun x : ℝ => max 0 (1 - |x|)) (t / (1 - Δ)) : ℝ) : ℂ)) := by
  have h1d : (0:ℝ) < 1 - Δ := by linarith
  have hpt : ∀ α : ℝ, ((Kfun Δ α : ℝ) : ℂ) * eC (α * t)
      = ((Δ⁻¹ : ℂ) * (((Real.sinc (Real.pi * α)) ^ 2 : ℂ) * eC (α * t))
          - (((Δ⁻¹ * (1 - Δ) ^ 2) : ℝ) : ℂ) *
              (((Real.sinc (Real.pi * ((1 - Δ) * α))) ^ 2 : ℂ) * eC (α * t))) := by
    intro α
    simp only [Kfun]
    push_cast
    have hs : Real.sinc (Real.pi * (1 - Δ) * α) = Real.sinc (Real.pi * ((1 - Δ) * α)) := by
      congr 1; ring
    rw [hs]
    ring
  rw [show ∫ α : ℝ, ((Kfun Δ α : ℝ) : ℂ) * eC (α * t)
      = ∫ α : ℝ, ((Δ⁻¹ : ℂ) * (((Real.sinc (Real.pi * α)) ^ 2 : ℂ) * eC (α * t))
          - (((Δ⁻¹ * (1 - Δ) ^ 2) : ℝ) : ℂ) *
              (((Real.sinc (Real.pi * ((1 - Δ) * α))) ^ 2 : ℂ) * eC (α * t))) from by
    simp_rw [hpt]]
  rw [MeasureTheory.integral_sub (integrable_sinc_sq_eC t |>.const_mul _)
      (integrable_sinc_sq_eC_scale h1d.ne' t |>.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    sinc_sq_eC_integral, sinc_sq_eC_integral_scale h1d]

/-- **The kernel's Fourier support.**  For `0 < Δ < 1` the transform of `Kfun Δ` vanishes off
`(-1, 1)`: this is the vanishing of the paper's weight `w` for `|x| ≥ 1`. -/
theorem Kfun_fourier_zero {Δ t : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (ht : 1 ≤ |t|) :
    ∫ α : ℝ, ((Kfun Δ α : ℝ) : ℂ) * eC (α * t) = 0 := by
  rw [Kfun_fourier hΔ0 hΔ1]
  have ht0 : (fun x : ℝ => max 0 (1 - |x|)) t = 0 := tri_eq_zero_of_one_le_abs ht
  have h1d : (0:ℝ) < 1 - Δ := by linarith
  have hle : |1 - Δ| ≤ 1 := by
    rw [abs_of_pos h1d]; linarith
  have hdiv : 1 ≤ |t / (1 - Δ)| := by
    rw [abs_div, abs_of_pos h1d, le_div_iff₀ h1d]
    linarith
  rw [ht0, tri_eq_zero_of_one_le_abs hdiv]
  simp



open LeanLab.ExceptionalSet.U1539 (Kfun eC Sp majorArcs calE)
open LeanLab.ExceptionalSet.DecompJ200 (majorInt minorInt window blockCount Eγ_minor_block Eγ_major_block)

attribute [local instance] Classical.propDecidable
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F Solvable)

/-- `eC` has modulus one. -/
lemma norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  unfold LeanLab.ExceptionalSet.U1539.eC
  rw [Complex.norm_exp]
  simp

/-- The major arcs are Borel: a countable union of closed arcs. -/
lemma measurableSet_majorArcs (P X : ℝ) : MeasurableSet (majorArcs P X) := by
  have h : majorArcs P X = ⋃ (q : ℕ) (a : ℤ),
      {α : ℝ | 1 ≤ q ∧ (q : ℝ) ≤ P ∧ Int.gcd a q = 1 ∧ |q * α - a| ≤ P / X} := by
    ext α
    simp only [majorArcs, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [h]
  refine MeasurableSet.iUnion (fun q => MeasurableSet.iUnion (fun a => ?_))
  by_cases hq : 1 ≤ q ∧ (q : ℝ) ≤ P ∧ Int.gcd a q = 1
  · have he : {α : ℝ | 1 ≤ q ∧ (q : ℝ) ≤ P ∧ Int.gcd a q = 1 ∧ |q * α - a| ≤ P / X}
        = {α : ℝ | |(q : ℝ) * α - (a : ℝ)| ≤ P / X} := by
      ext α
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h; exact h.2.2.2
      · intro h; exact ⟨hq.1, hq.2.1, hq.2.2, h⟩
    rw [he]
    exact isClosed_le (by fun_prop : Continuous fun α : ℝ => |(q : ℝ) * α - (a : ℝ)|)
      continuous_const |>.measurableSet
  · have he : {α : ℝ | 1 ≤ q ∧ (q : ℝ) ≤ P ∧ Int.gcd a q = 1 ∧ |q * α - a| ≤ P / X} = ∅ := by
      ext α
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hq ⟨h.1, h.2.1, h.2.2.1⟩
    rw [he]
    exact MeasurableSet.empty

/-- The integrand of display (6) is integrable: `Sp²` is bounded and `Kfun Δ` is integrable. -/
lemma integrable_arc_integrand {γ δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (N n : ℕ) :
    Integrable (fun α : ℝ => Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
      (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ) * eC (-(α * F γ n))) := by
  set Δ := calE γ κ N ^ (-(1 / 8 : ℝ)) with hΔdef
  have hΔpos : 0 < Δ := by rw [hΔdef]; exact Real.rpow_pos_of_pos (Real.exp_pos _) _
  set S := (Finset.Ioc ⌊F γ N ^ (6 * δ)⌋₊ ⌊F γ N⌋₊).filter Nat.Prime with hS
  have hSpos : ∀ p ∈ S, (0:ℝ) ≤ Real.log p := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
  -- the two sinc² pieces are integrable
  have hint1 : Integrable (fun α : ℝ => ((Real.sinc (Real.pi * α)) ^ 2 : ℂ)) :=
    integrable_sinc_sq_complex
  have hK : Integrable (fun α : ℝ => (Kfun Δ α : ℂ)) := by
    by_cases hΔ1 : Δ = 1
    · have he : (fun α : ℝ => (Kfun Δ α : ℂ))
          = (fun α : ℝ => ((Real.sinc (Real.pi * α)) ^ 2 : ℂ)) := by
        funext α; simp [Kfun, hΔ1]
      rw [he]; exact integrable_sinc_sq_complex
    · have hint2 : Integrable (fun α : ℝ => ((Real.sinc (Real.pi * ((1 - Δ) * α))) ^ 2 : ℂ)) :=
        integrable_sinc_sq_complex.comp_mul_left' (R := 1 - Δ) (by intro h0; exact hΔ1 (by linarith))
      have he : (fun α : ℝ => (Kfun Δ α : ℂ))
          = (fun α : ℝ => (Δ⁻¹ : ℂ) * (((Real.sinc (Real.pi * α)) ^ 2 : ℂ))
              - (((Δ⁻¹ * (1 - Δ) ^ 2) : ℝ) : ℂ) *
                  ((Real.sinc (Real.pi * ((1 - Δ) * α))) ^ 2 : ℂ)) := by
        funext α
        simp only [Kfun]
        push_cast
        have hs : Real.sinc (Real.pi * (1 - Δ) * α) = Real.sinc (Real.pi * ((1 - Δ) * α)) := by
          congr 1; ring
        rw [hs]
        ring
      rw [he]
      exact (hint1.const_mul _).sub (hint2.const_mul _)
  -- `Sp` is bounded, hence so is its square
  have hSp : ∀ α : ℝ, ‖Sp (F γ N ^ (6 * δ)) (F γ N) α‖ ≤ ∑ p ∈ S, Real.log p := by
    intro α
    have hsum : Sp (F γ N ^ (6 * δ)) (F γ N) α = ∑ p ∈ S, (Real.log p : ℂ) * eC (α * p) := rfl
    rw [hsum]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [norm_mul, Complex.norm_real, norm_eC, mul_one, Real.norm_eq_abs, abs_of_nonneg (hSpos p hp)]
  have hbound : ∀ α : ℝ, ‖Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
      (Kfun Δ α : ℂ) * eC (-(α * F γ n))‖ ≤
      (∑ p ∈ S, Real.log p) ^ 2 * ‖(Kfun Δ α : ℂ)‖ := by
    intro α
    rw [norm_mul, norm_mul, norm_eC, mul_one]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hSp α) 2
  have hSpcont : Continuous (fun α : ℝ => Sp (F γ N ^ (6 * δ)) (F γ N) α) := by
    have he : (fun α : ℝ => Sp (F γ N ^ (6 * δ)) (F γ N) α)
        = (fun α : ℝ => ∑ p ∈ S, (Real.log p : ℂ) *
            Complex.exp (↑(2 * Real.pi * (α * p)) * Complex.I)) := by
      funext α
      simp only [Sp, eC_eq, hS]
    rw [he]
    fun_prop
  have hmeas : AEStronglyMeasurable (fun α : ℝ => Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
      (Kfun Δ α : ℂ) * eC (-(α * F γ n))) volume := by
    apply Continuous.aestronglyMeasurable
    refine Continuous.mul (Continuous.mul (Continuous.pow hSpcont 2) ?_) ?_
    · have he : (fun α : ℝ => (Kfun Δ α : ℂ))
          = (fun α : ℝ => (Δ⁻¹ : ℂ) * (((Real.sinc (Real.pi * α)) ^ 2 : ℂ))
              - (((Δ⁻¹ * (1 - Δ) ^ 2) : ℝ) : ℂ) *
                  ((Real.sinc (Real.pi * ((1 - Δ) * α))) ^ 2 : ℂ)) := by
        funext α
        simp only [Kfun]
        push_cast
        have hs : Real.sinc (Real.pi * (1 - Δ) * α) = Real.sinc (Real.pi * ((1 - Δ) * α)) := by
          congr 1; ring
        rw [hs]
        ring
      rw [he]
      fun_prop
    · have he : (fun α : ℝ => eC (-(α * F γ n))) =
          fun α : ℝ => Complex.exp (↑(2 * Real.pi * (-(α * F γ n))) * Complex.I) := by
        funext α; rw [eC_eq]
      rw [he]; fun_prop
  refine Integrable.mono' (hK.norm.const_mul ((∑ p ∈ S, Real.log p) ^ 2)) hmeas
    (Filter.Eventually.of_forall hbound)

/-- Display (6): the two arc integrals add up to the complete integral. -/
lemma majorInt_add_minorInt {γ δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (N n : ℕ) :
    majorInt γ δ κ N n + minorInt γ δ κ N n
      = ∫ α : ℝ, Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
          (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ) * eC (-(α * F γ n)) :=
  MeasureTheory.integral_add_compl (measurableSet_majorArcs _ _)
    (integrable_arc_integrand hδ hκ N n)



open LeanLab.ExceptionalSet.U1539 (Kfun eC Sp majorArcs calE)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F Solvable)
open LeanLab.ExceptionalSet.DecompJ200 (majorInt minorInt window blockCount Eγ_minor_block Eγ_major_block)

attribute [local instance] Classical.propDecidable

/-- `eC` is multiplicative. -/
lemma eC_add (x y : ℝ) : eC x * eC y = eC (x + y) := by
  rw [eC_eq, eC_eq, eC_eq, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `‖Kfun Δ‖` is integrable. -/
lemma integrable_arc_Kfun {Δ : ℝ} (hΔ0 : 0 < Δ) :
    Integrable (fun α : ℝ => ‖(Kfun Δ α : ℂ)‖) := by
  by_cases hΔ1 : Δ = 1
  · have he : (fun α : ℝ => ‖(Kfun Δ α : ℂ)‖)
        = (fun α : ℝ => ‖(Real.sinc (Real.pi * α)) ^ 2‖) := by
      funext α
      rw [show Kfun Δ α = (Real.sinc (Real.pi * α)) ^ 2 by simp [Kfun, hΔ1], Complex.norm_real]
    rw [he]
    exact integrable_sinc_sq.norm
  · have hint1 : Integrable (fun α : ℝ => ((Real.sinc (Real.pi * α)) ^ 2 : ℂ)) :=
      integrable_sinc_sq_complex
    have hint2 : Integrable (fun α : ℝ => ((Real.sinc (Real.pi * ((1 - Δ) * α))) ^ 2 : ℂ)) :=
      integrable_sinc_sq_complex.comp_mul_left' (R := 1 - Δ)
        (by intro h0; exact hΔ1 (by linarith))
    have he : (fun α : ℝ => (Kfun Δ α : ℂ))
        = (fun α : ℝ => (Δ⁻¹ : ℂ) * (((Real.sinc (Real.pi * α)) ^ 2 : ℂ))
            - (((Δ⁻¹ * (1 - Δ) ^ 2) : ℝ) : ℂ) *
                ((Real.sinc (Real.pi * ((1 - Δ) * α))) ^ 2 : ℂ)) := by
      funext α
      simp only [Kfun]
      push_cast
      have hs : Real.sinc (Real.pi * (1 - Δ) * α) = Real.sinc (Real.pi * ((1 - Δ) * α)) := by
        congr 1; ring
      rw [hs]
      ring
    have hK : Integrable (fun α : ℝ => (Kfun Δ α : ℂ)) := by
      rw [he]
      exact (hint1.const_mul _).sub (hint2.const_mul _)
    exact hK.norm

/-- `Kfun Δ` times `eC` is integrable. -/
lemma integrable_Kfun_eC {Δ t : ℝ} (hΔ0 : 0 < Δ) :
    Integrable (fun α : ℝ => (Kfun Δ α : ℂ) * eC (α * t)) := by
  refine Integrable.mono' (integrable_arc_Kfun hΔ0) ?_ (Filter.Eventually.of_forall (fun α => ?_))
  · apply Continuous.aestronglyMeasurable
    refine Continuous.mul ?_ ?_
    · have he : (fun α : ℝ => (Kfun Δ α : ℂ))
          = (fun α : ℝ => (Δ⁻¹ : ℂ) * (((Real.sinc (Real.pi * α)) ^ 2 : ℂ))
              - ((((Δ⁻¹ * (1 - Δ) ^ 2) : ℝ) : ℂ)) *
                  ((Real.sinc (Real.pi * ((1 - Δ) * α))) ^ 2 : ℂ)) := by
        funext α
        simp only [Kfun]
        push_cast
        have hs : Real.sinc (Real.pi * (1 - Δ) * α) = Real.sinc (Real.pi * ((1 - Δ) * α)) := by
          congr 1; ring
        rw [hs]
        ring
      rw [he]; fun_prop
    · have he : (fun α : ℝ => eC (α * t)) =
          fun α : ℝ => Complex.exp (↑(2 * Real.pi * (α * t)) * Complex.I) := by
        funext α; rw [eC_eq]
      rw [he]; fun_prop
  · rw [norm_mul, norm_eC, mul_one]

/-- The complete arc integral as a double sum over prime pairs, with the kernel transform as the
inner integral. -/
theorem arc_integral_eq_pairSum {γ δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (N n : ℕ) :
    (∫ α : ℝ, Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
        (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ) * eC (-(α * F γ n)))
      = ∑ p ∈ (Finset.Ioc ⌊F γ N ^ (6 * δ)⌋₊ ⌊F γ N⌋₊).filter Nat.Prime,
          ∑ q ∈ (Finset.Ioc ⌊F γ N ^ (6 * δ)⌋₊ ⌊F γ N⌋₊).filter Nat.Prime,
            ((Real.log p * Real.log q : ℝ) : ℂ) *
              ∫ α : ℝ, (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ) *
                eC (α * ((p : ℝ) + q - F γ n)) := by
  set Δ := calE γ κ N ^ (-(1 / 8 : ℝ)) with hΔdef
  have hΔpos : 0 < Δ := by rw [hΔdef]; exact Real.rpow_pos_of_pos (Real.exp_pos _) _
  set S := (Finset.Ioc ⌊F γ N ^ (6 * δ)⌋₊ ⌊F γ N⌋₊).filter Nat.Prime with hS
  have hpt : ∀ α : ℝ,
      Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * F γ n))
      = ∑ p ∈ S, ∑ q ∈ S, ((Real.log p * Real.log q : ℝ) : ℂ) *
          ((Kfun Δ α : ℂ) * eC (α * ((p : ℝ) + q - F γ n))) := by
    intro α
    have hSp : Sp (F γ N ^ (6 * δ)) (F γ N) α = ∑ p ∈ S, (Real.log p : ℂ) * eC (α * p) := rfl
    rw [hSp, pow_two, Finset.sum_mul_sum]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => ?_))
    have h1 : eC (α * p) * eC (α * q) = eC (α * ((p : ℝ) + q)) := by
      rw [eC_add]
      congr 1
      push_cast
      ring
    have h2 : eC (α * ((p : ℝ) + q)) * eC (-(α * F γ n)) = eC (α * ((p : ℝ) + q - F γ n)) := by
      rw [eC_add]
      congr 1
      ring
    calc ((Real.log p : ℂ) * eC (α * p)) * ((Real.log q : ℂ) * eC (α * q)) *
          (Kfun Δ α : ℂ) * eC (-(α * F γ n))
        = ((Real.log p * Real.log q : ℝ) : ℂ) * ((Kfun Δ α : ℂ) *
            ((eC (α * p) * eC (α * q)) * eC (-(α * F γ n)))) := by
          push_cast; ring
      _ = _ := by rw [h1, h2]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun q hq => ?_)
      rw [MeasureTheory.integral_const_mul]
    · intro q hq
      exact (integrable_Kfun_eC (t := ((p : ℝ) + q - F γ n)) hΔpos).const_mul _
  · intro p hp
    exact MeasureTheory.integrable_finsetSum S (f := fun q α =>
      ((Real.log p * Real.log q : ℝ) : ℂ) *
        ((Kfun Δ α : ℂ) * eC (α * ((p : ℝ) + q - F γ n))))
      (fun q hq => (integrable_Kfun_eC (t := ((p : ℝ) + q - F γ n)) hΔpos).const_mul _)



open LeanLab.ExceptionalSet.U1539 (Kfun eC Sp majorArcs calE)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F Solvable)
open LeanLab.ExceptionalSet.DecompJ200 (majorInt minorInt window blockCount Eγ_minor_block Eγ_major_block)

attribute [local instance] Classical.propDecidable

/-- `0 ≤ (fun x : ℝ => max 0 (1 - |x|)) ≤ 1`. -/
lemma tri_nonneg (t : ℝ) : 0 ≤ (fun x : ℝ => max 0 (1 - |x|)) t := le_max_left _ _
lemma tri_le_one (t : ℝ) : (fun x : ℝ => max 0 (1 - |x|)) t ≤ 1 := by
  have h : |t| ≥ 0 := abs_nonneg t
  show max 0 (1 - |t|) ≤ 1
  exact max_le zero_le_one (by linarith)

/-- The kernel transform is bounded by `2 / Δ` once `Δ ≤ 1`. -/
theorem Kfun_fourier_norm_le {Δ t : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1) :
    ‖∫ α : ℝ, (Kfun Δ α : ℂ) * eC (α * t)‖ ≤ 2 / Δ := by
  rcases lt_or_ge Δ 1 with hlt | hge
  · rw [Kfun_fourier hΔ0 hlt]
    have h1 : ‖(Δ⁻¹ : ℂ) * (((fun x : ℝ => max 0 (1 - |x|)) t : ℝ) : ℂ)‖ ≤ Δ⁻¹ := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΔ0,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tri_nonneg t)]
      calc Δ⁻¹ * (fun x : ℝ => max 0 (1 - |x|)) t ≤ Δ⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (tri_le_one t) (le_of_lt (inv_pos.mpr hΔ0))
        _ = Δ⁻¹ := by ring
    have h2 : ‖(((Δ⁻¹ * (1 - Δ) ^ 2) : ℝ) : ℂ) * ((1 - Δ)⁻¹ * (((fun x : ℝ => max 0 (1 - |x|)) (t / (1 - Δ)) : ℝ) : ℂ))‖
        ≤ Δ⁻¹ * (1 - Δ) := by
      have h1d : (0:ℝ) < 1 - Δ := by linarith
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have htri : ‖(1 - Δ)⁻¹ * (((fun x : ℝ => max 0 (1 - |x|)) (t / (1 - Δ)) : ℝ) : ℂ)‖ ≤ (1 - Δ)⁻¹ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h1d),
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tri_nonneg _)]
        calc (1 - Δ)⁻¹ * (fun x : ℝ => max 0 (1 - |x|)) (t / (1 - Δ)) ≤ (1 - Δ)⁻¹ * 1 :=
              mul_le_mul_of_nonneg_left (tri_le_one _) (le_of_lt (inv_pos.mpr h1d))
          _ = (1 - Δ)⁻¹ := by ring
      calc (Δ⁻¹ * (1 - Δ) ^ 2) * ‖(1 - Δ)⁻¹ * (((fun x : ℝ => max 0 (1 - |x|)) (t / (1 - Δ)) : ℝ) : ℂ)‖
          ≤ (Δ⁻¹ * (1 - Δ) ^ 2) * (1 - Δ)⁻¹ := by
            refine mul_le_mul_of_nonneg_left htri (by positivity)
        _ = Δ⁻¹ * (1 - Δ) := by
            field_simp
    calc ‖(Δ⁻¹ : ℂ) * (((fun x : ℝ => max 0 (1 - |x|)) t : ℝ) : ℂ) -
          (((Δ⁻¹ * (1 - Δ) ^ 2) : ℝ) : ℂ) * ((1 - Δ)⁻¹ * (((fun x : ℝ => max 0 (1 - |x|)) (t / (1 - Δ)) : ℝ) : ℂ))‖
        ≤ Δ⁻¹ + Δ⁻¹ * (1 - Δ) := (norm_sub_le _ _).trans (add_le_add h1 h2)
      _ = Δ⁻¹ * (2 - Δ) := by ring
      _ ≤ 2 / Δ := by
          rw [show (2:ℝ) / Δ = Δ⁻¹ * 2 by field_simp]
          refine mul_le_mul_of_nonneg_left (by linarith) (le_of_lt (inv_pos.mpr hΔ0))
  · have hΔ1' : Δ = 1 := le_antisymm hΔ1 hge
    subst hΔ1'
    have he : (fun α : ℝ => (Kfun 1 α : ℂ) * eC (α * t))
        = (fun α : ℝ => ((Real.sinc (Real.pi * α)) ^ 2 : ℂ) * eC (α * t)) := by
      funext α; simp [Kfun]
    rw [he, sinc_sq_eC_integral, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tri_nonneg t)]
    linarith [tri_le_one t]



open LeanLab.ExceptionalSet.U1539 (Kfun eC Sp majorArcs calE)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F Solvable)
open LeanLab.ExceptionalSet.DecompJ200 (majorInt minorInt window blockCount Eγ_minor_block Eγ_major_block)

attribute [local instance] Classical.propDecidable

/-- A finite set of naturals inside an open interval of length `2` has at most `3` elements. -/
lemma card_le_three_of_interval {a : ℝ} {T : Finset ℕ}
    (h : ∀ q ∈ T, a < (q : ℝ) ∧ (q : ℝ) < a + 2) : T.card ≤ 3 := by
  have hceil : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
  have hsub : T ⊆ Finset.Icc ⌈a⌉₊ (⌈a⌉₊ + 2) := by
    intro q hq
    obtain ⟨h1, h2⟩ := h q hq
    refine Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr h1.le, ?_⟩
    have h3 : (q : ℝ) < (⌈a⌉₊ : ℝ) + 3 := by linarith
    have h4 : q < ⌈a⌉₊ + 3 := by exact_mod_cast h3
    omega
  calc T.card ≤ (Finset.Icc ⌈a⌉₊ (⌈a⌉₊ + 2)).card := Finset.card_le_card hsub
    _ = ⌈a⌉₊ + 2 + 1 - ⌈a⌉₊ := by rw [Nat.card_Icc]
    _ ≤ 3 := by omega



open LeanLab.ExceptionalSet.U1539 (Kfun eC Sp majorArcs calE)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F Solvable)
open LeanLab.ExceptionalSet.DecompJ200 (majorInt minorInt window blockCount Eγ_minor_block Eγ_major_block)

attribute [local instance] Classical.propDecidable

/-- For a non-solvable `n`, at most six prime pairs `(p, q)` of the relevant block have
`|p + q - F(n)| < 1`: one of the two primes must be `2`, and the other then lies in an interval
of length `2`. -/
lemma card_contributing_pairs_le {γ : ℝ} (N n : ℕ) (hns : ¬ Solvable γ n)
    (S : Finset ℕ) (hSprime : ∀ p ∈ S, p.Prime) :
    ((S.product S).filter (fun pq : ℕ × ℕ =>
      |((pq.1 : ℝ) + pq.2 - F γ n)| < 1)).card ≤ 6 := by
  set T := (S.product S).filter (fun pq : ℕ × ℕ =>
    |((pq.1 : ℝ) + pq.2 - F γ n)| < 1) with hT
  set S2 := S.filter (fun q : ℕ => q = 2) with hS2
  set B1 := S.filter (fun q : ℕ => |((2 : ℝ) + (q : ℝ) - F γ n)| < 1) with hB1
  set B2 := S.filter (fun p : ℕ => |((p : ℝ) + 2 - F γ n)| < 1) with hB2
  have hS2card : S2.card ≤ 1 := by
    have hsub : S2 ⊆ {2} := by
      intro q hq
      obtain ⟨hqS, hq2⟩ := Finset.mem_filter.mp hq
      simp [hq2]
    calc S2.card ≤ ({2} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 1 := by simp
  have hB1card : B1.card ≤ 3 := by
    refine card_le_three_of_interval (a := F γ n - 3) ?_
    intro q hq
    have hq1 : |((2 : ℝ) + (q : ℝ) - F γ n)| < 1 := (Finset.mem_filter.mp hq).2
    rw [abs_lt] at hq1
    constructor <;> linarith [hq1.1, hq1.2]
  have hB2card : B2.card ≤ 3 := by
    refine card_le_three_of_interval (a := F γ n - 3) ?_
    intro p hp
    have hp1 : |((p : ℝ) + 2 - F γ n)| < 1 := (Finset.mem_filter.mp hp).2
    rw [abs_lt] at hp1
    constructor <;> linarith [hp1.1, hp1.2]
  have hsub : T ⊆ S2 ×ˢ B1 ∪ B2 ×ˢ S2 := by
    intro pq hpq
    obtain ⟨hpqS, hpqc⟩ := Finset.mem_filter.mp hpq
    obtain ⟨hpS, hqS⟩ := Finset.mem_product.mp hpqS
    have hp : pq.1.Prime := hSprime pq.1 hpS
    have hq : pq.2.Prime := hSprime pq.2 hqS
    have htwo : pq.1 = 2 ∨ pq.2 = 2 := by
      by_contra hcon
      simp only [not_or] at hcon
      obtain ⟨hp2, hq2⟩ := hcon
      have hpo : Odd pq.1 := Nat.odd_iff.mpr ((hp.eq_two_or_odd).resolve_left hp2)
      have hqo : Odd pq.2 := Nat.odd_iff.mpr ((hq.eq_two_or_odd).resolve_left hq2)
      have hcast : |(((pq.1 + pq.2 : ℕ)) : ℝ) - F γ n| < 1 := by push_cast; exact hpqc
      exact hns ⟨pq.1, pq.2, hp, hq, hpo, hqo, hcast⟩
    rcases htwo with h2 | h2
    · refine Finset.mem_union_left _ (Finset.mem_product.mpr ⟨?_, ?_⟩)
      · exact Finset.mem_filter.mpr ⟨hpS, h2⟩
      · refine Finset.mem_filter.mpr ⟨hqS, ?_⟩
        rw [h2] at hpqc
        simpa using hpqc
    · refine Finset.mem_union_right _ (Finset.mem_product.mpr ⟨?_, ?_⟩)
      · refine Finset.mem_filter.mpr ⟨hpS, ?_⟩
        rw [h2] at hpqc
        simpa using hpqc
      · exact Finset.mem_filter.mpr ⟨hqS, h2⟩
  have h1 : (S2 ×ˢ B1).card ≤ 1 * 3 := by
    rw [Finset.card_product]
    exact Nat.mul_le_mul hS2card hB1card
  have h2 : (B2 ×ˢ S2).card ≤ 3 * 1 := by
    rw [Finset.card_product]
    exact Nat.mul_le_mul hB2card hS2card
  have hsub' : T ⊆ S2 ×ˢ B1 ∪ B2 ×ˢ S2 := hsub
  calc T.card ≤ (S2 ×ˢ B1 ∪ B2 ×ˢ S2).card := Finset.card_le_card hsub'
    _ ≤ (S2 ×ˢ B1).card + (B2 ×ˢ S2).card := Finset.card_union_le _ _
    _ ≤ 1 * 3 + 3 * 1 := by omega
    _ = 6 := by norm_num



open MeasureTheory intervalIntegral
open Filter Topology
open LeanLab.ExceptionalSet.U1539 (calE Kfun eC)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F Solvable)
open LeanLab.ExceptionalSet.DecompJ200 (majorInt minorInt window blockCount Eγ_minor_block Eγ_major_block)

attribute [local instance] Classical.propDecidable

lemma calE_eq' (γ κ : ℝ) (N : ℕ) :
    calE γ κ N = Real.exp (κ * Real.log (N:ℝ) ^ (3 - 2 * γ)) := rfl

lemma F_eq' (γ : ℝ) (N : ℕ) : F γ N = Real.exp (Real.log (N:ℝ) ^ γ) := rfl

lemma calE_rpow'' {γ κ : ℝ} {N : ℕ} (a : ℝ) :
    calE γ κ N ^ a = Real.exp (a * (κ * Real.log (N:ℝ) ^ (3 - 2 * γ))) := by
  rw [calE_eq', Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

/-- `12 (u+1)^2 ≤ exp (u/4)` for `u ≥ 4096`. -/
lemma poly_le_exp {u : ℝ} (hu : (4096:ℝ) ≤ u) :
    12 * (u + 1) ^ 2 ≤ Real.exp (u / 4) := by
  have h0 : (0:ℝ) < u := by linarith
  have hpos : (0:ℝ) < 12 * (u + 1) ^ 2 := by positivity
  rw [← Real.log_le_log_iff hpos (Real.exp_pos _), Real.log_exp,
    Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have hlog : Real.log (u + 1) ≤ 2 * Real.sqrt (u + 1) := by
    have h := Real.log_le_rpow_div (x := u + 1) (ε := (1/2 : ℝ)) (by linarith) (by norm_num)
    have h2 : Real.sqrt (u + 1) = (u + 1) ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow _
    rw [h2]
    calc Real.log (u + 1) ≤ (u + 1) ^ (1/2 : ℝ) / (1/2) := h
      _ = 2 * (u + 1) ^ (1/2 : ℝ) := by ring
  have hm : 32 * Real.sqrt (u + 1) ≤ u := by
    have h1 : (32:ℝ) ^ 2 * (u + 1) ≤ u ^ 2 := by nlinarith [hu, h0]
    have h2 : (32 * Real.sqrt (u + 1)) ^ 2 = 32 ^ 2 * (u + 1) := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]
    have h3 : (32 * Real.sqrt (u + 1)) ^ 2 ≤ u ^ 2 := by rw [h2]; exact h1
    have h4 := sq_le_sq.mp h3
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by linarith)] at h4
    exact h4
  have hlog12 : Real.log 12 ≤ 11 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 12 by norm_num)
    linarith
  push_cast
  nlinarith [hlog, hm, hlog12, hu]

/-- The core inequality of the threshold, in the variables `u = (log N)^γ`, `v = (log N)^{3-2γ}`. -/
lemma threshold_core {u v κ c₀ : ℝ} (hκ : 0 < κ) (hc₀ : 0 < c₀)
    (hu : (4096:ℝ) ≤ u) (h1 : κ * v ≤ u / 40)
    (h2 : Real.exp (-(u / 4)) < c₀ / 2)
    (h3 : Real.exp (-(7 / 30) * (κ * v)) < c₀ / 2) :
    12 * (u + 1) ^ 2 * Real.exp ((1 / 8) * (κ * v)) + Real.exp u * Real.exp (-(1 / 3) * (κ * v))
      < c₀ * (Real.exp u * Real.exp (-(1 / 10) * (κ * v))) := by
  set E := Real.exp u * Real.exp (-(1 / 10) * (κ * v)) with hE
  have hEpos : 0 < E := by rw [hE]; positivity
  -- the first term is at most `exp (-u/4) * E`
  have hT1 : 12 * (u + 1) ^ 2 * Real.exp ((1 / 8) * (κ * v)) ≤ Real.exp (-(u / 4)) * E := by
    have hp : 12 * (u + 1) ^ 2 ≤ Real.exp (u / 4) := poly_le_exp hu
    have hstep : 12 * (u + 1) ^ 2 * Real.exp ((1 / 8) * (κ * v))
        ≤ Real.exp (u / 4 + (1 / 8) * (κ * v)) := by
      calc 12 * (u + 1) ^ 2 * Real.exp ((1 / 8) * (κ * v))
          ≤ Real.exp (u / 4) * Real.exp ((1 / 8) * (κ * v)) :=
            mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
        _ = Real.exp (u / 4 + (1 / 8) * (κ * v)) := (Real.exp_add _ _).symm
    refine hstep.trans ?_
    have harg : u / 4 + (1 / 8) * (κ * v) ≤ -(u / 4) + (u + -(1 / 10) * (κ * v)) := by
      nlinarith [h1, hκ]
    calc Real.exp (u / 4 + (1 / 8) * (κ * v))
        ≤ Real.exp (-(u / 4) + (u + -(1 / 10) * (κ * v))) := Real.exp_le_exp.mpr harg
      _ = Real.exp (-(u / 4)) * E := by
          simp only [hE, Real.exp_add]
  -- the second term is at most `exp (-(7/30) κv) * E`
  have hT2 : Real.exp u * Real.exp (-(1 / 3) * (κ * v))
      ≤ Real.exp (-(7 / 30) * (κ * v)) * E := by
    have harg : u + -(1 / 3) * (κ * v) = -(7 / 30) * (κ * v) + (u + -(1 / 10) * (κ * v)) := by
      ring
    calc Real.exp u * Real.exp (-(1 / 3) * (κ * v))
        = Real.exp (u + -(1 / 3) * (κ * v)) := (Real.exp_add _ _).symm
      _ = Real.exp (-(7 / 30) * (κ * v) + (u + -(1 / 10) * (κ * v))) := by rw [harg]
      _ ≤ Real.exp (-(7 / 30) * (κ * v)) * E := le_of_eq (by simp only [hE, Real.exp_add])
  have hsum : 12 * (u + 1) ^ 2 * Real.exp ((1 / 8) * (κ * v))
      + Real.exp u * Real.exp (-(1 / 3) * (κ * v))
      ≤ (Real.exp (-(u / 4)) + Real.exp (-(7 / 30) * (κ * v))) * E := by
    have h := add_le_add hT1 hT2
    calc 12 * (u + 1) ^ 2 * Real.exp ((1 / 8) * (κ * v))
        + Real.exp u * Real.exp (-(1 / 3) * (κ * v))
        ≤ Real.exp (-(u / 4)) * E + Real.exp (-(7 / 30) * (κ * v)) * E := h
      _ = (Real.exp (-(u / 4)) + Real.exp (-(7 / 30) * (κ * v))) * E := by ring
  have hlt : Real.exp (-(u / 4)) + Real.exp (-(7 / 30) * (κ * v)) < c₀ := by linarith
  calc 12 * (u + 1) ^ 2 * Real.exp ((1 / 8) * (κ * v))
      + Real.exp u * Real.exp (-(1 / 3) * (κ * v))
      ≤ (Real.exp (-(u / 4)) + Real.exp (-(7 / 30) * (κ * v))) * E := hsum
    _ < c₀ * E := mul_lt_mul_of_pos_right hlt hEpos
    _ = c₀ * (Real.exp u * Real.exp (-(1 / 10) * (κ * v))) := by rw [hE]


/-- **The eventual threshold of `leaf_dyadic_split`.**  For `1 < γ < 3/2`, `κ > 0`, `c₀ > 0` and all
large `N`: the major-arc saving `X ℰ^(-1/10)` beats both the `(log X)²/Δ` pair term and the minor
arc term `X ℰ^(-1/3)`. -/
theorem exists_threshold {γ κ c₀ : ℝ} (h1 : 1 < γ) (h2 : γ < 3 / 2) (hκ : 0 < κ) (hc₀ : 0 < c₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      calE γ κ N ^ (-(1 / 8 : ℝ)) ≤ 1 ∧
      12 * (Real.log (F γ N) + 1) ^ 2 / calE γ κ N ^ (-(1 / 8 : ℝ))
        + F γ N * calE γ κ N ^ (-(1 / 3 : ℝ))
        < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) := by
  have hp : 0 < 3 - 2 * γ := by linarith
  have h3g : 0 < 3 * γ - 3 := by linarith
  have hL : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLu : Tendsto (fun N : ℕ => Real.log (N:ℝ) ^ γ) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : (0:ℝ) < γ)).comp hL
  have hLp : Tendsto (fun N : ℕ => Real.log (N:ℝ) ^ (3 - 2*γ)) atTop atTop :=
    (tendsto_rpow_atTop hp).comp hL
  have hLd : Tendsto (fun N : ℕ => Real.log (N:ℝ) ^ (3*γ - 3)) atTop atTop :=
    (tendsto_rpow_atTop h3g).comp hL
  obtain ⟨N₁, hN₁⟩ := (hLp.eventually_ge_atTop
    (max 1 ((30 / (7 * κ)) * (-Real.log (c₀ / 2)) + 1 / κ))).exists_forall_of_atTop
  obtain ⟨N₂, hN₂⟩ := (hLu.eventually_ge_atTop
    (max 4096 (4 * (-Real.log (c₀ / 2)) + 1))).exists_forall_of_atTop
  obtain ⟨N₃, hN₃⟩ := (hLd.eventually_ge_atTop (40 * κ)).exists_forall_of_atTop
  obtain ⟨N₄, hN₄⟩ := (hL.eventually_ge_atTop 1).exists_forall_of_atTop
  refine ⟨max (max N₁ N₂) (max N₃ N₄), fun N hN => ?_⟩
  have e1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have e2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have e3 : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have e4 : N₄ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  set L := Real.log (N:ℝ) with hLdef
  have hL1 : (1:ℝ) ≤ L := hN₄ N e4
  have hL0 : (0:ℝ) ≤ L := by linarith
  set v := L ^ (3 - 2*γ) with hvdef
  set u := L ^ γ with hudef
  have hv0 : (0:ℝ) ≤ v := Real.rpow_nonneg hL0 _
  have hu0 : (0:ℝ) ≤ u := Real.rpow_nonneg hL0 _
  have hu4096 : (4096:ℝ) ≤ u := le_trans (le_max_left _ _) (hN₂ N e2)
  have hκv : κ * v ≤ u / 40 := by
    have hd : 40 * κ ≤ L ^ (3*γ - 3) := hN₃ N e3
    have hmul : 40 * κ * v ≤ L ^ (3*γ - 3) * v := mul_le_mul_of_nonneg_right hd hv0
    have hsum : L ^ (3*γ - 3) * v = u := by
      rw [hvdef, hudef, ← Real.rpow_add (by linarith : (0:ℝ) < L)]
      congr 1
      ring
    rw [hsum] at hmul
    nlinarith [hmul, hκ]
  have hvbig : (30 / (7 * κ)) * (-Real.log (c₀ / 2)) + 1 / κ ≤ v :=
    le_trans (le_max_right _ _) (hN₁ N e1)
  have hcpos : (0:ℝ) < c₀ / 2 := by linarith
  have hexp1 : Real.exp (-(u / 4)) < c₀ / 2 := by
    have hu' : 4 * (-Real.log (c₀ / 2)) + 1 ≤ u := le_trans (le_max_right _ _) (hN₂ N e2)
    rw [← Real.exp_log hcpos]
    refine Real.exp_lt_exp.mpr ?_
    nlinarith
  have hexp2 : Real.exp (-(7 / 30) * (κ * v)) < c₀ / 2 := by
    have h1' : -Real.log (c₀ / 2) < (7 / 30) * (κ * v) := by
      have h2' : κ * ((30 / (7 * κ)) * (-Real.log (c₀ / 2)) + 1 / κ) ≤ κ * v :=
        mul_le_mul_of_nonneg_left hvbig hκ.le
      have hsimp : κ * ((30 / (7 * κ)) * (-Real.log (c₀ / 2)) + 1 / κ)
          = (30 / 7) * (-Real.log (c₀ / 2)) + 1 := by
        field_simp
      rw [hsimp] at h2'
      nlinarith [h2']
    rw [← Real.exp_log hcpos]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hFval : F γ N = Real.exp u := by rw [F_eq', ← hLdef, ← hudef]
  have hlogX : Real.log (F γ N) = u := by rw [hFval, Real.log_exp]
  have hΔ : calE γ κ N ^ (-(1 / 8 : ℝ)) = Real.exp (-(1 / 8) * (κ * v)) := by
    rw [calE_rpow'', ← hLdef, ← hvdef]
  have hC : calE γ κ N ^ (-(1 / 3 : ℝ)) = Real.exp (-(1 / 3) * (κ * v)) := by
    rw [calE_rpow'', ← hLdef, ← hvdef]
  have hD : calE γ κ N ^ (-(1 / 10 : ℝ)) = Real.exp (-(1 / 10) * (κ * v)) := by
    rw [calE_rpow'', ← hLdef, ← hvdef]
  have hΔle : calE γ κ N ^ (-(1 / 8 : ℝ)) ≤ 1 := by
    rw [hΔ, Real.exp_le_one_iff]
    have : (0:ℝ) ≤ κ * v := mul_nonneg hκ.le hv0
    nlinarith
  have hinvΔ : (calE γ κ N ^ (-(1 / 8 : ℝ)))⁻¹ = Real.exp ((1 / 8) * (κ * v)) := by
    rw [hΔ, ← Real.exp_neg]
    congr 1
    ring
  refine ⟨hΔle, ?_⟩
  have hmain := threshold_core (u := u) (v := v) (κ := κ) (c₀ := c₀) hκ hc₀ hu4096 hκv hexp1 hexp2
  calc 12 * (Real.log (F γ N) + 1) ^ 2 / calE γ κ N ^ (-(1 / 8 : ℝ))
        + F γ N * calE γ κ N ^ (-(1 / 3 : ℝ))
      = 12 * (u + 1) ^ 2 * Real.exp ((1 / 8) * (κ * v))
        + Real.exp u * Real.exp (-(1 / 3) * (κ * v)) := by
        rw [hlogX, hFval, hC, div_eq_mul_inv, hinvΔ]
    _ < c₀ * (Real.exp u * Real.exp (-(1 / 10) * (κ * v))) := hmain
    _ = c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) := by rw [hFval, hD]; ring


/-- The kernel's Fourier support, allowing `Δ = 1`. -/
lemma Kfun_fourier_zero_of_le {Δ t : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1) (ht : 1 ≤ |t|) :
    ∫ α : ℝ, (Kfun Δ α : ℂ) * eC (α * t) = 0 := by
  rcases lt_or_eq_of_le hΔ1 with h | h
  · exact Kfun_fourier_zero hΔ0 h ht
  · subst h
    rw [show (fun α : ℝ => (Kfun 1 α : ℂ) * eC (α * t))
        = (fun α : ℝ => ((Real.sinc (Real.pi * α)) ^ 2 : ℂ) * eC (α * t)) from by
      funext α; simp [Kfun]]
    rw [sinc_sq_eC_integral, tri_eq_zero_of_one_le_abs ht, Complex.ofReal_zero]

/-- The arc term of display (6) is at most `12 (log X + 1)² / Δ` on a non-solvable `n`. -/
theorem arc_integral_norm_le {γ δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (N n : ℕ)
    (hns : ¬ Solvable γ n) (hΔle : calE γ κ N ^ (-(1 / 8 : ℝ)) ≤ 1) :
    ‖majorInt γ δ κ N n + minorInt γ δ κ N n‖
      ≤ 12 * (Real.log (F γ N) + 1) ^ 2 / calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  set Δ := calE γ κ N ^ (-(1 / 8 : ℝ)) with hΔdef
  have hΔ0 : 0 < Δ := by rw [hΔdef]; exact Real.rpow_pos_of_pos (Real.exp_pos _) _
  rw [majorInt_add_minorInt hδ hκ N n, arc_integral_eq_pairSum hδ hκ N n]
  set S := (Finset.Ioc ⌊F γ N ^ (6 * δ)⌋₊ ⌊F γ N⌋₊).filter Nat.Prime with hS
  set c := (Real.log (F γ N) + 1) ^ 2 * (2 / Δ) with hc
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hX1 : (1:ℝ) ≤ F γ N := Real.one_le_exp (Real.rpow_nonneg
    (by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · subst h0; simp
      · exact Real.log_nonneg (by exact_mod_cast h0)) _)
  have hlogX : (0:ℝ) ≤ Real.log (F γ N) + 1 := by
    linarith [Real.log_nonneg hX1]
  have hlogp : ∀ p ∈ S, Real.log p ≤ Real.log (F γ N) + 1 := by
    intro p hp
    have hpI : p ∈ Finset.Ioc ⌊F γ N ^ (6 * δ)⌋₊ ⌊F γ N⌋₊ := (Finset.mem_filter.mp hp).1
    have hple : (p : ℝ) ≤ F γ N := by
      have h1' : p ≤ ⌊F γ N⌋₊ := (Finset.mem_Ioc.mp hpI).2
      have h2' : (⌊F γ N⌋₊ : ℝ) ≤ F γ N := Nat.floor_le (le_of_lt (Real.exp_pos _))
      have h3' : (p : ℝ) ≤ (⌊F γ N⌋₊ : ℝ) := by exact_mod_cast h1'
      linarith
    have hp0 : (0:ℝ) < p := by
      exact_mod_cast (Finset.mem_filter.mp hp).2.pos
    linarith [Real.log_le_log hp0 hple]
  have hlogp0 : ∀ p ∈ S, (0:ℝ) ≤ Real.log p := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
  have hterm : ∀ p ∈ S, ∀ q ∈ S,
      ‖((Real.log p * Real.log q : ℝ) : ℂ) *
        (∫ α : ℝ, (Kfun Δ α : ℂ) * eC (α * ((p : ℝ) + q - F γ n)))‖
      ≤ (if |((p : ℝ) + q - F γ n)| < 1 then c else 0) := by
    intro p hp q hq
    by_cases hcond : |((p : ℝ) + q - F γ n)| < 1
    · rw [if_pos hcond, hc, norm_mul, Complex.norm_real]
      have hK : ‖∫ α : ℝ, (Kfun Δ α : ℂ) * eC (α * ((p : ℝ) + q - F γ n))‖ ≤ 2 / Δ :=
        Kfun_fourier_norm_le hΔ0 hΔle
      have hlog2 : |Real.log p * Real.log q| ≤ (Real.log (F γ N) + 1) ^ 2 := by
        rw [abs_of_nonneg (mul_nonneg (hlogp0 p hp) (hlogp0 q hq))]
        have hp1 := hlogp p hp
        have hq1 := hlogp q hq
        have hq0 := hlogp0 q hq
        have hp0 := hlogp0 p hp
        nlinarith
      refine mul_le_mul hlog2 hK (norm_nonneg _) ?_
      positivity
    · rw [if_neg hcond]
      have hzero : ∫ α : ℝ, (Kfun Δ α : ℂ) * eC (α * ((p : ℝ) + q - F γ n)) = 0 :=
        Kfun_fourier_zero_of_le hΔ0 hΔle (by linarith)
      rw [hzero]; simp
  have hstep1 : ‖∑ p ∈ S, ∑ q ∈ S, ((Real.log p * Real.log q : ℝ) : ℂ) *
        (∫ α : ℝ, (Kfun Δ α : ℂ) * eC (α * ((p : ℝ) + q - F γ n)))‖
      ≤ ∑ p ∈ S, ∑ q ∈ S, (if |((p : ℝ) + q - F γ n)| < 1 then c else 0) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p hp => ?_))
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun q hq => hterm p hp q hq))
  have hprod : ∑ p ∈ S, ∑ q ∈ S, (if |((p : ℝ) + q - F γ n)| < 1 then c else 0)
      = ∑ pq ∈ S ×ˢ S, (if |((pq.1 : ℝ) + pq.2 - F γ n)| < 1 then c else 0) := by
    rw [Finset.sum_product]
  have hsum_eq : ∑ p ∈ S, ∑ q ∈ S, (if |((p : ℝ) + q - F γ n)| < 1 then c else 0)
      = ((S ×ˢ S).filter (fun pq : ℕ × ℕ => |((pq.1 : ℝ) + pq.2 - F γ n)| < 1)).card * c := by
    rw [hprod, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard := card_contributing_pairs_le N n hns S hSprime
  calc ‖∑ p ∈ S, ∑ q ∈ S, ((Real.log p * Real.log q : ℝ) : ℂ) *
        (∫ α : ℝ, (Kfun Δ α : ℂ) * eC (α * ((p : ℝ) + q - F γ n)))‖
      ≤ ∑ p ∈ S, ∑ q ∈ S, (if |((p : ℝ) + q - F γ n)| < 1 then c else 0) := hstep1
    _ = ((S ×ˢ S).filter (fun pq : ℕ × ℕ => |((pq.1 : ℝ) + pq.2 - F γ n)| < 1)).card * c := hsum_eq
    _ ≤ 6 * c := by
        refine mul_le_mul_of_nonneg_right ?_ ?_
        · exact_mod_cast hcard
        · rw [hc]; positivity
    _ = 12 * (Real.log (F γ N) + 1) ^ 2 / Δ := by
        rw [hc]; field_simp; ring


/-- The cardinal step: if every bad member of the window has one of two properties, the count is at
most the sum of the two counts. -/
theorem split_count (γ : ℝ) (Bad A B' : ℕ → Prop) (N : ℕ)
    (h : ∀ n ∈ window γ N, Bad n → A n ∨ B' n) :
    ((window γ N).filter Bad).card ≤
      ((window γ N).filter A).card + ((window γ N).filter B').card := by
  have hsub : (window γ N).filter Bad ⊆
      (window γ N).filter A ∪ (window γ N).filter B' := by
    intro n hn
    obtain ⟨hwin, hbad⟩ := Finset.mem_filter.mp hn
    rcases h n hwin hbad with ha | hb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwin, ha⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hwin, hb⟩)
  calc ((window γ N).filter Bad).card
      ≤ ((window γ N).filter A ∪ (window γ N).filter B').card := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _

/-- **`leaf_dyadic_split`, assembled.**  Every non-solvable `n` of the window of `N` is bad for the
minor arcs or for the major arcs, so the window count is at most the sum of the two block counts. -/
theorem leaf_dyadic_split_proof {γ δ κ c₀ : ℝ} (h1 : 1 < γ) (h2 : γ < 3 / 2) (hδ : 0 < δ)
    (hκ : 0 < κ) (hc₀ : 0 < c₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      blockCount γ (fun n => ¬ Solvable γ n) N
        ≤ Eγ_minor_block γ δ κ N + Eγ_major_block γ δ κ c₀ N := by
  obtain ⟨N₀, hN₀⟩ := exists_threshold (γ := γ) (κ := κ) (c₀ := c₀) h1 h2 hκ hc₀
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hΔle, hthr⟩ := hN₀ N hN
  have hbad : ∀ n ∈ window γ N, (¬ Solvable γ n) →
      (F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) < ‖minorInt γ δ κ N n‖) ∨
      ((majorInt γ δ κ N n).re < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))) := by
    intro n _ hns
    by_cases hmin : F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) < ‖minorInt γ δ κ N n‖
    · exact Or.inl hmin
    · refine Or.inr ?_
      have hle : ‖minorInt γ δ κ N n‖ ≤ F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) := not_lt.mp hmin
      have hr := arc_integral_norm_le hδ hκ N n hns hΔle
      have hre : (majorInt γ δ κ N n).re
          = (majorInt γ δ κ N n + minorInt γ δ κ N n).re - (minorInt γ δ κ N n).re := by
        simp [Complex.add_re]
      have h1' : (majorInt γ δ κ N n + minorInt γ δ κ N n).re
          ≤ ‖majorInt γ δ κ N n + minorInt γ δ κ N n‖ := Complex.re_le_norm _
      have h2' : -(minorInt γ δ κ N n).re ≤ ‖minorInt γ δ κ N n‖ := by
        have habs := Complex.abs_re_le_norm (minorInt γ δ κ N n)
        have hneg := neg_abs_le (minorInt γ δ κ N n).re
        linarith
      have hb : (majorInt γ δ κ N n).re
          ≤ 12 * (Real.log (F γ N) + 1) ^ 2 / calE γ κ N ^ (-(1 / 8 : ℝ))
            + F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
        rw [hre]
        linarith
      exact lt_of_le_of_lt hb hthr
  have hc := split_count γ (fun n => ¬ Solvable γ n)
    (fun n => F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) < ‖minorInt γ δ κ N n‖)
    (fun n => (majorInt γ δ κ N n).re < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))) N hbad
  simpa only [blockCount, Eγ_minor_block, Eγ_major_block] using hc

/-- LEAF page 357, display (6). For large `N` every `n` of the window with no solution is bad for
the major arcs or for the minor arcs: `majorInt + minorInt = r(F(n))`, the sum (5) of
`log p₁ log p₂ w(p₁ + p₂ - F(n))` over `P < p₁, p₂ ≤ X`, and `w` vanishes off `|x| < 1`, so
`r(F(n)) = 0` when `n` has no solution. Then `(majorInt).re ≤ ‖minorInt‖`, and
`ℰ^{-1/3} < c₀ ℰ^{-1/10}` for large `N`. -/
theorem leaf_dyadic_split (γ δ κ c₀ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hδ : 0 < δ) (hκ : 0 < κ)
    (hc₀ : 0 < c₀) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      blockCount γ (fun n => ¬ Solvable γ n) N ≤
        Eγ_minor_block γ δ κ N + Eγ_major_block γ δ κ c₀ N := leaf_dyadic_split_proof h1 h2 hδ hκ hc₀

/-- LEAF page 366, the variance bound of section 5, from Theorem 2 with `c = 1 - 3δ`, Vinogradov's
bound for `S` on `𝔫` and Chebyshev. The paper states the exceptions as `O(N ℰ^{-1/4})`; we ask only
for the weaker `O(N ℰ^{-1/12})`, which is all that the proof of Theorem 1 uses. -/
theorem leaf_minor_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (Eγ_minor_block γ δ κ N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by sorry

/-- LEAF page 365, Lemma 8, with one `κ` shared by the two arcs as in the paper, where `ℰ` is
fixed once for sections 4 to 7. `U1539.Lemma8` is the same bound with a private `κ`, too weak to
combine with `leaf_minor_bound`. -/
theorem leaf_major_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (Eγ_major_block γ δ κ c₀ N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by sorry

/-- ASSEMBLY of the three leaves above, p. 366: `r(F(n)) > 0` for all but `O(N ℰ^{-1/12})` values
of `n` with `X/2 < ν_n ≤ X`. -/
theorem block_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ B : ℝ, 0 < κ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (blockCount γ (fun n => ¬ Solvable γ n) N : ℝ) ≤
        B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨δ₁, hδ₁, hmin⟩ := leaf_minor_bound γ h1 h2
  obtain ⟨δ₂, hδ₂, hmaj⟩ := leaf_major_bound γ h1 h2
  have hδ : 0 < min δ₁ δ₂ / 2 := half_pos (lt_min hδ₁ hδ₂)
  have hδ1 : min δ₁ δ₂ / 2 < δ₁ := by
    have := min_le_left δ₁ δ₂
    have := lt_min hδ₁ hδ₂
    linarith
  have hδ2 : min δ₁ δ₂ / 2 < δ₂ := by
    have := min_le_right δ₁ δ₂
    have := lt_min hδ₁ hδ₂
    linarith
  obtain ⟨κ₁, hκ₁, hmin⟩ := hmin _ hδ hδ1
  obtain ⟨κ₂, hκ₂, hmaj⟩ := hmaj _ hδ hδ2
  have hκ : 0 < min κ₁ κ₂ := lt_min hκ₁ hκ₂
  obtain ⟨B₁, hB₁, N₁, hmin⟩ := hmin _ hκ (min_le_left _ _)
  obtain ⟨c₀, B₂, hc₀, hB₂, N₂, hmaj⟩ := hmaj _ hκ (min_le_right _ _)
  obtain ⟨N₃, hsplit⟩ := leaf_dyadic_split γ (min δ₁ δ₂ / 2) (min κ₁ κ₂) c₀ h1 h2 hδ hκ hc₀
  refine ⟨min κ₁ κ₂, B₁ + B₂, hκ, add_pos hB₁ hB₂, max N₁ (max N₂ N₃), fun N hN => ?_⟩
  have h₁ := hmin N (le_trans (le_max_left _ _) hN)
  have h₂ := hmaj N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
  have h₃ := hsplit N (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
  have h₃' : (blockCount γ (fun n => ¬ Solvable γ n) N : ℝ) ≤
      Eγ_minor_block γ (min δ₁ δ₂ / 2) (min κ₁ κ₂) N +
        Eγ_major_block γ (min δ₁ δ₂ / 2) (min κ₁ κ₂) c₀ N := by exact_mod_cast h₃
  calc _ ≤ _ := h₃'
    _ ≤ _ := add_le_add h₁ h₂
    _ = _ := by ring

/-! ### Batch 1: monotonicity of `F` and the secant bound for `x ↦ x ^ γ` -/

private lemma one_sub_rpow_le_mul_one_sub {γ : ℝ} (h1 : 1 ≤ γ) {r : ℝ} (hr0 : 0 ≤ r) :
    1 - r ^ γ ≤ γ * (1 - r) := by
  have hb := one_add_mul_self_le_rpow_one_add (s := r - 1) (p := γ) (by linarith) h1
  rw [add_sub_cancel] at hb
  linarith

private lemma rpow_sub_le {γ : ℝ} (h1 : 1 ≤ γ) {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) :
    (a + d) ^ γ ≤ a ^ γ + γ * d * (a + d) ^ (γ - 1) := by
  rcases eq_or_lt_of_le hd with rfl | hd'
  · simp
  set v := a + d with hvdef
  have hv : 0 < v := by rw [hvdef]; linarith
  have hrv : a / v * v = a := by field_simp
  have hr0 : 0 ≤ a / v := div_nonneg ha hv.le
  have hB : 1 - (a / v) ^ γ ≤ γ * (d / v) := by
    have h := one_sub_rpow_le_mul_one_sub h1 hr0
    have h1r : 1 - a / v = d / v := by field_simp; ring
    rw [h1r] at h
    exact h
  have hvp : 0 < v ^ γ := Real.rpow_pos_of_pos hv _
  have hmul := mul_le_mul_of_nonneg_left hB hvp.le
  have hkey : v ^ γ * (1 - (a / v) ^ γ) = v ^ γ - a ^ γ := by
    have h : a ^ γ = (a / v) ^ γ * v ^ γ := by rw [← Real.mul_rpow hr0 hv.le, hrv]
    rw [h]; ring
  have hvv : v ^ γ = v ^ (γ - 1) * v := by
    conv_lhs => rw [show γ = (γ - 1) + 1 by ring]
    rw [Real.rpow_add hv, Real.rpow_one]
  have hrhs : v ^ γ * (γ * (d / v)) = γ * d * v ^ (γ - 1) := by
    rw [hvv]; field_simp
  rw [hkey, hrhs] at hmul
  have hfin : a ^ γ + γ * d * (a + d) ^ (γ - 1) = a ^ γ + γ * d * v ^ (γ - 1) := by rw [hvdef]
  rw [hfin]
  linarith

/-! ### Batch 2: `2 ^ (1/8) ≤ 9/8` and the log increment bound -/

private lemma two_rpow_eighth_le : (2 : ℝ) ^ (1 / 8 : ℝ) ≤ 9 / 8 := by
  have h := rpow_one_add_le_one_add_mul_self (s := (1 : ℝ)) (p := (1 / 8 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

private lemma log_le_log_add_div {n N K : ℕ} (hn : 1 ≤ n) (hNn : n ≤ N) (hNK : N ≤ n + K) :
    Real.log N ≤ Real.log n + (K : ℝ) / n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h1 : Real.log N ≤ Real.log ((n : ℝ) + K) := by
    refine Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) ?_
    exact_mod_cast hNK
  have h2 : Real.log ((n : ℝ) + K) = Real.log n + Real.log (1 + (K : ℝ) / n) := by
    have h : (n : ℝ) + K = (n : ℝ) * (1 + (K : ℝ) / n) := by field_simp
    rw [h, Real.log_mul hn0.ne' (by positivity)]
  have h3 : Real.log (1 + (K : ℝ) / n) ≤ (K : ℝ) / n := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + (K : ℝ) / n by positivity)
    linarith
  linarith

/-! ### Batch 3: membership in the window of `N` -/

private lemma mem_window_iff {γ : ℝ} {N n : ℕ} :
    n ∈ window γ N ↔ n ≤ 2 * N ∧ F γ N / 2 < (nu γ n : ℝ) ∧ (nu γ n : ℝ) ≤ F γ N := by
  unfold window
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

private lemma log_eight_ge_one : (1 : ℝ) ≤ Real.log 8 := by
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  have h := Real.log_two_gt_d9
  rw [hlog8]; linarith

private lemma rpow_one_sub_mul {x γ : ℝ} (hx : 0 < x) :
    x ^ (1 - γ) * x ^ (γ - 1) = 1 := by
  rw [← Real.rpow_add hx, show 1 - γ + (γ - 1) = 0 by ring, Real.rpow_zero]

/-- The width `log N - log n` that the window of `N` allows at a given `n`. -/
private noncomputable def dlt (γ : ℝ) (n : ℕ) : ℝ :=
  (Real.log 2 / (8 * γ)) * (Real.log (n : ℝ) + 1) ^ (1 - γ)

private lemma log_nat_add_one_pos (n : ℕ) : (0 : ℝ) < Real.log (n : ℝ) + 1 := by
  have h : (0 : ℝ) ≤ Real.log (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · exact Real.log_nonneg (by exact_mod_cast h0)
  linarith

private lemma dlt_nonneg {γ : ℝ} (hγ : 0 < γ) (n : ℕ) : 0 ≤ dlt γ n := by
  have h : (0 : ℝ) < (Real.log (n : ℝ) + 1) ^ (1 - γ) :=
    Real.rpow_pos_of_pos (log_nat_add_one_pos n) _
  have h2 : (0 : ℝ) < Real.log 2 / (8 * γ) :=
    div_pos (Real.log_pos (by norm_num)) (by linarith)
  exact mul_nonneg h2.le h.le

private lemma dlt_le_one {γ : ℝ} (hγ : 1 < γ) (n : ℕ) : dlt γ n ≤ 1 := by
  have hc : Real.log 2 / (8 * γ) ≤ 1 := by
    have h1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    have h2 : (1 : ℝ) ≤ 8 * γ := by linarith
    rw [div_le_one (by linarith : (0 : ℝ) < 8 * γ)]
    linarith
  have hbase : (1 : ℝ) ≤ Real.log (n : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ Real.log (n : ℝ) := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp
      · exact Real.log_nonneg (by exact_mod_cast h0)
    linarith
  have hpow : (Real.log (n : ℝ) + 1) ^ (1 - γ) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le hbase (by linarith : 1 - γ ≤ 0)
    rwa [Real.rpow_zero] at h
  calc dlt γ n = (Real.log 2 / (8 * γ)) * (Real.log (n : ℝ) + 1) ^ (1 - γ) := rfl
    _ ≤ 1 * 1 := by
      refine mul_le_mul hc hpow (Real.rpow_nonneg (by linarith) _) (by norm_num)
    _ = 1 := by norm_num

private lemma dlt_mul {γ : ℝ} (hγ : 1 < γ) (n : ℕ) :
    γ * dlt γ n * (Real.log (n : ℝ) + 1) ^ (γ - 1) = Real.log 2 / 8 := by
  have hx : (0 : ℝ) < Real.log (n : ℝ) + 1 := log_nat_add_one_pos n
  have hγ0 : (0 : ℝ) < γ := by linarith
  have h := rpow_one_sub_mul hx (γ := γ)
  have hc : γ * (Real.log 2 / (8 * γ)) = Real.log 2 / 8 := by field_simp
  rw [dlt]
  set A := (Real.log (n : ℝ) + 1) ^ (1 - γ) with hA
  set B := (Real.log (n : ℝ) + 1) ^ (γ - 1) with hB
  have hAB : A * B = 1 := h
  calc γ * (Real.log 2 / (8 * γ) * A) * B
      = (γ * (Real.log 2 / (8 * γ))) * (A * B) := by ring
    _ = (Real.log 2 / 8) * 1 := by rw [hc, hAB]
    _ = Real.log 2 / 8 := by ring

private lemma mem_window_of_log_le {γ : ℝ} (h1 : 1 < γ) {n N : ℕ} (hn : 8 ≤ n) (hNn : n ≤ N)
    (hlog : Real.log N ≤ Real.log n + dlt γ n) :
    n ∈ window γ N := by
  rw [mem_window_iff]
  set a := Real.log n with hadef
  have hγ0 : 0 < γ := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNn
    linarith
  have ha0 : 0 ≤ a := Real.log_nonneg hn1
  have ha1 : 1 ≤ a := by
    rw [hadef]
    have h : Real.log 8 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    linarith [log_eight_ge_one]
  have hx : (0 : ℝ) < a + 1 := by linarith
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hla : a ≤ Real.log N := Real.log_le_log hn0 (by exact_mod_cast hNn)
  have hd0 : 0 ≤ dlt γ n := dlt_nonneg hγ0 n
  have hd1 : dlt γ n ≤ 1 := dlt_le_one h1 n
  have hdle : dlt γ n = (Real.log 2 / (8 * γ)) * (a + 1) ^ (1 - γ) := by rw [dlt, hadef]
  have step1 : (Real.log N) ^ γ ≤ (a + dlt γ n) ^ γ := by
    refine Real.rpow_le_rpow hlogN0 ?_ hγ0.le
    rw [hadef]
    exact hlog
  have step2 : (a + dlt γ n) ^ γ ≤ a ^ γ + γ * dlt γ n * (a + 1) ^ (γ - 1) := by
    have hbase := rpow_sub_le h1.le ha0 hd0
    have hmono : (a + dlt γ n) ^ (γ - 1) ≤ (a + 1) ^ (γ - 1) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith : (0 : ℝ) ≤ γ - 1)
    have hgd : 0 ≤ γ * dlt γ n := mul_nonneg hγ0.le hd0
    nlinarith
  have step3 : γ * dlt γ n * (a + 1) ^ (γ - 1) = Real.log 2 / 8 := by
    rw [hdle]
    have := dlt_mul h1 n
    rw [dlt] at this
    linarith [this]
  have hub : (Real.log N) ^ γ ≤ a ^ γ + Real.log 2 / 8 :=
    step1.trans (step2.trans (by linarith [step3]))
  have hFn : F γ n = Real.exp (a ^ γ) := by rw [F, hadef]
  have hFN : F γ N = Real.exp ((Real.log N) ^ γ) := rfl
  have hbig : (2 : ℝ) < Real.exp (a ^ γ) * (7 / 8) := by
    have h1e : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hmono : Real.exp 1 ≤ Real.exp (a ^ γ) := by
      refine Real.exp_le_exp.mpr ?_
      have h : (1 : ℝ) ≤ a ^ γ := Real.one_le_rpow ha1 hγ0.le
      linarith
    nlinarith
  refine ⟨by omega, ?_, ?_⟩
  · -- `F γ N / 2 < ν_n`
    have hle : F γ N ≤ Real.exp (a ^ γ) * (9 / 8) := by
      rw [hFN]
      have hexp : Real.exp ((Real.log N) ^ γ) ≤
          Real.exp (a ^ γ) * Real.exp (Real.log 2 / 8) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (Real.log 2 / 8) = (2 : ℝ) ^ (1 / 8 : ℝ) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring_nf
      rw [h2] at hexp
      have h3 := two_rpow_eighth_le
      nlinarith
    have hfloor : Real.exp (a ^ γ) - 1 < (nu γ n : ℝ) := by
      rw [nu, hFn]
      exact Int.sub_one_lt_floor _
    nlinarith
  · -- `ν_n ≤ F γ N`
    have h1' : (nu γ n : ℝ) ≤ F γ n := by
      rw [nu]; exact Int.floor_le _
    have h2' : F γ n ≤ F γ N := by
      rw [hFn, hFN]
      exact Real.exp_le_exp.mpr (Real.rpow_le_rpow ha0 hla hγ0.le)
    linarith

/-! ### Batch 4: counting the windows that cover a dyadic block -/

/-- The stretch of `N` above `n` over which `n` stays in the window of `N`. -/
private noncomputable def step (γ : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) * dlt γ n⌋₊

private lemma step_le {γ : ℝ} (hγ : 0 < γ) (n : ℕ) :
    (step γ n : ℝ) ≤ (n : ℝ) * dlt γ n :=
  Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (dlt_nonneg hγ n))

private lemma step_lt_succ {γ : ℝ} (n : ℕ) : (n : ℝ) * dlt γ n < (step γ n : ℝ) + 1 :=
  Nat.lt_floor_add_one _

private lemma step_le_self {γ : ℝ} (hγ : 1 < γ) (n : ℕ) : step γ n ≤ n := by
  have h := step_le (by linarith) n
  have h1 : (n : ℝ) * dlt γ n ≤ (n : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left (dlt_le_one hγ n) (Nat.cast_nonneg n)
  have h2 : (step γ n : ℝ) ≤ (n : ℝ) := by simpa using h.trans h1
  exact_mod_cast h2

private lemma mem_window_of_step {γ : ℝ} (h1 : 1 < γ) {n N : ℕ} (hn : 8 ≤ n)
    (hNn : n ≤ N) (hNK : N ≤ n + step γ n) : n ∈ window γ N := by
  refine mem_window_of_log_le h1 hn hNn ?_
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h1' : Real.log N ≤ Real.log n + (step γ n : ℝ) / n :=
    log_le_log_add_div (by omega) hNn hNK
  have h2 : (step γ n : ℝ) / n ≤ dlt γ n := by
    rw [div_le_iff₀ hn0]
    calc (step γ n : ℝ) ≤ (n : ℝ) * dlt γ n := step_le (by linarith) n
      _ = dlt γ n * n := by ring
  linarith

/-- The number of windows that must contain each member of `[M, 2M)`. -/
private noncomputable def mult (γ : ℝ) (M : ℕ) : ℕ :=
  ⌊(Real.log 2 / (16 * γ)) * (M : ℝ) * (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (1 - γ)⌋₊

private lemma mult_le_cast {γ : ℝ} (hγ : 0 < γ) (M : ℕ) :
    (mult γ M : ℝ) ≤
      (Real.log 2 / (16 * γ)) * (M : ℝ) * (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (1 - γ) := by
  refine Nat.floor_le ?_
  have h1 : (0 : ℝ) < Real.log 2 / (16 * γ) :=
    div_pos (Real.log_pos (by norm_num)) (by linarith)
  have h2 : (0 : ℝ) < (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (1 - γ) :=
    Real.rpow_pos_of_pos (log_nat_add_one_pos _) _
  exact mul_nonneg (mul_nonneg h1.le (Nat.cast_nonneg M)) h2.le

private lemma mult_le_step_succ {γ : ℝ} (h1 : 1 < γ) {M n : ℕ} (_hM : 8 ≤ M)
    (hnM : M ≤ n) (hn2M : n < 2 * M) : mult γ M ≤ step γ n + 1 := by
  have hγ0 : 0 < γ := by linarith
  set A := Real.log 2 / (16 * γ) with hA
  set L := Real.log ((2 * M : ℕ) : ℝ) + 1 with hL
  set X := Real.log (n : ℝ) + 1 with hX
  have hA0 : 0 ≤ A := by
    rw [hA]; exact (div_pos (Real.log_pos (by norm_num)) (by linarith)).le
  have hL0 : 0 < L := log_nat_add_one_pos _
  have hX0 : 0 < X := log_nat_add_one_pos _
  have hMn : (M : ℝ) ≤ 2 * (n : ℝ) := by
    have : M ≤ 2 * n := by omega
    exact_mod_cast this
  have hXL : X ≤ L := by
    have h1 : (n : ℝ) ≤ ((2 * M : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ 2 * M)
    have := Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) h1
    rw [hL, hX]; linarith
  have hpow : L ^ (1 - γ) ≤ X ^ (1 - γ) :=
    (Real.rpow_le_rpow_iff_of_neg hL0 hX0 (by linarith : 1 - γ < 0)).mpr hXL
  have hmain : (mult γ M : ℝ) ≤ (n : ℝ) * dlt γ n := by
    have h1 : (mult γ M : ℝ) ≤ A * (M : ℝ) * L ^ (1 - γ) := by
      rw [hA, hL]; exact mult_le_cast hγ0 M
    have h2 : A * (M : ℝ) * L ^ (1 - γ) ≤ A * (2 * (n : ℝ)) * X ^ (1 - γ) := by
      have hstep1 : A * (M : ℝ) * L ^ (1 - γ) ≤ A * (2 * (n : ℝ)) * L ^ (1 - γ) := by
        have := mul_le_mul_of_nonneg_left hMn hA0
        have hLp : (0 : ℝ) ≤ L ^ (1 - γ) := Real.rpow_nonneg hL0.le _
        nlinarith
      have hA2 : 0 ≤ A * (2 * (n : ℝ)) := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
      exact hstep1.trans (mul_le_mul_of_nonneg_left hpow hA2)
    have hd : (n : ℝ) * dlt γ n = 2 * (A * (n : ℝ) * X ^ (1 - γ)) := by
      rw [dlt, hA, hX]; ring
    calc (mult γ M : ℝ) ≤ A * (M : ℝ) * L ^ (1 - γ) := h1
      _ ≤ A * (2 * (n : ℝ)) * X ^ (1 - γ) := h2
      _ = (n : ℝ) * dlt γ n := by rw [hd]; ring
  have hfin : (mult γ M : ℝ) ≤ ((step γ n + 1 : ℕ) : ℝ) := by
    have := step_lt_succ (γ := γ) n
    push_cast
    linarith
  exact_mod_cast hfin

private lemma card_window_ge_mult {γ : ℝ} (h1 : 1 < γ) {M : ℕ} (hM : 8 ≤ M) {n : ℕ}
    (hn : M ≤ n) (hn2 : n < 2 * M) :
    mult γ M ≤ ((Finset.Ico M (4 * M + 1)).filter (fun N => n ∈ window γ N)).card := by
  have hn8 : 8 ≤ n := le_trans hM hn
  have hsub : Finset.Ico n (n + step γ n + 1) ⊆
      (Finset.Ico M (4 * M + 1)).filter (fun N => n ∈ window γ N) := by
    intro N hN
    simp only [Finset.mem_Ico] at hN
    obtain ⟨hN1, hN2⟩ := hN
    have h3 : N ≤ n + step γ n := by omega
    refine Finset.mem_filter.mpr ⟨?_, mem_window_of_step h1 hn8 hN1 h3⟩
    refine Finset.mem_Ico.mpr ⟨le_trans hn hN1, ?_⟩
    have hs : step γ n ≤ n := step_le_self h1 n
    omega
  have hcard : (Finset.Ico n (n + step γ n + 1)).card = step γ n + 1 := by
    rw [Nat.card_Ico]; omega
  calc mult γ M ≤ step γ n + 1 := mult_le_step_succ h1 hM hn hn2
    _ = (Finset.Ico n (n + step γ n + 1)).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Double counting: every bad member of `[M, 2M)` lies in `mlt` windows `N ∈ [M, 4M]`, so the
dyadic count is at most the sum of the window counts divided by `mlt`. -/
private lemma card_mul_le_sum_blocks (γ : ℝ) (Bad : ℕ → Prop) (M mlt : ℕ)
    (hstep : ∀ n ∈ (Finset.Ico M (2 * M)).filter Bad,
      (mlt : ℝ) ≤ ((Finset.Ico M (4 * M + 1)).filter (fun N => n ∈ window γ N)).card) :
    (mlt : ℝ) * (((Finset.Ico M (2 * M)).filter Bad).card : ℝ) ≤
      ∑ N ∈ Finset.Ico M (4 * M + 1), (blockCount γ Bad N : ℝ) := by
  set S := (Finset.Ico M (2 * M)).filter Bad with hS
  set t := Finset.Ico M (4 * M + 1) with ht
  have h1 : (mlt : ℝ) * (S.card : ℝ) = ∑ _n ∈ S, (mlt : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [h1]
  have hstep' : ∀ n ∈ S, (mlt : ℝ) ≤ ((t.filter (fun N => n ∈ window γ N)).card : ℝ) := by
    intro n hn
    rw [hS] at hn
    exact_mod_cast hstep n hn
  calc ∑ _n ∈ S, (mlt : ℝ)
      ≤ ∑ n ∈ S, ((t.filter (fun N => n ∈ window γ N)).card : ℝ) := Finset.sum_le_sum hstep'
    _ = ∑ n ∈ S, ∑ N ∈ t, (if n ∈ window γ N then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.card_filter]
        push_cast
        simp
    _ = ∑ N ∈ t, ∑ n ∈ S, (if n ∈ window γ N then (1 : ℝ) else 0) := Finset.sum_comm
    _ ≤ ∑ N ∈ t, (blockCount γ Bad N : ℝ) := by
        refine Finset.sum_le_sum (fun N _ => ?_)
        have hbc : (blockCount γ Bad N : ℝ) = (((window γ N).filter Bad).card : ℝ) := rfl
        rw [hbc]
        have hsub : S.filter (fun n => n ∈ window γ N) ⊆ (window γ N).filter Bad := by
          intro n hn
          simp only [Finset.mem_filter] at hn ⊢
          rw [hS] at hn
          simp only [Finset.mem_filter] at hn
          exact ⟨hn.2, hn.1.2⟩
        have hcard : ((S.filter (fun n => n ∈ window γ N)).card : ℝ) =
            ∑ n ∈ S, (if n ∈ window γ N then (1 : ℝ) else 0) := by
          rw [Finset.card_filter]
          push_cast
          simp
        rw [← hcard]
        exact_mod_cast Finset.card_le_card hsub

/-! ### Batch 5a: eventual bounds -/

/-- For `p > 0` and `ε > 0`, `log t ≤ ε * t ^ p` from some point on. -/
private lemma exists_log_le_mul_rpow {p : ℝ} (hp : 0 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → Real.log t ≤ ε * t ^ p := by
  set s := p / 2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have hsp : s + s = p := by rw [hs]; ring
  have hes : 0 < ε * s := mul_pos hε hs0
  refine ⟨max 2 ((1 / (ε * s)) ^ (1 / s)), ?_⟩
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have ht0 : 0 < t := by linarith
  have hTt : (1 / (ε * s)) ^ (1 / s) ≤ t := le_trans (le_max_right _ _) ht
  have hbase : (0 : ℝ) < 1 / (ε * s) := by positivity
  have hts : 1 / (ε * s) ≤ t ^ s := by
    have h1 : ((1 / (ε * s)) ^ (1 / s)) ^ s = (1 / (ε * s)) ^ (1 : ℝ) := by
      rw [← Real.rpow_mul hbase.le]
      congr 1
      field_simp
    rw [Real.rpow_one] at h1
    rw [← h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hbase.le _) hTt hs0.le
  have hts0 : (0 : ℝ) ≤ t ^ s := Real.rpow_nonneg ht0.le _
  have hone : (1 : ℝ) ≤ ε * s * t ^ s := by
    have h := mul_le_mul_of_nonneg_left hts hes.le
    have h' : ε * s * (1 / (ε * s)) = 1 := by field_simp
    rwa [h'] at h
  have hsq : t ^ s * t ^ s = t ^ p := by
    rw [← Real.rpow_add ht0, hsp]
  have hstep : t ^ s ≤ ε * s * t ^ p := by
    calc t ^ s = 1 * t ^ s := by ring
      _ ≤ (ε * s * t ^ s) * t ^ s := mul_le_mul_of_nonneg_right hone hts0
      _ = ε * s * (t ^ s * t ^ s) := by ring
      _ = ε * s * t ^ p := by rw [hsq]
  have hlog : Real.log t = (1 / s) * Real.log (t ^ s) := by
    rw [Real.log_rpow ht0]
    field_simp
  have hlog2 : Real.log (t ^ s) ≤ t ^ s := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht0 s)
    linarith
  calc Real.log t = (1 / s) * Real.log (t ^ s) := hlog
    _ ≤ (1 / s) * t ^ s := mul_le_mul_of_nonneg_left hlog2 (by positivity)
    _ ≤ (1 / s) * (ε * s * t ^ p) := mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = ε * t ^ p := by field_simp

/-- `κ / 24 * (log M) ^ p ≤ log M / 2` for large `M`, when `0 < p < 1`. -/
private lemma exists_calE_small {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {κ : ℝ} (hκ : 0 < κ) :
    ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M → κ / 24 * Real.log M ^ p ≤ Real.log M / 2 := by
  set L₀ := (κ / 12) ^ (1 / (1 - p)) with hL₀
  have hL₀0 : 0 < L₀ := Real.rpow_pos_of_pos (by linarith) _
  refine ⟨⌈Real.exp L₀⌉₊ + 1, fun M hM => ?_⟩
  have hMe : Real.exp L₀ ≤ (M : ℝ) := by
    have h3 : (⌈Real.exp L₀⌉₊ : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hM
    have h2 : Real.exp L₀ ≤ (⌈Real.exp L₀⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  have hL : L₀ ≤ Real.log M := by
    have h := Real.log_le_log (Real.exp_pos L₀) hMe
    rwa [Real.log_exp] at h
  have hLpos : 0 < Real.log M := lt_of_lt_of_le hL₀0 hL
  have hpow : L₀ ^ (1 - p) ≤ (Real.log M) ^ (1 - p) :=
    Real.rpow_le_rpow hL₀0.le hL (by linarith : (0 : ℝ) ≤ 1 - p)
  have hL₀pow : L₀ ^ (1 - p) = κ / 12 := by
    rw [hL₀]
    rw [← Real.rpow_mul (show (0 : ℝ) ≤ κ / 12 by linarith)]
    rw [show (1 / (1 - p)) * (1 - p) = 1 by field_simp, Real.rpow_one]
  have hkey : κ / 12 ≤ (Real.log M) ^ (1 - p) := by rw [← hL₀pow]; exact hpow
  have hsplit : (Real.log M) ^ (1 - p) * (Real.log M) ^ p = Real.log M := by
    rw [← Real.rpow_add hLpos, show 1 - p + p = 1 by ring, Real.rpow_one]
  have hLp : 0 ≤ (Real.log M) ^ p := Real.rpow_nonneg hLpos.le _
  have hT := mul_le_mul_of_nonneg_right hkey hLp
  rw [hsplit] at hT
  calc κ / 24 * Real.log M ^ p = (κ / 12) * Real.log M ^ p / 2 := by ring
    _ ≤ (Real.log M) ^ (1 - p) * (Real.log M) ^ p / 2 := by linarith
    _ = Real.log M / 2 := by rw [hsplit]

private lemma log_twenty_one_ge_three : (3 : ℝ) ≤ Real.log 21 := by
  have hexp3 : Real.exp 3 < 21 := by
    have hsplit : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    rw [hsplit]
    have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    nlinarith
  have h := Real.log_lt_log (Real.exp_pos 3) hexp3
  rw [Real.log_exp] at h
  linarith

/-- Absorption: `(log (2M) + 1) ^ (γ - 1) ≤ exp (κ/24 * (log M) ^ (3 - 2γ))` eventually. -/
private lemma eventually_absorb {γ κ : ℝ} (h1 : 1 < γ) (h2 : γ < 3 / 2) (hκ : 0 < κ) :
    ∃ M1 : ℕ, ∀ M : ℕ, M1 ≤ M →
      (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (γ - 1) ≤
        Real.exp (κ / 24 * Real.log M ^ (3 - 2 * γ)) := by
  set p := 3 - 2 * γ with hpdef
  have hp : 0 < p := by rw [hpdef]; linarith
  have hp1 : p < 1 := by rw [hpdef]; linarith
  have hγ1 : 0 < γ - 1 := by linarith
  set ε := κ / (48 * (γ - 1)) with hεdef
  have hε : 0 < ε := div_pos hκ (by linarith)
  obtain ⟨T, hT⟩ := exists_log_le_mul_rpow hp hε
  refine ⟨max 21 (⌈Real.exp T⌉₊ + 1), fun M hM => ?_⟩
  have hM21 : 21 ≤ M := le_trans (le_max_left _ _) hM
  have hMe : Real.exp T ≤ (M : ℝ) := by
    have h3 : (⌈Real.exp T⌉₊ : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast (le_trans (le_max_right _ _) hM)
    have h2 : Real.exp T ≤ (⌈Real.exp T⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  have hL3 : 3 ≤ Real.log M :=
    le_trans log_twenty_one_ge_three
      (Real.log_le_log (by norm_num) (by exact_mod_cast hM21))
  have hLT : T ≤ Real.log M := by
    have h := Real.log_le_log (Real.exp_pos T) hMe
    rwa [Real.log_exp] at h
  have hLpos : 0 < Real.log M := by linarith
  have h2Mpos : (0 : ℝ) < ((2 * M : ℕ) : ℝ) := by
    have : 0 < 2 * M := by omega
    exact_mod_cast this
  have hlog2M : Real.log ((2 * M : ℕ) : ℝ) = Real.log 2 + Real.log M := by
    rw [show ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) by push_cast; ring,
      Real.log_mul (by norm_num) (by positivity)]
  have hX3 : Real.log ((2 * M : ℕ) : ℝ) + 1 ≤ 3 * Real.log M := by
    have hlog2 : Real.log 2 ≤ Real.log M :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ M))
    rw [hlog2M]; linarith
  have h2M1 : (0 : ℝ) ≤ Real.log ((2 * M : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * M))
  have hpow : (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (γ - 1) ≤ (3 * Real.log M) ^ (γ - 1) :=
    Real.rpow_le_rpow (by linarith) hX3 hγ1.le
  have hexp3L : (3 * Real.log M) ^ (γ - 1) =
      Real.exp ((γ - 1) * Real.log (3 * Real.log M)) := by
    rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < 3 * Real.log M)]
    ring_nf
  have hlog3L : Real.log (3 * Real.log M) ≤ 2 * Real.log (Real.log M) := by
    have hmul : Real.log (3 * Real.log M) = Real.log 3 + Real.log (Real.log M) :=
      Real.log_mul (by norm_num) (by positivity)
    have h3L : Real.log 3 ≤ Real.log (Real.log M) := Real.log_le_log (by norm_num) (by linarith)
    rw [hmul]; linarith
  have hlogL : Real.log (Real.log M) ≤ ε * (Real.log M) ^ p := hT _ hLT
  have hε' : 2 * (γ - 1) * ε = κ / 24 := by
    rw [hεdef]; field_simp; ring
  have hLp : 0 ≤ (Real.log M) ^ p := Real.rpow_nonneg hLpos.le _
  have hfinal : (γ - 1) * Real.log (3 * Real.log M) ≤ κ / 24 * (Real.log M) ^ p := by
    have h := mul_le_mul_of_nonneg_left hlog3L hγ1.le
    have h' := mul_le_mul_of_nonneg_left hlogL (by positivity : (0 : ℝ) ≤ 2 * (γ - 1))
    nlinarith [h, h', hε', hLp]
  calc (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (γ - 1) ≤ (3 * Real.log M) ^ (γ - 1) := hpow
    _ = Real.exp ((γ - 1) * Real.log (3 * Real.log M)) := hexp3L
    _ ≤ Real.exp (κ / 24 * (Real.log M) ^ (3 - 2 * γ)) := Real.exp_le_exp.mpr hfinal

private lemma calE_rpow {γ κ : ℝ} {N : ℕ} :
    calE γ κ N ^ (-(1 / 12 : ℝ)) = Real.exp (-(κ / 12) * Real.log N ^ (3 - 2 * γ)) := by
  rw [calE, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

/-- The window counts summed over `[M, 4M]`, using `calE N ^ (-1/12) ≤ calE M ^ (-1/12)`. -/
private lemma sum_blockCount_le {γ κ B : ℝ} (h1 : 1 < γ) (h2 : γ < 3 / 2) (hκ : 0 < κ) (hB : 0 < B)
    {Bad : ℕ → Prop} {N₀ : ℕ}
    (h : ∀ N : ℕ, N₀ ≤ N → (blockCount γ Bad N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ)))
    {M : ℕ} (hMN₀ : N₀ ≤ M) (hM1 : 1 ≤ M) :
    ∑ N ∈ Finset.Ico M (4 * M + 1), (blockCount γ Bad N : ℝ) ≤
      16 * B * (M : ℝ) ^ 2 * Real.exp (-(κ / 12) * Real.log M ^ (3 - 2 * γ)) := by
  set E := Real.exp (-(κ / 12) * Real.log M ^ (3 - 2 * γ)) with hEdef
  have hE : 0 < E := Real.exp_pos _
  have hp : 0 < 3 - 2 * γ := by linarith
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM1)
  have hcard : (Finset.Ico M (4 * M + 1)).card = 3 * M + 1 := by
    rw [Nat.card_Ico]; omega
  have hterm : ∀ N ∈ Finset.Ico M (4 * M + 1),
      (blockCount γ Bad N : ℝ) ≤ B * (4 * (M : ℝ)) * E := by
    intro N hN
    obtain ⟨hNM, hN4⟩ := Finset.mem_Ico.mp hN
    have h1' : (blockCount γ Bad N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) :=
      h N (le_trans hMN₀ hNM)
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
      have : 1 ≤ N := le_trans hM1 hNM
      exact_mod_cast this
    have hNM' : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNM
    have hlogNM : Real.log M ≤ Real.log N := Real.log_le_log hM0 hNM'
    have hpowN : (Real.log M) ^ (3 - 2 * γ) ≤ (Real.log N) ^ (3 - 2 * γ) :=
      Real.rpow_le_rpow hlogM0 hlogNM hp.le
    have hexpN : Real.exp (-(κ / 12) * Real.log N ^ (3 - 2 * γ)) ≤ E := by
      rw [hEdef]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hpowN, hκ]
    have hcalN : calE γ κ N ^ (-(1 / 12 : ℝ)) = Real.exp (-(κ / 12) * Real.log N ^ (3 - 2 * γ)) :=
      calE_rpow
    rw [hcalN] at h1'
    have h4 : (N : ℝ) ≤ 4 * (M : ℝ) := by exact_mod_cast (by omega : N ≤ 4 * M)
    have hBN : (0 : ℝ) ≤ B * N := by positivity
    have hstep1 : B * (N : ℝ) * Real.exp (-(κ / 12) * Real.log N ^ (3 - 2 * γ)) ≤ B * (N : ℝ) * E :=
      mul_le_mul_of_nonneg_left hexpN hBN
    have hstep2 : B * (N : ℝ) * E ≤ B * (4 * (M : ℝ)) * E := by
      have : B * (N : ℝ) ≤ B * (4 * (M : ℝ)) := mul_le_mul_of_nonneg_left h4 hB.le
      exact mul_le_mul_of_nonneg_right this hE.le
    linarith
  have hsum : ∑ N ∈ Finset.Ico M (4 * M + 1), (blockCount γ Bad N : ℝ) ≤
      ∑ _N ∈ Finset.Ico M (4 * M + 1), (B * (4 * (M : ℝ)) * E) := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at hsum
  have h3 : ((3 * M + 1 : ℕ) : ℝ) ≤ 4 * (M : ℝ) := by
    have : 3 * M + 1 ≤ 4 * M := by omega
    exact_mod_cast this
  have h4 : ((3 * M + 1 : ℕ) : ℝ) * (B * (4 * (M : ℝ)) * E) ≤
      (4 * (M : ℝ)) * (B * (4 * (M : ℝ)) * E) :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  have h5 : (4 * (M : ℝ)) * (B * (4 * (M : ℝ)) * E) =
      16 * B * (M : ℝ) ^ 2 * E := by ring
  linarith [hsum, h4, h5]

/-- LEAF page 366, "a routine dyadic dissection argument", last line of section 5. For any set
`Bad`: a block bound in the windows of `F` gives a saving on `[M, 2M)`. The block `[M, 2M)` meets
about `log₂ (F(2M)/F(M)) ≪ (log M)^γ` windows, each of size at most `B N ℰ^{-1/12}`, and that power
of `log M` is absorbed by the exponential. -/
theorem leaf_block_dissection (γ κ B : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hκ : 0 < κ) (hB : 0 < B)
    (Bad : ℕ → Prop) (N₀ : ℕ)
    (h : ∀ N : ℕ, N₀ ≤ N → (blockCount γ Bad N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ))) :
    ∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      (dyadicCount Bad M : ℝ) ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) := by
  have hp : 0 < 3 - 2 * γ := by linarith
  have hp1 : 3 - 2 * γ < 1 := by linarith
  have hγ0 : 0 < γ := by linarith
  have hA2 : 0 < Real.log 2 / (16 * γ) :=
    div_pos (Real.log_pos (by norm_num)) (by linarith)
  obtain ⟨M1, hM1⟩ := eventually_absorb h1 h2 hκ
  obtain ⟨M2, hM2⟩ := exists_calE_small (p := 3 - 2 * γ) hp hp1 hκ
  refine ⟨κ / 24, by linarith, 32 * B / (Real.log 2 / (16 * γ)), by positivity,
    max N₀ (max 8 (max M1 (max M2 5000))), ?_⟩
  intro M hM0
  have hMN₀ : N₀ ≤ M := le_trans (Nat.le_max_left _ _) hM0
  have hM8 : 8 ≤ M := le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hM0
  have hMmid : max M1 (max M2 5000) ≤ M := by
    refine le_trans ?_ hM0
    exact le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hMM1 : M1 ≤ M := le_trans (Nat.le_max_left _ _) hMmid
  have hMM2 : M2 ≤ M := le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_right _ _) hMmid)
  have hM5000 : 5000 ≤ M :=
    le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_right _ _) hMmid)
  have hM1' : 1 ≤ M := by omega
  have hMposN : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  -- the double count
  have hcount' : (mult γ M : ℝ) * (dyadicCount Bad M : ℝ) ≤
      ∑ N ∈ Finset.Ico M (4 * M + 1), (blockCount γ Bad N : ℝ) := by
    refine card_mul_le_sum_blocks γ Bad M (mult γ M) (fun n hn => ?_)
    obtain ⟨hnI, _⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnM, hn2M⟩ := Finset.mem_Ico.mp hnI
    exact_mod_cast card_window_ge_mult h1 hM8 hnM hn2M
  have hsum := sum_blockCount_le h1 h2 hκ hB h hMN₀ hM1'
  set k := (Real.log 2 / (16 * γ)) * (M : ℝ) *
    (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (1 - γ) with hkdef
  set Q := (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (γ - 1) with hQdef
  have hQpos : 0 < Q := by
    rw [hQdef]; exact Real.rpow_pos_of_pos (log_nat_add_one_pos _) _
  have hinvQ : (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (1 - γ) = Q⁻¹ := by
    rw [hQdef, show (1 : ℝ) - γ = -(γ - 1) by ring,
      Real.rpow_neg (le_of_lt (log_nat_add_one_pos _))]
  have hkform : k = (Real.log 2 / (16 * γ)) * (M : ℝ) * Q⁻¹ := by rw [hkdef, hinvQ]
  have hkpos : 0 < k := by
    have h3 : 0 < (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (1 - γ) :=
      Real.rpow_pos_of_pos (log_nat_add_one_pos _) _
    rw [hkdef]; exact mul_pos (mul_pos hA2 hMposN) h3
  have hmult_le : (mult γ M : ℝ) ≤ k := by
    rw [hkdef]; exact mult_le_cast hγ0 M
  have hmult_lt : k < (mult γ M : ℝ) + 1 := by
    rw [hkdef]; exact Nat.lt_floor_add_one _
  -- `√M = exp (log M / 2)`
  have hQsqM : Real.sqrt (M : ℝ) = Real.exp (Real.log M / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hMposN]
    congr 1
    ring
  have hQle : Q ≤ Real.sqrt (M : ℝ) := by
    refine le_trans (hM1 M hMM1) ?_
    rw [hQsqM]
    exact Real.exp_le_exp.mpr (hM2 M hMM2)
  have hsqrtpos : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMposN
  have hMsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt hMposN.le
  have hsqrt70 : (70 : ℝ) ≤ Real.sqrt (M : ℝ) := by
    have hsq : Real.sqrt ((70 : ℝ) ^ 2) ≤ Real.sqrt (M : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 4900 ≤ M))
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 70)] at hsq
  have h70 : (2 : ℝ) ≤ (Real.log 2 / (16 * γ)) * 70 := by
    have hlog2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : (0 : ℝ) < 16 * γ)]
    nlinarith
  have hk2 : 2 ≤ k := by
    rw [hkform]
    have hle : Real.sqrt (M : ℝ) ≤ (M : ℝ) / Q := by
      rw [le_div_iff₀ hQpos]
      calc Real.sqrt (M : ℝ) * Q ≤ Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) :=
            mul_le_mul_of_nonneg_left hQle hsqrtpos.le
        _ = (M : ℝ) := hMsq
    have h4 : (M : ℝ) / Q = (M : ℝ) * Q⁻¹ := by ring
    have hstep : (Real.log 2 / (16 * γ)) * Real.sqrt (M : ℝ) ≤
        (Real.log 2 / (16 * γ)) * (M : ℝ) * Q⁻¹ := by
      calc (Real.log 2 / (16 * γ)) * Real.sqrt (M : ℝ)
          ≤ (Real.log 2 / (16 * γ)) * ((M : ℝ) / Q) :=
            mul_le_mul_of_nonneg_left hle hA2.le
        _ = (Real.log 2 / (16 * γ)) * (M : ℝ) * Q⁻¹ := by
            rw [h4]; ring
    calc (2 : ℝ) ≤ (Real.log 2 / (16 * γ)) * 70 := h70
      _ ≤ (Real.log 2 / (16 * γ)) * Real.sqrt (M : ℝ) :=
          mul_le_mul_of_nonneg_left hsqrt70 hA2.le
      _ ≤ _ := hstep
  have hmultk : k / 2 ≤ (mult γ M : ℝ) := by linarith
  set E1 := Real.exp (-(κ / 12) * Real.log M ^ (3 - 2 * γ)) with hE1def
  have hDk : (dyadicCount Bad M : ℝ) * k ≤
      2 * (∑ N ∈ Finset.Ico M (4 * M + 1), (blockCount γ Bad N : ℝ)) := by
    have hD0 : (0 : ℝ) ≤ (dyadicCount Bad M : ℝ) := Nat.cast_nonneg _
    nlinarith [hcount', hmultk, hkpos, hD0]
  have hS16 : ∑ N ∈ Finset.Ico M (4 * M + 1), (blockCount γ Bad N : ℝ) ≤
      16 * B * (M : ℝ) ^ 2 * E1 := by
    rw [hE1def]; exact hsum
  have hD_le : (dyadicCount Bad M : ℝ) ≤ 32 * B * (M : ℝ) ^ 2 * E1 / k := by
    rw [le_div_iff₀ hkpos]
    nlinarith [hDk, hS16]
  refine hD_le.trans ?_
  have hscalar : E1 ≤ Real.exp (-(κ / 24) * Real.log M ^ (3 - 2 * γ)) * Q⁻¹ := by
    have hQle' : Q ≤ Real.exp (κ / 24 * Real.log M ^ (3 - 2 * γ)) := hM1 M hMM1
    have hone : (1 : ℝ) ≤ Real.exp (κ / 24 * Real.log M ^ (3 - 2 * γ)) * Q⁻¹ := by
      have h := mul_le_mul_of_nonneg_right hQle' (le_of_lt (inv_pos.mpr hQpos))
      rwa [mul_inv_cancel₀ (ne_of_gt hQpos)] at h
    have hpos1 : (0 : ℝ) < Real.exp (-(κ / 12) * Real.log M ^ (3 - 2 * γ)) := Real.exp_pos _
    have h := mul_le_mul_of_nonneg_left hone hpos1.le
    rw [mul_one] at h
    calc E1 = Real.exp (-(κ / 12) * Real.log M ^ (3 - 2 * γ)) := hE1def
      _ ≤ Real.exp (-(κ / 12) * Real.log M ^ (3 - 2 * γ)) *
            (Real.exp (κ / 24 * Real.log M ^ (3 - 2 * γ)) * Q⁻¹) := h
      _ = Real.exp (-(κ / 24) * Real.log M ^ (3 - 2 * γ)) * Q⁻¹ := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          ring
  rw [div_le_iff₀ hkpos, hkform]
  have hM2nn : (0 : ℝ) ≤ 32 * B * (M : ℝ) ^ 2 := by positivity
  calc 32 * B * (M : ℝ) ^ 2 * E1
      ≤ 32 * B * (M : ℝ) ^ 2 *
          (Real.exp (-(κ / 24) * Real.log M ^ (3 - 2 * γ)) * Q⁻¹) :=
        mul_le_mul_of_nonneg_left hscalar hM2nn
    _ = 32 * B / (Real.log 2 / (16 * γ)) * (M : ℝ) *
          Real.exp (-(κ / 24) * Real.log M ^ (3 - 2 * γ)) *
          ((Real.log 2 / (16 * γ)) * (M : ℝ) * Q⁻¹) := by
        field_simp

/-- ASSEMBLY page 366 and 367. No longer Theorem 1 restated: it follows from `block_bound` and the
dissection leaf, and does not use `BrudernPerelli1998.brudernPerelli`. -/
theorem leaf_dyadic_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      (Eγ_dyadic γ M : ℝ) ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) := by
  obtain ⟨κ, B, hκ, hB, N₀, h⟩ := block_bound γ h1 h2
  obtain ⟨c, hc, C, hC, M0, hM⟩ :=
    leaf_block_dissection γ κ B h1 h2 hκ hB (fun n => ¬ Solvable γ n) N₀ h
  refine ⟨c, hc, C, hC, M0, fun M hM0 => ?_⟩
  have e : Eγ_dyadic γ M = dyadicCount (fun n => ¬ Solvable γ n) M := by
    unfold Eγ_dyadic dyadicCount
    congr!
  rw [e]
  exact hM M hM0

/-- PROVED. The total exceptions up to `N` are at most the sum over the dyadic blocks. -/
theorem leaf_dyadic_sum (γ : ℝ) (N : ℕ) :
    (Eγ γ N : ℝ) ≤ (∑ i ∈ dyadicIdx N, (Eγ_dyadic γ i : ℝ)) := by
  have hsub : (Finset.Icc 1 N).filter (fun n => ¬ Solvable γ n) ⊆
      (dyadicIdx N).biUnion (fun i => (Finset.Ico i (2 * i)).filter (fun n => ¬ Solvable γ n)) := by
    intro n hn
    obtain ⟨hn, hb⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    refine Finset.mem_biUnion.mpr ⟨2 ^ Nat.log 2 n, ?_, Finset.mem_filter.mpr ⟨?_, hb⟩⟩
    · refine Finset.mem_image.mpr ⟨Nat.log 2 n, ?_, rfl⟩
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right hnN))
    · refine Finset.mem_Ico.mpr ⟨Nat.pow_log_le_self 2 (by omega), ?_⟩
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
      rw [pow_succ] at this
      omega
  have hcard : Eγ γ N ≤ ∑ i ∈ dyadicIdx N, Eγ_dyadic γ i :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  exact_mod_cast hcard

/-- For `0 < p ≤ 1` and `0 ≤ y`, `y ^ p ≤ y + 1`. -/
private lemma rpow_le_self_add_one {y p : ℝ} (hy : 0 ≤ y) (hp : 0 < p) (hp1 : p ≤ 1) :
    y ^ p ≤ y + 1 := by
  by_cases h : y ≤ 1
  · have := Real.rpow_le_one hy h hp.le
    linarith
  · have hy1 : (1 : ℝ) < y := not_le.mp h
    have h' := Real.rpow_le_rpow_of_exponent_le hy1.le hp1
    rw [Real.rpow_one] at h'
    linarith

/-- PROVED, page 367. The sum of the exponential bound over the dyadic blocks: the sum runs over
`M = 2 ^ j ≤ N` and is geometric; over all `M ≤ N` it would be about `N²` times the exponential. -/
theorem leaf_dyadic_sum_exp (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ c' > 0, ∃ C' > 0, ∀ N : ℕ, 2 ≤ N →
      (∑ M ∈ dyadicIdx N, C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) : ℝ)
      ≤ C' * N * Real.exp (-c' * Real.log N ^ (3 - 2 * γ)) := by
  set p : ℝ := 3 - 2 * γ with hpdef
  have hp : 0 < p := by rw [hpdef]; linarith
  have hp1 : p < 1 := by rw [hpdef]; linarith
  set d : ℝ := min c (1 / 2) with hd
  have hd0 : 0 < d := lt_min hc (by norm_num)
  have hdc : d ≤ c := min_le_left _ _
  have hd2 : d ≤ 1 / 2 := min_le_right _ _
  refine ⟨d, hd0, C * Real.exp d * 4, by positivity, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  set L : ℝ := Real.log N with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hN1
  set sN : ℝ := Real.exp (L / 2) with hsN
  have hsN0 : 0 < sN := Real.exp_pos _
  have hsN2 : sN ^ 2 = N := by
    rw [hsN, ← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (L / 2) = L := by push_cast; ring
    rw [this, hL, Real.exp_log hN0]
  set r : ℝ := Real.exp (Real.log 2 / 2) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr2 : r ^ 2 = 2 := by
    rw [hr, ← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (Real.log 2 / 2) = Real.log 2 := by push_cast; ring
    rw [this, Real.exp_log (by norm_num)]
  have hr43 : 4 / 3 ≤ r := by
    by_contra hlt
    have hlt' : r < 4 / 3 := not_le.mp hlt
    nlinarith
  have hgeom : ∀ J : ℕ, ∑ j ∈ Finset.range (J + 1), r ^ j ≤ 4 * r ^ J := by
    intro J
    induction J with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ r n]
      have hrn : 0 < r ^ n := pow_pos hr0 n
      nlinarith
  have hterm : ∀ j ∈ Finset.range (Nat.log 2 N + 1),
      C * ((2 ^ j : ℕ) : ℝ) * Real.exp (-c * Real.log ((2 ^ j : ℕ) : ℝ) ^ p) ≤
        (C * Real.exp d * Real.exp (-d * L ^ p) * sN) * r ^ j := by
    intro j hj
    have hjN : 2 ^ j ≤ N := by
      have hj' : j ≤ Nat.log 2 N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      exact (Nat.pow_le_pow_right (by norm_num) hj').trans (Nat.pow_log_le_self 2 (by omega))
    have hM1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
    set x : ℝ := Real.log ((2 ^ j : ℕ) : ℝ) with hx
    have hx0 : 0 ≤ x := Real.log_nonneg hM1
    have hxL : x ≤ L := Real.log_le_log (by linarith) (by exact_mod_cast hjN)
    have hy0 : 0 ≤ L - x := by linarith
    have hsub : L ^ p ≤ x ^ p + (L - x) ^ p := by
      have := Real.rpow_add_le_add_rpow hx0 hy0 hp.le hp1.le
      rwa [add_sub_cancel] at this
    have hy1 : (L - x) ^ p ≤ (L - x) + 1 := rpow_le_self_add_one hy0 hp hp1.le
    have hxp : 0 ≤ x ^ p := Real.rpow_nonneg hx0 _
    have hyp : 0 ≤ (L - x) ^ p := Real.rpow_nonneg hy0 _
    have hkey : -c * x ^ p ≤ d + -d * L ^ p + (L - x) / 2 := by
      have e1 : d * L ^ p ≤ d * x ^ p + d * (L - x) ^ p := by nlinarith
      have e2 : d * x ^ p ≤ c * x ^ p := mul_le_mul_of_nonneg_right hdc hxp
      have e3 : d * (L - x) ^ p ≤ d * ((L - x) + 1) := mul_le_mul_of_nonneg_left hy1 hd0.le
      have e4 : d * (L - x) ≤ (1 / 2) * (L - x) := mul_le_mul_of_nonneg_right hd2 hy0
      nlinarith
    have hexp := Real.exp_le_exp.mpr hkey
    have hxval : ((2 ^ j : ℕ) : ℝ) = Real.exp x := by
      rw [hx, Real.exp_log (by linarith)]
    have hrj : r ^ j = Real.exp (x / 2) := by
      rw [hr, ← Real.exp_nat_mul, hx]
      congr 1
      push_cast
      rw [Real.log_pow]
      ring
    have hcomb : Real.exp x * Real.exp (d + -d * L ^ p + (L - x) / 2) =
        Real.exp d * Real.exp (-d * L ^ p) * sN * Real.exp (x / 2) := by
      rw [hsN]
      simp only [← Real.exp_add]
      congr 1
      ring
    rw [hrj]
    calc C * ((2 ^ j : ℕ) : ℝ) * Real.exp (-c * x ^ p)
        = C * Real.exp x * Real.exp (-c * x ^ p) := by rw [← hxval]
      _ ≤ C * Real.exp x * Real.exp (d + -d * L ^ p + (L - x) / 2) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = C * (Real.exp x * Real.exp (d + -d * L ^ p + (L - x) / 2)) := by ring
      _ = _ := by rw [hcomb]; ring
  have hinj : Set.InjOn (fun j : ℕ => 2 ^ j)
      (Finset.range (Nat.log 2 N + 1) : Set ℕ) :=
    fun _ _ _ _ h => Nat.pow_right_injective (le_refl 2) h
  unfold dyadicIdx
  rw [Finset.sum_image hinj]
  have hA : 0 ≤ C * Real.exp d * Real.exp (-d * L ^ p) * sN := by positivity
  have hrJ : r ^ Nat.log 2 N ≤ sN := by
    have h2J : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have : (r ^ Nat.log 2 N) ^ 2 ≤ sN ^ 2 := by
      rw [hsN2, ← pow_mul, mul_comm, pow_mul, hr2]
      exact_mod_cast h2J
    exact (pow_le_pow_iff_left₀ (by positivity) hsN0.le (by norm_num)).mp this
  calc _ ≤ ∑ j ∈ Finset.range (Nat.log 2 N + 1),
        (C * Real.exp d * Real.exp (-d * L ^ p) * sN) * r ^ j := Finset.sum_le_sum hterm
    _ = (C * Real.exp d * Real.exp (-d * L ^ p) * sN) *
        ∑ j ∈ Finset.range (Nat.log 2 N + 1), r ^ j := by rw [Finset.mul_sum]
    _ ≤ (C * Real.exp d * Real.exp (-d * L ^ p) * sN) * (4 * sN) :=
        mul_le_mul_of_nonneg_left ((hgeom _).trans (by linarith)) hA
    _ = C * Real.exp d * 4 * sN ^ 2 * Real.exp (-d * L ^ p) := by ring
    _ = _ := by rw [hsN2]

/-- For `N ≥ 2` and `0 < p < 1`, the factor `N * exp (-c * (log N) ^ p)` dominates the constant
`exp (-c) * 2 ^ (1 - c)` when `0 < c ≤ 1`. -/
private lemma le_mul_exp_neg_mul_log_rpow {c p : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hp : 0 < p) (hp1 : p < 1) {N : ℕ} (hN : 2 ≤ N) :
    Real.exp (-c) * (2 : ℝ) ^ (1 - c) ≤
      (N : ℝ) * Real.exp (-c * Real.log N ^ p) := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hstep : Real.log N ^ p ≤ Real.log N + 1 := rpow_le_self_add_one hlog hp hp1.le
  have hmul : c * Real.log N ^ p ≤ c * (Real.log N + 1) :=
    mul_le_mul_of_nonneg_left hstep hc.le
  have hexp_le : Real.exp (-c * Real.log N - c) ≤ Real.exp (-c * Real.log N ^ p) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpow : (0 : ℝ) ≤ 1 - c := by linarith
  have hNpow : (2 : ℝ) ^ (1 - c) ≤ (N : ℝ) ^ (1 - c) :=
    Real.rpow_le_rpow (by norm_num) hN2 hpow
  have hmain : (N : ℝ) * Real.exp (-c * Real.log N) = (N : ℝ) ^ (1 - c) := by
    calc (N : ℝ) * Real.exp (-c * Real.log N)
        = Real.exp (Real.log N) * Real.exp (-c * Real.log N) := by rw [Real.exp_log hNpos]
      _ = Real.exp (Real.log N + -c * Real.log N) := by rw [← Real.exp_add]
      _ = Real.exp (Real.log N * (1 - c)) := by
          congr 1
          ring
      _ = (N : ℝ) ^ (1 - c) := by rw [Real.rpow_def_of_pos hNpos]
  calc Real.exp (-c) * (2 : ℝ) ^ (1 - c)
      ≤ Real.exp (-c) * (N : ℝ) ^ (1 - c) :=
        mul_le_mul_of_nonneg_left hNpow (Real.exp_pos _).le
    _ = Real.exp (-c) * ((N : ℝ) * Real.exp (-c * Real.log N)) := by rw [hmain]
    _ = (N : ℝ) * (Real.exp (-c) * Real.exp (-c * Real.log N)) := by ring
    _ = (N : ℝ) * Real.exp (-c * Real.log N - c) := by
        congr 1
        rw [← Real.exp_add]
        ring
    _ ≤ (N : ℝ) * Real.exp (-c * Real.log N ^ p) :=
        mul_le_mul_of_nonneg_left hexp_le hNpos.le

/-- LEAF page 367: Given the exponential sum bound and dyadic sum bound, Theorem 1 holds. -/
theorem leaf_theorem1_from_sums (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    (∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M → (Eγ_dyadic γ M : ℝ) ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ))) →
    (∀ M : ℕ, Eγ_dyadic γ M ≤ M) →
    (∀ N : ℕ, (Eγ γ N : ℝ) ≤ (∑ i ∈ dyadicIdx N, Eγ_dyadic γ i : ℝ)) →
    (∀ c C : ℝ, 0 < c → 0 < C → ∃ c' > 0, ∃ C' > 0, ∀ N : ℕ, 2 ≤ N →
      (∑ M ∈ dyadicIdx N, C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) : ℝ) ≤ C' * N * Real.exp (-c' * Real.log N ^ (3 - 2 * γ))) →
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (Eγ γ N : ℝ) ≤ C * N * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := by
  intro hA hB hC hD
  obtain ⟨c₀, hc₀, C₀, hC₀, M₀, hM₀⟩ := hA
  obtain ⟨c₁, hc₁, C₁, hC₁, hD₁⟩ := hD c₀ C₀ hc₀ hC₀
  have hp : 0 < 3 - 2 * γ := by linarith
  have hp1 : 3 - 2 * γ < 1 := by linarith
  set c : ℝ := min c₁ (1 / 2) with hcdef
  have hc : 0 < c := by
    rw [hcdef]; exact lt_min hc₁ (by norm_num)
  have hcc₁ : c ≤ c₁ := by
    rw [hcdef]; exact min_le_left _ _
  have hc1 : c ≤ 1 := by
    rw [hcdef]; have := min_le_right c₁ (1 / 2 : ℝ); linarith
  have hδ : 0 < Real.exp (-c) * (2 : ℝ) ^ (1 - c) :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨c, hc, (M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)) + C₁, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hnonneg : (0 : ℝ) ≤ Real.log N ^ (3 - 2 * γ) := Real.rpow_nonneg hlogN _
  have hexp_le : Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ)) ≤
      Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsplit : (∑ i ∈ dyadicIdx N, (Eγ_dyadic γ i : ℝ))
      = (∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (Eγ_dyadic γ i : ℝ))
      + (∑ i ∈ (dyadicIdx N).filter (fun i => ¬ i < M₀), (Eγ_dyadic γ i : ℝ)) :=
    (Finset.sum_filter_add_sum_filter_not (dyadicIdx N) (fun i => i < M₀)
      (fun i => (Eγ_dyadic γ i : ℝ))).symm
  have hpart1 : (∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (Eγ_dyadic γ i : ℝ))
      ≤ (M₀ : ℝ) ^ 2 := by
    have h1 : (∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (Eγ_dyadic γ i : ℝ))
        ≤ ∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (i : ℝ) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      exact_mod_cast hB i
    have h2 : (∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (i : ℝ)) ≤ (M₀ : ℝ) ^ 2 := by
      have hcard : ((dyadicIdx N).filter (fun i => i < M₀)).card ≤ M₀ := by
        have hsub : (dyadicIdx N).filter (fun i => i < M₀) ⊆ Finset.range M₀ := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
          exact hi.2
        calc _ ≤ (Finset.range M₀).card := Finset.card_le_card hsub
          _ = M₀ := Finset.card_range M₀
      have hcard' : (((dyadicIdx N).filter (fun i => i < M₀)).card : ℝ) ≤ (M₀ : ℝ) := by
        exact_mod_cast hcard
      have hM₀nn : (0 : ℝ) ≤ (M₀ : ℝ) := by positivity
      calc (∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (i : ℝ))
          ≤ ∑ _i ∈ (dyadicIdx N).filter (fun i => i < M₀), (M₀ : ℝ) := by
            refine Finset.sum_le_sum (fun i hi => ?_)
            have hi' : i < M₀ := (Finset.mem_filter.mp hi).2
            exact_mod_cast hi'.le
        _ = (((dyadicIdx N).filter (fun i => i < M₀)).card : ℝ) * (M₀ : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (M₀ : ℝ) * (M₀ : ℝ) := by nlinarith
        _ = (M₀ : ℝ) ^ 2 := by ring
    linarith
  have hpart2 : (∑ i ∈ (dyadicIdx N).filter (fun i => ¬ i < M₀), (Eγ_dyadic γ i : ℝ))
      ≤ C₁ * N * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ)) := by
    have hle1 : (∑ i ∈ (dyadicIdx N).filter (fun i => ¬ i < M₀), (Eγ_dyadic γ i : ℝ))
        ≤ ∑ i ∈ (dyadicIdx N).filter (fun i => ¬ i < M₀),
            (C₀ * i * Real.exp (-c₀ * Real.log i ^ (3 - 2 * γ))) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hiM : M₀ ≤ i := by
        have := (Finset.mem_filter.mp hi).2
        omega
      exact hM₀ i hiM
    have hle2 : (∑ i ∈ (dyadicIdx N).filter (fun i => ¬ i < M₀),
            (C₀ * i * Real.exp (-c₀ * Real.log i ^ (3 - 2 * γ))))
        ≤ ∑ i ∈ dyadicIdx N, (C₀ * i * Real.exp (-c₀ * Real.log i ^ (3 - 2 * γ))) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
      intro i _ _
      positivity
    linarith [hD₁ N hN]
  have hDbound : (M₀ : ℝ) ^ 2 ≤ ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)))
      * ((N : ℝ) * Real.exp (-c * Real.log N ^ (3 - 2 * γ))) := by
    have hkey := le_mul_exp_neg_mul_log_rpow (c := c) (p := 3 - 2 * γ) hc hc1 hp hp1 hN
    calc (M₀ : ℝ) ^ 2
        = ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)))
            * (Real.exp (-c) * (2 : ℝ) ^ (1 - c)) := by field_simp
      _ ≤ ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)))
            * ((N : ℝ) * Real.exp (-c * Real.log N ^ (3 - 2 * γ))) :=
          mul_le_mul_of_nonneg_left hkey (div_nonneg (sq_nonneg _) hδ.le)
  have hC₁le : C₁ * N * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ))
      ≤ C₁ * N * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := by
    have h1 : (0 : ℝ) ≤ C₁ * (N : ℝ) := by positivity
    calc C₁ * (N : ℝ) * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ))
        = (C₁ * (N : ℝ)) * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ)) := by ring
      _ ≤ (C₁ * (N : ℝ)) * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) :=
          mul_le_mul_of_nonneg_left hexp_le h1
  calc (Eγ γ N : ℝ)
      ≤ (∑ i ∈ dyadicIdx N, (Eγ_dyadic γ i : ℝ)) := hC N
    _ = (∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (Eγ_dyadic γ i : ℝ))
        + (∑ i ∈ (dyadicIdx N).filter (fun i => ¬ i < M₀), (Eγ_dyadic γ i : ℝ)) := hsplit
    _ ≤ (M₀ : ℝ) ^ 2 + C₁ * N * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ)) := by linarith
    _ ≤ ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)) + C₁)
        * ((N : ℝ) * Real.exp (-c * Real.log N ^ (3 - 2 * γ))) := by nlinarith
    _ = ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)) + C₁) * N
        * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := by ring

/-- ASSEMBLY. Theorem 1 of Brudern and Perelli 1998 from leaves. -/
theorem brudernPerelli_assembly : Theorem1 := by
  intro γ h1 h2
  exact leaf_theorem1_from_sums γ h1 h2
    (leaf_dyadic_bound γ h1 h2)
    (leaf_dyadic_trivial γ)
    (leaf_dyadic_sum γ)
    (leaf_dyadic_sum_exp γ h1 h2)

end LeanLab.ExceptionalSet.DecompJ200
