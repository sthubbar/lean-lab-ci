import LeanLab.ExceptionalSet.SPLIT_leaf_poisson
import LeanLab.ExceptionalSet.Decomp462a
import LeanLab.ExceptionalSet.Decomp462e

/-!
Split of the sealed statement `leaf_poisson_summation` of
`LeanLab.ExceptionalSet.SPLIT_leaf_poisson` into five strictly smaller steps, plus an assembly
`leaf_poisson_summation_split` whose statement is the sealed statement and whose proof uses only
the five leaves.

The argument is the standard one for a sampling formula of this shape. Write `F` for the
periodization of the modulated kernel, `F x = ∑' n, K (x + n) * eC (-((x + n) * v))`. Then

* `F` is 1-periodic, because shifting `x` by one only relabels the integer index;
* `F` is continuous, which is where the frequency support of `K` is used: a kernel whose
  transform is carried by the unit interval has bounded, summable shifts;
* the `m`-th Fourier coefficient of `F`, integrated over one period, is the value of the
  transform of `K` at the shifted frequency `v + m`: folding the unit interval over the real
  line and using `eC` at an integer argument gives the shift;
* all but at most two of those coefficients vanish: the two integer shifts nearest to `-v` are
  the only ones whose frequency falls in the closed unit interval, and at the boundary
  frequencies the vanishing comes from continuity of the transform rather than from the strict
  inequality `1 < |α|`;
* a continuous 1-periodic function whose coefficients vanish off two frequencies equals its
  finite Fourier series.

The assembly evaluates `F` at `α` by the last step and rewrites the coefficients by the third.

AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp371d

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck)

/-- LEAF. Periodicity step: the periodization of the modulated kernel is 1-periodic. Shifting
`x` by one carries the series to itself by the index change `n ↦ n + 1`, and the modulation
`eC (-((x + n) * v))` moves with the shift because it is a function of `x + n`. -/
theorem leaf_summation_periodic (K : ℝ → ℂ) (v : ℝ) :
    Function.Periodic (fun x : ℝ => ∑' n : ℤ, K (x + n) * eC (-((x + n) * v))) 1 := by
  intro x
  dsimp only
  let equiv := Equiv.addRight (1:ℤ)
  have h_eq : (fun (n : ℤ) => K (x + 1 + ↑n) * eC (-((x + 1 + ↑n) * v))) =
              (fun (n : ℤ) => K (x + ↑(equiv n)) * eC (-((x + ↑(equiv n)) * v))) := by
    ext n
    congr 2
    · change x + 1 + (n : ℝ) = x + ((n + 1 : ℤ) : ℝ)
      push_cast; ring
    · change -((x + 1 + (n : ℝ)) * v) = -((x + ((n + 1 : ℤ) : ℝ)) * v)
      push_cast; ring
  rw [h_eq]
  exact (Equiv.tsum_eq equiv (fun (n:ℤ) => K (x + ↑n) * eC (-((x + ↑n) * v))))

/-- LEAF. Continuity step: the periodization of the modulated kernel is continuous on the real
line, as a function of the base point. This is where integrability and continuity of `K` and the
frequencies carried by its transform are used: with the transform supported in the closed unit
interval, the periodization is a finite trigonometric sum in the base point, hence continuous. -/
theorem leaf_summation_continuous (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v : ℝ) :
    Continuous (fun x : ℝ => ∑' n : ℤ, K (x + n) * eC (-((x + n) * v))) := by
  exact Decomp462a.continuous_of_translate_norm K hcont
    (Decomp462e.translate_norm_supplied K hK hcont hsupp) v

/-- LEAF. Fourier coefficient step: the `m`-th Fourier coefficient of the periodization, taken
over one period, is the transform of `K` at the shifted frequency `v + m`. The period is folded
back onto the real line: the integral of the `n`-th summand over `[0,1]` is the integral of
`K u * eC (-(u * (v + m)))` over the adjacent interval `[n, n+1]`, because `eC` at the integer
argument `n * m` is one. -/
theorem leaf_summation_fourier_coeff (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v : ℝ) (m : ℤ) :
    (∫ x in (0 : ℝ)..1,
        (∑' n : ℤ, K (x + n) * eC (-((x + n) * v))) * eC (-(x * (m : ℝ)))) =
      ftR K (v + (m : ℝ)) := by
  exact Decomp462a.fourier_coeff_of_translate_norm K hcont
    (Decomp462e.translate_norm_supplied K hK hcont hsupp) v m

/-- LEAF. Support step: every integer shift other than the two nearest to `-v` puts the
frequency `v + m` at distance at least one from the origin, and the transform of `K` vanishes
there. At the boundary frequency `|v + m| = 1`, which occurs exactly when `v` is an integer and
`m = 1 - ⌊v⌋`, the vanishing is not covered by the strict inequality `1 < |α|` and comes from
continuity of the transform instead. -/
theorem leaf_summation_coefficient_vanishes (K : ℝ → ℂ) (hK : Integrable K)
    (hcont : Continuous K) (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v : ℝ) :
    ∀ m : ℤ, m ≠ -⌊v⌋ → m ≠ -(⌊v⌋ + 1) → ftR K (v + (m : ℝ)) = 0 := by
  intro m hm₁ hm₂
  exact leaf_poisson_endpoint K hK hcont hsupp _ (leaf_poisson_index v m hm₁ hm₂)

/-- LEAF. Fourier series step: a continuous 1-periodic function whose Fourier coefficients,
integrated over one period, vanish off two distinct integer frequencies `a` and `b` is equal to
its finite Fourier series at every point. Only two coefficients are nonzero, so the coefficient
series is summable, and a continuous function on the circle is the sum of its Fourier series. -/
theorem leaf_summation_fourier_series (F : ℝ → ℂ) (hper : Function.Periodic F 1)
    (hcont : Continuous F) (a b : ℤ) (hab : a ≠ b)
    (hfin : ∀ m : ℤ, m ≠ a → m ≠ b →
      (∫ x in (0 : ℝ)..1, F x * eC (-(x * (m : ℝ)))) = 0) (α : ℝ) :
    F α = ∑' m : ℤ, eC (α * (m : ℝ)) * ∫ x in (0 : ℝ)..1, F x * eC (-(x * (m : ℝ))) := by
  let G : C(UnitAddCircle, ℂ) := ⟨hper.lift, continuous_coinduced_dom.mpr hcont⟩
  have hphase (m : ℤ) (x : ℝ) : fourier (T := 1) m (x : UnitAddCircle) =
      eC (x * (m : ℝ)) := by
    rw [fourier_coe_apply]
    unfold eC
    simp only [Complex.ofReal_one, div_one]
    congr 1
    push_cast
    ring
  have hcoeff (m : ℤ) : fourierCoeff G m =
      ∫ x in (0 : ℝ)..1, F x * eC (-(x * (m : ℝ))) := by
    rw [fourierCoeff_eq_intervalIntegral _ m 0]
    simp only [div_one, one_smul, zero_add]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [hphase]
    simp only [G, ContinuousMap.coe_mk, Function.Periodic.lift_coe, smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  have hs : Summable (fourierCoeff G) := by
    apply summable_of_ne_finset_zero (s := {a, b})
    intro m hm
    rw [hcoeff]
    apply hfin m
    · intro he; exact hm (by simp [he])
    · intro he; exact hm (by simp [he])
  have hsum := (has_pointwise_sum_fourier_series_of_summable hs (α : UnitAddCircle)).tsum_eq.symm
  change G (α : UnitAddCircle) = _
  rw [hsum]
  apply tsum_congr
  intro m
  rw [hcoeff, hphase, smul_eq_mul, mul_comm]

/-- Assembly: the sealed statement, from the five leaves above. The periodization is 1-periodic
and continuous, its coefficients vanish off the two shifts `-⌊v⌋` and `-(⌊v⌋ + 1)`, so it is the
sum of its finite Fourier series; each coefficient is the transform of `K` at `v + m`. -/
theorem leaf_poisson_summation_split (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
      ∑' m : ℤ, eC (α * (m : ℝ)) * ftR K (v + (m : ℝ)) := by
  have hne : (-⌊v⌋ : ℤ) ≠ -(⌊v⌋ + 1) := by omega
  have hseries :=
    leaf_summation_fourier_series
      (fun x : ℝ => ∑' n : ℤ, K (x + n) * eC (-((x + n) * v)))
      (leaf_summation_periodic K v) (leaf_summation_continuous K hK hcont hsupp v)
      (-⌊v⌋) (-(⌊v⌋ + 1)) hne
      (fun m h1 h2 => by
        rw [leaf_summation_fourier_coeff K hK hcont hsupp v m]
        exact leaf_summation_coefficient_vanishes K hK hcont hsupp v m h1 h2) α
  change (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
      ∑' m : ℤ, eC (α * (m : ℝ)) * ftR K (v + (m : ℝ))
  rw [hseries]
  exact tsum_congr fun m => by
    rw [leaf_summation_fourier_coeff K hK hcont hsupp v m]

end LeanLab.ExceptionalSet.Decomp371d
