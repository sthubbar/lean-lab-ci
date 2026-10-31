/-
# Pintz and Althöfer 2026, Theorem 3: `UpperHalf` reduced to an L² integral by Bessel

Unit U-1197, T2 FRONTIER, idea I-0080, PC run 20261020T0902Z-22676.

Source: Pintz and Althöfer, arXiv 2610.15559v1, Section 4.4: the bad even `n` in `(X/2, X]`
are counted by Bessel's inequality for `F_X² − V_X²` on `[0, 1]`, where
`F_X(α) = Σ Λ(m) e^{−m/X} e(mα)` and `V_X` is the major arc model with coefficients `v_X(n)`.

What is here, all PROVED unconditional:
* `bessel_finset`: Bessel's inequality on the circle `ℝ/ℤ`, for every `f` in `L²` and every
  finite set `S` of frequencies, `Σ_{n∈S} |f̂(n)|² ≤ ∫ |f|²`, from Mathlib's Parseval.
* `fourierCoeff_trig`: the `n`-th Fourier coefficient of a trigonometric polynomial
  `Σ_{m≤M} a_m e(mα)` is `a_n` for `0 ≤ n ≤ M`.
* `fourierCoeff_trig_sq`: the `n`-th coefficient of its square is `Σ_{u≤n} a_u a_{n−u}`
  for `n ≤ M`.
* `fourierCoeff_FX_sq`: with `a_m = Λ(m) e^{−m/X}` the `n`-th coefficient of `F_{X,M}²` is
  `R_Λ(n) e^{−n/X}`, for `n ≤ M`, the coefficient the paper writes.
* `UpperHalfL2 θ`: for every `η > 0` and large `x`, SOME `L²` function `W` on the circle has the
  model coefficients `v_X(n)` at every bad even `n ∈ (x/2, x]` and
  `∫ |F_{x,x²}² − W|² ≤ K x^{2a(θ)+1+2η} log x`. This is the paper's (4.13) in integral form.
* `upperHalf_of_L2`: `UpperHalfL2 θ → UpperHalf θ`, so Theorem 3 is now CONDITIONAL ON
  `UpperHalfL2 θ` only: `theorem3_of_L2`, `five_eighths_of_L2`.

The truncation `M = x` of `F_X` loses nothing at the window, since every bad `n ≤ x`.
KNOWN mathematics, the paper's own route. AI wrote this Lean code. Binary Goldbach is OPEN.
TRUNCATION FIX, same run, after U-1200: every L² Prop here uses `F_{x,x²} = Σ_{m≤x²}`, not
`Σ_{m≤x}`. With the cut at `x`, the coefficients of `F²` at `n ∈ (x, 2x]` miss the pairs with a
part above `x` and differ from the model's by about `2(n − x)𝔖(n)e^{−n/x}`, so the integral is
`≫ x³` and the Prop would be FALSE for large `x`, since `2a(θ) + 1 < 3`. With the cut at `x²` the
omitted tail `Σ_{m>x²} Λ(m)e^{−m/x}` is `O(x² e^{−x})`, so the Prop is the paper's statement up to
a negligible error; the coefficients on the window are unchanged, `n ≤ x ≤ x²`.
-/
import LeanLab.ExceptionalSet.PintzAlthofer2026Split

namespace LeanLab.ExceptionalSet.PintzAlthofer2026Bessel

open Finset Real MeasureTheory AddCircle LeanLab.ExceptionalSet.PintzAlthofer2026
open LeanLab.ExceptionalSet.PintzAlthofer2026Split

attribute [local instance] Classical.propDecidable

noncomputable section

instance : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

local notation "𝕋" => AddCircle (1 : ℝ)

/-! ### Bessel on the circle -/

/-- **Bessel's inequality**: for `f ∈ L²(ℝ/ℤ)` and a finite set `S` of frequencies,
`Σ_{n∈S} ‖f̂(n)‖² ≤ ∫ ‖f‖²`. -/
theorem bessel_finset {f : 𝕋 → ℂ} (hf : MemLp f 2 haarAddCircle) (S : Finset ℤ) :
    ∑ n ∈ S, ‖fourierCoeff f n‖ ^ 2 ≤ ∫ t, ‖f t‖ ^ 2 ∂haarAddCircle := by
  set g := hf.toLp f
  have hcoef : fourierCoeff (g : 𝕋 → ℂ) = fourierCoeff f :=
    fourierCoeff_congr_ae (MemLp.coeFn_toLp hf)
  have hint : ∫ t, ‖(g : 𝕋 → ℂ) t‖ ^ 2 ∂haarAddCircle = ∫ t, ‖f t‖ ^ 2 ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hf] with t ht
    rw [ht]
  have h := hasSum_sq_fourierCoeff g
  rw [hcoef, hint] at h
  exact sum_le_hasSum S (fun i _ => by positivity) h

/-! ### Trigonometric polynomials and their squares -/

/-- `Σ_{m≤M} a_m e(m t)` on `ℝ/ℤ`. -/
def trig (a : ℕ → ℂ) (M : ℕ) (t : 𝕋) : ℂ :=
  ∑ m ∈ range (M + 1), a m * fourier (m : ℤ) t

theorem continuous_trig (a : ℕ → ℂ) (M : ℕ) : Continuous (trig a M) := by
  unfold trig
  exact continuous_finsetSum _ fun m _ => continuous_const.mul (fourier (m : ℤ)).continuous

theorem integrable_fourier_mul (c : ℂ) (k : ℤ) :
    Integrable (fun t : 𝕋 => c * fourier k t) haarAddCircle :=
  (continuous_const.mul (fourier k).continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The coefficient of a single term `c e(k t)`. -/
theorem fourierCoeff_monomial (c : ℂ) (k n : ℤ) :
    fourierCoeff (fun t : 𝕋 => c * fourier k t) n = if n = k then c else 0 := by
  rw [fourierCoeff.const_mul]
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) k) n
  rw [h]
  by_cases hn : n = k
  · subst hn; simp
  · simp [hn]

/-- The coefficient of a finite sum of monomials. -/
theorem fourierCoeff_sum_monomial {ι : Type*} (s : Finset ι) (c : ι → ℂ) (k : ι → ℤ) (n : ℤ) :
    fourierCoeff (fun t : 𝕋 => ∑ i ∈ s, c i * fourier (k i) t) n =
      ∑ i ∈ s, if n = k i then c i else 0 := by
  have hfun : (fun t : 𝕋 => ∑ i ∈ s, c i * fourier (k i) t) =
      ∑ i ∈ s, (fun t : 𝕋 => c i * fourier (k i) t) := by
    ext t; simp [Finset.sum_apply]
  rw [hfun, fourierCoeff.sum s _ (fun i _ => integrable_fourier_mul (c i) (k i))]
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => fourierCoeff_monomial (c i) (k i) n

/-- `fourierCoeff_trig`: the `n`-th coefficient of `Σ_{m≤M} a_m e(mt)` is `a_n` for `n ≤ M`. -/
theorem fourierCoeff_trig (a : ℕ → ℂ) (M n : ℕ) (hn : n ≤ M) :
    fourierCoeff (trig a M) n = a n := by
  unfold trig
  rw [fourierCoeff_sum_monomial]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b _ hb
    have : ((n : ℤ) = (b : ℤ)) ↔ n = b := Nat.cast_inj
    simp [this, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hn)) h

/-- The square of `trig` as a double sum of monomials. -/
theorem trig_sq (a : ℕ → ℂ) (M : ℕ) (t : 𝕋) :
    trig a M t ^ 2 = ∑ p ∈ range (M + 1) ×ˢ range (M + 1),
      (a p.1 * a p.2) * fourier ((p.1 : ℤ) + (p.2 : ℤ)) t := by
  unfold trig
  rw [sq, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
  rw [fourier_add]; ring

/-- `fourierCoeff_trig_sq`: for `n ≤ M`, the `n`-th coefficient of `trig² ` is the
convolution `Σ_{u≤n} a_u a_{n−u}`. -/
theorem fourierCoeff_trig_sq (a : ℕ → ℂ) (M n : ℕ) (hn : n ≤ M) :
    fourierCoeff (fun t => trig a M t ^ 2) n =
      ∑ u ∈ range (n + 1), a u * a (n - u) := by
  have hfun : (fun t => trig a M t ^ 2) = (fun t : 𝕋 => ∑ p ∈ range (M + 1) ×ˢ range (M + 1),
      (a p.1 * a p.2) * fourier ((p.1 : ℤ) + (p.2 : ℤ)) t) := by
    ext t; exact trig_sq a M t
  rw [hfun, fourierCoeff_sum_monomial]
  -- keep the pairs with p.1 + p.2 = n
  have hcast : ∀ p : ℕ × ℕ, ((n : ℤ) = (p.1 : ℤ) + (p.2 : ℤ)) ↔ p.1 + p.2 = n := by
    intro p; constructor
    · intro h; have : ((p.1 + p.2 : ℕ) : ℤ) = (n : ℤ) := by push_cast; linarith
      exact_mod_cast this
    · intro h; rw [← h]; push_cast; ring
  simp_rw [hcast]
  rw [← Finset.sum_filter]
  -- the filtered set is the image of `u ↦ (u, n - u)` over `range (n+1)`
  have hset : (range (M + 1) ×ˢ range (M + 1)).filter (fun p : ℕ × ℕ => p.1 + p.2 = n) =
      (range (n + 1)).image (fun u => (u, n - u)) := by
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨_, _⟩, h⟩; exact ⟨u, by omega, rfl, by omega⟩
    · rintro ⟨w, hw, rfl, rfl⟩; exact ⟨⟨by omega, by omega⟩, by omega⟩
  rw [hset, Finset.sum_image]
  intro x _ y _ h
  simp only [Prod.mk.injEq] at h
  exact h.1

/-! ### `F_X` and the coefficient `R_Λ(n) e^{−n/X}` -/

/-- The coefficients `Λ(m) e^{−m/X}` of `F_X`. -/
def aF (X : ℝ) (m : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt m * Real.exp (-(m : ℝ) / X) : ℝ) : ℂ)

/-- `F_{X,M}(t) = Σ_{m≤M} Λ(m) e^{−m/X} e(mt)`, the paper's `F_X` truncated at `M`. -/
def FX (X : ℝ) (M : ℕ) : 𝕋 → ℂ := trig (aF X) M

/-- `fourierCoeff_FX_sq`: for `n ≤ M` the `n`-th coefficient of `F_{X,M}²` is
`R_Λ(n) e^{−n/X}`, exactly the coefficient the paper writes for `F_X²`. -/
theorem fourierCoeff_FX_sq (X : ℝ) (M n : ℕ) (hn : n ≤ M) :
    fourierCoeff (fun t => FX X M t ^ 2) n =
      ((RΛ n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) := by
  unfold FX
  rw [fourierCoeff_trig_sq _ M n hn]
  unfold RΛ aF
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' : u ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hu)
  have hsum : (-(u : ℝ) / X) + (-((n - u : ℕ) : ℝ) / X) = -(n : ℝ) / X := by
    rw [Nat.cast_sub hu']; ring
  have hexp : Complex.exp (↑(-(u : ℝ) / X)) * Complex.exp (↑(-((n - u : ℕ) : ℝ) / X)) =
      Complex.exp (↑(-(n : ℝ) / X)) := by
    rw [← Complex.exp_add, ← Complex.ofReal_add, hsum]
  rw [← Complex.ofReal_exp, ← Complex.ofReal_exp, ← Complex.ofReal_exp] at *
  have : ((Real.exp (-(u : ℝ) / X)) : ℂ) * ((Real.exp (-((n - u : ℕ) : ℝ) / X)) : ℂ) =
      ((Real.exp (-(n : ℝ) / X)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, hsum]
  push_cast at this ⊢
  linear_combination (ArithmeticFunction.vonMangoldt u : ℂ) *
    (ArithmeticFunction.vonMangoldt (n - u) : ℂ) * this

theorem memLp_FX_sq (X : ℝ) (M : ℕ) : MemLp (fun t => FX X M t ^ 2) 2 haarAddCircle :=
  ((continuous_trig _ M).pow 2).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-! ### `UpperHalf` from an L² bound -/

/-- **The L² form of the upper half**, the paper's (4.13) after Bessel, as a Prop, NOT proved:
for every `η > 0` and large `x` there is an `L²` function `W` on `ℝ/ℤ` whose Fourier coefficient
at every bad even `n ∈ (x/2, x]` is the model coefficient `v_X(n)`, with
`∫ |F_{x,x²}² − W|² ≤ K x^{2a(θ)+1+2η} log x`. In the paper `W = V_X`, the major arc model. -/
def UpperHalfL2 (θ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ K : ℝ, ∃ X0 : ℕ, ∀ x : ℕ, X0 ≤ x →
    ∃ W : 𝕋 → ℂ, MemLp W 2 haarAddCircle ∧
      (∀ n ∈ windowSet x, fourierCoeff W n = model x n) ∧
      ∫ t, ‖FX x (x ^ 2) t ^ 2 - W t‖ ^ 2 ∂haarAddCircle ≤
        K * (x : ℝ) ^ (2 * a θ + 1 + 2 * η) * Real.log x

theorem window_le (x n : ℕ) (hn : n ∈ windowSet x) : n ≤ x := by
  simp only [windowSet, Finset.mem_filter, Finset.mem_Icc] at hn
  exact hn.1.2

/-- **`upperHalf_of_L2`**: the L² bound gives `UpperHalf`, by Bessel. -/
theorem upperHalf_of_L2 {θ : ℝ} (hL : UpperHalfL2 θ) : UpperHalf θ := by
  intro η hη
  obtain ⟨K, X0, hK⟩ := hL η hη
  refine ⟨K, X0, fun x hx => ?_⟩
  obtain ⟨W, hW, hcoef, hint⟩ := hK x hx
  set G : 𝕋 → ℂ := fun t => FX x (x ^ 2) t ^ 2 - W t
  have hG : MemLp G 2 haarAddCircle := (memLp_FX_sq (x : ℝ) (x ^ 2)).sub hW
  have hcoefG : ∀ n ∈ windowSet x, fourierCoeff G n = coefF x n := by
    intro n hn
    have hsub : fourierCoeff G = fourierCoeff (fun t => FX x (x ^ 2) t ^ 2) - fourierCoeff W := by
      have h := fourierCoeff.add (T := (1 : ℝ)) (f := fun t => FX x (x ^ 2) t ^ 2) (g := -W)
        ((memLp_FX_sq (x : ℝ) (x ^ 2)).integrable one_le_two) (hW.integrable one_le_two).neg
      have hneg : fourierCoeff (-W) = -fourierCoeff W := by
        ext m
        have := fourierCoeff.const_smul (T := (1 : ℝ)) W (-1) m
        simpa [neg_smul, one_smul] using this
      rw [hneg] at h
      have hG' : G = (fun t => FX x (x ^ 2) t ^ 2) + -W := by
        ext t; simp [G, sub_eq_add_neg]
      rw [hG', h, sub_eq_add_neg]
    rw [hsub, Pi.sub_apply, fourierCoeff_FX_sq (x : ℝ) (x ^ 2) n ((window_le x n hn).trans (Nat.le_self_pow two_ne_zero x)), hcoef n hn]
    rfl
  have hb := bessel_finset hG ((windowSet x).image (fun n : ℕ => (n : ℤ)))
  rw [Finset.sum_image (fun a _ b _ h => by exact_mod_cast h)] at hb
  calc ∑ n ∈ windowSet x, ‖coefF x n‖ ^ 2
      = ∑ n ∈ windowSet x, ‖fourierCoeff G n‖ ^ 2 :=
        Finset.sum_congr rfl fun n hn => by rw [hcoefG n hn]
    _ ≤ ∫ t, ‖G t‖ ^ 2 ∂haarAddCircle := hb
    _ ≤ _ := hint

/-- Theorem 3 of Pintz-Althöfer, CONDITIONAL ON `UpperHalfL2 θ` only. -/
theorem theorem3_of_L2 {θ : ℝ} (h1 : 1 / 2 ≤ θ) (h2 : θ ≤ 2 / 3) (hL : UpperHalfL2 θ) :
    ∀ ε : ℝ, 0 < ε → PowerBound (g θ + ε) :=
  theorem3_of_upperHalf h1 h2 (upperHalf_of_L2 hL)

/-- θ = 5/8, CONDITIONAL ON `UpperHalfL2 (5/8)` only: `E(X) ≪ X^{25/44+ε}`. -/
theorem five_eighths_of_L2 (hL : UpperHalfL2 (5 / 8)) :
    ∀ ε : ℝ, 0 < ε → PowerBound (25 / 44 + ε) :=
  five_eighths_of_upperHalf (upperHalf_of_L2 hL)

/-! ### Vacuity -/

/-- The hypotheses of `fourierCoeff_FX_sq` hold: at `n = 4 ≤ M = 4` the coefficient is
`R_Λ(4) e^{−4/X}`, and `R_Λ(4) = (log 2)² > 0`, the pair `2 + 2`. -/
example : fourierCoeff (fun t => FX 10 4 t ^ 2) 4 =
    ((RΛ 4 * Real.exp (-((4 : ℕ) : ℝ) / 10) : ℝ) : ℂ) :=
  fourierCoeff_FX_sq 10 4 4 le_rfl

/-- `bessel_finset` is not vacuous: `f = e(t)` has `∫ |f|² = 1` and `f̂(1) = 1`. -/
example : ∑ n ∈ ({1} : Finset ℤ), ‖fourierCoeff (fun t : 𝕋 => (1 : ℂ) * fourier 1 t) n‖ ^ 2
    = 1 := by
  rw [Finset.sum_singleton, fourierCoeff_monomial]; simp

end

end LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
