/-
P0022, Kaniecki 1995, Lemma 5, p. 369: the input `Parseval1920` reduced to a strictly smaller
named input `Parseval18BC`. Session MANUAL-N1, unit U-7152, T1.

`Parseval1920` packs four steps of p. 369: the explicit formula (18) with Parseval, in the
variable `τ` with `t` over all of `ℝ` and factor `1/(2π)`; the substitution `e^τ = y`; the fold
of `∫_{-∞}^{∞}` to `2 ∫_0^∞` by the symmetry `t ↦ -t`; and identity (20), `g = B + C`.
This file PROVES the substitution and the fold, so `Parseval1920` follows from
`Parseval18BC`: the paper's display after "Thus by the Parseval theorem", in `τ` and over all
`t ∈ ℝ`, with `g` already written as `B + C` of (20). Identity (20) and the explicit formula
with Parseval stay inside `Parseval18BC`, CITED, the paper's reference [12], under RH.
The left side uses `θ` where the paper's display uses `θ₀`; they differ only at the jumps of
`θ`, a null set, so the integral is the same; the paper makes the same change for (19).

Main results: `parseval1920_of_18BC`, `lemma5_of_18BC`.
AI wrote this Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Kaniecki1995.Lemma5Red

namespace LeanLab.Kaniecki1995.U7152

open LeanLab.Kaniecki1995 LeanLab.Kaniecki1995.L5 Real MeasureTheory Set
open scoped ArithmeticFunction.vonMangoldt LSeries.notation ENNReal ComplexConjugate

/-- `((θ(e^{δ+τ}) - θ(e^τ) - e^τ/T)/e^{στ})²` with `e^δ = 1 + 1/T`, so `e^{δ+τ} = e^τ + e^τ/T`;
the integrand of the left side of the Parseval display, p. 369. -/
noncomputable def tauIntegrand (T σ τ : ℝ) : ℝ :=
  ((Chebyshev.theta (Real.exp τ + Real.exp τ / T) - Chebyshev.theta (Real.exp τ) -
    Real.exp τ / T) / Real.exp (σ * τ)) ^ 2

/-- The Parseval display of p. 369 in `τ` over all `t ∈ ℝ`, with `g = B + C` by (20):
under RH, for `T > 7.02`, `1/2 < σ ≤ 3/4`,
`∫_0^∞ ((θ(e^{δ+τ}) - θ(e^τ) - e^τ/T)/e^{στ})² dτ
   ≤ (1/2π) ∫_{-∞}^{∞} |(e^{δ(σ+it)} - 1)/(σ+it)|² |ζ'/ζ + B + C|² dt`.
CITED, the paper's reference [12] for (18), Parseval's theorem, and identity (20). -/
def Parseval18BC : Prop :=
  RiemannHypothesis → ∀ T σ : ℝ, 7.02 < T → 1 / 2 < σ → σ ≤ 3 / 4 →
    ∫⁻ τ in Ioi (0 : ℝ), ENNReal.ofReal (tauIntegrand T σ τ) ≤
      ENNReal.ofReal (1 / (2 * π)) *
        ∫⁻ t, ENNReal.ofReal (kern T σ t *
          ‖logDerivZeta (sAt σ t) + dirB σ t + primeC σ t‖ ^ 2)

/-! ### The substitution `y = e^τ`, PROVED -/

theorem thetaIntegrand_exp (T σ τ : ℝ) :
    Real.exp τ * thetaIntegrand T σ (Real.exp τ) = tauIntegrand T σ τ := by
  unfold thetaIntegrand tauIntegrand
  set N := Chebyshev.theta (Real.exp τ + Real.exp τ / T) - Chebyshev.theta (Real.exp τ) -
    Real.exp τ / T
  rw [← Real.exp_mul, div_pow, div_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  have h1 : Real.exp (↑(2 : ℕ) * (τ * (1 / 2 + σ))) = Real.exp τ * Real.exp (↑(2 : ℕ) * (σ * τ)) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  rw [h1]
  have h2 : 0 < Real.exp τ := Real.exp_pos τ
  have h3 : 0 < Real.exp (↑(2 : ℕ) * (σ * τ)) := Real.exp_pos _
  field_simp

/-- `I = ∫_1^∞ … dy = ∫_0^∞ … dτ`, the substitution `e^τ = y` of p. 369. -/
theorem IInt_eq_tau (T σ : ℝ) :
    IInt T σ = ∫⁻ τ in Ioi (0 : ℝ), ENNReal.ofReal (tauIntegrand T σ τ) := by
  unfold IInt
  have himg : Real.exp '' Ioi (0 : ℝ) = Ioi 1 := by rw [Real.image_exp_Ioi, Real.exp_zero]
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun τ _ => ?_)
  rw [abs_of_pos (Real.exp_pos τ), ← ENNReal.ofReal_mul (Real.exp_pos τ).le,
    thetaIntegrand_exp]

/-! ### The symmetry `t ↦ -t`, PROVED -/

theorem sAt_neg (σ t : ℝ) : sAt σ (-t) = conj (sAt σ t) := by
  simp [sAt]

theorem kern_neg (T σ t : ℝ) : kern T σ (-t) = kern T σ t := by
  unfold kern
  have : ((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) = conj ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    simp
  rw [this]
  congr 1
  have h : (Complex.exp ((Real.log (1 + 1 / T) : ℂ) * conj ((σ : ℂ) + (t : ℂ) * Complex.I)) - 1) /
      conj ((σ : ℂ) + (t : ℂ) * Complex.I) =
      conj ((Complex.exp ((Real.log (1 + 1 / T) : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I)) - 1) /
        ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    rw [map_div₀, map_sub, map_one, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  rw [h, Complex.norm_conj]

theorem natCast_cpow_conj (n : ℕ) (s : ℂ) : (n : ℂ) ^ conj s = conj ((n : ℂ) ^ s) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · by_cases hs : s = 0
    · subst hs; simp
    · have : conj s ≠ 0 := by simpa using hs
      simp [Complex.zero_cpow hs, Complex.zero_cpow this]
  · have harg : (n : ℂ).arg ≠ π := by
      rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
    rw [Complex.cpow_conj _ _ harg, Complex.conj_natCast]

theorem deriv_zeta_conj (s : ℂ) : deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  have hf : riemannZeta = (starRingEnd ℂ) ∘ riemannZeta ∘ (starRingEnd ℂ) := by
    funext z; simp [riemannZeta_conj]
  have := congrFun (deriv_conj_conj (f := riemannZeta)) (conj s)
  rw [← hf] at this
  simpa using this

theorem logDerivZeta_conj (s : ℂ) : logDerivZeta (conj s) = conj (logDerivZeta s) := by
  unfold logDerivZeta
  rw [deriv_zeta_conj, riemannZeta_conj, map_div₀]

theorem LSeries_vonMangoldt_conj (s : ℂ) : LSeries ↗Λ (conj s) = conj (LSeries ↗Λ s) := by
  unfold LSeries
  rw [Complex.conj_tsum]
  congr 1
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', map_div₀,
      natCast_cpow_conj, Complex.conj_ofReal]

theorem dirB_neg (σ t : ℝ) : dirB σ (-t) = conj (dirB σ t) := by
  unfold dirB
  rw [sAt_neg, ← LSeries_vonMangoldt_conj, map_mul, map_ofNat]

theorem primeTerm_conj (s : ℂ) (n : ℕ) : primeTerm (conj s) n = conj (primeTerm s n) := by
  unfold primeTerm
  split_ifs
  · have h2 : (2 : ℂ) * conj s = conj (2 * s) := by rw [map_mul, map_ofNat]
    rw [h2, natCast_cpow_conj, natCast_cpow_conj, map_div₀, map_mul, map_sub, map_one,
      Complex.conj_ofReal]
  · simp

theorem primeC_neg (σ t : ℝ) : primeC σ (-t) = conj (primeC σ t) := by
  unfold primeC
  rw [Complex.conj_tsum, sAt_neg]
  congr 1
  funext n
  exact primeTerm_conj _ n

theorem norm_F_neg (σ t : ℝ) :
    ‖logDerivZeta (sAt σ (-t)) + dirB σ (-t) + primeC σ (-t)‖ =
      ‖logDerivZeta (sAt σ t) + dirB σ t + primeC σ t‖ := by
  rw [dirB_neg, primeC_neg, sAt_neg, logDerivZeta_conj, ← map_add, ← map_add,
    Complex.norm_conj]

/-- An even function: `∫_ℝ f = 2 ∫_0^∞ f`. -/
theorem lintegral_even {f : ℝ → ℝ≥0∞} (hf : ∀ t, f (-t) = f t) :
    ∫⁻ t, f t = 2 * ∫⁻ t in Ioi (0 : ℝ), f t := by
  have hneg : ∫⁻ t in Iio (0 : ℝ), f t = ∫⁻ t in Ioi (0 : ℝ), f t := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.neg ℝ).measurableEmbedding f (Ioi 0)
    have hpre' : (Neg.neg : ℝ → ℝ) ⁻¹' Ioi 0 = Iio 0 := by ext x; simp
    rw [hpre'] at h
    simp only [hf] at h
    exact h
  have h0 : ∫⁻ t in ({0} : Set ℝ), f t = 0 := setLIntegral_measure_zero _ _ (by simp)
  have hsplit := lintegral_add_compl (μ := volume) f (measurableSet_singleton (0 : ℝ))
  have hc : ({0} : Set ℝ)ᶜ = Iio 0 ∪ Ioi 0 := by
    ext x
    simp only [mem_compl_iff, mem_singleton_iff, mem_union, mem_Iio, mem_Ioi]
    exact ne_iff_lt_or_gt
  rw [h0, zero_add, hc, lintegral_union measurableSet_Ioi (Set.disjoint_left.2 fun x hx hy =>
    lt_asymm (Set.mem_Iio.1 hx) (Set.mem_Ioi.1 hy)), hneg] at hsplit
  rw [← hsplit, two_mul]

/-- `(1/2π) ∫_ℝ k |ζ'/ζ + B + C|² = (1/π) ∫_0^∞ k |ζ'/ζ + B + C|²`. -/
theorem fold_eq (T σ : ℝ) :
    ENNReal.ofReal (1 / (2 * π)) *
        ∫⁻ t, ENNReal.ofReal (kern T σ t *
          ‖logDerivZeta (sAt σ t) + dirB σ t + primeC σ t‖ ^ 2) =
      ENNReal.ofReal (1 / π) *
        wInt T σ (fun t => logDerivZeta (sAt σ t) + dirB σ t + primeC σ t) := by
  unfold wInt
  rw [lintegral_even (fun t => by rw [kern_neg, norm_F_neg]), ← mul_assoc]
  congr 1
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-! ### Main results -/

/-- **`Parseval1920` from `Parseval18BC`.** PROVED: the substitution and the fold. -/
theorem parseval1920_of_18BC (hP : Parseval18BC) : Parseval1920 := by
  intro hRH T σ hT hσ hσ'
  rw [IInt_eq_tau, ← fold_eq]
  exact hP hRH T σ hT hσ hσ'

/-- The converse: the two inputs are equivalent, so the reduction loses nothing. -/
theorem parseval18BC_of_1920 (hP : Parseval1920) : Parseval18BC := by
  intro hRH T σ hT hσ hσ'
  rw [← IInt_eq_tau, fold_eq]
  exact hP hRH T σ hT hσ hσ'

/-- **Lemma 5**, CONDITIONAL ON `Lemma4`, `Parseval18BC`, `Bound21`, `Bound22`. -/
theorem lemma5_of_18BC (h4 : Lemma4) (hP : Parseval18BC) (h21 : Bound21) (h22 : Bound22) :
    Lemma5 :=
  lemma5_of h4 (parseval1920_of_18BC hP) h21 h22

end LeanLab.Kaniecki1995.U7152

#print axioms LeanLab.Kaniecki1995.U7152.IInt_eq_tau
#print axioms LeanLab.Kaniecki1995.U7152.fold_eq
#print axioms LeanLab.Kaniecki1995.U7152.parseval1920_of_18BC
#print axioms LeanLab.Kaniecki1995.U7152.parseval18BC_of_1920
#print axioms LeanLab.Kaniecki1995.U7152.lemma5_of_18BC
