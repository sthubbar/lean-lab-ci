import LeanLab.LanguascoPerelli1996.Primitive422
import LeanLab.LanguascoPerelli1996.Thm3I2
import LeanLab.LanguascoPerelli1996.Lemma2Full318
import LeanLab.LanguascoPerelli1996.Lemma1Full108

/-!
P0071 pages 355 through 359, displays 14 through 24.
Keep the actual Gauss weighted zero sums throughout the reduction.
The larger truncation height X squared stays in the range of estimate 3.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Decomp545a
open Real Filter MeasureTheory intervalIntegral
open scoped Classical

/-- Derived scalar input for page 358 estimate 3.
A fixed positive power absorbs the logarithm at large X. -/
theorem eventually_log_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, Real.log X ≤ X ^ ε := by
  filter_upwards [(isLittleO_log_rpow_atTop hε).bound (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop (0 : ℝ)] with X hX hX0
  simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hX0 _)] using
    (le_abs_self (Real.log X)).trans hX

/-- Derived scalar input for the modulus range in page 350 estimate 3.
The third power of log is at most the square root for large X. -/
theorem eventually_log_cube_le_sqrt :
    ∀ᶠ X : ℝ in atTop, Real.log X ^ 3 ≤ X ^ (1 / 2 : ℝ) := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop 3 (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1), eventually_ge_atTop (1 : ℝ)] with X hX hX1
  have hX0 : 0 ≤ X := by linarith
  have hl : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hh : |Real.log X ^ 3| ≤ X ^ (1 / 2 : ℝ) := by
    simpa only [Real.norm_eq_abs, one_mul, Real.rpow_ofNat,
      abs_of_nonneg (Real.rpow_nonneg hX0 _)] using hX
  exact (le_abs_self _).trans hh

/-- Derived modulus inclusion needed to use estimate 3 above the GMC range.
The full allowed q range is retained. -/
theorem modulus_in_estimate3_range {X θ : ℝ} (hX : 1 < X) (hθ : θ ≤ 1 / 2)
    (hlog : Real.log X ^ 3 ≤ X ^ (1 / 2 : ℝ)) {q : ℕ}
    (hq : (q : ℝ) ≤ X ^ θ) :
    (q : ℝ) ≤ X / Real.log X ^ 3 := by
  have hl : 0 < Real.log X ^ 3 := pow_pos (Real.log_pos hX) _
  apply (le_div_iff₀ hl).2
  have hroot : X ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) = X := by
    rw [← Real.rpow_add (by linarith : 0 < X)]
    norm_num
  have hqr : (q : ℝ) ≤ X ^ (1 / 2 : ℝ) := hq.trans (Real.rpow_le_rpow_of_exponent_le hX.le hθ)
  nlinarith [mul_le_mul hqr hlog (pow_nonneg (Real.log_nonneg hX.le) _) (Real.rpow_nonneg (by linarith) _)]

/-- Page 358, combine GMCxi below X and estimate 3 above X.
The conclusion is a bound on the same actual F, not individual characters.
CONDITIONAL ON estimate 3. -/
theorem correlation_envelope {θ : ℝ} (hθ : θ ≤ 1 / 2)
    {ξ : ℝ → ℕ → ℝ} (hG : GMCxi θ ξ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C X0 : ℝ, 0 ≤ C ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X ^ θ →
        ∀ a : ℕ, Nat.Coprime a q → ∀ T : ℝ,
          X * ξ X q / 2 ≤ T → T ≤ X ^ 2 →
            ‖F X T q a‖ ≤ C * (q : ℝ) ^ 2 * T * X ^ ε := by
  obtain ⟨C, X1, h1⟩ := hG.2.2 ε hε
  obtain ⟨D, X2, h2⟩ := estimate3 hG.1 2 (by norm_num)
  obtain ⟨X3, h3⟩ := eventually_atTop.1 (eventually_log_le_rpow hε)
  obtain ⟨X4, h4⟩ := eventually_atTop.1 eventually_log_cube_le_sqrt
  refine ⟨max 0 C + max 0 D, max 2 (max X1 (max X2 (max X3 X4))), by positivity,
    le_max_left _ _, ?_⟩
  intro X hX q inst hq a ha T hWT hTK
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hX1 : 1 < X := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hx1 : X1 ≤ X := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hX
  have hx2 : X2 ≤ X := (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hX
  have hx3 : X3 ≤ X := (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) (le_max_right _ _)).trans hX
  have hx4 : X4 ≤ X := (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) (le_max_right _ _)).trans hX
  have hξ := (hG.2.1 X q).1
  have hT : 0 ≤ T := le_trans (by positivity : 0 ≤ X * ξ X q / 2) hWT
  have hr : 0 ≤ X ^ ε := Real.rpow_nonneg (by linarith) _
  have hC : C ≤ max 0 C + max 0 D := by nlinarith [le_max_right 0 C, le_max_left 0 D]
  have hD : D ≤ max 0 C + max 0 D := by nlinarith [le_max_left 0 C, le_max_right 0 D]
  by_cases hTX : T ≤ X
  · exact (h1 X hx1 q hq a ha T hWT hTX).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC (sq_nonneg _)) hT) hr)
  · have hb := h2 X hx2 T (le_of_not_ge hTX) (by simpa only [Real.rpow_two] using hTK)
      q (modulus_in_estimate3_range hX1 hθ (h4 X hx4) hq) a ha
    have hD0 : 0 ≤ max 0 D := le_max_left _ _
    calc
      ‖F X T q a‖ ≤ D * (q : ℝ) ^ 2 * T * Real.log X := hb
      _ ≤ max 0 D * (q : ℝ) ^ 2 * T * Real.log X :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right 0 D) (sq_nonneg _)) hT)
          (Real.log_nonneg hX1.le)
      _ ≤ max 0 D * (q : ℝ) ^ 2 * T * X ^ ε :=
        mul_le_mul_of_nonneg_left (h3 X hx3) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by nlinarith [le_max_left 0 C] : max 0 D ≤ max 0 C + max 0 D)
          (sq_nonneg _)) hT) hr

/-- Derived normalization identity before page 355 display 14.
Euler's exact product formula retains the full totient denominator. -/
theorem totient_ratio_eq_product {q : ℕ} (hq : 0 < q) :
    (q : ℝ) / q.totient = ∏ p ∈ q.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hp : ∀ p ∈ q.primeFactors, 0 < (p : ℝ) - 1 := by
    intro p hp
    have hh := (Nat.prime_of_mem_primeFactors hp).two_le
    have hh' : (2 : ℝ) ≤ p := by exact_mod_cast hh
    linarith
  have hprod : (0 : ℝ) < ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := Finset.prod_pos hp
  have hh := congrArg (fun n : ℕ => (n : ℝ)) (Nat.totient_mul_prod_primeFactors q)
  push_cast at hh
  have hc : (∏ p ∈ q.primeFactors, ((p - 1 : ℕ) : ℝ)) =
      ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]
  rw [hc] at hh
  rw [Finset.prod_div_distrib]
  apply (div_eq_div_iff hφ.ne' hprod.ne').2
  nlinarith [hh]

/-- Derived elementary normalization bound for displays 14 and 23.
For every positive epsilon the ratio q over phi of q is at most a
constant times q to epsilon. No analytic number theory is assumed. -/
theorem totient_ratio_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, 0 < q → (q : ℝ) / q.totient ≤ C * (q : ℝ) ^ ε := by
  classical
  let P : ℕ := ⌈(2 : ℝ) ^ (1 / ε)⌉₊
  refine ⟨(2 : ℝ) ^ P, by positivity, ?_⟩
  intro q hq
  have hp2 : ∀ p ∈ q.primeFactors, (2 : ℝ) ≤ p := by
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hpoint : ∀ p ∈ q.primeFactors,
      (p : ℝ) / ((p : ℝ) - 1) ≤ (if p < P then 2 else 1) * (p : ℝ) ^ ε := by
    intro p hp
    have hp' := hp2 p hp
    have hp0 : 0 < (p : ℝ) - 1 := by linarith
    have hratio : (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := (div_le_iff₀ hp0).2 (by linarith)
    have hpow1 : 1 ≤ (p : ℝ) ^ ε := Real.one_le_rpow (by linarith) hε.le
    by_cases hsmall : p < P
    · simp only [ite_eq_left hsmall]
      nlinarith
    · have hbase : (2 : ℝ) ^ (1 / ε) ≤ p :=
        (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_of_not_gt hsmall)
      have hpow2 : 2 ≤ (p : ℝ) ^ ε := by
        calc
          (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
            rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
            simp [ne_of_gt hε]
          _ ≤ _ := Real.rpow_le_rpow (by positivity) hbase hε.le
      simpa only [ite_eq_right hsmall, one_mul] using hratio.trans hpow2
  have hcount : (q.primeFactors.filter (fun p => p < P)).card ≤ P := by
    have hs : q.primeFactors.filter (fun p => p < P) ⊆ Finset.range P := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    simpa using Finset.card_le_card hs
  have hb : (∏ p ∈ q.primeFactors, (if p < P then (2 : ℝ) else 1)) ≤ (2 : ℝ) ^ P := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, mul_one, Finset.prod_const]
    exact pow_le_pow_right₀ (by norm_num) hcount
  have hrad : (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ q := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  rw [totient_ratio_eq_product hq]
  calc
    _ ≤ ∏ p ∈ q.primeFactors, (if p < P then 2 else 1) * (p : ℝ) ^ ε :=
      Finset.prod_le_prod₀ (fun p hp => div_nonneg (Nat.cast_nonneg p)
        (by have hh := hp2 p hp; linarith)) hpoint
    _ = (∏ p ∈ q.primeFactors, (if p < P then (2 : ℝ) else 1)) *
        (∏ p ∈ q.primeFactors, (p : ℝ) ^ ε) := Finset.prod_mul_distrib
    _ ≤ (2 : ℝ) ^ P * (q : ℝ) ^ ε := by
      apply mul_le_mul hb
      · rw [Real.finsetProd_rpow _ _ (fun p hp => Nat.cast_nonneg p)]
        exact Real.rpow_le_rpow (by positivity) hrad hε.le
      · positivity
      · positivity

/-- Page 355 before display 14, the actual original character polynomial. -/
noncomputable def originalPolynomial (X Y η : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊,
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) * e ((n : ℝ) * η)

/-- Page 355 before display 14, the actual inducing primitive polynomial. -/
noncomputable def primitivePolynomial (X Y η : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊,
    (ArithmeticFunction.vonMangoldt n : ℂ) *
      χ.primitiveCharacter (n : ZMod χ.conductor) * e ((n : ℝ) * η)

/-- Derived exact correction before display 14.
This retains the full Gauss weighted primitive replacement error.
It is not bounded by the individual character comparison. -/
noncomputable def primitiveCorrection (X Y η : ℝ) (q : ℕ) [NeZero q] (a : ℕ) : ℂ :=
  (∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * tau χ⁻¹ *
    (originalPolynomial X Y η χ - primitivePolynomial X Y η χ)) / (q.totient : ℂ)

/-- Page 355 before display 14, retain the primitive correction exactly
while applying the already proved bad prime error. No cancellation estimate
is inferred from the individual primitive character bound. -/
theorem stopped_primitive_reduction {q : ℕ} [NeZero q] (a : ℕ)
    (ha : Nat.Coprime a q) (X Y η : ℝ) :
    ‖Decomp381a.partialR X Y η q a -
      (((∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * tau χ⁻¹ *
          primitivePolynomial X Y η χ) / (q.totient : ℂ) -
        (muPhi q : ℂ) * (∑ n ∈ Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊, e ((n : ℝ) * η))) +
        primitiveCorrection X Y η q a)‖ ≤ Real.log ⌊Y⌋₊ * Real.log q / Real.log 2 := by
  have hs : (∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * tau χ⁻¹ *
      originalPolynomial X Y η χ) =
      (∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * tau χ⁻¹ *
        primitivePolynomial X Y η χ) +
      (∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * tau χ⁻¹ *
        (originalPolynomial X Y η χ - primitivePolynomial X Y η χ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro χ hχ
    ring
  have he :
      (((∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * tau χ⁻¹ *
          primitivePolynomial X Y η χ) / (q.totient : ℂ) -
        (muPhi q : ℂ) * (∑ n ∈ Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊, e ((n : ℝ) * η))) +
        primitiveCorrection X Y η q a) =
      (∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * tau χ⁻¹ *
        originalPolynomial X Y η χ) / (q.totient : ℂ) -
        (muPhi q : ℂ) * (∑ n ∈ Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊, e ((n : ℝ) * η)) := by
    rw [hs]
    unfold primitiveCorrection
    ring
  rw [he]
  exact BadPrimes422.stopped_character_error a ha X Y η

/-- Page 355 before display 14, the original exact character expansion
with the actual primitive correction displayed rather than suppressed. -/
theorem stopped_primitive_expansion {q : ℕ} [NeZero q] (a : ℕ)
    (ha : Nat.Coprime a q) (X Y η : ℝ) :
    (q.totient : ℂ) * Decomp381a.partialR X Y η q a =
      (∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * tau χ⁻¹ * primitivePolynomial X Y η χ) +
      (q.totient : ℂ) * primitiveCorrection X Y η q a -
      (q.totient : ℂ) * (muPhi q : ℂ) *
        (∑ n ∈ Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊, e ((n : ℝ) * η)) +
      (q.totient : ℂ) *
        ∑ n ∈ (Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊).filter (fun n => ¬ Nat.Coprime n q),
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            e ((n : ℝ) * ((a : ℝ) / q)) * e ((n : ℝ) * η) := by
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have hh := Character422.stopped_character_expansion a ha X Y η
  have hc (z : ℂ) : (q.totient : ℂ) * (z / (q.totient : ℂ)) = z := by
    field_simp [hφ]
  unfold primitiveCorrection
  rw [hc]
  rw [← Finset.sum_add_distrib]
  convert hh using 1
  congr 2
  apply Finset.sum_congr rfl
  intro χ hχ
  unfold originalPolynomial
  ring

/-- Derived local comparison accompanying the exact correction above.
This reuses Primitive422 and bounds each character separately.
It makes no assertion about the norm of primitiveCorrection. -/
theorem individual_primitive_error {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (X Y η : ℝ) :
    ‖originalPolynomial X Y η χ - primitivePolynomial X Y η χ‖ ≤
      Real.log ⌊Y⌋₊ * Real.log q / Real.log 2 := by
  exact Primitive422.primitive_polynomial_difference χ _ ⌊Y⌋₊ η
    (fun n hn => (Finset.mem_Icc.mp hn).2)

/-- Page 356 displays 15 and 16, the primitive of the actual zero band.
The zeros and multiplicities are the sealed L function zeros. -/
noncomputable def zeroPrimitive (x U T : ℝ) (q : ℕ) [NeZero q] (a : ℕ) : ℂ :=
  ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * tau χ⁻¹ *
    ∑ᶠ ρ ∈ ntZeros χ T \ {ρ | |ρ.im| ≤ U},
      (mult χ ρ : ℂ) * Complex.exp (ρ * (Real.log x : ℂ)) / ρ

/-- Derived endpoint rounding for display 21.
The lower argument excludes exactly the integers below ceil of X over four. -/
noncomputable def lowerEndpoint (X : ℝ) : ℝ := (⌈X / 4⌉₊ : ℝ) - 1

/-- Derived clipped endpoint for the sharp stopped windows in display 23.
Both endpoints of the original finite polynomial remain present. -/
noncomputable def clippedEndpoint (X Y t : ℝ) : ℝ :=
  max (lowerEndpoint X) (min (⌊Y⌋₊ : ℝ) t)

/-- Pages 356 and 357, a zero window with both stopped endpoints retained.
The variable t ranges over a real unit cell of a discrete Gallagher window. -/
noncomputable def zeroWindow (X Y : ℝ) (q : ℕ) [NeZero q] (a L : ℕ)
    (U T t : ℝ) : ℂ :=
  zeroPrimitive (clippedEndpoint X Y t) U T q a -
    zeroPrimitive (clippedEndpoint X Y (t - L)) U T q a

/-- Derived integer regions of displays 14 and 23.
Indices zero, one and two are the leading, interior and trailing regions. -/
noncomputable def cells (X Y : ℝ) (L : ℕ) (r : Fin 3) : Finset ℕ :=
  (Finset.range (⌊Y⌋₊ + 1 + L)).filter (fun m =>
    if r = 0 then m < ⌊Y⌋₊ + 1 ∧ m < ⌈X / 4⌉₊ + L
    else if r = 1 then m < ⌊Y⌋₊ + 1 ∧ ⌈X / 4⌉₊ + L ≤ m
    else ⌊Y⌋₊ + 1 ≤ m)

/-- Derived arithmetic region mass for display 23.
This uses exactly the three regions already defined in Window422. -/
noncomputable def regionMass (X Y : ℝ) (q a L : ℕ) (r : Fin 3) : ℝ :=
  ∑ m ∈ cells X Y L r,
    ‖LeanLab.PNTPort.Gallagher.win (Window422.coeff X q a) (⌊Y⌋₊ + 1) L m‖ ^ 2

/-- Pages 356 and 357, the real zero mass over the exact unit cells.
It has a genuine integral, not values sampled at integer endpoints. -/
noncomputable def zeroMass (X Y : ℝ) (q : ℕ) [NeZero q] (a L : ℕ)
    (r : Fin 3) (U T : ℝ) : ℝ :=
  ∑ m ∈ cells X Y L r, ∫ t in (m : ℝ)..(m + 1 : ℝ),
    ‖zeroWindow X Y q a L U T t‖ ^ 2

/-- Derived identification with the sealed leading region in display 23. -/
theorem regionMass_leading (X Y : ℝ) (q a L : ℕ) :
    regionMass X Y q a L 0 = Window422.leadingMass X Y q a L := by
  simp only [regionMass, cells, Window422.leadingMass, ite_true]

/-- Derived identification with the sealed interior region in display 23. -/
theorem regionMass_interior (X Y : ℝ) (q a L : ℕ) :
    regionMass X Y q a L 1 = Window422.interiorMass X Y q a L := by
  simp only [regionMass, cells, Window422.interiorMass,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, ite_true]

/-- Derived identification with the sealed trailing region in display 23. -/
theorem regionMass_trailing (X Y : ℝ) (q a L : ℕ) :
    regionMass X Y q a L 2 = Window422.trailingMass X Y q a L := by
  simp only [regionMass, cells, Window422.trailingMass,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ite_false]

/-- Derived concrete zero band instance for displays 15 through 19.
Equal height endpoints give the empty band for every character. -/
theorem zeroPrimitive_same (x T : ℝ) (q : ℕ) [NeZero q] (a : ℕ) :
    zeroPrimitive x T T q a = 0 := by
  have hs (χ : DirichletCharacter ℂ q) : ntZeros χ T \ {ρ | |ρ.im| ≤ T} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ρ hρ
    exact hρ.2 hρ.1.2.2.2
  simp only [zeroPrimitive, hs, finsum_mem_empty, mul_zero, Finset.sum_const_zero]

/-- Derived concrete zero mass instance for displays 15 through 19.
Every region mass of an empty zero band is zero. -/
theorem zeroMass_same (X Y : ℝ) (q : ℕ) [NeZero q] (a L : ℕ) (r : Fin 3) (T : ℝ) :
    zeroMass X Y q a L r T T = 0 := by
  simp [zeroMass, zeroWindow, zeroPrimitive_same, intervalIntegral.integral_zero]

/-- Page 356, split the actual primitive at height W.
No coefficient norm bound replaces the Gauss weighted character sum. -/
theorem zeroPrimitive_split (x W K : ℝ) (hWK : W ≤ K)
    (q : ℕ) [NeZero q] (a : ℕ) :
    zeroPrimitive x (-1) K q a =
      zeroPrimitive x (-1) W q a + zeroPrimitive x W K q a := by
  classical
  have hneg : {ρ : ℂ | |ρ.im| ≤ (-1 : ℝ)} = ∅ := by
    ext ρ
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    linarith [abs_nonneg ρ.im]
  unfold zeroPrimitive
  simp only [hneg, Set.sdiff_empty]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [← mul_add]
  congr 1
  have hinter : ntZeros χ K ∩ {ρ | |ρ.im| ≤ W} = ntZeros χ W := by
    ext ρ
    simp only [ntZeros, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h0, h1, h2, _⟩, hW⟩
      exact ⟨h0, h1, h2, hW⟩
    · rintro ⟨h0, h1, h2, hW⟩
      exact ⟨⟨h0, h1, h2, hW.trans hWK⟩, hW⟩
  have hh := finsum_mem_inter_add_sdiff
    (f := fun ρ : ℂ => (mult χ ρ : ℂ) * Complex.exp (ρ * (Real.log x : ℂ)) / ρ)
    {ρ | |ρ.im| ≤ W} (Zeros108.ntZeros_finite χ K)
  rw [hinter] at hh
  exact hh.symm

/-- Page 356, the same split with both window endpoints retained. -/
theorem zeroWindow_split (X Y : ℝ) (q : ℕ) [NeZero q] (a L : ℕ)
    (W K t : ℝ) (hWK : W ≤ K) :
    zeroWindow X Y q a L (-1) K t =
      zeroWindow X Y q a L (-1) W t + zeroWindow X Y q a L W K t := by
  unfold zeroWindow
  rw [zeroPrimitive_split _ W K hWK, zeroPrimitive_split _ W K hWK]
  ring

/-- Page 356, the zero primitive is continuous on positive arguments.
Finiteness of all bounded zero sets was already proved in Zeros108. -/
theorem continuous_zeroPrimitive_comp {f : ℝ → ℝ} (hf : Continuous f)
    (hpos : ∀ t, 0 < f t) (U T : ℝ) (q : ℕ) [NeZero q] (a : ℕ) :
    Continuous (fun t => zeroPrimitive (f t) U T q a) := by
  classical
  have hlog := hf.log (fun t => (hpos t).ne')
  unfold zeroPrimitive
  simp_rw [finsum_mem_eq_finite_toFinset_sum _
    ((Zeros108.ntZeros_finite _ T).sdiff (t := {ρ : ℂ | |ρ.im| ≤ U}))]
  fun_prop

/-- Derived positivity of the rounded lower endpoint in display 21. -/
theorem lowerEndpoint_pos {X : ℝ} (hX : 8 ≤ X) : 0 < lowerEndpoint X := by
  have hh := Nat.le_ceil (X / 4)
  unfold lowerEndpoint
  linarith

/-- Page 356, the clipped zero window is continuous.
The positive clamp also covers unit cells before the support begins. -/
theorem continuous_zeroWindow {X : ℝ} (hX : 8 ≤ X) (Y : ℝ)
    (q : ℕ) [NeZero q] (a L : ℕ) (U T : ℝ) :
    Continuous (zeroWindow X Y q a L U T) := by
  have hc : Continuous (fun t : ℝ => clippedEndpoint X Y t) := by
    unfold clippedEndpoint
    fun_prop
  have hp : ∀ t : ℝ, 0 < clippedEndpoint X Y t := fun t =>
    (lowerEndpoint_pos hX).trans_le (le_max_left _ _)
  have hc' : Continuous (fun t : ℝ => clippedEndpoint X Y (t - L)) := hc.comp (by fun_prop)
  exact (continuous_zeroPrimitive_comp hc hp U T q a).sub
    (continuous_zeroPrimitive_comp hc' (fun t => hp (t - L)) U T q a)

/-- Page 356, the low and high bands bound the full zero mass.
This is just the squared norm inequality under each actual cell integral. -/
theorem zeroMass_split {X : ℝ} (hX : 8 ≤ X) (Y : ℝ)
    (q : ℕ) [NeZero q] (a L : ℕ) (r : Fin 3) (W K : ℝ) (hWK : W ≤ K) :
    zeroMass X Y q a L r (-1) K ≤
      2 * (zeroMass X Y q a L r (-1) W + zeroMass X Y q a L r W K) := by
  unfold zeroMass
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  have hc (U T : ℝ) : IntervalIntegrable (fun t : ℝ => ‖zeroWindow X Y q a L U T t‖ ^ 2)
      volume (m : ℝ) (m + 1 : ℝ) :=
    ((continuous_zeroWindow hX Y q a L U T).norm.pow 2).intervalIntegrable _ _
  calc
    _ ≤ ∫ t in (m : ℝ)..(m + 1 : ℝ),
        2 * (‖zeroWindow X Y q a L (-1) W t‖ ^ 2 + ‖zeroWindow X Y q a L W K t‖ ^ 2) := by
      apply integral_mono_on (by linarith) (hc _ _)
        (((continuous_zeroWindow hX Y q a L (-1) W).norm.pow 2 |>.add
          ((continuous_zeroWindow hX Y q a L W K).norm.pow 2)).const_mul 2 |>.intervalIntegrable _ _)
      intro t ht
      change ‖zeroWindow X Y q a L (-1) K t‖ ^ 2 ≤
        2 * (‖zeroWindow X Y q a L (-1) W t‖ ^ 2 + ‖zeroWindow X Y q a L W K t‖ ^ 2)
      rw [zeroWindow_split X Y q a L W K t hWK]
      have hh := norm_add_le (zeroWindow X Y q a L (-1) W t) (zeroWindow X Y q a L W K t)
      nlinarith [sq_nonneg (‖zeroWindow X Y q a L (-1) W t‖ - ‖zeroWindow X Y q a L W K t‖),
        pow_le_pow_left₀ (norm_nonneg _) hh 2]
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]
      exact congrArg (fun z : ℝ => 2 * z) (intervalIntegral.integral_add (hc (-1) W) (hc W K))

/-- Page 356 display 15, the actual correlation bracket. -/
noncomputable def correlationBracket (X W K : ℝ) (q : ℕ) [NeZero q] (a : ℕ) : ℝ :=
  (‖F X K q a‖ + ‖F X W q a‖) / K ^ 2 +
    ∫ u in W..K, (u ^ 3)⁻¹ * (‖F X u q a‖ + ‖F X W q a‖)

/-- Page 356 display 15, substitute a linear envelope for the actual F.
The integral estimate reuses the existing exact scalar computation. -/
theorem correlationBracket_le {X W K c : ℝ} (hW : 0 < W) (hWK : W ≤ K)
    (hc : 0 ≤ c) (q : ℕ) [NeZero q] (a : ℕ)
    (hF : ∀ u : ℝ, W ≤ u → u ≤ K → ‖F X u q a‖ ≤ c * u) :
    correlationBracket X W K q a ≤ 4 * c / W := by
  have hK : 0 < K := hW.trans_le hWK
  have hFW := hF W le_rfl hWK
  have hFK := hF K hWK le_rfl
  by_cases hEq : W = K
  · subst K
    simp only [correlationBracket, integral_same, add_zero]
    apply (div_le_iff₀ (sq_pos_of_pos hW)).2
    have hright : (4 * c / W) * W ^ 2 = 4 * c * W := by field_simp <;> ring
    rw [hright]
    nlinarith
  have hlt : W < K := lt_of_le_of_ne hWK hEq
  have hi : IntervalIntegrable (fun u : ℝ => (u ^ 3)⁻¹ * (c * u + c * W)) volume W K := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul
    · apply ContinuousOn.inv₀ (by fun_prop)
      intro u hu
      rw [Set.uIcc_of_le hWK] at hu
      exact pow_ne_zero _ (hW.trans_le hu.1).ne'
    · fun_prop
  have hmono : (∫ u in W..K, (u ^ 3)⁻¹ * (‖F X u q a‖ + ‖F X W q a‖)) ≤
      ∫ u in W..K, (u ^ 3)⁻¹ * (c * u + c * W) := by
    rw [integral_of_le hWK, integral_of_le hWK]
    have hnonneg : ∀ᵐ u : ℝ ∂(volume.restrict (Set.Ioc W K)),
        0 ≤ (u ^ 3)⁻¹ * (‖F X u q a‖ + ‖F X W q a‖) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (hW.le.trans hu.1.le) 3))
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
    have hmajor : ∀ᵐ u : ℝ ∂(volume.restrict (Set.Ioc W K)),
        (u ^ 3)⁻¹ * (‖F X u q a‖ + ‖F X W q a‖) ≤ (u ^ 3)⁻¹ * (c * u + c * W) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact mul_le_mul_of_nonneg_left (add_le_add (hF u hu.1.le hu.2) hFW)
        (inv_nonneg.mpr (pow_nonneg (hW.le.trans hu.1.le) 3))
    exact MeasureTheory.integral_mono_of_nonneg hnonneg hi.1 hmajor
  have hscalar := Thm3I2.bracket_integral hc (by linarith : 0 < W / 2)
    (by linarith : 2 * (W / 2) < K)
  have he : 2 * (W / 2) = W := by ring
  rw [he] at hscalar
  have hr : (7 / 4 : ℝ) * c / (W / 2) ≤ 4 * c / W := by
    have heq : (7 / 4 : ℝ) * c / (W / 2) = ((7 / 2 : ℝ) * c) / W := by
      field_simp [hW.ne'] <;> ring
    rw [heq]
    exact div_le_div_of_nonneg_right (by nlinarith : (7 / 2 : ℝ) * c ≤ 4 * c) hW.le
  unfold correlationBracket
  exact (add_le_add (div_le_div_of_nonneg_right (add_le_add hFK hFW) (sq_nonneg _)) hmono).trans
    (hscalar.trans hr)

/-- Derived cutoff for displays 15 through 19.
The cutoff one retains the small height range in the sealed statements. -/
noncomputable def lowHeight (X ξ : ℝ) : ℝ := max 1 (X * ξ / 2)

/-- Derived low band scale for display 16.
Long windows use the stopped support instead of an unbounded interval. -/
noncomputable def lowScale (X : ℝ) (L : ℕ) : ℝ := min ((L : ℝ) ^ 2) ((X + L) * X)

/-- Derived geometry for the GMCxi cutoff in page 358.
The cutoff lies inside the extended correlation envelope. -/
theorem lowHeight_range {X ξ : ℝ} (hX : 2 ≤ X) (hξ : 0 < ξ) (hξ2 : ξ ≤ 1 / 2) :
    1 ≤ lowHeight X ξ ∧ X * ξ / 2 ≤ lowHeight X ξ ∧ lowHeight X ξ ≤ X ∧
      lowHeight X ξ ≤ X ^ 2 := by
  have hX0 : 0 ≤ X := by linarith
  have hWX : lowHeight X ξ ≤ X := by
    unfold lowHeight
    apply max_le <;> nlinarith [mul_le_mul_of_nonneg_left hξ2 hX0]
  exact ⟨le_max_left _ _, le_max_right _ _, hWX, hWX.trans (by nlinarith)⟩

/-- Derived scalar absorption of the low band from display 16.
It applies to all positive window lengths, including lengths above X. -/
theorem lowScale_height_le {X ξ : ℝ} (hX : 2 ≤ X) {L : ℕ} (hL : 0 < L)
    (hlo : 1 / (4 * (L : ℝ)) ≤ ξ) (hhi : ξ ≤ 1 / (2 * (L : ℝ))) :
    lowScale X L * lowHeight X ξ ≤ 9 * L * X := by
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hX0 : 0 ≤ X := by linarith
  have hlo' := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * L)).1 hlo
  have hhi' := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L)).1 hhi
  by_cases hW : 1 ≤ X * ξ / 2
  · rw [lowHeight, max_eq_right hW]
    have hb := mul_le_mul_of_nonneg_right (min_le_left ((L : ℝ) ^ 2) ((X + L) * X))
      (by linarith : 0 ≤ X * ξ / 2)
    have hh := mul_le_mul_of_nonneg_left hhi' (by positivity : 0 ≤ (L : ℝ) * X)
    unfold lowScale
    nlinarith
  · have hWX : X ≤ 8 * L := by
      have hh := mul_le_mul_of_nonneg_left hlo' hX0
      have hh' := mul_le_mul_of_nonneg_left (le_of_not_ge hW) (by positivity : 0 ≤ 8 * (L : ℝ))
      nlinarith
    rw [lowHeight, max_eq_left (le_of_not_ge hW), mul_one]
    exact (min_le_right _ _).trans (by nlinarith)

/-- Derived scalar absorption of the high band from display 15. -/
theorem highScale_le {X ξ : ℝ} (hX : 2 ≤ X) {L : ℕ} (hL : 0 < L)
    (hlo : 1 / (4 * (L : ℝ)) ≤ ξ) :
    X ^ 2 / lowHeight X ξ ≤ 8 * L * X := by
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hW : 0 < lowHeight X ξ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hX0 : 0 ≤ X := by linarith
  have hlo' := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * L)).1 hlo
  apply (div_le_iff₀ hW).2
  have hh := mul_le_mul_of_nonneg_left (le_max_right 1 (X * ξ / 2)) (by positivity : 0 ≤ 8 * (L : ℝ) * X)
  have hh' := mul_le_mul_of_nonneg_left hlo' (sq_nonneg X)
  dsimp only [lowHeight] at *
  nlinarith

/-- Page 357 display 19, exact scalar integral followed by log absorption.
The lower height one prevents a spurious log of an arbitrarily small xi. -/
theorem endpoint_integral_sq_le {X W c : ℝ} (hX : 2 ≤ X) (hW : 1 ≤ W)
    (hWK : W ≤ X ^ 2) (hc : 0 ≤ c) :
    (∫ u in W..(X ^ 2), u ^ (-(3 : ℝ) / 2) * (c * u) ^ (1 / 2 : ℝ)) ^ 2 ≤
      4 * c * Real.log X ^ 2 := by
  have hW0 : 0 < W := by linarith
  have hX0 : 0 < X := by linarith
  rw [Thm3I2.J2_integral hc hW0 hWK, mul_pow]
  have hs : (c ^ (1 / 2 : ℝ)) ^ 2 = c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc]
    norm_num
  rw [hs]
  have hlog0 : 0 ≤ Real.log (X ^ 2 / W) := Real.log_nonneg ((le_div_iff₀ hW0).2 (by linarith))
  have hlog : Real.log (X ^ 2 / W) ≤ 2 * Real.log X := by
    rw [Real.log_div (sq_pos_of_pos hX0).ne' hW0.ne', Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [Real.log_nonneg hW]
  have hp := pow_le_pow_left₀ hlog0 hlog 2
  nlinarith [mul_le_mul_of_nonneg_left hp hc]

/-- Page 356, differentiation of one zero primitive on the positive axis.
The zero is nonzero because its real part lies in the open critical strip. -/
theorem zero_term_hasDerivAt {x : ℝ} (hx : 0 < x) (ρ : ℂ) (hρ : ρ ≠ 0) (m : ℂ) :
    HasDerivAt (fun t : ℝ => m * Complex.exp (ρ * (Real.log t : ℂ)) / ρ)
      (m * Complex.exp (ρ * (Real.log x : ℂ)) / (x : ℂ)) x := by
  have hh := ((((Real.hasDerivAt_log hx.ne').ofReal_comp.const_mul ρ).cexp).const_mul m).div_const ρ
  convert hh using 1
  push_cast
  field_simp [hρ, ne_of_gt hx] <;> ring

/-- Page 356 display 16, the zero primitive differentiates to the
unweighted band on GRH. The actual character cancellation is retained. -/
theorem zeroPrimitive_hasDerivAt (hG : GRH) {x : ℝ} (hx : 0 < x)
    (U T : ℝ) (q : ℕ) [NeZero q] (a : ℕ) :
    HasDerivAt (fun t : ℝ => zeroPrimitive t U T q a)
      (((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * zSum x U T q a) x := by
  classical
  have hp (χ : DirichletCharacter ℂ q) (ρ : ℂ) (hρ : ρ ∈ ntZeros χ T) :
      Complex.exp (ρ * (Real.log x : ℂ)) / (x : ℂ) =
        ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (ρ.im : ℂ) * (Real.log x : ℂ)) := by
    have hre := hG q χ ρ hρ.1 hρ.2.1 hρ.2.2.1
    have hrepr : ρ = (1 / 2 : ℂ) + Complex.I * (ρ.im : ℂ) := by
      apply Complex.ext <;> simp [hre]
    have hpow : ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = Complex.exp ((-(1 / 2 : ℂ)) * (Real.log x : ℂ)) := by
      rw [Real.rpow_def_of_pos hx, Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    have hxe : (x : ℂ) = Complex.exp (Real.log x : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log hx]
    rw [hxe, ← Complex.exp_sub, hpow, ← Complex.exp_add]
    congr 1
    nth_rw 1 [hrepr]
    ring
  have hs (χ : DirichletCharacter ℂ q) : HasDerivAt
      (fun t : ℝ => ∑ ρ ∈ ((Zeros108.ntZeros_finite χ T).sdiff
        (t := {ρ : ℂ | |ρ.im| ≤ U})).toFinset,
        (mult χ ρ : ℂ) * Complex.exp (ρ * (Real.log t : ℂ)) / ρ)
      (∑ ρ ∈ ((Zeros108.ntZeros_finite χ T).sdiff
        (t := {ρ : ℂ | |ρ.im| ≤ U})).toFinset,
        (mult χ ρ : ℂ) * Complex.exp (ρ * (Real.log x : ℂ)) / (x : ℂ)) x := by
    apply HasDerivAt.fun_sum
    intro ρ hρ
    have hm := ((Set.Finite.mem_toFinset _).mp hρ).1
    have hρ0 : ρ ≠ 0 := by
      intro hz
      have := hm.2.1
      simpa [hz] using this
    exact zero_term_hasDerivAt hx ρ hρ0 _
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun χ _ =>
    (hs χ).const_mul (χ (a : ZMod q) * tau χ⁻¹))
  have heq : (fun t : ℝ => zeroPrimitive t U T q a) =
      (fun t : ℝ => ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * tau χ⁻¹ *
        ∑ ρ ∈ ((Zeros108.ntZeros_finite χ T).sdiff
          (t := {ρ : ℂ | |ρ.im| ≤ U})).toFinset,
          (mult χ ρ : ℂ) * Complex.exp (ρ * (Real.log t : ℂ)) / ρ) := by
    funext t
    unfold zeroPrimitive
    congr 1
    ext χ
    rw [finsum_mem_eq_finite_toFinset_sum _
      ((Zeros108.ntZeros_finite χ T).sdiff (t := {ρ : ℂ | |ρ.im| ≤ U}))]
  rw [heq]
  convert hh using 1
  rw [Band108.zSum_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [show (mult χ ρ : ℂ) * Complex.exp (ρ * (Real.log x : ℂ)) / (x : ℂ) =
      (mult χ ρ : ℂ) * (Complex.exp (ρ * (Real.log x : ℂ)) / (x : ℂ)) by ring,
    hp χ ρ ((Set.Finite.mem_toFinset _).mp hρ).1]
  ring

/-- Derived logarithmic absorption for page 357 display 19.
This keeps the endpoint log loss explicit until the final epsilon budget. -/
theorem eventually_log_sq_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, Real.log X ^ 2 ≤ X ^ ε := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop 2 hε).bound
    (by norm_num : (0 : ℝ) < 1), eventually_ge_atTop (1 : ℝ)] with X hX hX1
  have hh : |Real.log X ^ 2| ≤ X ^ ε := by
    simpa only [Real.norm_eq_abs, one_mul, Real.rpow_ofNat,
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ X) _)] using hX
  exact (le_abs_self _).trans hh

/-- Derived elementary instance for every rounded model in this file.
It is independent of the unproved GRH and GMC hypotheses. -/
theorem rounded_model_instance :
    lowerEndpoint 16 = 3 ∧ clippedEndpoint 16 16 8 = 8 ∧
      1 ≤ lowHeight 16 (1 / 8) ∧
        (1 / (4 * (2 : ℝ)) ≤ 1 / 8 ∧ 1 / 8 ≤ 1 / (2 * (2 : ℝ))) := by
  norm_num [lowerEndpoint, clippedEndpoint, lowHeight]

/-- Derived comparison for the scaled endpoints in page 357 display 19.
Changing the positive center of the actual correlation costs only the
explicit exponential weight translation factor. No GRH is needed. -/
theorem correlation_change_center {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (T : ℝ) (q : ℕ) [NeZero q] (a : ℕ) :
    ‖F Y T q a‖ ≤ Real.exp (2 * |Real.log (Y / X)|) * ‖F X T q a‖ := by
  let r := Real.log (Y / X)
  have hr : X * Real.exp r = Y := by
    dsimp [r]
    rw [Real.exp_log (div_pos hY hX)]
    field_simp [hX.ne']
  have he (v : ℝ) : Y * Real.exp v = X * Real.exp (v + r) := by
    rw [← hr, Real.exp_add]
    ring
  rw [← Mass108.full_weighted_mass hY T q a, ← Mass108.full_weighted_mass hX T q a]
  simp_rw [he]
  have hshift :
      (∫ v : ℝ, ‖zSum (X * Real.exp (v + r)) (-1) T q a‖ ^ 2 * Real.exp (-2 * |v|)) =
        ∫ v : ℝ, ‖zSum (X * Real.exp v) (-1) T q a‖ ^ 2 * Real.exp (-2 * |v - r|) := by
    simpa only [add_sub_cancel_right] using
      MeasureTheory.integral_add_right_eq_self
        (fun v : ℝ => ‖zSum (X * Real.exp v) (-1) T q a‖ ^ 2 * Real.exp (-2 * |v - r|)) r
  rw [hshift, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_mono_of_nonneg
    (ae_of_all _ (fun v => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))
    ((Correlation108.correlation_identity hX T q a).1.const_mul _)
  apply ae_of_all
  intro v
  have habs : |v| ≤ |v - r| + |r| := by
    simpa only [sub_add_cancel] using abs_add_le (v - r) r
  have hweight : Real.exp (-2 * |v - r|) ≤ Real.exp (2 * |r|) * Real.exp (-2 * |v|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hh := mul_le_mul_of_nonneg_left hweight (sq_nonneg (‖zSum (X * Real.exp v) (-1) T q a‖))
  simpa only [mul_left_comm] using hh

/-- Derived Fubini input for P0071 page 357 display 16.
The total mass of a moving interval integral is its length times the
original integral. Mathlib supplies the convolution integral theorem. -/
theorem moving_integral_mass (f : ℝ → ℝ) (hf : Integrable f) {h : ℝ} (hh : 0 ≤ h) :
    Integrable (fun t : ℝ => ∫ u in (t - h)..t, f u) ∧
      (∫ t : ℝ, ∫ u in (t - h)..t, f u) = h * ∫ u : ℝ, f u := by
  let g : ℝ → ℝ := (Set.Icc 0 h).indicator (fun _ => 1)
  have hg : Integrable g := by
    have hg0 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc 0 h) volume :=
      continuousOn_const.integrableOn_Icc
    exact (integrable_indicator_iff measurableSet_Icc).2 hg0
  have he (t : ℝ) :
      convolution g f (ContinuousLinearMap.mul ℝ ℝ) volume t = ∫ u in (t - h)..t, f u := by
    rw [convolution_mul_swap]
    have hind : (fun u : ℝ => g (t - u) * f u) = (Set.Icc (t - h) t).indicator f := by
      funext u
      by_cases hu : u ∈ Set.Icc (t - h) t
      · have htu : t - u ∈ Set.Icc 0 h := by
          constructor <;> linarith [hu.1, hu.2]
        simp [g, htu, hu]
      · have htu : t - u ∉ Set.Icc 0 h := by
          intro htu
          apply hu
          constructor <;> linarith [htu.1, htu.2]
        simp [g, htu, hu]
    rw [hind, MeasureTheory.integral_indicator measurableSet_Icc,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact (intervalIntegral.integral_of_le (by linarith : t - h ≤ t)).symm
  have heq : convolution g f (ContinuousLinearMap.mul ℝ ℝ) volume =
      (fun t : ℝ => ∫ u in (t - h)..t, f u) := funext he
  have hgint : ∫ t : ℝ, g t = h := by
    dsimp only [g]
    rw [MeasureTheory.integral_indicator measurableSet_Icc]
    simp [hh]
  constructor
  · rw [← heq]
    exact MeasureTheory.Integrable.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hg hf
  · rw [← heq, MeasureTheory.integral_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hg hf, hgint]
    rfl


/-- Derived Cauchy Schwarz input for P0071 page 357 display 16.
The square of a complex interval integral is at most its length times
the squared norm integral. This specializes Mathlib Holder to exponent two. -/
theorem interval_norm_sq_le {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioc a b)))
    (hf2 : Integrable (fun u => ‖f u‖ ^ 2) (volume.restrict (Set.Ioc a b))) :
    ‖∫ u in a..b, f u‖ ^ 2 ≤ (b - a) * ∫ u in a..b, ‖f u‖ ^ 2 := by
  let μ := volume.restrict (Set.Ioc a b)
  have hfm : MemLp (fun u => ‖f u‖) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = (2 : ENNReal) by norm_num]
    exact (memLp_two_iff_integrable_sq hf.norm).2 hf2
  have h1m : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = (2 : ENNReal) by norm_num]
    apply (memLp_two_iff_integrable_sq aestronglyMeasurable_const).2
    exact ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).pow 2).intervalIntegrable a b |>.1
  have hpq : (2 : ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  have hcs := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    (ae_of_all _ (fun u => norm_nonneg (f u))) (ae_of_all _ (fun _ : ℝ => (by norm_num : (0 : ℝ) ≤ 1)))
    hfm h1m
  simp only [mul_one, Real.rpow_two, one_pow] at hcs
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hcs
  have hlen : (∫ _u : ℝ, (1 : ℝ) ∂μ) = b - a := by
    simp [μ, hab]
  rw [hlen] at hcs
  have hnorm := MeasureTheory.norm_integral_le_integral_norm (μ := μ) f
  have hq0 : 0 ≤ ∫ u : ℝ, ‖f u‖ ^ 2 ∂μ := MeasureTheory.integral_nonneg (fun u => sq_nonneg _)
  have hh := pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans hcs) 2
  rw [mul_pow, Real.sq_sqrt hq0, Real.sq_sqrt (sub_nonneg.mpr hab)] at hh
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  simpa only [mul_comm] using hh

/-- Derived stopped support identity for P0071 page 356 and display 16.
Integrating a function restricted to the original support is exactly
integration between the two clipped endpoints. No endpoint is discarded. -/
theorem integral_clipped (f : ℝ → ℂ) {A B a b : ℝ} (hAB : A ≤ B) (hab : a ≤ b) :
    (∫ u in a..b, (Set.Icc A B).indicator f u) =
      ∫ u in (max A (min B a))..(max A (min B b)), f u := by
  rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Icc_eq_integral_Ioc,
    MeasureTheory.integral_indicator measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc, Set.Icc_inter_Icc]
  change (∫ u in Set.Icc (max A a) (min B b), f u) = _
  have hzero (hz : min B b ≤ max A a) :
      (∫ u in Set.Icc (max A a) (min B b), f u) = 0 := by
    apply MeasureTheory.setIntegral_measure_zero
    rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]
    linarith
  by_cases hbA : b ≤ A
  · have hca : max A (min B a) = A := max_eq_left ((min_le_right _ _).trans (hab.trans hbA))
    have hcb : max A (min B b) = A := max_eq_left ((min_le_right _ _).trans hbA)
    rw [hca, hcb, intervalIntegral.integral_same]
    exact hzero ((min_le_right _ _).trans (hbA.trans (le_max_left _ _)))
  by_cases hBa : B ≤ a
  · conv_rhs => rw [min_eq_left hBa, min_eq_left (hBa.trans hab), max_eq_right hAB,
      intervalIntegral.integral_same]
    exact hzero ((min_le_left _ _).trans (hBa.trans (le_max_right _ _)))
  have hAb : A ≤ b := le_of_not_ge hbA
  have haB : a ≤ B := le_of_not_ge hBa
  have hle : max A a ≤ min B b := max_le (le_min hAB hAb) (le_min haB hab)
  rw [min_eq_right haB, max_eq_right (le_min hAB hAb)]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le hle).symm

/-- Page 357 display 16, the band derivative with a positive lower clamp.
The clamp gives a continuous extension without altering the stopped support. -/
noncomputable def zeroDerivative (X U T : ℝ) (q : ℕ) [NeZero q] (a : ℕ) (t : ℝ) : ℂ :=
  (((max (lowerEndpoint X) t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    zSum (max (lowerEndpoint X) t) U T q a

/-- Page 357 display 16, restrict the actual band derivative to both
integer endpoints of the stopped polynomial. -/
noncomputable def stoppedZeroDerivative (X Y U T : ℝ) (q : ℕ) [NeZero q] (a : ℕ) : ℝ → ℂ :=
  (Set.Icc (lowerEndpoint X) (⌊Y⌋₊ : ℝ)).indicator (zeroDerivative X U T q a)

/-- Derived regularity for page 357 display 16.
The positive clamp preserves continuity of the actual weighted zero band. -/
theorem continuous_zeroDerivative {X : ℝ} (hX : 8 ≤ X) (U T : ℝ)
    (q : ℕ) [NeZero q] (a : ℕ) : Continuous (zeroDerivative X U T q a) := by
  have hc : Continuous (fun t : ℝ => max (lowerEndpoint X) t) := continuous_const.max continuous_id
  have hp : ∀ t : ℝ, 0 < max (lowerEndpoint X) t := fun t =>
    (lowerEndpoint_pos hX).trans_le (le_max_left _ _)
  have hw : Continuous (fun t : ℝ => (max (lowerEndpoint X) t) ^ (-(1 / 2 : ℝ))) :=
    hc.rpow_const (fun t => Or.inl (hp t).ne')
  exact (Complex.continuous_ofReal.comp hw).mul
    (Lemma1Full108.continuous_zSum_comp hc hp U T q a)

/-- Derived integrability for page 357 display 16.
The band derivative and its squared norm are integrable on the exact support. -/
theorem stoppedZeroDerivative_integrable {X : ℝ} (hX : 8 ≤ X) (Y U T : ℝ)
    (q : ℕ) [NeZero q] (a : ℕ) :
    Integrable (stoppedZeroDerivative X Y U T q a) ∧
      Integrable (fun t : ℝ => ‖stoppedZeroDerivative X Y U T q a t‖ ^ 2) := by
  have hc := continuous_zeroDerivative hX U T q a
  have hi : Integrable (stoppedZeroDerivative X Y U T q a) :=
    (integrable_indicator_iff measurableSet_Icc).2 hc.continuousOn.integrableOn_Icc
  refine ⟨hi, ?_⟩
  have he : (fun t : ℝ => ‖stoppedZeroDerivative X Y U T q a t‖ ^ 2) =
      (Set.Icc (lowerEndpoint X) (⌊Y⌋₊ : ℝ)).indicator
        (fun t : ℝ => ‖zeroDerivative X U T q a t‖ ^ 2) := by
    funext t
    by_cases ht : t ∈ Set.Icc (lowerEndpoint X) (⌊Y⌋₊ : ℝ) <;>
      simp [stoppedZeroDerivative, ht]
  rw [he]
  exact (integrable_indicator_iff measurableSet_Icc).2
    (hc.norm.pow 2).continuousOn.integrableOn_Icc

/-- Page 357 display 16 with the true stopped endpoints from display 21.
The zero window is exactly a moving integral of its supported derivative.
CONDITIONAL ON GRH with clean axioms. -/
theorem zeroWindow_eq_integral (hG : GRH) {X : ℝ} (hX : 8 ≤ X) (Y : ℝ)
    (hY : lowerEndpoint X ≤ (⌊Y⌋₊ : ℝ)) (q : ℕ) [NeZero q] (a L : ℕ)
    (U T t : ℝ) :
    zeroWindow X Y q a L U T t =
      ∫ u in (t - L)..t, stoppedZeroDerivative X Y U T q a u := by
  let A := lowerEndpoint X
  let B : ℝ := ⌊Y⌋₊
  let l := clippedEndpoint X Y (t - L)
  let r := clippedEndpoint X Y t
  have hLreal : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hl : A ≤ l := le_max_left _ _
  have hr : r ≤ B := max_le hY (min_le_left _ _)
  have hlr : l ≤ r := max_le_max_left A (min_le_min_left B (sub_le_self t hLreal))
  have hc := continuous_zeroDerivative hX U T q a
  have hd : ∀ u ∈ Set.uIcc l r,
      HasDerivAt (fun v : ℝ => zeroPrimitive v U T q a) (zeroDerivative X U T q a u) u := by
    intro u hu
    rw [Set.uIcc_of_le hlr] at hu
    have hAu : A ≤ u := hl.trans hu.1
    have hAu' : lowerEndpoint X ≤ u := hAu
    have hu0 : 0 < u := (lowerEndpoint_pos hX).trans_le hAu
    simpa only [zeroDerivative, max_eq_right hAu'] using zeroPrimitive_hasDerivAt hG hu0 U T q a
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable l r)
  have hclip := integral_clipped (zeroDerivative X U T q a) hY
    (sub_le_self t hLreal)
  change (∫ u in (t - L)..t, stoppedZeroDerivative X Y U T q a u) = ∫ u in l..r, zeroDerivative X U T q a u at hclip
  exact hFTC.symm.trans hclip.symm

/-- Derived cell transfer for P0071 page 357 display 16.
Each exact integer region lies inside the full covering interval.
Nonnegative mass on its disjoint unit cells is at most the full integral. -/
theorem region_integral_le (g : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    (X Y : ℝ) (L : ℕ) (r : Fin 3) :
    (∑ m ∈ cells X Y L r, ∫ t in (m : ℝ)..(m + 1 : ℝ), g t) ≤
      ∫ t in (0 : ℝ)..((⌊Y⌋₊ + 1 + L : ℕ) : ℝ), g t := by
  let N := ⌊Y⌋₊ + 1 + L
  have hs : cells X Y L r ⊆ Finset.range N := by
    intro m hm
    exact (Finset.mem_filter.mp hm).1
  have he := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => (n : ℝ)) (n := N) (μ := volume)
    (fun k hk => hg.intervalIntegrable (k : ℝ) ((k + 1 : ℕ) : ℝ))
  calc
    _ ≤ ∑ m ∈ Finset.range N, ∫ t in (m : ℝ)..(m + 1 : ℝ), g t :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun m hm hnot =>
        intervalIntegral.integral_nonneg_of_forall (by linarith) hg0)
    _ = _ := by
      simpa only [N, Nat.cast_zero, Nat.cast_add, Nat.cast_one] using he

/-- Derived rounding bounds for P0071 page 357 display 16.
The exact stopped support lies between X over eight and twice X. -/
theorem rounded_support_bounds {X Y : ℝ} (hX : 16 ≤ X) (hY : X / 4 ≤ Y) (hY2 : Y ≤ 2 * X) :
    X / 8 ≤ lowerEndpoint X ∧ lowerEndpoint X ≤ (⌊Y⌋₊ : ℝ) ∧ (⌊Y⌋₊ : ℝ) ≤ 2 * X := by
  have hceil := Nat.le_ceil (X / 4)
  have hY0 : 0 ≤ Y := by linarith
  have hfloor := Nat.floor_le hY0
  have hc : ⌈X / 4⌉₊ ≤ ⌊Y⌋₊ + 1 := by
    apply Nat.ceil_le.mpr
    push_cast
    exact hY.trans (Nat.lt_floor_add_one Y).le
  have hc' : (⌈X / 4⌉₊ : ℝ) ≤ (⌊Y⌋₊ : ℝ) + 1 := by exact_mod_cast hc
  unfold lowerEndpoint
  exact ⟨by linarith, by linarith, hfloor.trans hY2⟩

/-- Page 357 display 16, the full supported derivative mass.
Lemma 1 applies to the actual Gauss weighted band before any GMC bound.
The reciprocal weight is at most eight over X on the stopped support.
CONDITIONAL ON GRH with clean axioms. -/
theorem stoppedZeroDerivative_mass (hG : GRH) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 16 ≤ X → ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q →
      ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X → ∀ W : ℝ, 0 ≤ W →
        (∫ t : ℝ, ‖stoppedZeroDerivative X Y (-1) W q a t‖ ^ 2) ≤ C * ‖F X W q a‖ := by
  obtain ⟨K, hK⟩ := LeanLab.LanguascoPerelli1996.lemma1 hG (1 / 8) 2 (by norm_num) (by norm_num)
  refine ⟨8 * max 0 K, by positivity, ?_⟩
  intro X hX q inst a ha Y hY hY2 W hW
  let A := lowerEndpoint X
  let B : ℝ := ⌊Y⌋₊
  have hXpos : 0 < X := by linarith
  have hX8 : 8 ≤ X := by linarith
  have hbounds := rounded_support_bounds hX hY hY2
  have hApos : 0 < A := lowerEndpoint_pos hX8
  have hAB : A ≤ B := hbounds.2.1
  have hmass : (∫ t : ℝ, ‖stoppedZeroDerivative X Y (-1) W q a t‖ ^ 2) =
      ∫ t in A..B, ‖zeroDerivative X (-1) W q a t‖ ^ 2 := by
    have he : (fun t : ℝ => ‖stoppedZeroDerivative X Y (-1) W q a t‖ ^ 2) =
        (Set.Icc A B).indicator (fun t : ℝ => ‖zeroDerivative X (-1) W q a t‖ ^ 2) := by
      funext t
      by_cases ht : t ∈ Set.Icc (lowerEndpoint X) (⌊Y⌋₊ : ℝ) <;>
        simp [stoppedZeroDerivative, A, B, ht]
    rw [he, MeasureTheory.integral_indicator measurableSet_Icc,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hAB]
  rw [hmass]
  by_cases hEq : A = B
  · rw [hEq, intervalIntegral.integral_same]
    positivity
  have hlt : A < B := lt_of_le_of_ne hAB hEq
  let H : ℝ → ℝ := fun t => ‖zSum (max A t) (-1) W q a‖ ^ 2
  have hHc : Continuous H := (Lemma1Full108.continuous_zSum_comp
    (continuous_const.max continuous_id) (fun t => hApos.trans_le (le_max_left _ _)) (-1) W q a).norm.pow 2
  have hc := (continuous_zeroDerivative hX8 (-1) W q a).norm.pow 2
  have hp : ∀ u ∈ Set.Icc A B, ‖zeroDerivative X (-1) W q a u‖ ^ 2 ≤ (8 / X) * H u := by
    intro u hu
    have hu0 : 0 < u := hApos.trans_le hu.1
    have hAu : lowerEndpoint X ≤ u := hu.1
    have hnorm : ‖zeroDerivative X (-1) W q a u‖ ^ 2 = u⁻¹ * H u := by
      simp only [zeroDerivative, H, A, max_eq_right hAu, norm_mul, mul_pow,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have he : (u ^ (-(1 / 2 : ℝ))) ^ 2 = u⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
        norm_num [Real.rpow_neg_one]
      rw [he]
    have huX : X ≤ 8 * u := by linarith [hbounds.1.trans hu.1]
    have hinv : u⁻¹ ≤ 8 / X := by
      rw [← one_div]
      exact (div_le_div_iff₀ hu0 hXpos).2 (by linarith)
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right hinv (sq_nonneg _)
  have hI : (∫ t in A..B, ‖zeroDerivative X (-1) W q a t‖ ^ 2) ≤
      (8 / X) * ∫ t in A..B, H t := by
    calc
      _ ≤ ∫ t in A..B, (8 / X) * H t :=
        intervalIntegral.integral_mono_on hAB (hc.intervalIntegrable _ _)
          ((continuous_const.mul hHc).intervalIntegrable _ _) hp
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hband : (∫ t in A..B, H t) = ∫ t in A..B, ‖zSum t (-1) W q a‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hAB] at ht
    dsimp [H]
    rw [max_eq_right ht.1]
  have hα : (1 / 8 : ℝ) ≤ A / X := (le_div_iff₀ hXpos).2 (by linarith [hbounds.1])
  have hαβ : A / X < B / X := (div_lt_div_iff_of_pos_right hXpos).2 hlt
  have hβ : B / X ≤ 2 := (div_le_iff₀ hXpos).2 hbounds.2.2
  have hb := hK X hXpos W hW q a ha (A / X) (B / X) hα hαβ hβ
  have heA : A / X * X = A := div_mul_cancel₀ _ hXpos.ne'
  have heB : B / X * X = B := div_mul_cancel₀ _ hXpos.ne'
  rw [heA, heB, ← hband] at hb
  calc
    _ ≤ (8 / X) * (K * X * ‖F X W q a‖) :=
      hI.trans (mul_le_mul_of_nonneg_left hb (by positivity))
    _ ≤ (8 / X) * (max 0 K * X * ‖F X W q a‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right 0 K) hXpos.le) (norm_nonneg _)) (by positivity)
    _ = _ := by field_simp [hXpos.ne']

/-- Derived real height partial summation bridge for P0071 page 356 display 15.
A monotone real multiplier is controlled by every symmetric height prefix.
The proof groups equal absolute heights and reuses Partial318.monotone_mass_le.
No individual coefficient norm bound or GRH input is used. -/
theorem height_weighted_mass {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ)
    {W K M B : ℝ} (w : ℝ → ℝ) (hWK : W < K) (hM : 0 ≤ M) (hw0 : 0 ≤ w W)
    (hw : MonotoneOn w (Set.Icc W K)) (hB : w K ≤ B)
    (hγ : ∀ i ∈ s, W < |γ i| ∧ |γ i| ≤ K)
    (hmass : ∀ u : ℝ, W ≤ u → u ≤ K →
      Interpolation318.mass s (fun i => if |γ i| ≤ u then c i else 0) γ ≤ M) :
    Interpolation318.mass s (fun i => (w |γ i| : ℂ) * c i) γ ≤ 4 * B ^ 2 * M := by
  classical
  by_cases hs : s = ∅
  · subst s
    simp only [Interpolation318.mass, Finset.sum_empty, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_mul, MeasureTheory.integral_zero]
    positivity
  let H := s.image (fun i => |γ i|)
  have hH : H.Nonempty := (Finset.nonempty_iff_ne_empty.mpr hs).image _
  have hcardpos : 0 < H.card := Finset.card_pos.mpr hH
  let N := H.card - 1
  have hcard : H.card = N + 1 := by dsimp only [N]; omega
  let e := H.orderIsoOfFin hcard
  let idx : (i : ι) → i ∈ s → Fin (N + 1) := fun i hi =>
    e.symm ⟨|γ i|, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  let f : ℕ → ι → ℂ := fun k i =>
    if hi : i ∈ s then if (idx i hi).val = k then c i else 0 else 0
  let v : ℕ → ℝ := fun k => w (e ⟨min k N, by omega⟩ : ℝ)
  have hheight (k : Fin (N + 1)) : W < (e k : ℝ) ∧ (e k : ℝ) ≤ K := by
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp (e k).property
    simpa only [← he] using hγ i hi
  have hv : Monotone v := by
    intro k l hkl
    apply hw ⟨(hheight _).1.le, (hheight _).2⟩ ⟨(hheight _).1.le, (hheight _).2⟩
    exact e.monotone (show (⟨min k N, by omega⟩ : Fin (N + 1)) ≤ ⟨min l N, by omega⟩ from
      min_le_min_right N hkl)
  have hv0 : 0 ≤ v 0 := hw0.trans
    (hw ⟨le_rfl, hWK.le⟩ ⟨(hheight _).1.le, (hheight _).2⟩ (hheight _).1.le)
  have hpre (k : ℕ) (hk : k ≤ N) (i : ι) (hi : i ∈ s) :
      (∑ j ∈ Finset.range (k + 1), f j i) =
        if |γ i| ≤ (e ⟨k, by omega⟩ : ℝ) then c i else 0 := by
    have hh : (idx i hi).val ≤ k ↔ |γ i| ≤ (e ⟨k, by omega⟩ : ℝ) := by
      have hh := (e.le_iff_le (x := idx i hi) (y := ⟨k, by omega⟩)).symm
      change (idx i hi).val ≤ k ↔ (e (idx i hi) : ℝ) ≤ (e ⟨k, by omega⟩ : ℝ) at hh
      simpa only [idx, OrderIso.apply_symm_apply] using hh
    simp only [f, dite_eq_left hi, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff, hh]
  have hp (k : ℕ) (hk : k ≤ N) :
      Interpolation318.mass s (fun i => ∑ j ∈ Finset.range (k + 1), f j i) γ ≤ M := by
    rw [Partial318.mass_congr s _ _ γ (fun i hi => hpre k hk i hi)]
    exact hmass (e ⟨k, by omega⟩) (hheight _).1.le (hheight _).2
  have hcoef (i : ι) (hi : i ∈ s) :
      (∑ k ∈ Finset.range (N + 1), (v k : ℂ) * f k i) = (w |γ i| : ℂ) * c i := by
    have hh : v (idx i hi).val = w |γ i| := by
      have hfin : (⟨min (idx i hi).val N, by omega⟩ : Fin (N + 1)) = idx i hi := by
        apply Fin.ext
        exact Nat.min_eq_left (Nat.le_of_lt_succ (idx i hi).isLt)
      change w (e (⟨min (idx i hi).val N, by omega⟩ : Fin (N + 1)) : ℝ) = w |γ i|
      rw [hfin]
      simp only [idx, OrderIso.apply_symm_apply]
    simp only [f, dite_eq_left hi, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_range,
      (idx i hi).isLt, ite_eq_left, hh]
  rw [← Partial318.mass_congr s _ _ γ hcoef]
  have hb := Partial318.monotone_mass_le s γ f v N hM hv0 hv hp
  have hvN0 : 0 ≤ v N := hv0.trans (hv (Nat.zero_le N))
  have hvNB : v N ≤ B := (hw ⟨(hheight _).1.le, (hheight _).2⟩
    ⟨hWK.le, le_rfl⟩ (hheight _).2).trans hB
  have hbound := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hvN0 hvNB 2) hM
  nlinarith

/-- Derived finite reciprocal height estimate for page 356 display 15.
Symmetric prefix mass control is preserved. The proof uses the real
monotone multiplier theorem and the existing frequency interpolation.
This is not the full variable height integral estimate of display 15. -/
theorem reciprocal_band_mass {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ)
    {W K M : ℝ} (hW : 1 ≤ W) (hWK : W < K) (hM : 0 ≤ M)
    (hγ : ∀ i ∈ s, W < |γ i| ∧ |γ i| ≤ K)
    (hmass : ∀ u : ℝ, W ≤ u → u ≤ K →
      Interpolation318.mass s (fun i => if |γ i| ≤ u then c i else 0) γ ≤ M) :
    Interpolation318.mass s (fun i => c i / ((1 / 2 : ℂ) + Complex.I * (γ i : ℂ))) γ ≤ 105 * M / W ^ 2 := by
  classical
  have hWpos : 0 < W := by linarith
  have hWne : W ≠ 0 := hWpos.ne'
  have scale (z : ℂ) (d : ι → ℂ) :
      Interpolation318.mass s (fun i => z * d i) γ = ‖z‖ ^ 2 * Interpolation318.mass s d γ := by
    have he (v : ℝ) :
        (∑ i ∈ s, z * d i * Complex.exp (Complex.I * (γ i : ℂ) * (v : ℂ))) =
          z * ∑ i ∈ s, d i * Complex.exp (Complex.I * (γ i : ℂ) * (v : ℂ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    unfold Interpolation318.mass
    simp_rw [he, norm_mul, mul_pow, mul_assoc]
    rw [MeasureTheory.integral_const_mul]
  have submass (d e : ι → ℂ) :
      Interpolation318.mass s (fun i => d i - e i) γ ≤ 2 * (Interpolation318.mass s d γ + Interpolation318.mass s e γ) := by
    let f : Fin 2 → ι → ℂ := fun k => if k = 0 then d else fun i => -e i
    have hh := Partial318.mass_sum_le s Finset.univ f γ (fun _ => (1 : ℝ))
      (fun k hk => by norm_num)
    simpa [Fin.sum_univ_two, f, Partial318.mass_neg, sub_eq_add_neg] using hh
  let b : ℝ → ℝ := fun u => ((1 / 4 : ℝ) + u ^ 2)⁻¹
  let a : ℝ → ℝ := fun u => b W - b u
  let d : ι → ℂ := fun i => (b |γ i| : ℂ) * c i
  have hbpos (u : ℝ) : 0 < b u := by dsimp [b]; positivity
  have hbmono : AntitoneOn b (Set.Icc W K) := by
    intro u hu v hv huv
    apply inv_anti₀ (by positivity : 0 < (1 / 4 : ℝ) + u ^ 2)
    have hu0 : 0 ≤ u := by linarith [hu.1]
    nlinarith [pow_le_pow_left₀ hu0 huv 2]
  have hamono : MonotoneOn a (Set.Icc W K) := by
    intro u hu v hv huv
    exact sub_le_sub_left (hbmono hu hv huv) (b W)
  have ha := height_weighted_mass (B := b W) s c γ a hWK hM (by dsimp [a]; linarith)
    hamono (by dsimp [a]; linarith [hbpos K]) hγ hmass
  have hbase : Interpolation318.mass s c γ ≤ M := by
    have hh := hmass K hWK.le le_rfl
    have he := Partial318.mass_congr s (fun i => if |γ i| ≤ K then c i else 0) c γ
      (fun i hi => ite_eq_left (hγ i hi).2)
    rw [he] at hh
    exact hh
  have hd0 : Interpolation318.mass s d γ ≤ 10 * b W ^ 2 * M := by
    have he := Partial318.mass_congr s d
      (fun i => (b W : ℂ) * c i - (a |γ i| : ℂ) * c i) γ (fun i hi => by
        dsimp [d, a]
        push_cast
        ring)
    have hh := submass (fun i => (b W : ℂ) * c i) (fun i => (a |γ i| : ℂ) * c i)
    rw [← he, scale] at hh
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hh
    have hm := mul_le_mul_of_nonneg_left hbase (sq_nonneg (b W))
    nlinarith
  have hbW : b W ≤ 1 / W ^ 2 := by
    dsimp [b]
    simpa only [one_div] using inv_anti₀ (sq_pos_of_pos hWpos)
      (by linarith : W ^ 2 ≤ (1 / 4 : ℝ) + W ^ 2)
  have hbW2 : b W ^ 2 ≤ 1 / W ^ 4 := by
    have hh := pow_le_pow_left₀ (hbpos W).le hbW 2
    convert hh using 1 <;> field_simp [hWne]
  let M0 := 10 * M / W ^ 4
  have hM0 : 0 ≤ M0 := by dsimp [M0]; positivity
  have hd : Interpolation318.mass s d γ ≤ M0 := by
    calc
      _ ≤ 10 * b W ^ 2 * M := hd0
      _ = (10 * M) * b W ^ 2 := by ring
      _ ≤ (10 * M) * (1 / W ^ 4) := mul_le_mul_of_nonneg_left hbW2 (by positivity)
      _ = _ := by dsimp [M0]; ring
  let w2 : ℝ → ℝ := fun u => u ^ 2 / ((1 / 4 : ℝ) + u ^ 2)
  have hw2 : MonotoneOn w2 (Set.Icc W K) := by
    intro u hu v hv huv
    apply (div_le_div_iff₀ (by positivity : 0 < (1 / 4 : ℝ) + u ^ 2)
      (by positivity : 0 < (1 / 4 : ℝ) + v ^ 2)).2
    have hu0 : 0 ≤ u := by linarith [hu.1]
    nlinarith [pow_le_pow_left₀ hu0 huv 2]
  have h2 := height_weighted_mass (B := 1) s c γ w2 hWK hM (by dsimp [w2]; positivity) hw2
    (by dsimp [w2]; apply (div_le_one (by positivity)).2; linarith) hγ hmass
  norm_num only [one_pow, mul_one] at h2
  have he2 : Interpolation318.mass s (fun i => (γ i : ℂ) ^ 2 * d i) γ =
      Interpolation318.mass s (fun i => (w2 |γ i| : ℂ) * c i) γ := by
    apply Partial318.mass_congr
    intro i hi
    dsimp [d, b, w2]
    simp only [sq_abs]
    push_cast
    ring
  have hsecond : Interpolation318.mass s (fun i => (γ i : ℂ) ^ 2 * d i) γ ≤ 4 * W ^ 4 * M0 := by
    rw [he2]
    have he : 4 * W ^ 4 * M0 = 40 * M := by dsimp [M0]; field_simp [hWne]; ring
    rw [he]
    nlinarith
  have hfirst := Interpolation318.mass_first_le s d γ hW hM0 hd hsecond
  have heFirst : 5 * W ^ 2 * M0 = 50 * M / W ^ 2 := by dsimp [M0]; field_simp [hWne]; ring
  rw [heFirst] at hfirst
  have hW24 : W ^ 2 ≤ W ^ 4 := pow_le_pow_right₀ hW (by norm_num)
  have hd2 : Interpolation318.mass s d γ ≤ 10 * M / W ^ 2 := by
    have hh := one_div_le_one_div_of_le (sq_pos_of_pos hWpos) hW24
    have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 10 * M)
    exact hd.trans (by dsimp [M0]; simpa only [mul_one_div] using hh')
  have hcoef : Interpolation318.mass s (fun i => c i / ((1 / 2 : ℂ) + Complex.I * (γ i : ℂ))) γ =
      Interpolation318.mass s (fun i => (1 / 2 : ℂ) * d i - Complex.I * ((γ i : ℂ) * d i)) γ := by
    apply Partial318.mass_congr
    intro i hi
    have hn : Complex.normSq ((1 / 2 : ℂ) + Complex.I * (γ i : ℂ)) =
        (1 / 4 : ℝ) + γ i ^ 2 := by
      norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]; ring
    rw [div_eq_mul_inv, Complex.inv_def, hn]
    have hc : starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * (γ i : ℂ)) =
        (1 / 2 : ℂ) - Complex.I * (γ i : ℂ) := by norm_num [sub_eq_add_neg, map_ofNat]
    rw [hc]
    dsimp [d, b]
    simp only [sq_abs]
    ring
  rw [hcoef]
  have hh := submass (fun i => (1 / 2 : ℂ) * d i) (fun i => Complex.I * ((γ i : ℂ) * d i))
  rw [scale, scale] at hh
  norm_num [norm_div] at hh
  have hn : 105 * M / W ^ 2 = 2 * ((1 / 4 : ℝ) * (10 * M / W ^ 2) + 50 * M / W ^ 2) := by ring
  rw [hn]
  linarith

/-- LEAF. CITED. P0071 page 355 before display 14, the sharp character
explicit formula from Davenport, reference 2. The logarithmic error also
covers imprimitive characters and the half weight at integer endpoints.
The formula is stated for the actual L function and actual Lambda sum.
No GMC hypothesis or window estimate occurs in this cited input. -/
theorem sharp_character_explicit_formula :
    GRH → ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
        ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) -
          (if χ = 1 then (x : ℂ) else 0) +
          ∑ᶠ ρ ∈ ntZeros χ T,
            (mult χ ρ : ℂ) * Complex.exp (ρ * (Real.log x : ℂ)) / ρ‖ ≤
          C * (1 + x / T) * Real.log ((q : ℝ) * x * T) ^ 2 := by
  sorry

/-- LEAF. P0071 pages 355 and 358 displays 14 and 23, the mean square
transfer from the sharp formula to the stopped arithmetic windows.
The exact finite primitive correction is retained in stopped_primitive_reduction
and stopped_primitive_expansion above. Those proofs reuse Character422,
BadPrimes422 and Primitive422 without discarding a Gauss weighted error.
The remaining obligation retains the correlated truncation error under
integration over the real cells. It has no GMC or F bound as a hypothesis.
The totient denominator is exact. It is not replaced by q here. -/
theorem sharp_window_comparison
    (hExplicit : GRH → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
          ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) -
            (if χ = 1 then (x : ℂ) else 0) +
            ∑ᶠ ρ ∈ ntZeros χ T,
              (mult χ ρ : ℂ) * Complex.exp (ρ * (Real.log x : ℂ)) / ρ‖ ≤
            C * (1 + x / T) * Real.log ((q : ℝ) * x * T) ^ 2) :
    GRH → ∀ δ : ℝ, 0 < δ → ∃ A X0 : ℝ, 0 ≤ A ∧ 16 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X → ∀ (q : ℕ) [NeZero q],
        (q : ℝ) ≤ X ^ (1 / 2 : ℝ) → ∀ a : ℕ, Nat.Coprime a q →
          ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X → ∀ L : ℕ, 0 < L → ∀ r : Fin 3,
            regionMass X Y q a L r ≤
              A * X ^ δ * (zeroMass X Y q a L r (-1) (X ^ 2) / (q.totient : ℝ) ^ 2 +
                L * X ^ (1 + δ)) := by
  sorry

/-- LEAF. P0071 page 357 display 16, low zero band mean square.
The two competing scales retain the finite stopped support for long windows.
FTC, Cauchy Schwarz and the moving integral mass identity prove both
support scales. Lemma 1 is applied to the actual weighted band.
CONDITIONAL ON GRH with clean axioms. -/
theorem low_zero_mass :
    GRH → ∃ A : ℝ, 0 ≤ A ∧ ∀ X : ℝ, 16 ≤ X →
      ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q →
        ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X → ∀ L : ℕ, 0 < L →
          ∀ r : Fin 3, ∀ W : ℝ, 1 ≤ W →
            zeroMass X Y q a L r (-1) W ≤ A * lowScale X L * ‖F X W q a‖ := by
  intro hG
  obtain ⟨C, hC, hMass⟩ := stoppedZeroDerivative_mass hG
  refine ⟨6 * C, by positivity, ?_⟩
  intro X hX q inst a ha Y hY hY2 L hL r W hW
  have hX8 : 8 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  have hbounds := rounded_support_bounds hX hY hY2
  let A := lowerEndpoint X
  let B : ℝ := ⌊Y⌋₊
  let N : ℕ := ⌊Y⌋₊ + 1 + L
  let G := zeroDerivative X (-1) W q a
  let g := stoppedZeroDerivative X Y (-1) W q a
  let f : ℝ → ℝ := fun u => ‖g u‖ ^ 2
  let U : ℝ → ℝ := fun t => ∫ u in (t - L)..t, f u
  have hAB : A ≤ B := hbounds.2.1
  have hgi : Integrable g := (stoppedZeroDerivative_integrable hX8 Y (-1) W q a).1
  have hfi : Integrable f := (stoppedZeroDerivative_integrable hX8 Y (-1) W q a).2
  have hfn : ∀ t, 0 ≤ f t := fun t => sq_nonneg _
  have hM : (∫ u : ℝ, f u) ≤ C * ‖F X W q a‖ := hMass X hX q a ha Y hY hY2 W (by linarith)
  have hM0 : 0 ≤ ∫ u : ℝ, f u := MeasureTheory.integral_nonneg hfn
  have hwindow (t : ℝ) : zeroWindow X Y q a L (-1) W t = ∫ u in (t - L)..t, g u :=
    zeroWindow_eq_integral hG hX8 Y hAB q a L (-1) W t
  have hcc : Continuous (fun t => ‖zeroWindow X Y q a L (-1) W t‖ ^ 2) :=
    (continuous_zeroWindow hX8 Y q a L (-1) W).norm.pow 2
  have hcell : zeroMass X Y q a L r (-1) W ≤
      ∫ t in (0 : ℝ)..(N : ℝ), ‖zeroWindow X Y q a L (-1) W t‖ ^ 2 :=
    region_integral_le _ hcc (fun t => sq_nonneg _) X Y L r
  have hshortPoint (t : ℝ) : ‖zeroWindow X Y q a L (-1) W t‖ ^ 2 ≤ (L : ℝ) * U t := by
    have hgiOn : Integrable g (volume.restrict (Set.Ioc (t - L) t)) := hgi.integrableOn
    have hfiOn : Integrable f (volume.restrict (Set.Ioc (t - L) t)) := hfi.integrableOn
    have hh := interval_norm_sq_le (sub_le_self t hL0) hgiOn.aestronglyMeasurable hfiOn
    have he : t - (t - L) = (L : ℝ) := by ring
    rw [he] at hh
    rw [hwindow]
    exact hh
  obtain ⟨hUi, hUint⟩ := moving_integral_mass f hfi hL0
  have hUn : ∀ t : ℝ, 0 ≤ U t := fun t =>
    intervalIntegral.integral_nonneg_of_forall (sub_le_self t hL0) hfn
  have hUsub : (∫ t in (0 : ℝ)..(N : ℝ), U t) ≤ ∫ t : ℝ, U t := by
    rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
    exact MeasureTheory.setIntegral_le_integral hUi (ae_of_all _ hUn)
  have hshort : zeroMass X Y q a L r (-1) W ≤ (L : ℝ) ^ 2 * (C * ‖F X W q a‖) := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..(N : ℝ), ‖zeroWindow X Y q a L (-1) W t‖ ^ 2 := hcell
      _ ≤ ∫ t in (0 : ℝ)..(N : ℝ), (L : ℝ) * U t :=
        intervalIntegral.integral_mono_on (Nat.cast_nonneg N) (hcc.intervalIntegrable _ _)
          (hUi.const_mul (L : ℝ)).intervalIntegrable (fun t ht => hshortPoint t)
      _ = (L : ℝ) * ∫ t in (0 : ℝ)..(N : ℝ), U t := intervalIntegral.integral_const_mul _ _
      _ ≤ (L : ℝ) * ∫ t : ℝ, U t := mul_le_mul_of_nonneg_left hUsub hL0
      _ = (L : ℝ) ^ 2 * ∫ t : ℝ, f t := by rw [hUint]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hM (sq_nonneg _)
  have hcG : Continuous G := continuous_zeroDerivative hX8 (-1) W q a
  have hfmass : (∫ t : ℝ, f t) = ∫ t in A..B, ‖G t‖ ^ 2 := by
    have he : f = (Set.Icc A B).indicator (fun t : ℝ => ‖G t‖ ^ 2) := by
      funext t
      by_cases ht : t ∈ Set.Icc (lowerEndpoint X) (⌊Y⌋₊ : ℝ) <;>
        simp [f, g, G, stoppedZeroDerivative, A, B, ht]
    rw [he, MeasureTheory.integral_indicator measurableSet_Icc,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hAB]
  have hlongPoint (t : ℝ) : ‖zeroWindow X Y q a L (-1) W t‖ ^ 2 ≤ 2 * X * (C * ‖F X W q a‖) := by
    let l := clippedEndpoint X Y (t - L)
    let v := clippedEndpoint X Y t
    have hl : A ≤ l := le_max_left _ _
    have hv : v ≤ B := max_le hAB (min_le_left _ _)
    have hlv : l ≤ v := max_le_max_left A (min_le_min_left B (sub_le_self t hL0))
    have hh := integral_clipped G hAB (sub_le_self t hL0)
    have he : zeroWindow X Y q a L (-1) W t = ∫ u in l..v, G u := (hwindow t).trans hh
    have hcs := interval_norm_sq_le hlv hcG.aestronglyMeasurable
      (((hcG.norm.pow 2).intervalIntegrable l v).1)
    have hsub : (∫ u in l..v, ‖G u‖ ^ 2) ≤ ∫ t : ℝ, f t := by
      rw [hfmass]
      exact intervalIntegral.integral_mono_interval hl hlv hv
        (Filter.Eventually.of_forall (fun t => sq_nonneg _)) ((hcG.norm.pow 2).intervalIntegrable A B)
    have hlen : v - l ≤ 2 * X := by
      have hA0 : 0 ≤ A := (lowerEndpoint_pos hX8).le
      have hB : B ≤ 2 * X := hbounds.2.2
      linarith
    rw [he]
    calc
      _ ≤ (v - l) * ∫ u in l..v, ‖G u‖ ^ 2 := hcs
      _ ≤ (v - l) * ∫ t : ℝ, f t := mul_le_mul_of_nonneg_left hsub (sub_nonneg.mpr hlv)
      _ ≤ (2 * X) * ∫ t : ℝ, f t := mul_le_mul_of_nonneg_right hlen hM0
      _ ≤ _ := mul_le_mul_of_nonneg_left hM (by positivity)
  have hN : (N : ℝ) ≤ 3 * (X + L) := by
    have hB := hbounds.2.2
    dsimp [N]
    push_cast
    nlinarith
  have hlong : zeroMass X Y q a L r (-1) W ≤ 6 * C * ((X + L) * X) * ‖F X W q a‖ := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..(N : ℝ), ‖zeroWindow X Y q a L (-1) W t‖ ^ 2 := hcell
      _ ≤ ∫ _t in (0 : ℝ)..(N : ℝ), 2 * X * (C * ‖F X W q a‖) :=
        intervalIntegral.integral_mono_on (Nat.cast_nonneg N) (hcc.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _) (fun t ht => hlongPoint t)
      _ = (N : ℝ) * (2 * X * (C * ‖F X W q a‖)) := by rw [intervalIntegral.integral_const]; ring
      _ ≤ (3 * (X + L)) * (2 * X * (C * ‖F X W q a‖)) :=
        mul_le_mul_of_nonneg_right hN (by positivity)
      _ = _ := by ring
  by_cases hs : (L : ℝ) ^ 2 ≤ (X + L) * X
  · rw [lowScale, min_eq_left hs]
    have hp : 0 ≤ (L : ℝ) ^ 2 * (C * ‖F X W q a‖) := by positivity
    nlinarith
  · rw [lowScale, min_eq_right (le_of_not_ge hs)]
    exact hlong

/-- LEAF. P0071 page 356 display 15, high interior zero band.
Only the actual zero primitive mass is estimated. The arithmetic sum,
explicit formula error and GMC substitution occur in separate steps.
The missing theory is L2 partial summation for the reciprocal zero factor. -/
theorem interior_high_zero_mass :
    GRH → ∀ δ : ℝ, 0 < δ → ∃ A X0 : ℝ, 0 ≤ A ∧ 16 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X → ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q →
        ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X → ∀ L : ℕ, 0 < L →
          ∀ W : ℝ, 1 ≤ W → W ≤ X ^ 2 →
            zeroMass X Y q a L 1 W (X ^ 2) ≤
              A * X ^ (2 + δ) * correlationBracket X W (X ^ 2) q a := by
  sorry

/-- LEAF. P0071 page 357 displays 17 through 19, high endpoint bands.
The first term is the moving endpoint contribution from display 17.
The second term retains the fixed endpoint integral from displays 18 and 19.
The correlation envelope bounds the same Gauss weighted F on every prefix.
The elementary scalar evaluation of the endpoint integral is proved above. -/
theorem endpoint_high_zero_mass :
    GRH → ∀ δ : ℝ, 0 < δ → ∃ A X0 : ℝ, 0 ≤ A ∧ 16 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X → ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q →
        ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X → ∀ L : ℕ, 0 < L →
          ∀ r : Fin 3, r = 0 ∨ r = 2 → ∀ W c : ℝ, 1 ≤ W → W ≤ X ^ 2 → 0 ≤ c →
            (∀ u : ℝ, W ≤ u → u ≤ X ^ 2 → ‖F X u q a‖ ≤ c * u) →
              zeroMass X Y q a L r W (X ^ 2) ≤
                A * (X ^ (2 + δ) * correlationBracket X W (X ^ 2) q a +
                  L * X ^ (1 + δ) *
                    (c + (∫ u in W..(X ^ 2),
                      u ^ (-(3 : ℝ) / 2) * (c * u) ^ (1 / 2 : ℝ)) ^ 2)) := by
  sorry

/-- Derived elementary assembly of displays 15, 16 and 19.
All inputs here are real scalar inequalities. The proof uses no cited leaf. -/
theorem zero_mass_scalar {X ξ δ c A B f b i zlow zhigh z : ℝ} {L : ℕ}
    (hX : 2 ≤ X) (hδ : 0 ≤ δ) (hL : 0 < L)
    (hlo : 1 / (4 * (L : ℝ)) ≤ ξ) (hhi : ξ ≤ 1 / (2 * (L : ℝ)))
    (hc : 0 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : f ≤ c * lowHeight X ξ)
    (hb : b ≤ 4 * c / lowHeight X ξ)
    (hi : i ≤ 4 * c * Real.log X ^ 2) (hlog : Real.log X ^ 2 ≤ X ^ δ)
    (hlow : zlow ≤ A * lowScale X L * f)
    (hhigh : zhigh ≤ B * (X ^ (2 + δ) * b + L * X ^ (1 + δ) * (c + i)))
    (hz : z ≤ 2 * (zlow + zhigh)) :
    z ≤ (2 * (9 * A + 37 * B)) * c * L * X ^ (1 + 2 * δ) := by
  have hX0 : 0 < X := by linarith
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hr : 1 ≤ X ^ δ := Real.one_le_rpow (by linarith) hδ
  have hr0 : 0 ≤ X ^ δ := by positivity
  have hr2 : 1 ≤ (X ^ δ) ^ 2 := one_le_pow₀ hr
  have hr12 : X ^ δ ≤ (X ^ δ) ^ 2 := by nlinarith
  have hpow1 : X ^ (1 + δ) = X * X ^ δ := by rw [Real.rpow_add hX0, Real.rpow_one]
  have hpow2 : X ^ (2 + δ) = X ^ 2 * X ^ δ := by rw [Real.rpow_add hX0, Real.rpow_two]
  have hpow12 : X ^ (1 + 2 * δ) = X * (X ^ δ) ^ 2 := by
    rw [Real.rpow_add hX0, Real.rpow_one, mul_comm 2 δ, Real.rpow_mul hX0.le, Real.rpow_two]
  have hscale0 : 0 ≤ lowScale X L := by unfold lowScale; positivity
  have hl : zlow ≤ 9 * A * c * L * X := by
    calc
      _ ≤ A * lowScale X L * (c * lowHeight X ξ) :=
        hlow.trans (mul_le_mul_of_nonneg_left hf (by positivity))
      _ = A * c * (lowScale X L * lowHeight X ξ) := by ring
      _ ≤ A * c * (9 * L * X) :=
        mul_le_mul_of_nonneg_left (lowScale_height_le hX hL hlo hhi) (by positivity)
      _ = _ := by ring
  have hb' : X ^ (2 + δ) * b ≤ 32 * c * L * X * X ^ δ := by
    calc
      _ ≤ X ^ (2 + δ) * (4 * c / lowHeight X ξ) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (4 * c * X ^ δ) * (X ^ 2 / lowHeight X ξ) := by rw [hpow2]; ring
      _ ≤ (4 * c * X ^ δ) * (8 * L * X) :=
        mul_le_mul_of_nonneg_left (highScale_le hX hL hlo) (by positivity)
      _ = _ := by ring
  have hi' : c + i ≤ 5 * c * X ^ δ := by
    have hh := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 4 * c)
    have hh' := mul_le_mul_of_nonneg_left hr hc
    nlinarith
  have hi'' : L * X ^ (1 + δ) * (c + i) ≤ 5 * c * L * X * (X ^ δ) ^ 2 := by
    calc
      _ ≤ L * X ^ (1 + δ) * (5 * c * X ^ δ) := mul_le_mul_of_nonneg_left hi' (by positivity)
      _ = _ := by rw [hpow1]; ring
  have hh : zhigh ≤ 37 * B * c * L * X * (X ^ δ) ^ 2 := by
    have hh := hhigh.trans (mul_le_mul_of_nonneg_left (add_le_add hb' hi'') hB)
    have hh' := mul_le_mul_of_nonneg_left hr12 (by positivity : 0 ≤ 32 * c * L * X)
    nlinarith [mul_le_mul_of_nonneg_left hh' hB]
  have hl' : zlow ≤ 9 * A * c * L * X * (X ^ δ) ^ 2 :=
    hl.trans (by nlinarith [mul_le_mul_of_nonneg_left hr2 (by positivity : 0 ≤ 9 * A * c * L * X)])
  rw [hpow12]
  nlinarith

/-- Derived totient and epsilon bookkeeping after the sharp formula.
The exact totient factor is absorbed only through the proved ratio bound. -/
theorem arithmetic_mass_scalar {X δ A D C H q φ z m : ℝ} {L : ℕ}
    (hX : 1 ≤ X) (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hφ : 0 < φ) (hq : 0 ≤ q)
    (hratio : q / φ ≤ H * X ^ δ)
    (hz : z ≤ D * (C * q ^ 2 * X ^ δ) * L * X ^ (1 + 2 * δ))
    (hm : m ≤ A * X ^ δ * (z / φ ^ 2 + L * X ^ (1 + δ))) :
    m ≤ (A * (D * C * H ^ 2 + 1)) * L * X ^ (1 + 6 * δ) := by
  have hX0 : 0 < X := by linarith
  have hr : 1 ≤ X ^ δ := Real.one_le_rpow hX hδ
  have hr0 : 0 ≤ X ^ δ := by positivity
  have hpow1 : X ^ (1 + δ) = X * X ^ δ := by rw [Real.rpow_add hX0, Real.rpow_one]
  have hpow12 : X ^ (1 + 2 * δ) = X * (X ^ δ) ^ 2 := by
    rw [Real.rpow_add hX0, Real.rpow_one, mul_comm 2 δ, Real.rpow_mul hX0.le, Real.rpow_two]
  have hpow16 : X ^ (1 + 6 * δ) = X * (X ^ δ) ^ 6 := by
    rw [Real.rpow_add hX0, Real.rpow_one, mul_comm 6 δ, Real.rpow_mul hX0.le, Real.rpow_ofNat]
  have hratio2 : (q / φ) ^ 2 ≤ H ^ 2 * (X ^ δ) ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (div_nonneg hq hφ.le) hratio 2
  have hdiv : z / φ ^ 2 ≤ D * C * H ^ 2 * L * X * (X ^ δ) ^ 5 := by
    calc
      _ ≤ (D * (C * q ^ 2 * X ^ δ) * L * X ^ (1 + 2 * δ)) / φ ^ 2 :=
        div_le_div_of_nonneg_right hz (sq_nonneg _)
      _ = D * C * L * X * (X ^ δ) ^ 3 * (q / φ) ^ 2 := by rw [hpow12]; field_simp <;> ring
      _ ≤ D * C * L * X * (X ^ δ) ^ 3 * (H ^ 2 * (X ^ δ) ^ 2) :=
        mul_le_mul_of_nonneg_left hratio2 (by positivity)
      _ = _ := by ring
  have hr26 : (X ^ δ) ^ 2 ≤ (X ^ δ) ^ 6 := pow_le_pow_right₀ hr (by norm_num)
  have hh := hm.trans (mul_le_mul_of_nonneg_left
    (add_le_add hdiv (le_refl (L * X ^ (1 + δ)))) (by positivity : 0 ≤ A * X ^ δ))
  rw [hpow1] at hh
  rw [hpow16]
  have hh' := mul_le_mul_of_nonneg_left hr26 (by positivity : 0 ≤ A * L * X)
  nlinarith

/-- Derived interior version of the endpoint bookkeeping template.
The additional endpoint term is nonnegative and is not used to prove display 15. -/
theorem interior_high_zero_mass_extended :
    GRH → ∀ δ : ℝ, 0 < δ → ∃ A X0 : ℝ, 0 ≤ A ∧ 16 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X → ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q →
        ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X → ∀ L : ℕ, 0 < L →
          ∀ W c : ℝ, 1 ≤ W → W ≤ X ^ 2 → 0 ≤ c →
            (∀ u : ℝ, W ≤ u → u ≤ X ^ 2 → ‖F X u q a‖ ≤ c * u) →
              zeroMass X Y q a L 1 W (X ^ 2) ≤
                A * (X ^ (2 + δ) * correlationBracket X W (X ^ 2) q a +
                  L * X ^ (1 + δ) *
                    (c + (∫ u in W..(X ^ 2),
                      u ^ (-(3 : ℝ) / 2) * (c * u) ^ (1 / 2 : ℝ)) ^ 2)) := by
  intro hG δ hδ
  obtain ⟨A, X0, hA, hX0, h⟩ := interior_high_zero_mass hG δ hδ
  refine ⟨A, X0, hA, hX0, ?_⟩
  intro X hX q inst a ha Y hY hY2 L hL W c hW hWK hc hF
  have hh := h X hX q a ha Y hY hY2 L hL W hW hWK
  have hp : 0 ≤ L * X ^ (1 + δ) *
      (c + (∫ u in W..(X ^ 2), u ^ (-(3 : ℝ) / 2) * (c * u) ^ (1 / 2 : ℝ)) ^ 2) := by
    have hX0' : 0 ≤ X := by linarith
    positivity
  exact hh.trans (by nlinarith [mul_nonneg hA hp])

/-- Pages 355 through 359, the conditional window assembly for a fixed region.
The high band estimate is supplied separately for the interior and endpoints.
The correlation envelope comes from the statement's GMCxi hypothesis and
estimate 3. No individual primitive estimate is used as a cancellation bound.
CONDITIONAL ON the sharp formula, its window transfer and the two zero bands. -/
theorem region_window_bound (r : Fin 3)
    (hHigh : GRH → ∀ δ : ℝ, 0 < δ → ∃ A X0 : ℝ, 0 ≤ A ∧ 16 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X → ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q →
        ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X → ∀ L : ℕ, 0 < L →
          ∀ W c : ℝ, 1 ≤ W → W ≤ X ^ 2 → 0 ≤ c →
            (∀ u : ℝ, W ≤ u → u ≤ X ^ 2 → ‖F X u q a‖ ≤ c * u) →
              zeroMass X Y q a L r W (X ^ 2) ≤
                A * (X ^ (2 + δ) * correlationBracket X W (X ^ 2) q a +
                  L * X ^ (1 + δ) *
                    (c + (∫ u in W..(X ^ 2),
                      u ^ (-(3 : ℝ) / 2) * (c * u) ^ (1 / 2 : ℝ)) ^ 2))) :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → ∀ ξ : ℝ → ℕ → ℝ, GMCxi θ ξ →
      ∀ ε : ℝ, 0 < ε → ∃ B X0 : ℝ, 0 ≤ B ∧ ∀ X : ℝ, X0 ≤ X → 1 ≤ X →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X ^ θ → ∀ a : ℕ, Nat.Coprime a q →
          ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X →
            ∀ L : ℕ, 0 < L → 1 / (4 * (L : ℝ)) ≤ ξ X q →
              ξ X q ≤ 1 / (2 * (L : ℝ)) →
                regionMass X Y q a L r ≤ B * L * X ^ (1 + ε) := by
  intro θ hθ hθ2 ξ hG ε hε
  let δ := ε / 6
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, Xs, hA, hXs, hSharp⟩ :=
    sharp_window_comparison sharp_character_explicit_formula hG.1 δ hδ
  obtain ⟨B, hB, hLow⟩ := low_zero_mass hG.1
  obtain ⟨E, Xh, hE, hXh, hHigh'⟩ := hHigh hG.1 δ hδ
  obtain ⟨C, Xe, hC, hXe, hEnv⟩ := correlation_envelope hθ2 hG hδ
  obtain ⟨H, hH, hRatio⟩ := totient_ratio_le_rpow hδ
  obtain ⟨Xl, hLog⟩ := eventually_atTop.1 (eventually_log_sq_le_rpow hδ)
  let D := 2 * (9 * B + 37 * E)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨A * (D * C * H ^ 2 + 1), max 16 (max Xs (max Xh (max Xe Xl))), by positivity, ?_⟩
  intro X hX hX1 q inst hq a ha Y hY hY2 L hL hlo hhi
  have ht : 16 ≤ X ∧ Xs ≤ X ∧ Xh ≤ X ∧ Xe ≤ X ∧ Xl ≤ X := by
    simpa only [max_le_iff] using hX
  have hX2 : 2 ≤ X := by linarith [ht.1]
  have hXpos : 0 < X := by linarith
  have hqroot : (q : ℝ) ≤ X ^ (1 / 2 : ℝ) :=
    hq.trans (Real.rpow_le_rpow_of_exponent_le hX1 hθ2)
  have hqX : (q : ℝ) ≤ X := by
    simpa only [Real.rpow_one] using hq.trans
      (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith : θ ≤ 1))
  let W := lowHeight X (ξ X q)
  have hW := lowHeight_range hX2 (hG.2.1 X q).1 (hG.2.1 X q).2
  have hWpos : 0 < W := by dsimp [W]; linarith [hW.1]
  let c := C * (q : ℝ) ^ 2 * X ^ δ
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hF : ∀ u : ℝ, W ≤ u → u ≤ X ^ 2 → ‖F X u q a‖ ≤ c * u := by
    intro u hWu huK
    have hh := hEnv X ht.2.2.2.1 q hq a ha u (hW.2.1.trans hWu) huK
    convert hh using 1 <;> dsimp [c] <;> ring
  have hlow := hLow X ht.1 q a ha Y hY hY2 L hL r W hW.1
  have hhigh := hHigh' X ht.2.2.1 q a ha Y hY hY2 L hL W c hW.1 hW.2.2.2 hc hF
  have hz : zeroMass X Y q a L r (-1) (X ^ 2) ≤ D * c * L * X ^ (1 + 2 * δ) := by
    exact zero_mass_scalar hX2 hδ.le hL hlo hhi hc hB hE
      (hF W le_rfl hW.2.2.2)
      (correlationBracket_le hWpos hW.2.2.2 hc q a hF)
      (endpoint_integral_sq_le hX2 hW.1 hW.2.2.2 hc)
      (hLog X ht.2.2.2.2) hlow hhigh
      (zeroMass_split (by linarith [ht.1]) Y q a L r W (X ^ 2) hW.2.2.2)
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hratio : (q : ℝ) / q.totient ≤ H * X ^ δ :=
    (hRatio q (Nat.pos_of_ne_zero (NeZero.ne q))).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg q) hqX hδ.le) hH)
  have hh := arithmetic_mass_scalar hX1 hδ.le hA hD hC hH hφ (Nat.cast_nonneg q) hratio
    hz (hSharp X ht.2.1 q hqroot a ha Y hY hY2 L hL r)
  have hbudget : 6 * δ = ε := by dsimp [δ]; ring
  simpa only [hbudget] using hh

/-- Pages 356 through 359, displays 15, 16 and 23, exact interior target.
The parent has no admission. It remains CONDITIONAL ON the named analytic leaves. -/
theorem interior_window_bound_decomposed :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → ∀ ξ : ℝ → ℕ → ℝ, GMCxi θ ξ →
      ∀ ε : ℝ, 0 < ε → ∃ B X0 : ℝ, 0 ≤ B ∧ ∀ X : ℝ, X0 ≤ X → 1 ≤ X →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X ^ θ → ∀ a : ℕ, Nat.Coprime a q →
          ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X →
            ∀ L : ℕ, 0 < L → 1 / (4 * (L : ℝ)) ≤ ξ X q →
              ξ X q ≤ 1 / (2 * (L : ℝ)) →
                Window422.interiorMass X Y q a L ≤ B * L * X ^ (1 + ε) := by
  simpa only [regionMass_interior] using
    (region_window_bound 1 interior_high_zero_mass_extended)

/-- Pages 357 through 359, displays 17 through 19 and 23.
Assemble one endpoint from its fixed and moving contributions.
CONDITIONAL ON the named analytic leaves. -/
theorem endpoint_window_bound (r : Fin 3) (hr : r = 0 ∨ r = 2) :

    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → ∀ ξ : ℝ → ℕ → ℝ, GMCxi θ ξ →
      ∀ ε : ℝ, 0 < ε → ∃ B X0 : ℝ, 0 ≤ B ∧ ∀ X : ℝ, X0 ≤ X → 1 ≤ X →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X ^ θ → ∀ a : ℕ, Nat.Coprime a q →
          ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X →
            ∀ L : ℕ, 0 < L → 1 / (4 * (L : ℝ)) ≤ ξ X q →
              ξ X q ≤ 1 / (2 * (L : ℝ)) →
                regionMass X Y q a L r ≤ B * L * X ^ (1 + ε) := by
  apply region_window_bound r
  intro hG δ hδ
  obtain ⟨A, X0, hA, hX0, h⟩ := endpoint_high_zero_mass hG δ hδ
  refine ⟨A, X0, hA, hX0, ?_⟩
  intro X hX q inst a ha Y hY hY2 L hL W c hW hWK hc hF
  exact h X hX q a ha Y hY hY2 L hL r hr W c hW hWK hc hF

/-- Pages 356 through 359, exact leading target.
CONDITIONAL ON the named analytic leaves. -/
theorem leading_window_bound_decomposed :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → ∀ ξ : ℝ → ℕ → ℝ, GMCxi θ ξ →
      ∀ ε : ℝ, 0 < ε → ∃ B X0 : ℝ, 0 ≤ B ∧ ∀ X : ℝ, X0 ≤ X → 1 ≤ X →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X ^ θ → ∀ a : ℕ, Nat.Coprime a q →
          ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X →
            ∀ L : ℕ, 0 < L → 1 / (4 * (L : ℝ)) ≤ ξ X q →
              ξ X q ≤ 1 / (2 * (L : ℝ)) →
                Window422.leadingMass X Y q a L ≤ B * L * X ^ (1 + ε) := by
  simpa only [regionMass_leading] using (endpoint_window_bound 0 (Or.inl rfl))

/-- Pages 357 through 359, exact trailing target.
CONDITIONAL ON the named analytic leaves. -/
theorem trailing_window_bound_decomposed :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → ∀ ξ : ℝ → ℕ → ℝ, GMCxi θ ξ →
      ∀ ε : ℝ, 0 < ε → ∃ B X0 : ℝ, 0 ≤ B ∧ ∀ X : ℝ, X0 ≤ X → 1 ≤ X →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X ^ θ → ∀ a : ℕ, Nat.Coprime a q →
          ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X →
            ∀ L : ℕ, 0 < L → 1 / (4 * (L : ℝ)) ≤ ξ X q →
              ξ X q ≤ 1 / (2 * (L : ℝ)) →
                Window422.trailingMass X Y q a L ≤ B * L * X ^ (1 + ε) := by
  simpa only [regionMass_trailing] using (endpoint_window_bound 2 (Or.inr rfl))

end LeanLab.LanguascoPerelli1996.Decomp545a

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.eventually_log_le_rpow
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.eventually_log_cube_le_sqrt
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.modulus_in_estimate3_range
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.correlation_envelope

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.totient_ratio_eq_product
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.totient_ratio_le_rpow

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.zeroPrimitive
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.lowerEndpoint
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.clippedEndpoint
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.zeroWindow
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.cells
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.regionMass
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.zeroMass
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.regionMass_leading
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.regionMass_interior
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.regionMass_trailing
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.zeroPrimitive_split
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.zeroWindow_split
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.continuous_zeroPrimitive_comp
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.lowerEndpoint_pos
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.continuous_zeroWindow
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.zeroMass_split

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.correlationBracket
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.correlationBracket_le
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.lowHeight
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.lowScale
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.lowHeight_range
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.lowScale_height_le
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.highScale_le
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.endpoint_integral_sq_le

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.zero_term_hasDerivAt
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.zeroPrimitive_hasDerivAt

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.eventually_log_sq_le_rpow
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.rounded_model_instance

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.sharp_character_explicit_formula
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.sharp_window_comparison
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.low_zero_mass
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.interior_high_zero_mass
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.endpoint_high_zero_mass

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.zero_mass_scalar
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.arithmetic_mass_scalar

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.interior_high_zero_mass_extended
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.region_window_bound

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.interior_window_bound_decomposed
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.endpoint_window_bound
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.leading_window_bound_decomposed
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.trailing_window_bound_decomposed

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.correlation_change_center

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.zeroPrimitive_same
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.zeroMass_same

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.originalPolynomial
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.primitivePolynomial
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.primitiveCorrection
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.stopped_primitive_reduction
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.stopped_primitive_expansion
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.individual_primitive_error

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.moving_integral_mass

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.interval_norm_sq_le

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.integral_clipped

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.zeroDerivative
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.stoppedZeroDerivative
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.continuous_zeroDerivative
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.stoppedZeroDerivative_integrable
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.zeroWindow_eq_integral

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.region_integral_le

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.rounded_support_bounds
#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.stoppedZeroDerivative_mass

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.height_weighted_mass

#print axioms LeanLab.LanguascoPerelli1996.Decomp545a.reciprocal_band_mass
