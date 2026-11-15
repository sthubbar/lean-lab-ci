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

/-- LEAF. The contour argument has a finite limit from above at every positive
cutoff. Trudgian page 1 inclusive height convention and page 3 display 2.3.
This is endpoint regularity only and gives no bound for the limit.
-/
theorem argument_right_limit576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {T : ℝ} (hT : 1 ≤ T) :
    ∃ A : ℝ, Tendsto (argument576 χ) (𝓝[>] T) (𝓝 A) := by
  sorry

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
