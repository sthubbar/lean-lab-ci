/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130.
Task556 splits the written range weighted mean square into displays 28 and 32.
The major contribution is defined as the exact representation minus the minor coefficient.
The finite Fourier identification is proved below. The analytic estimate remains a LEAF.
No import of Decomp516a or a module importing it occurs here.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp1534a
import LeanLab.KumchevLiu2007.Decomp1534c
import LeanLab.KumchevLiu2007.Decomp506a
import Mathlib.Analysis.Fourier.AddCircle

namespace LeanLab.KumchevLiu2007.Task556a

open Real Complex MeasureTheory LeanLab.KumchevLiu2007
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- Numerical notation for P0088 pages 8 and 15, displays 33 and 34. -/
noncomputable def windowY (X ε : ℝ) : ℝ := X ^ (7 / 12 + ε / 2)

/-- Numerical notation for P0088 pages 8 and 15, displays 33 and 34. -/
noncomputable def windowPairs (X Y : ℝ) (n : ℕ) : Finset (ℕ × ℕ) := ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter (fun v => X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧ Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt Y ∧ v.1 + v.2 ^ 2 = n)

/-- Numerical notation for P0088 pages 8 and 15, displays 33 and 34. -/
noncomputable def series2 (n : ℕ) (P : ℝ) : ℂ := ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q

/-- Numerical notation for P0088 pages 8 and 15, displays 33 and 34. -/
noncomputable def roughCount (X Y P : ℝ) (n : ℕ) : ℕ := ((windowPairs X Y n).filter (fun v => v.1.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ v.2 → Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ))).card

/-- Numerical notation for P0088 pages 8 and 15, displays 33 and 34. -/
noncomputable def f2Weight (z0 u : ℝ) : ℝ := 1 / Real.log u + ∫ t in z0..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t))

/-- Numerical notation for P0088 pages 8 and 15, displays 33 and 34. -/
noncomputable def singInt (X Y P : ℝ) (n : ℕ) : ℝ := ∑ v ∈ windowPairs X Y n, (1 / Real.log (v.1 : ℝ)) * f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (v.2 : ℝ)

/-- Numerical notation for P0088 pages 8 and 15, displays 33 and 34. -/
noncomputable def err53 (X ε B : ℝ) (n : ℕ) : ℝ := ‖(roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) - series2 n (Real.log X ^ B) * (singInt X (windowY X ε) (Real.log X ^ B) n : ℂ)‖
/-- Page 2 intervals 5 and page 8 display 34, before imposing the representation equation. -/
noncomputable def roughPairs (X Y P : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
    (fun v => X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
      Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt Y ∧
      v.1.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ v.2 →
        Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ))

/-- Page 4 display 13, the finite exponential polynomial for the rough representation. -/
noncomputable def representationPolynomial (X Y P : ℝ) (α : AddCircle (1 : ℝ)) : ℂ :=
  ∑ v ∈ roughPairs X Y P, fourier (v.1 + v.2 ^ 2 : ℕ) α

/-- Page 4 displays 14 and 15, periodic closed major arcs on the real line. -/
noncomputable def majorArcs (H P : ℝ) : Set ℝ :=
  {α | ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ P ∧ ∃ a : ℤ,
    IsCoprime a (q : ℤ) ∧ |(q : ℝ) * α - a| ≤ (H / P)⁻¹}

/-- Page 8 display 32, the minor arc Fourier coefficient on one full period. -/
noncomputable def minorCoefficient (X Y H P : ℝ) (n : ℕ) : ℂ :=
  ∫ α in Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H P)ᶜ,
    fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
      representationPolynomial X Y P (α : AddCircle (1 : ℝ))

/-- Page 7 display 28, major contribution as the exact total minus the minor coefficient. -/
noncomputable def majorError (X Y H P : ℝ) (n : ℕ) : ℂ :=
  (roughCount X Y P n : ℂ) - minorCoefficient X Y H P n -
    series2 n P * (singInt X Y P n : ℂ)

/-- Page 8 display 33, the integers in the mean square. -/
noncomputable def intervalNumbers (X H : ℝ) : Finset ℕ :=
  (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ))

/-- Page 4 display 12, the rough representation count as a fiber cardinal. -/
theorem roughCount_eq_fiber_card (X Y P : ℝ) (n : ℕ) :
    roughCount X Y P n =
      ((roughPairs X Y P).filter (fun v => v.1 + v.2 ^ 2 = n)).card := by
  unfold roughCount
  congr 1
  ext v
  simp only [windowPairs, roughPairs, Finset.mem_filter]
  tauto

/-- Page 4 display 13, exact Fourier inversion for the finite representation polynomial. -/
theorem representationPolynomial_fourierCoeff (X Y P : ℝ) (n : ℕ) :
    fourierCoeff (representationPolynomial X Y P) (n : ℤ) = (roughCount X Y P n : ℂ) := by
  have hf : representationPolynomial X Y P =
      ∑ v ∈ roughPairs X Y P,
        (fourier ((v.1 + v.2 ^ 2 : ℕ) : ℤ) : AddCircle (1 : ℝ) → ℂ) := by
    ext α
    simp [representationPolynomial]
  rw [hf, fourierCoeff.sum]
  · simp only [Finset.sum_apply, fourierCoeff_fourier, Pi.single_apply]
    rw [roughCount_eq_fiber_card]
    simp
    congr 1
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hv, he⟩
      exact ⟨hv, by exact_mod_cast he.symm⟩
    · rintro ⟨hv, he⟩
      exact ⟨hv, by exact_mod_cast he.symm⟩
  · intro v hv
    exact (fourier ((v.1 + v.2 ^ 2 : ℕ) : ℤ)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Page 4 display 15: the periodic major arc set is measurable. -/
theorem measurableSet_majorArcs (H P : ℝ) : MeasurableSet (majorArcs H P) := by
  have he : majorArcs H P = ⋃ q : ℕ, ⋃ (_ : 1 ≤ q), ⋃ (_ : (q : ℝ) ≤ P),
      ⋃ a : ℤ, ⋃ (_ : IsCoprime a (q : ℤ)),
        {α : ℝ | |(q : ℝ) * α - a| ≤ (H / P)⁻¹} := by
    ext α
    simp [majorArcs, and_left_comm]
  rw [he]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun a =>
      MeasurableSet.iUnion fun _ => ?_
  have hc : Continuous (fun α : ℝ => |(q : ℝ) * α - a|) := by fun_prop
  exact (isClosed_le hc continuous_const).measurableSet

/-- Page 4 display 13: the finite exponential polynomial is continuous on the real line. -/
theorem continuous_representationPolynomial (X Y P : ℝ) :
    Continuous (fun α : ℝ => representationPolynomial X Y P (α : AddCircle (1 : ℝ))) := by
  unfold representationPolynomial
  exact continuous_finsetSum _ fun v _ =>
    (fourier ((v.1 + v.2 ^ 2 : ℕ) : ℤ)).continuous.comp (AddCircle.continuous_mk' 1)

/-- Page 4 display 13 in the real unit interval integral convention. -/
theorem totalCoefficient_eq_count (X Y P : ℝ) (n : ℕ) :
    (∫ α in Set.Ioc (0 : ℝ) 1,
      fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
        representationPolynomial X Y P (α : AddCircle (1 : ℝ))) =
      (roughCount X Y P n : ℂ) := by
  have hf := representationPolynomial_fourierCoeff X Y P n
  rw [fourierCoeff_eq_intervalIntegral _ _ 0] at hf
  simpa only [div_self (by norm_num : (1 : ℝ) ≠ 0), zero_add, one_smul,
    smul_eq_mul, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hf

/-- Pages 4 and 7 displays 13, 15 and 28: the complement definition of majorError
is exactly the major arc integral minus the singular main term. -/
theorem majorError_eq_major_integral (X Y H P : ℝ) (n : ℕ) :
    majorError X Y H P n =
      (∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs H P,
        fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
          representationPolynomial X Y P (α : AddCircle (1 : ℝ))) -
        series2 n P * (singInt X Y P n : ℂ) := by
  have hc : Continuous (fun α : ℝ =>
      fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
        representationPolynomial X Y P (α : AddCircle (1 : ℝ))) :=
    ((fourier (-(n : ℤ))).continuous.comp (AddCircle.continuous_mk' 1)).mul
      (continuous_representationPolynomial X Y P)
  have hs := integral_inter_add_sdiff (measurableSet_majorArcs H P)
    (hc.integrableOn_Ioc (μ := volume) (a := 0) (b := 1))
  rw [Set.sdiff_eq, totalCoefficient_eq_count X Y P n] at hs
  unfold majorError minorCoefficient
  linear_combination -hs

/-- The cancellation free pointwise estimate for the page 4 representation polynomial. -/
theorem representationPolynomial_norm_le_card (X Y P : ℝ) (α : AddCircle (1 : ℝ)) :
    ‖representationPolynomial X Y P α‖ ≤ (roughPairs X Y P).card := by
  unfold representationPolynomial
  calc
    _ ≤ ∑ v ∈ roughPairs X Y P, ‖fourier ((v.1 + v.2 ^ 2 : ℕ) : ℤ) α‖ := norm_sum_le _ _
    _ = _ := by simp [fourier_apply, Circle.norm_coe]

/-- The cancellation free minor coefficient estimate. It supplies no logarithmic saving. -/
theorem minorCoefficient_norm_le_card (X Y H P : ℝ) (n : ℕ) :
    ‖minorCoefficient X Y H P n‖ ≤ (roughPairs X Y P).card := by
  let s := Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H P)ᶜ
  have hs : volume s ≤ 1 := by
    calc volume s ≤ volume (Set.Ioc (0 : ℝ) 1) := measure_mono Set.inter_subset_left
         _ = 1 := by simp
  have hsfin : volume s < ⊤ := lt_of_le_of_lt hs (by simp)
  have hsreal : volume.real s ≤ 1 := by
    simpa only [measureReal_def, ENNReal.toReal_one] using ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤) hs
  unfold minorCoefficient
  calc
    _ ≤ (roughPairs X Y P).card * volume.real s := by
      apply norm_setIntegral_le_of_norm_le_const hsfin
      intro α hα
      rw [norm_mul, fourier_apply, Circle.norm_coe, one_mul]
      exact representationPolynomial_norm_le_card X Y P _
    _ ≤ (roughPairs X Y P).card * 1 :=
      mul_le_mul_of_nonneg_left hsreal (by positivity)
    _ = _ := mul_one _

/-- The finite mean square available from absolute values alone. This bound is
weaker than page 8 display 32 and does not replace its analytic leaf. -/
theorem minor_mean_square_absolute (X Y H P : ℝ) :
    (∑ n ∈ intervalNumbers X H, ‖minorCoefficient X Y H P n‖ ^ 2) ≤
      ((intervalNumbers X H).card : ℝ) * ((roughPairs X Y P).card : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ _n ∈ intervalNumbers X H, ((roughPairs X Y P).card : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (minorCoefficient_norm_le_card X Y H P n)
    _ = _ := by simp

/-- Page 16 written H range forces epsilon at most 11/36 when X exceeds one. -/
theorem written_range_epsilon_le {X H ε : ℝ} (hX : 1 < X)
    (hl : X ^ (7 / 18 + ε) ≤ H) (hu : H ≤ X ^ (1 - ε)) :
    ε ≤ 11 / 36 := by
  have he := (Real.rpow_le_rpow_left_iff hX).mp (hl.trans hu)
  linarith

/-- Page 15 Lemma 3.4 parameter conversion has a positive epsilon power margin. -/
theorem short_square_exponent_margin {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 11 / 36) :
    (7 / 12 + ε / 2) * (2 / 3 + ε / 2) ≤ 7 / 18 + ε - ε / 4 := by
  nlinarith [mul_nonneg hε (show 0 ≤ 1 / 2 - ε by linarith)]

/-- Page 15 condition theta2 at least 2/3 plus a positive epsilon is available
from the page 16 written lower bound for H. -/
theorem window_power_le_H {X H ε : ℝ} (hX : 1 < X) (hε : 0 < ε)
    (hl : X ^ (7 / 18 + ε) ≤ H) (hu : H ≤ X ^ (1 - ε)) :
    windowY X ε ^ (2 / 3 + ε / 2) ≤ H := by
  rw [windowY, ← Real.rpow_mul (by linarith : 0 ≤ X)]
  apply le_trans (Real.rpow_le_rpow_of_exponent_le hX.le ?_) hl
  have hm := short_square_exponent_margin hε.le (written_range_epsilon_le hX hl hu)
  linarith

/-- Page 2 display 5, the prime interval. -/
noncomputable def primeWindow (X Y : ℝ) : Finset ℕ :=
  (Finset.range (⌊X⌋₊ + 1)).filter (fun m : ℕ => X - Y ≤ (m : ℝ) ∧ (m : ℝ) < X)

/-- Page 2 display 5, the square root interval. -/
noncomputable def squareWindow (Y : ℝ) : Finset ℕ :=
  (Finset.range (⌊Real.sqrt Y⌋₊ + 1)).filter
    (fun m : ℕ => Real.sqrt Y / 2 ≤ (m : ℝ) ∧ (m : ℝ) < Real.sqrt Y)

/-- Page 4 display 10, the rough number indicator. -/
noncomputable def roughWeight (z : ℝ) (m : ℕ) : ℂ :=
  if ∀ p : ℕ, p.Prime → p ∣ m → z ≤ (p : ℝ) then 1 else 0

/-- Page 4 display 10 and page 15 support verification: the rough weight is bounded by one. -/
theorem roughWeight_norm_le_one (z : ℝ) (m : ℕ) : ‖roughWeight z m‖ ≤ 1 := by
  unfold roughWeight
  split_ifs <;> simp

/-- Page 4 display 10: a prime divisor below the cutoff forces the rough weight to vanish. -/
theorem roughWeight_eq_zero_of_small_prime {z : ℝ} {m p : ℕ}
    (hp : p.Prime) (hd : p ∣ m) (hz : (p : ℝ) < z) : roughWeight z m = 0 := by
  unfold roughWeight
  split_ifs with h
  · exact False.elim ((not_le_of_gt hz) (h p hp hd))
  · rfl

/-- Page 15 verification of A2.1: a nonzero rough weight is coprime to each
positive modulus below its cutoff. -/
theorem roughWeight_coprime {z : ℝ} {m q : ℕ} (hq : 0 < q) (hz : (q : ℝ) < z)
    (hm : roughWeight z m ≠ 0) : m.Coprime q := by
  by_contra hn
  obtain ⟨p, hp, hpm, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd hq hpq
  exact hm (roughWeight_eq_zero_of_small_prime hp hpm (hpq'.trans_lt hz))

/-- Page 15 support verification of A2.1: the rough cutoff eventually exceeds P. -/
theorem logPower_lt_roughCutoff (B ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop, Real.log X ^ B <
      windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) := by
  let e := (7 / 12 + ε / 2) / 4
  have he : 0 < e := by dsimp [e]; positivity
  have ht := (isLittleO_log_rpow_rpow_atTop (3 * B) he).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [ht, Filter.eventually_gt_atTop (1 : ℝ)] with X hsmall hX
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX
  have hP : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL _
  have hy : 0 < X ^ e := Real.rpow_pos_of_pos hX0 _
  have hsmall' : Real.log X ^ (3 * B) ≤ (1 / 2 : ℝ) * X ^ e := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL (3 * B)), abs_of_pos hy] using hsmall
  have hpow : (Real.log X ^ B) ^ (3 : ℕ) < windowY X ε ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le, windowY, ← Real.rpow_mul hX0.le]
    have heq : (7 / 12 + ε / 2) * (1 / 4 : ℝ) = e := by dsimp [e]; ring
    rw [heq]
    norm_num only [Nat.cast_ofNat]
    rw [mul_comm B (3 : ℝ)]
    linarith
  rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv]
  apply (lt_div_iff₀ (sq_pos_of_pos hP)).mpr
  nlinarith [hpow]

/-- Page 15 A2.1 support in every logarithmic modulus, with no cited analytic input. -/
theorem roughWeight_eventually_coprime (B ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ m : ℕ, roughWeight (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) m ≠ 0 →
        m.Coprime q := by
  filter_upwards [logPower_lt_roughCutoff B ε hε] with X hcut q hq hqP m hm
  exact roughWeight_coprime hq (hqP.trans_lt hcut) hm

/-- Page 5 hypothesis A1.2, the character defect on a subinterval of I1. -/
noncomputable def primeCharacterDefect {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X Y u v : ℝ) : ℂ :=
  ∑ m ∈ (primeWindow X Y).filter (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v),
    ((if m.Prime then (1 : ℂ) else 0) -
      (if χ = 1 then ((1 / Real.log (m : ℝ) : ℝ) : ℂ) else 0)) * χ m

/-- Page 5 hypothesis A2.2, the squared interval character defect. -/
noncomputable def roughCharacterDefect {q : ℕ} (χ : DirichletCharacter ℂ q)
    (Y P δ t : ℝ) : ℂ :=
  ∑ m ∈ (squareWindow Y).filter
      (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t),
    (roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m -
      (if χ = 1 then (f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℂ)
       else 0)) * χ m

/-- LEAF. P0088 page 15, first paragraph of Section 4, supplying page 5
hypothesis A1.2 for the prime weight. The source invokes the short interval
Siegel Walfisz argument at theta1 greater than 7/12. This is not the long
interval theorem already formalized elsewhere in the lab. -/
theorem prime_short_interval_character (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hε1 : ε ≤ 11 / 36) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, ∀ u v : ℝ,
        X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        ‖primeCharacterDefect χ X (windowY X ε) u v‖ ≤
          C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) := by
  sorry

/-- LEAF. P0088 page 15, first paragraph of Section 4, supplying page 5
hypothesis A2.2 for the rough weight and the displayed f2. The interval
parameter is restricted to 0 < delta <= q Q divided by Y. Here Q = H/P
is page 4 display 14. The written H range is page 16 after display 55. -/
theorem rough_short_interval_character (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, ∀ δ : ℝ,
        0 < δ → δ ≤ (q : ℝ) * (H / Real.log X ^ B) / windowY X ε →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖roughCharacterDefect χ (windowY X ε) (Real.log X ^ B) δ t‖ ^ 2) ≤
            C * ((q : ℝ) * (H / Real.log X ^ B)) ^ 2 *
              (Real.log X ^ B) ^ (-4 : ℤ) := by
  sorry

/-- Page 7 hypothesis A2.3, the rough short quadratic exponential sum. -/
noncomputable def roughShortSum (Y P H α t : ℝ) : ℂ :=
  ∑ m ∈ (squareWindow Y).filter
      (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
    roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m *
      fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))

/-- LEAF. P0088 page 11 Lemma 3.4, applied to the two sums of page 15
display 52. The conclusion is precisely the rough weight A2.3 of page 7.
The written range is page 16 after display 55. The two specialized bilinear
estimates, Buchstab identity and parameter conversion remain within this leaf. -/
theorem lemma34_rough_minor_input (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

end LeanLab.KumchevLiu2007.Task556a
