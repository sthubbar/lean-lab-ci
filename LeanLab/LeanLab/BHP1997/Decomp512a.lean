/-
P0069 Baker Harman Pintz 1997, Section 2, pages 5 to 10.
The Fourier identity and the partition are elementary. The major and minor
arc estimates remain separate cited analytic leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Thm2Sing
import LeanLab.HeathBrown1985.DivisorEps
import LeanLab.BHP1997.Route512Large
import LeanLab.BHP1997.Route512Kernel
import LeanLab.BHP1997.Route512Moment
import LeanLab.BHP1997.Route512Small
import LeanLab.BHP1997.Route512Eta
import LeanLab.BHP1997.Route512MajorFinal

namespace LeanLab.BHP1997.Section2MS
open Classical Complex Thm2 MeasureTheory Set
open scoped ComplexConjugate

/-- P0069 Baker Harman Pintz 1997, Section 2, page 6, the display after 2.1:
Σ_{2n ∈ K} |∫_{1/Q}^{1+1/Q} S₁S₂e(-2nα)dα - uvY/(ℒℒ') 𝔖(2n)|² ≪ H Y² ℒ^{-A-7}, for every
A > 0, with K = [x, x + H] and H = x^{θ₁θ₂} = Y^{θ₂}. The integral is written as the
convolution it equals by orthogonality. -/
def MeanSquare (ε : ℝ) (a b : ℝ → ℕ → ℂ) (u v : ℝ) : Prop :=
  let θ₁ : ℝ := 11 / 20 + ε
  let θ₂ : ℝ := 2 * (1 / 16 - 1 / 10 ^ 5)
  let Y : ℝ → ℝ := fun x => x ^ θ₁
  let I : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊x - 2 * Y x⌋₊ ⌊x⌋₊
  let J : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊Y x⌋₊ ⌊2 * Y x⌋₊
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
    ∑ N ∈ (Finset.Icc ⌈x⌉₊ ⌊x + x ^ (θ₁ * θ₂)⌋₊).filter (fun N : ℕ => Even N),
      ‖(∑ k ∈ I x, ∑ m ∈ J x, if k + m = N then a x k * b x m else 0) -
          u * v * Y x / (Real.log x * Real.log (Y x)) * sing (N / 2)‖ ^ 2 ≤
      C * x ^ (θ₁ * θ₂) * Y x ^ 2 * Real.log x ^ (-A - 7)

/-- P0069 Baker Harman Pintz 1997, page 3, Theorem 2 with an arbitrary conclusion `P`:
the hypotheses i to iv copied verbatim from `Thm2.Theorem2`. With `P = Conclusion` it is
`Thm2.Theorem2` itself, see `theorem2_iff_with`. -/
def Theorem2With (ε B : ℝ)
    (P : (ℝ → ℕ → ℂ) → (ℝ → ℕ → ℂ) → ℝ → ℝ →
      (ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q)) → Prop) : Prop :=
  ∀ (a b : ℝ → ℕ → ℂ) (u v : ℝ) (E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q)),
    let θ₁ : ℝ := 11 / 20 + ε
    let θ₂ : ℝ := 2 * (1 / 16 - 1 / 10 ^ 5)
    let Y : ℝ → ℝ := fun x => x ^ θ₁
    let Q : ℝ → ℕ := fun x => ⌊(Y x ^ θ₂) ^ (1 / 2 : ℝ) / 2⌋₊
    let I : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊x - 2 * Y x⌋₊ ⌊x⌋₊
    let J : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊Y x⌋₊ ⌊2 * Y x⌋₊
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
        ‖∑ k ∈ (I x).filter (fun k : ℕ => (k : ℝ) ≤ t),
          (a x k * χ (k : ZMod q) - delta χ * u / Real.log x)‖ ≤ C * Y x * Real.log x ^ (-A)) →
    (∃ C : ℝ, ∀ x k, ‖a x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B ∧
      ‖b x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
      Nat.gcd k (primorialBelow (Real.log x ^ A)) ≠ 1 → a x k = 0) →
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ 2 * Y x →
        ‖∑ m ∈ (J x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (b x m * χ (m : ZMod q) - delta χ * v / Real.log (Y x))‖ ≤
            C * Y x * Real.log x ^ (-A)) →
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ Q x →
      ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
      ∀ z : ℝ, (q * Q x : ℝ) / (6 * Y x) ≤ z → z ≤ 6 * q * Q x / Y x →
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
          ∫ y in (Y x / 2)..(3 * Y x),
            ‖∑ m ∈ (J x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (b x m * χ (m : ZMod q) - delta χ * v / Real.log (Y x))‖ ^ 2 ≤
          C * ((q : ℝ) * Q x) ^ 2 * Y x * Real.log x ^ (-A)) →
    P a b u v E

/-- P0069 page 1: the long interval length Y. -/
noncomputable def length512 (ε x : ℝ) : ℝ := x ^ (11 / 20 + ε)

/-- P0069 page 3: the Farey order Q. -/
noncomputable def order512 (ε x : ℝ) : ℕ :=
  ⌊(length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) / 2⌋₊

/-- P0069 page 5: a complete period starting at 1/Q. -/
noncomputable def period512 (ε x : ℝ) : Set ℝ :=
  Ioc (1 / (order512 ε x : ℝ)) (1 + 1 / (order512 ε x : ℝ))

/-- P0069 page 5: the major arcs with half width log x to power 4D divided by qY.
Clipping to the complete period is harmless for sufficiently large x. -/
noncomputable def major512 (ε D x : ℝ) : Set ℝ :=
  period512 ε x ∩ ⋃ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
    ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
      Icc ((r : ℝ) / q - Real.log x ^ (4 * D) / (q * length512 ε x))
          ((r : ℝ) / q + Real.log x ^ (4 * D) / (q * length512 ε x))

/-- P0069 page 5: the minor arcs are the complement inside the complete period. -/
noncomputable def minor512 (ε D x : ℝ) : Set ℝ := period512 ε x \ major512 ε D x

/-- P0069 page 5: S with its finite support displayed. -/
noncomputable def polynomial512 (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ S, a k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))

/-- P0069 page 5: S1 S2 e at frequency minus N. -/
noncomputable def integrand512 (ε x : ℝ) (a b : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t *
    polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t *
      @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))

/-- P0069 page 6: the expected main term in 2.2. -/
noncomputable def expected512 (ε x u v : ℝ) (N : ℕ) : ℂ :=
  u * v * length512 ε x / (Real.log x * Real.log (length512 ε x)) * sing (N / 2)

/-- P0069 page 6: the even frequencies in K. -/
noncomputable def frequencies512 (ε x : ℝ) : Finset ℕ :=
  (Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
    (fun N => Even N)

/-- P0069 page 5: both arc sets are measurable. -/
theorem measurable_major512 (ε D x : ℝ) : MeasurableSet (major512 ε D x) := by
  unfold major512 period512
  apply measurableSet_Ioc.inter
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun _ => measurableSet_Icc

/-- P0069 page 5: the complement defining the minor arcs is measurable. -/
theorem measurable_minor512 (ε D x : ℝ) : MeasurableSet (minor512 ε D x) := by
  exact measurableSet_Ioc.diff (measurable_major512 ε D x)

/-- P0069 page 5: the two arc sets partition a complete period. -/
theorem arc_partition512 (ε D x : ℝ) :
    major512 ε D x ∪ minor512 ε D x = period512 ε x := by
  exact union_sdiff_cancel (inter_subset_left : major512 ε D x ⊆ period512 ε x)

/-- P0069 page 5: the two arc sets are disjoint. -/
theorem arc_disjoint512 (ε D x : ℝ) : Disjoint (major512 ε D x) (minor512 ε D x) := by
  exact disjoint_sdiff_right

/-- P0069 page 5: each finite exponential polynomial is continuous. -/
theorem continuous_polynomial512 (S : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (polynomial512 S a) := by
  unfold polynomial512
  exact continuous_finsetSum S fun k hk => continuous_const.mul
    ((map_continuous (fourier (T := (1 : ℝ)) (k : ℤ))).comp (AddCircle.continuous_mk' 1))

/-- P0069 page 5: the Fourier integrand is continuous. -/
theorem continuous_integrand512 (ε x : ℝ) (a b : ℕ → ℂ) (N : ℕ) :
    Continuous (integrand512 ε x a b N) := by
  exact ((continuous_polynomial512 _ _).mul (continuous_polynomial512 _ _)).mul
    ((map_continuous (fourier (T := (1 : ℝ)) (-(N : ℤ)))).comp
      (AddCircle.continuous_mk' 1))

/-- P0069 page 5: the integrand is integrable over the complete period. -/
theorem integrable_period512 (ε x : ℝ) (a b : ℕ → ℂ) (N : ℕ) :
    IntegrableOn (integrand512 ε x a b N) (period512 ε x) := by
  exact (continuous_integrand512 ε x a b N).integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- P0069 page 6: split the Fourier coefficient over the two disjoint arc sets. -/
theorem integral_arc_partition512 (ε D x : ℝ) (a b : ℕ → ℂ) (N : ℕ) :
    (∫ t in period512 ε x, integrand512 ε x a b N t) =
      (∫ t in major512 ε D x, integrand512 ε x a b N t) +
        ∫ t in minor512 ε D x, integrand512 ε x a b N t := by
  rw [← arc_partition512 ε D x]
  apply setIntegral_union (arc_disjoint512 ε D x) (measurable_minor512 ε D x)
  · exact (integrable_period512 ε x a b N).mono_set inter_subset_left
  · exact (integrable_period512 ε x a b N).mono_set sdiff_subset

/-- P0069 page 5: integer exponentials are orthogonal on any complete period. -/
theorem integral_fourier512 (n : ℤ) (c : ℝ) :
    (∫ t in c..c + 1, @fourier 1 n (t : AddCircle (1 : ℝ))) = if n = 0 then 1 else 0 := by
  have h := fourierCoeff_eq_intervalIntegral (T := (1 : ℝ)) (@fourier 1 n) 0 c
  simp only [one_div_one, one_smul, fourier_zero] at h
  rw [fourierCoeff_fourier] at h
  simpa [Pi.single_apply, eq_comm] using h.symm

/-- P0069 page 6: the elementary square bound used to combine 2.2 and 2.3. -/
theorem norm_add_square512 (z w : ℂ) :
    ‖z + w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have h := norm_add_le z w
  have hh : ‖z + w‖ ^ 2 ≤ (‖z‖ + ‖w‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

/-- P0069 page 6: add the two mean square bounds with the factor from Cauchy. -/
theorem combine_square512 (S : Finset ℕ) (f g main : ℕ → ℂ) (U V : ℝ)
    (hmajor : ∑ N ∈ S, ‖f N - main N‖ ^ 2 ≤ U)
    (hminor : ∑ N ∈ S, ‖g N‖ ^ 2 ≤ V) :
    ∑ N ∈ S, ‖f N + g N - main N‖ ^ 2 ≤ 2 * U + 2 * V := by
  calc
    _ ≤ ∑ N ∈ S, (2 * ‖f N - main N‖ ^ 2 + 2 * ‖g N‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro N hN
      convert norm_add_square512 (f N - main N) (g N) using 1 <;> congr 2 <;> ring
    _ = 2 * (∑ N ∈ S, ‖f N - main N‖ ^ 2) + 2 * (∑ N ∈ S, ‖g N‖ ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := by linarith

/-- P0069 page 5: expand the product and add its integer frequencies. -/
theorem polynomial_product512 (S T : Finset ℕ) (a b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    polynomial512 S a t * polynomial512 T b t * @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ)) =
      ∑ k ∈ S, ∑ m ∈ T, (a k * b m) *
        @fourier 1 ((k : ℤ) + (m : ℤ) - (N : ℤ)) (t : AddCircle (1 : ℝ)) := by
  simp only [polynomial512, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro m hm
  rw [sub_eq_add_neg, fourier_add, fourier_add]
  ring

/-- P0069 page 5: orthogonality converts the integral to the exact convolution. -/
theorem convolution_integral512 (S T : Finset ℕ) (a b : ℕ → ℂ) (N : ℕ) (c : ℝ) :
    (∫ t in c..c + 1, polynomial512 S a t * polynomial512 T b t *
      @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) =
        ∑ k ∈ S, ∑ m ∈ T, if k + m = N then a k * b m else 0 := by
  have hc (k m : ℕ) : Continuous (fun t : ℝ => (a k * b m) *
      @fourier 1 ((k : ℤ) + (m : ℤ) - (N : ℤ)) (t : AddCircle (1 : ℝ))) :=
    continuous_const.mul ((map_continuous (fourier _)).comp (AddCircle.continuous_mk' 1))
  simp_rw [polynomial_product512]
  rw [intervalIntegral.integral_finsetSum (fun k hk =>
    (continuous_finsetSum T fun m hm => hc k m).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [intervalIntegral.integral_finsetSum (fun m hm => (hc k m).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [intervalIntegral.integral_const_mul, integral_fourier512]
  have he : (k : ℤ) + (m : ℤ) - (N : ℤ) = 0 ↔ k + m = N := by omega
  simp [he]

/-- P0069 page 5: the actual Fourier integrals over the arc partition sum to the
convolution, with no analytic hypothesis. -/
theorem convolution_arcs512 (ε D x : ℝ) (a b : ℕ → ℂ) (N : ℕ) :
    (∑ k ∈ Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊,
      ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
        if k + m = N then a k * b m else 0) =
      (∫ t in major512 ε D x, integrand512 ε x a b N t) +
        ∫ t in minor512 ε D x, integrand512 ε x a b N t := by
  rw [← integral_arc_partition512]
  unfold period512
  rw [← intervalIntegral.integral_of_le (by linarith :
    1 / (order512 ε x : ℝ) ≤ 1 + 1 / (order512 ε x : ℝ))]
  simpa only [integrand512, add_comm (1 : ℝ)] using
    (convolution_integral512 _ _ a b N (1 / (order512 ε x : ℝ))).symm

/-- P0069 page 6 display 2.2: the major arc mean square as a real quantity. -/
noncomputable def majorError512 (ε D x : ℝ) (a b : ℕ → ℂ) (u v : ℝ) : ℝ :=
  ∑ N ∈ frequencies512 ε x,
    ‖(∫ t in major512 ε D x, integrand512 ε x a b N t) - expected512 ε x u v N‖ ^ 2

/-- P0069 page 6 display 2.3: the minor arc mean square as a real quantity. -/
noncomputable def minorError512 (ε D x : ℝ) (a b : ℕ → ℂ) : ℝ :=
  ∑ N ∈ frequencies512 ε x,
    ‖∫ t in minor512 ε D x, integrand512 ε x a b N t‖ ^ 2

/-- P0069 page 6: H Y squared times the requested logarithmic saving. -/
noncomputable def scale512 (ε A x : ℝ) : ℝ :=
  x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
    length512 ε x ^ 2 * Real.log x ^ (-A - 7)

/-- P0069 page 6: the scale is nonnegative for x at least 1. -/
theorem scale_nonneg512 (ε A : ℝ) {x : ℝ} (hx : 1 ≤ x) : 0 ≤ scale512 ε A x := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  unfold scale512
  positivity

/-- P0069 page 6: the Ramanujan sum c_q at frequency minus N. -/
noncomputable def ramanujan512 (q N : ℕ) : ℂ :=
  ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
    @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))

/-- P0069 page 8, the display after extending 2.6 to a complete period:
the truncated singular series main term. -/
noncomputable def truncatedMain512 (ε D x u v : ℝ) (N : ℕ) : ℂ :=
  u * v * length512 ε x / (Real.log x * Real.log (length512 ε x)) *
    ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
      (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 * ramanujan512 q N

/-- P0069 pages 7 and 8, displays 2.5 and 2.6 and the following extension error:
the replacement error as an exact mean square. -/
noncomputable def replacementError512 (ε D x : ℝ) (a b : ℕ → ℂ) (u v : ℝ) : ℝ :=
  ∑ N ∈ frequencies512 ε x,
    ‖(∫ t in major512 ε D x, integrand512 ε x a b N t) - truncatedMain512 ε D x u v N‖ ^ 2

/-- P0069 page 8, displays 2.7 to 2.9: the exact truncated singular series error. -/
noncomputable def seriesError512 (ε D x u v : ℝ) : ℝ :=
  ∑ N ∈ frequencies512 ε x,
    ‖truncatedMain512 ε D x u v N - expected512 ε x u v N‖ ^ 2

/-- P0069 page 8: split the major arc error into replacement and singular series errors. -/
theorem major_error_split512 (ε D x : ℝ) (a b : ℕ → ℂ) (u v : ℝ) :
    majorError512 ε D x a b u v ≤
      2 * replacementError512 ε D x a b u v + 2 * seriesError512 ε D x u v := by
  unfold majorError512 replacementError512 seriesError512
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro N hN
  have h := norm_add_square512
    ((∫ t in major512 ε D x, integrand512 ε x a b N t) - truncatedMain512 ε D x u v N)
    (truncatedMain512 ε D x u v N - expected512 ε x u v N)
  simpa only [sub_add_sub_cancel] using h

/-- P0069 pages 6 to 10: two eventual error estimates with sufficiently large arc
parameters combine with a common parameter and a common threshold. -/
theorem combine_eventual512 (ε A : ℝ) (F G H : ℝ → ℝ → ℝ)
    (hF : ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      F D x ≤ C * scale512 ε A x)
    (hG : ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      G D x ≤ C * scale512 ε A x)
    (hH : ∀ D x, H D x ≤ 2 * F D x + 2 * G D x) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      H D x ≤ C * scale512 ε A x := by
  obtain ⟨D₁, hD₁⟩ := hF
  obtain ⟨D₂, hD₂⟩ := hG
  refine ⟨max D₁ D₂, fun D hD => ?_⟩
  obtain ⟨C₁, hC₁⟩ := hD₁ D ((le_max_left _ _).trans hD)
  obtain ⟨C₂, hC₂⟩ := hD₂ D ((le_max_right _ _).trans hD)
  let C := max (max C₁ C₂) (max (2 * C₁ + 2 * C₂) 1)
  refine ⟨C, fun x hx => ?_⟩
  have hx₁ : C₁ ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx₂ : C₂ ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx1 : 1 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  calc
    H D x ≤ 2 * F D x + 2 * G D x := hH D x
    _ ≤ (2 * C₁ + 2 * C₂) * scale512 ε A x := by
      nlinarith [hC₁ x hx₁, hC₂ x hx₂]
    _ ≤ C * scale512 ε A x := mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) (scale_nonneg512 ε A hx1)

/-- P0069 page 7 display 2.6: the principal model with the original eta limits.
The coprime numerator sum is written as its exact Ramanujan sum. -/
noncomputable def principalArc512 (ε D x u v : ℝ) (N : ℕ) : ℂ :=
  u * v / (Real.log x * Real.log (length512 ε x)) *
    ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
      (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 * ramanujan512 q N *
        ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
          (Real.log x ^ (4 * D) / (q * length512 ε x)),
          integrand512 ε x (fun _ => 1) (fun _ => 1) N t

/-- P0069 page 7 display 2.5 and its S2 analogue: coefficient replacement error. -/
noncomputable def coefficientReplacementError512 (ε D x : ℝ)
    (a b : ℕ → ℂ) (u v : ℝ) : ℝ :=
  ∑ N ∈ frequencies512 ε x,
    ‖(∫ t in major512 ε D x, integrand512 ε x a b N t) - principalArc512 ε D x u v N‖ ^ 2

/-- P0069 page 8 first two displays: eta extension and finite endpoint error. -/
noncomputable def etaExtensionError512 (ε D x u v : ℝ) : ℝ :=
  ∑ N ∈ frequencies512 ε x,
    ‖principalArc512 ε D x u v N - truncatedMain512 ε D x u v N‖ ^ 2

/-- LEAF. P0069 page 7 display 2.5 and the immediately following S2 replacement.
The pointwise L1 replacement savings give every requested mean square saving.
The exact principal model has the original eta limits in display 2.6.
PROVED 2026-11-15 from Route512MajorFinal.major_coefficients_raw512j, no sorry. -/
theorem leaf_major_coefficients512 :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Theorem2With ε B (fun a b u v _ =>
        ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
          ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
            coefficientReplacementError512 ε D x (a x) (b x) u v ≤ C * scale512 ε A x) := by
  intro B
  refine ⟨1, one_pos, fun ε hε _ => ?_⟩
  unfold Theorem2With
  intro a b u v E θ₁ θ₂ Y Q I J hi hii hiii hiv _ A hA
  exact Route512Major.major_coefficients_raw512j B ε hε a b u v hi hii hiii hiv A hA

/-- LEAF. P0069 page 8 first two displays after 2.6: extend the eta integral
to a complete period and replace the exact convolution count by Y.
The original finite support and its endpoint error are retained.
PROVED 2026-11-15 from Route512Eta.eta_extension_raw512, no sorry. -/
theorem leaf_major_eta_extension512 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u v : ℝ,
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          etaExtensionError512 ε D x u v ≤ C * scale512 ε A x := by
  exact LeanLab.BHP1997.Route512.eta_extension_raw512

/-- LEAF. P0069 pages 6 to 8, displays 2.4 to 2.6 and the first display on page 8.
Replace both exponential sums by their principal approximations and extend each
short eta integral to a complete period. The finite interval endpoint error is
included in the stated replacement mean square. CONDITIONAL ON the separate
coefficient replacement and eta extension leaves. -/
theorem leaf_major_replacement512 :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Theorem2With ε B (fun a b u v _ =>
        ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
          ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
            replacementError512 ε D x (a x) (b x) u v ≤ C * scale512 ε A x) := by
  intro B
  obtain ⟨ε₁, hε₁, hcoeff⟩ := leaf_major_coefficients512 B
  obtain ⟨ε₂, hε₂, heta⟩ := leaf_major_eta_extension512
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂,
    fun ε hε he a b u v E h1 h2 h3 h4 h5 A hA => ?_⟩
  have hc := hcoeff ε hε (lt_of_lt_of_le he (min_le_left _ _))
    a b u v E h1 h2 h3 h4 h5 A hA
  have ht := heta ε hε (lt_of_lt_of_le he (min_le_right _ _)) u v A hA
  apply combine_eventual512 ε A
    (fun D x => coefficientReplacementError512 ε D x (a x) (b x) u v)
    (fun D x => etaExtensionError512 ε D x u v)
    (fun D x => replacementError512 ε D x (a x) (b x) u v) hc ht
  intro D x
  unfold replacementError512 coefficientReplacementError512 etaExtensionError512
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro N hN
  have h := norm_add_square512
    ((∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) - principalArc512 ε D x u v N)
    (principalArc512 ε D x u v N - truncatedMain512 ε D x u v N)
  simpa only [sub_add_sub_cancel] using h

/-- P0069 page 8 display 2.8: the small-divisor part of the Vaughan tail weight. -/
noncomputable def smallDivisorTail512 (P : ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ N.divisors.filter (fun d : ℕ => (d : ℝ) ≤ P), (d : ℝ) / (Nat.totient d : ℝ) / P

/-- P0069 page 8 display 2.9: the large-divisor part of the Vaughan tail weight. -/
noncomputable def largeDivisorTail512 (P : ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ N.divisors.filter (fun d : ℕ => P < (d : ℝ)), 1 / (Nat.totient d : ℝ)

/-- P0069 page 8 display 2.8: the exact small-divisor mean square on K. -/
noncomputable def smallDivisorMoment512 (ε D x : ℝ) : ℝ :=
  ∑ N ∈ frequencies512 ε x, smallDivisorTail512 (Real.log x ^ (2 * D)) N ^ 2

/-- P0069 page 8 display 2.9: the exact large-divisor mean square on K. -/
noncomputable def largeDivisorMoment512 (ε D x : ℝ) : ℝ :=
  ∑ N ∈ frequencies512 ε x, largeDivisorTail512 (Real.log x ^ (2 * D)) N ^ 2

/-- P0069 page 8 display 2.7: the exact mean square of the minimum weight. -/
noncomputable def divisorTailMoment512 (ε D x : ℝ) : ℝ :=
  ∑ N ∈ frequencies512 ε x,
    (∑ d ∈ N.divisors, 1 / (Nat.totient d : ℝ) *
      min ((d : ℝ) / Real.log x ^ (2 * D)) 1) ^ 2

/-- P0069 page 8: both divisor mean squares are nonnegative. -/
theorem divisor_moments_nonneg512 (ε D x : ℝ) :
    0 ≤ smallDivisorMoment512 ε D x ∧ 0 ≤ largeDivisorMoment512 ε D x := by
  constructor <;> exact Finset.sum_nonneg (fun N hN => sq_nonneg _)

/-- P0069 page 8: split the minimum in the Vaughan weight at d equal to P. -/
theorem divisor_tail_partition512 {P : ℝ} (hP : 0 < P) (N : ℕ) :
    (∑ d ∈ N.divisors, 1 / (Nat.totient d : ℝ) * min ((d : ℝ) / P) 1) =
      smallDivisorTail512 P N + largeDivisorTail512 P N := by
  unfold smallDivisorTail512 largeDivisorTail512
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : (d : ℝ) ≤ P
  · rw [min_eq_left ((div_le_one₀ hP).mpr h)]
    simp only [h, not_lt_of_ge h, ite_true, ite_false, add_zero]
    ring
  · have hh : P < (d : ℝ) := lt_of_not_ge h
    rw [min_eq_right ((one_le_div₀ hP).mpr hh.le)]
    simp only [h, hh, ite_true, ite_false, zero_add, mul_one]

/-- P0069 page 8: Cauchy separates the two parts of the divisor tail moment. -/
theorem divisor_tail_moment_split512 (ε D x : ℝ)
    (hP : 0 < Real.log x ^ (2 * D)) :
    divisorTailMoment512 ε D x ≤
      2 * smallDivisorMoment512 ε D x + 2 * largeDivisorMoment512 ε D x := by
  unfold divisorTailMoment512 smallDivisorMoment512 largeDivisorMoment512
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro N hN
  rw [divisor_tail_partition512 hP N]
  nlinarith [sq_nonneg (smallDivisorTail512 (Real.log x ^ (2 * D)) N -
    largeDivisorTail512 (Real.log x ^ (2 * D)) N)]

/-! ### Private helpers for the Vaughan 3.23 and 3.26 leaves -/

private lemma e512_add (x y : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * ((x + y : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (y : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma e512_nat_mul (k : ℕ) (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (((k : ℝ) * x : ℝ) : ℂ)) =
      (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, e512_add, ih, pow_succ]

private lemma e512_int_mul (k : ℤ) (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (((k : ℝ) * x : ℝ) : ℂ)) =
      (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ k := by
  have harg : (2 * (Real.pi : ℂ) * Complex.I * (((k : ℝ) * x : ℝ) : ℂ))
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) := by push_cast; ring
  rw [harg, Complex.exp_int_mul]

private lemma e512_int_cast (k : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) : ℂ)) = 1 := by
  have h2 : Complex.exp (2 * Real.pi * Complex.I * ((1 : ℝ) : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨1, by push_cast; ring⟩
  have h := e512_int_mul k 1
  rw [mul_one] at h
  rw [h, h2, one_zpow]

private lemma two_pi_I_ne_zero512 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have h1 : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  exact mul_ne_zero h1 Complex.I_ne_zero

private lemma e512_eq_one_iff {x : ℝ} :
    Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) = 1 ↔ ∃ k : ℤ, x = (k : ℝ) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    refine ⟨n, ?_⟩
    have hx : (2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)
        = (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℝ) : ℂ) := by rw [hn]; push_cast; ring
    exact Complex.ofReal_injective (mul_left_cancel₀ two_pi_I_ne_zero512 hx)
  · rintro ⟨k, rfl⟩
    exact e512_int_cast k

/-- The orthogonality relation `Σ_{b<m} e(bk/m) = m` if `m ∣ k`, else `0`. -/
private lemma e512_sum_orth {m : ℕ} (hm : 0 < m) (k : ℤ) :
    ∑ b ∈ Finset.range m, Complex.exp (2 * Real.pi * Complex.I * (((b : ℝ) * (k : ℝ)) / m : ℝ))
      = if (m : ℤ) ∣ k then (m : ℂ) else 0 := by
  have hmR : ((m : ℝ)) ≠ 0 := by positivity
  set c : ℂ := Complex.exp (2 * Real.pi * Complex.I * (((k : ℝ)) / m : ℝ)) with hc
  have hterm : ∀ b ∈ Finset.range m,
      Complex.exp (2 * Real.pi * Complex.I * (((b : ℝ) * (k : ℝ)) / m : ℝ)) = c ^ b := by
    intro b _
    have harg : ((b : ℝ) * (k : ℝ)) / m = (b : ℝ) * ((k : ℝ) / m) := by field_simp
    rw [harg, e512_nat_mul]
  rw [Finset.sum_congr rfl hterm]
  have hcm : c ^ m = 1 := by
    have h1 : c ^ m = Complex.exp (2 * Real.pi * Complex.I * (((m : ℝ) * ((k : ℝ) / m) : ℝ) : ℂ)) := by
      rw [hc]; exact (e512_nat_mul m ((k : ℝ) / m)).symm
    rw [h1, mul_div_cancel₀ (k : ℝ) hmR, e512_int_cast]
  have hiff : c = 1 ↔ (m : ℤ) ∣ k := by
    rw [hc, e512_eq_one_iff]
    constructor
    · rintro ⟨j, hj⟩
      have h2 : (k : ℝ) = (j : ℝ) * (m : ℝ) := by
        rw [div_eq_iff hmR] at hj
        linarith [hj]
      have h3 : k = j * (m : ℤ) := by exact_mod_cast h2
      exact ⟨j, by rw [h3]; ring⟩
    · rintro ⟨j, rfl⟩
      refine ⟨j, ?_⟩
      push_cast
      field_simp
  by_cases h1 : c = 1
  · rw [ite_eq_left (hiff.mp h1)]
    simp [h1]
  · rw [ite_eq_right (fun h => h1 (hiff.mpr h))]
    rw [geom_sum_eq h1 m, hcm]
    simp

private lemma filter_Icc_eq_range512 {q : ℕ} (hq : 2 ≤ q) :
    (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q) =
      (Finset.range q).filter (fun r => Nat.Coprime r q) := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, hc⟩
    refine ⟨?_, hc⟩
    rcases lt_or_eq_of_le h2 with h | h
    · exact h
    · exfalso
      subst h
      simp only [Nat.Coprime, Nat.gcd_self] at hc
      omega
  · rintro ⟨h1, hc⟩
    refine ⟨⟨?_, le_of_lt h1⟩, hc⟩
    rcases Nat.eq_zero_or_pos r with h | h
    · exfalso
      subst h
      simp only [Nat.Coprime, Nat.gcd_zero_left] at hc
      omega
    · exact h

private lemma ramanujan512_one (N : ℕ) : ramanujan512 1 N = 1 := by
  unfold ramanujan512
  have h : (Finset.Icc 1 1).filter (fun r => Nat.Coprime r 1) = {1} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, -⟩
      omega
    · rintro rfl
      exact ⟨⟨le_rfl, le_rfl⟩, Nat.coprime_one_right 1⟩
  rw [h, Finset.sum_singleton]
  rw [fourier_coe_apply, Complex.exp_eq_one_iff]
  exact ⟨-(N : ℤ), by push_cast; ring⟩

private lemma ramanujan512_exp_range (q N : ℕ) (hq : 2 ≤ q) :
    ramanujan512 q N =
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * ((-(N : ℤ) : ℤ) : ℝ)) / q : ℝ)) := by
  unfold ramanujan512
  rw [filter_Icc_eq_range512 hq]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

private lemma sum_moebius_divisors512 (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) = if n = 1 then 1 else 0 := by
  have h := ArithmeticFunction.coe_mul_zeta_apply (f := ArithmeticFunction.moebius) (x := n)
  rw [ArithmeticFunction.moebius_mul_coe_zeta] at h
  rw [← h]
  exact ArithmeticFunction.one_apply

private lemma divisors_filter_dvd_eq_gcd512 {q a : ℕ} (hq : q ≠ 0) :
    q.divisors.filter (fun d => d ∣ a) = (a.gcd q).divisors := by
  have hg : a.gcd q ∣ q := Nat.gcd_dvd_right a q
  have hg0 : a.gcd q ≠ 0 := by
    rcases Nat.eq_zero_or_pos (a.gcd q) with h | h
    · rw [h] at hg; exact absurd (Nat.eq_zero_of_zero_dvd hg) hq
    · exact h.ne'
  rw [← Nat.divisors_filter_dvd_of_dvd hq hg]
  refine Finset.filter_congr (fun d hd => ?_)
  simp only [Nat.mem_divisors] at hd
  exact ⟨fun h => Nat.dvd_gcd h hd.1, fun h => Nat.dvd_trans h (Nat.gcd_dvd_left a q)⟩

private lemma indicator_coprime512 {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    (if a.gcd q = 1 then (1:ℂ) else 0)
      = ∑ d ∈ q.divisors, (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) := by
  rw [← Finset.sum_filter, divisors_filter_dvd_eq_gcd512 hq]
  have h := congrArg (fun z : ℤ => (z : ℂ)) (sum_moebius_divisors512 (a.gcd q))
  push_cast at h
  exact h.symm

private lemma sum_range_filter_dvd512 {q d : ℕ} (hd : 0 < d) (hdq : d ∣ q) (g : ℕ → ℂ) :
    ∑ a ∈ (Finset.range q).filter (fun a => d ∣ a), g a
      = ∑ b ∈ Finset.range (q / d), g (d * b) := by
  have hdq' : d * (q / d) = q := Nat.mul_div_cancel' hdq
  have hset : (Finset.range q).filter (fun a => d ∣ a)
      = (Finset.range (q / d)).image (fun b => d * b) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨haq, b, rfl⟩
      refine ⟨b, ?_, rfl⟩
      rw [← hdq'] at haq
      exact Nat.lt_of_mul_lt_mul_left haq
    · rintro ⟨b, hb, rfl⟩
      refine ⟨?_, ⟨b, rfl⟩⟩
      rw [← hdq']
      exact Nat.mul_lt_mul_of_pos_left hb hd
  rw [hset, Finset.sum_image]
  intro x _ y _ hxy
  exact Nat.eq_of_mul_eq_mul_left hd hxy

/-- The general exponential sum as a divisor sum. -/
private lemma ramanujan_exp_dvd (q : ℕ) (k : ℤ) (hq : 2 ≤ q) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (k : ℝ)) / q : ℝ)))
      = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
        (if ((q / d : ℕ) : ℤ) ∣ k then ((q / d : ℕ) : ℂ) else 0) := by
  have hq0 : q ≠ 0 := by omega
  have hqR : ((q : ℝ)) ≠ 0 := by positivity
  have hfilter : (Finset.range q).filter (fun a => Nat.Coprime a q)
      = (Finset.range q).filter (fun a => a.gcd q = 1) :=
    Finset.filter_congr (fun a _ => Nat.coprime_iff_gcd_eq_one)
  rw [hfilter, Finset.sum_filter]
  have hstep1 : ∑ a ∈ Finset.range q,
      (if a.gcd q = 1 then Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (k : ℝ)) / q : ℝ)) else 0)
      = ∑ a ∈ Finset.range q,
          (∑ d ∈ q.divisors, (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0))
            * Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (k : ℝ)) / q : ℝ)) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have h1 : (if a.gcd q = 1 then (1:ℂ) else 0)
          * Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (k : ℝ)) / q : ℝ))
        = (if a.gcd q = 1 then
            Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (k : ℝ)) / q : ℝ)) else 0) := by
      by_cases h : a.gcd q = 1 <;> simp [h]
    rw [← h1, indicator_coprime512 hq0 a]
  rw [hstep1]
  have hstep2 : ∀ a ∈ Finset.range q,
      (∑ d ∈ q.divisors, (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0))
        * Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (k : ℝ)) / q : ℝ))
      = ∑ d ∈ q.divisors,
          (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0)
            * Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (k : ℝ)) / q : ℝ)) := by
    intro a _
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl hstep2, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdvd : d ∣ q := (Nat.mem_divisors.mp hd).1
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
  have hm0 : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd0
  have hfac : ∑ a ∈ Finset.range q,
        (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0)
          * Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (k : ℝ)) / q : ℝ))
      = ∑ a ∈ Finset.range q,
          (if d ∣ a then (ArithmeticFunction.moebius d : ℂ)
            * Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (k : ℝ)) / q : ℝ)) else 0) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases h : d ∣ a <;> simp [h]
  rw [hfac, ← Finset.sum_filter, sum_range_filter_dvd512 hd0 hdvd, ← Finset.mul_sum]
  congr 1
  have hqd : d * (q / d) = q := Nat.mul_div_cancel' hdvd
  have harg : ∀ b : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * (((d * b : ℕ) : ℝ) * (k : ℝ) / q : ℝ))
      = Complex.exp (2 * Real.pi * Complex.I *
          (((b : ℝ) * (k : ℝ)) / (((q / d : ℕ)) : ℝ) : ℝ)) := by
    intro b
    congr 1
    rw [Nat.cast_div hdvd (by positivity : ((d : ℕ) : ℝ) ≠ 0), ← hqd]
    push_cast
    have hdR : ((d : ℕ) : ℝ) ≠ 0 := by positivity
    have hmR : (((q / d : ℕ)) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [Finset.sum_congr rfl (fun b _ => harg b), e512_sum_orth hm0 k]

/-- The Ramanujan sum `c_q(N)` as an exact divisor sum. -/
private lemma ramanujan512_dvd (q N : ℕ) (hq : 2 ≤ q) :
    ramanujan512 q N = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
      (if ((q / d : ℕ) : ℤ) ∣ (N : ℤ) then ((q / d : ℕ) : ℂ) else 0) := by
  rw [ramanujan512_exp_range q N hq, ramanujan_exp_dvd q (-(N : ℤ)) hq]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hd : (((q / d : ℕ)) : ℤ) ∣ -(N : ℤ) ↔ (((q / d : ℕ)) : ℤ) ∣ (N : ℤ) := Int.dvd_neg
  by_cases h : (((q / d : ℕ)) : ℤ) ∣ (N : ℤ)
  · simp only [if_pos (hd.mpr h), if_pos h]
  · simp only [if_neg (fun hh => h (hd.mp hh)), if_neg h]

open scoped ArithmeticFunction.Moebius

/-- The real divisor form of `c_q(N)`: `Σ_{d ∣ q} (q/d)·μ(d)` restricted to `(q/d) ∣ N`. -/
private lemma c512_real_form (q N : ℕ) (hq : 1 ≤ q) :
    ramanujan512 q N =
      ((∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) : ℝ) : ℂ) := by
  rcases eq_or_lt_of_le hq with h | h
  · subst h
    rw [ramanujan512_one]
    have h1 : (∑ d ∈ (1 : ℕ).divisors, (if (1 / d : ℕ) ∣ N then ((1 / d : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = 1 := by
      rw [Nat.divisors_one, Finset.sum_singleton]
      norm_num
    rw [h1]
    norm_num
  · have h2 : 2 ≤ q := h
    rw [ramanujan512_dvd q N h2, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases hd : ((q / d : ℕ) : ℤ) ∣ (N : ℤ)
    · rw [if_pos hd, if_pos (Int.natCast_dvd_natCast.mp hd)]
      push_cast
      ring
    · rw [if_neg hd, if_neg (fun hh => hd (Int.natCast_dvd_natCast.mpr hh))]
      push_cast
      ring

/-- Reindex the divisor sum: the Möbius index can be put on `q / d`. -/
private lemma c512_conv_form (q N : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ))
      = ∑ e ∈ q.divisors, (if e ∣ N then (e : ℝ) else 0) *
        ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ) := by
  have hq0 : q ≠ 0 := hq.ne'
  refine Finset.sum_nbij' (fun d => q / d) (fun e => q / e) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hq0⟩
  · intro e he
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors he), hq0⟩
  · intro d hd
    exact Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hq0
  · intro e he
    exact Nat.div_div_self (Nat.dvd_of_mem_divisors he) hq0
  · intro d hd
    rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hq0]

/-- The weight `d ↦ d · 1_{d ∣ N}` is multiplicative. -/
private lemma gDiv512_mult (N : ℕ) (g : ArithmeticFunction ℝ)
    (hg : ∀ d, g d = if d ∣ N then (d : ℝ) else 0) : g.IsMultiplicative := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · rw [hg]; simp
  · rw [hg, hg, hg]
    by_cases ha : a ∣ N
    · by_cases hb : b ∣ N
      · rw [if_pos (hab.mul_dvd_of_dvd_of_dvd ha hb), if_pos ha, if_pos hb]
        push_cast
        ring
      · rw [if_neg (fun h => hb (dvd_trans (dvd_mul_left b a) h)), if_neg hb, mul_zero]
    · rw [if_neg (fun h => ha (dvd_trans (dvd_mul_right a b) h)), if_neg ha, zero_mul]

/-- The Ramanujan divisor sum as the Dirichlet convolution `(d ↦ d·1_{d ∣ N}) * μ`. -/
private lemma conv512 (N : ℕ) (g : ArithmeticFunction ℝ)
    (hg : ∀ d, g d = if d ∣ N then (d : ℝ) else 0) (q : ℕ) :
    (g * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) q
      = ∑ e ∈ q.divisors, (if e ∣ N then ((e : ℕ) : ℝ) else 0) *
          ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (fun a b => g a * (ArithmeticFunction.moebius : ArithmeticFunction ℝ) b)]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [hg, ArithmeticFunction.intCoe_apply]

/-- The real Ramanujan divisor sum is multiplicative in the modulus. -/
private lemma c512_real_mul {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 0 < m) (hn : 0 < n) (N : ℕ) :
    (∑ d ∈ (m * n).divisors,
        (if (m * n / d : ℕ) ∣ N then ((m * n / d : ℕ) : ℝ) else 0) *
          ((ArithmeticFunction.moebius d : ℤ) : ℝ))
      = (∑ d ∈ m.divisors,
          (if (m / d : ℕ) ∣ N then ((m / d : ℕ) : ℝ) else 0) *
            ((ArithmeticFunction.moebius d : ℤ) : ℝ)) *
        (∑ d ∈ n.divisors,
          (if (n / d : ℕ) ∣ N then ((n / d : ℕ) : ℝ) else 0) *
            ((ArithmeticFunction.moebius d : ℤ) : ℝ)) := by
  set g : ArithmeticFunction ℝ := ⟨fun d => if d ∣ N then (d : ℝ) else 0, by simp⟩ with hgdef
  have hg : ∀ d, g d = if d ∣ N then (d : ℝ) else 0 := fun d => rfl
  have hmul : (g * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)).IsMultiplicative :=
    (gDiv512_mult N g hg).mul ArithmeticFunction.isMultiplicative_moebius.intCast
  rw [c512_conv_form (m * n) N (Nat.mul_pos hm hn), c512_conv_form m N hm,
    c512_conv_form n N hn, ← conv512 N g hg (m * n), ← conv512 N g hg m,
    ← conv512 N g hg n]
  exact hmul.map_mul_of_coprime hmn

/-- The Ramanujan sum at a prime. -/
private lemma c512_prime {p : ℕ} (hp : p.Prime) (N : ℕ) :
    (∑ d ∈ p.divisors, (if (p / d : ℕ) ∣ N then ((p / d : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ))
      = if p ∣ N then ((p : ℝ) - 1) else -1 := by
  rw [hp.divisors, Finset.sum_insert (by simp [hp.ne_one.symm]), Finset.sum_singleton]
  have hμ1 : ((ArithmeticFunction.moebius 1 : ℤ) : ℝ) = 1 := by
    rw [ArithmeticFunction.moebius_apply_one]; norm_num
  have hμp : ((ArithmeticFunction.moebius p : ℤ) : ℝ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime hp]; norm_num
  rw [hμ1, hμp, Nat.div_one, Nat.div_self hp.pos, if_pos (one_dvd N)]
  by_cases h : p ∣ N
  · rw [if_pos h, if_pos h]
    push_cast
    ring
  · rw [if_neg h, if_neg h]
    ring

/-- `n ≤ φ(n) d(n)`, since `n / φ(n) = Π_{p ∣ n} p/(p-1) ≤ 2 ^ ω(n) ≤ d(n)`. -/
private lemma le_totient_mul_card_divisors512 (n : ℕ) :
    n ≤ Nat.totient n * n.divisors.card := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hid := Nat.totient_mul_prod_primeFactors n
  have h2 : ∏ p ∈ n.primeFactors, p ≤
      2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun p hp => ?_)
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have h3 : 2 ^ n.primeFactors.card ≤ n.divisors.card := by
    rw [Nat.card_divisors hn.ne', ← Finset.prod_const]
    refine Finset.prod_le_prod (fun p hp => ?_)
    have hp' : p ∈ n.factorization.support := by rwa [Nat.support_factorization]
    have : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp'
    omega
  have hQ : 0 < ∏ p ∈ n.primeFactors, (p - 1) := by
    refine Finset.prod_pos fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hmain : n * ∏ p ∈ n.primeFactors, (p - 1) ≤
      (Nat.totient n * n.divisors.card) * ∏ p ∈ n.primeFactors, (p - 1) := by
    calc n * ∏ p ∈ n.primeFactors, (p - 1)
        = Nat.totient n * ∏ p ∈ n.primeFactors, p := hid.symm
      _ ≤ Nat.totient n * (2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (p - 1)) :=
          Nat.mul_le_mul_left _ h2
      _ ≤ Nat.totient n * (n.divisors.card * ∏ p ∈ n.primeFactors, (p - 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h3)
      _ = (Nat.totient n * n.divisors.card) * ∏ p ∈ n.primeFactors, (p - 1) := by ring
  exact Nat.le_of_mul_le_mul_right hmain hQ

/-- `1 / φ(n)² ≪ n^{-2+2/k}`, from the divisor bound. -/
private lemma totient_sq_le512 (k : ℕ) (hk : 1 ≤ k) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n →
      1 / (Nat.totient n : ℝ) ^ 2 ≤ D ^ 2 * (n : ℝ) ^ (-2 + 2 * (k : ℝ)⁻¹) := by
  obtain ⟨D, hD, hDb⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow k hk
  refine ⟨D, hD, fun n hn => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hφ : (0 : ℝ) < (Nat.totient n : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hn
  have h0 := le_totient_mul_card_divisors512 n
  have h1 : (n : ℝ) ≤ (Nat.totient n : ℝ) * (D * (n : ℝ) ^ ((k : ℝ)⁻¹)) := by
    have h' : (n : ℝ) ≤ (Nat.totient n : ℝ) * (n.divisors.card : ℝ) := by exact_mod_cast h0
    exact h'.trans (mul_le_mul_of_nonneg_left (hDb n hn) hφ.le)
  set t : ℝ := (k : ℝ)⁻¹ with ht
  have hnt : 0 < (n : ℝ) ^ t := Real.rpow_pos_of_pos hnR t
  have hsplit : (n : ℝ) = (n : ℝ) ^ (1 - t) * (n : ℝ) ^ t := by
    rw [← Real.rpow_add hnR]
    norm_num
  have h3 : (n : ℝ) ^ (1 - t) * (n : ℝ) ^ t ≤
      (D * (Nat.totient n : ℝ)) * (n : ℝ) ^ t := by
    rw [← hsplit]
    exact h1.trans_eq (by ring)
  have h2 : (n : ℝ) ^ (1 - t) ≤ D * (Nat.totient n : ℝ) :=
    le_of_mul_le_mul_right h3 hnt
  have h4 : ((n : ℝ) ^ (1 - t)) ^ 2 ≤ (D * (Nat.totient n : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  have e1 : ((n : ℝ) ^ (1 - t)) ^ 2 = (n : ℝ) ^ (2 - 2 * t) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    congr 1
    push_cast
    ring
  have key : (n : ℝ) ^ (2 - 2 * t) ≤ D ^ 2 * (Nat.totient n : ℝ) ^ 2 := by
    rw [← e1, ← mul_pow]
    exact h4
  have e2 : -2 + 2 * (k : ℝ)⁻¹ = -(2 - 2 * t) := by rw [ht]; ring
  have hn2 : (0 : ℝ) < (n : ℝ) ^ (2 - 2 * t) := Real.rpow_pos_of_pos hnR _
  have hφ2 : (0 : ℝ) < (Nat.totient n : ℝ) ^ 2 := by positivity
  rw [e2, Real.rpow_neg hnR.le, ← div_eq_mul_inv, le_div_iff₀ hn2, div_mul_eq_mul_div,
    one_mul, div_le_iff₀ hφ2]
  simpa using key

/-- `|c_q(N)|` is bounded by the divisor sum of `N`. -/
private lemma c512_abs_le (N q : ℕ) (hN : 1 ≤ N) :
    |∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ ∑ e ∈ N.divisors, (e : ℝ) := by
  rcases Nat.eq_zero_or_pos q with hq0 | hq
  · subst hq0
    rw [Nat.divisors_zero, Finset.sum_empty, abs_zero]
    exact Finset.sum_nonneg (fun e _ => by positivity)
  · rw [c512_conv_form q N hq]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hstep : ∑ e ∈ q.divisors,
        |(if e ∣ N then ((e : ℕ) : ℝ) else 0) * ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ)|
        ≤ ∑ e ∈ q.divisors, (if e ∣ N then ((e : ℕ) : ℝ) else 0) := by
      refine Finset.sum_le_sum (fun e _ => ?_)
      rw [abs_mul]
      have hmu : |((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ)| ≤ 1 := by
        have h := ArithmeticFunction.abs_moebius_le_one (n := q / e)
        rw [abs_le] at h
        rw [abs_le]
        exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
      calc |(if e ∣ N then ((e : ℕ) : ℝ) else 0)| *
            |((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ)|
          ≤ |(if e ∣ N then ((e : ℕ) : ℝ) else 0)| * 1 :=
            mul_le_mul_of_nonneg_left hmu (abs_nonneg _)
        _ = (if e ∣ N then ((e : ℕ) : ℝ) else 0) := by
            rw [mul_one, abs_of_nonneg]
            split_ifs <;> positivity
    refine hstep.trans ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun e _ _ => by positivity)
    intro e he
    rw [Finset.mem_filter] at he
    exact Nat.mem_divisors.mpr ⟨he.2, by omega⟩

/-- `μ(q)² φ(q)^{-2} c_q(N)` is absolutely summable. -/
private lemma summable_c512 (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun q : ℕ => ‖((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
      (Nat.totient q : ℝ) ^ 2 *
        (∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) *
          ((ArithmeticFunction.moebius d : ℤ) : ℝ))‖) := by
  obtain ⟨D, hD, hDn⟩ := totient_sq_le512 4 (by norm_num)
  have hS0 : (0 : ℝ) ≤ ∑ e ∈ N.divisors, (e : ℝ) :=
    Finset.sum_nonneg (fun e _ => by positivity)
  have hcomp : Summable (fun q : ℕ =>
      ((∑ e ∈ N.divisors, (e : ℝ)) * D ^ 2) * (q : ℝ) ^ (-2 + 2 * (4 : ℝ)⁻¹)) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_) hcomp
  rcases Nat.eq_zero_or_pos q with hq0 | hq
  · subst hq0
    have h0 : ((ArithmeticFunction.moebius 0 : ℤ) : ℝ) = 0 := by
      simp [ArithmeticFunction.moebius]
    have hz : ((0 : ℕ) : ℝ) ^ (-2 + 2 * (4 : ℝ)⁻¹) = 0 := by
      rw [Nat.cast_zero]
      exact Real.zero_rpow (by norm_num)
    rw [h0, hz]
    simp
  · have hφ : (0 : ℝ) < (Nat.totient q : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq
    have hφ2 : (0 : ℝ) < (Nat.totient q : ℝ) ^ 2 := by positivity
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hS := c512_abs_le N q hN
    have hm := hDn q hq
    have hmu : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
      have h := ArithmeticFunction.abs_moebius_le_one (n := q)
      rw [abs_le] at h
      rw [abs_le]
      exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    have hmu2 : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).mpr hmu
    have hA0 : (0 : ℝ) ≤ ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        (Nat.totient q : ℝ) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hA0]
    calc ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
          |∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) *
            ((ArithmeticFunction.moebius d : ℤ) : ℝ)|
        ≤ (1 / (Nat.totient q : ℝ) ^ 2) * (∑ e ∈ N.divisors, (e : ℝ)) :=
          mul_le_mul (div_le_div_of_nonneg_right hmu2 hφ2.le) hS (abs_nonneg _)
            (by positivity)
      _ ≤ (D ^ 2 * (q : ℝ) ^ (-2 + 2 * (4 : ℝ)⁻¹)) * (∑ e ∈ N.divisors, (e : ℝ)) :=
          mul_le_mul_of_nonneg_right hm hS0
      _ = ((∑ e ∈ N.divisors, (e : ℝ)) * D ^ 2) * (q : ℝ) ^ (-2 + 2 * (4 : ℝ)⁻¹) := by
          ring

/-- The local Euler factor `1 + μ(p)² φ(p)^{-2} c_p(N)` at a prime. -/
private lemma c512_local {p : ℕ} (hp : p.Prime) (N : ℕ) :
    1 + ((ArithmeticFunction.moebius p : ℤ) : ℝ) ^ 2 / (Nat.totient p : ℝ) ^ 2 *
        (∑ d ∈ p.divisors, (if (p / d : ℕ) ∣ N then ((p / d : ℕ) : ℝ) else 0) *
          ((ArithmeticFunction.moebius d : ℤ) : ℝ))
      = if p ∣ N then (p : ℝ) / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  rw [c512_prime hp N, ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp,
    Nat.cast_sub hp.one_lt.le, Nat.cast_one, Int.cast_neg, Int.cast_one]
  have hd1 : (p : ℝ) - 1 ≠ 0 := by linarith
  by_cases h : p ∣ N
  · rw [if_pos h, if_pos h]
    field_simp
    ring
  · rw [if_neg h, if_neg h]
    field_simp
    ring

/-- The finite Euler product for `F`, in terms of the twin-prime product. -/
private lemma prod_local512 (N n : ℕ) (hN : 2 ≤ N) (hEven : Even N) (hn : N < n) :
    ∏ p ∈ (Finset.range n).filter (fun p => Nat.Prime p),
        (1 + ((ArithmeticFunction.moebius p : ℤ) : ℝ) ^ 2 / (Nat.totient p : ℝ) ^ 2 *
          (∑ d ∈ p.divisors, (if (p / d : ℕ) ∣ N then ((p / d : ℕ) : ℝ) else 0) *
            ((ArithmeticFunction.moebius d : ℤ) : ℝ)))
      = 2 * (∏ p ∈ (Finset.range n).filter (fun p => Nat.Prime p ∧ 2 < p),
              (1 - 1 / ((p : ℝ) - 1) ^ 2)) *
          (∏ p ∈ (N / 2).primeFactors.filter (fun p => 2 < p),
              (((p : ℝ) - 1) / ((p : ℝ) - 2))) := by
  set S : Finset ℕ := (Finset.range n).filter (fun p => Nat.Prime p) with hS
  set P : ℕ → ℝ := fun p =>
    1 + ((ArithmeticFunction.moebius p : ℤ) : ℝ) ^ 2 / (Nat.totient p : ℝ) ^ 2 *
        (∑ d ∈ p.divisors, (if (p / d : ℕ) ∣ N then ((p / d : ℕ) : ℝ) else 0) *
          ((ArithmeticFunction.moebius d : ℤ) : ℝ)) with hPdef
  set T : Finset ℕ := (N / 2).primeFactors.filter (fun p => 2 < p) with hT
  set G : ℕ → ℝ := fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2 with hGdef
  set Q : ℕ → ℝ := fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2) with hQdef
  change S.prod P =
    2 * (Finset.filter (fun p => Nat.Prime p ∧ 2 < p) (Finset.range n)).prod G * T.prod Q
  have h2N : 2 ∣ N := hEven.two_dvd
  have h2S : 2 ∈ S := by
    rw [hS]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
  have hP2 : P 2 = 2 := by
    have hloc := c512_local Nat.prime_two N
    rw [if_pos h2N] at hloc
    rw [show P 2 = _ from hloc]
    norm_num
  have hstep : ∀ p ∈ S, p ≠ 2 → P p = G p * (if p ∣ N then Q p else 1) := by
    intro p hpS hpne
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hpS).2
    have hp3 : 2 < p := by
      rcases lt_or_eq_of_le hpp.two_le with h | h
      · exact h
      · exact absurd h.symm hpne
    have hloc := c512_local hpp N
    rw [show P p = _ from hloc]
    have hd1 : (p : ℝ) - 1 ≠ 0 := by
      have hp2' : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      linarith
    have hp2' : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp3
    have hd2 : (p : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
    by_cases h : p ∣ N
    · rw [if_pos h, if_pos h]
      simp only [hGdef, hQdef]
      field_simp
      ring
    · rw [if_neg h, if_neg h, mul_one]
  have hsplit : ∏ p ∈ S, P p = P 2 * ∏ p ∈ S.erase 2, P p := by
    rw [← Finset.mul_prod_erase S P h2S]
  have hE2 : S.filter (fun p => 2 < p) =
      Finset.filter (fun p => Nat.Prime p ∧ 2 < p) (Finset.range n) := by
    rw [hS, Finset.filter_filter]
  have hE : S.erase 2 = S.filter (fun p => 2 < p) := by
    ext p
    simp only [Finset.mem_erase, Finset.mem_filter]
    constructor
    · rintro ⟨hp2, hpS⟩
      have hpp : Nat.Prime p := (Finset.mem_filter.mp hpS).2
      exact ⟨hpS, by
        rcases lt_or_eq_of_le hpp.two_le with h | h
        · exact h
        · exact absurd h.symm hp2⟩
    · rintro ⟨hpS, hp2⟩
      refine ⟨?_, hpS⟩
      intro h
      rw [h] at hp2
      exact lt_irrefl 2 hp2
  have hstep' : ∏ p ∈ S.erase 2, P p
      = (∏ p ∈ S.erase 2, G p) * (∏ p ∈ S.erase 2, (if p ∣ N then Q p else 1)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun p hp =>
      hstep p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp))
  have hprime2 : Nat.Prime 2 := Nat.prime_two
  have hTmem : T ⊆ S.erase 2 := by
    intro p hpT
    rw [hT, Finset.mem_filter, Nat.mem_primeFactors] at hpT
    obtain ⟨⟨hpp, hpN2, -⟩, hp2⟩ := hpT
    refine Finset.mem_erase.mpr ⟨by omega, ?_⟩
    rw [hS]
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hpp⟩
    have hpN : p ∣ N := hpN2.trans (Nat.div_dvd_of_dvd h2N)
    have := Nat.le_of_dvd (by omega) hpN
    omega
  have hTset : (S.erase 2).filter (fun p => p ∣ N) = T := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hpE, hpN⟩
      have hpp : Nat.Prime p := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hpE)).2
      have hp2 : 2 < p := by
        have hpS := Finset.mem_of_mem_erase hpE
        have hpp2 : Nat.Prime p := (Finset.mem_filter.mp hpS).2
        rcases lt_or_eq_of_le hpp2.two_le with h | h
        · exact h
        · rw [h] at hpE
          exact absurd rfl (Finset.ne_of_mem_erase hpE)
      have hcop : Nat.Coprime p 2 := by
        refine (Nat.Prime.coprime_iff_not_dvd hpp).mpr ?_
        intro hd
        have hd' : p = 1 ∨ p = 2 := (Nat.dvd_prime Nat.prime_two).mp hd
        omega
      have hpN' : p ∣ N / 2 * 2 := by rw [Nat.div_mul_cancel h2N]; exact hpN
      have hpN2 : p ∣ N / 2 := hcop.dvd_of_dvd_mul_right hpN'
      rw [hT]
      have hN2 : N / 2 ≠ 0 := by
        have hp2pos : 0 < N / 2 := Nat.div_pos (by omega : 2 ≤ N) (by norm_num)
        omega
      exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp, hpN2, hN2⟩, hp2⟩
    · intro hpT
      have hpE := hTmem hpT
      refine ⟨hpE, ?_⟩
      rw [hT, Finset.mem_filter, Nat.mem_primeFactors] at hpT
      exact hpT.1.2.1.trans (Nat.div_dvd_of_dvd h2N)
  have hTsplit : ∏ p ∈ S.erase 2, (if p ∣ N then Q p else 1) = ∏ p ∈ T, Q p := by
    rw [← Finset.prod_filter]
    rw [hTset]
  rw [hsplit, hP2, hstep', hTsplit, hE, hE2]
  ring

/-- The prime-power Euler factor of `F`. -/
private lemma tsum_prime_pow512 {p : ℕ} (hp : p.Prime) (N : ℕ) :
    (∑' e : ℕ, ((ArithmeticFunction.moebius (p ^ e) : ℤ) : ℝ) ^ 2 /
      (Nat.totient (p ^ e) : ℝ) ^ 2 *
        (∑ d ∈ (p ^ e).divisors,
          (if (p ^ e / d : ℕ) ∣ N then ((p ^ e / d : ℕ) : ℝ) else 0) *
            ((ArithmeticFunction.moebius d : ℤ) : ℝ)))
      = 1 + ((ArithmeticFunction.moebius p : ℤ) : ℝ) ^ 2 / (Nat.totient p : ℝ) ^ 2 *
        (∑ d ∈ p.divisors, (if (p / d : ℕ) ∣ N then ((p / d : ℕ) : ℝ) else 0) *
          ((ArithmeticFunction.moebius d : ℤ) : ℝ)) := by
  have hzero : ∀ e : ℕ, e ∉ ({0, 1} : Finset ℕ) →
      ((ArithmeticFunction.moebius (p ^ e) : ℤ) : ℝ) ^ 2 / (Nat.totient (p ^ e) : ℝ) ^ 2 *
        (∑ d ∈ (p ^ e).divisors,
          (if (p ^ e / d : ℕ) ∣ N then ((p ^ e / d : ℕ) : ℝ) else 0) *
            ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = 0 := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    obtain ⟨h0, h1⟩ := he
    have he2 : e ≠ 1 := h1
    have he0 : e ≠ 0 := h0
    have hmu : ArithmeticFunction.moebius (p ^ e) = 0 := by
      rw [ArithmeticFunction.moebius_apply_prime_pow hp he0]
      simp [he2]
    rw [hmu]
    norm_num
  rw [tsum_eq_sum (s := ({0, 1} : Finset ℕ)) hzero, Finset.sum_insert (by norm_num),
    Finset.sum_singleton]
  norm_num

/-- The real Ramanujan singular series as an Euler product. -/
private lemma hasSum_real512 (N : ℕ) (hN : 2 ≤ N) (hEven : Even N) :
    HasSum (fun q : ℕ => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
      (Nat.totient q : ℝ) ^ 2 *
        (∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) *
          ((ArithmeticFunction.moebius d : ℤ) : ℝ))) (sing (N / 2)) := by
  set F : ℕ → ℝ := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
      (Nat.totient q : ℝ) ^ 2 *
        (∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) *
          ((ArithmeticFunction.moebius d : ℤ) : ℝ)) with hF
  set G : ℕ → ℝ := fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2 with hG
  set Q : ℕ → ℝ := fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2) with hQ
  set T : Finset ℕ := (N / 2).primeFactors.filter (fun p => 2 < p) with hT
  have hF0 : F 0 = 0 := by
    simp only [hF, ArithmeticFunction.moebius]
    norm_num
  have hc1 : (∑ d ∈ (1 : ℕ).divisors,
      (if (1 / d : ℕ) ∣ N then ((1 / d : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = 1 := by
    rw [Nat.divisors_one, Finset.sum_singleton, Nat.div_one, if_pos (one_dvd N),
      ArithmeticFunction.moebius_apply_one]
    norm_num
  have hF1 : F 1 = 1 := by
    simp only [hF]
    rw [hc1, ArithmeticFunction.moebius_apply_one, Nat.totient_one]
    norm_num
  have hFmul : ∀ {m n : ℕ}, Nat.Coprime m n → F (m * n) = F m * F n := by
    intro m n hmn
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      have hn1 : n = 1 := by
        have h := hmn
        rwa [Nat.coprime_zero_left] at h
      subst hn1
      simp [hF0, hF1]
    · rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · subst hn0
        have hm1 : m = 1 := by
          have h := hmn
          rwa [Nat.coprime_zero_right] at h
        subst hm1
        simp [hF0, hF1]
      · simp only [hF]
        rw [c512_real_mul hmn hm0 hn0 N]
        have hmu : ((ArithmeticFunction.moebius (m * n) : ℤ) : ℝ) ^ 2 =
            ((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2 *
              ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 := by
          rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn]
          push_cast
          ring
        rw [hmu, Nat.totient_mul hmn]
        push_cast
        field_simp
        try ring
  have hsum : Summable (fun q : ℕ => ‖F q‖) := by
    have := summable_c512 N (by omega : 1 ≤ N)
    simpa only [hF] using this
  have hpp : ∀ p : ℕ, Nat.Prime p → (∑' e : ℕ, F (p ^ e)) = 1 + F p := by
    intro p hp
    have h := tsum_prime_pow512 hp N
    simpa only [hF] using h
  have hEuler := EulerProduct.eulerProduct (f := F) hF1 (fun {m n} hmn => hFmul hmn) hsum hF0
  have hlim1 : Filter.Tendsto (fun n : ℕ => ∏ p ∈ Nat.primesBelow n, (1 + F p))
      Filter.atTop (nhds (∑' q, F q)) := by
    refine hEuler.congr' (Filter.Eventually.of_forall (fun n => ?_))
    exact Finset.prod_congr rfl (fun p hp => hpp p (Nat.prime_of_mem_primesBelow hp))
  have hC2 : Filter.Tendsto (fun n : ℕ =>
      ∏ p ∈ (Finset.range n).filter (fun p => Nat.Prime p ∧ 2 < p), G p) Filter.atTop (nhds C2) := by
    have hsub := (hasProd_subtype_iff_mulIndicator (s := {p : ℕ | p.Prime ∧ 2 < p})
      (f := fun p : ℕ => 1 - 1 / ((p : ℝ) - 1) ^ 2)).mp Thm2.C2_multipliable.hasProd
    have h := hsub.tendsto_prod_nat
    refine h.congr' (Filter.Eventually.of_forall (fun n => ?_))
    simp only [Set.mulIndicator_apply, Set.mem_setOf_eq, hG, Finset.prod_filter]
  have hlim2 : Filter.Tendsto (fun n : ℕ =>
      2 * (∏ p ∈ (Finset.range n).filter (fun p => Nat.Prime p ∧ 2 < p), G p) *
        (∏ p ∈ T, Q p)) Filter.atTop (nhds (2 * C2 * ∏ p ∈ T, Q p)) :=
    (hC2.const_mul 2).mul_const _
  have heq : (fun n : ℕ => ∏ p ∈ Nat.primesBelow n, (1 + F p)) =ᶠ[Filter.atTop]
      (fun n : ℕ => 2 * (∏ p ∈ (Finset.range n).filter (fun p => Nat.Prime p ∧ 2 < p), G p) *
          (∏ p ∈ T, Q p)) := by
    filter_upwards [Filter.eventually_ge_atTop (N + 1)] with n hn
    have h := prod_local512 N n hN hEven (by omega)
    simpa only [hF, hG, hQ, hT, Nat.primesBelow] using h
  have hlim2' : Filter.Tendsto (fun n : ℕ => ∏ p ∈ Nat.primesBelow n, (1 + F p))
      Filter.atTop (nhds (2 * C2 * ∏ p ∈ T, Q p)) :=
    hlim2.congr' heq.symm
  have hZ : (∑' q : ℕ, F q) = 2 * C2 * ∏ p ∈ T, Q p := tendsto_nhds_unique hlim1 hlim2'
  have hsing : sing (N / 2) = 2 * C2 * ∏ p ∈ T, Q p := by
    simp only [Thm2.sing, hT, hQ]
  have hfin := hsum.of_norm.hasSum
  rw [hZ, ← hsing] at hfin
  exact hfin

/-! ### The squarefree evaluation -/

/-- `Σ_{e ∣ g} e · μ(g/e) = φ(g)`, the Dirichlet convolution `id * μ = φ`. -/
private lemma totient_conv323 (g : ℕ) (hg : 0 < g) :
    (∑ e ∈ g.divisors, (e : ℝ) * ((ArithmeticFunction.moebius (g / e) : ℤ) : ℝ))
      = (Nat.totient g : ℝ) := by
  have hrev : (∑ e ∈ g.divisors, (e : ℝ) * ((ArithmeticFunction.moebius (g / e) : ℤ) : ℝ))
      = ∑ e ∈ g.divisors,
          ((g / e : ℕ) : ℝ) * ((ArithmeticFunction.moebius e : ℤ) : ℝ) := by
    refine Finset.sum_nbij' (fun e => g / e) (fun e => g / e) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors ha), hg.ne'⟩
    · intro b hb
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hb), hg.ne'⟩
    · intro a ha
      exact Nat.div_div_self (Nat.dvd_of_mem_divisors ha) hg.ne'
    · intro b hb
      exact Nat.div_div_self (Nat.dvd_of_mem_divisors hb) hg.ne'
    · intro a ha
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors ha) hg.ne']
  have hinv : ∀ n : ℕ, 0 < n →
      (∑ x ∈ n.divisorsAntidiagonal,
          ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) * (x.2 : ℝ))
        = (Nat.totient n : ℝ) := by
    have hmain := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := fun n : ℕ => (Nat.totient n : ℝ)) (g := fun n : ℕ => (n : ℝ))).mp (by
        intro n hn
        have h := congrArg (fun k : ℕ => (k : ℝ)) (Nat.sum_totient n)
        simpa [Nat.cast_sum] using h)
    intro n hn
    exact hmain n hn
  rw [hrev, ← Nat.sum_divisorsAntidiagonal (f := fun a b =>
    ((b : ℕ) : ℝ) * ((ArithmeticFunction.moebius a : ℤ) : ℝ))]
  have hcongr : (∑ i ∈ g.divisorsAntidiagonal,
      ((i.2 : ℕ) : ℝ) * ((ArithmeticFunction.moebius i.1 : ℤ) : ℝ))
      = ∑ i ∈ g.divisorsAntidiagonal,
          ((ArithmeticFunction.moebius i.1 : ℤ) : ℝ) * (i.2 : ℝ) :=
    Finset.sum_congr rfl (fun i _ => by ring)
  rw [hcongr, hinv g hg]

/-- LEAF: Vaughan 1981 chapter 3, display 3.14 and the evaluation of the Ramanujan sum used
in the proof of display 3.23 on book page 34: for squarefree q the Ramanujan sum
c_q(-m) = Σ_{(a,q)=1} e(-am/q) equals μ(q/(q,m)) φ((q,m)), so its absolute value is
φ((q,m)). Class EASY: the lab's private `c512_real_form` in Decomp512a writes c_q as
Σ_{d|q} [q/d ∣ m] (q/d) μ(d), and for squarefree q = g r with g = (q,m) this is
μ(r) Σ_{e|g} e μ(g/e) = μ(r) φ(g). -/
private theorem leaf_ramanujan_sqfree_norm512 (q N : ℕ) (hq : Squarefree q) :
    ‖ramanujan512 q N‖ ≤ (Nat.totient (Nat.gcd q N) : ℝ) := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
  set g : ℕ := Nat.gcd q N with hgdef
  have hgq : g ∣ q := by rw [hgdef]; exact Nat.gcd_dvd_left q N
  have hgne : g ≠ 0 := by
    rintro h0
    rw [h0] at hgq
    exact hq0 (Nat.eq_zero_of_zero_dvd hgq)
  have hgpos : 0 < g := Nat.pos_of_ne_zero hgne
  set r : ℕ := q / g with hrdef
  have hqr : g * r = q := by
    rw [hrdef]; exact Nat.mul_div_cancel' hgq
  have hcop : Nat.Coprime r g := by
    set d : ℕ := Nat.gcd r g with hddef
    have hd1 : d ∣ g := Nat.gcd_dvd_right r g
    have hd2 : d ∣ r := Nat.gcd_dvd_left r g
    obtain ⟨g', hg'⟩ := hd1
    obtain ⟨r', hr'⟩ := hd2
    have hdvd : d * d ∣ q := by
      refine ⟨g' * r', ?_⟩
      rw [← hqr, hg', hr']
      ring
    have hunit : IsUnit d := (Squarefree.eq_1 q).mp hq d hdvd
    have hone : d = 1 := Nat.isUnit_iff.mp hunit
    exact Nat.coprime_iff_gcd_eq_one.mpr hone
  have hform : ramanujan512 q N = ((∑ e ∈ q.divisors,
      (if e ∣ N then ((e : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ) : ℝ) : ℂ) := by
    rw [c512_real_form q N hq1, c512_conv_form q N hqpos]
  have hsupp : (∑ e ∈ q.divisors, (if e ∣ N then ((e : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ))
      = ∑ e ∈ g.divisors,
          ((e : ℕ) : ℝ) * ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ) := by
    have hstep : (∑ e ∈ q.divisors, (if e ∣ N then ((e : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ))
        = ∑ e ∈ q.divisors,
            (if e ∣ N then
              ((e : ℕ) : ℝ) * ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ) else 0) := by
      refine Finset.sum_congr rfl (fun e _ => ?_)
      by_cases h : e ∣ N <;> simp [h]
    rw [hstep, ← Finset.sum_filter]
    have hf : q.divisors.filter (fun e => e ∣ N) = g.divisors := by
      rw [hgdef, Nat.gcd_comm]
      exact divisors_filter_dvd_eq_gcd512 (q := q) (a := N) hq0
    rw [hf]
  have hsplit : ∀ e ∈ g.divisors, ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ)
      = ((ArithmeticFunction.moebius r : ℤ) : ℝ) *
        ((ArithmeticFunction.moebius (g / e) : ℤ) : ℝ) := by
    intro e he
    have hepos : 0 < e := Nat.pos_of_mem_divisors he
    have hge : g = e * (g / e) := (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)).symm
    have h1 : q / e = (g / e) * r := by
      have hq' : q = e * ((g / e) * r) := by
        rw [← Nat.mul_assoc, hge.symm, hqr]
      rw [hq', Nat.mul_div_cancel_left _ hepos]
    have hcopge : Nat.Coprime r (g / e) :=
      hcop.coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors he))
    rw [h1, Nat.mul_comm (g / e) r,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcopge.gcd_eq_one]
    push_cast
    ring
  have hfac : (∑ e ∈ g.divisors, ((e : ℕ) : ℝ) *
        ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ))
      = ((ArithmeticFunction.moebius r : ℤ) : ℝ) * (Nat.totient g : ℝ) := by
    have hterm : ∀ e ∈ g.divisors, ((e : ℕ) : ℝ) *
        ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ)
        = ((ArithmeticFunction.moebius r : ℤ) : ℝ) *
          (((e : ℕ) : ℝ) * ((ArithmeticFunction.moebius (g / e) : ℤ) : ℝ)) := by
      intro e he
      rw [hsplit e he]; ring
    rw [Finset.sum_congr rfl hterm, ← totient_conv323 g hgpos, Finset.mul_sum]
  rw [hform, hsupp, hfac, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.totient g : ℝ))]
  have hmu : |((ArithmeticFunction.moebius r : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := r)
  calc |((ArithmeticFunction.moebius r : ℤ) : ℝ)| * (Nat.totient g : ℝ)
      ≤ 1 * (Nat.totient g : ℝ) :=
        mul_le_mul_of_nonneg_right hmu (by positivity)
    _ = (Nat.totient g : ℝ) := by rw [one_mul]

/-! ## 1. A product of distinct primes is squarefree -/

private lemma squarefree_prod_primes323 (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    Squarefree (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha' : Nat.Prime a := hs a (Finset.mem_insert_self a s)
    have hs' : ∀ p ∈ s, Nat.Prime p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hcop : a.Coprime (∏ p ∈ s, p) := by
      rw [ha'.coprime_iff_not_dvd]
      intro hdvd
      obtain ⟨p, hp, hap⟩ :=
        (Prime.dvd_finset_prod_iff (Nat.Prime.prime ha') (fun x : ℕ => x)).mp hdvd
      have hpp : Nat.Prime p := hs' p hp
      have hpa : p = a := (Nat.Prime.dvd_iff_eq hpp ha'.ne_one).mp hap
      exact ha (hpa ▸ hp)
    rw [Nat.squarefree_mul_iff]
    exact ⟨hcop, (Nat.Prime.prime ha').squarefree, ih hs'⟩

/-! ## 2. Euler product as a sum over squarefree divisors -/

private lemma sum_sqfree_divisors323 (n : ℕ) (hn : n ≠ 0) (w : ℕ → ℝ) :
    (∑ d ∈ n.divisors.filter (fun d => Squarefree d), ∏ p ∈ d.primeFactors, w p)
      = ∏ p ∈ n.primeFactors, (1 + w p) := by
  classical
  have hinj : Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) ↑(n.primeFactors.powerset) := by
    intro s hs t ht hst
    have hsp : ∀ p ∈ s, Nat.Prime p :=
      fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hs hp)
    have htp : ∀ p ∈ t, Nat.Prime p :=
      fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp)
    have hst' : (∏ p ∈ s, p) = (∏ p ∈ t, p) := by simpa using hst
    rw [← Nat.primeFactors_prod hsp, ← Nat.primeFactors_prod htp, hst']
  have himage : (n.primeFactors.powerset).image (fun t : Finset ℕ => ∏ p ∈ t, p)
      = n.divisors.filter (fun d => Squarefree d) := by
    ext d
    constructor
    · intro hd
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
      have ht' : t ⊆ n.primeFactors := Finset.mem_powerset.mp ht
      have htp : ∀ p ∈ t, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (ht' hp)
      refine Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨?_, hn⟩, squarefree_prod_primes323 t htp⟩
      exact (Finset.prod_dvd_prod_of_subset t n.primeFactors (fun p => p) ht').trans
        (Nat.prod_primeFactors_dvd n)
    · intro hd
      obtain ⟨hdv, hsq⟩ := Finset.mem_filter.mp hd
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hdv
      refine Finset.mem_image.mpr ⟨d.primeFactors, ?_, ?_⟩
      · rw [Finset.mem_powerset]
        intro p hp
        exact Nat.Prime.mem_primeFactors (Nat.prime_of_mem_primeFactors hp)
          (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdvd) hn
      · exact Nat.prod_primeFactors_of_squarefree hsq
  rw [← himage, Finset.sum_image (fun x hx y hy h => hinj hx hy h), Finset.prod_one_add]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Nat.primeFactors_prod
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp))]

/-! ## 3. `n / φ n` as a product over the primes -/

private lemma totient_ratio323 (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) / (Nat.totient n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hn0 : n ≠ 0 := by omega
  have hφ : (0 : ℝ) < (Nat.totient n : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hn
  have hcast : (Nat.totient n : ℝ) * ∏ p ∈ n.primeFactors, (p : ℝ)
      = (n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) (Nat.totient_mul_prod_primeFactors n)
    push_cast at h
    have hQ : (∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ))
        = ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
      refine Finset.prod_congr rfl (fun p hp => ?_)
      rw [Nat.cast_sub (Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hp)), Nat.cast_one]
    rw [hQ] at h
    exact h
  have hQ0 : (∏ p ∈ n.primeFactors, ((p : ℝ) - 1)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun p hp => ?_)
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp))
    linarith
  rw [Finset.prod_div_distrib, div_eq_div_iff (ne_of_gt hφ) hQ0]
  rw [mul_comm (∏ p ∈ n.primeFactors, (p : ℝ)) (Nat.totient n : ℝ)]
  exact hcast.symm

/-! ## 4. The exact Dirichlet convolution identity -/

private lemma sq_div_totient_sq323 (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) / (Nat.totient n : ℝ)) ^ 2
      = ∑ d ∈ n.divisors.filter (fun d => Squarefree d),
          ∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) := by
  have hn0 : n ≠ 0 := by omega
  rw [totient_ratio323 n hn, ← Finset.prod_pow]
  have h1 : ∀ p ∈ n.primeFactors,
      ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 = 1 + (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 := by
    intro p hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp))
    have hp1 : ((p : ℝ) - 1) ≠ 0 := by linarith
    field_simp
    ring
  rw [Finset.prod_congr rfl h1]
  exact (sum_sqfree_divisors323 n hn0 _).symm

/-! ## 5. The reciprocal square tail -/

private lemma inv_sq_Ioo_le323 (t : ℝ) (ht : 0 < t) (N : ℕ) :
    (∑ k ∈ Finset.Ioo ⌊t⌋₊ N, ((k : ℝ) ^ 2)⁻¹) ≤ 2 / t := by
  have h1 : (∑ k ∈ Finset.Ioo ⌊t⌋₊ N, ((k : ℝ) ^ 2)⁻¹) ≤ 2 / ((⌊t⌋₊ : ℝ) + 1) :=
    sum_Ioo_inv_sq_le ⌊t⌋₊ N
  have h2 : (2 : ℝ) / ((⌊t⌋₊ : ℝ) + 1) ≤ 2 / t :=
    div_le_div_of_nonneg_left (by norm_num) ht (le_of_lt (Nat.lt_floor_add_one t))
  linarith

/-! ## 6. The per-prime weight against `p^{-3/2}` -/

private lemma wprime_le323 {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) :
    (2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2) ≤ (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hpR : (7 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp7
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hpoly : (2 * (p : ℝ) - 1) ^ 2 * (p : ℝ) ≤ ((p : ℝ) - 1) ^ 4 := by
    have hfac : ((p : ℝ) - 1) ^ 4 - (2 * (p : ℝ) - 1) ^ 2 * (p : ℝ)
        = ((p : ℝ) - 7) * ((p : ℝ) ^ 3 - (p : ℝ) ^ 2 + 3 * (p : ℝ) + 16) + 113 := by ring
    have h1 : (0 : ℝ) ≤ (p : ℝ) - 7 := by linarith
    have h2 : (0 : ℝ) ≤ (p : ℝ) ^ 3 - (p : ℝ) ^ 2 + 3 * (p : ℝ) + 16 := by nlinarith [hp0]
    nlinarith
  have hmul : (2 * (p : ℝ) - 1) * Real.sqrt (p : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by
    have hsq1 : ((2 * (p : ℝ) - 1) * Real.sqrt (p : ℝ)) ^ 2
        = (2 * (p : ℝ) - 1) ^ 2 * (p : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]
    have h4 : (((p : ℝ) - 1) ^ 2) ^ 2 = ((p : ℝ) - 1) ^ 4 := by ring
    have ha0 : (0 : ℝ) ≤ (2 * (p : ℝ) - 1) * Real.sqrt (p : ℝ) := by
      have hs := Real.sqrt_nonneg (p : ℝ)
      nlinarith [hp0, hs]
    have hb0 : (0 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by positivity
    nlinarith [hsq1, hpoly, ha0, hb0, sq_nonneg ((2 * (p : ℝ) - 1) * Real.sqrt (p : ℝ) - ((p : ℝ) - 1) ^ 2), h4]
  have hrpow : (p : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / ((p : ℝ) * Real.sqrt (p : ℝ)) := by
    have h3 : (p : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (p : ℝ) := (Real.sqrt_eq_rpow (p : ℝ)).symm
    rw [Real.rpow_neg (le_of_lt hp0),
      show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp0, Real.rpow_one, h3,
      one_div]
  rw [hrpow, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hmul, hp0]

/-! ## 7. An `rpow` product identity -/

private lemma prod_rpow323 (s : Finset ℕ) (h : ∀ p ∈ s, 0 < p) :
    (∏ p ∈ s, (p : ℝ) ^ (-(3 / 2 : ℝ))) = ((∏ p ∈ s, p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast h a (Finset.mem_insert_self a s)
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul,
        Real.mul_rpow (le_of_lt ha0) (by positivity)]
      rw [ih (fun p hp => h p (Finset.mem_insert_of_mem hp))]

/-! ## 8. The small primes -/

private lemma wsmall_le323 {p : ℕ} (hp : 2 ≤ p) :
    (2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2) ≤ 3 / 2 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hden : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) ^ 2 := by positivity
  rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)]
  have hfac : 3 * ((p : ℝ) * ((p : ℝ) - 1) ^ 2) - (2 * (p : ℝ) - 1) * 2
      = ((p : ℝ) - 2) * (3 * (p : ℝ) ^ 2 - 1) := by ring
  have h1 : (0 : ℝ) ≤ (p : ℝ) - 2 := by linarith
  have h2 : (0 : ℝ) ≤ 3 * (p : ℝ) ^ 2 - 1 := by nlinarith
  have h3 : (0 : ℝ) ≤ ((p : ℝ) - 2) * (3 * (p : ℝ) ^ 2 - 1) := mul_nonneg h1 h2
  linarith

/-! ## 9. The weight of a squarefree `d` -/

private lemma weightd_nonneg323 (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    0 ≤ ∏ p ∈ s, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)) := by
  refine Finset.prod_nonneg (fun p hp => ?_)
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hs p hp).two_le
  have h3 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h4 : (0 : ℝ) ≤ 2 * (p : ℝ) - 1 := by linarith
  have h5 : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) ^ 2 := by positivity
  exact div_nonneg h4 (le_of_lt h5)

/-- Product comparison for nonnegative real factors (induction form). -/
private lemma prod_le_prod_real323 (f g : ℕ → ℝ) :
    ∀ s : Finset ℕ, (∀ p ∈ s, f p ≤ g p) → (∀ p ∈ s, 0 ≤ f p) → (∀ p ∈ s, 0 ≤ g p) →
      (∏ p ∈ s, f p) ≤ ∏ p ∈ s, g p := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | insert a s ha ih =>
      intro hs hs0 hg0
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have ha1 : f a ≤ g a := hs a (Finset.mem_insert_self a s)
      have ha0 : 0 ≤ f a := hs0 a (Finset.mem_insert_self a s)
      have hga0 : 0 ≤ g a := hg0 a (Finset.mem_insert_self a s)
      have hs1 : ∀ p ∈ s, f p ≤ g p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have hs2 : ∀ p ∈ s, 0 ≤ f p := fun p hp => hs0 p (Finset.mem_insert_of_mem hp)
      have hs3 : ∀ p ∈ s, 0 ≤ g p := fun p hp => hg0 p (Finset.mem_insert_of_mem hp)
      exact mul_le_mul ha1 (ih hs1 hs2 hs3) (Finset.prod_nonneg hs2) hga0

private lemma weight_le323 (d : ℕ) (hd : Squarefree d) :
    (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
      ≤ 1000 * (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
  classical
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · rw [h0] at hd
    exact absurd hd (by simp)
  have hd0 : d ≠ 0 := hpos.ne'
  set A : Finset ℕ := d.primeFactors.filter (fun p => p < 7) with hA
  set B : Finset ℕ := d.primeFactors.filter (fun p => ¬ p < 7) with hB
  have hsplit : (∏ p ∈ d.primeFactors,
        ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
      = (∏ p ∈ A, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))) *
        (∏ p ∈ B, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))) := by
    rw [hA, hB, Finset.prod_filter_mul_prod_filter_not]
  have hAsub : A ⊆ ({2, 3, 5} : Finset ℕ) := by
    intro p hp
    rw [hA, Finset.mem_filter] at hp
    obtain ⟨hpd, hp7⟩ := hp
    have hp' : Nat.Prime p := Nat.prime_of_mem_primeFactors hpd
    have hmem : p ∈ Finset.filter Nat.Prime (Finset.range 7) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hp7, hp'⟩
    have hsub : Finset.filter Nat.Prime (Finset.range 7) ⊆ ({2, 3, 5} : Finset ℕ) := by
      decide
    exact hsub hmem
  have hAsmall : (∏ p ∈ A, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
      ≤ 3.375 := by
    have h1 : ∀ p ∈ A, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)) ≤ 3 / 2 := by
      intro p hp
      rw [hA] at hp
      obtain ⟨hpd, hp7⟩ := Finset.mem_filter.mp hp
      exact wsmall_le323 (Nat.prime_of_mem_primeFactors hpd).two_le
    have h0 : ∀ p ∈ A, (0 : ℝ) ≤ (2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2) := by
      intro p hp
      rw [hA] at hp
      obtain ⟨hpd, hp7⟩ := Finset.mem_filter.mp hp
      have hp' : Nat.Prime p := Nat.prime_of_mem_primeFactors hpd
      have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp'.two_le
      have : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by
        have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        positivity
      have : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) ^ 2 := by positivity
      have : (0 : ℝ) ≤ 2 * (p : ℝ) - 1 := by linarith
      exact div_nonneg this (le_of_lt ‹(0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) ^ 2›)
    calc (∏ p ∈ A, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
        ≤ ∏ p ∈ A, (3 / 2 : ℝ) :=
          prod_le_prod_real323 _ _ A h1 h0 (fun p _ => by norm_num)
      _ = (3 / 2 : ℝ) ^ A.card := Finset.prod_const (3 / 2 : ℝ)
      _ ≤ (3 / 2 : ℝ) ^ 3 := by
          apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3 / 2)
          calc A.card ≤ ({2, 3, 5} : Finset ℕ).card := Finset.card_le_card hAsub
            _ = 3 := by decide
      _ = 3.375 := by norm_num
  have hBbig : (∏ p ∈ B, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
      ≤ ((∏ p ∈ B, p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have h1 : ∀ p ∈ B, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))
        ≤ (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
      intro p hp
      rw [hB] at hp
      obtain ⟨hpd, hp7⟩ := Finset.mem_filter.mp hp
      exact wprime_le323 (Nat.prime_of_mem_primeFactors hpd) (by omega)
    have h0 : ∀ p ∈ B, (0 : ℝ) ≤ (2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2) := by
      intro p hp
      rw [hB] at hp
      obtain ⟨hpd, hp7⟩ := Finset.mem_filter.mp hp
      have hp' : Nat.Prime p := Nat.prime_of_mem_primeFactors hpd
      have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp'.two_le
      have h3 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have h4 : (0 : ℝ) ≤ 2 * (p : ℝ) - 1 := by linarith
      have : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) ^ 2 := by positivity
      exact div_nonneg h4 (le_of_lt this)
    calc (∏ p ∈ B, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
        ≤ ∏ p ∈ B, (p : ℝ) ^ (-(3 / 2 : ℝ)) :=
          prod_le_prod_real323 _ _ B h1 h0
            (fun p hp => Real.rpow_nonneg (by positivity) _)
      _ = ((∏ p ∈ B, p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) :=
          prod_rpow323 B (fun p hp => by
            rw [hB] at hp
            exact Nat.Prime.pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1))
  have hd_eq : d = (∏ p ∈ A, p) * (∏ p ∈ B, p) := by
    rw [hA, hB, Finset.prod_filter_mul_prod_filter_not,
      Nat.prod_primeFactors_of_squarefree hd]
  have hB30 : ((∏ p ∈ B, p : ℕ) : ℝ) ≥ (d : ℝ) / 30 := by
    have hAle : (∏ p ∈ A, p) ≤ 30 := by
      have hdvd : (∏ p ∈ A, p) ∣ ∏ p ∈ ({2, 3, 5} : Finset ℕ), p :=
        Finset.prod_dvd_prod_of_subset A _ (fun p => p) hAsub
      have hval : (∏ p ∈ ({2, 3, 5} : Finset ℕ), p) = 30 := by decide
      rw [hval] at hdvd
      exact Nat.le_of_dvd (by norm_num) hdvd
    have hBpos : 0 < (∏ p ∈ B, p) := by
      refine Finset.prod_pos (fun p hp => ?_)
      rw [hB] at hp
      exact Nat.Prime.pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
    have hBposR : (0 : ℝ) < ((∏ p ∈ B, p : ℕ) : ℝ) := by exact_mod_cast hBpos
    have hcast : (d : ℝ) = ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ B, p : ℕ) : ℝ) := by
      rw [hd_eq]; push_cast; ring
    have hAleR : ((∏ p ∈ A, p : ℕ) : ℝ) ≤ 30 := by exact_mod_cast hAle
    rw [hcast, ge_iff_le, div_le_iff₀ (by norm_num : (0 : ℝ) < 30)]
    nlinarith [hAleR, hBposR]
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hpos
  have hm32 : ((∏ p ∈ B, p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))
      ≤ (180 : ℝ) * (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have hd30 : (0 : ℝ) < (d : ℝ) / 30 := by positivity
    have h1 := Real.rpow_le_rpow_of_nonpos hd30 hB30 (by norm_num : (-(3 / 2 : ℝ)) ≤ 0)
    have h2 : ((d : ℝ) / 30) ^ (-(3 / 2 : ℝ))
        = (30 : ℝ) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [Real.div_rpow (le_of_lt hdR) (by norm_num : (0 : ℝ) ≤ 30),
        Real.rpow_neg (le_of_lt hdR), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 30)]
      field_simp
    have h3 : (30 : ℝ) ^ (3 / 2 : ℝ) ≤ 180 := by
      have h : (30 : ℝ) ^ (3 / 2 : ℝ) = 30 * Real.sqrt 30 := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
          Real.rpow_add (by norm_num : (0 : ℝ) < 30), Real.rpow_one, ← Real.sqrt_eq_rpow]
      rw [h]
      have hsq : Real.sqrt 30 ≤ 6 := by
        have hle := Real.sqrt_le_sqrt (show (30 : ℝ) ≤ 36 by norm_num)
        have h36 : (36 : ℝ) = 6 ^ 2 := by norm_num
        rw [h36, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 6)] at hle
        exact hle
      nlinarith
    calc ((∏ p ∈ B, p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))
        ≤ ((d : ℝ) / 30) ^ (-(3 / 2 : ℝ)) := h1
      _ = (30 : ℝ) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (-(3 / 2 : ℝ)) := h2
      _ ≤ 180 * (d : ℝ) ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (le_of_lt hdR) _)
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (le_of_lt hdR) _
  calc (∏ p ∈ d.primeFactors,
        ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
      = (∏ p ∈ A, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))) *
        (∏ p ∈ B, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))) := hsplit
    _ ≤ 3.375 * ((∏ p ∈ B, p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) :=
        mul_le_mul hAsmall hBbig
          (weightd_nonneg323 B (fun p hp => by
            rw [hB, Finset.mem_filter] at hp
            exact Nat.prime_of_mem_primeFactors hp.1))
          (by norm_num)
    _ ≤ 3.375 * (180 * (d : ℝ) ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hm32 (by norm_num)
    _ = 607.5 * (d : ℝ) ^ (-(3 / 2 : ℝ)) := by ring
    _ ≤ 1000 * (d : ℝ) ^ (-(3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right (by norm_num) hd_nn

/-! ## 10. Multiples of `d` in the tail -/

private lemma multiples_tail323 (Z : ℝ) (hZ : 0 < Z) (R d : ℕ) (hd : 1 ≤ d) :
    (∑ n ∈ ((Finset.Icc 1 R).filter (fun n : ℕ => Z < (n : ℝ))).filter (fun n => d ∣ n),
        1 / (n : ℝ) ^ 2)
      ≤ (1 / (d : ℝ) ^ 2) * (2 / (Z / (d : ℝ))) := by
  classical
  have hdpos : 0 < d := hd
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  set S : Finset ℕ :=
    ((Finset.Icc 1 R).filter (fun n : ℕ => Z < (n : ℝ))).filter (fun n => d ∣ n) with hS
  have hmem : ∀ n ∈ S, 1 ≤ n ∧ n ≤ R ∧ Z < (n : ℝ) ∧ d ∣ n := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hn
    exact ⟨hn.1.1.1, hn.1.1.2, hn.1.2, hn.2⟩
  have hinj : Set.InjOn (fun n : ℕ => n / d) ↑S := by
    intro a ha b hb hab
    obtain ⟨-, -, -, hadvd⟩ := hmem a ha
    obtain ⟨-, -, -, hbdvd⟩ := hmem b hb
    simp only at hab
    rw [← Nat.mul_div_cancel' hadvd, ← Nat.mul_div_cancel' hbdvd, hab]
  have hterm : ∀ n ∈ S, 1 / (n : ℝ) ^ 2 = (1 / (d : ℝ) ^ 2) * (1 / ((n / d : ℕ) : ℝ) ^ 2) := by
    intro n hn
    obtain ⟨hn1, -, -, hdvd⟩ := hmem n hn
    have hn0 : 0 < n := hn1
    have hn_eq : n = d * (n / d) := (Nat.mul_div_cancel' hdvd).symm
    have h2 : ((n : ℝ)) = (d : ℝ) * ((n / d : ℕ) : ℝ) := by
      conv_lhs => rw [hn_eq]
      push_cast
      ring
    rw [h2, mul_pow]
    ring
  have hsub : S.image (fun n => n / d) ⊆ Finset.Ioo ⌊Z / (d : ℝ)⌋₊ (R + 1) := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hn1, hnR, hnZ, hdvd⟩ := hmem n hn
    have hn0 : 0 < n := hn1
    have hn_eq : n = d * (n / d) := (Nat.mul_div_cancel' hdvd).symm
    have he : ((n : ℝ)) = (d : ℝ) * ((n / d : ℕ) : ℝ) := by
      conv_lhs => rw [hn_eq]
      push_cast
      ring
    have h1 : Z / (d : ℝ) < ((n / d : ℕ) : ℝ) := by
      rw [div_lt_iff₀ hdR]
      linarith [hnZ, he]
    have h2 : ((⌊Z / (d : ℝ)⌋₊ : ℕ) : ℝ) < ((n / d : ℕ) : ℝ) :=
      lt_of_le_of_lt (Nat.floor_le (by positivity : (0 : ℝ) ≤ Z / (d : ℝ))) h1
    have h2' : ⌊Z / (d : ℝ)⌋₊ < n / d := by exact_mod_cast h2
    have h3 : n / d ≤ R := Nat.le_trans (Nat.div_le_self n d) hnR
    exact Finset.mem_Ioo.mpr ⟨h2', by omega⟩
  calc (∑ n ∈ S, 1 / (n : ℝ) ^ 2)
      = ∑ n ∈ S, (1 / (d : ℝ) ^ 2) * (1 / ((n / d : ℕ) : ℝ) ^ 2) :=
        Finset.sum_congr rfl hterm
    _ = (1 / (d : ℝ) ^ 2) * ∑ n ∈ S, 1 / ((n / d : ℕ) : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
    _ = (1 / (d : ℝ) ^ 2) * ∑ k ∈ S.image (fun n => n / d), 1 / (k : ℝ) ^ 2 := by
        rw [← Finset.sum_image (f := fun k : ℕ => 1 / (k : ℝ) ^ 2) (g := fun n : ℕ => n / d)
          (fun x hx y hy h => hinj hx hy h)]
    _ ≤ (1 / (d : ℝ) ^ 2) * ∑ k ∈ Finset.Ioo ⌊Z / (d : ℝ)⌋₊ (R + 1), 1 / (k : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    _ ≤ (1 / (d : ℝ) ^ 2) * (2 / (Z / (d : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h := inv_sq_Ioo_le323 (Z / (d : ℝ)) (by positivity) (R + 1)
        simpa [one_div] using h

/-! ## 11. The Euler product gives `n / φ n` with coefficients `2/p` -/

private lemma weight_nonneg323 (d : ℕ) :
    0 ≤ ∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) := by
  refine Finset.prod_nonneg (fun p hp => ?_)
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp))
  have h3 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h4 : (0 : ℝ) ≤ 2 * (p : ℝ) - 1 := by linarith
  have h5 : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by positivity
  exact div_nonneg h4 (le_of_lt h5)

/-! ## 12. The leaf -/

private lemma tail_bound323 (Z : ℝ) (hZ : 0 < Z) (R : ℕ) :
    (∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => Z < (r : ℝ)),
        1 / (Nat.totient r : ℝ) ^ 2)
      ≤ 2 * (1000 * (∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)))) / Z := by
  classical
  set T : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) with hTdef
  have hTsum : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  set D : Finset ℕ := Finset.Icc 1 R with hD
  set S : Finset ℕ := D.filter (fun n : ℕ => Z < (n : ℝ)) with hS
  have hSmem : ∀ n ∈ S, 1 ≤ n ∧ n ≤ R := by
    intro n hn
    rw [hS, hD, Finset.mem_filter, Finset.mem_Icc] at hn
    exact hn.1
  -- (A) the pointwise convolution bound
  have hA : ∀ n ∈ S, 1 / (Nat.totient n : ℝ) ^ 2
      ≤ (1 / (n : ℝ) ^ 2) * (∑ d ∈ D, if (d ∣ n ∧ Squarefree d) then
          (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0) := by
    intro n hn
    obtain ⟨hn1, hnR⟩ := hSmem n hn
    have hn0 : n ≠ 0 := by omega
    have hdiv : (n.divisors.filter (fun d => Squarefree d))
        = D.filter (fun d => d ∣ n ∧ Squarefree d) := by
      ext d
      simp only [hD, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdv, hsq⟩
        have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hdv
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
          le_trans (Nat.le_of_dvd (by omega) hdvd) hnR⟩, hdvd, hsq⟩
      · rintro ⟨⟨h1, h2⟩, hdvd, hsq⟩
        exact ⟨Nat.mem_divisors.mpr ⟨hdvd, hn0⟩, hsq⟩
    have htwo : (∑ d ∈ D, if (d ∣ n ∧ Squarefree d) then
          (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0)
        = ∑ d ∈ n.divisors.filter (fun d => Squarefree d),
            ∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) := by
      rw [← Finset.sum_filter, hdiv]
    have hkey : 1 / (Nat.totient n : ℝ) ^ 2
        = (1 / (n : ℝ) ^ 2) * ((n : ℝ) / (Nat.totient n : ℝ)) ^ 2 := by
      rw [div_pow]
      field_simp
    rw [hkey, sq_div_totient_sq323 n hn1, htwo]
  -- (B) exchange the two sums
  have hB : (∑ n ∈ S, 1 / (Nat.totient n : ℝ) ^ 2)
      ≤ ∑ d ∈ D, (if Squarefree d then
          (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0) *
          (∑ n ∈ S.filter (fun n => d ∣ n), 1 / (n : ℝ) ^ 2) := by
    calc (∑ n ∈ S, 1 / (Nat.totient n : ℝ) ^ 2)
        ≤ ∑ n ∈ S, (1 / (n : ℝ) ^ 2) * (∑ d ∈ D, if (d ∣ n ∧ Squarefree d) then
            (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0) :=
          Finset.sum_le_sum hA
      _ = ∑ n ∈ S, ∑ d ∈ D, (1 / (n : ℝ) ^ 2) *
            (if (d ∣ n ∧ Squarefree d) then
              (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0) := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ d ∈ D, ∑ n ∈ S, (1 / (n : ℝ) ^ 2) *
            (if (d ∣ n ∧ Squarefree d) then
              (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0) :=
          Finset.sum_comm
      _ = ∑ d ∈ D, (if Squarefree d then
            (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0) *
            (∑ n ∈ S.filter (fun n => d ∣ n), 1 / (n : ℝ) ^ 2) := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          by_cases hsq : Squarefree d
          · rw [if_pos hsq]
            have hL : (∑ n ∈ S, (1 / (n : ℝ) ^ 2) * (if (d ∣ n ∧ Squarefree d) then
                (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0))
                = ∑ n ∈ S.filter (fun n => d ∣ n),
                    (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) *
                      (1 / (n : ℝ) ^ 2) := by
              have hstep : ∀ n ∈ S, (1 / (n : ℝ) ^ 2) * (if (d ∣ n ∧ Squarefree d) then
                    (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0)
                  = (if d ∣ n then
                    (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) *
                      (1 / (n : ℝ) ^ 2) else 0) := by
                intro n _
                by_cases h : d ∣ n
                · rw [if_pos ⟨h, hsq⟩, if_pos h]; ring
                · rw [if_neg (fun hh => h hh.1), if_neg h, mul_zero]
              rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter]
            rw [hL, Finset.mul_sum]
          · rw [if_neg hsq, zero_mul]
            refine Finset.sum_eq_zero (fun n _ => ?_)
            rw [if_neg (fun h => hsq h.2), mul_zero]
  -- (C) the bound for each `d`
  have hC : ∀ d ∈ D, (if Squarefree d then
        (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0) *
        (∑ n ∈ S.filter (fun n => d ∣ n), 1 / (n : ℝ) ^ 2)
      ≤ (if Squarefree d then
          (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
          else 0) * (2 / Z) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hinner := multiples_tail323 Z hZ R d hd1
    by_cases hsq : Squarefree d
    · rw [if_pos hsq, if_pos hsq]
      have hGn : 0 ≤ ∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) :=
        weight_nonneg323 d
      have hdR : (0 : ℝ) < (d : ℝ) := by
        have h0 : 0 < d := by omega
        exact_mod_cast h0
      have hsplit : (∏ p ∈ d.primeFactors,
            ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))) * (d : ℝ)
          = ∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) := by
        have hd_cast : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
          rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
        rw [hd_cast, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun p hp => ?_)
        have h2 : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp))
        have hp0 : (p : ℝ) ≠ 0 := by linarith
        have hp1 : ((p : ℝ) - 1) ≠ 0 := by linarith
        field_simp
      have hZd : (0 : ℝ) < Z / (d : ℝ) := by positivity
      calc (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) *
              (∑ n ∈ S.filter (fun n => d ∣ n), 1 / (n : ℝ) ^ 2)
          ≤ (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) *
              ((1 / (d : ℝ) ^ 2) * (2 / (Z / (d : ℝ)))) :=
            mul_le_mul_of_nonneg_left hinner hGn
        _ = (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))) *
              (2 / Z) := by
            rw [← hsplit]
            field_simp
    · rw [if_neg hsq, if_neg hsq, zero_mul, zero_mul]
  -- (D) bound the `d`-sum
  have hDsum : (∑ d ∈ D, (if Squarefree d then
        (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))) else 0))
      ≤ 1000 * T := by
    have h1 : ∀ d ∈ D, (if Squarefree d then
        (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))) else 0)
        ≤ 1000 * (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
      intro d hd
      by_cases hsq : Squarefree d
      · rw [if_pos hsq]
        exact weight_le323 d hsq
      · rw [if_neg hsq]
        have hdR : (0 : ℝ) < (d : ℝ) := by
          have h0 : 0 < d := by
            have := hd
            rw [hD, Finset.mem_Icc] at this
            omega
          exact_mod_cast h0
        have hnn := Real.rpow_nonneg (le_of_lt hdR) (-(3 / 2 : ℝ))
        nlinarith
    calc (∑ d ∈ D, (if Squarefree d then
          (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))) else 0))
        ≤ ∑ d ∈ D, 1000 * (d : ℝ) ^ (-(3 / 2 : ℝ)) := Finset.sum_le_sum h1
      _ = 1000 * ∑ d ∈ D, (d : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ 1000 * T := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact hTsum.sum_le_tsum D (fun i _ => Real.rpow_nonneg (by positivity) _)
  have key : (∑ r ∈ S, 1 / (Nat.totient r : ℝ) ^ 2) ≤ 2 * (1000 * T) / Z := by
    calc (∑ r ∈ S, 1 / (Nat.totient r : ℝ) ^ 2)
        ≤ ∑ d ∈ D, (if Squarefree d then
              (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0) *
              (∑ n ∈ S.filter (fun n => d ∣ n), 1 / (n : ℝ) ^ 2) := hB
      _ ≤ ∑ d ∈ D, (if Squarefree d then
              (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
              else 0) * (2 / Z) := Finset.sum_le_sum hC
      _ = (2 / Z) * ∑ d ∈ D, (if Squarefree d then
              (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
              else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          ring
      _ ≤ (2 / Z) * (1000 * T) := mul_le_mul_of_nonneg_left hDsum (by positivity)
      _ = 2 * (1000 * T) / Z := by ring
  exact key

/-- LEAF: Vaughan 1981 chapter 3, book page 34, the elementary fact printed under display
3.23: Σ_{q>Z} φ(q)^{-2} ≪ Z^{-1}, together with the convergence of Σ_q φ(q)^{-2}, which
gives the bound min(Z^{-1}, 1) for every Z > 0, uniformly in the upper cutoff R.
Class MEDIUM: from Σ_{q≤R} (q/φ(q))² ≪ R, which follows from
q/φ(q) = Σ_{d|q} μ(d)²/φ(d), and partial summation. -/
private theorem leaf_totient_sq_tail512 :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Z : ℝ, 0 < Z → ∀ R : ℕ,
      ∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => Z < (r : ℝ)),
          1 / (Nat.totient r : ℝ) ^ 2 ≤ K * min (1 / Z) 1 := by
  classical
  set T : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) with hTdef
  have hT0 : 0 ≤ T := tsum_nonneg (fun n => Real.rpow_nonneg (by positivity) _)
  refine ⟨2 * (1000 * T) + 2, by linarith, ?_⟩
  intro Z hZ R
  by_cases hZ1 : Z ≤ 1
  · -- `min (1/Z) 1 = 1`: bound the whole range by `1 + Σ_{r>1}`
    have hstep1 : (∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => Z < (r : ℝ)),
        1 / (Nat.totient r : ℝ) ^ 2) ≤ ∑ r ∈ Finset.Icc 1 R, 1 / (Nat.totient r : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => by positivity)
    have hsub2 : Finset.Icc 1 R ⊆
        insert 1 ((Finset.Icc 1 R).filter (fun r : ℕ => 1 < (r : ℝ))) := by
      intro r hr
      rw [Finset.mem_Icc] at hr
      rcases eq_or_lt_of_le hr.1 with h | h
      · rw [← h]; exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hr, ?_⟩)
        have : (1 : ℝ) < (r : ℝ) := by exact_mod_cast h
        exact this
    have hnin : (1 : ℕ) ∉ (Finset.Icc 1 R).filter (fun r : ℕ => 1 < (r : ℝ)) := by
      simp
    have hstep2 : (∑ r ∈ Finset.Icc 1 R, 1 / (Nat.totient r : ℝ) ^ 2)
        ≤ 1 + ∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => 1 < (r : ℝ)),
            1 / (Nat.totient r : ℝ) ^ 2 := by
      calc (∑ r ∈ Finset.Icc 1 R, 1 / (Nat.totient r : ℝ) ^ 2)
          ≤ ∑ r ∈ insert 1 ((Finset.Icc 1 R).filter (fun r : ℕ => 1 < (r : ℝ))),
              1 / (Nat.totient r : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun i _ _ => by positivity)
        _ = 1 / (Nat.totient 1 : ℝ) ^ 2 +
              ∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => 1 < (r : ℝ)),
                1 / (Nat.totient r : ℝ) ^ 2 := Finset.sum_insert hnin
        _ = 1 + ∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => 1 < (r : ℝ)),
                1 / (Nat.totient r : ℝ) ^ 2 := by
            rw [Nat.totient_one]; norm_num
    have hstep3 : (∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => 1 < (r : ℝ)),
        1 / (Nat.totient r : ℝ) ^ 2) ≤ 2 * (1000 * T) / 1 := tail_bound323 1 one_pos R
    have hmin : min (1 / Z) 1 = 1 := by
      apply min_eq_right
      rw [le_div_iff₀ hZ]
      linarith
    rw [hmin]
    linarith
  · have hZgt : 1 < Z := not_le.mp hZ1
    have hmin : min (1 / Z) 1 = 1 / Z := by
      apply min_eq_left
      rw [div_le_one hZ]
      linarith
    rw [hmin]
    have hstep1 : (∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => Z < (r : ℝ)),
        1 / (Nat.totient r : ℝ) ^ 2) ≤ 2 * (1000 * T) / Z := tail_bound323 Z hZ R
    have hstep2 : 2 * (1000 * T) / Z ≤ (2 * (1000 * T) + 2) / Z := by
      rw [add_div]
      have : (0 : ℝ) ≤ 2 / Z := by positivity
      linarith
    have hstep3 : (2 * (1000 * T) + 2) / Z = (2 * (1000 * T) + 2) * (1 / Z) := by
      rw [mul_one_div]
    linarith


/-- LEAF, CITED. R. C. Vaughan, The Hardy-Littlewood Method, Cambridge 1981, chapter 3,
book page 34, display 3.23, read from the page image of `copies/Vaughan1981-ch3.pdf` pdf
page 9: for every positive integer m and 0 < X < Y,
Σ_{X<q≤Y} μ(q)²/φ(q)² Σ_{a ≤ q, (a,q)=1} e(-am/q) ≪ Σ_{d|m} μ(d)²/φ(d) min(d/X, 1),
with an absolute implied constant. The inner sum is the lab's `ramanujan512 q m`; the
range X < q ≤ Y over integers is written `Ioc ⌊X⌋₊ M`. Vaughan proves it from 3.14 and the
elementary fact Σ_{q>Z} φ(q)^{-2} ≪ Z^{-1}, printed under 3.23. Split from
`leaf_vaughan_tail_reduction512`, REREAD U-1740, 2026-11-21.
PROVED 2026-11-23 by the inlined Vaughan argument, no sorry: display 3.14 is
`leaf_ramanujan_sqfree_norm512`, the elementary fact is `leaf_totient_sq_tail512`, and the
fibre bound sorts the squarefree q by g = gcd q N and sends each fibre into the r tail. -/
theorem leaf_vaughan_323_512 :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → ∀ X : ℝ, 0 < X → ∀ M : ℕ,
      ‖∑ q ∈ Finset.Ioc ⌊X⌋₊ M,
          (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
            ramanujan512 q N‖ ≤
        K * ∑ d ∈ N.divisors,
          (ArithmeticFunction.moebius d : ℝ) ^ 2 / (Nat.totient d : ℝ) *
            min ((d : ℝ) / X) 1 := by
  obtain ⟨K, hK0, hK⟩ := leaf_totient_sq_tail512
  refine ⟨K, hK0, fun N hN X hX M => ?_⟩
  set S := Finset.Ioc ⌊X⌋₊ M with hS
  let f : ℕ → ℝ := fun q =>
    if Squarefree q then (Nat.totient (Nat.gcd q N) : ℝ) / (Nat.totient q : ℝ) ^ 2 else 0
  have hf0 : ∀ q, 0 ≤ f q := by
    intro q; simp only [f]; split_ifs <;> positivity
  -- step 1: triangle inequality and the Ramanujan bound
  have step1 : ‖∑ q ∈ S, (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
      ramanujan512 q N‖ ≤ ∑ q ∈ S, f q := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    by_cases hq : Squarefree q
    · have hmu : (ArithmeticFunction.moebius q : ℂ) ^ 2 = 1 := by
        have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq
        exact_mod_cast this
      simp only [f, if_pos hq, hmu, norm_mul, norm_div, norm_one, norm_pow,
        Complex.norm_natCast]
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right (leaf_ramanujan_sqfree_norm512 q N hq) (by positivity)
    · have hmu : (ArithmeticFunction.moebius q : ℂ) = 0 := by
        have := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq
        exact_mod_cast this
      simp [f, hq]
  -- step 2: sort by g = gcd q N
  have hN0 : N ≠ 0 := by omega
  have hmaps : ∀ q ∈ S, Nat.gcd q N ∈ N.divisors := by
    intro q _
    exact Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right q N, hN0⟩
  have step2 : ∑ q ∈ S, f q =
      ∑ g ∈ N.divisors, ∑ q ∈ S.filter (fun q => Nat.gcd q N = g), f q :=
    (Finset.sum_fiberwise_of_maps_to hmaps f).symm
  -- step 3: each fiber
  have step3 : ∀ g ∈ N.divisors, ∑ q ∈ S.filter (fun q => Nat.gcd q N = g), f q ≤
      K * ((ArithmeticFunction.moebius g : ℝ) ^ 2 / (Nat.totient g : ℝ) *
        min ((g : ℝ) / X) 1) := by
    intro g hg
    have hgpos : 0 < g := Nat.pos_of_mem_divisors hg
    by_cases hsg : Squarefree g
    · have hmu : (ArithmeticFunction.moebius g : ℝ) ^ 2 = 1 := by
        have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsg
        exact_mod_cast this
      rw [hmu]
      have hphig : (0 : ℝ) < Nat.totient g := by exact_mod_cast Nat.totient_pos.2 hgpos
      let h : ℕ → ℝ := fun r => 1 / (Nat.totient r : ℝ) ^ 2
      have hle : ∀ q ∈ S.filter (fun q => Nat.gcd q N = g),
          f q ≤ 1 / (Nat.totient g : ℝ) * h (q / g) := by
        intro q hq
        rw [Finset.mem_filter] at hq
        by_cases hsq : Squarefree q
        · have hgq : g ∣ q := hq.2 ▸ Nat.gcd_dvd_left q N
          have hqe : q = g * (q / g) := (Nat.mul_div_cancel' hgq).symm
          have hcop : Nat.Coprime g (q / g) :=
            Nat.coprime_of_squarefree_mul (hqe ▸ hsq)
          have htot : (Nat.totient q : ℝ) =
              (Nat.totient g : ℝ) * (Nat.totient (q / g) : ℝ) := by
            conv_lhs => rw [hqe]
            rw [Nat.totient_mul hcop]; push_cast; ring
          simp only [f, h, if_pos hsq, hq.2, htot]
          have hr : (0 : ℝ) < Nat.totient (q / g) := by
            have hq0 : 0 < q := by
              rcases Nat.eq_zero_or_pos q with h0 | h0
              · exact absurd (h0 ▸ hsq) not_squarefree_zero
              · exact h0
            have : 0 < q / g := Nat.div_pos (Nat.le_of_dvd hq0 hgq) hgpos
            exact_mod_cast Nat.totient_pos.2 this
          field_simp
          ring_nf
          exact le_refl _
        · simp only [f, if_neg hsq]
          simp only [h]; positivity
      refine (Finset.sum_le_sum hle).trans ?_
      rw [← Finset.mul_sum]
      have hinj : Set.InjOn (fun q => q / g) ↑(S.filter (fun q => Nat.gcd q N = g)) := by
        intro a ha b hb hab
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
        have ha' : g ∣ a := ha.2 ▸ Nat.gcd_dvd_left a N
        have hb' : g ∣ b := hb.2 ▸ Nat.gcd_dvd_left b N
        simp only at hab
        rw [← Nat.mul_div_cancel' ha', ← Nat.mul_div_cancel' hb', hab]
      rw [← Finset.sum_image (f := h) hinj]
      have hsub : (S.filter (fun q => Nat.gcd q N = g)).image (fun q => q / g) ⊆
          (Finset.Icc 1 M).filter (fun r : ℕ => X / g < (r : ℝ)) := by
        intro r hr
        rw [Finset.mem_image] at hr
        obtain ⟨q, hq, rfl⟩ := hr
        rw [Finset.mem_filter, hS, Finset.mem_Ioc] at hq
        have hgq : g ∣ q := hq.2 ▸ Nat.gcd_dvd_left q N
        have hXq : X < (q : ℝ) := Nat.lt_of_floor_lt hq.1.1
        have hq0 : 0 < q := by
          have : (0 : ℝ) < q := lt_trans hX hXq
          exact_mod_cast this
        rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨Nat.div_pos (Nat.le_of_dvd hq0 hgq) hgpos,
          le_trans (Nat.div_le_self q g) hq.1.2⟩, ?_⟩
        have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
        rw [div_lt_iff₀ hgR]
        have : ((q / g : ℕ) : ℝ) * g = q := by
          rw [← Nat.cast_mul, Nat.div_mul_cancel hgq]
        rw [this]; exact hXq
      have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
      have htail := hK (X / g) (div_pos hX hgR) M
      have hmono := Finset.sum_le_sum_of_subset_of_nonneg (f := h) hsub
        (fun r _ _ => by simp only [h]; positivity)
      rw [one_div_div] at htail
      calc 1 / (Nat.totient g : ℝ) * ∑ r ∈ (S.filter (fun q => Nat.gcd q N = g)).image
              (fun q => q / g), h r
          ≤ 1 / (Nat.totient g : ℝ) * (K * min ((g : ℝ) / X) 1) := by
            apply mul_le_mul_of_nonneg_left (hmono.trans htail)
            positivity
        _ = K * (1 / (Nat.totient g : ℝ) * min ((g : ℝ) / X) 1) := by ring
    · have hzero : ∀ q ∈ S.filter (fun q => Nat.gcd q N = g), f q = 0 := by
        intro q hq
        rw [Finset.mem_filter] at hq
        have hgq : g ∣ q := hq.2 ▸ Nat.gcd_dvd_left q N
        have hsq : ¬ Squarefree q := fun hs => hsg (Squarefree.squarefree_of_dvd hgq hs)
        simp only [f, if_neg hsq]
      rw [Finset.sum_eq_zero hzero]
      apply mul_nonneg hK0
      positivity
  calc _ ≤ ∑ q ∈ S, f q := step1
    _ = _ := step2
    _ ≤ ∑ g ∈ N.divisors, K * ((ArithmeticFunction.moebius g : ℝ) ^ 2 /
          (Nat.totient g : ℝ) * min ((g : ℝ) / X) 1) := Finset.sum_le_sum step3
    _ = _ := by rw [Finset.mul_sum]


/-- LEAF, CITED. Vaughan 1981, book page 34, displays 3.24 and 3.26, read from the page
image: the series 𝔖₁(m) = Σ_q μ(q)²/φ(q)² Σ_{(a,q)=1} e(-am/q) converges, and
𝔖₁(m) = Π_{p∤m} (1 - (p-1)^{-2}) Π_{p|m} (1 + (p-1)^{-1}).
For even m the factor at 2 is 2, and for an odd prime p dividing m the two Euler factors
differ by the ratio (p-1)/(p-2), so 𝔖₁(m) = 2 C₂ Π_{p|m, p>2} (p-1)/(p-2) = `sing (m/2)`,
the P0069 page 6 singular series 𝔖(2n) at 2n = m. The q = 0 term is 0 since μ 0 = 0.
Split from `leaf_vaughan_tail_reduction512`, REREAD U-1740, 2026-11-21. OPEN. -/
theorem leaf_vaughan_326_512 (N : ℕ) (hN : 2 ≤ N) (hE : Even N) :
    HasSum (fun q : ℕ => (ArithmeticFunction.moebius q : ℂ) ^ 2 /
      (Nat.totient q : ℂ) ^ 2 * ramanujan512 q N) (sing (N / 2) : ℂ) := by
  have hcoe : ∀ q : ℕ, (ArithmeticFunction.moebius q : ℂ) ^ 2 /
      (Nat.totient q : ℂ) ^ 2 * ramanujan512 q N =
        ((((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
          (∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) *
            ((ArithmeticFunction.moebius d : ℤ) : ℝ)) : ℝ) : ℂ) := by
    intro q
    rcases Nat.eq_zero_or_pos q with hq0 | hq
    · subst hq0
      simp [ArithmeticFunction.moebius, ramanujan512]
    · rw [c512_real_form q N hq]
      push_cast
      ring
  have hfun : (fun q : ℕ => (ArithmeticFunction.moebius q : ℂ) ^ 2 /
      (Nat.totient q : ℂ) ^ 2 * ramanujan512 q N) =
      (fun q : ℕ => ((((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        (Nat.totient q : ℝ) ^ 2 *
          (∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) *
            ((ArithmeticFunction.moebius d : ℤ) : ℝ)) : ℝ) : ℂ)) :=
    funext hcoe
  rw [hfun]
  exact (hasSum_real512 N hN hE).map Complex.ofRealCLM Complex.ofRealCLM.continuous

/-- P0069 page 8 display 2.7, using Vaughan reference 31 display 3.23.
QUESTION ANSWERED, REREAD U-1740 2026-11-21 from the page images: the printed center
of 2.7 writes uvY/ℒ² 𝔖(2n), while display 2.6 and the line before 2.7 carry
uv/(ℒℒ'), ℒ = log x, ℒ' = log Y. The ℒ² is a print slip: with ℒ² literally, the
difference would keep uvY(1/(ℒℒ') - 1/ℒ²)𝔖(2n), which is not small since ℒ' is a fixed
fraction of ℒ. The middle line of 2.7, Y² |Σ_{q>ℒ^{2A}} μ²/φ² c_q(-2n)|², drops the
whole factor uv/(ℒℒ') as bounded, so this leaf's log x times log Y is the reading the
printed chain proves. The H Y² ℒ^{-A-7} term is kept and unused.
CONDITIONAL ON the two cited LEAFs `leaf_vaughan_323_512` and `leaf_vaughan_326_512`;
the reduction itself is proved here. -/
theorem leaf_vaughan_tail_reduction512 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u v : ℝ,
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          seriesError512 ε D x u v ≤ C * (scale512 ε A x + length512 ε x ^ 2 *
            divisorTailMoment512 ε D x) := by
  obtain ⟨K, hK0, hK⟩ := leaf_vaughan_323_512
  refine ⟨1, one_pos, fun ε hε _ u v A _ => ⟨0, fun D _ => ?_⟩⟩
  refine ⟨max ((|u * v| * K) ^ 2) (Real.exp 2), fun x hx => ?_⟩
  have hxe : Real.exp 2 ≤ x := (le_max_right _ _).trans hx
  have he3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hLx : 2 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 2) hxe
    rwa [Real.log_exp] at h
  have hY0 : 0 < length512 ε x := by unfold length512; positivity
  have hLY : 1 ≤ Real.log (length512 ε x) := by
    unfold length512
    rw [Real.log_rpow hx0]
    nlinarith
  have hP0 : 0 < Real.log x ^ (2 * D) := Real.rpow_pos_of_pos (by linarith) _
  have key : ∀ N ∈ frequencies512 ε x,
      ‖truncatedMain512 ε D x u v N - expected512 ε x u v N‖ ^ 2 ≤
        (|u * v| * K) ^ 2 * length512 ε x ^ 2 *
          (∑ d ∈ N.divisors, 1 / (Nat.totient d : ℝ) *
            min ((d : ℝ) / Real.log x ^ (2 * D)) 1) ^ 2 := by
    intro N hN
    simp only [frequencies512, Finset.mem_filter, Finset.mem_Icc] at hN
    obtain ⟨⟨hNlo, -⟩, hEv⟩ := hN
    have hN2 : 2 ≤ N := by
      have h3 : 2 < ⌈x⌉₊ := Nat.lt_ceil.mpr (by norm_num; linarith)
      omega
    let f : ℕ → ℂ := fun q => (ArithmeticFunction.moebius q : ℂ) ^ 2 /
      (Nat.totient q : ℂ) ^ 2 * ramanujan512 q N
    have hf0 : f 0 = 0 := by simp [f]
    have hr : ∀ m : ℕ, ∑ q ∈ Finset.range (m + 1), f q = ∑ q ∈ Finset.Icc 1 m, f q := by
      intro m
      induction m with
      | zero => simp [hf0]
      | succ k ih => rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
    have hsplit : ∀ m : ℕ, ⌊Real.log x ^ (2 * D)⌋₊ ≤ m →
        ∑ q ∈ Finset.range (m + 1), f q =
          ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊, f q +
            ∑ q ∈ Finset.Ioc ⌊Real.log x ^ (2 * D)⌋₊ m, f q := by
      intro m hm
      rw [hr m]
      induction m, hm using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_Ioc_succ_top hk, add_assoc]
    have htail : ‖(sing (N / 2) : ℂ) - ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊, f q‖ ≤
        K * ∑ d ∈ N.divisors, (ArithmeticFunction.moebius d : ℝ) ^ 2 /
          (Nat.totient d : ℝ) * min ((d : ℝ) / Real.log x ^ (2 * D)) 1 := by
      have ht := ((leaf_vaughan_326_512 N hN2 hEv).tendsto_sum_nat.comp
        (Filter.tendsto_add_atTop_nat 1)).sub_const
          (∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊, f q)
      refine le_of_tendsto ht.norm ?_
      rw [Filter.eventually_atTop]
      refine ⟨⌊Real.log x ^ (2 * D)⌋₊, fun m hm => ?_⟩
      simp only [Function.comp]
      rw [hsplit m hm, add_sub_cancel_left]
      exact hK N (by omega) _ hP0 m
    have hw : (∑ d ∈ N.divisors, (ArithmeticFunction.moebius d : ℝ) ^ 2 /
          (Nat.totient d : ℝ) * min ((d : ℝ) / Real.log x ^ (2 * D)) 1) ≤
        ∑ d ∈ N.divisors, 1 / (Nat.totient d : ℝ) *
          min ((d : ℝ) / Real.log x ^ (2 * D)) 1 := by
      apply Finset.sum_le_sum
      intro d _
      have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hmu2 : ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 ≤ 1 :=
        (sq_le_one_iff_abs_le_one _).mpr hmu
      have hmin : 0 ≤ min ((d : ℝ) / Real.log x ^ (2 * D)) 1 :=
        le_min (div_nonneg (Nat.cast_nonneg _) hP0.le) zero_le_one
      have hphi : 0 ≤ (Nat.totient d : ℝ) := Nat.cast_nonneg _
      gcongr
    have hdiff : truncatedMain512 ε D x u v N - expected512 ε x u v N =
        ((u * v * length512 ε x / (Real.log x * Real.log (length512 ε x)) : ℝ) : ℂ) *
          (∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊, f q - (sing (N / 2) : ℂ)) := by
      unfold truncatedMain512 expected512
      push_cast
      ring
    have hc : |u * v * length512 ε x / (Real.log x * Real.log (length512 ε x))| ≤
        |u * v| * length512 ε x := by
      have hden : 1 ≤ Real.log x * Real.log (length512 ε x) := by nlinarith
      have hdpos : 0 < Real.log x * Real.log (length512 ε x) := by linarith
      rw [abs_div, abs_mul, abs_of_pos hY0, abs_of_pos hdpos]
      exact div_le_self (by positivity) hden
    have hnorm : ‖truncatedMain512 ε D x u v N - expected512 ε x u v N‖ ≤
        |u * v| * K * length512 ε x * (∑ d ∈ N.divisors, 1 / (Nat.totient d : ℝ) *
          min ((d : ℝ) / Real.log x ^ (2 * D)) 1) := by
      rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev]
      calc _ ≤ (|u * v| * length512 ε x) *
            (K * ∑ d ∈ N.divisors, (ArithmeticFunction.moebius d : ℝ) ^ 2 /
              (Nat.totient d : ℝ) * min ((d : ℝ) / Real.log x ^ (2 * D)) 1) :=
            mul_le_mul hc htail (norm_nonneg _) (by positivity)
        _ ≤ (|u * v| * length512 ε x) * (K * ∑ d ∈ N.divisors, 1 / (Nat.totient d : ℝ) *
              min ((d : ℝ) / Real.log x ^ (2 * D)) 1) := by gcongr
        _ = _ := by ring
    calc _ ≤ (|u * v| * K * length512 ε x * (∑ d ∈ N.divisors, 1 / (Nat.totient d : ℝ) *
          min ((d : ℝ) / Real.log x ^ (2 * D)) 1)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = _ := by ring
  have hmom : 0 ≤ divisorTailMoment512 ε D x :=
    Finset.sum_nonneg (fun N _ => sq_nonneg _)
  have hscale := scale_nonneg512 ε A hx1
  have hCK : (|u * v| * K) ^ 2 ≤ max ((|u * v| * K) ^ 2) (Real.exp 2) := le_max_left _ _
  calc seriesError512 ε D x u v
      ≤ ∑ N ∈ frequencies512 ε x, (|u * v| * K) ^ 2 * length512 ε x ^ 2 *
          (∑ d ∈ N.divisors, 1 / (Nat.totient d : ℝ) *
            min ((d : ℝ) / Real.log x ^ (2 * D)) 1) ^ 2 := Finset.sum_le_sum key
    _ = (|u * v| * K) ^ 2 * (length512 ε x ^ 2 * divisorTailMoment512 ε D x) := by
      unfold divisorTailMoment512
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N _
      ring
    _ ≤ max ((|u * v| * K) ^ 2) (Real.exp 2) *
          (length512 ε x ^ 2 * divisorTailMoment512 ε D x) :=
      mul_le_mul_of_nonneg_right hCK (by positivity)
    _ ≤ max ((|u * v| * K) ^ 2) (Real.exp 2) *
          (scale512 ε A x + length512 ε x ^ 2 * divisorTailMoment512 ε D x) :=
      mul_le_mul_of_nonneg_left (by linarith) ((sq_nonneg _).trans hCK)

/-- LEAF. P0069 page 8 display 2.8: the small-divisor mean square estimate on K.
The uniform short interval divisor moment bound used by the paper is not supplied
by a full summatory divisor estimate.
PROVED 2026-11-15 from Route512Small.small_divisor_moment_raw512, no sorry. -/
theorem leaf_small_divisor_moment512 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x → smallDivisorMoment512 ε D x ≤
          C * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * Real.log x ^ (-A - 7) := by
  refine ⟨1, one_pos, fun ε hε hε1 A hA => ?_⟩
  have hc : (2 : ℝ) * (1 / 16 - 1 / 10 ^ 5) ≤ 1 / 8 := by norm_num
  have hc0 : (0 : ℝ) < 2 * (1 / 16 - 1 / 10 ^ 5) := by norm_num
  have h0 : (0 : ℝ) < (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) :=
    mul_pos (by linarith) hc0
  have h1 : (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) ≤ 1 := by
    calc (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))
        ≤ (31 / 20) * (1 / 8) := mul_le_mul (by linarith) hc hc0.le (by norm_num)
      _ ≤ 1 := by norm_num
  obtain ⟨D₀, hD₀⟩ :=
    LeanLab.BHP1997.Route512.small_divisor_moment_raw512 _ h0 h1 A hA
  refine ⟨D₀, fun D hD => ?_⟩
  obtain ⟨C, hC⟩ := hD₀ D hD
  refine ⟨C, fun x hx => ?_⟩
  have hraw := hC x hx
  unfold smallDivisorMoment512 smallDivisorTail512 frequencies512
  exact hraw

/-- LEAF. P0069 page 8 display 2.9: the large-divisor mean square estimate on K.
It is separate from the small-divisor bound and retains the printed tail range.
PROVED 2026-11-15 from Route512Large.large_divisor_moment_raw512, no sorry. -/
theorem leaf_large_divisor_moment512 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x → largeDivisorMoment512 ε D x ≤
          C * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * Real.log x ^ (-A - 7) := by
  refine ⟨1, one_pos, fun ε hε hε1 A hA => ?_⟩
  have hc : (2 : ℝ) * (1 / 16 - 1 / 10 ^ 5) ≤ 1 / 8 := by norm_num
  have hc0 : (0 : ℝ) < 2 * (1 / 16 - 1 / 10 ^ 5) := by norm_num
  have h0 : (0 : ℝ) < (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) :=
    mul_pos (by linarith) hc0
  have h1 : (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) ≤ 1 := by
    calc (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))
        ≤ (31 / 20) * (1 / 8) := mul_le_mul (by linarith) hc hc0.le (by norm_num)
      _ ≤ 1 := by norm_num
  obtain ⟨D₀, hD₀⟩ :=
    LeanLab.BHP1997.Route512.large_divisor_moment_raw512 _ h0 h1 A hA
  refine ⟨D₀, fun D hD => ?_⟩
  obtain ⟨C, hC⟩ := hD₀ D hD
  refine ⟨C, fun x hx => ?_⟩
  have hraw := hC x hx
  unfold largeDivisorMoment512 largeDivisorTail512 frequencies512
  exact hraw

/-- P0069 page 8: assemble 2.7, 2.8 and 2.9 with common epsilon, parameter and
threshold. CONDITIONAL ON those three printed estimates. -/
theorem singular_series_tail_of_three512 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u v : ℝ,
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x → seriesError512 ε D x u v ≤ C * scale512 ε A x := by
  obtain ⟨ε₀, hε₀, h0⟩ := leaf_vaughan_tail_reduction512
  obtain ⟨ε₁, hε₁, h1⟩ := leaf_small_divisor_moment512
  obtain ⟨ε₂, hε₂, h2⟩ := leaf_large_divisor_moment512
  refine ⟨min ε₀ (min ε₁ ε₂), lt_min hε₀ (lt_min hε₁ hε₂), ?_⟩
  intro ε hε he u v A hA
  obtain ⟨D₀, hD₀⟩ := h0 ε hε (lt_of_lt_of_le he (min_le_left _ _)) u v A hA
  obtain ⟨D₁, hD₁⟩ := h1 ε hε
    (lt_of_lt_of_le he ((min_le_right _ _).trans (min_le_left _ _))) A hA
  obtain ⟨D₂, hD₂⟩ := h2 ε hε
    (lt_of_lt_of_le he ((min_le_right _ _).trans (min_le_right _ _))) A hA
  refine ⟨max D₀ (max D₁ D₂), fun D hD => ?_⟩
  obtain ⟨C₀, hC₀⟩ := hD₀ D ((le_max_left _ _).trans hD)
  obtain ⟨C₁, hC₁⟩ := hD₁ D ((le_max_left _ _).trans ((le_max_right _ _).trans hD))
  obtain ⟨C₂, hC₂⟩ := hD₂ D ((le_max_right _ _).trans ((le_max_right _ _).trans hD))
  let C := max (max C₀ (max C₁ C₂)) (max (|C₀| * (1 + 2 * C₁ + 2 * C₂)) 3)
  refine ⟨C, fun x hx => ?_⟩
  have hxl : max C₀ (max C₁ C₂) ≤ x := (le_max_left _ _).trans hx
  have hx₀ : C₀ ≤ x := (le_max_left _ _).trans hxl
  have hx₁ : C₁ ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hxl)
  have hx₂ : C₂ ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hxl)
  have hx3 : 3 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx3
  have hP : 0 < Real.log x ^ (2 * D) :=
    Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
  have htn : 0 ≤ divisorTailMoment512 ε D x :=
    Finset.sum_nonneg (fun N hN => sq_nonneg _)
  have hnonneg : 0 ≤ scale512 ε A x + length512 ε x ^ 2 * divisorTailMoment512 ε D x :=
    add_nonneg (scale_nonneg512 ε A hx1) (mul_nonneg (sq_nonneg _) htn)
  let R := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * Real.log x ^ (-A - 7)
  have hsum : smallDivisorMoment512 ε D x + largeDivisorMoment512 ε D x ≤ (C₁ + C₂) * R := by
    calc
      _ ≤ C₁ * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * Real.log x ^ (-A - 7) +
          C₂ * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * Real.log x ^ (-A - 7) :=
        add_le_add (hC₁ x hx₁) (hC₂ x hx₂)
      _ = _ := by dsimp [R]; ring
  have ht : divisorTailMoment512 ε D x ≤ 2 * (C₁ + C₂) * R := by
    calc
      _ ≤ 2 * smallDivisorMoment512 ε D x + 2 * largeDivisorMoment512 ε D x :=
        divisor_tail_moment_split512 ε D x hP
      _ = 2 * (smallDivisorMoment512 ε D x + largeDivisorMoment512 ε D x) := by ring
      _ ≤ 2 * ((C₁ + C₂) * R) := mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = _ := by ring
  calc
    seriesError512 ε D x u v ≤ C₀ * (scale512 ε A x + length512 ε x ^ 2 *
        divisorTailMoment512 ε D x) := hC₀ x hx₀
    _ ≤ |C₀| * (scale512 ε A x + length512 ε x ^ 2 * divisorTailMoment512 ε D x) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hnonneg
    _ ≤ |C₀| * (scale512 ε A x + length512 ε x ^ 2 * (2 * (C₁ + C₂) * R)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left ht (sq_nonneg _)))
        (abs_nonneg _)
    _ = (|C₀| * (1 + 2 * C₁ + 2 * C₂)) * scale512 ε A x := by dsimp [R]; unfold scale512; ring
    _ ≤ C * scale512 ε A x := mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) (scale_nonneg512 ε A hx1)

/-- LEAF. P0069 page 8, displays 2.7 to 2.9, using Vaughan reference 31 display 3.23.
The truncated singular series has the required averaged tail bound over K.
This statement has no coefficient family hypothesis. CONDITIONAL ON the three
printed estimates now separated below it in the dependency graph. -/
theorem leaf_singular_series_tail512 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u v : ℝ,
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x → seriesError512 ε D x u v ≤ C * scale512 ε A x := by
  exact singular_series_tail_of_three512

/-- LEAF. P0069 page 6 display 2.2, proved in the paper on pages 6 to 8 using
2.4 to 2.9. The requested loss is A. The internal arc parameter D is sufficiently large
in A and B. OPEN until the character approximation and singular series tail
estimates are formalized. -/
theorem leaf_major_arc_mean_square512 :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Theorem2With ε B (fun a b u v _ =>
        ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
          ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
            majorError512 ε D x (a x) (b x) u v ≤ C * scale512 ε A x) := by
  intro B
  obtain ⟨ε₁, hε₁, hrep⟩ := leaf_major_replacement512 B
  obtain ⟨ε₂, hε₂, htail⟩ := leaf_singular_series_tail512
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂,
    fun ε hε hε₀ a b u v E h1 h2 h3 h4 h5 A hA => ?_⟩
  have hr := hrep ε hε (lt_of_lt_of_le hε₀ (min_le_left _ _)) a b u v E h1 h2 h3 h4 h5 A hA
  have ht := htail ε hε (lt_of_lt_of_le hε₀ (min_le_right _ _)) u v A hA
  exact combine_eventual512 ε A
    (fun D x => replacementError512 ε D x (a x) (b x) u v)
    (fun D x => seriesError512 ε D x u v)
    (fun D x => majorError512 ε D x (a x) (b x) u v) hr ht
    (fun D x => major_error_split512 ε D x (a x) (b x) u v)

/-- P0069 page 9 display 2.11: the local energy of S2 on a minor arc neighborhood
of radius 1/H. -/
noncomputable def localMinorEnergy512 (ε D x : ℝ) (b : ℕ → ℂ) (ζ : ℝ) : ℝ :=
  ∫ t in Ioo (ζ - 1 / x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))))
      (ζ + 1 / x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) ∩ minor512 ε D x,
    ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ ^ 2

/-- LEAF. P0069 pages 8 and 9, display 2.10 and the reduction to 2.11.
Parseval, Cauchy and the periodic Dirichlet kernel convert arbitrarily strong
uniform local minor arc energy savings into the required mean square saving.
The input concerns the actual local integral of S2.
PROVED 2026-11-15 from Route512Kernel.gallagher_window512 and
Route512Moment.short_divisor_moment512, no sorry. -/
theorem leaf_minor_kernel_reduction512 :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Theorem2With ε B (fun a b _ _ _ =>
        (∀ L : ℝ, 0 < L → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
          ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ ζ : ℝ,
            localMinorEnergy512 ε D x (b x) ζ ≤
              C * length512 ε x * Real.log x ^ (-L)) →
        ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
          ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
            minorError512 ε D x (a x) (b x) ≤ C * scale512 ε A x) := by
  intro B
  refine ⟨1, one_pos, fun ε hε _ a b u v E h1 h2 h3 h4 h5 hloc A hA => ?_⟩
  -- the real variable bookkeeping behind display 2.10: Cauchy with the two energy bounds
  have key : ∀ H Y l1 l2 l3 Sa G c2 c3 c4 : ℝ, 0 ≤ H → 0 ≤ Y → 0 ≤ l1 → 0 ≤ l2 →
      l1 * l2 ≤ l3 → G ≤ 30 * H * Sa * (c4 * Y * l2) → Sa ≤ c2 * (c3 * Y * l1) →
      0 ≤ c2 → 0 ≤ c3 → 0 ≤ c4 → G ≤ (30 * (c2 * c3) * c4) * (H * Y ^ 2 * l3) := by
    intro H Y l1 l2 l3 Sa G c2 c3 c4 hH hY hl1 hl2 h12 hG hSa hc2 hc3 hc4
    have hE : 0 ≤ c4 * Y * l2 := mul_nonneg (mul_nonneg hc4 hY) hl2
    have hH30 : 0 ≤ 30 * H := mul_nonneg (by norm_num) hH
    have hK : 0 ≤ 30 * (c2 * c3) * c4 :=
      mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hc2 hc3)) hc4
    calc G ≤ 30 * H * Sa * (c4 * Y * l2) := hG
      _ ≤ 30 * H * (c2 * (c3 * Y * l1)) * (c4 * Y * l2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSa hH30) hE
      _ = (30 * (c2 * c3) * c4) * (H * Y ^ 2 * (l1 * l2)) := by ring
      _ ≤ (30 * (c2 * c3) * c4) * (H * Y ^ 2 * l3) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h12 (mul_nonneg hH (sq_nonneg Y))) hK
  -- hypothesis ii of Theorem 2, the page 9 divisor moment, and the local energy input 2.11
  obtain ⟨C2, hC2⟩ := h2
  obtain ⟨c, C3, hC3⟩ := Route512.short_divisor_moment512 B ε hε
  have hL : 0 < A + 7 + |c| := by positivity
  obtain ⟨D₀, hD₀⟩ := hloc (A + 7 + |c|) hL
  refine ⟨D₀, fun D hD => ?_⟩
  obtain ⟨C4, hC4⟩ := hD₀ D hD
  refine ⟨max (max C3 C4) (max (30 * (C2 ^ 2 * |C3|) * |C4|) 3), fun x hx => ?_⟩
  have hx3 : C3 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx4 : C4 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx3' : (3 : ℝ) ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx3'
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx3'
  have hlog1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    linarith
  have hlog0 : 0 < Real.log x := lt_of_lt_of_le one_pos hlog1
  have hθ : (0 : ℝ) ≤ (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) :=
    mul_nonneg (by linarith) (by norm_num)
  have hH1 : 1 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) :=
    Real.one_le_rpow hx1 hθ
  have hHn : 0 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) :=
    le_trans zero_le_one hH1
  have hYn : 0 ≤ length512 ε x := Real.rpow_nonneg hx0.le _
  have hΛ1 : 0 ≤ Real.log x ^ c := Real.rpow_nonneg hlog0.le _
  have hΛ2 : 0 ≤ Real.log x ^ (-(A + 7 + |c|)) := Real.rpow_nonneg hlog0.le _
  have hΛ : Real.log x ^ c * Real.log x ^ (-(A + 7 + |c|)) ≤ Real.log x ^ (-A - 7) := by
    rw [← Real.rpow_add hlog0]
    exact Real.rpow_le_rpow_of_exponent_le hlog1 (by have := le_abs_self c; linarith)
  -- the minor arcs lie in the complete period starting at 1/Q
  have hmc : minor512 ε D x ⊆
      Ioc (1 / (order512 ε x : ℝ)) (1 / (order512 ε x : ℝ) + 1) := by
    intro t ht
    have ht' : t ∈ Ioc (1 / (order512 ε x : ℝ)) (1 + 1 / (order512 ε x : ℝ)) :=
      (show minor512 ε D x ⊆ period512 ε x from sdiff_subset) ht
    exact ⟨ht'.1, by have := ht'.2; linarith⟩
  -- the frequencies of K lie in an interval of length H starting at the ceiling of x
  have hK : ∀ N ∈ frequencies512 ε x, ⌈x⌉₊ ≤ N ∧
      (N : ℝ) ≤ (⌈x⌉₊ : ℝ) + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := by
    intro N hN
    unfold frequencies512 at hN
    rw [Finset.mem_filter, Finset.mem_Icc] at hN
    refine ⟨hN.1.1, ?_⟩
    have h1 : (N : ℝ) ≤
        (⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊ : ℝ) := by
      exact_mod_cast hN.1.2
    have h2 : (⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊ : ℝ) ≤
        x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) :=
      Nat.floor_le (add_nonneg hx0.le hHn)
    have h3 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    linarith
  -- display 2.11 as the uniform local energy input of the window inequality
  have hE : ∀ ζ : ℝ,
      ∫ t in Ioo (ζ - 1 / x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))))
          (ζ + 1 / x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) ∩ minor512 ε D x,
        ‖∑ k ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
          b x k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))‖ ^ 2 ≤
        |C4| * length512 ε x * Real.log x ^ (-(A + 7 + |c|)) := by
    intro ζ
    have h1 : C4 * length512 ε x * Real.log x ^ (-(A + 7 + |c|)) ≤
        |C4| * length512 ε x * Real.log x ^ (-(A + 7 + |c|)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C4) hYn) hΛ2
    exact (hC4 x hx4 ζ).trans h1
  -- page 9 first display: the energy of S1 by hypothesis ii and the divisor moment
  have hSa : ∑ k ∈ Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊, ‖a x k‖ ^ 2 ≤
      C2 ^ 2 * (|C3| * length512 ε x * Real.log x ^ c) := by
    have hleaf : ∑ k ∈ Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊,
        ((k.divisors.card : ℕ) : ℝ) ^ (2 * B) ≤
          C3 * length512 ε x * Real.log x ^ c := hC3 x hx3
    have hpt : ∀ k ∈ Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊,
        ‖a x k‖ ^ 2 ≤ C2 ^ 2 * ((k.divisors.card : ℕ) : ℝ) ^ (2 * B) := by
      intro k _
      have hτ : (0 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
      have hτB : (0 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) ^ B := Real.rpow_nonneg hτ B
      have h' : ‖a x k‖ ≤ |C2| * ((k.divisors.card : ℕ) : ℝ) ^ B :=
        (hC2 x k).1.trans (mul_le_mul_of_nonneg_right (le_abs_self C2) hτB)
      have hsq : ‖a x k‖ ^ 2 ≤ (|C2| * ((k.divisors.card : ℕ) : ℝ) ^ B) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h' 2
      have he : (((k.divisors.card : ℕ) : ℝ) ^ B) ^ 2 =
          ((k.divisors.card : ℕ) : ℝ) ^ (2 * B) := by
        rw [mul_comm 2 B, Real.rpow_mul hτ, Real.rpow_two]
      calc ‖a x k‖ ^ 2 ≤ (|C2| * ((k.divisors.card : ℕ) : ℝ) ^ B) ^ 2 := hsq
        _ = C2 ^ 2 * ((k.divisors.card : ℕ) : ℝ) ^ (2 * B) := by
          rw [mul_pow, sq_abs, he]
    calc ∑ k ∈ Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊, ‖a x k‖ ^ 2
        ≤ ∑ k ∈ Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊,
            C2 ^ 2 * ((k.divisors.card : ℕ) : ℝ) ^ (2 * B) := Finset.sum_le_sum hpt
      _ = C2 ^ 2 * ∑ k ∈ Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊,
            ((k.divisors.card : ℕ) : ℝ) ^ (2 * B) := by rw [Finset.mul_sum]
      _ ≤ C2 ^ 2 * (C3 * length512 ε x * Real.log x ^ c) :=
        mul_le_mul_of_nonneg_left hleaf (sq_nonneg _)
      _ ≤ C2 ^ 2 * (|C3| * length512 ε x * Real.log x ^ c) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self C3) hYn) hΛ1) (sq_nonneg _)
  -- display 2.10: Parseval, Cauchy and the periodic kernel, as the window inequality
  have hG : minorError512 ε D x (a x) (b x) ≤
      30 * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
        (∑ k ∈ Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊, ‖a x k‖ ^ 2) *
          (|C4| * length512 ε x * Real.log x ^ (-(A + 7 + |c|))) :=
    Route512.gallagher_window512 (1 / (order512 ε x : ℝ)) (minor512 ε D x)
      (measurable_minor512 ε D x) hmc
      (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊)
      (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)
      (a x) (b x) (frequencies512 ε x) ⌈x⌉₊
      (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))))
      (|C4| * length512 ε x * Real.log x ^ (-(A + 7 + |c|))) hH1 hK hE
  have hfin := key (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))))
    (length512 ε x) (Real.log x ^ c) (Real.log x ^ (-(A + 7 + |c|)))
    (Real.log x ^ (-A - 7))
    (∑ k ∈ Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊, ‖a x k‖ ^ 2)
    (minorError512 ε D x (a x) (b x)) (C2 ^ 2) |C3| |C4|
    hHn hYn hΛ1 hΛ2 hΛ hG hSa (sq_nonneg _) (abs_nonneg _) (abs_nonneg _)
  calc minorError512 ε D x (a x) (b x)
      ≤ (30 * (C2 ^ 2 * |C3|) * |C4|) *
          (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * length512 ε x ^ 2 *
            Real.log x ^ (-A - 7)) := hfin
    _ = (30 * (C2 ^ 2 * |C3|) * |C4|) * scale512 ε A x := rfl
    _ ≤ max (max C3 C4) (max (30 * (C2 ^ 2 * |C3|) * |C4|) 3) * scale512 ε A x :=
      mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _))
        (scale_nonneg512 ε A hx1)

/-- LEAF. P0069 pages 9 and 10, display 2.11, reduced there to 2.12, 2.13 and 2.15.
The exceptional characters use Parseval. The remaining characters use Gallagher
2.16 and the Saffari Vaughan window comparison before hypothesis iv.
This is a uniform local energy estimate for the actual S2. OPEN. -/
theorem leaf_minor_local_energy512 :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Theorem2With ε B (fun _ b _ _ _ =>
        ∀ L : ℝ, 0 < L → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
          ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ ζ : ℝ,
            localMinorEnergy512 ε D x (b x) ζ ≤
              C * length512 ε x * Real.log x ^ (-L)) := by
  sorry

/-- LEAF. P0069 page 6 display 2.3, proved in the paper on pages 8 to 10 using
2.10 to 2.16. This is the actual minor arc integral, not a substitute bound.
OPEN until the localized minor arc estimate and Gallagher transfer are formalized. -/
theorem leaf_minor_arc_mean_square512 :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Theorem2With ε B (fun a b _ _ _ =>
        ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
          ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
            minorError512 ε D x (a x) (b x) ≤ C * scale512 ε A x) := by
  intro B
  obtain ⟨ε₁, hε₁, hkernel⟩ := leaf_minor_kernel_reduction512 B
  obtain ⟨ε₂, hε₂, hlocal⟩ := leaf_minor_local_energy512 B
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun ε hε hε₀ a b u v E h1 h2 h3 h4 h5 => ?_⟩
  exact (hkernel ε hε (lt_of_lt_of_le hε₀ (min_le_left _ _)) a b u v E h1 h2 h3 h4 h5)
    (hlocal ε hε (lt_of_lt_of_le hε₀ (min_le_right _ _)) a b u v E h1 h2 h3 h4 h5)

/-- P0069 page 6: the complete mean square follows by the exact Fourier partition
and the two separately stated estimates. CONDITIONAL ON 2.2 and 2.3. -/
theorem meanSquare_of_arcs512 (ε : ℝ) (a b : ℝ → ℕ → ℂ) (u v : ℝ)
    (hmajor : ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
      ∃ C : ℝ, ∀ x : ℝ, C ≤ x → majorError512 ε D x (a x) (b x) u v ≤ C * scale512 ε A x)
    (hminor : ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
      ∃ C : ℝ, ∀ x : ℝ, C ≤ x → minorError512 ε D x (a x) (b x) ≤ C * scale512 ε A x) :
    MeanSquare ε a b u v := by
  dsimp only [MeanSquare]
  intro A hA
  obtain ⟨D₁, hD₁⟩ := hmajor A hA
  obtain ⟨D₂, hD₂⟩ := hminor A hA
  let D := max D₁ D₂
  obtain ⟨C₁, hC₁⟩ := hD₁ D (le_max_left _ _)
  obtain ⟨C₂, hC₂⟩ := hD₂ D (le_max_right _ _)
  let C := max (max C₁ C₂) (max (2 * C₁ + 2 * C₂) 1)
  refine ⟨C, fun x hx => ?_⟩
  have hx₁ : C₁ ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx₂ : C₂ ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have h := combine_square512 (frequencies512 ε x)
    (fun N => ∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t)
    (fun N => ∫ t in minor512 ε D x, integrand512 ε x (a x) (b x) N t)
    (expected512 ε x u v) (C₁ * scale512 ε A x) (C₂ * scale512 ε A x)
    (hC₁ x hx₁) (hC₂ x hx₂)
  have hb : 2 * (C₁ * scale512 ε A x) + 2 * (C₂ * scale512 ε A x) ≤ C * scale512 ε A x := by
    calc
      _ = (2 * C₁ + 2 * C₂) * scale512 ε A x := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _))
        (scale_nonneg512 ε A ((le_max_right _ _).trans ((le_max_right _ _).trans hx)))
  have hh := h.trans hb
  simp_rw [← convolution_arcs512] at hh
  simpa only [frequencies512, expected512, scale512, length512, mul_assoc] using hh

/-- P0069 page 6: choose the smaller epsilon window and apply both analytic leaves.
CONDITIONAL ON the two open arc estimates. -/
theorem section2_from_arc_leaves512 :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Theorem2With ε B (fun a b u v _ => MeanSquare ε a b u v) := by
  intro B
  obtain ⟨ε₁, hε₁, hmajor⟩ := leaf_major_arc_mean_square512 B
  obtain ⟨ε₂, hε₂, hminor⟩ := leaf_minor_arc_mean_square512 B
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun ε hε hε₀ a b u v E h1 h2 h3 h4 h5 => ?_⟩
  exact meanSquare_of_arcs512 ε a b u v
    (hmajor ε hε (lt_of_lt_of_le hε₀ (min_le_left _ _)) a b u v E h1 h2 h3 h4 h5)
    (hminor ε hε (lt_of_lt_of_le hε₀ (min_le_right _ _)) a b u v E h1 h2 h3 h4 h5)

/-- P0069 page 9, Parseval before 2.11: expand the squared polynomial. -/
theorem polynomial_norm_square512 (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    (‖polynomial512 S a t‖ ^ 2 : ℂ) =
      ∑ k ∈ S, ∑ m ∈ S, (conj (a k) * a m) *
        @fourier 1 (-(k : ℤ) + (m : ℤ)) (t : AddCircle (1 : ℝ)) := by
  push_cast
  rw [← Complex.conj_mul']
  simp only [polynomial512, map_sum, map_mul, ← fourier_neg, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro m hm
  rw [fourier_add]
  ring

/-- P0069 page 9, Parseval before 2.11: the exact finite polynomial energy identity
on every complete period. -/
theorem parseval512 (S : Finset ℕ) (a : ℕ → ℂ) (c : ℝ) :
    (∫ t in c..c + 1, ‖polynomial512 S a t‖ ^ 2) = ∑ k ∈ S, ‖a k‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [Complex.ofReal_pow, polynomial_norm_square512]
  have hc (k m : ℕ) : Continuous (fun t : ℝ => (conj (a k) * a m) *
      @fourier 1 (-(k : ℤ) + (m : ℤ)) (t : AddCircle (1 : ℝ))) :=
    continuous_const.mul ((map_continuous (fourier _)).comp (AddCircle.continuous_mk' 1))
  rw [intervalIntegral.integral_finsetSum (fun k hk =>
    (continuous_finsetSum S fun m hm => hc k m).intervalIntegrable _ _)]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [intervalIntegral.integral_finsetSum (fun m hm => (hc k m).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul, integral_fourier512]
  have he (m : ℕ) : -(k : ℤ) + (m : ℤ) = 0 ↔ m = k := by omega
  simp [he, hk, Complex.conj_mul']

/-- P0069 page 10, the Cauchy step leading to 2.15: split the character sum
into the exceptional set and its complement before applying finite Cauchy. -/
theorem exceptional_cauchy512 {ι : Type*} [Fintype ι] (E : Finset ι) (W : ι → ℂ) :
    (∑ χ : ι, ‖W χ‖) ^ 2 ≤
      2 * (E.card : ℝ) * (∑ χ ∈ E, ‖W χ‖ ^ 2) +
        2 * ((Finset.univ \ E).card : ℝ) * (∑ χ ∈ Finset.univ \ E, ‖W χ‖ ^ 2) := by
  have h₁ := sq_sum_le_card_mul_sum_sq (s := E) (f := fun χ => ‖W χ‖)
  have h₂ := sq_sum_le_card_mul_sum_sq (s := Finset.univ \ E) (f := fun χ => ‖W χ‖)
  have hp : (∑ χ : ι, ‖W χ‖) = (∑ χ ∈ E, ‖W χ‖) +
      (∑ χ ∈ Finset.univ \ E, ‖W χ‖) := by
    simpa only [Finset.compl_eq_univ_sdiff] using
      (Finset.sum_add_sum_compl E (fun χ => ‖W χ‖)).symm
  rw [hp]
  nlinarith [sq_nonneg ((∑ χ ∈ E, ‖W χ‖) - (∑ χ ∈ Finset.univ \ E, ‖W χ‖))]

/-- P0069 page 10, the exceptional part of 2.15: an integral on a shorter interval
is bounded by the full Parseval energy. -/
theorem parseval_subinterval512 (S : Finset ℕ) (a : ℕ → ℂ) {c l r : ℝ}
    (hcl : c ≤ l) (hlr : l ≤ r) (hrc : r ≤ c + 1) :
    (∫ t in l..r, ‖polynomial512 S a t‖ ^ 2) ≤ ∑ k ∈ S, ‖a k‖ ^ 2 := by
  rw [← parseval512 S a c]
  exact intervalIntegral.integral_mono_interval hcl hlr hrc
    (Filter.Eventually.of_forall (fun t => sq_nonneg _))
    (((continuous_polynomial512 S a).norm.pow 2).intervalIntegrable c (c + 1))

/-- P0069 page 3: all five analytic hypotheses hold jointly for the zero coefficient
families with zero densities and empty exceptional sets. This supplies an explicit
nonvacuity test for each arc leaf. -/
theorem zero_inputs512 (ε B : ℝ)
    (P : (ℝ → ℕ → ℂ) → (ℝ → ℕ → ℂ) → ℝ → ℝ →
      (ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q)) → Prop)
    (h : Theorem2With ε B P) :
    P (fun _ _ => 0) (fun _ _ => 0) 0 0 (fun _ _ _ => ∅) := by
  apply h (fun _ _ => 0) (fun _ _ => 0) 0 0 (fun _ _ _ => ∅)
  · intro A hA
    exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩
  · intro A hA
    exact ⟨0, by simp⟩
  · intro A hA
    exact ⟨0, by simp⟩
  · intro A hA
    exact ⟨0, by simp⟩

/-- P0069 page 6 display 2.2: the zero instance has no major arc error. -/
theorem zero_major_error512 (ε D x : ℝ) :
    majorError512 ε D x (fun _ => 0) (fun _ => 0) 0 0 = 0 := by
  simp [majorError512, expected512, integrand512, polynomial512]

/-- P0069 page 6 display 2.3: the zero instance has no minor arc error. -/
theorem zero_minor_error512 (ε D x : ℝ) :
    minorError512 ε D x (fun _ => 0) (fun _ => 0) = 0 := by
  simp [minorError512, integrand512, polynomial512]

/-- P0069 page 10, exceptional character part of 2.15: Parseval and the bound
on character values control the centered polynomial by the coefficient energy
and its constant center. No distribution or mean value estimate is assumed. -/
theorem centered_character_parseval512 (S : Finset ℕ) (b : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (c : ℂ) (d : ℝ) :
    (∫ t in d..d + 1, ‖polynomial512 S (fun m => b m * χ (m : ZMod q) - c) t‖ ^ 2) ≤
      2 * (∑ m ∈ S, ‖b m‖ ^ 2) + 2 * (S.card : ℝ) * ‖c‖ ^ 2 := by
  rw [parseval512]
  calc
    _ ≤ ∑ m ∈ S, (2 * ‖b m‖ ^ 2 + 2 * ‖c‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro m hm
      have hn : ‖b m * χ (m : ZMod q)‖ ≤ ‖b m‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)
      calc
        ‖b m * χ (m : ZMod q) - c‖ ^ 2 ≤
            2 * ‖b m * χ (m : ZMod q)‖ ^ 2 + 2 * ‖c‖ ^ 2 := by
          simpa only [sub_eq_add_neg, norm_neg] using
            norm_add_square512 (b m * χ (m : ZMod q)) (-c)
        _ ≤ _ := by nlinarith [pow_le_pow_left₀ (norm_nonneg _) hn 2]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring

/-- P0069 page 6 display 2.1: discrete Parseval for the Gauss transforms. -/
theorem gauss_parseval512 {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    ∑ t : ZMod q, ‖∑ r : ZMod q, f r * ZMod.stdAddChar (r * t)‖ ^ 2 =
      (q : ℝ) * ∑ r : ZMod q, ‖f r‖ ^ 2 := by
  let e : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  have hexp (t : ZMod q) :
      (‖∑ r : ZMod q, f r * e (r * t)‖ ^ 2 : ℂ) =
        ∑ r : ZMod q, ∑ s : ZMod q, (conj (f r) * f s) * e ((s - r) * t) := by
    rw [← Complex.conj_mul']
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
      ← AddChar.map_neg_eq_conj]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    calc
      _ = (conj (f r) * f s) * (e (-(r * t)) * e (s * t)) := by ring
      _ = _ := by
        rw [← e.map_add_eq_mul]
        congr 2
        ring
  apply Complex.ofReal_injective
  push_cast
  change (∑ t : ZMod q, (‖∑ r : ZMod q, f r * e (r * t)‖ ^ 2 : ℂ)) =
    (q : ℂ) * ∑ r : ZMod q, (‖f r‖ ^ 2 : ℂ)
  have he : e.IsPrimitive := ZMod.isPrimitive_stdAddChar q
  calc
    _ = ∑ r : ZMod q, ∑ s : ZMod q,
        (conj (f r) * f s) * ∑ t : ZMod q, e (t * (s - r)) := by
      simp_rw [hexp]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [mul_comm t]
    _ = _ := by
      simp only [AddChar.sum_mulShift _ he, sub_eq_zero,
        mul_ite, mul_zero]
      simp [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Complex.conj_mul']
      ring

/-- P0069 page 6 display 2.1: the Gauss sum norm bound for every modulus. -/
theorem gauss_norm512 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ ZMod.stdAddChar‖ ≤ Real.sqrt (q : ℝ) := by
  let e : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  let G : ZMod q → ℂ := fun t => ∑ r : ZMod q, χ r * e (r * t)
  let S : Finset (ZMod q) := Finset.univ.filter IsUnit
  have hS : 0 < (S.card : ℝ) := by
    have hmem : (1 : ZMod q) ∈ S := by simp [S]
    exact_mod_cast Finset.card_pos.mpr ⟨1, hmem⟩
  have hnorm (t : ZMod q) (ht : IsUnit t) : ‖G t‖ = ‖gaussSum χ e‖ := by
    have h := gaussSum_mulShift_eq χ e ht.unit
    have heq : G t = gaussSum χ (e.mulShift ht.unit) := by
      simp only [G, gaussSum, AddChar.mulShift_apply, ht.unit_spec, mul_comm]
    rw [heq, h, norm_mul, (χ⁻¹).unit_norm_eq_one ht.unit, one_mul]
  have hcoef : ∑ r : ZMod q, ‖χ r‖ ^ 2 = (S.card : ℝ) := by
    have hp (r : ZMod q) : ‖χ r‖ ^ 2 = if IsUnit r then 1 else 0 := by
      by_cases hr : IsUnit r
      · rw [if_pos hr, ← hr.unit_spec, χ.unit_norm_eq_one]
        norm_num
      · rw [if_neg hr, χ.map_nonunit hr, norm_zero, zero_pow (by decide)]
    simp_rw [hp]
    simp [S, Finset.sum_boole]
  have hlow : (S.card : ℝ) * ‖gaussSum χ e‖ ^ 2 ≤ ∑ t : ZMod q, ‖G t‖ ^ 2 := by
    calc
      _ = ∑ t ∈ S, ‖G t‖ ^ 2 := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        apply Finset.sum_congr rfl
        intro t ht
        rw [hnorm t (Finset.mem_filter.mp ht).2]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun t ht hnot => sq_nonneg _)
  have hparse := gauss_parseval512 (q := q) χ
  change (∑ t : ZMod q, ‖G t‖ ^ 2) = (q : ℝ) * ∑ r : ZMod q, ‖χ r‖ ^ 2 at hparse
  rw [hcoef] at hparse
  have hsq : ‖gaussSum χ e‖ ^ 2 ≤ (q : ℝ) := by
    apply (mul_le_mul_iff_left₀ hS).mp
    nlinarith [hlow]
  exact (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg q)).mpr hsq

/-- P0069 page 6 display 2.4: finite character inversion for an arbitrary unit. -/
theorem gauss_inversion512 {q : ℕ} [NeZero q] (e : AddChar (ZMod q) ℂ)
    (k : ZMod q) (hk : IsUnit k) :
    (∑ χ : DirichletCharacter ℂ q, gaussSum χ⁻¹ e * χ k) = (q.totient : ℂ) * e k := by
  have hinv (χ : DirichletCharacter ℂ q) : χ⁻¹ k = χ k⁻¹ := by
    rw [MulChar.inv_apply_eq_inv']
    have hmul : χ k⁻¹ * χ k = 1 := by rw [← map_mul, ZMod.inv_mul_of_unit k hk, map_one]
    exact (eq_inv_of_mul_eq_one_left hmul).symm
  have horth (r : ZMod q) :
      (∑ χ : DirichletCharacter ℂ q, χ⁻¹ r * χ k) = if r = k then (q.totient : ℂ) else 0 := by
    calc
      _ = ∑ χ : DirichletCharacter ℂ q, χ r * χ⁻¹ k := by
        exact Fintype.sum_equiv (Equiv.inv (DirichletCharacter ℂ q)) _ _ (fun χ => by simp)
      _ = ∑ χ : DirichletCharacter ℂ q, χ k⁻¹ * χ r := by
        apply Finset.sum_congr rfl
        intro χ hχ
        rw [hinv]
        ring
      _ = _ := by
        rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hk r]
        simp only [eq_comm]
  calc
    _ = ∑ r : ZMod q, e r * ∑ χ : DirichletCharacter ℂ q, χ⁻¹ r * χ k := by
      simp only [gaussSum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      ring
    _ = _ := by
      simp only [horth, mul_ite, mul_zero]
      simp [mul_comm]

/-- P0069 page 6 display 2.4: expand the supported polynomial in characters. -/
theorem character_expansion512 (S : Finset ℕ) (a : ℕ → ℂ)
    {q : ℕ} [NeZero q] (r : ZMod q) (hr : IsUnit r) (e : AddChar (ZMod q) ℂ) (t : ℝ)
    (hsupp : ∀ k ∈ S, a k ≠ 0 → IsUnit (k : ZMod q)) :
    (∑ k ∈ S, a k * e ((k : ZMod q) * r) * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        gaussSum χ⁻¹ e * χ r * polynomial512 S (fun k => a k * χ (k : ZMod q)) t := by
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  apply (mul_left_cancel₀ hφ)
  rw [← mul_assoc, mul_inv_cancel₀ hφ, one_mul, Finset.mul_sum]
  simp only [polynomial512, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases ha : a k = 0
  · simp [ha]
  have hunit := (hsupp k hk ha).mul hr
  have hg := gauss_inversion512 e ((k : ZMod q) * r) hunit
  calc
    _ = (a k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
        ((q.totient : ℂ) * e ((k : ZMod q) * r)) := by ring
    _ = _ := by
      rw [← hg, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [map_mul]
      ring
/-- P0069 pages 5 and 6: split a rational shift from each integer frequency. -/
theorem fourier_rational_shift512 {q : ℕ} [NeZero q] (k : ℕ) (r : ℤ) (t : ℝ) :
    @fourier 1 (k : ℤ) (((r : ℝ) / q + t : ℝ) : AddCircle (1 : ℝ)) =
      ZMod.stdAddChar (((k : ℤ) * r : ℤ) : ZMod q) *
        @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ)) := by
  rw [fourier_coe_apply, fourier_coe_apply, ZMod.stdAddChar_coe]
  simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_intCast,
    Complex.ofReal_natCast, Complex.ofReal_one, Int.cast_mul, Int.cast_natCast, div_one]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- P0069 page 6 display 2.4, first two equalities: the exact character expansion
of S1 at a rational arc, before subtracting the principal model. -/
theorem shifted_character_expansion512 (S : Finset ℕ) (a : ℕ → ℂ)
    {q : ℕ} [NeZero q] (r : ℤ) (hr : IsUnit (r : ZMod q)) (t : ℝ)
    (hsupp : ∀ k ∈ S, a k ≠ 0 → IsUnit (k : ZMod q)) :
    polynomial512 S a ((r : ℝ) / q + t) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        gaussSum χ⁻¹ ZMod.stdAddChar * χ (r : ZMod q) *
          polynomial512 S (fun k => a k * χ (k : ZMod q)) t := by
  simpa only [polynomial512, fourier_rational_shift512, Int.cast_mul, Int.cast_natCast,
    mul_assoc] using character_expansion512 S a (r : ZMod q) hr ZMod.stdAddChar t hsupp

/-- P0069 pages 2 and 8: normalization diagnostic for the printed center in 2.7.
This compares denominators and does not refute the printed mean square estimate. -/
theorem log_normalization_gap512 (ε x : ℝ) (hε : ε < 9 / 20) (hx : 1 < x) :
    Real.log x * Real.log (length512 ε x) < Real.log x ^ 2 := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hL : 0 < Real.log x := Real.log_pos hx
  rw [length512, Real.log_rpow hx0]
  calc
    Real.log x * ((11 / 20 + ε) * Real.log x) = (11 / 20 + ε) * Real.log x ^ 2 := by ring
    _ < 1 * Real.log x ^ 2 := mul_lt_mul_of_pos_right (by linarith) (sq_pos_of_pos hL)
    _ = _ := one_mul _

/-- P0069 page 8, second display after 2.6: the finite convolution count is Y
up to the endpoint error. Strict N greater than x avoids the boundary pair. -/
theorem convolution_count512 (x Y : ℝ) (N : ℕ) (hY : 0 ≤ Y) (hxy : 2 * Y ≤ x)
    (hlo : x < (N : ℝ)) (hhi : (N : ℝ) ≤ x + Y) :
    (∑ k ∈ Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊,
      ∑ m ∈ Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊, if k + m = N then (1 : ℂ) else 0) =
        ((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).card : ℂ) ∧
      |((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).card : ℝ) - Y| ≤ 1 := by
  constructor
  · rw [Finset.sum_comm]
    calc
      _ = ∑ m ∈ Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hm' := Finset.mem_Ioc.mp hm
        have hmlo : Y < (m : ℝ) := Nat.lt_of_floor_lt hm'.1
        have hmhi : (m : ℝ) ≤ 2 * Y := (Nat.le_floor_iff (by linarith)).mp hm'.2
        have hmn : m ≤ N := by exact_mod_cast (hmhi.trans (hxy.trans hlo.le))
        have hk : N - m ∈ Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊ := by
          apply Finset.mem_Ioc.mpr
          constructor
          · apply (Nat.floor_lt (by linarith : 0 ≤ x - 2 * Y)).mpr
            rw [Nat.cast_sub hmn]
            linarith
          · apply Nat.le_floor
            rw [Nat.cast_sub hmn]
            linarith
        rw [Finset.sum_eq_single (N - m)]
        · simp [Nat.sub_add_cancel hmn]
        · intro k hk' hkm
          have hne : k + m ≠ N := by omega
          simp [hne]
        · intro hnot
          exact (hnot hk).elim
      _ = _ := by simp
  · rw [Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono (by linarith : Y ≤ 2 * Y))]
    have h₁ := Nat.floor_le hY
    have h₂ := Nat.floor_le (by linarith : 0 ≤ 2 * Y)
    have h₃ := Nat.lt_floor_add_one Y
    have h₄ := Nat.lt_floor_add_one (2 * Y)
    rw [abs_le]
    constructor <;> linarith

end LeanLab.BHP1997.Section2MS
