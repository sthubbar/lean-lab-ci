/-
P0069 Baker Harman Pintz 1997, Section 2, pages 5 to 10.
The Fourier identity and the partition are elementary. The major and minor
arc estimates remain separate cited analytic leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Thm2Sing

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
The exact principal model has the original eta limits in display 2.6. OPEN. -/
theorem leaf_major_coefficients512 :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Theorem2With ε B (fun a b u v _ =>
        ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
          ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
            coefficientReplacementError512 ε D x (a x) (b x) u v ≤ C * scale512 ε A x) := by
  sorry

/-- LEAF. P0069 page 8 first two displays after 2.6: extend the eta integral
to a complete period and replace the exact convolution count by Y.
The original finite support and its endpoint error are retained. OPEN. -/
theorem leaf_major_eta_extension512 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u v : ℝ,
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          etaExtensionError512 ε D x u v ≤ C * scale512 ε A x := by
  sorry

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

/-- LEAF. P0069 page 8 display 2.7, using Vaughan reference 31 display 3.23.
QUESTION: the printed center in 2.7 has log x squared. This leaf retains log x
 times log Y from the sealed target 2.2 and the preceding exact model 2.6.
It is a normalized reading of that chain, not a literal transcription of 2.7.
The actual truncated singular series error is reduced to the two divisor moments.
Retain the harmless nonnegative H Y squared logarithmic error term printed in 2.7.
The small epsilon and large internal arc parameter conventions are unchanged. OPEN. -/
theorem leaf_vaughan_tail_reduction512 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u v : ℝ,
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          seriesError512 ε D x u v ≤ C * (scale512 ε A x + length512 ε x ^ 2 *
            divisorTailMoment512 ε D x) := by
  sorry

/-- LEAF. P0069 page 8 display 2.8: the small-divisor mean square estimate on K.
The uniform short interval divisor moment bound used by the paper is not supplied
by a full summatory divisor estimate. OPEN. -/
theorem leaf_small_divisor_moment512 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x → smallDivisorMoment512 ε D x ≤
          C * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * Real.log x ^ (-A - 7) := by
  sorry

/-- LEAF. P0069 page 8 display 2.9: the large-divisor mean square estimate on K.
It is separate from the small-divisor bound and retains the printed tail range. OPEN. -/
theorem leaf_large_divisor_moment512 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x → largeDivisorMoment512 ε D x ≤
          C * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * Real.log x ^ (-A - 7) := by
  sorry

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
The input concerns the actual local integral of S2. OPEN. -/
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
  sorry

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
