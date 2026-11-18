/-
Partial decomposition of P0079, arXiv 0811.3663v2, pages 4 to 12.
AI wrote this Lean code. Goldbach is open.
The threshold sign QUESTION is not an input leaf here.
-/
import LeanLab.LZPowersOfTwo.Statements

open Real Finset MeasureTheory Filter

noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 4, the common exponent cutoff. -/
def cutoff293 (s : ℕ) (μ : ℕ → ℝ) (ε X : ℝ) : ℝ :=
  logb 2 (ε * X / (2 * ∑ i : Fin s, |μ i|))

/-- P0079 page 4, the additive character. -/
def character293 (u : ℝ) : ℂ := Complex.exp ((2 * Real.pi * u : ℝ) * Complex.I)

/-- P0079 page 4, the prime exponential sum. -/
def primeSum293 (ε X α : ℝ) : ℂ :=
  ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)),
    (Real.log p : ℂ) * character293 ((p : ℝ) * α)

/-- P0079 page 4, the powers of two exponential sum. -/
def powerSum293 (L α : ℝ) : ℂ :=
  ∑ m ∈ Icc 1 ⌊L⌋₊, character293 (2 ^ m * α)

/-- P0079 page 4, the kernel with its continuous value at zero. -/
def kernel293 (η α : ℝ) : ℝ := (η * Real.sinc (Real.pi * η * α)) ^ 2

/-- P0079 page 4, the integrand defining I. -/
def integrand293 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X α : ℝ) : ℂ :=
  primeSum293 ε X (l1 * α) * primeSum293 ε X (l2 * α) *
    (∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)) *
    character293 (γ * α) * kernel293 η α

/-- P0079 page 4, display 14, the major arc. -/
def major293 (X : ℝ) : Set ℝ := {α | |α| ≤ X ^ (1 / 3 : ℝ) / X}

/-- P0079 page 4, display 14, the minor arc. -/
def minor293 (X L : ℝ) : Set ℝ := {α | X ^ (1 / 3 : ℝ) / X < |α| ∧ |α| ≤ L ^ 2}

/-- P0079 page 4, display 14, the trivial arc. -/
def trivial293 (X L : ℝ) : Set ℝ := (major293 X ∪ minor293 X L)ᶜ

/-! ### Proof of the counting leaf, P0079 page 4, displays 11 to 13

The helper lemmas below sit in their own namespace `CountIntegral293`. Each is a proved step
of the paper's page 4 argument: kernel bounds and integrability, the box transform, the
Fejer kernel transform to the tent function, the finite expansion and the weighted count. -/

namespace CountIntegral293
open FourierTransform
open scoped Convolution

/-- P0079 page 4, the additive character has unit norm. -/
theorem character_norm293 (u : ℝ) : ‖character293 u‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

/-- P0079 page 4, display 12. The continuous kernel is nonnegative. -/
theorem kernel_nonneg293 (η α : ℝ) : 0 ≤ kernel293 η α := by
  exact sq_nonneg _

/-- P0079 page 4, display 12. The continuous kernel is at most eta squared. -/
theorem kernel_le293 (η α : ℝ) : kernel293 η α ≤ η ^ 2 := by
  have h := mul_self_le_mul_self (abs_nonneg (Real.sinc (Real.pi * η * α)))
    (Real.abs_sinc_le_one (Real.pi * η * α))
  simp only [← pow_two, sq_abs, one_pow] at h
  simpa only [kernel293, mul_pow, mul_one] using mul_le_mul_of_nonneg_left h (sq_nonneg η)

/-- P0079 page 4, display 12. The kernel decays quadratically away from zero. -/
theorem kernel_mul_sq_le293 (η α : ℝ) : kernel293 η α * α ^ 2 ≤ 1 / Real.pi ^ 2 := by
  by_cases hη : η = 0
  · simp [hη, kernel293]
    positivity
  by_cases hα : α = 0
  · simp [hα, kernel293]
    positivity
  have harg : Real.pi * η * α ≠ 0 := mul_ne_zero (mul_ne_zero Real.pi_ne_zero hη) hα
  unfold kernel293
  rw [Real.sinc_of_ne_zero harg]
  have heq : (η * (sin (Real.pi * η * α) / (Real.pi * η * α))) ^ 2 * α ^ 2 =
      sin (Real.pi * η * α) ^ 2 / Real.pi ^ 2 := by
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right (Real.sin_sq_le_one _) (sq_nonneg _)

/-- P0079 page 4, display 12. The kernel is bounded by an integrable Cauchy majorant. -/
theorem kernel_cauchy_le293 (η α : ℝ) :
    kernel293 η α ≤ (η ^ 2 + 1 / Real.pi ^ 2) * (1 + α ^ 2)⁻¹ := by
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith only [kernel_le293 η α, kernel_mul_sq_le293 η α]

/-- P0079 page 4, display 12. The continuous sine kernel is integrable on the real line. -/
theorem kernel_integrable293 (η : ℝ) : Integrable (kernel293 η) := by
  apply (integrable_inv_one_add_sq.const_mul (η ^ 2 + 1 / Real.pi ^ 2)).mono'
  · have hc : Continuous (kernel293 η) := by unfold kernel293; fun_prop
    exact hc.aestronglyMeasurable
  · exact Eventually.of_forall (fun α => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg293 η α)] using kernel_cauchy_le293 η α)

/-- P0079 page 4, display 11. Multiplying the kernel by a character preserves integrability. -/
theorem kernel_character_integrable293 (η t : ℝ) :
    Integrable (fun α => character293 (t * α) * (kernel293 η α : ℂ)) := by
  have hk : Integrable (fun α => (kernel293 η α : ℂ)) :=
    (kernel_integrable293 η).ofReal
  apply hk.bdd_mul (c := 1)
  · have hc : Continuous (fun α : ℝ => character293 (t * α)) := by
      unfold character293
      fun_prop
    exact hc.aestronglyMeasurable
  · exact Eventually.of_forall (fun α => (character_norm293 _).le)

/-- P0079 page 4, the prime sum is bounded uniformly in its frequency. -/
theorem primeSum_norm_le293 (ε X α : ℝ) :
    ‖primeSum293 ε X α‖ ≤
      ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)), |log p| := by
  unfold primeSum293
  calc
    _ ≤ ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)),
      ‖(log p : ℂ) * character293 ((p : ℝ) * α)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, character_norm293, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- P0079 page 4, the powers sum is bounded by its number of terms. -/
theorem powerSum_norm_le293 (L α : ℝ) :
    ‖powerSum293 L α‖ ≤ ((Icc 1 ⌊L⌋₊).card : ℝ) := by
  unfold powerSum293
  calc
    _ ≤ ∑ m ∈ Icc 1 ⌊L⌋₊, ‖character293 (2 ^ m * α)‖ := norm_sum_le _ _
    _ = _ := by simp only [character_norm293, sum_const, nsmul_eq_mul, mul_one]

/-- P0079 page 4, definition of I and displays 11 to 12. All full-line
integrals in the counting argument are well-defined without an analytic hypothesis. -/
theorem integrand_integrable293 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X : ℝ) :
    Integrable (integrand293 s l1 l2 μ γ η ε X) := by
  let P := ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)), |log p|
  let N : ℝ := ((Icc 1 ⌊cutoff293 s μ ε X⌋₊).card : ℝ)
  let g : ℝ → ℂ := fun α => primeSum293 ε X (l1 * α) * primeSum293 ε X (l2 * α) *
    (∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)) * character293 (γ * α)
  have hP : 0 ≤ P := sum_nonneg (fun _ _ => abs_nonneg _)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hprod : ∀ α : ℝ,
      ‖∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ ≤ N ^ s := by
    intro α
    calc
      _ ≤ ∏ i : Fin s, ‖powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ := norm_prod_le _ _
      _ ≤ ∏ _ : Fin s, N := prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => powerSum_norm_le293 _ _)
      _ = _ := by simp
  have hg : ∀ α : ℝ, ‖g α‖ ≤ (P * P) * N ^ s := by
    intro α
    dsimp [g]
    simp only [norm_mul, character_norm293, mul_one]
    exact mul_le_mul (mul_le_mul (primeSum_norm_le293 _ _ _) (primeSum_norm_le293 _ _ _)
      (norm_nonneg _) hP) (hprod α) (norm_nonneg _) (mul_nonneg hP hP)
  have hc : Continuous g := by
    dsimp [g]
    unfold primeSum293 powerSum293 character293
    fun_prop
  have hk : Integrable (fun α => (kernel293 η α : ℂ)) := (kernel_integrable293 η).ofReal
  exact hk.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall hg)

/-- P0079 page 4, display 11. The elementary centered-box transform is
eta times sinc of pi eta alpha. This is an input to the squared-kernel identity. -/
theorem character_interval293 (η α : ℝ) :
    (∫ u in -(η / 2)..(η / 2), character293 (u * α)) =
      ((η * Real.sinc (Real.pi * η * α) : ℝ) : ℂ) := by
  by_cases hα : α = 0
  · simp [hα, character293, intervalIntegral.integral_const]

  let c : ℝ := 2 * Real.pi * α
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hα
  have heq : (fun u : ℝ => character293 (u * α)) =
      (fun u : ℝ => Complex.exp ((c * u : ℝ) * Complex.I)) := by
    funext u
    unfold character293
    rw [show 2 * Real.pi * (u * α) = c * u by dsimp [c]; ring]
  rw [heq, intervalIntegral.integral_comp_mul_left (fun u : ℝ => Complex.exp (u * Complex.I)) hc]
  rw [show c * -(η / 2) = -(c * (η / 2)) by ring, integral_exp_mul_I_eq_sinc]
  have harg : c * (η / 2) = Real.pi * η * α := by dsimp [c]; ring
  rw [harg]
  have hcoeff : c⁻¹ * (2 * (Real.pi * η * α)) = η := by
    dsimp [c]
    field_simp

  rw [Complex.real_smul]
  have hcoeff' := congrArg (fun r : ℝ => (r : ℂ)) hcoeff
  push_cast at hcoeff' ⊢
  linear_combination hcoeff' * (Real.sinc (Real.pi * η * α) : ℂ)

/-- P0079 page 4, display 11. The overlap of two centered boxes is the tent
function. This is the real convolution calculation behind the kernel identity. -/
theorem box_overlap293 (η t : ℝ) :
    (∫ u : ℝ, (Set.Icc (-(η / 2)) (η / 2)).indicator (fun _ => (1 : ℝ)) u *
      (Set.Icc (-(η / 2)) (η / 2)).indicator (fun _ => (1 : ℝ)) (t - u)) =
      max 0 (η - |t|) := by
  have hid : (fun u : ℝ => (Set.Icc (-(η / 2)) (η / 2)).indicator (fun _ => (1 : ℝ)) u *
      (Set.Icc (-(η / 2)) (η / 2)).indicator (fun _ => (1 : ℝ)) (t - u)) =
      (Set.Icc (max (-(η / 2)) (t - η / 2)) (min (η / 2) (t + η / 2))).indicator
        (fun _ => (1 : ℝ)) := by
    funext u
    have hcond : (u ∈ Set.Icc (-(η / 2)) (η / 2) ∧ t - u ∈ Set.Icc (-(η / 2)) (η / 2)) ↔
        u ∈ Set.Icc (max (-(η / 2)) (t - η / 2)) (min (η / 2) (t + η / 2)) := by
      simp only [Set.mem_Icc, max_le_iff, le_min_iff]
      constructor <;> rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ <;> constructor <;> constructor <;> linarith
    simp only [Set.indicator_apply, ← hcond]
    by_cases ha : u ∈ Set.Icc (-(η / 2)) (η / 2) <;>
      by_cases hb : t - u ∈ Set.Icc (-(η / 2)) (η / 2) <;> simp [ha, hb]
  rw [hid, integral_indicator_const (1 : ℝ) measurableSet_Icc, smul_eq_mul, mul_one,
    Real.volume_real_Icc]
  rcases le_total 0 t with ht | ht
  · rw [min_eq_left (show η / 2 ≤ t + η / 2 by linarith),
      max_eq_right (show -(η / 2) ≤ t - η / 2 by linarith), abs_of_nonneg ht, max_comm]
    congr 1
    ring
  · rw [min_eq_right (show t + η / 2 ≤ η / 2 by linarith),
      max_eq_left (show t - η / 2 ≤ -(η / 2) by linarith), abs_of_nonpos ht, max_comm]
    congr 1
    ring

/-- P0079 page 4, display 11. The full-line transform of the continuous
squared-sine kernel is the tent function. -/
theorem kernel_transform293 (η t : ℝ) (hη : 0 < η) :
    (∫ α : ℝ, character293 (t * α) * (kernel293 η α : ℂ)) =
      ((max 0 (η - |t|) : ℝ) : ℂ) := by
  let A : Set ℝ := Set.Icc (-(η / 2)) (η / 2)
  let f : ℝ → ℂ := A.indicator (fun _ => 1)
  have hf : Integrable f := by
    dsimp [f]
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hft : ∀ ξ : ℝ, 𝓕 f ξ = ((η * sinc (Real.pi * η * ξ) : ℝ) : ℂ) := by
    intro ξ
    rw [Real.fourier_eq']
    have heq : (fun u : ℝ => Complex.exp ((-2 * Real.pi * inner ℝ u ξ : ℝ) * Complex.I) • f u) =
        A.indicator (fun u => character293 (u * (-ξ))) := by
      funext u
      by_cases hu : u ∈ A
      · simp only [f, Set.indicator_of_mem hu, smul_eq_mul, mul_one]
        unfold character293
        rw [Real.inner_apply]
        rw [show -2 * Real.pi * (u * ξ) = 2 * Real.pi * (u * (-ξ)) by ring]
      · simp [f, hu]
    rw [heq, integral_indicator measurableSet_Icc]
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show -(η / 2) ≤ η / 2 by linarith)]
    rw [character_interval293]
    rw [show Real.pi * η * (-ξ) = -(Real.pi * η * ξ) by ring, sinc_neg]
  let g : ℝ → ℂ := f ⋆[ContinuousLinearMap.mul ℂ ℂ] f
  have hg : ∀ x : ℝ, g x = ((max 0 (η - |x|) : ℝ) : ℂ) := by
    intro x
    rw [show g x = ∫ u : ℝ, f u * f (x - u) by rfl]
    have heq : (fun u : ℝ => f u * f (x - u)) =
        (fun u : ℝ => ((A.indicator (fun _ => (1 : ℝ)) u *
          A.indicator (fun _ => (1 : ℝ)) (x - u) : ℝ) : ℂ)) := by
      funext u
      by_cases hu : u ∈ A <;> by_cases hv : x - u ∈ A <;> simp [f, hu, hv]
    rw [heq, integral_complex_ofReal]
    exact congrArg (fun r : ℝ => (r : ℂ)) (box_overlap293 η x)
  have hgc : Continuous g := by
    have H : g = (fun x : ℝ => ((max 0 (η - |x|) : ℝ) : ℂ)) := funext hg
    rw [H]
    fun_prop
  have hgi : Integrable g := hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf
  have hfg : 𝓕 g = (fun ξ : ℝ => (kernel293 η ξ : ℂ)) := by
    funext ξ
    rw [show 𝓕 g ξ = 𝓕 (f ⋆[ContinuousLinearMap.mul ℂ ℂ] f) ξ by rfl,
      Real.fourier_mul_convolution_eq hf hf, hft]
    simp only [kernel293, pow_two, Complex.ofReal_mul]
  have hki : Integrable (𝓕 g) := by rw [hfg]; exact (kernel_integrable293 η).ofReal
  have H := hgc.fourierInv_fourier_eq hgi hki
  calc
    _ = 𝓕⁻ (𝓕 g) t := by
      rw [hfg, Real.fourierInv_eq']
      apply integral_congr_ae
      exact Eventually.of_forall (fun α => by
        simp only [smul_eq_mul, Real.inner_apply]
        unfold character293
        rw [show 2 * Real.pi * (t * α) = 2 * Real.pi * (α * t) by ring])
    _ = g t := congrFun H t
    _ = _ := hg t

/-- P0079 page 4, definition of N. The solution set in a fixed box is finite. -/
theorem counted_set_finite293 {s : ℕ} (l1 l2 : ℝ) (μ : Fin s → ℝ) (γ η ε X : ℝ) :
    {x ∈ Sol l1 l2 μ γ η | ε * X ≤ x.1 ∧ (x.1 : ℝ) ≤ X ∧ ε * X ≤ x.2.1 ∧
      (x.2.1 : ℝ) ≤ X ∧ ∀ i, (x.2.2 i : ℝ) ≤ logb 2 (ε * X / (2 * ∑ j, |μ j|))}.Finite := by
  let L := logb 2 (ε * X / (2 * ∑ j, |μ j|))
  have hfun : {m : Fin s → ℕ | ∀ i, m i ≤ ⌊L⌋₊}.Finite := by
    apply (Set.finite_range (fun m : Fin s → Fin (⌊L⌋₊ + 1) => fun i => (m i : ℕ))).subset
    intro m hm
    exact ⟨(fun i => ⟨m i, Nat.lt_succ_of_le (hm i)⟩), rfl⟩
  apply ((Set.finite_Iic ⌊X⌋₊).prod ((Set.finite_Iic ⌊X⌋₊).prod hfun)).subset
  intro x hx
  exact ⟨Nat.le_floor hx.2.2.1, Nat.le_floor hx.2.2.2.2.1,
    fun i => Nat.le_floor (hx.2.2.2.2.2 i)⟩

/-- P0079 page 4, the weighted counting inequality before display 13.
Any finite collection of candidate prime tuples contributes at most eta log squared X
per counted solution. The collection need not contain every candidate. -/
theorem weighted_count_le293 {s : ℕ} (l1 l2 : ℝ) (μ : Fin s → ℝ) (γ η ε X : ℝ)
    (hη : 0 < η) (hX : 2 ≤ X) (T : Finset (ℕ × ℕ × (Fin s → ℕ)))
    (hT : ∀ x ∈ T, x.1.Prime ∧ x.2.1.Prime ∧ (∀ i, 1 ≤ x.2.2 i) ∧
      ε * X ≤ x.1 ∧ (x.1 : ℝ) ≤ X ∧ ε * X ≤ x.2.1 ∧ (x.2.1 : ℝ) ≤ X ∧
      ∀ i, (x.2.2 i : ℝ) ≤ logb 2 (ε * X / (2 * ∑ j, |μ j|))) :
    ∑ x ∈ T, log x.1 * log x.2.1 * max 0 (η - |form l1 l2 μ γ x.1 x.2.1 x.2.2|) ≤
      η * (log X) ^ 2 * NX l1 l2 μ γ η ε X := by
  let S := T.filter (fun x => |form l1 l2 μ γ x.1 x.2.1 x.2.2| < η)
  let w := fun x : ℕ × ℕ × (Fin s → ℕ) =>
    log x.1 * log x.2.1 * max 0 (η - |form l1 l2 μ γ x.1 x.2.1 x.2.2|)
  have hsum : ∑ x ∈ T, w x = ∑ x ∈ S, w x := by
    symm
    dsimp only [S]
    rw [sum_filter]
    apply sum_congr rfl
    intro x hx
    split_ifs with h
    · rfl
    · have hz : max 0 (η - |form l1 l2 μ γ x.1 x.2.1 x.2.2|) = 0 :=
        max_eq_left (by linarith [le_of_not_gt h])
      simp [w, hz]
  have hweight : ∀ x ∈ S, w x ≤ η * (log X) ^ 2 := by
    intro x hx
    obtain ⟨hp1, hp2, hm, hlow1, hupp1, hlow2, hupp2, hcut⟩ := hT x (mem_filter.mp hx).1
    have hp1' : (1 : ℝ) ≤ x.1 := by exact_mod_cast hp1.one_lt.le
    have hp2' : (1 : ℝ) ≤ x.2.1 := by exact_mod_cast hp2.one_lt.le
    have hlog1 := log_nonneg hp1'
    have hlog2 := log_nonneg hp2'
    have hlogX : 0 ≤ log X := log_nonneg (by linarith)
    have hlog1X : log x.1 ≤ log X := log_le_log (by linarith) hupp1
    have hlog2X : log x.2.1 ≤ log X := log_le_log (by linarith) hupp2
    have htent : max 0 (η - |form l1 l2 μ γ x.1 x.2.1 x.2.2|) ≤ η :=
      max_le hη.le (by linarith [abs_nonneg (form l1 l2 μ γ x.1 x.2.1 x.2.2)])
    calc
      w x ≤ (log X * log X) * η :=
        mul_le_mul (mul_le_mul hlog1X hlog2X hlog2 hlogX) htent
          (le_max_left _ _) (mul_nonneg hlogX hlogX)
      _ = _ := by ring
  have hcard : S.card ≤ NX l1 l2 μ γ η ε X := by
    rw [← Set.ncard_coe_finset S]
    apply Set.ncard_le_ncard (ht := counted_set_finite293 l1 l2 μ γ η ε X)
    intro x hx
    have hxs := mem_filter.mp hx
    obtain ⟨hp1, hp2, hm, hlow1, hupp1, hlow2, hupp2, hcut⟩ := hT x hxs.1
    exact ⟨⟨hp1, hp2, hm, hxs.2⟩, hlow1, hupp1, hlow2, hupp2, hcut⟩
  calc
    _ = ∑ x ∈ S, w x := hsum
    _ ≤ ∑ _ ∈ S, η * (log X) ^ 2 := sum_le_sum hweight
    _ = (S.card : ℝ) * (η * (log X) ^ 2) := by simp
    _ ≤ (NX l1 l2 μ γ η ε X : ℝ) * (η * (log X) ^ 2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by ring

/-- P0079 page 4, definition of the additive character. Addition of phases
is multiplication of characters. -/
theorem character_add293 (x y : ℝ) : character293 (x + y) = character293 x * character293 y := by
  unfold character293
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- P0079 page 4, expansion of the product of power sums. A finite phase sum
has character equal to the product of its characters. -/
theorem character_sum293 {ι : Type*} (T : Finset ι) (φ : ι → ℝ) :
    character293 (∑ i ∈ T, φ i) = ∏ i ∈ T, character293 (φ i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [character293]
  | @insert a T ha ih => simp [ha, character_add293, ih]

/-- P0079 page 4, displays 11 to 13. A finite weighted exponential sum
integrates term by term against the kernel to the weighted tent sum. -/
theorem finite_kernel_integral293 {ι : Type*} (T : Finset ι) (w : ι → ℂ) (φ : ι → ℝ)
    (η : ℝ) (hη : 0 < η) :
    (∫ α : ℝ, (∑ i ∈ T, w i * character293 (φ i * α)) * (kernel293 η α : ℂ)) =
      ∑ i ∈ T, w i * ((max 0 (η - |φ i|) : ℝ) : ℂ) := by
  simp_rw [sum_mul, mul_assoc]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro i hi
    rw [integral_const_mul, kernel_transform293 η (φ i) hη]
  · intro i hi
    exact (kernel_character_integrable293 η (φ i)).const_mul (w i)

/-- P0079 page 4, expansion of the product defining I before display 13.
The integrand is a finite weighted character sum times the kernel. -/
theorem integrand_expansion293 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ)
    (γ η ε X α : ℝ) :
    integrand293 s l1 l2 μ γ η ε X α =
      (∑ x ∈ (((range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ))) ×ˢ
        (((range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ))) ×ˢ
          Fintype.piFinset (fun _ : Fin s => Icc 1 ⌊cutoff293 s μ ε X⌋₊))),
        ((log x.1 * log x.2.1 : ℝ) : ℂ) *
          character293 (form l1 l2 (fun i : Fin s => μ i) γ x.1 x.2.1 x.2.2 * α)) *
        (kernel293 η α : ℂ) := by
  classical
  unfold integrand293 primeSum293 powerSum293
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.prod_univ_sum]
  simp only [Finset.sum_product]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro m hm
  rw [← character_sum293]
  simp only [form, add_mul, Finset.sum_mul, character_add293]
  push_cast
  ring

end CountIntegral293

/-- LEAF. P0079 page 4, displays 11 to 13. Fourier expansion bounds the full
integral by the weighted number of solutions. No irrationality input is used. -/
theorem count_integral293 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X : ℝ)
    (hη : 0 < η) (hε : 0 < ε) (hX : 2 ≤ X) :
    Integrable (integrand293 s l1 l2 μ γ η ε X) ∧
    (∫ α : ℝ, integrand293 s l1 l2 μ γ η ε X α).re ≤
      η * (log X) ^ 2 * NX l1 l2 (fun i : Fin s => μ i) γ η ε X := by
  classical
  refine ⟨CountIntegral293.integrand_integrable293 s l1 l2 μ γ η ε X, ?_⟩
  have hi := CountIntegral293.finite_kernel_integral293 ((((range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ))) ×ˢ
        (((range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ))) ×ˢ
          Fintype.piFinset (fun _ : Fin s => Icc 1 ⌊cutoff293 s μ ε X⌋₊))))
    (fun x => ((log x.1 * log x.2.1 : ℝ) : ℂ))
    (fun x => form l1 l2 (fun i : Fin s => μ i) γ x.1 x.2.1 x.2.2) η hη
  have heq : (∫ α : ℝ, integrand293 s l1 l2 μ γ η ε X α).re =
      ∑ x ∈ (((range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ))) ×ˢ
        (((range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ))) ×ˢ
          Fintype.piFinset (fun _ : Fin s => Icc 1 ⌊cutoff293 s μ ε X⌋₊))), log x.1 * log x.2.1 *
        max 0 (η - |form l1 l2 (fun i : Fin s => μ i) γ x.1 x.2.1 x.2.2|) := by
    simp_rw [CountIntegral293.integrand_expansion293]
    rw [hi]
    simp only [Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [heq]
  apply CountIntegral293.weighted_count_le293 l1 l2 (fun i : Fin s => μ i) γ η ε X hη hX
  intro x hx
  simp only [mem_product, mem_filter, mem_range,
    Fintype.mem_piFinset, mem_Icc] at hx
  refine ⟨hx.1.2.1, hx.2.1.2.1, fun i => (hx.2.2 i).1, hx.1.2.2, ?_,
    hx.2.1.2.2, ?_, ?_⟩
  · exact (by exact_mod_cast Nat.le_of_lt_succ hx.1.1 : (x.1 : ℝ) ≤ ⌊X⌋₊).trans
      (Nat.floor_le (by linarith))
  · exact (by exact_mod_cast Nat.le_of_lt_succ hx.2.1.1 : (x.2.1 : ℝ) ≤ ⌊X⌋₊).trans
      (Nat.floor_le (by linarith))
  · intro i
    have hL : 0 < cutoff293 s μ ε X := Nat.pos_of_floor_pos
      (lt_of_lt_of_le Nat.zero_lt_one ((hx.2.2 i).1.trans (hx.2.2 i).2))
    exact (by exact_mod_cast (hx.2.2 i).2 :
      (x.2.2 i : ℝ) ≤ ⌊cutoff293 s μ ε X⌋₊).trans (Nat.floor_le hL.le)

/-- LEAF. P0079 page 9, displays 33 to 35. This is only the major arc estimate.
It makes no assertion about the sign of the final major minus minor coefficient. -/
theorem major_lower293 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ᶠ X : ℝ in atTop,
      (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 * X * (cutoff293 s μ ε X) ^ s ≤
        (∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α).re := by
  sorry

/-! ### Proof of the trivial arc leaf, P0079 page 10, Section 5, display 17

The helper lemmas below sit in their own namespace `TrivialSmall293`. The paper bounds the powers
of two sums trivially, applies Cauchy-Schwarz, and bounds the tail mean square of the prime sums
by periodicity and Parseval. Here the periodic splitting is replaced by a pointwise majorant of
the kernel tail by two narrow Fejer kernels, and the Prime Number Theorem by Chebyshev's bound.
AI wrote this Lean code. Goldbach is open. -/

namespace TrivialSmall293
open CountIntegral293

/-- Closed form of the kernel away from zero. -/
theorem kernel_eq_of_ne293 (η β : ℝ) (hη : η ≠ 0) (hβ : β ≠ 0) :
    kernel293 η β = sin (Real.pi * η * β) ^ 2 / (Real.pi ^ 2 * β ^ 2) := by
  have harg : Real.pi * η * β ≠ 0 := mul_ne_zero (mul_ne_zero Real.pi_ne_zero hη) hβ
  unfold kernel293
  rw [Real.sinc_of_ne_zero harg]
  field_simp

/-- Standard majorant. Outside [-T, T] the kernel is at most four times the sum of a narrow Fejer kernel and its shift by T. -/
theorem tail_kernel_le293 (η T α : ℝ) (hT : 0 < T) (hα : T < |α|) :
    kernel293 η α ≤ 4 * (kernel293 (1 / (2 * T)) α + kernel293 (1 / (2 * T)) (α - T)) := by
  have hα0 : α ≠ 0 := by
    intro h; rw [h, abs_zero] at hα; linarith
  have hαT : α - T ≠ 0 := by
    intro h
    have : α = T := by linarith
    rw [this, abs_of_pos hT] at hα; linarith
  have hη' : (1 / (2 * T) : ℝ) ≠ 0 := by positivity
  have hprod : 0 ≤ (α + T) * (3 * α - T) := by
    rcases abs_cases α with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h] at hα; exact (mul_pos (by linarith) (by linarith)).le
    · rw [h] at hα; exact (mul_pos_of_neg_of_neg (by linarith) (by linarith)).le
  have hsq : (α - T) ^ 2 ≤ 4 * α ^ 2 := by nlinarith only [hprod]
  have hα2 : 0 < α ^ 2 := by positivity
  have hαT2 : 0 < (α - T) ^ 2 := by positivity
  have hpi2 : 0 < Real.pi ^ 2 := by positivity
  have hA : 0 < Real.pi ^ 2 * α ^ 2 := mul_pos hpi2 hα2
  have h1 : kernel293 η α ≤ 1 / (Real.pi ^ 2 * α ^ 2) := by
    rw [le_div_iff₀ hA]
    have h := kernel_mul_sq_le293 η α
    have h' := mul_le_mul_of_nonneg_right h hpi2.le
    have e : 1 / Real.pi ^ 2 * Real.pi ^ 2 = 1 := by field_simp
    rw [e] at h'
    linarith only [h']
  set θ : ℝ := Real.pi * (1 / (2 * T)) * α with hθ
  have hshift : Real.pi * (1 / (2 * T)) * (α - T) = θ - Real.pi / 2 := by
    rw [hθ]; field_simp
  have hsin : sin (Real.pi * (1 / (2 * T)) * (α - T)) ^ 2 = cos θ ^ 2 := by
    rw [hshift, Real.sin_sub_pi_div_two, neg_sq]
  rw [kernel_eq_of_ne293 _ α hη' hα0, kernel_eq_of_ne293 _ (α - T) hη' hαT, hsin]
  have hc : cos θ ^ 2 / (Real.pi ^ 2 * (4 * α ^ 2)) ≤
      cos θ ^ 2 / (Real.pi ^ 2 * (α - T) ^ 2) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hpi2 hαT2)
      (mul_le_mul_of_nonneg_left hsq hpi2.le)
  have hsc : sin θ ^ 2 + cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have e2 : cos θ ^ 2 / (Real.pi ^ 2 * (4 * α ^ 2)) =
      cos θ ^ 2 / 4 * (1 / (Real.pi ^ 2 * α ^ 2)) := by
    field_simp
  have e3 : sin θ ^ 2 / (Real.pi ^ 2 * α ^ 2) = sin θ ^ 2 * (1 / (Real.pi ^ 2 * α ^ 2)) := by
    ring
  have hpos : 0 ≤ 1 / (Real.pi ^ 2 * α ^ 2) := by positivity
  rw [e2] at hc
  rw [e3]
  nlinarith only [h1, hc, hsc, hpos, mul_nonneg (sq_nonneg (sin θ)) hpos]

/-- Conjugating the additive character negates the phase. -/
theorem character_conj293 (u : ℝ) :
    (starRingEnd ℂ) (character293 u) = character293 (-u) := by
  unfold character293
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- Expansion of the squared prime sum as a double character sum. -/
theorem primeSum_sq_expansion293 (ε X l a β : ℝ) :
    ((‖primeSum293 ε X (l * (β + a))‖ ^ 2 : ℝ) : ℂ) =
      ∑ x ∈ ((range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ))) ×ˢ
          ((range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ))),
        (((Real.log (x.1 : ℝ) * Real.log (x.2 : ℝ) : ℝ) : ℂ) *
          character293 (l * ((x.1 : ℝ) - (x.2 : ℝ)) * a)) *
          character293 (l * ((x.1 : ℝ) - (x.2 : ℝ)) * β) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  unfold primeSum293
  rw [map_sum, Finset.sum_mul_sum, Finset.sum_product]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  dsimp only
  rw [map_mul, Complex.conj_ofReal, character_conj293]
  have h : character293 (l * ((p : ℝ) - (q : ℝ)) * a) * character293 (l * ((p : ℝ) - (q : ℝ)) * β) =
      character293 ((p : ℝ) * (l * (β + a))) * character293 (-((q : ℝ) * (l * (β + a)))) := by
    rw [← character_add293, ← character_add293]
    congr 1
    ring
  rw [Complex.ofReal_mul]
  linear_combination -(((Real.log (p : ℝ) : ℝ) : ℂ) * ((Real.log (q : ℝ) : ℝ) : ℂ)) * h

/-- Only the diagonal survives a tent no wider than |l|. -/
theorem diag_sum293 (P : Finset ℕ) (l a η' : ℝ) (hη : 0 < η') (hl : η' ≤ |l|) :
    ∑ x ∈ P ×ˢ P,
        (((Real.log (x.1 : ℝ) * Real.log (x.2 : ℝ) : ℝ) : ℂ) *
          character293 (l * ((x.1 : ℝ) - (x.2 : ℝ)) * a)) *
          ((max 0 (η' - |l * ((x.1 : ℝ) - (x.2 : ℝ))|) : ℝ) : ℂ) =
      ((η' * ∑ p ∈ P, (Real.log (p : ℝ)) ^ 2 : ℝ) : ℂ) := by
  rw [Finset.sum_product, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [Finset.sum_eq_single p]
  · have h0 : character293 0 = 1 := by simp [character293]
    simp only [sub_self, mul_zero, zero_mul, h0, abs_zero, sub_zero, max_eq_right hη.le, mul_one]
    push_cast
    ring
  · intro q _ hne
    have hz : ((p : ℤ) - (q : ℤ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne.symm)
    have h1 : ((1 : ℤ) : ℝ) ≤ ((|(p : ℤ) - (q : ℤ)| : ℤ) : ℝ) :=
      Int.cast_le.mpr (Int.one_le_abs hz)
    push_cast at h1
    have h2 : |l| ≤ |l * ((p : ℝ) - (q : ℝ))| := by
      rw [abs_mul]
      exact le_mul_of_one_le_right (abs_nonneg l) h1
    have h3 : max 0 (η' - |l * ((p : ℝ) - (q : ℝ))|) = 0 := max_eq_left (by linarith)
    simp only [h3, Complex.ofReal_zero, mul_zero]
  · intro h
    exact absurd hp h

/-- Parseval with the Fejer kernel. A kernel no wider than |l| sees only the diagonal of the squared prime sum. -/
theorem prime_meansq293 (ε X l a η' : ℝ) (hη : 0 < η') (hl : η' ≤ |l|) :
    Integrable (fun α : ℝ => ‖primeSum293 ε X (l * α)‖ ^ 2 * kernel293 η' (α - a)) ∧
    ∫ α : ℝ, ‖primeSum293 ε X (l * α)‖ ^ 2 * kernel293 η' (α - a) =
      η' * ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)), (log p) ^ 2 := by
  constructor
  · have hk : Integrable (fun α : ℝ => kernel293 η' (α - a)) :=
      (kernel_integrable293 η').comp_sub_right a
    have hc : Continuous (fun α : ℝ => ‖primeSum293 ε X (l * α)‖ ^ 2) := by
      unfold primeSum293 character293
      fun_prop
    have hb : ∀ α : ℝ, ‖‖primeSum293 ε X (l * α)‖ ^ 2‖ ≤
        (∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)), |log p|) ^ 2 := by
      intro α
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (primeSum_norm_le293 _ _ _) 2
    exact hk.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall hb)
  · have h1 : ∫ α : ℝ, ‖primeSum293 ε X (l * α)‖ ^ 2 * kernel293 η' (α - a) =
        ∫ β : ℝ, ‖primeSum293 ε X (l * (β + a))‖ ^ 2 * kernel293 η' β := by
      have h := integral_sub_right_eq_self (μ := volume)
        (fun β : ℝ => ‖primeSum293 ε X (l * (β + a))‖ ^ 2 * kernel293 η' β) a
      simp only [sub_add_cancel] at h
      exact h
    have h2 : ∀ β : ℝ, ((‖primeSum293 ε X (l * (β + a))‖ ^ 2 * kernel293 η' β : ℝ) : ℂ) =
        (∑ x ∈ ((range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ))) ×ˢ
          ((range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ))),
        (((Real.log (x.1 : ℝ) * Real.log (x.2 : ℝ) : ℝ) : ℂ) *
          character293 (l * ((x.1 : ℝ) - (x.2 : ℝ)) * a)) *
          character293 (l * ((x.1 : ℝ) - (x.2 : ℝ)) * β)) * (kernel293 η' β : ℂ) := by
      intro β
      rw [Complex.ofReal_mul, primeSum_sq_expansion293]
    have hi := finite_kernel_integral293
      (((range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ))) ×ˢ
          ((range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ))))
      (fun x : ℕ × ℕ => ((Real.log (x.1 : ℝ) * Real.log (x.2 : ℝ) : ℝ) : ℂ) *
          character293 (l * ((x.1 : ℝ) - (x.2 : ℝ)) * a))
      (fun x : ℕ × ℕ => l * ((x.1 : ℝ) - (x.2 : ℝ))) η' hη
    have hC : ((∫ β : ℝ, ‖primeSum293 ε X (l * (β + a))‖ ^ 2 * kernel293 η' β : ℝ) : ℂ) =
        ((η' * ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)),
          (Real.log (p : ℝ)) ^ 2 : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact (integral_congr_ae (Eventually.of_forall h2)).trans
        (hi.trans (diag_sum293 _ l a η' hη hl))
    rw [h1]
    exact Complex.ofReal_injective hC

/-- Chebyshev's bound theta(X) ≤ log 4 * X, weighted by one more logarithm. -/
theorem prime_log_sq_sum_le293 (ε X : ℝ) (hX : 1 ≤ X) :
    ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)), (log p) ^ 2 ≤
      log 4 * X * log X := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hlogX : 0 ≤ log X := Real.log_nonneg hX
  have h1 : ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)),
      (log p) ^ 2 ≤
      ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)),
        log X * log p := by
    refine Finset.sum_le_sum fun p hp => ?_
    rw [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpX, hpp, -⟩ := hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
    have hple : (p : ℝ) ≤ X :=
      le_trans (by exact_mod_cast Nat.lt_succ_iff.mp hpX) (Nat.floor_le hX0)
    have hlp : 0 ≤ log (p : ℝ) := Real.log_nonneg hp1
    have hle : log (p : ℝ) ≤ log X := Real.log_le_log (by linarith) hple
    rw [sq]
    exact mul_le_mul_of_nonneg_right hle hlp
  have h2 : ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)),
      log (p : ℝ) ≤ Chebyshev.theta X := by
    unfold Chebyshev.theta
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_range] at hp
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hp.2.1.pos, Nat.lt_succ_iff.mp hp.1⟩, hp.2.1⟩
    · intro p hp _
      rw [Finset.mem_filter] at hp
      exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
  calc _ ≤ ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)),
        log X * log p := h1
    _ = log X * ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)),
        log (p : ℝ) := by rw [Finset.mul_sum]
    _ ≤ log X * (log 4 * X) :=
        mul_le_mul_of_nonneg_left (h2.trans (Chebyshev.theta_le_log4_mul_x hX0)) hlogX
    _ = log 4 * X * log X := by ring

/-- P0079 page 4. The cutoff L = log_2 (ε X / (2 M)) tends to infinity and L^2 dominates any multiple of log X. -/
theorem cutoff_eventually293 (s : ℕ) (μ : ℕ → ℝ) (ε : ℝ) (hs : 2 ≤ s) (hμ : ∀ i, μ i ≠ 0)
    (hε : 0 < ε) (C : ℝ) :
    ∀ᶠ X : ℝ in atTop, C ≤ cutoff293 s μ ε X ∧ C * log X ≤ (cutoff293 s μ ε X) ^ 2 := by
  have hM : 0 < ∑ i : Fin s, |μ i| :=
    Finset.sum_pos (fun i _ => abs_pos.mpr (hμ i)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hc : 0 < ε / (2 * ∑ i : Fin s, |μ i|) := by positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    tendsto_log_atTop.eventually_ge_atTop
      (2 * |log (ε / (2 * ∑ i : Fin s, |μ i|))| + 6 * |C|)] with X hX hl
  have hXpos : 0 < X := by linarith
  have hcut : cutoff293 s μ ε X =
      (log (ε / (2 * ∑ i : Fin s, |μ i|)) + log X) / log 2 := by
    unfold cutoff293
    rw [show ε * X / (2 * ∑ i : Fin s, |μ i|) = ε / (2 * ∑ i : Fin s, |μ i|) * X by ring,
      logb, log_mul hc.ne' hXpos.ne']
  rw [hcut]
  generalize log (ε / (2 * ∑ i : Fin s, |μ i|)) = a at hl
  generalize log X = l at hl
  have h2 : 0 < log 2 := log_pos (by norm_num)
  have h2' : log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have ha := neg_abs_le a
  have hC0 := abs_nonneg C
  have hCle := le_abs_self C
  have ha0 := abs_nonneg a
  have ht : l / 2 ≤ a + l := by linarith
  have ht0 : 0 ≤ a + l := by linarith
  have hdiv : a + l ≤ (a + l) / log 2 := by
    rw [le_div_iff₀ h2]; nlinarith
  refine ⟨by linarith, ?_⟩
  have h1 : C * l ≤ |C| * l := mul_le_mul_of_nonneg_right hCle (by linarith)
  have h3 : |C| * l ≤ (l / 2) ^ 2 := by nlinarith
  have h4 : (l / 2) ^ 2 ≤ ((a + l) / log 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  linarith

/-- P0079 page 4, display 14. Every point of the trivial arc lies beyond L squared. -/
theorem trivial_mem293 (X L α : ℝ) (h : α ∈ trivial293 X L) : L ^ 2 < |α| := by
  simp only [trivial293, major293, minor293, Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq,
    not_or, not_and, not_le] at h
  exact h.2 h.1

/-- P0079 page 4, display 14. The trivial arc is a measurable set. -/
theorem trivial_measurable293 (X L : ℝ) : MeasurableSet (trivial293 X L) := by
  have habs : Measurable (fun α : ℝ => |α|) := continuous_abs.measurable
  have hmaj : MeasurableSet (major293 X) := measurableSet_le habs measurable_const
  have hmin : MeasurableSet (minor293 X L) :=
    (measurableSet_lt measurable_const habs).inter (measurableSet_le habs measurable_const)
  exact (hmaj.union hmin).compl

/-- P0079 page 10, Section 5. The trivial arc bound at a fixed large X: the powers of two sums
are bounded trivially, the product of the prime sums by the arithmetic and geometric mean
inequality, and the squared prime sums by Parseval against narrow Fejer kernels. -/
theorem trivial_bound293 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X : ℝ) (hX : 1 ≤ X)
    (hL : 0 < cutoff293 s μ ε X)
    (h1 : 1 / (2 * (cutoff293 s μ ε X) ^ 2) ≤ |l1|)
    (h2 : 1 / (2 * (cutoff293 s μ ε X) ^ 2) ≤ |l2|) :
    ‖∫ α in trivial293 X (cutoff293 s μ ε X), integrand293 s l1 l2 μ γ η ε X α‖ ≤
      (cutoff293 s μ ε X) ^ s * (4 / (cutoff293 s μ ε X) ^ 2) * (log 4 * X * log X) := by
  set L := cutoff293 s μ ε X with hLdef
  set T : ℝ := L ^ 2 with hTdef
  have hT : 0 < T := by positivity
  set η' : ℝ := 1 / (2 * T) with hη'def
  have hη' : 0 < η' := by positivity
  set Sg : ℝ := ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)),
    (log p) ^ 2 with hSgdef
  obtain ⟨i10, e10⟩ := prime_meansq293 ε X l1 0 η' hη' h1
  obtain ⟨i1T, e1T⟩ := prime_meansq293 ε X l1 T η' hη' h1
  obtain ⟨i20, e20⟩ := prime_meansq293 ε X l2 0 η' hη' h2
  obtain ⟨i2T, e2T⟩ := prime_meansq293 ε X l2 T η' hη' h2
  let G : ℝ → ℝ := fun α => L ^ s * (2 *
    ((‖primeSum293 ε X (l1 * α)‖ ^ 2 * kernel293 η' (α - 0) +
      ‖primeSum293 ε X (l1 * α)‖ ^ 2 * kernel293 η' (α - T)) +
     (‖primeSum293 ε X (l2 * α)‖ ^ 2 * kernel293 η' (α - 0) +
      ‖primeSum293 ε X (l2 * α)‖ ^ 2 * kernel293 η' (α - T))))
  have hGi : Integrable G := (((i10.add i1T).add (i20.add i2T)).const_mul 2).const_mul (L ^ s)
  have hGint : ∫ α, G α = L ^ s * (4 / T) * Sg := by
    have : ∫ α, G α = L ^ s * (2 * ((η' * Sg + η' * Sg) + (η' * Sg + η' * Sg))) := by
      simp only [G]
      have hadd := integral_add (i10.add i1T) (i20.add i2T)
      simp only [Pi.add_apply] at hadd
      rw [integral_const_mul, integral_const_mul, hadd,
        integral_add i10 i1T, integral_add i20 i2T, e10, e1T, e20, e2T]
    rw [this, hη'def]
    field_simp
    ring
  have hGnn : ∀ α, 0 ≤ G α := by
    intro α
    have := kernel_nonneg293 η' (α - 0)
    have := kernel_nonneg293 η' (α - T)
    simp only [G]
    positivity
  have hN : ((Icc 1 ⌊L⌋₊).card : ℝ) ≤ L := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
    exact Nat.floor_le hL.le
  have hpt : ∀ α ∈ trivial293 X L, ‖integrand293 s l1 l2 μ γ η ε X α‖ ≤ G α := by
    intro α hα
    have hα' : T < |α| := trivial_mem293 X L α hα
    have hk := tail_kernel_le293 η T α hT hα'
    have hk0 := kernel_nonneg293 η α
    have hprod : ‖∏ i : Fin s, powerSum293 L (μ i * α)‖ ≤ L ^ s := by
      calc
        _ ≤ ∏ i : Fin s, ‖powerSum293 L (μ i * α)‖ := norm_prod_le _ _
        _ ≤ ∏ _ : Fin s, L := prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun i _ => (powerSum_norm_le293 _ _).trans hN)
        _ = _ := by simp
    have hnorm : ‖integrand293 s l1 l2 μ γ η ε X α‖ =
        ‖primeSum293 ε X (l1 * α)‖ * ‖primeSum293 ε X (l2 * α)‖ *
          ‖∏ i : Fin s, powerSum293 L (μ i * α)‖ * kernel293 η α := by
      simp only [integrand293, norm_mul, character_norm293, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hk0, ← hLdef]
    rw [hnorm]
    set x := ‖primeSum293 ε X (l1 * α)‖
    set y := ‖primeSum293 ε X (l2 * α)‖
    set pr := ‖∏ i : Fin s, powerSum293 L (μ i * α)‖
    have hx : 0 ≤ x := norm_nonneg _
    have hy : 0 ≤ y := norm_nonneg _
    have hpr : 0 ≤ pr := norm_nonneg _
    have hLs : 0 ≤ L ^ s := by positivity
    have hk' : 0 ≤ kernel293 η' α + kernel293 η' (α - T) :=
      add_nonneg (kernel_nonneg293 _ _) (kernel_nonneg293 _ _)
    have hxy : x * y ≤ (x ^ 2 + y ^ 2) / 2 := by nlinarith [sq_nonneg (x - y)]
    calc
      x * y * pr * kernel293 η α ≤ ((x ^ 2 + y ^ 2) / 2) * L ^ s *
          (4 * (kernel293 η' α + kernel293 η' (α - T))) :=
        mul_le_mul (mul_le_mul hxy hprod hpr (by positivity)) hk hk0 (by positivity)
      _ = G α := by
        simp only [G, sub_zero]
        ring
  have hfi : Integrable (integrand293 s l1 l2 μ γ η ε X) :=
    integrand_integrable293 s l1 l2 μ γ η ε X
  calc
    _ ≤ ∫ α in trivial293 X L, ‖integrand293 s l1 l2 μ γ η ε X α‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ α in trivial293 X L, G α :=
      setIntegral_mono_on hfi.norm.integrableOn hGi.integrableOn
        (trivial_measurable293 X L) hpt
    _ ≤ ∫ α, G α := setIntegral_le_integral hGi (Eventually.of_forall hGnn)
    _ = L ^ s * (4 / T) * Sg := hGint
    _ ≤ L ^ s * (4 / T) * (log 4 * X * log X) :=
      mul_le_mul_of_nonneg_left (prime_log_sq_sum_le293 ε X hX) (by positivity)

end TrivialSmall293

/-- LEAF. P0079 page 10, Section 5, display 17. The trivial arc is little o
of X times L to the power s. The tolerance is explicit. -/
theorem trivial_small293 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : l1 ≠ 0) (h2 : l2 ≠ 0) (hμ : ∀ i, μ i ≠ 0)
    (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in trivial293 X (cutoff293 s μ ε X), integrand293 s l1 l2 μ γ η ε X α‖ ≤
        δ * X * (cutoff293 s μ ε X) ^ s := by
  intro δ hδ
  have ha1 : 0 < |l1| := abs_pos.mpr h1
  have ha2 : 0 < |l2| := abs_pos.mpr h2
  set C : ℝ := max (max 1 (4 * log 4 / δ)) (max (1 / (2 * |l1|)) (1 / (2 * |l2|))) with hC
  have hC1 : 1 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCδ : 4 * log 4 / δ ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCl1 : 1 / (2 * |l1|) ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCl2 : 1 / (2 * |l2|) ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  filter_upwards [TrivialSmall293.cutoff_eventually293 s μ ε hs hμ hε C, eventually_ge_atTop 1]
    with X hX hX1
  obtain ⟨hCL, hCL2⟩ := hX
  set L := cutoff293 s μ ε X with hLdef
  have hL1 : 1 ≤ L := hC1.trans hCL
  have hL : 0 < L := by linarith
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hlogX : 0 ≤ log X := log_nonneg hX1
  have key : ∀ l : ℝ, 0 < |l| → 1 / (2 * |l|) ≤ C → 1 / (2 * L ^ 2) ≤ |l| := by
    intro l hl hCl
    have h3 : 1 / (2 * |l|) ≤ L ^ 2 := (hCl.trans hCL).trans hLL
    rw [div_le_iff₀ (by positivity)] at h3 ⊢
    nlinarith
  have hb := TrivialSmall293.trivial_bound293 s l1 l2 μ γ η ε X hX1 hL
    (key l1 ha1 hCl1) (key l2 ha2 hCl2)
  refine hb.trans ?_
  have h4 : 4 * log 4 * log X ≤ δ * L ^ 2 := by
    have h5 : 4 * log 4 / δ * log X ≤ L ^ 2 :=
      (mul_le_mul_of_nonneg_right hCδ hlogX).trans hCL2
    have h6 : δ * (4 * log 4 / δ * log X) ≤ δ * L ^ 2 := mul_le_mul_of_nonneg_left h5 hδ.le
    have h7 : δ * (4 * log 4 / δ * log X) = 4 * log 4 * log X := by field_simp
    linarith
  have hLs : 0 ≤ L ^ s := by positivity
  have hX0 : 0 ≤ X := by linarith
  have h8 : L ^ s * (4 / L ^ 2) * (log 4 * X * log X) =
      (4 * log 4 * log X) / L ^ 2 * (X * L ^ s) := by
    field_simp
  have h9 : (4 * log 4 * log X) / L ^ 2 ≤ δ := by
    rw [div_le_iff₀ (by positivity)]
    exact h4
  rw [h8]
  calc
    _ ≤ δ * (X * L ^ s) := mul_le_mul_of_nonneg_right h9 (by positivity)
    _ = _ := by ring

/-- LEAF. P0079 pages 11 to 12, displays 40 to 43 and their conclusions.
The two cases share the estimate. A positive tolerance absorbs the little o term.
This leaf does not assert display 19 or the disputed endpoint implication. -/
theorem minor_upper293 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : (ν = nuTr ∧ IsTr (l1 / l2)) ∨ (ν = nuAlg ∧ IsAlg (l1 / l2)))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in minor293 X (cutoff293 s μ ε X), integrand293 s l1 l2 μ γ η ε X α‖ ≤
        (ν ^ (s - 2) * Cq r1.den r2.den + δ) * η * X * (cutoff293 s μ ε X) ^ s := by
  sorry

end LeanLab.LZPowersOfTwo
