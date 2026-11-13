/-
P0070. A. Perelli and J. Pintz, On the exceptional set for the 2k-twin primes problem,
Compositio Math. 82, 1992, pp. 355 to 372, Section 5, p. 364: Gallagher's lemma,
P. X. Gallagher, A large sieve density estimate near σ = 1, Invent. Math. 11, 1970,
pp. 329 to 339, Lemma 1, in a finite form with complex coefficients.

ROUTE BURST session 9, 2026-11-12. COPIED WITH ATTRIBUTION, proofs unchanged up to renaming
of the namespace: the kernel and Fourier inputs are from `LeanLab/LZPowersOfTwo`, files
`Decomp293a`, `Decomp293b`, `KernelBounds293`, `FourierBox293`, `KernelFourier293`,
`CountBounds293`, `PrimeMoment353`, and the real-coefficient Gallagher lemma `gallagher_p2`
with its window lemmas is from `LZPowersOfTwo/Burst8Gallagher.lean` on the branch
`claude/LZPowersOfTwo-split-p2`, ROUTE BURST session 8. They are copied, not imported, so that
this folder does not depend on another paper's folder. New here: the complex form
`gallagher_complex`, from the real form applied to the real and imaginary parts.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import Mathlib

open Real Finset MeasureTheory Filter FourierTransform
open scoped Convolution
noncomputable section
namespace LeanLab.PerelliPintz1992.Burst9G

/-- The additive character `e(u) = exp(2πiu)`, `LZPowersOfTwo.character293`. -/
def character293 (u : ℝ) : ℂ := Complex.exp ((2 * Real.pi * u : ℝ) * Complex.I)

/-- The Fejér type kernel `(η sinc(πηα))²`, `LZPowersOfTwo.kernel293`. -/
def kernel293 (η α : ℝ) : ℝ := (η * Real.sinc (Real.pi * η * α)) ^ 2

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

/-- P0079 page 4, definition of the additive character. Addition of phases
is multiplication of characters. -/
theorem character_add293 (x y : ℝ) : character293 (x + y) = character293 x * character293 y := by
  unfold character293
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

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

/-- P0079 page 4, definition of e. Negating the phase conjugates the character. -/
theorem character_neg353 (u : ℝ) :
    character293 (-u) = starRingEnd ℂ (character293 u) := by
  unfold character293
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The window `{x : x < n ≤ x + h} = [n - h, n)`. -/
def win (h : ℝ) (n : ℕ) : Set ℝ := Set.Ico ((n : ℝ) - h) n

/-- Gallagher's window sum `C(x) = ∑_{x < n ≤ x + h} a_n`. -/
def winSum (T : Finset ℕ) (a : ℕ → ℝ) (h x : ℝ) : ℝ :=
  ∑ n ∈ T, (win h n).indicator (fun _ => a n) x

/-- The overlap of two windows has length `max(0, h - |m - n|)`. -/
theorem win_inter_p2 (h : ℝ) (hh : 0 < h) (m n : ℕ) :
    volume.real (win h m ∩ win h n) = max 0 (h - |(m : ℝ) - n|) := by
  unfold win
  rw [Set.Ico_inter_Ico, measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal', max_comm]
  congr 1
  rcases le_total (m : ℝ) n with hmn | hmn
  · rw [max_eq_right (by linarith), min_eq_left hmn, abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left (by linarith), min_eq_right hmn, abs_of_nonneg (by linarith)]; ring

/-- The square of a window sum is the double sum over overlapping windows. -/
theorem winSum_sq_p2 (T : Finset ℕ) (a : ℕ → ℝ) (h x : ℝ) :
    winSum T a h x ^ 2 =
      ∑ m ∈ T, ∑ n ∈ T, (win h m ∩ win h n).indicator (fun _ => a m * a n) x := by
  unfold winSum
  rw [sq, sum_mul_sum]
  apply sum_congr rfl; intro m _
  apply sum_congr rfl; intro n _
  by_cases hm : x ∈ win h m <;> by_cases hn : x ∈ win h n <;>
    simp [hm, hn, Set.indicator_of_mem, Set.indicator_of_notMem]

theorem winSum_sq_integral_p2 (T : Finset ℕ) (a : ℕ → ℝ) (h : ℝ) (hh : 0 < h) :
    Integrable (fun x => winSum T a h x ^ 2) ∧
    (∫ x : ℝ, winSum T a h x ^ 2) =
      ∑ m ∈ T, ∑ n ∈ T, a m * a n * max 0 (h - |(m : ℝ) - n|) := by
  have hmeas : ∀ m n : ℕ, MeasurableSet (win h m ∩ win h n) := fun m n =>
    measurableSet_Ico.inter measurableSet_Ico
  have hfin : ∀ m n : ℕ, volume (win h m ∩ win h n) ≠ ⊤ := fun m n =>
    ((measure_mono Set.inter_subset_left).trans_lt measure_Ico_lt_top).ne
  have hint : ∀ m n : ℕ, Integrable ((win h m ∩ win h n).indicator (fun _ => a m * a n)) :=
    fun m n => (integrable_indicator_iff (hmeas m n)).mpr
      (integrableOn_const (hfin m n))
  simp_rw [winSum_sq_p2]
  constructor
  · exact integrable_finsetSum _ (fun m _ => integrable_finsetSum _ (fun n _ => hint m n))
  rw [integral_finsetSum _ (fun m _ => integrable_finsetSum _ (fun n _ => hint m n))]
  apply sum_congr rfl; intro m _
  rw [integral_finsetSum _ (fun n _ => hint m n)]
  apply sum_congr rfl; intro n _
  rw [integral_indicator_const _ (hmeas m n), win_inter_p2 h hh, smul_eq_mul]
  ring

/-- The exponential sum `∑ a_n e(nα)`. -/
def expSum (T : Finset ℕ) (a : ℕ → ℝ) (α : ℝ) : ℂ :=
  ∑ n ∈ T, (a n : ℂ) * character293 ((n : ℝ) * α)

theorem expSum_sq_p2 (T : Finset ℕ) (a : ℕ → ℝ) (α : ℝ) :
    ((‖expSum T a α‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ T, ∑ n ∈ T, ((a m * a n : ℝ) : ℂ) * character293 (((m : ℝ) - n) * α) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  unfold expSum
  simp only [map_sum, map_mul, Complex.conj_ofReal]
  rw [sum_mul_sum]
  apply sum_congr rfl; intro m _
  apply sum_congr rfl; intro n _
  rw [← character_neg353, show ((m : ℝ) - n) * α = (m : ℝ) * α + -((n : ℝ) * α) by ring,
    character_add293]
  push_cast
  ring

/-- Gallagher's identity: `∫ |∑ a_n e(nα)|^2 K_h = ∫ C(x)^2 dx`. PROVED. -/
theorem gallagher_identity_p2 (T : Finset ℕ) (a : ℕ → ℝ) (h : ℝ) (hh : 0 < h) :
    (∫ α : ℝ, ‖expSum T a α‖ ^ 2 * kernel293 h α) = ∫ x : ℝ, winSum T a h x ^ 2 := by
  rw [(winSum_sq_integral_p2 T a h hh).2]
  let w : ℕ × ℕ → ℂ := fun x => ((a x.1 * a x.2 : ℝ) : ℂ)
  let φ : ℕ × ℕ → ℝ := fun x => (x.1 : ℝ) - x.2
  have key : ∀ α : ℝ, (((‖expSum T a α‖ ^ 2 * kernel293 h α : ℝ)) : ℂ) =
      (∑ x ∈ T ×ˢ T, w x * character293 (φ x * α)) * (kernel293 h α : ℂ) := by
    intro α
    rw [Complex.ofReal_mul, expSum_sq_p2]
    simp only [w, φ, sum_product]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [key]
  rw [finite_kernel_integral293 (T ×ˢ T) w φ h hh]
  simp only [w, φ, sum_product]
  push_cast
  rfl

/-- `sinc t ≥ 2/π` for `|t| ≤ π/2` (Jordan's inequality). -/
theorem sinc_ge_p2 (t : ℝ) (ht : |t| ≤ π / 2) : 2 / π ≤ Real.sinc t := by
  rcases eq_or_ne t 0 with h0 | h0
  · rw [h0, Real.sinc_zero, div_le_one pi_pos]; linarith [pi_gt_three]
  rw [Real.sinc_of_ne_zero h0]
  have key : ∀ u : ℝ, 0 < u → u ≤ π / 2 → 2 / π ≤ sin u / u := by
    intro u hu hu'
    rw [le_div_iff₀ hu]
    exact Real.mul_le_sin hu.le hu'
  rcases lt_or_gt_of_ne h0 with hn | hp
  · have := key (-t) (by linarith) (by rw [abs_of_neg hn] at ht; linarith)
    rwa [Real.sin_neg, neg_div_neg_eq] at this
  · exact key t hp (by rwa [abs_of_pos hp] at ht)

/-- `K_h(α) ≥ (2h/π)^2` for `|α| ≤ 1/(2h)`. -/
theorem kernel_ge_p2 (h α : ℝ) (hh : 0 < h) (hα : |α| ≤ 1 / (2 * h)) :
    (2 * h / π) ^ 2 ≤ kernel293 h α := by
  unfold kernel293
  have ht : |π * h * α| ≤ π / 2 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < π * h)]
    calc π * h * |α| ≤ π * h * (1 / (2 * h)) := by gcongr
      _ = π / 2 := by field_simp
  have hs := sinc_ge_p2 _ ht
  have h1 : 2 * h / π ≤ h * Real.sinc (π * h * α) := by
    calc 2 * h / π = h * (2 / π) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs hh.le
  exact pow_le_pow_left₀ (by positivity) h1 2

/-- Gallagher's lemma [5, Lemma 1], finite form: for `0 < Y`,
`∫_{-Y}^{Y} |∑ a_n e(nα)|^2 dα ≤ π^2 Y^2 ∫ |∑_{x < n ≤ x + 1/(2Y)} a_n|^2 dx`. PROVED. -/
theorem gallagher_p2 (T : Finset ℕ) (a : ℕ → ℝ) (Y : ℝ) (hY : 0 < Y) :
    (∫ α in (-Y)..Y, ‖expSum T a α‖ ^ 2) ≤
      π ^ 2 * Y ^ 2 * ∫ x : ℝ, winSum T a (1 / (2 * Y)) x ^ 2 := by
  set h := 1 / (2 * Y) with hh_def
  have hh : 0 < h := by positivity
  have hc : Continuous (fun α => ‖expSum T a α‖ ^ 2) := by
    unfold expSum character293; fun_prop
  have hK : Integrable (fun α => ‖expSum T a α‖ ^ 2 * kernel293 h α) := by
    let P := ∑ n ∈ T, |a n|
    apply (kernel_integrable293 h).bdd_mul (c := P ^ 2) hc.aestronglyMeasurable
    apply Eventually.of_forall; intro α
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    unfold expSum
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    apply sum_congr rfl; intro n _
    rw [norm_mul, character_norm293, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hYh : Y = 1 / (2 * h) := by rw [hh_def]; field_simp
  have hpt : ∀ α ∈ Set.Icc (-Y) Y, ‖expSum T a α‖ ^ 2 ≤
      (π / (2 * h)) ^ 2 * (‖expSum T a α‖ ^ 2 * kernel293 h α) := by
    intro α hα
    have hα' : |α| ≤ 1 / (2 * h) := by rw [← hYh]; exact abs_le.mpr hα
    have hk := kernel_ge_p2 h α hh hα'
    have e : (π / (2 * h)) ^ 2 * (2 * h / π) ^ 2 = 1 := by field_simp
    have hn : 0 ≤ ‖expSum T a α‖ ^ 2 := sq_nonneg _
    calc ‖expSum T a α‖ ^ 2 = (π / (2 * h)) ^ 2 * (2 * h / π) ^ 2 * ‖expSum T a α‖ ^ 2 := by
          rw [e, one_mul]
      _ ≤ (π / (2 * h)) ^ 2 * kernel293 h α * ‖expSum T a α‖ ^ 2 := by gcongr
      _ = _ := by ring
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  calc (∫ α in Set.Icc (-Y) Y, ‖expSum T a α‖ ^ 2)
      ≤ ∫ α in Set.Icc (-Y) Y, (π / (2 * h)) ^ 2 * (‖expSum T a α‖ ^ 2 * kernel293 h α) :=
        setIntegral_mono_on (hc.integrableOn_Icc) (hK.const_mul _).integrableOn
          measurableSet_Icc hpt
    _ ≤ ∫ α : ℝ, (π / (2 * h)) ^ 2 * (‖expSum T a α‖ ^ 2 * kernel293 h α) :=
        setIntegral_le_integral (hK.const_mul _) (Eventually.of_forall (fun α =>
          mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (kernel_nonneg293 h α))))
    _ = (π / (2 * h)) ^ 2 * ∫ α : ℝ, ‖expSum T a α‖ ^ 2 * kernel293 h α := integral_const_mul _ _
    _ = π ^ 2 * Y ^ 2 * ∫ x : ℝ, winSum T a h x ^ 2 := by
        rw [gallagher_identity_p2 T a h hh, hYh]; field_simp


/-! ### The complex form, new in burst 9 -/

/-- The complex window sum `Σ_{x < n ≤ x + h} c_n`. -/
def cwinSum (T : Finset ℕ) (c : ℕ → ℂ) (h x : ℝ) : ℂ :=
  ∑ n ∈ T, (win h n).indicator (fun _ => c n) x

/-- The complex exponential sum `Σ c_n e(nα)`. -/
def cexpSum (T : Finset ℕ) (c : ℕ → ℂ) (α : ℝ) : ℂ :=
  ∑ n ∈ T, c n * character293 ((n : ℝ) * α)

theorem cexpSum_eq (T : Finset ℕ) (c : ℕ → ℂ) (α : ℝ) :
    cexpSum T c α = expSum T (fun n => (c n).re) α +
      Complex.I * expSum T (fun n => (c n).im) α := by
  unfold cexpSum expSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  conv_lhs => rw [← Complex.re_add_im (c n)]
  ring

theorem cwinSum_re (T : Finset ℕ) (c : ℕ → ℂ) (h x : ℝ) :
    (cwinSum T c h x).re = winSum T (fun n => (c n).re) h x := by
  unfold cwinSum winSum
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hx : x ∈ win h n <;> simp [hx]

theorem cwinSum_im (T : Finset ℕ) (c : ℕ → ℂ) (h x : ℝ) :
    (cwinSum T c h x).im = winSum T (fun n => (c n).im) h x := by
  unfold cwinSum winSum
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hx : x ∈ win h n <;> simp [hx]

theorem norm_cwinSum_sq (T : Finset ℕ) (c : ℕ → ℂ) (h x : ℝ) :
    ‖cwinSum T c h x‖ ^ 2 =
      winSum T (fun n => (c n).re) h x ^ 2 + winSum T (fun n => (c n).im) h x ^ 2 := by
  rw [← cwinSum_re, ← cwinSum_im, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem norm_add_I_mul_sq_le (u v : ℂ) :
    ‖u + Complex.I * v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h1 : ‖u + Complex.I * v‖ ≤ ‖u‖ + ‖v‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
  have h0 : 0 ≤ ‖u + Complex.I * v‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖u‖ - ‖v‖), norm_nonneg u, norm_nonneg v]

/-- The complex window sum is square integrable, and its square integral is the sum of those of
its real and imaginary parts. -/
theorem cwinSum_sq_integrable (T : Finset ℕ) (c : ℕ → ℂ) (h : ℝ) (hh : 0 < h) :
    Integrable (fun x => ‖cwinSum T c h x‖ ^ 2) := by
  simp_rw [norm_cwinSum_sq]
  exact (winSum_sq_integral_p2 T _ h hh).1.add (winSum_sq_integral_p2 T _ h hh).1

/-- **Gallagher's lemma, complex finite form**, Invent. Math. 11, 1970, Lemma 1, as used on
p. 364 of P0070: for `0 < Y`,
`∫_{-Y}^{Y} |Σ c_n e(nα)|² dα ≤ 2π² Y² ∫ |Σ_{x < n ≤ x + 1/(2Y)} c_n|² dx`.
From `gallagher_p2` for the real and imaginary parts. PROVED. -/
theorem gallagher_complex (T : Finset ℕ) (c : ℕ → ℂ) (Y : ℝ) (hY : 0 < Y) :
    (∫ α in (-Y)..Y, ‖cexpSum T c α‖ ^ 2) ≤
      2 * π ^ 2 * Y ^ 2 * ∫ x : ℝ, ‖cwinSum T c (1 / (2 * Y)) x‖ ^ 2 := by
  set a1 : ℕ → ℝ := fun n => (c n).re
  set a2 : ℕ → ℝ := fun n => (c n).im
  have hh : 0 < 1 / (2 * Y) := by positivity
  have hc1 : Continuous (fun α => ‖expSum T a1 α‖ ^ 2) := by
    unfold expSum character293; fun_prop
  have hc2 : Continuous (fun α => ‖expSum T a2 α‖ ^ 2) := by
    unfold expSum character293; fun_prop
  have hc : Continuous (fun α => ‖cexpSum T c α‖ ^ 2) := by
    unfold cexpSum character293; fun_prop
  have hYY : -Y ≤ Y := by linarith
  have step1 : (∫ α in (-Y)..Y, ‖cexpSum T c α‖ ^ 2) ≤
      ∫ α in (-Y)..Y, (2 * ‖expSum T a1 α‖ ^ 2 + 2 * ‖expSum T a2 α‖ ^ 2) := by
    refine intervalIntegral.integral_mono_on hYY (hc.intervalIntegrable _ _)
      (((continuous_const.mul hc1).add (continuous_const.mul hc2)).intervalIntegrable _ _) ?_
    intro α _
    rw [cexpSum_eq]
    exact norm_add_I_mul_sq_le _ _
  have hsplit : (∫ α in (-Y)..Y, (2 * ‖expSum T a1 α‖ ^ 2 + 2 * ‖expSum T a2 α‖ ^ 2)) =
      2 * (∫ α in (-Y)..Y, ‖expSum T a1 α‖ ^ 2) +
        2 * ∫ α in (-Y)..Y, ‖expSum T a2 α‖ ^ 2 := by
    have i1 : IntervalIntegrable (fun α => 2 * ‖expSum T a1 α‖ ^ 2) volume (-Y) Y :=
      (continuous_const.mul hc1).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun α => 2 * ‖expSum T a2 α‖ ^ 2) volume (-Y) Y :=
      (continuous_const.mul hc2).intervalIntegrable _ _
    rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have g1 := gallagher_p2 T a1 Y hY
  have g2 := gallagher_p2 T a2 Y hY
  have hI : (∫ x : ℝ, ‖cwinSum T c (1 / (2 * Y)) x‖ ^ 2) =
      (∫ x : ℝ, winSum T a1 (1 / (2 * Y)) x ^ 2) + ∫ x : ℝ, winSum T a2 (1 / (2 * Y)) x ^ 2 := by
    simp_rw [norm_cwinSum_sq]
    exact integral_add (winSum_sq_integral_p2 T _ _ hh).1 (winSum_sq_integral_p2 T _ _ hh).1
  rw [hI]
  have hp : 0 ≤ π ^ 2 * Y ^ 2 := by positivity
  nlinarith

#print axioms kernel_transform293
#print axioms gallagher_p2
#print axioms cwinSum_sq_integrable
#print axioms gallagher_complex

end LeanLab.PerelliPintz1992.Burst9G
