import LeanLab.ExceptionalSet.Decomp464j
import LeanLab.ExceptionalSet.Decomp404b

/-!
P0082 page367 after display31 and the following weighted coefficient identity.
The shifted kernel has its Fourier transform in the interval from minus one to zero.
The generic proved Poisson formula isolates the upper adjacent coefficient.
No exceptional count or odd moment estimate is asserted here.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.OddKernel467
open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (Kfun eC ftR hcheck norm_eC)
open LeanLab.ExceptionalSet.KernelTransform264 (weight)

/-- P0082 page367 after display31. The inverse transform of w_e is
one half times e of minus alpha divided by two times K at alpha divided by two. -/
noncomputable def evenKernel (Δ α : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (Kfun Δ ((1 / 2) * α) : ℂ) * eC (-((1 / 2) * α))

/-- P0082 page367 after display31. Dilation and a bounded exponential
phase preserve the integrability of the original kernel. -/
theorem evenKernel_integrable (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    Integrable (evenKernel Δ) := by
  have he : Continuous (fun α : ℝ => eC (-((1 / 2) * α))) := by unfold eC; fun_prop
  exact (((KernelTransform264.Kfun_integrable hΔ hΔ1).comp_mul_left'
    (by norm_num : (1 / 2 : ℝ) ≠ 0)).const_mul (1 / 2 : ℂ)).mul_bdd
      he.aestronglyMeasurable (Filter.Eventually.of_forall (fun α => (norm_eC _).le))

/-- P0082 page367 after display31. The shifted kernel is continuous. -/
theorem evenKernel_continuous (Δ : ℝ) : Continuous (evenKernel Δ) := by
  unfold evenKernel
  apply Continuous.mul
  · exact continuous_const.mul ((KernelTransform264.Kfun_continuous Δ).comp
      (continuous_const.mul continuous_id))
  · unfold eC
    fun_prop

/-- P0082 page367 display31 and its inverse transform calculation.
The transform of the shifted kernel is w of twice the frequency plus one. -/
theorem ftR_evenKernel (Δ y : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    ftR (evenKernel Δ) y = (weight Δ (2 * y + 1) : ℂ) := by
  let f : ℝ → ℂ := fun x => (Kfun Δ x : ℂ) * eC (-(x * 1))
  have he : evenKernel Δ = fun x => (1 / 2 : ℂ) * f ((1 / 2) * x) := by
    funext x
    dsimp [evenKernel, f]
    simp only [mul_one]
    ring
  have hs : FourierTransform.fourier (fun x => (1 / 2 : ℂ) * f ((1 / 2) * x)) y =
      (1 / 2 : ℂ) * FourierTransform.fourier (fun x => f ((1 / 2) * x)) y := by
    simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [Decomp404b.ftR_eq_fourier, he, hs,
    TriangleKernel264.fourier_comp_pos_mul f (by norm_num : (0 : ℝ) < 1 / 2)]
  dsimp only [f]
  rw [Decomp404b.fourier_modulated_kernel Δ 1 _ hΔ hΔ1]
  norm_num
  congr 1
  ring

/-- P0082 page367, use of Lemma1 with the shifted kernel. Its transform
vanishes outside the closed unit interval. In fact its support is smaller. -/
theorem evenKernel_transform_support (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    ∀ y : ℝ, 1 < |y| → ftR (evenKernel Δ) y = 0 := by
  intro y hy
  rw [ftR_evenKernel Δ y hΔ hΔ1]
  have hh : 1 ≤ |2 * y + 1| := by
    rw [le_abs]
    rcases lt_abs.mp hy with hy | hy
    · left
      linarith
    · right
      linarith
  rw [KernelTransform264.weight_zero hΔ hΔ1 hh]
  simp

/-- P0082 page367 final display. For any periodic integrable h, the
shifted kernel selects the upper adjacent Fourier coefficient with its weight. -/
theorem weighted_adjacent_identity (h : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (∫ α : ℝ, h α * evenKernel Δ α * eC (-(α * v))) =
      (weight Δ (2 * Int.fract v - 1) : ℂ) * hcheck h (⌊v⌋ + 1) := by
  have hmain := Decomp464j.lemma1_supplied h (evenKernel Δ) hper hh
    (evenKernel_integrable Δ hΔ hΔ1) (evenKernel_continuous Δ)
    (evenKernel_transform_support Δ hΔ hΔ1) v
  rw [ftR_evenKernel Δ (Int.fract v) hΔ hΔ1,
    ftR_evenKernel Δ (Int.fract v - 1) hΔ hΔ1] at hmain
  have hz : weight Δ (2 * Int.fract v + 1) = 0 := by
    apply KernelTransform264.weight_zero hΔ hΔ1
    rw [abs_of_nonneg (by linarith [Int.fract_nonneg v])]
    linarith [Int.fract_nonneg v]
  have he : 2 * (Int.fract v - 1) + 1 = 2 * Int.fract v - 1 := by ring
  simpa only [hz, Complex.ofReal_zero, zero_mul, zero_add, he] using hmain

/-- P0082 page367 final display and page368 boundary paragraph. In the
closed plateau range the weighted identity gives the adjacent coefficient itself. -/
theorem plateau_adjacent_identity (h : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hleft : Δ / 2 ≤ Int.fract v) (hright : Int.fract v ≤ 1 - Δ / 2) :
    (∫ α : ℝ, h α * evenKernel Δ α * eC (-(α * v))) = hcheck h (⌊v⌋ + 1) := by
  rw [weighted_adjacent_identity h hper hh Δ v hΔ hΔ1]
  have hplateau : |2 * Int.fract v - 1| ≤ 1 - Δ := by
    rw [abs_le]
    constructor <;> linarith
  rw [KernelTransform264.weight_one hΔ hΔ1 hplateau]
  simp

end LeanLab.ExceptionalSet.OddKernel467
