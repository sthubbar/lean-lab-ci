/-
P0088 page 7 display 29 on translated blocks of the n variable.
The windows remain anchored at X. Only the geometric sum interval is shifted.
The proof follows Eq33RouteA.minor_mean_square_core with that interval separated.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Eq33RouteA

namespace LeanLab.KumchevLiu2007.Task628

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d
open LeanLab.PNTPort.LargeSieve
open scoped BigOperators Topology

/-- Page 7 display 29, derived block version. The prime and rough sums keep
windows anchored at X. The n sum starts at any nonnegative X'. The same
kernel majorant M gives the same constant four. -/
theorem minor_mean_square_shifted {X X' Y H P M : ℝ} (hX' : 0 ≤ X') (hXY : 0 ≤ X - Y)
    (hY : 1 ≤ Y) (hH : 1 ≤ H) (hM : 0 ≤ M)
    (hmass : ∀ β ∈ Set.Icc (0 : ℝ) 1, kernelMass Y H P β ≤ M) :
    (∑ n ∈ intervalNumbers X' H, ‖minorCoefficient X Y H P n‖ ^ 2) ≤
      4 * Y * M := by
  have hH0 : 0 < H := by linarith
  have hsm : MeasurableSet (Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H P)ᶜ) :=
    measurableSet_Ioc.inter (measurableSet_majorArcs H P).compl
  obtain ⟨s, hs⟩ : ∃ s : Set ℝ, s = Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H P)ᶜ :=
    ⟨_, rfl⟩
  rw [← hs] at hsm
  have hsub : s ⊆ Set.Ioc (0 : ℝ) 1 := hs ▸ Set.inter_subset_left
  have hsIcc : ∀ α ∈ s, α ∈ Set.Icc (0 : ℝ) 1 := fun α hα =>
    ⟨(hsub hα).1.le, (hsub hα).2⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure ℝ, μ = volume.restrict s := ⟨_, rfl⟩
  have hfin : IsFiniteMeasure μ := by
    rw [hμ]
    exact ⟨by
      rw [Measure.restrict_apply_univ]
      exact (measure_mono hsub).trans_lt (by simp)⟩
  have hciC : ∀ f : ℝ → ℂ, Continuous f → Integrable f μ := fun f hf => by
    rw [hμ]
    exact (hf.integrableOn_Ioc (μ := volume) (a := 0) (b := 1)).mono_set hsub
  have hciR : ∀ f : ℝ → ℝ, Continuous f → Integrable f μ := fun f hf => by
    rw [hμ]
    exact (hf.integrableOn_Ioc (μ := volume) (a := 0) (b := 1)).mono_set hsub
  have hae : ∀ p : ℝ → Prop, (∀ α ∈ s, p α) → ∀ᵐ α ∂μ, p α := fun p hp => by
    rw [hμ]
    exact ae_restrict_of_forall_mem hsm hp
  -- the exponential sums and the kernel
  have hS1c : Continuous (fun α : ℝ => primeSum X Y α) := by
    unfold primeSum
    exact continuous_finsetSum _ fun m _ =>
      (fourier (m : ℤ)).continuous.comp (AddCircle.continuous_mk' 1)
  have hS2c : Continuous (fun α : ℝ => roughSum Y P α) := by
    unfold roughSum
    exact continuous_finsetSum _ fun m _ => continuous_const.mul
      ((fourier ((m ^ 2 : ℕ) : ℤ)).continuous.comp (AddCircle.continuous_mk' 1))
  have hFc := continuous_representationPolynomial X Y P
  have hFeq : ∀ α : ℝ, representationPolynomial X Y P (α : AddCircle (1 : ℝ)) =
      primeSum X Y α * roughSum Y P α :=
    representationPolynomial_eq_prime_mul_rough X Y P
  have hkc : Continuous (fun p : ℝ × ℝ => shortKernel H p.1 p.2) := by
    unfold shortKernel
    refine Continuous.inv₀ ?_ ?_
    · exact continuous_const.max
        (((AddCircle.continuous_mk' 1).comp continuous_fst).dist
          ((AddCircle.continuous_mk' 1).comp continuous_snd))
    · intro p
      exact (lt_max_of_lt_left (inv_pos.mpr hH0)).ne'
  have hk0 : ∀ α β : ℝ, 0 ≤ shortKernel H α β := fun α β =>
    shortKernel_nonneg hH0 α β
  have hksymm : ∀ α β : ℝ, shortKernel H α β = shortKernel H β α := fun α β => by
    unfold shortKernel
    rw [dist_comm]
  have hf1c : Continuous (fun α : ℝ => ‖primeSum X Y α‖ ^ 2) := hS1c.norm.pow 2
  have hf2c : Continuous (fun α : ℝ => ‖roughSum Y P α‖ ^ 2) := hS2c.norm.pow 2
  have hf1i := hciR _ hf1c
  have hkm : ∀ β : ℝ, kernelMass Y H P β =
      ∫ α, ‖roughSum Y P α‖ ^ 2 * shortKernel H α β ∂μ := fun β => by
    rw [hμ, hs]
    rfl
  have hkm0 : ∀ β : ℝ, 0 ≤ kernelMass Y H P β := fun β => by
    rw [hkm]
    exact integral_nonneg fun α => mul_nonneg (sq_nonneg _) (hk0 α β)
  -- the integrand of the minor coefficient
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ → ℂ, g = fun (n : ℕ) (α : ℝ) =>
      fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
        representationPolynomial X Y P (α : AddCircle (1 : ℝ)) := ⟨_, rfl⟩
  have hgc : ∀ n, Continuous (g n) := fun n => by
    rw [hg]
    exact ((fourier (-(n : ℤ))).continuous.comp (AddCircle.continuous_mk' 1)).mul hFc
  have hc : ∀ n, minorCoefficient X Y H P n = ∫ α, g n α ∂μ := fun n => by
    rw [hg, hμ, hs]
    rfl
  -- the kernel from the sum over n
  obtain ⟨D, hD⟩ : ∃ D : ℝ → ℝ → ℂ, D = fun (α β : ℝ) =>
      ∑ n ∈ intervalNumbers X' H,
        fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
          (starRingEnd ℂ) (fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ))) := ⟨_, rfl⟩
  have hDle : ∀ α β, ‖D α β‖ ≤ 2 * shortKernel H α β := fun α β => by
    rw [hD]
    exact Eq33RouteA.interval_kernel_le_shortKernel hX' hH α β
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ → ℂ, G = fun (α β : ℝ) =>
      representationPolynomial X Y P (α : AddCircle (1 : ℝ)) *
        (starRingEnd ℂ) (representationPolynomial X Y P (β : AddCircle (1 : ℝ))) *
          D α β := ⟨_, rfl⟩
  have hgg : ∀ α β, ∑ n ∈ intervalNumbers X' H, g n α * (starRingEnd ℂ) (g n β) =
      G α β := by
    intro α β
    rw [hg, hG, hD]
    simp only [map_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  -- expansion of the square, first line of display 29
  have hTC : ((∑ n ∈ intervalNumbers X' H,
      ‖minorCoefficient X Y H P n‖ ^ 2 : ℝ) : ℂ) = ∫ α, ∫ β, G α β ∂μ ∂μ := by
    simp_rw [← hgg]
    have h1 : ∀ α, ∫ β, ∑ n ∈ intervalNumbers X' H,
        g n α * (starRingEnd ℂ) (g n β) ∂μ =
        ∑ n ∈ intervalNumbers X' H,
          g n α * (starRingEnd ℂ) (∫ β, g n β ∂μ) := by
      intro α
      have hint : ∀ n ∈ intervalNumbers X' H,
          Integrable (fun β : ℝ => g n α * (starRingEnd ℂ) (g n β)) μ := fun n _ =>
        (hciC _ (Complex.continuous_conj.comp (hgc n))).const_mul _
      rw [integral_finsetSum _ hint]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [integral_const_mul, integral_conj]
    simp_rw [h1]
    have hint : ∀ n ∈ intervalNumbers X' H, Integrable (fun α : ℝ =>
        g n α * (starRingEnd ℂ) (∫ β, g n β ∂μ)) μ := fun n _ =>
      (hciC _ (hgc n)).mul_const _
    rw [integral_finsetSum _ hint]
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_mul_const, ← hc n, Complex.mul_conj']
  -- arithmetic and geometric mean inequality, second line of display 29
  have hpt : ∀ α β, ‖G α β‖ ≤
      ‖primeSum X Y α‖ ^ 2 * (‖roughSum Y P β‖ ^ 2 * shortKernel H β α) +
        ‖roughSum Y P α‖ ^ 2 * (‖primeSum X Y β‖ ^ 2 * shortKernel H α β) := by
    intro α β
    rw [hG]
    show ‖representationPolynomial X Y P (α : AddCircle (1 : ℝ)) *
        (starRingEnd ℂ) (representationPolynomial X Y P (β : AddCircle (1 : ℝ))) *
          D α β‖ ≤ _
    rw [norm_mul, norm_mul, RCLike.norm_conj, hFeq α, hFeq β, norm_mul, norm_mul,
      hksymm β α]
    have hd := hDle α β
    have hk := hk0 α β
    have hsq := mul_nonneg (sq_nonneg (‖primeSum X Y α‖ * ‖roughSum Y P β‖ -
      ‖roughSum Y P α‖ * ‖primeSum X Y β‖)) hk
    have hprod : 0 ≤ ‖primeSum X Y α‖ * ‖roughSum Y P α‖ *
        (‖primeSum X Y β‖ * ‖roughSum Y P β‖) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hd hprod]
  have hPhi : ∀ α ∈ s, ‖∫ β, G α β ∂μ‖ ≤ ‖primeSum X Y α‖ ^ 2 * M +
      ∫ β, ‖roughSum Y P α‖ ^ 2 * (‖primeSum X Y β‖ ^ 2 * shortKernel H α β) ∂μ := by
    intro α hα
    have hi1 : Integrable (fun β : ℝ =>
        ‖primeSum X Y α‖ ^ 2 * (‖roughSum Y P β‖ ^ 2 * shortKernel H β α)) μ :=
      (hciR _ (hf2c.mul (hkc.comp (continuous_id.prodMk continuous_const)))).const_mul _
    have hi2 : Integrable (fun β : ℝ =>
        ‖roughSum Y P α‖ ^ 2 * (‖primeSum X Y β‖ ^ 2 * shortKernel H α β)) μ :=
      (hciR _ (hf1c.mul (hkc.comp (continuous_const.prodMk continuous_id)))).const_mul _
    have hi12 : Integrable (fun β : ℝ =>
        ‖primeSum X Y α‖ ^ 2 * (‖roughSum Y P β‖ ^ 2 * shortKernel H β α) +
        ‖roughSum Y P α‖ ^ 2 * (‖primeSum X Y β‖ ^ 2 * shortKernel H α β)) μ :=
      hi1.add hi2
    have h := norm_integral_le_of_norm_le hi12 (Filter.Eventually.of_forall (hpt α))
    rw [integral_add hi1 hi2, integral_const_mul (‖primeSum X Y α‖ ^ 2)
      (fun β : ℝ => ‖roughSum Y P β‖ ^ 2 * shortKernel H β α), ← hkm α] at h
    have h2 := mul_le_mul_of_nonneg_left (hmass α (hsIcc α hα))
      (sq_nonneg ‖primeSum X Y α‖)
    linarith
  -- joint integrability for the exchange of the two integrals
  have hji : Integrable (Function.uncurry fun α β : ℝ =>
      ‖roughSum Y P α‖ ^ 2 * (‖primeSum X Y β‖ ^ 2 * shortKernel H α β))
      (μ.prod μ) := by
    have hcont : Continuous (Function.uncurry fun α β : ℝ =>
        ‖roughSum Y P α‖ ^ 2 * (‖primeSum X Y β‖ ^ 2 * shortKernel H α β)) :=
      (hf2c.comp continuous_fst).mul ((hf1c.comp continuous_snd).mul hkc)
    rw [hμ, Measure.prod_restrict]
    exact (hcont.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono (fun α hα => hsIcc α hα) (fun α hα => hsIcc α hα))
  have hjl : Integrable (fun α : ℝ => ∫ β,
      ‖roughSum Y P α‖ ^ 2 * (‖primeSum X Y β‖ ^ 2 * shortKernel H α β) ∂μ) μ :=
    hji.integral_prod_left
  have hRi : Integrable (fun α : ℝ => ‖primeSum X Y α‖ ^ 2 * M + ∫ β,
      ‖roughSum Y P α‖ ^ 2 * (‖primeSum X Y β‖ ^ 2 * shortKernel H α β) ∂μ) μ :=
    (hf1i.mul_const M).add hjl
  have hmain : ‖∫ α, ∫ β, G α β ∂μ ∂μ‖ ≤
      ∫ α, (‖primeSum X Y α‖ ^ 2 * M + ∫ β,
        ‖roughSum Y P α‖ ^ 2 * (‖primeSum X Y β‖ ^ 2 * shortKernel H α β) ∂μ) ∂μ := by
    refine (norm_integral_le_integral_norm _).trans ?_
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun α => norm_nonneg _)
      hRi (hae _ hPhi)
  -- exchange of the integrals, third line of display 29
  have hswap : ∫ α, ∫ β,
      ‖roughSum Y P α‖ ^ 2 * (‖primeSum X Y β‖ ^ 2 * shortKernel H α β) ∂μ ∂μ =
      ∫ β, ‖primeSum X Y β‖ ^ 2 * kernelMass Y H P β ∂μ := by
    rw [integral_integral_swap hji]
    refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
    show ∫ α, ‖roughSum Y P α‖ ^ 2 * (‖primeSum X Y β‖ ^ 2 * shortKernel H α β) ∂μ =
      ‖primeSum X Y β‖ ^ 2 * kernelMass Y H P β
    rw [hkm β, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
    beta_reduce
    ring
  have hsecond : ∫ β, ‖primeSum X Y β‖ ^ 2 * kernelMass Y H P β ∂μ ≤
      ∫ β, ‖primeSum X Y β‖ ^ 2 * M ∂μ := by
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun β => mul_nonneg (sq_nonneg _) (hkm0 β))
      (hf1i.mul_const M) (hae _ fun β hβ => ?_)
    exact mul_le_mul_of_nonneg_left (hmass β (hsIcc β hβ)) (sq_nonneg _)
  -- the prime Parseval bound, page 5 display 17
  have hI1 : ∫ α, ‖primeSum X Y α‖ ^ 2 ∂μ ≤ 2 * Y := by
    have h01 := primeSum_parseval_le (X := X) (Y := Y) hXY hY
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h01
    refine le_trans ?_ h01
    rw [hμ]
    exact setIntegral_mono_set (hf1c.integrableOn_Ioc)
      (Filter.Eventually.of_forall fun α => sq_nonneg _) hsub.eventuallyLE
  have hT0 : 0 ≤ ∑ n ∈ intervalNumbers X' H, ‖minorCoefficient X Y H P n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => sq_nonneg _
  have hnorm : ∑ n ∈ intervalNumbers X' H, ‖minorCoefficient X Y H P n‖ ^ 2 =
      ‖∫ α, ∫ β, G α β ∂μ ∂μ‖ := by
    rw [← hTC, Complex.norm_of_nonneg hT0]
  rw [integral_add (hf1i.mul_const M) hjl, hswap,
    integral_mul_const M (fun α : ℝ => ‖primeSum X Y α‖ ^ 2)] at hmain
  rw [integral_mul_const M (fun α : ℝ => ‖primeSum X Y α‖ ^ 2)] at hsecond
  rw [hnorm]
  have hIM := mul_le_mul_of_nonneg_right hI1 hM
  linarith


end LeanLab.KumchevLiu2007.Task628

#print axioms LeanLab.KumchevLiu2007.Task628.minor_mean_square_shifted
