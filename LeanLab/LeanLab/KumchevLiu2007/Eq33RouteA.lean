/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 7, the well known bound
before display 29 and display 29 itself, with the prime Parseval bound of
page 5 display 17.

This file proves the statement of Task556d.minor_mean_square_of_kernel under
the name minor_mean_square_of_kernel_route. The steps are those of the paper:
expand the square of the minor coefficient, sum the geometric series over the
interval of length H, bound the kernel by min of H and the inverse circle
distance, use the arithmetic and geometric mean inequality inside the double
integral, and finish with I1 at most 2 Y.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp556d

namespace LeanLab.KumchevLiu2007.Eq33RouteA

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d
open LeanLab.PNTPort.LargeSieve
open scoped BigOperators Topology

/-- P0088 page 7, inside the well known bound before display 29: the sine
is at least twice the distance to the nearest integer. -/
theorem two_mul_abs_sub_round_le_abs_sin (θ : ℝ) :
    2 * |θ - round θ| ≤ |Real.sin (π * θ)| := by
  have ht : |θ - round θ| ≤ 1 / 2 := abs_sub_round θ
  have hs : Real.sin (π * θ) =
      (-1) ^ (round θ) * Real.sin (π * (θ - round θ)) := by
    have h : π * θ = π * (θ - round θ) + (round θ : ℤ) * π := by ring
    rw [h, Real.sin_add_int_mul_pi]
  rw [hs, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  have hpi := Real.pi_pos
  have habs : |π * (θ - round θ)| = π * |θ - round θ| := by
    rw [abs_mul, abs_of_pos hpi]
  have hle : π * |θ - round θ| ≤ π / 2 := by nlinarith
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by rw [habs]; linarith), habs]
  have h := Real.mul_le_sin (x := π * |θ - round θ|) (by positivity) hle
  have h2 : 2 / π * (π * |θ - round θ|) = 2 * |θ - round θ| := by
    field_simp
  linarith

/-- P0088 page 7, the well known bound before display 29, inverse distance
part: the exponential sum over a block of consecutive integers times the
distance of the frequency to the nearest integer is at most one half. -/
theorem interval_exponential_sum_mul_dist_le (a b : ℕ) (hab : a ≤ b) (θ : ℝ) :
    ‖∑ n ∈ Finset.Ioc a b, e (n * θ)‖ * |θ - round θ| ≤ 1 / 2 := by
  have hgeom : (∑ n ∈ Finset.Ioc a b, e (n * θ)) * (e θ - 1) =
      e θ ^ (b + 1) - e θ ^ (a + 1) := by
    simp_rw [e_nat_mul]
    rw [← Finset.Ico_add_one_add_one_eq_Ioc]
    exact geom_sum_Ico_mul _ (by omega)
  have h1 : ‖∑ n ∈ Finset.Ioc a b, e (n * θ)‖ * ‖e θ - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    calc
      _ ≤ ‖e θ ^ (b + 1)‖ + ‖e θ ^ (a + 1)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_pow, norm_e, one_pow, one_pow]; norm_num
  have h2 : 4 * |θ - round θ| ≤ ‖e θ - 1‖ := by
    rw [LeanLab.PNTPort.Gallagher.norm_e_sub_one]
    linarith [two_mul_abs_sub_round_le_abs_sin θ]
  have h3 := mul_le_mul_of_nonneg_left h2
    (norm_nonneg (∑ n ∈ Finset.Ioc a b, e (n * θ)))
  linarith

/-- P0088 page 7 display 29: the circle distance of two real points is the
distance of their difference to the nearest integer. -/
theorem dist_addCircle_eq_abs_sub_round (α β : ℝ) :
    dist (α : AddCircle (1 : ℝ)) (β : AddCircle (1 : ℝ)) =
      |(α - β) - round (α - β)| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq]
  simp

/-- P0088 page 8 display 33: the integers of the mean square form the block
of consecutive integers above the floor of X. -/
theorem intervalNumbers_eq_Ioc_floor {X H : ℝ} (hX : 0 ≤ X) :
    intervalNumbers X H = Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊ := by
  ext n
  simp only [intervalNumbers, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  rw [Nat.lt_succ_iff, ← Nat.floor_lt hX]
  tauto

/-- P0088 page 7, the well known bound before display 29, in the form used
in display 29: the kernel obtained by summing the geometric series over the
interval of length H is at most twice the short kernel, that is twice the
minimum of H and the inverse circle distance. -/
theorem interval_kernel_le_shortKernel {X H : ℝ} (hX : 0 ≤ X) (hH : 1 ≤ H)
    (α β : ℝ) :
    ‖∑ n ∈ intervalNumbers X H,
        fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
          (starRingEnd ℂ) (fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)))‖ ≤
      2 * shortKernel H α β := by
  have hH0 : 0 < H := by linarith
  have hterm : ∀ n : ℕ, fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
      (starRingEnd ℂ) (fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ))) =
        e (n * (β - α)) := by
    intro n
    rw [fourier_neg, fourier_neg, Complex.conj_conj, fourier_nat_eq_e,
      fourier_nat_eq_e, ← e_neg, ← e_add]
    congr 1
    ring
  simp_rw [hterm]
  rw [intervalNumbers_eq_Ioc_floor hX]
  have hab : ⌊X⌋₊ ≤ ⌊X + H⌋₊ := Nat.floor_mono (by linarith)
  have hgeo := interval_exponential_sum_mul_dist_le ⌊X⌋₊ ⌊X + H⌋₊ hab (β - α)
  rw [← dist_addCircle_eq_abs_sub_round β α, dist_comm] at hgeo
  have hcard : ‖∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊, e (n * (β - α))‖ ≤ 2 * H := by
    calc
      _ ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊, ‖e ((n : ℝ) * (β - α))‖ :=
        norm_sum_le _ _
      _ = ((⌊X + H⌋₊ : ℝ) - ⌊X⌋₊) := by
        simp only [norm_e, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
        rw [Nat.cast_sub hab]
      _ ≤ 2 * H := by
        have hb := Nat.floor_le (by linarith : 0 ≤ X + H)
        have ha := Nat.lt_floor_add_one X
        linarith
  have hS := norm_nonneg (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊, e (n * (β - α)))
  have hm : 0 < max H⁻¹ (dist (α : AddCircle (1 : ℝ)) (β : AddCircle (1 : ℝ))) :=
    lt_max_of_lt_left (inv_pos.mpr hH0)
  unfold shortKernel
  rw [← div_eq_mul_inv, le_div_iff₀ hm]
  rcases max_choice H⁻¹ (dist (α : AddCircle (1 : ℝ)) (β : AddCircle (1 : ℝ)))
    with h | h
  · rw [h, ← div_eq_mul_inv, div_le_iff₀ hH0]
    exact hcard
  · rw [h]
    linarith

/-- P0088 page 7 display 29 with the prime Parseval bound of page 5 display
17, for general parameters. Expand the square, sum the geometric series,
apply the arithmetic and geometric mean inequality inside the double integral
and bound I1 by 2 Y. -/
theorem minor_mean_square_core {X Y H P M : ℝ} (hX : 0 ≤ X) (hXY : 0 ≤ X - Y)
    (hY : 1 ≤ Y) (hH : 1 ≤ H) (hM : 0 ≤ M)
    (hmass : ∀ β ∈ Set.Icc (0 : ℝ) 1, kernelMass Y H P β ≤ M) :
    (∑ n ∈ intervalNumbers X H, ‖minorCoefficient X Y H P n‖ ^ 2) ≤
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
      ∑ n ∈ intervalNumbers X H,
        fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
          (starRingEnd ℂ) (fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ))) := ⟨_, rfl⟩
  have hDle : ∀ α β, ‖D α β‖ ≤ 2 * shortKernel H α β := fun α β => by
    rw [hD]
    exact interval_kernel_le_shortKernel hX hH α β
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ → ℂ, G = fun (α β : ℝ) =>
      representationPolynomial X Y P (α : AddCircle (1 : ℝ)) *
        (starRingEnd ℂ) (representationPolynomial X Y P (β : AddCircle (1 : ℝ))) *
          D α β := ⟨_, rfl⟩
  have hgg : ∀ α β, ∑ n ∈ intervalNumbers X H, g n α * (starRingEnd ℂ) (g n β) =
      G α β := by
    intro α β
    rw [hg, hG, hD]
    simp only [map_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  -- expansion of the square, first line of display 29
  have hTC : ((∑ n ∈ intervalNumbers X H,
      ‖minorCoefficient X Y H P n‖ ^ 2 : ℝ) : ℂ) = ∫ α, ∫ β, G α β ∂μ ∂μ := by
    simp_rw [← hgg]
    have h1 : ∀ α, ∫ β, ∑ n ∈ intervalNumbers X H,
        g n α * (starRingEnd ℂ) (g n β) ∂μ =
        ∑ n ∈ intervalNumbers X H,
          g n α * (starRingEnd ℂ) (∫ β, g n β ∂μ) := by
      intro α
      have hint : ∀ n ∈ intervalNumbers X H,
          Integrable (fun β : ℝ => g n α * (starRingEnd ℂ) (g n β)) μ := fun n _ =>
        (hciC _ (Complex.continuous_conj.comp (hgc n))).const_mul _
      rw [integral_finsetSum _ hint]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [integral_const_mul, integral_conj]
    simp_rw [h1]
    have hint : ∀ n ∈ intervalNumbers X H, Integrable (fun α : ℝ =>
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
  have hT0 : 0 ≤ ∑ n ∈ intervalNumbers X H, ‖minorCoefficient X Y H P n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => sq_nonneg _
  have hnorm : ∑ n ∈ intervalNumbers X H, ‖minorCoefficient X Y H P n‖ ^ 2 =
      ‖∫ α, ∫ β, G α β ∂μ ∂μ‖ := by
    rw [← hTC, Complex.norm_of_nonneg hT0]
  rw [integral_add (hf1i.mul_const M) hjl, hswap,
    integral_mul_const M (fun α : ℝ => ‖primeSum X Y α‖ ^ 2)] at hmain
  rw [integral_mul_const M (fun α : ℝ => ‖primeSum X Y α‖ ^ 2)] at hsecond
  rw [hnorm]
  have hIM := mul_le_mul_of_nonneg_right hI1 hM
  linarith

/-- P0088 page 7 display 29 with I1 bounded by a constant times Y.
This is the short Dirichlet kernel and Cauchy step, the statement of
Task556d.minor_mean_square_of_kernel, proved here with K equal to 4 and
X0 equal to 2. -/
theorem minor_mean_square_of_kernel_route (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ K X0 : ℝ, 0 < K ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ M : ℝ, 0 ≤ M →
      (∀ β ∈ Set.Icc (0 : ℝ) 1,
        kernelMass (windowY X ε) H (Real.log X ^ B) β ≤ M) →
      (∑ n ∈ intervalNumbers X H,
        ‖minorCoefficient X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2) ≤
          K * windowY X ε * M := by
  refine ⟨4, 2, by norm_num, le_rfl, ?_⟩
  intro X H hX hH hHX M hM hmass
  have hX1 : 1 < X := by linarith
  have hε1 := written_range_epsilon_le hX1 hH hHX
  have hH1 : 1 ≤ H := (Real.one_le_rpow hX1.le (by positivity)).trans hH
  have hY1 : 1 ≤ windowY X ε := by
    unfold windowY
    exact Real.one_le_rpow hX1.le (by positivity)
  have hYX : windowY X ε ≤ X := by
    unfold windowY
    calc
      X ^ (7 / 12 + ε / 2) ≤ X ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hX1.le (by linarith)
      _ = X := Real.rpow_one X
  exact minor_mean_square_core (by linarith) (by linarith) hY1 hH1 hM hmass

end LeanLab.KumchevLiu2007.Eq33RouteA
