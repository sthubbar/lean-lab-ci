/-
Public statements of Brudern and Perelli 1998.
Task264 moves the unchanged data to State1539Data264 to let the proved
section 8 leaves discharge the original derivative statements.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.ExceptionalSet.Decomp1539a
import LeanLab.ExceptionalSet.KernelTail385
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Function.Floor

namespace LeanLab.ExceptionalSet.Task653

open Real MeasureTheory Filter Asymptotics Topology
open scoped FourierTransform Convolution
open LeanLab.ExceptionalSet.U1539

/-- P0082 pages 355 and 356. Lemma 1 from local Poisson and sampling proofs.
The downstream exact supply cannot be imported without a cycle.
AI wrote this Lean code. Goldbach is open. -/
theorem lemma1_with_sampling653 :
    U1539.Lemma1 ∧
    (∀ (h K : ℝ → ℂ), Function.Periodic h 1 → IntervalIntegrable h volume 0 1 →
      Integrable K → Continuous K → (∀ ξ : ℝ, 1 < |ξ| → ftR K ξ = 0) → ∀ v : ℝ,
      (∫ α, h α * K α * eC (-(α * v))) =
        ∫ α in (0 : ℝ)..1,
          h α * (∑' n : ℤ, K (α + n) * eC (-((α + n) * v)))) ∧
    (∀ K : ℝ → ℂ, Integrable K → Continuous K →
      (∀ ξ : ℝ, 1 < |ξ| → ftR K ξ = 0) → ∀ v α : ℝ,
      (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
        eC (-(α * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) +
          eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1)) ∧
    (∀ (K : ℝ → ℂ), Integrable K → ∀ hcont : Continuous K,
      (∀ ξ : ℝ, 1 < |ξ| → ftR K ξ = 0) → ∀ S : TopologicalSpace.Compacts ℝ,
      Summable (fun n : ℤ =>
        ‖((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖)) := by
  -- Local reuse of Decomp404b.integral_periodization.
  have integral_periodization (g : ℝ → ℂ) (hg : Integrable g) :
      (∫ x, g x) = ∫ x in (0 : ℝ)..1, ∑' n : ℤ, g (x + n) := by
    have hi (n : ℤ) : Integrable (fun x : ℝ => g (x + n)) (volume.restrict (Set.Ioc 0 1)) := by
      exact (hg.comp_add_right (n : ℝ)).integrableOn
    have hs : Summable (fun n : ℤ => ∫ x in Set.Ioc (0 : ℝ) 1, ‖g (x + n)‖) := by
      simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        hg.norm.hasSum_intervalIntegral_comp_add_int.summable
    calc
      _ = ∑' n : ℤ, ∫ x in (0 : ℝ)..1, g (x + n) :=
        hg.hasSum_intervalIntegral_comp_add_int.tsum_eq.symm
      _ = _ := by
        simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact integral_tsum_of_summable_integral_norm hi hs
  -- Local reuse of Decomp404b.fold_of_integrable.
  have fold_of_integrable (h K : ℝ → ℂ) (hper : Function.Periodic h 1) (v : ℝ)
      (hg : Integrable (fun x : ℝ => h x * K x * eC (-(x * v)))) :
      (∫ x, h x * K x * eC (-(x * v))) =
        ∫ x in (0 : ℝ)..1, h x * (∑' n : ℤ, K (x + n) * eC (-((x + n) * v))) := by
    rw [integral_periodization _ hg]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    have he (n : ℤ) : h (x + n) = h x := by
      simpa only [mul_one] using hper.int_mul n x
    simp_rw [he, mul_assoc]
    exact tsum_mul_left
  -- Local reuse of Decomp404b.kernel_decay.
  have kernel_decay (Δ x : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hx : x ≠ 0) :
      ‖(Kfun Δ x : ℂ)‖ ≤ (2 / (Δ * Real.pi ^ 2)) * |x| ^ (-2 : ℝ) := by
    have hp : Real.pi * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx
    have hq : Real.pi * (1 - Δ) * x ≠ 0 :=
      mul_ne_zero (mul_ne_zero Real.pi_ne_zero (by linarith)) hx
    have he : Kfun Δ x =
        (Real.sin (Real.pi * x) ^ 2 - Real.sin (Real.pi * (1 - Δ) * x) ^ 2) /
          (Δ * Real.pi ^ 2 * x ^ 2) := by
      rw [Kfun, Real.sinc_of_ne_zero hp, Real.sinc_of_ne_zero hq]
      field_simp
    have hden : 0 < Δ * Real.pi ^ 2 * x ^ 2 := by positivity
    have hs (y : ℝ) : Real.sin y ^ 2 ≤ 1 := by
      nlinarith [Real.abs_sin_le_one y, sq_nonneg (Real.cos y), Real.sin_sq_add_cos_sq y]
    have hnum : |Real.sin (Real.pi * x) ^ 2 - Real.sin (Real.pi * (1 - Δ) * x) ^ 2| ≤ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [hs (Real.pi * x), hs (Real.pi * (1 - Δ) * x),
        sq_nonneg (Real.sin (Real.pi * x)), sq_nonneg (Real.sin (Real.pi * (1 - Δ) * x))]
    simp only [Complex.norm_real, Real.norm_eq_abs, he, abs_div, abs_of_pos hden]
    calc
      _ ≤ 2 / (Δ * Real.pi ^ 2 * x ^ 2) := div_le_div_of_nonneg_right hnum hden.le
      _ = _ := by
        rw [Real.rpow_neg (abs_nonneg x), Real.rpow_two, sq_abs]
        ring
  -- Local reuse of Decomp404b.ftR_eq_fourier.
  have ftR_eq_fourier (K : ℝ → ℂ) (y : ℝ) :
      ftR K y = FourierTransform.fourier K y := by
    simp only [ftR, eC, Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
    apply integral_congr_ae
    filter_upwards with x
    have hx : 2 * (Real.pi : ℂ) * Complex.I * (-(y * x) : ℝ) =
        ↑(-2 * Real.pi * x * y) * Complex.I := by push_cast; ring
    rw [hx]
    ring
  -- Local reuse of Decomp404b.modulated_kernel_isBigO.
  have modulated_kernel_isBigO (Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
      (fun x : ℝ => (Kfun Δ x : ℂ) * eC (-(x * v))) =O[cocompact ℝ]
        (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    apply IsBigO.of_bound (2 / (Δ * Real.pi ^ 2))
    filter_upwards [(isCompact_singleton : IsCompact ({0} : Set ℝ)).compl_mem_cocompact] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    simpa only [norm_mul, norm_eC, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)] using kernel_decay Δ x hΔ hΔ1 hx0
  -- Local reuse of Decomp464a.leaf_poisson_index_shift.
  have leaf_poisson_index_shift (v : ℝ) (m : ℤ) :
      v + (m : ℝ) = Int.fract v + ((m + ⌊v⌋ : ℤ) : ℝ) := by
    simp only [Int.fract, Int.cast_add]
    ring
  -- Local reuse of Decomp464a.leaf_poisson_index_ne_zero.
  have leaf_poisson_index_ne_zero (v : ℝ) (m : ℤ) (hm : m ≠ -⌊v⌋) :
      m + ⌊v⌋ ≠ 0 := by
    omega
  -- Local reuse of Decomp464a.leaf_poisson_index_ne_neg_one.
  have leaf_poisson_index_ne_neg_one (v : ℝ) (m : ℤ) (hm : m ≠ -(⌊v⌋ + 1)) :
      m + ⌊v⌋ ≠ -1 := by
    omega
  -- Local reuse of Decomp464a.leaf_poisson_index_dichotomy.
  have leaf_poisson_index_dichotomy (k : ℤ) (h0 : k ≠ 0) (h1 : k ≠ -1) :
      1 ≤ k ∨ k ≤ -2 := by
    omega
  -- Local reuse of Decomp464a.leaf_poisson_index_upper.
  have leaf_poisson_index_upper (v : ℝ) (k : ℤ) (hk : 1 ≤ k) :
      1 ≤ |Int.fract v + (k : ℝ)| := by
    have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    exact (by linarith [Int.fract_nonneg v] : (1 : ℝ) ≤ Int.fract v + (k : ℝ)).trans
      (le_abs_self _)
  -- Local reuse of Decomp464a.leaf_poisson_index_lower.
  have leaf_poisson_index_lower (v : ℝ) (k : ℤ) (hk : k ≤ -2) :
      1 ≤ |Int.fract v + (k : ℝ)| := by
    have hk' : (k : ℝ) ≤ -2 := by exact_mod_cast hk
    have hneg : Int.fract v + (k : ℝ) ≤ -1 := by linarith [Int.fract_lt_one v]
    calc (1 : ℝ) ≤ -(Int.fract v + (k : ℝ)) := by linarith
      _ ≤ |Int.fract v + (k : ℝ)| := neg_le_abs _
  -- Local reuse of Decomp464a.leaf_poisson_index_split.
  have leaf_poisson_index_split (v : ℝ) :
      ∀ m : ℤ, m ≠ -⌊v⌋ → m ≠ -(⌊v⌋ + 1) → 1 ≤ |v + (m : ℝ)| := by
    intro m hm hm'
    rw [leaf_poisson_index_shift v m]
    have h0 : m + ⌊v⌋ ≠ 0 := leaf_poisson_index_ne_zero v m hm
    have h1 : m + ⌊v⌋ ≠ -1 := leaf_poisson_index_ne_neg_one v m hm'
    rcases leaf_poisson_index_dichotomy (m + ⌊v⌋) h0 h1 with hk | hk
    · exact leaf_poisson_index_upper v (m + ⌊v⌋) hk
    · exact leaf_poisson_index_lower v (m + ⌊v⌋) hk
  -- Local reuse of Decomp464b.leaf_ftR_continuous.
  have leaf_ftR_continuous (K : ℝ → ℂ) (hK : Integrable K) : Continuous (ftR K) := by
    have hct : Continuous (FourierTransform.fourier K) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (L := innerₗ ℝ) continuous_inner hK
    have he : ftR K = FourierTransform.fourier K :=
      funext (ftR_eq_fourier K)
    rw [he]
    exact hct
  -- Local reuse of Decomp464b.leaf_rescale_tendsto.
  have leaf_rescale_tendsto (ξ : ℝ) :
      Filter.Tendsto (fun n : ℕ => ξ * (1 + (1 : ℝ) / ((n : ℝ) + 1))) Filter.atTop (nhds ξ) := by
    simpa only [add_zero, mul_one] using
      (tendsto_const_nhds (x := ξ)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  -- Local reuse of Decomp464b.leaf_rescale_abs_gt_one.
  have leaf_rescale_abs_gt_one (ξ : ℝ) (hξ : 1 ≤ |ξ|) (n : ℕ) :
      1 < |ξ * (1 + (1 : ℝ) / ((n : ℝ) + 1))| := by
    have hp : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    rw [abs_mul, abs_of_pos (by linarith : 0 < 1 + (1 : ℝ) / ((n : ℝ) + 1))]
    nlinarith
  -- Local reuse of Decomp464b.leaf_eq_zero_of_tendsto.
  have leaf_eq_zero_of_tendsto {f : ℝ → ℂ} {u : ℕ → ℝ} {ξ : ℝ}
      (hf : Continuous f) (hu : Filter.Tendsto u Filter.atTop (nhds ξ)) (h0 : ∀ n : ℕ, f (u n) = 0) :
      f ξ = 0 := by
    have hlim : Filter.Tendsto (fun _ : ℕ => (0 : ℂ)) Filter.atTop (nhds (f ξ)) := by
      simpa only [Function.comp_def, h0] using (hf.continuousAt.tendsto.comp hu)
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  -- Local reuse of Decomp464b.leaf_poisson_endpoint_split.
  have leaf_poisson_endpoint_split (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
      (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
      ∀ ξ : ℝ, 1 ≤ |ξ| → ftR K ξ = 0 := by
    intro ξ hξ
    refine leaf_eq_zero_of_tendsto (f := ftR K) (u := fun n : ℕ => ξ * (1 + (1 : ℝ) / ((n : ℝ) + 1)))
      (leaf_ftR_continuous K hK) (leaf_rescale_tendsto ξ) ?_
    intro n
    exact hsupp _ (leaf_rescale_abs_gt_one ξ hξ n)
  -- Local reuse of SPLIT_leaf_poisson_collapse.leaf_collapse_index_vanishes.
  have leaf_collapse_index_vanishes (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
      (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
      ∀ m : ℤ, m ≠ -⌊v⌋ → m ≠ -(⌊v⌋ + 1) →
        eC (α * (m : ℝ)) * ftR K (v + (m : ℝ)) = 0 := by
    intro m hm₀ hm₁
    rw [leaf_poisson_endpoint_split K hK hcont hsupp _ (leaf_poisson_index_split v m hm₀ hm₁),
      mul_zero]
  -- Local reuse of SPLIT_leaf_poisson_collapse.leaf_collapse_tsum_pair.
  have leaf_collapse_tsum_pair (F : ℤ → ℂ) (a b : ℤ) (hab : a ≠ b)
      (h : ∀ m : ℤ, m ≠ a → m ≠ b → F m = 0) :
      (∑' m : ℤ, F m) = F a + F b := by
    have hzero : ∀ m ∉ ({a, b} : Finset ℤ), F m = 0 := by
      intro m hm
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
      exact h m hm.1 hm.2
    rw [tsum_eq_sum hzero, Finset.sum_pair hab]
  -- Local reuse of SPLIT_leaf_poisson_collapse.leaf_collapse_term_floor.
  have leaf_collapse_term_floor (K : ℝ → ℂ) (v α : ℝ) :
      eC (α * ((-⌊v⌋ : ℤ) : ℝ)) * ftR K (v + ((-⌊v⌋ : ℤ) : ℝ)) =
        eC (-(α * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) := by
    simp only [Int.cast_neg, mul_neg, Int.fract, sub_eq_add_neg]
  -- Local reuse of SPLIT_leaf_poisson_collapse.leaf_collapse_term_succ.
  have leaf_collapse_term_succ (K : ℝ → ℂ) (v α : ℝ) :
      eC (α * ((-(⌊v⌋ + 1) : ℤ) : ℝ)) * ftR K (v + ((-(⌊v⌋ + 1) : ℤ) : ℝ)) =
        eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1) := by
    have hfreq : v + ((-(⌊v⌋ + 1) : ℤ) : ℝ) = Int.fract v - 1 := by
      simp only [Int.cast_neg, Int.cast_add, Int.cast_one, Int.fract]
      ring
    rw [hfreq, Int.cast_neg, mul_neg]
  -- Local reuse of SPLIT_leaf_poisson_collapse.leaf_poisson_collapse_split.
  have leaf_poisson_collapse_split (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
      (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
      (∑' m : ℤ, eC (α * (m : ℝ)) * ftR K (v + (m : ℝ))) =
        eC (-(α * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) +
          eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1) := by
    have hne : (-⌊v⌋ : ℤ) ≠ -(⌊v⌋ + 1) := by omega
    rw [leaf_collapse_tsum_pair (fun m : ℤ => eC (α * (m : ℝ)) * ftR K (v + (m : ℝ)))
      (-⌊v⌋) (-(⌊v⌋ + 1)) hne (leaf_collapse_index_vanishes K hK hcont hsupp v α)]
    rw [leaf_collapse_term_floor K v α, leaf_collapse_term_succ K v α]
  -- Local reuse of Decomp450j.bandlimited_fourier_integrable.
  have bandlimited_fourier_integrable (K : ℝ → ℂ) (hK : Integrable K)
      (hsupp : ∀ ξ : ℝ, 1 < |ξ| → ftR K ξ = 0) :
      Integrable (FourierTransform.fourier K) := by
    have hct : Continuous (FourierTransform.fourier K) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (L := innerₗ ℝ) continuous_inner hK
    have hsupport : Function.support (FourierTransform.fourier K) ⊆ Set.Icc (-1 : ℝ) 1 := by
      intro ξ hξ
      by_contra hout
      have hlarge : 1 < |ξ| := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hout
        rcases hout with hlo | hhi
        · rw [abs_of_neg (by linarith)]
          linarith
        · rw [abs_of_nonneg (by linarith)]
          exact hhi
      apply hξ
      rw [← ftR_eq_fourier]
      exact hsupp ξ hlarge
    apply hct.integrable_of_hasCompactSupport
    rw [hasCompactSupport_def]
    exact isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hsupport isClosed_Icc)
  -- Local reuse of Decomp464g.wide_kernel_fourier.
  have wide_kernel_fourier (ξ : ℝ) :
      FourierTransform.fourier
        (fun x : ℝ => (2 : ℂ) * (Kfun (1 / 4) (2 * x) : ℂ)) ξ =
        (KernelTransform264.weight (1 / 4) (ξ / 2) : ℂ) := by
    have hscale : FourierTransform.fourier
        (fun x : ℝ => (2 : ℂ) * (Kfun (1 / 4) (2 * x) : ℂ)) ξ =
        (2 : ℂ) * FourierTransform.fourier
          (fun x : ℝ => (Kfun (1 / 4) (2 * x) : ℂ)) ξ := by
      simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    have hd := TriangleKernel264.fourier_comp_pos_mul
      (fun t : ℝ => (Kfun (1 / 4) t : ℂ)) (by norm_num : (0 : ℝ) < 2) ξ
    rw [hscale, hd,
      KernelTransform264.fourier_Kfun (by norm_num) (by norm_num)]
    norm_num <;> ring
  -- Local reuse of Decomp464g.bandlimited_reproducing_convolution.
  have bandlimited_reproducing_convolution (K : ℝ → ℂ) (hK : Integrable K)
      (hcont : Continuous K) (hsupp : ∀ ξ : ℝ, 1 < |ξ| → ftR K ξ = 0) (x : ℝ) :
      (∫ y : ℝ, K y * ((2 : ℂ) * (Kfun (1 / 4) (2 * (x - y)) : ℂ))) = K x := by
    let H : ℝ → ℂ := fun y => (2 : ℂ) * (Kfun (1 / 4) (2 * y) : ℂ)
    let C : ℝ → ℂ := K ⋆[ContinuousLinearMap.mul ℂ ℂ] H
    have hHi : Integrable H :=
      ((KernelTransform264.Kfun_integrable (by norm_num : (0 : ℝ) < 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1)).comp_mul_left'
          (by norm_num : (2 : ℝ) ≠ 0)).const_mul (2 : ℂ)
    have hHc : Continuous H := continuous_const.mul
      ((KernelTransform264.Kfun_continuous (1 / 4)).comp (continuous_const.mul continuous_id))
    have hHb : BddAbove (Set.range fun y => ‖H y‖) := by
      refine ⟨4, ?_⟩
      rintro _ ⟨y, rfl⟩
      have hk := KernelTail385.kernel_abs_le_two_sub (1 / 4) (2 * y)
        (by norm_num) (by norm_num)
      dsimp only [H]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      norm_num
      linarith
    have hCi : Integrable C := hK.integrable_convolution
      (L := ContinuousLinearMap.mul ℂ ℂ) hHi
    have hCc : Continuous C :=
      BddAbove.continuous_convolution_right_of_integrable
        (ContinuousLinearMap.mul ℂ ℂ) hHb hK hHc
    have hFeq : FourierTransform.fourier C = FourierTransform.fourier K := by
      funext ξ
      change FourierTransform.fourier (K ⋆[ContinuousLinearMap.mul ℂ ℂ] H) ξ = _
      rw [Real.fourier_mul_convolution_eq hK hHi]
      by_cases hξ : |ξ| ≤ 1
      · have hw : KernelTransform264.weight (1 / 4) (ξ / 2) = 1 := by
          apply KernelTransform264.weight_one (by norm_num) (by norm_num)
          rw [abs_div]
          norm_num
          linarith
        have hwide : FourierTransform.fourier H ξ =
            (KernelTransform264.weight (1 / 4) (ξ / 2) : ℂ) := wide_kernel_fourier ξ
        rw [hwide, hw, Complex.ofReal_one, mul_one]
      · have hz : FourierTransform.fourier K ξ = 0 := by
          rw [← ftR_eq_fourier]
          exact hsupp ξ (lt_of_not_ge hξ)
        rw [hz, zero_mul]
    have hFi : Integrable (FourierTransform.fourier K) :=
      bandlimited_fourier_integrable K hK hsupp
    have hCFi : Integrable (FourierTransform.fourier C) := hFeq.symm ▸ hFi
    have hCK : C = K := by
      calc
        C = FourierTransformInv.fourierInv (FourierTransform.fourier C) :=
          (hCc.fourierInv_fourier_eq hCi hCFi).symm
        _ = FourierTransformInv.fourierInv (FourierTransform.fourier K) := by rw [hFeq]
        _ = K := hcont.fourierInv_fourier_eq hK hFi
    change C x = K x
    exact congrFun hCK x
  -- Local reuse of Decomp464h.convolution_translate_norm.
  have convolution_translate_norm (K H : ℝ → ℂ) (hK : Integrable K)
      (hKc : Continuous K) (hHc : Continuous H)
      (hHnorm : ∀ T : TopologicalSpace.Compacts ℝ,
        Summable (fun n : ℤ =>
          ‖((⟨H, hHc⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict T‖))
      (hrepr : ∀ x : ℝ, K x = ∫ y : ℝ, K y * H (x - y))
      (S : TopologicalSpace.Compacts ℝ) :
      Summable (fun n : ℤ =>
        ‖((⟨K, hKc⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖) := by
    let T : TopologicalSpace.Compacts ℝ :=
      ⟨(fun p : ℝ × ℝ => p.1 - p.2) '' ((S : Set ℝ) ×ˢ Set.Icc (0 : ℝ) 1),
        (S.isCompact.prod isCompact_Icc).image (continuous_fst.sub continuous_snd)⟩
    let M : ℤ → ℝ := fun n =>
      ‖((⟨H, hHc⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict T‖
    have hM : Summable M := hHnorm T
    have hM0 (n : ℤ) : 0 ≤ M n := norm_nonneg _
    let C := ∑' n : ℤ, M n
    have hMC (n : ℤ) : M n ≤ C := hM.le_tsum n (fun j _ => hM0 j)
    let g : ℤ → ℝ → ℝ := fun n y => ‖K y‖ * M (n - ⌊y⌋)
    have hg0 (n : ℤ) (y : ℝ) : 0 ≤ g n y := mul_nonneg (norm_nonneg _) (hM0 _)
    have hgi (n : ℤ) : Integrable (g n) := by
      have hm : Measurable (fun y : ℝ => M (n - ⌊y⌋)) :=
        (measurable_of_countable M).comp (measurable_const.sub Int.measurable_floor)
      apply hK.norm.mul_bdd hm.aestronglyMeasurable
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (hM0 _)]
      exact hMC _
    have hHbound (n : ℤ) (x : S) (y : ℝ) :
        ‖H ((x : ℝ) + (n : ℝ) - y)‖ ≤ M (n - ⌊y⌋) := by
      let z : T := ⟨(x : ℝ) - Int.fract y,
        ⟨((x : ℝ), Int.fract y),
          ⟨x.property, ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩⟩, rfl⟩⟩
      have he : (x : ℝ) + (n : ℝ) - y =
          (z : ℝ) + ((n - ⌊y⌋ : ℤ) : ℝ) := by
        dsimp only [z]
        simp only [Int.fract, Int.cast_sub]
        ring
      rw [he]
      exact ContinuousMap.norm_coe_le_norm
        (((⟨H, hHc⟩ : C(ℝ, ℂ)).comp
          (ContinuousMap.addRight ((n - ⌊y⌋ : ℤ) : ℝ))).restrict T) z
    have hsup (n : ℤ) :
        ‖((⟨K, hKc⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖ ≤
          ∫ y : ℝ, g n y := by
      apply (ContinuousMap.norm_le _ (integral_nonneg (hg0 n))).mpr
      intro x
      change ‖K ((x : ℝ) + (n : ℝ))‖ ≤ _
      rw [hrepr ((x : ℝ) + (n : ℝ))]
      apply (norm_integral_le_integral_norm _).trans
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => norm_nonneg _)) (hgi n)
      filter_upwards with y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hHbound n x y) (norm_nonneg _)
    have hsumM (s : Finset ℤ) (y : ℝ) : ∑ n ∈ s, M (n - ⌊y⌋) ≤ C := by
      have hs : Summable (fun n : ℤ => M (n - ⌊y⌋)) :=
        (Equiv.summable_iff (f := M) (Equiv.subRight (⌊y⌋ : ℤ))).mpr hM
      have ht : (∑' n : ℤ, M (n - ⌊y⌋)) = C := (Equiv.subRight ⌊y⌋).tsum_eq M
      exact (hs.sum_le_tsum s (fun n _ => hM0 _)).trans_eq ht
    apply summable_of_sum_le (fun n => norm_nonneg _) (c := (∫ y : ℝ, ‖K y‖) * C)
    intro s
    calc
      _ ≤ ∑ n ∈ s, ∫ y : ℝ, g n y := Finset.sum_le_sum (fun n _ => hsup n)
      _ = ∫ y : ℝ, ∑ n ∈ s, g n y :=
        (integral_finsetSum s (fun n _ => hgi n)).symm
      _ ≤ ∫ y : ℝ, ‖K y‖ * C := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun y => Finset.sum_nonneg (fun n _ => hg0 n y)))
          (hK.norm.mul_const C)
        filter_upwards with y
        change (∑ n ∈ s, ‖K y‖ * M (n - ⌊y⌋)) ≤ ‖K y‖ * C
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hsumM s y) (norm_nonneg _)
      _ = _ := integral_mul_const _ _
  -- Local reuse of Decomp450a.kernel_translate_norm.
  have kernel_translate_norm (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
      (S : TopologicalSpace.Compacts ℝ) :
      Summable (fun n : ℤ =>
        ‖((⟨fun x : ℝ => (LeanLab.ExceptionalSet.U1539.Kfun Δ x : ℂ),
          KernelTransform264.Kfun_continuous Δ⟩ : C(ℝ, ℂ)).comp
            (ContinuousMap.addRight (n : ℝ))).restrict S‖) := by
    have hd : Asymptotics.IsBigO (Filter.cocompact ℝ)
        (fun x : ℝ => (LeanLab.ExceptionalSet.U1539.Kfun Δ x : ℂ))
        (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
      simpa only [mul_zero, neg_zero, eC, Complex.ofReal_zero,
        Complex.exp_zero, mul_one] using modulated_kernel_isBigO Δ 0 hΔ hΔ1
    exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
      ((isBigO_norm_restrict_cocompact
        ⟨_, KernelTransform264.Kfun_continuous Δ⟩ (by norm_num : (0 : ℝ) < 2) hd S).comp_tendsto
          Int.tendsto_coe_cofinite)
  -- Local reuse of Decomp464i.leaf_translate_norm_supplied.
  have leaf_translate_norm_supplied (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
      (hsupp : ∀ ξ : ℝ, 1 < |ξ| → ftR K ξ = 0) :
      ∀ S : TopologicalSpace.Compacts ℝ,
        Summable (fun n : ℤ =>
          ‖((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖) := by
    let H : ℝ → ℂ := fun y => (2 : ℂ) * (Kfun (1 / 4) (2 * y) : ℂ)
    have hHc : Continuous H := continuous_const.mul
      ((KernelTransform264.Kfun_continuous (1 / 4)).comp (continuous_const.mul continuous_id))
    have hHnorm (S : TopologicalSpace.Compacts ℝ) :
        Summable (fun n : ℤ =>
          ‖((⟨H, hHc⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖) := by
      let T : TopologicalSpace.Compacts ℝ :=
        ⟨(fun x : ℝ => 2 * x) '' (S : Set ℝ),
          S.isCompact.image (continuous_const.mul continuous_id)⟩
      let M : ℤ → ℝ := fun n =>
        ‖((⟨fun x : ℝ => (Kfun (1 / 4) x : ℂ),
          KernelTransform264.Kfun_continuous (1 / 4)⟩ : C(ℝ, ℂ)).comp
            (ContinuousMap.addRight (n : ℝ))).restrict T‖
      have hM : Summable M :=
        kernel_translate_norm (1 / 4) (by norm_num) (by norm_num) T
      have hinj : Function.Injective (fun n : ℤ => 2 * n) := by
        intro a b hab
        exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hab
      have hME : Summable (fun n : ℤ => 2 * M (2 * n)) :=
        (hM.comp_injective hinj).mul_left 2
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hME
      apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num) (norm_nonneg _))).mpr
      intro x
      change ‖(2 : ℂ) * (Kfun (1 / 4) (2 * ((x : ℝ) + (n : ℝ))) : ℂ)‖ ≤ 2 * M (2 * n)
      rw [norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have he : 2 * ((x : ℝ) + (n : ℝ)) =
          2 * (x : ℝ) + ((2 * n : ℤ) : ℝ) := by
        push_cast
        ring
      rw [he]
      exact ContinuousMap.norm_coe_le_norm
        (((⟨fun y : ℝ => (Kfun (1 / 4) y : ℂ),
          KernelTransform264.Kfun_continuous (1 / 4)⟩ : C(ℝ, ℂ)).comp
            (ContinuousMap.addRight ((2 * n : ℤ) : ℝ))).restrict T)
        ⟨2 * (x : ℝ), ⟨(x : ℝ), x.property, rfl⟩⟩
    intro S
    exact convolution_translate_norm K H hK hcont hHc hHnorm
      (fun x => (bandlimited_reproducing_convolution K hK hcont hsupp x).symm) S
  -- Local reuse of Decomp450b.product_integrable_of_translate_norm.
  have product_integrable_of_translate_norm (h K : ℝ → ℂ)
      (hper : Function.Periodic h 1) (hh : IntervalIntegrable h volume 0 1)
      (hcont : Continuous K)
      (hnorm : Summable (fun n : ℤ =>
        ‖((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict
          (Set.Icc 0 1)‖)) :
      Integrable (fun x : ℝ => h x * K x) := by
    let c : ℤ → ℝ := fun n =>
      ‖((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict
        (Set.Icc 0 1)‖
    have hperiod (n : ℤ) (x : ℝ) : h (x + n) = h x := by
      simpa only [mul_one] using hper.int_mul n x
    have hhn (n : ℤ) : IntervalIntegrable h volume (n : ℝ) (n + 1) := by
      have hi := hh.comp_add_right (-(n : ℝ))
      simp only [show (fun x : ℝ => h (x + -(n : ℝ))) = h from
        funext (fun x => by simpa only [Int.cast_neg] using hperiod (-n) x)] at hi
      convert hi using 1 <;> ring
    have hgn (n : ℤ) : IntegrableOn (fun x : ℝ => h x * K x)
        (Set.Ioc (n : ℝ) (n + 1)) := by
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
        ((hhn n).mul_continuousOn hcont.continuousOn)
    have hbound (n : ℤ) (x : ℝ) (hx : x ∈ Set.Ioc (n : ℝ) (n + 1)) : ‖K x‖ ≤ c n := by
      have hb := (((⟨K, hcont⟩ : C(ℝ, ℂ)).comp
        (ContinuousMap.addRight (n : ℝ))).restrict (Set.Icc 0 1)).norm_coe_le_norm
          ⟨x - n, ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩
      simpa only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply,
        ContinuousMap.coe_mk, ContinuousMap.coe_addRight, sub_add_cancel] using hb
    have hintegral (n : ℤ) :
        (∫ x in Set.Ioc (n : ℝ) (n + 1), ‖h x‖) = ∫ x in (0 : ℝ)..1, ‖h x‖ := by
      rw [← intervalIntegral.integral_of_le (by linarith : (n : ℝ) ≤ n + 1)]
      have hi := intervalIntegral.integral_comp_add_right (fun x : ℝ => ‖h x‖) (n : ℝ)
        (a := 0) (b := 1)
      rw [show (1 : ℝ) + n = n + 1 by ring] at hi
      simpa only [zero_add, hperiod] using hi.symm
    have hs : Summable (fun n : ℤ =>
        ∫ x in Set.Ioc (n : ℝ) (n + 1), ‖h x * K x‖) := by
      apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _))
        (fun n => ?_) (hnorm.mul_left (∫ x in (0 : ℝ)..1, ‖h x‖))
      calc
        _ ≤ ∫ x in Set.Ioc (n : ℝ) (n + 1), ‖h x‖ * c n := by
          apply setIntegral_mono_on (hgn n).norm
            (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp (hhn n)).norm.mul_const _)
            measurableSet_Ioc
          intro x hx
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hbound n x hx) (norm_nonneg _)
        _ = (∫ x in (0 : ℝ)..1, ‖h x‖) * c n := by
          rw [integral_mul_const, hintegral]
    have hi := integrableOn_iUnion_of_summable_integral_norm hgn hs
    simpa only [iUnion_Ioc_intCast, integrableOn_univ] using hi
  -- Local reuse of Decomp450a.fourier_modulated.
  have fourier_modulated (K : ℝ → ℂ) (v y : ℝ) :
      FourierTransform.fourier (fun x : ℝ => K x * eC (-(x * v))) y = ftR K (v + y) := by
    rw [← ftR_eq_fourier]
    unfold ftR
    apply integral_congr_ae
    filter_upwards with x
    unfold eC
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  -- Local reuse of Decomp450a.modulated_translate_norm.
  have modulated_translate_norm (K : ℝ → ℂ) (hcont : Continuous K)
      (v : ℝ) (S : TopologicalSpace.Compacts ℝ) (n : ℤ) :
      ‖((⟨fun x : ℝ => K x * eC (-(x * v)),
        hcont.mul (by unfold eC; fun_prop)⟩ : C(ℝ, ℂ)).comp
          (ContinuousMap.addRight (n : ℝ))).restrict S‖ =
        ‖((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖ := by
    simp only [ContinuousMap.norm_eq_iSup_norm, ContinuousMap.restrict_apply,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.coe_addRight,
      norm_mul, LeanLab.ExceptionalSet.U1539.norm_eC, mul_one]
  -- Local reuse of Decomp450a.summation_of_translate_norm.
  have summation_of_translate_norm (K : ℝ → ℂ) (hK : Integrable K)
      (hcont : Continuous K) (hsupp : ∀ ξ : ℝ, 1 < |ξ| → ftR K ξ = 0)
      (hnorm : ∀ S : TopologicalSpace.Compacts ℝ,
        Summable (fun n : ℤ =>
          ‖((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖))
      (v α : ℝ) :
      (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
        ∑' m : ℤ, eC (α * (m : ℝ)) * ftR K (v + (m : ℝ)) := by
    classical
    let f : C(ℝ, ℂ) := ⟨fun x => K x * eC (-(x * v)),
      hcont.mul (by unfold eC; fun_prop)⟩
    have hf (m : ℤ) : FourierTransform.fourier (f : ℝ → ℂ) m = ftR K (v + m) :=
      fourier_modulated K v m
    have hzero (m : ℤ) (hm : m ∉ ({-⌊v⌋, -(⌊v⌋ + 1)} : Finset ℤ)) :
        FourierTransform.fourier (f : ℝ → ℂ) m = 0 := by
      rw [hf]
      apply leaf_poisson_endpoint_split K hK hcont hsupp
      apply leaf_poisson_index_split v m
      · intro he; exact hm (by simp [he])
      · intro he; exact hm (by simp [he])
    have hfnorm : ∀ S : TopologicalSpace.Compacts ℝ,
        Summable (fun n : ℤ => ‖(f.comp (ContinuousMap.addRight (n : ℝ))).restrict S‖) := by
      intro S
      convert hnorm S using 1
      funext n
      exact modulated_translate_norm K hcont v S n
    have hp := Real.tsum_eq_tsum_fourier hfnorm (summable_of_ne_finset_zero hzero) α
    change (∑' n : ℤ, f (α + n)) = _
    rw [hp]
    apply tsum_congr
    intro m
    rw [hf]
    simp only [fourier_coe_apply, Complex.ofReal_one, div_one]
    have he : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (α : ℂ)) =
        eC (α * (m : ℝ)) := by
      unfold eC
      push_cast
      congr 1
      ring
    rw [he, mul_comm]
  -- Local reuse of Decomp464j.product_integrable_supplied.
  have product_integrable_supplied (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
      (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
      (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
      Integrable (fun α : ℝ => h α * K α) := by
    exact product_integrable_of_translate_norm h K hper hh hcont
      (leaf_translate_norm_supplied K hK hcont hsupp
        ⟨Set.Icc 0 1, isCompact_Icc⟩)
  -- Local reuse of Decomp464j.fold_supplied.
  have fold_supplied (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
      (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
      (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v : ℝ) :
      (∫ α, h α * K α * eC (-(α * v))) =
        ∫ α in (0 : ℝ)..1,
          h α * (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) := by
    apply fold_of_integrable h K hper v
    have he : Continuous (fun α : ℝ => eC (-(α * v))) := by unfold eC; fun_prop
    exact (product_integrable_supplied h K hper hh hK hcont hsupp).mul_bdd
      he.aestronglyMeasurable (Filter.Eventually.of_forall (fun α => (U1539.norm_eC _).le))
  -- Local reuse of Decomp464j.poisson_summation_supplied.
  have poisson_summation_supplied (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
      (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
      (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
        ∑' m : ℤ, eC (α * (m : ℝ)) * ftR K (v + (m : ℝ)) := by
    exact summation_of_translate_norm K hK hcont hsupp
      (leaf_translate_norm_supplied K hK hcont hsupp) v α
  -- Local reuse of Decomp464j.poisson_supplied.
  have poisson_supplied (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
      (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
      (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
        eC (-(α * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) +
          eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1) := by
    rw [poisson_summation_supplied K hK hcont hsupp v α,
      leaf_poisson_collapse_split K hK hcont hsupp v α]
  refine ⟨?_, fold_supplied, poisson_supplied, leaf_translate_norm_supplied⟩
  · intro h K hper hh hK hcont hsupp v
    have hg0 : IntervalIntegrable (fun α : ℝ => h α * eC (-(α * (⌊v⌋ : ℝ)))) volume 0 1 := by
      apply hh.mul_continuousOn
      unfold eC
      fun_prop
    have hg1 : IntervalIntegrable (fun α : ℝ => h α * eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ)))) volume 0 1 := by
      apply hh.mul_continuousOn
      unfold eC
      fun_prop
    calc
      _ = ∫ α in (0 : ℝ)..1,
          (h α * eC (-(α * (⌊v⌋ : ℝ)))) * ftR K (Int.fract v) +
            (h α * eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ)))) * ftR K (Int.fract v - 1) := by
        rw [fold_supplied h K hper hh hK hcont hsupp v]
        apply intervalIntegral.integral_congr
        intro α hα
        dsimp only
        rw [poisson_supplied K hK hcont hsupp v α]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add
          (hg0.mul_const (ftR K (Int.fract v)))
          (hg1.mul_const (ftR K (Int.fract v - 1))),
          intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
        unfold hcheck
        ring

/-- P0082 pages 355 and 356. The exact Lemma 1 projection of the proved inputs. -/
theorem lemma1_via_poisson653 : U1539.Lemma1 :=
  lemma1_with_sampling653.1

end LeanLab.ExceptionalSet.Task653

namespace LeanLab.ExceptionalSet.U1539

/-! ### Sealed statements -/

/-- CITED. Theorem 2 of J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378, p. 354, proved there in §8 from Karacuba's estimate.
Decomp1539a splits that proof into leaves. -/
theorem theorem2 : Theorem2 := by sorry

/-- CITED. Lemma 10 of Brüdern-Perelli 1998, p. 370-371, which is Theorem 1 of
A. A. Karacuba, Estimates for trigonometric sums by Vinogradov's method, and some
applications, Proc. Steklov Inst. Math. 112 (1973) 251-265, in Brüdern-Perelli's notation. -/
theorem lemma10 : Lemma10 := by sorry

/-- Lemma 1 of the paper, p. 355-356, a Poisson summation identity. Open statement. -/
theorem lemma1 : Lemma1 := by
  exact LeanLab.ExceptionalSet.Task653.lemma1_via_poisson653

/-- Lemma 4 of the paper, p. 359, from Theorem 2 with `c = 1/2` by Vinogradov's
equidistribution argument. Open statement. -/
theorem lemma4 : Lemma4 := by sorry

/-- Lemma 6 of the paper, p. 362, proved in its §6. Open statement. -/
theorem lemma6 : Lemma6 := by sorry

/-- Lemma 7 of the paper, p. 362-364. Open statement. -/
theorem lemma7 : Lemma7 := by sorry

/-- Lemma 8 of the paper, p. 364-365. Open statement. -/
theorem lemma8 : Lemma8 := by sorry

/-- Lemma 9 of the paper, p. 368, proved in its §7. Open statement. -/
theorem lemma9 : Lemma9 := by sorry

/-- Lemma 11 of the paper, p. 372. Open statement; Decomp1539a splits it. -/
theorem lemma11 : Lemma11 := by
  exact section8_derivative_inputs.1

/-- Lemma 12 of the paper, p. 373, with `s^{2t+j}`. Open statement; Decomp1539a splits it. -/
theorem lemma12 : Lemma12 := by
  exact section8_derivative_inputs.2.1

/-- Lemma 13 of the paper, p. 375. Open statement; Decomp1539a splits it. -/
theorem lemma13 : Lemma13 := by
  exact section8_derivative_inputs.2.2.1

/-- Lemma 14 of the paper, p. 375. Open statement; Decomp1539a splits it. -/
theorem lemma14 : Lemma14 := by
  exact section8_derivative_inputs.2.2.2.1

/-- Lemma 15 of the paper, p. 375-376. Open statement; Decomp1539a splits it. -/
theorem lemma15 : Lemma15 := by
  exact section8_derivative_inputs.2.2.2.2.1

/-- Lemma 16 (a) of the paper, p. 376. Open statement; Decomp1539a splits it. -/
theorem lemma16a : Lemma16a := by
  exact section8_derivative_inputs.2.2.2.2.2.1

/-- Lemma 16 (b) of the paper, p. 376. Open statement; Decomp1539a splits it. -/
theorem lemma16b : Lemma16b := by
  exact section8_derivative_inputs.2.2.2.2.2.2


/-- Theorem 2 from the CITED `lemma10` of State1539 and the leaves. -/
theorem theorem2_via_karacuba : Theorem2 := theorem2_of_all_leaves lemma10

end LeanLab.ExceptionalSet.U1539
