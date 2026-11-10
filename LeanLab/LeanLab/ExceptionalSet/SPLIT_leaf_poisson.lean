import LeanLab.ExceptionalSet.Decomp371d

/-!
Split of the sealed statement `leaf_poisson` of `LeanLab.ExceptionalSet.Decomp371d`
into four strictly smaller steps, plus an assembly `leaf_poisson_split` whose statement is
the sealed statement and whose proof uses only the four leaves.

The steps are the usual two halves of a Poisson summation argument:
* the summation identity itself, over the integer shifts of the modulated kernel;
* the vanishing of the Fourier transform of `K` at the two unit frequencies, which is where
  the continuity of `K` enters, since the support hypothesis only covers `|α| > 1`;
* the index bookkeeping that singles out the two integer shifts whose frequency falls in the
  unit interval;
* the collapse of the resulting series to those two terms.

AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp371d

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck)


/-- The modulus of the exponential character is one. -/
private lemma eC_norm (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  have h : (2 * (π : ℂ) * Complex.I * (x : ℂ)) = ((2 * π * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]


/-- The exponential character is continuous. -/
private lemma eC_continuous : Continuous eC := by
  unfold eC
  fun_prop


/-- The Fourier transform `ftR K` of an integrable `K` is continuous. -/
private lemma continuous_ftR (K : ℝ → ℂ) (hK : Integrable K) : Continuous (ftR K) := by
  unfold ftR
  have key : ∀ β : ℝ, Continuous fun x : ℝ => K β * eC (-(x * β)) := by
    intro β
    exact continuous_const.mul
      (eC_continuous.comp ((continuous_id.mul continuous_const : Continuous fun x : ℝ => x * β).neg))
  have keym : ∀ ξ : ℝ, AEStronglyMeasurable (fun β : ℝ => K β * eC (-(ξ * β))) := by
    intro ξ
    exact hK.aestronglyMeasurable.mul
      (eC_continuous.comp ((continuous_const.mul continuous_id : Continuous fun β : ℝ => ξ * β).neg)).aestronglyMeasurable
  refine continuous_of_dominated (bound := fun β => ‖K β‖)
    (F := fun ξ β => K β * eC (-(ξ * β))) keym ?_ hK.norm ?_
  · intro ξ
    filter_upwards with β
    rw [norm_mul, eC_norm, mul_one]
  · filter_upwards with β
    exact key β


/-- `ftR` is Mathlib's Fourier transform. -/
private lemma ftR_eq_fourier (K : ℝ → ℂ) : ftR K = FourierTransform.fourier K := by
  funext α
  unfold LeanLab.ExceptionalSet.U1539.ftR
  rw [Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun γ => ?_)
  simp only []
  have h1 : (-inner ℝ γ α) = -(α * γ) := by simp [mul_comm]
  rw [h1, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply, mul_comm]
  unfold LeanLab.ExceptionalSet.U1539.eC
  congr 1
  push_cast
  ring


/-- Compact Fourier support makes the transform integrable. -/
private lemma integrable_ftR (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) : Integrable (ftR K) := by
  have hcont' : Continuous (ftR K) := continuous_ftR K hK
  refine hcont'.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc ?_
  intro ξ hξ
  refine hsupp ξ ?_
  have h : ξ < -1 ∨ 1 < ξ := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hξ
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith


/-- A smooth bump equal to one on `[-1,1]`, supported in `[-2,2]`, whose Fourier transform
decays quadratically.  This is the multiplier that turns the merely integrable `K` into a
convolution with a rapidly decaying kernel. -/
private lemma bump_decay :
    ∃ (c : ContDiffBump (0 : ℝ)) (B : ℝ), c.rIn = 1 ∧ c.rOut = 2 ∧ 0 ≤ B ∧
      (∀ x : ℝ, |x| ≤ 1 → ((c x : ℝ) : ℂ) = 1) ∧
      (∀ u : ℝ,
        ‖FourierTransform.fourier (fun x : ℝ => ((c x : ℝ) : ℂ)) u‖ ≤ B / (1 + u ^ 2)) := by
  set c : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩ with hc
  set ψ : ℝ → ℂ := fun x => ((c x : ℝ) : ℂ) with hψ
  have hC : ContDiff ℝ 2 ψ :=
    (Complex.ofRealCLM.contDiff).comp (c.contDiff (n := 2))
  have hcs : HasCompactSupport ψ :=
    c.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hint1 : Integrable (iteratedDeriv 1 ψ) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hC.continuous_iteratedDeriv 1 (by norm_num)
    · rw [iteratedDeriv_one]; exact hcs.deriv
  have hint2 : Integrable (iteratedDeriv 2 ψ) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hC.continuous_iteratedDeriv 2 (by norm_num)
    · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
      exact hcs.deriv.deriv
  refine ⟨c, (∫ v, ‖ψ v‖) + (4 * π ^ 2)⁻¹ * ∫ v, ‖iteratedDeriv 2 ψ v‖, rfl, rfl, ?_, ?_, ?_⟩
  · have h1 : 0 ≤ ∫ v, ‖ψ v‖ := integral_nonneg fun v => norm_nonneg _
    have h2 : 0 ≤ (4 * π ^ 2)⁻¹ * ∫ v, ‖iteratedDeriv 2 ψ v‖ := by positivity
    linarith
  · intro x hx
    have hx' : x ∈ Metric.closedBall (0 : ℝ) c.rIn := by
      rw [Metric.mem_closedBall, Real.dist_eq]
      simpa using hx
    exact_mod_cast c.one_of_mem_closedBall hx'
  · intro u
    rw [hψ]
    have hintψ : Integrable ψ := hC.continuous.integrable_of_hasCompactSupport hcs
    have hint0 : Integrable (iteratedDeriv 0 ψ) := by rw [iteratedDeriv_zero]; exact hintψ
    have h := Real.one_add_sq_mul_norm_fourier_le hC (fun k hk => by
      match k, hk with
      | 0, _ => exact hint0
      | 1, _ => exact hint1
      | 2, _ => exact hint2
      | (k + 3), hk => exact absurd hk (by omega)) u
    have hpos : (0 : ℝ) < 1 + u ^ 2 := by positivity
    rw [le_div_iff₀ hpos]
    calc ‖FourierTransform.fourier ψ u‖ * (1 + u ^ 2)
        = (1 + u ^ 2) * ‖FourierTransform.fourier ψ u‖ := by ring
      _ ≤ (∫ v, ‖ψ v‖) + (4 * π ^ 2)⁻¹ * ∫ v, ‖iteratedDeriv 2 ψ v‖ := h


/-- `𝓕⁻` is `𝓕` at the opposite point. -/
private lemma fourierInv_neg_eq (f : ℝ → ℂ) (w : ℝ) :
    FourierTransform.fourierInv f w = FourierTransform.fourier f (-w) := by
  rw [Real.fourierInv_eq, Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [inner_neg_right, neg_neg]


/-- The inverse transform of the bump: integrable, quadratically decaying, and with transform
identically one on `[-1,1]`. -/
private lemma exists_kernel :
    ∃ (φ : ℝ → ℂ) (B : ℝ), 0 ≤ B ∧ Integrable φ ∧ Continuous φ ∧
      (∀ t : ℝ, ‖φ t‖ ≤ B / (1 + t ^ 2)) ∧
      (∀ ξ : ℝ, |ξ| ≤ 1 → FourierTransform.fourier φ ξ = 1) := by
  obtain ⟨c, B, hr, hR, hB, hone, hdec⟩ := bump_decay
  set ψ : ℝ → ℂ := fun x => ((c x : ℝ) : ℂ) with hψ
  have hC : ContDiff ℝ 2 ψ := (Complex.ofRealCLM.contDiff).comp (c.contDiff (n := 2))
  have hcs : HasCompactSupport ψ :=
    c.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hintψ : Integrable ψ := hC.continuous.integrable_of_hasCompactSupport hcs
  have hcontF : Continuous (FourierTransform.fourier ψ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hintψ
  have hintFψ : Integrable (FourierTransform.fourier ψ) := by
    refine Integrable.mono' (g := fun u : ℝ => B * (1 + u ^ 2)⁻¹)
      (integrable_inv_one_add_sq.const_mul B) hcontF.aestronglyMeasurable ?_
    filter_upwards with u
    simpa only [div_eq_mul_inv] using hdec u
  refine ⟨FourierTransform.fourierInv ψ, B, hB, ?_, ?_, ?_, ?_⟩
  · refine Integrable.mono' (g := fun u : ℝ => B * (1 + u ^ 2)⁻¹)
      (integrable_inv_one_add_sq.const_mul B) ?_ ?_
    · have heq : FourierTransformInv.fourierInv ψ = fun t => FourierTransform.fourier ψ (-t) :=
        funext (fourierInv_neg_eq ψ)
      rw [heq]
      exact (hcontF.comp continuous_neg).aestronglyMeasurable
    · filter_upwards with t
      rw [fourierInv_neg_eq]
      simpa only [div_eq_mul_inv, neg_sq] using hdec (-t)
  · have heq : FourierTransformInv.fourierInv ψ = fun t => FourierTransform.fourier ψ (-t) :=
      funext (fourierInv_neg_eq ψ)
    rw [heq]
    exact hcontF.comp continuous_neg
  · intro t
    rw [fourierInv_neg_eq]
    simpa only [div_eq_mul_inv, neg_sq] using hdec (-t)
  · intro ξ hξ
    have h := Continuous.fourier_fourierInv_eq hC.continuous hintψ hintFψ
    rw [h]
    exact hone ξ hξ


/-- Harmonic tail bound `∑_{k=1}^{n+1} k⁻² ≤ 2 - 1/(n+1)`. -/
private lemma sum_Icc_inv_sq_le_aux (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 (n + 1), ((k : ℝ))⁻¹ ^ 2 ≤ 2 - ((n : ℝ) + 1)⁻¹ := by
  induction n with
  | zero =>
      norm_num
  | succ m ih =>
      rw [show m + 1 + 1 = (m + 1) + 1 from rfl]
      have h1 : 1 ≤ m + 1 + 1 := by omega
      rw [Finset.sum_Icc_succ_top h1]
      have hstep : (((m + 1 + 1 : ℕ) : ℝ))⁻¹ ^ 2 ≤ ((m : ℝ) + 1)⁻¹ - ((m : ℝ) + 1 + 1)⁻¹ := by
        have ha : (0:ℝ) < (m:ℝ) + 1 := by positivity
        have hb : (0:ℝ) < (m:ℝ) + 1 + 1 := by positivity
        have hc : ((m:ℝ) + 1)⁻¹ - ((m:ℝ) + 1 + 1)⁻¹
            = (((m:ℝ) + 1) * ((m:ℝ) + 1 + 1))⁻¹ := by
          field_simp
          ring
        rw [hc, inv_pow]
        rw [← one_div, ← one_div]
        have hle : ((m:ℝ) + 1) * ((m:ℝ) + 1 + 1) ≤ (((m + 1 + 1 : ℕ) : ℝ)) ^ 2 := by
          push_cast
          nlinarith
        exact one_div_le_one_div_of_le (by positivity) hle
      push_cast
      push_cast at hstep
      linarith


/-- Harmonic tail bound `∑_{k=1}^{n} k⁻² ≤ 2` on the integers. -/
private lemma sum_Icc_inv_sq_le (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, ((k : ℝ))⁻¹ ^ 2 ≤ 2 := by
  match n with
  | 0 => norm_num
  | (m + 1) =>
      have h := sum_Icc_inv_sq_le_aux m
      have h1 : (0:ℝ) < (m:ℝ) + 1 := by positivity
      linarith [inv_pos.mpr h1]


/-- Harmonic tail on the positive integers `ℤ ∩ [1,∞)`. -/
private lemma sum_inv_sq_int_pos (s : Finset ℤ) (h : ∀ j ∈ s, 1 ≤ j) :
    ∑ j ∈ s, ((j : ℝ))⁻¹ ^ 2 ≤ 2 := by
  classical
  set f : ℤ → ℕ := fun j => j.toNat with hf
  have hfval : ∀ j ∈ s, ((f j : ℝ)) = (j : ℝ) := by
    intro j hj
    have h1 : 0 ≤ j := by linarith [h j hj]
    have h2 : ((j.toNat : ℤ)) = j := Int.toNat_of_nonneg h1
    have h3 : ((f j : ℤ)) = j := by rw [hf]; exact h2
    exact_mod_cast h3
  have hinj : ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b := by
    intro a ha b hb hab
    have h1 := hfval a ha
    have h2 := hfval b hb
    have h3 : (a : ℝ) = (b : ℝ) := by rw [← h1, ← h2, hab]
    exact_mod_cast h3
  have himg : ∑ j ∈ s, ((j : ℝ))⁻¹ ^ 2 = ∑ k ∈ s.image f, ((k : ℝ))⁻¹ ^ 2 := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun j hj => by rw [hfval j hj]
  rw [himg]
  set M := (s.image f).sup id with hM
  have hmem : ∀ k ∈ s.image f, k ≤ M := by
    intro k hk
    exact Finset.le_sup (f := id) hk
  have hge : ∀ k ∈ s.image f, 1 ≤ k := by
    intro k hk
    obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp hk
    have := h j hj
    have hcast : j ≥ 1 := this
    rw [← hjk]
    have : (1:ℤ) ≤ j := hcast
    have hnf : (f j) = j.toNat := rfl
    rw [hnf]
    omega
  have hsub : s.image f ⊆ Finset.Icc 1 M := by
    intro k hk
    exact Finset.mem_Icc.mpr ⟨hge k hk, hmem k hk⟩
  have hnn : ∀ k ∈ Finset.Icc 1 M, k ∉ s.image f → 0 ≤ ((k : ℝ))⁻¹ ^ 2 := by
    intro k _ _
    positivity
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn) (sum_Icc_inv_sq_le M)


/-- Harmonic tail on the negative integers `ℤ ∩ (-∞,-1]`. -/
private lemma sum_inv_sq_int_neg (s : Finset ℤ) (h : ∀ j ∈ s, j ≤ -1) :
    ∑ j ∈ s, ((j : ℝ))⁻¹ ^ 2 ≤ 2 := by
  classical
  have hinj : ∀ a ∈ s, ∀ b ∈ s, (fun j : ℤ => -j) a = (fun j : ℤ => -j) b → a = b := by
    intro a _ b _ hab
    simp only at hab
    linarith
  have hstep : ∑ j ∈ s, ((j : ℝ))⁻¹ ^ 2 = ∑ j ∈ s.image (fun j : ℤ => -j), ((j : ℝ))⁻¹ ^ 2 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hcast : ((-j : ℤ) : ℝ) = -(j : ℝ) := by push_cast; ring
    rw [hcast, inv_neg, neg_sq]
  rw [hstep]
  refine sum_inv_sq_int_pos _ (fun j hj => ?_)
  obtain ⟨i, hi, hji⟩ := Finset.mem_image.mp hj
  rw [← hji]
  have hle := h i hi
  omega


/-- The exponential character is multiplicative. -/
private lemma eC_add (a b : ℝ) : eC a * eC b = eC (a + b) := by
  unfold LeanLab.ExceptionalSet.U1539.eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring


/-- `𝓕` as an explicit integral against `eC`. -/
private lemma fourier_eq_integral_eC (f : ℝ → ℂ) (w : ℝ) :
    FourierTransform.fourier f w = ∫ v, eC (-(v * w)) * f v := by
  rw [Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only []
  have h1 : (-inner ℝ v w) = -(v * w) := by simp [mul_comm]
  rw [h1, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  unfold LeanLab.ExceptionalSet.U1539.eC
  congr 1
  push_cast
  ring


/-- Fourier inversion in the form used below. -/
private lemma ftR_inversion (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (x : ℝ) :
    K x = ∫ ξ, ftR K ξ * eC (x * ξ) := by
  have hĝ : Integrable (FourierTransform.fourier K) := by
    rw [← ftR_eq_fourier K]
    exact integrable_ftR K hK hcont hsupp
  have hf : FourierTransformInv.fourierInv (FourierTransform.fourier K) = K :=
    Continuous.fourierInv_fourier_eq hcont hK hĝ
  conv_lhs => rw [← hf]
  rw [Real.fourierInv_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only []
  rw [ftR_eq_fourier K]
  have h1 : inner ℝ ξ x = x * ξ := by simp [mul_comm]
  rw [h1, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply, mul_comm]
  unfold LeanLab.ExceptionalSet.U1539.eC
  congr 1
  push_cast
  ring


/-- The convolution representation: a bandlimited integrable kernel is the convolution of
itself with the rapidly decaying inverse transform `φ` of the bump.  This is where the decay
that makes the shifts of `K` summable comes from. -/
private lemma K_eq_convolution (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    ∃ (φ : ℝ → ℂ) (B : ℝ), 0 ≤ B ∧ Integrable φ ∧ Continuous φ ∧
      (∀ t : ℝ, ‖φ t‖ ≤ B / (1 + t ^ 2)) ∧ ∀ x : ℝ, K x = ∫ y, φ y * K (x - y) := by
  obtain ⟨φ, B, hB, hφint, hφcont, hφdec, hφfour⟩ := exists_kernel
  refine ⟨φ, B, hB, hφint, hφcont, hφdec, fun x => ?_⟩
  have hĝ : Integrable (ftR K) := integrable_ftR K hK hcont hsupp
  set F : ℝ → ℝ → ℂ := fun ξ y => eC (-(y * ξ)) * φ y * (ftR K ξ * eC (x * ξ)) with hF
  have hak : ∀ y ξ : ℝ, F ξ y = φ y * (ftR K ξ * eC ((x - y) * ξ)) := by
    intro y ξ
    simp only [hF]
    have h2 : eC (-(y * ξ)) * eC (x * ξ) = eC ((x - y) * ξ) := by
      rw [eC_add]
      congr 1
      ring
    calc eC (-(y * ξ)) * φ y * (ftR K ξ * eC (x * ξ))
        = φ y * (ftR K ξ * (eC (-(y * ξ)) * eC (x * ξ))) := by ring
      _ = φ y * (ftR K ξ * eC ((x - y) * ξ)) := by rw [h2]
  have hprod : Integrable (Function.uncurry F) (volume.prod volume) := by
    have hchar : Continuous fun p : ℝ × ℝ => eC (-(p.2 * p.1)) * eC (x * p.1) := by
      unfold LeanLab.ExceptionalSet.U1539.eC
      fun_prop
    have h1 : Integrable (fun p : ℝ × ℝ => ftR K p.1 * φ p.2) (volume.prod volume) :=
      hĝ.mul_prod hφint
    have hbound : Integrable (fun p : ℝ × ℝ => ‖ftR K p.1‖ * ‖φ p.2‖) (volume.prod volume) :=
      hĝ.norm.mul_prod hφint.norm
    have hF' : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
      have hm : AEStronglyMeasurable
          ((fun p : ℝ × ℝ => eC (-(p.2 * p.1)) * eC (x * p.1)) *
            fun p : ℝ × ℝ => ftR K p.1 * φ p.2)
          (volume.prod volume) :=
        hchar.aestronglyMeasurable.mul h1.aestronglyMeasurable
      refine hm.congr ?_
      filter_upwards with p
      obtain ⟨a, b⟩ := p
      simp only [hF, Function.uncurry_apply_pair, Pi.mul_apply]
      ring
    have hnormeq : (fun p : ℝ × ℝ => ‖Function.uncurry F p‖)
        = fun p : ℝ × ℝ => ‖ftR K p.1‖ * ‖φ p.2‖ := by
      funext p
      obtain ⟨a, b⟩ := p
      simp only [hF, Function.uncurry_apply_pair, norm_mul, eC_norm, mul_one]
      ring
    have hnn : Integrable (fun p : ℝ × ℝ => ‖Function.uncurry F p‖) (volume.prod volume) := by
      rw [hnormeq]
      exact hbound
    exact (integrable_norm_iff hF').mp hnn
  have hstep1 : (∫ ξ, ftR K ξ * eC (x * ξ))
      = ∫ ξ, FourierTransform.fourier φ ξ * (ftR K ξ * eC (x * ξ)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only []
    rcases lt_or_ge (1 : ℝ) |ξ| with hlt | hle
    · rw [hsupp ξ hlt]; ring
    · rw [hφfour ξ hle, one_mul]
  have hstep2 : (∫ ξ, FourierTransform.fourier φ ξ * (ftR K ξ * eC (x * ξ)))
      = ∫ ξ, (∫ y, eC (-(y * ξ)) * φ y) * (ftR K ξ * eC (x * ξ)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only []
    rw [fourier_eq_integral_eC]
  rw [ftR_inversion K hK hcont hsupp x, hstep1, hstep2]
  have hshape : (∫ ξ, (∫ y, eC (-(y * ξ)) * φ y) * (ftR K ξ * eC (x * ξ)))
      = ∫ ξ, ∫ y, F ξ y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hF]
    exact (integral_mul_const _ _).symm
  rw [hshape, integral_integral_swap hprod]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hinner : (∫ ξ, F ξ y) = φ y * K (x - y) := by
    rw [show (∫ ξ, F ξ y) = ∫ ξ, φ y * (ftR K ξ * eC ((x - y) * ξ)) from
      integral_congr_ae (Filter.Eventually.of_forall fun ξ => hak y ξ)]
    rw [integral_const_mul, ftR_inversion K hK hcont hsupp (x - y)]
  exact hinner


/-- Reciprocal squares over the non-zero integers of a finite set. -/
private lemma sum_inv_sq_int_ne_zero (s : Finset ℤ) :
    ∑ j ∈ s.filter (fun j => j ≠ 0), 4 * ((j : ℝ))⁻¹ ^ 2 ≤ 16 := by
  classical
  have hsplit : s.filter (fun j => j ≠ 0)
      = s.filter (fun j => 1 ≤ j) ∪ s.filter (fun j => j ≤ -1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hmem, hne⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inr ⟨hmem, by omega⟩
      · exact Or.inl ⟨hmem, by omega⟩
    · rintro (⟨hmem, h⟩ | ⟨hmem, h⟩)
      · exact ⟨hmem, by omega⟩
      · exact ⟨hmem, by omega⟩
  rw [hsplit, Finset.sum_union]
  · have hp := sum_inv_sq_int_pos (s.filter (fun j => 1 ≤ j))
      (fun j hj => (Finset.mem_filter.mp hj).2)
    have hn := sum_inv_sq_int_neg (s.filter (fun j => j ≤ -1))
      (fun j hj => (Finset.mem_filter.mp hj).2)
    have hp4 : ∑ j ∈ s.filter (fun j => 1 ≤ j), 4 * ((j : ℝ))⁻¹ ^ 2
        = 4 * ∑ j ∈ s.filter (fun j => 1 ≤ j), ((j : ℝ))⁻¹ ^ 2 := (Finset.mul_sum ..).symm
    have hn4 : ∑ j ∈ s.filter (fun j => j ≤ -1), 4 * ((j : ℝ))⁻¹ ^ 2
        = 4 * ∑ j ∈ s.filter (fun j => j ≤ -1), ((j : ℝ))⁻¹ ^ 2 := (Finset.mul_sum ..).symm
    rw [hp4, hn4]
    linarith
  · refine Finset.disjoint_left.mpr ?_
    intro j hj1 hj2
    have h1 := (Finset.mem_filter.mp hj1).2
    have h2 := (Finset.mem_filter.mp hj2).2
    omega


/-- Away from zero the shift kernel is dominated by the reciprocal square. -/
private lemma inv_one_add_sq_div_four_le (j : ℤ) (hj : j ≠ 0) :
    (1 + (j : ℝ) ^ 2 / 4)⁻¹ ≤ 4 * ((j : ℝ) ^ 2)⁻¹ := by
  have hjnz : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  have hpos : (0 : ℝ) < (j : ℝ) ^ 2 := by positivity
  have h4 : (0 : ℝ) < 4 + (j : ℝ) ^ 2 := by positivity
  have h1 : (1 + (j : ℝ) ^ 2 / 4) = (4 + (j : ℝ) ^ 2) / 4 := by ring
  have h2 : ((4 + (j : ℝ) ^ 2) / 4)⁻¹ = 4 * (4 + (j : ℝ) ^ 2)⁻¹ := by
    rw [inv_div, div_eq_mul_inv]
  rw [h1, h2]
  have hle : (j : ℝ) ^ 2 ≤ 4 + (j : ℝ) ^ 2 := by linarith
  calc 4 * (4 + (j : ℝ) ^ 2)⁻¹ ≤ 4 * ((j : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ hpos hle) (by norm_num)


/-- The shift lattice is sparse: `∑_{n ∈ s} (1 + (v+n)²)⁻¹ ≤ 17`, uniformly in the shift `v`.
This is the estimate that makes the shifts of `K` summable once `K` is a convolution with a
quadratically decaying kernel. -/
private lemma sum_inv_one_add_sq_shift (v : ℝ) (s : Finset ℤ) :
    ∑ n ∈ s, (1 + (v + n) ^ 2)⁻¹ ≤ 17 := by
  classical
  set m : ℤ := ⌊v + (1 / 2 : ℝ)⌋ with hm
  set c : ℝ := v - (m : ℝ) with hc
  have hc1 : -(1 / 2 : ℝ) ≤ c := by
    have h : ((m : ℤ) : ℝ) ≤ v + 1 / 2 := by
      simpa only [hm] using Int.floor_le (v + 1 / 2)
    simp only [hc]
    linarith
  have hc2 : c < 1 / 2 := by
    have h : v + 1 / 2 < ((m : ℤ) : ℝ) + 1 := by
      simpa only [hm] using Int.lt_floor_add_one (v + 1 / 2)
    simp only [hc]
    linarith
  have hinj : ∀ a ∈ s, ∀ b ∈ s, a + m = b + m → a = b := by
    intro a _ b _ hab
    omega
  have hreindex : ∑ n ∈ s, (1 + (v + n) ^ 2)⁻¹
      = ∑ j ∈ s.image (fun n : ℤ => n + m), (1 + (c + (j : ℝ)) ^ 2)⁻¹ := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 2
    rw [hc]
    push_cast
    ring
  rw [hreindex]
  have hcj : ∀ j : ℤ, (j : ℝ) ^ 2 / 4 ≤ (c + (j : ℝ)) ^ 2 := by
    intro j
    have hcabs : |c| ≤ 1 / 2 := by
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    rcases eq_or_ne j 0 with hj | hj
    · subst hj
      push_cast
      nlinarith [sq_nonneg c]
    · have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
        have h : (1 : ℤ) ≤ |j| := by
          rcases lt_or_gt_of_ne hj with h | h
          · have hle : j ≤ -1 := by omega
            rw [abs_of_nonpos (by omega)]
            omega
          · have hge : 1 ≤ j := by omega
            rw [abs_of_nonneg (by omega)]
            omega
        exact_mod_cast h
      have h3 : |(j : ℝ)| - |c| ≤ |c + (j : ℝ)| := by
        have h := abs_sub_abs_le_abs_sub (j : ℝ) (-c)
        simpa [abs_neg, sub_eq_add_neg, add_comm] using h
      have h4 : |(j : ℝ)| / 2 ≤ |c + (j : ℝ)| := by linarith
      have h5 : (0:ℝ) ≤ |(j : ℝ)| / 2 := by positivity
      nlinarith [sq_abs (c + (j : ℝ)), sq_abs (j : ℝ), sq_nonneg (|(j : ℝ)| / 2),
        sq_nonneg (|c + (j : ℝ)|)]
  have hterm : ∀ j ∈ s.image (fun n : ℤ => n + m),
      (1 + (c + (j : ℝ)) ^ 2)⁻¹ ≤ (1 + (j : ℝ) ^ 2 / 4)⁻¹ := by
    intro j _
    have hden : 1 + (j : ℝ) ^ 2 / 4 ≤ 1 + (c + (j : ℝ)) ^ 2 := by linarith [hcj j]
    have hp : (0:ℝ) < 1 + (j : ℝ) ^ 2 / 4 := by positivity
    have h := one_div_le_one_div_of_le hp hden
    simpa only [one_div] using h
  set t : Finset ℤ := s.image (fun n : ℤ => n + m) with ht
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have herase : t.erase 0 = t.filter (fun j => j ≠ 0) := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  have hstep : ∑ j ∈ t, (1 + (j : ℝ) ^ 2 / 4)⁻¹ ≤ 1 + ∑ j ∈ t.erase 0, 4 * ((j : ℝ))⁻¹ ^ 2 := by
    by_cases h0 : (0 : ℤ) ∈ t
    · have hs : ∑ j ∈ t.erase 0, (1 + (j : ℝ) ^ 2 / 4)⁻¹ + (1 + ((0:ℤ) : ℝ) ^ 2 / 4)⁻¹
          = ∑ j ∈ t, (1 + (j : ℝ) ^ 2 / 4)⁻¹ :=
        Finset.sum_erase_add (s := t) (f := fun j : ℤ => (1 + (j : ℝ) ^ 2 / 4)⁻¹) h0
      rw [← hs]
      have hf0 : (1 + ((0:ℤ) : ℝ) ^ 2 / 4)⁻¹ = 1 := by norm_num
      rw [hf0]
      have hb : ∀ j ∈ t.erase 0, (1 + (j : ℝ) ^ 2 / 4)⁻¹ ≤ 4 * ((j : ℝ))⁻¹ ^ 2 := by
        intro j hj
        have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
        calc (1 + (j : ℝ) ^ 2 / 4)⁻¹ ≤ 4 * ((j : ℝ) ^ 2)⁻¹ := inv_one_add_sq_div_four_le j hj0
          _ = 4 * ((j : ℝ))⁻¹ ^ 2 := by rw [inv_pow]
      linarith [Finset.sum_le_sum hb]
    · have hs : t.erase 0 = t := by
        ext j
        simp only [Finset.mem_erase]
        constructor
        · rintro ⟨-, h⟩; exact h
        · intro h
          exact ⟨by rintro rfl; exact h0 h, h⟩
      rw [hs]
      have hb : ∀ j ∈ t, (1 + (j : ℝ) ^ 2 / 4)⁻¹ ≤ 4 * ((j : ℝ))⁻¹ ^ 2 := by
        intro j hj
        have hj0 : j ≠ 0 := by
          intro h; exact h0 (h ▸ hj)
        calc (1 + (j : ℝ) ^ 2 / 4)⁻¹ ≤ 4 * ((j : ℝ) ^ 2)⁻¹ := inv_one_add_sq_div_four_le j hj0
          _ = 4 * ((j : ℝ))⁻¹ ^ 2 := by rw [inv_pow]
      have hsum := Finset.sum_le_sum hb
      linarith
  rw [herase] at hstep
  linarith [sum_inv_sq_int_ne_zero t]


/-- Summability of the unit shifts of `K`, with an explicit bound.  This is exactly the
hypothesis Mathlib's Poisson summation needs, and it comes from `K = φ * K` together with the
sparsity of the shift lattice. -/
private lemma shift_summable (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ∀ s : Finset ℤ, ∑ n ∈ s, ‖K (x + n)‖ ≤ C := by
  obtain ⟨φ, B, hB, hφint, hφcont, hφdec, hφfour⟩ := K_eq_convolution K hK hcont hsupp
  have hφB : ∀ t : ℝ, ‖φ t‖ ≤ B := by
    intro t
    refine (hφdec t).trans ?_
    have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
    rw [div_le_iff₀ hpos]
    nlinarith [hB]
  have hgint : ∀ c : ℝ, Integrable (fun z : ℝ => ‖φ (c - z)‖ * ‖K z‖) := by
    intro c
    refine Integrable.mono' (hK.norm.const_mul B) ?_ ?_
    · exact (((hφcont.comp (continuous_const.sub continuous_id)).norm).aestronglyMeasurable).mul
        hK.norm.aestronglyMeasurable
    · filter_upwards with z
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_norm]
      exact mul_le_mul_of_nonneg_right (hφB (c - z)) (norm_nonneg _)
  refine ⟨17 * B * ∫ z, ‖K z‖, ?_, fun x s => ?_⟩
  · have h1 : (0:ℝ) ≤ ∫ z, ‖K z‖ := integral_nonneg fun z => norm_nonneg _
    have h2 : (0:ℝ) ≤ B := hB
    nlinarith
  · -- change the variable in each summand so that the decay acts on the shift
    have hterm : ∀ n : ℤ, ‖K (x + (n:ℝ))‖ ≤ ∫ z, ‖φ (x + (n:ℝ) - z)‖ * ‖K z‖ := by
      intro n
      have h1 : K (x + (n:ℝ)) = ∫ y, φ y * K (x + (n:ℝ) - y) := hφfour (x + (n:ℝ))
      calc ‖K (x + (n:ℝ))‖ = ‖∫ y, φ y * K (x + (n:ℝ) - y)‖ := by rw [h1]
        _ ≤ ∫ y, ‖φ y * K (x + (n:ℝ) - y)‖ := norm_integral_le_integral_norm _
        _ = ∫ y, ‖φ y‖ * ‖K (x + (n:ℝ) - y)‖ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            simp only [norm_mul]
        _ = ∫ z, ‖φ (x + (n:ℝ) - z)‖ * ‖K z‖ := by
            have hcv : (∫ y : ℝ, ‖φ y‖ * ‖K (x + (n:ℝ) - y)‖)
                = ∫ z : ℝ, ‖φ (x + (n:ℝ) - z)‖ * ‖K z‖ := by
              simpa using (MeasureTheory.integral_sub_left_eq_self
                (fun z : ℝ => ‖φ (x + (n:ℝ) - z)‖ * ‖K z‖) (volume : Measure ℝ) (x + (n:ℝ)))
            exact hcv
    refine le_trans (Finset.sum_le_sum fun n _ => hterm n) ?_
    have hsumint : ∑ n ∈ s, ∫ z, ‖φ (x + (n:ℝ) - z)‖ * ‖K z‖
        = ∫ z, ∑ n ∈ s, ‖φ (x + (n:ℝ) - z)‖ * ‖K z‖ := by
      refine (integral_finsetSum s ?_).symm
      intro n _
      exact hgint (x + (n:ℝ))
    rw [hsumint]
    have hinner : ∀ z : ℝ, ∑ n ∈ s, ‖φ (x + (n:ℝ) - z)‖ * ‖K z‖ ≤ 17 * B * ‖K z‖ := by
      intro z
      have hsplit : ∑ n ∈ s, ‖φ (x + (n:ℝ) - z)‖ * ‖K z‖
          = (∑ n ∈ s, ‖φ ((x - z) + (n:ℝ))‖) * ‖K z‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun n _ => ?_
        congr 2
        ring
      rw [hsplit]
      have hb : ∑ n ∈ s, ‖φ ((x - z) + (n:ℝ))‖ ≤ 17 * B := by
        have h1 : ∑ n ∈ s, ‖φ ((x - z) + (n:ℝ))‖
            ≤ ∑ n ∈ s, B * (1 + ((x - z) + (n:ℝ)) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun n _ => ?_
          calc ‖φ ((x - z) + (n:ℝ))‖ ≤ B / (1 + ((x - z) + (n:ℝ)) ^ 2) := hφdec _
            _ = B * (1 + ((x - z) + (n:ℝ)) ^ 2)⁻¹ := by rw [div_eq_mul_inv]
        have h2 : ∑ n ∈ s, B * (1 + ((x - z) + (n:ℝ)) ^ 2)⁻¹
            = B * ∑ n ∈ s, (1 + ((x - z) + (n:ℝ)) ^ 2)⁻¹ := (Finset.mul_sum ..).symm
        have h3 := sum_inv_one_add_sq_shift (x - z) s
        rw [h2] at h1
        nlinarith [h1, h3, hB]
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    have hint1 : Integrable (fun z : ℝ => ∑ n ∈ s, ‖φ (x + (n:ℝ) - z)‖ * ‖K z‖) :=
      integrable_finsetSum s (fun n _ => hgint (x + (n:ℝ)))
    have hint2 : Integrable (fun z : ℝ => 17 * B * ‖K z‖) := hK.norm.const_mul (17 * B)
    calc ∫ z, (∑ n ∈ s, ‖φ (x + (n:ℝ) - z)‖ * ‖K z‖) ≤ ∫ z, 17 * B * ‖K z‖ :=
          integral_mono_ae hint1 hint2 (Filter.Eventually.of_forall hinner)
      _ = 17 * B * ∫ z, ‖K z‖ := integral_const_mul ..


/-- The quadratic kernel with a one-sided slack dominates the plain one, uniformly in `R`. -/
private lemma inv_sq_slack (s R : ℝ) (hR : 0 ≤ R) :
    (4 * (1 + R ^ 2))⁻¹ * (1 + s ^ 2) ≤ 1 + max 0 (|s| - R) ^ 2 := by
  have hpos : (0:ℝ) < 4 * (1 + R ^ 2) := by positivity
  have hmax : (0:ℝ) ≤ max 0 (|s| - R) ^ 2 := by positivity
  have habs2 : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
  have key : (1 + s ^ 2) / (4 * (1 + R ^ 2)) ≤ 1 + max 0 (|s| - R) ^ 2 := by
    rcases lt_or_ge (2 * R) |s| with hgt | hle
    · have h1 : |s| / 2 ≤ |s| - R := by linarith
      have h3 : |s| / 2 ≤ max 0 (|s| - R) := le_trans h1 (le_max_right _ _)
      have h4 : (|s| / 2) ^ 2 ≤ max 0 (|s| - R) ^ 2 := by nlinarith [abs_nonneg s]
      have h5 : s ^ 2 / 4 ≤ max 0 (|s| - R) ^ 2 := by
        rw [habs2]
        nlinarith [h4]
      have h6 : (1 + s ^ 2) / (4 * (1 + R ^ 2)) ≤ (1 + s ^ 2) / 4 := by
        have h7 : (1 + s ^ 2) / (4 * (1 + R ^ 2)) = ((1 + s ^ 2) / 4) * (1 / (1 + R ^ 2)) := by
          field_simp
        have h8 : (1 / (1 + R ^ 2) : ℝ) ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith [sq_nonneg R]
        have h9 : (0:ℝ) ≤ (1 + s ^ 2) / 4 := by positivity
        rw [h7]
        calc ((1 + s ^ 2) / 4) * (1 / (1 + R ^ 2)) ≤ ((1 + s ^ 2) / 4) * 1 :=
              mul_le_mul_of_nonneg_left h8 h9
          _ = (1 + s ^ 2) / 4 := by ring
      have h10 : (1 + s ^ 2) / 4 ≤ 1 + max 0 (|s| - R) ^ 2 := by linarith
      linarith
    · have hs2 : s ^ 2 ≤ 4 * R ^ 2 := by
        rw [habs2]
        nlinarith [hle, abs_nonneg s]
      have h6 : (1 + s ^ 2) / (4 * (1 + R ^ 2)) ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith
      linarith
  rw [inv_mul_eq_div]
  exact key


/-- Away from the origin the slacked kernel is comparable with the plain one. -/
private lemma inv_slack_le (s R : ℝ) (hR : 0 ≤ R) :
    (1 + max 0 (|s| - R) ^ 2)⁻¹ ≤ (4 * (1 + R ^ 2)) * (1 + s ^ 2)⁻¹ := by
  have hc : (0:ℝ) < 4 * (1 + R ^ 2) := by positivity
  have hS : (0:ℝ) < 1 + s ^ 2 := by positivity
  have hD : (0:ℝ) < 1 + max 0 (|s| - R) ^ 2 := by positivity
  have h1 := inv_sq_slack s R hR
  have h2 : (1 + s ^ 2) ≤ (4 * (1 + R ^ 2)) * (1 + max 0 (|s| - R) ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left h1 (le_of_lt hc)
    calc (1 + s ^ 2) = (4 * (1 + R ^ 2)) * ((4 * (1 + R ^ 2))⁻¹ * (1 + s ^ 2)) := by
          field_simp
      _ ≤ _ := hmul
  have h3 : (1 + s ^ 2) / (4 * (1 + R ^ 2)) ≤ 1 + max 0 (|s| - R) ^ 2 := by
    rw [div_le_iff₀ hc]
    linarith
  have h4 : (0:ℝ) < (1 + s ^ 2) / (4 * (1 + R ^ 2)) := by positivity
  have hstep : (1 + max 0 (|s| - R) ^ 2)⁻¹ ≤ ((1 + s ^ 2) / (4 * (1 + R ^ 2)))⁻¹ :=
    by simpa only [one_div] using one_div_le_one_div_of_le h4 h3
  calc (1 + max 0 (|s| - R) ^ 2)⁻¹ ≤ ((1 + s ^ 2) / (4 * (1 + R ^ 2)))⁻¹ := hstep
    _ = (4 * (1 + R ^ 2)) * (1 + s ^ 2)⁻¹ := by
        rw [inv_div, div_eq_mul_inv]


/-- Pointwise, the kernel with slack dominates the modulated inverse transform. -/
private lemma phi_slack_le (φ : ℝ → ℂ) (B R : ℝ) (hB : 0 ≤ B)
    (hφdec : ∀ t : ℝ, ‖φ t‖ ≤ B / (1 + t ^ 2))
    (K : ℝ → ℂ) (x : ℝ) (hx : |x| ≤ R) (n : ℤ) (z : ℝ) :
    ‖φ (x + (n:ℝ) - z)‖ * ‖K z‖
      ≤ B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖ := by
  have h1 : |(n:ℝ) - z| - |x| ≤ |x + (n:ℝ) - z| := by
    have h := abs_sub_abs_le_abs_sub ((n:ℝ) - z) (-x)
    have h' : |(n:ℝ) - z| - |x| ≤ |(n:ℝ) - z + x| := by
      simpa [abs_neg, sub_eq_add_neg, add_comm] using h
    have h'' : ((n:ℝ) - z) + x = x + (n:ℝ) - z := by ring
    rwa [h''] at h'
  have h2 : max 0 (|(n:ℝ) - z| - R) ≤ |x + (n:ℝ) - z| :=
    max_le (abs_nonneg _) (by linarith)
  have h3 : max 0 (|(n:ℝ) - z| - R) ≤ |x + (n:ℝ) - z| := h2
  have h4 : (max 0 (|(n:ℝ) - z| - R)) ^ 2 ≤ (x + (n:ℝ) - z) ^ 2 := by
    have hpos := le_max_left (0:ℝ) (|(n:ℝ) - z| - R)
    nlinarith [sq_abs (x + (n:ℝ) - z), abs_nonneg (x + (n:ℝ) - z)]
  have hD : (0:ℝ) < 1 + max 0 (|(n:ℝ) - z| - R) ^ 2 := by positivity
  have hinv : (1 + (x + (n:ℝ) - z) ^ 2)⁻¹ ≤ (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ := by
    have hle : 1 + max 0 (|(n:ℝ) - z| - R) ^ 2 ≤ 1 + (x + (n:ℝ) - z) ^ 2 := by linarith
    have h := one_div_le_one_div_of_le hD hle
    simpa only [one_div] using h
  have h5 : ‖φ (x + (n:ℝ) - z)‖ ≤ B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ := by
    calc ‖φ (x + (n:ℝ) - z)‖ ≤ B / (1 + (x + (n:ℝ) - z) ^ 2) := hφdec _
      _ = B * (1 + (x + (n:ℝ) - z) ^ 2)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hinv hB
  calc ‖φ (x + (n:ℝ) - z)‖ * ‖K z‖
      ≤ (B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹) * ‖K z‖ :=
        mul_le_mul_of_nonneg_right h5 (norm_nonneg _)
    _ = B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖ := by ring


/-- Summability of the shifts, uniformly on a compact: the hypothesis Mathlib's Poisson
summation needs.  The slack `R` in the kernel is what makes the estimate local. -/
private lemma shift_sup_summable (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : Finset ℤ,
      ∑ n ∈ s, (⨆ x : Set.Icc (-R) R, ‖K ((x:ℝ) + (n:ℝ))‖) ≤ C := by
  obtain ⟨φ, B, hB, hφint, hφcont, hφdec, hφfour⟩ := K_eq_convolution K hK hcont hsupp
  have hφB : ∀ t : ℝ, ‖φ t‖ ≤ B := by
    intro t
    refine (hφdec t).trans ?_
    have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
    rw [div_le_iff₀ hpos]
    nlinarith [hB]
  have hker : ∀ n : ℤ,
      Integrable (fun z : ℝ => B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖) := by
    intro n
    have hcont1 : Continuous fun z : ℝ => B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ := by
      have hc : Continuous fun t : ℝ => B * (1 + max 0 (|t| - R) ^ 2)⁻¹ := by
        have h1 : Continuous fun t : ℝ => (1 + max 0 (|t| - R) ^ 2) := by fun_prop
        exact continuous_const.mul (h1.inv₀ fun t => ne_of_gt (by positivity))
      have hcomp' : Continuous
          fun z : ℝ => (fun t : ℝ => B * (1 + max 0 (|t| - R) ^ 2)⁻¹) ((n:ℝ) - z) :=
        hc.comp (show Continuous fun z : ℝ => (n:ℝ) - z by fun_prop)
      exact hcomp'
    refine Integrable.mono' (hK.norm.const_mul B) ?_ ?_
    · exact hcont1.aestronglyMeasurable.mul hK.norm.aestronglyMeasurable
    · filter_upwards with z
      have h1 : (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ (by positivity)]
        have h2 : (0:ℝ) ≤ max 0 (|(n:ℝ) - z| - R) ^ 2 := by positivity
        linarith
      have h2 : ‖B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖‖
          = B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖ := by
        rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hB,
          abs_of_nonneg (inv_nonneg.mpr (by positivity)), norm_norm]
      rw [h2]
      have h3 : B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖ ≤ B * 1 * ‖K z‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hB) (norm_nonneg (K z))
      linarith [h3]
  haveI : Nonempty (Set.Icc (-R : ℝ) R) :=
    ⟨⟨0, by rw [Set.mem_Icc]; exact ⟨by linarith, hR⟩⟩⟩
  have hsup : ∀ n : ℤ, (⨆ x : Set.Icc (-R) R, ‖K ((x:ℝ) + (n:ℝ))‖)
      ≤ ∫ z, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖ := by
    intro n
    refine ciSup_le fun x => ?_
    have hx' : |(x:ℝ)| ≤ R := by
      have hx := x.2
      rw [Set.mem_Icc] at hx
      exact abs_le.mpr ⟨hx.1, hx.2⟩
    have h1 : K ((x:ℝ) + (n:ℝ)) = ∫ y, φ y * K ((x:ℝ) + (n:ℝ) - y) := hφfour _
    calc ‖K ((x:ℝ) + (n:ℝ))‖ = ‖∫ y, φ y * K ((x:ℝ) + (n:ℝ) - y)‖ := by rw [h1]
      _ ≤ ∫ y, ‖φ y * K ((x:ℝ) + (n:ℝ) - y)‖ := norm_integral_le_integral_norm _
      _ = ∫ y, ‖φ y‖ * ‖K ((x:ℝ) + (n:ℝ) - y)‖ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [norm_mul]
      _ = ∫ z, ‖φ ((x:ℝ) + (n:ℝ) - z)‖ * ‖K z‖ := by
          have hcv : (∫ y : ℝ, ‖φ y‖ * ‖K ((x:ℝ) + (n:ℝ) - y)‖)
              = ∫ z : ℝ, ‖φ ((x:ℝ) + (n:ℝ) - z)‖ * ‖K z‖ := by
            simpa using (MeasureTheory.integral_sub_left_eq_self
              (fun z : ℝ => ‖φ ((x:ℝ) + (n:ℝ) - z)‖ * ‖K z‖) (volume : Measure ℝ) ((x:ℝ) + (n:ℝ)))
          exact hcv
      _ ≤ ∫ z, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖ := by
          refine integral_mono_ae ?_ (hker n) (Filter.Eventually.of_forall fun z => ?_)
          · refine Integrable.mono' (hK.norm.const_mul B) ?_ ?_
            · exact (((hφcont.comp (show Continuous fun z : ℝ => (x:ℝ) + (n:ℝ) - z by fun_prop)).norm).aestronglyMeasurable).mul
                hK.norm.aestronglyMeasurable
            · filter_upwards with z
              rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_norm]
              exact mul_le_mul_of_nonneg_right (hφB _) (norm_nonneg _)
          · exact phi_slack_le φ B R hB hφdec K (x:ℝ) hx' n z
  refine ⟨B * (4 * (1 + R ^ 2)) * 17 * ∫ z, ‖K z‖, ?_, fun s => ?_⟩
  · have h1 : (0:ℝ) ≤ ∫ z, ‖K z‖ := integral_nonneg fun z => norm_nonneg _
    have h2 : (0:ℝ) ≤ 4 * (1 + R ^ 2) := by positivity
    have h3 : (0:ℝ) ≤ B * (4 * (1 + R ^ 2)) := mul_nonneg hB h2
    have h4 : (0:ℝ) ≤ B * (4 * (1 + R ^ 2)) * 17 := mul_nonneg h3 (by norm_num)
    exact mul_nonneg h4 h1
  · refine le_trans (Finset.sum_le_sum fun n _ => hsup n) ?_
    have hsumint : ∑ n ∈ s, ∫ z, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖
        = ∫ z, ∑ n ∈ s, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖ := by
      refine (integral_finsetSum s ?_).symm
      intro n _
      exact hker n
    rw [hsumint]
    have hinner : ∀ z : ℝ, ∑ n ∈ s, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖
        ≤ B * (4 * (1 + R ^ 2)) * 17 * ‖K z‖ := by
      intro z
      have h1 : ∑ n ∈ s, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖
          = (∑ n ∈ s, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹) * ‖K z‖ := by
        rw [Finset.sum_mul]
      rw [h1]
      have hstep1 : ∑ n ∈ s, (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹
          ≤ (4 * (1 + R ^ 2)) * ∑ n ∈ s, (1 + ((n:ℝ) - z) ^ 2)⁻¹ := by
        calc ∑ n ∈ s, (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹
            ≤ ∑ n ∈ s, (4 * (1 + R ^ 2)) * (1 + ((n:ℝ) - z) ^ 2)⁻¹ :=
              Finset.sum_le_sum fun n _ => inv_slack_le ((n:ℝ) - z) R hR
          _ = (4 * (1 + R ^ 2)) * ∑ n ∈ s, (1 + ((n:ℝ) - z) ^ 2)⁻¹ := (Finset.mul_sum ..).symm
      have hstep2 : ∑ n ∈ s, (1 + ((n:ℝ) - z) ^ 2)⁻¹ ≤ 17 := by
        rw [show (∑ n ∈ s, (1 + ((n:ℝ) - z) ^ 2)⁻¹)
            = ∑ n ∈ s, (1 + ((-z) + (n:ℝ)) ^ 2)⁻¹ from
          Finset.sum_congr rfl fun n _ => by
            congr 2
            ring]
        exact sum_inv_one_add_sq_shift (-z) s
      have hpos4 : (0:ℝ) ≤ 4 * (1 + R ^ 2) := by positivity
      have h2 : ∑ n ∈ s, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ ≤ B * (4 * (1 + R ^ 2)) * 17 := by
        calc ∑ n ∈ s, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹
            = B * ∑ n ∈ s, (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ := (Finset.mul_sum ..).symm
          _ ≤ B * ((4 * (1 + R ^ 2)) * ∑ n ∈ s, (1 + ((n:ℝ) - z) ^ 2)⁻¹) :=
              mul_le_mul_of_nonneg_left hstep1 hB
          _ ≤ B * ((4 * (1 + R ^ 2)) * 17) := by
              refine mul_le_mul_of_nonneg_left ?_ hB
              exact mul_le_mul_of_nonneg_left hstep2 hpos4
          _ = B * (4 * (1 + R ^ 2)) * 17 := by ring
      exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    have hint1 : Integrable
        (fun z : ℝ => ∑ n ∈ s, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖) :=
      integrable_finsetSum s (fun n _ => hker n)
    have hint2 : Integrable (fun z : ℝ => B * (4 * (1 + R ^ 2)) * 17 * ‖K z‖) :=
      hK.norm.const_mul _
    calc ∫ z, (∑ n ∈ s, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖)
        ≤ ∫ z, B * (4 * (1 + R ^ 2)) * 17 * ‖K z‖ :=
          integral_mono_ae hint1 hint2 (Filter.Eventually.of_forall hinner)
      _ = B * (4 * (1 + R ^ 2)) * 17 * ∫ z, ‖K z‖ := integral_const_mul ..


/-- The exponential characters on the unit circle are the ones of `eC`. -/
private lemma fourier_coe_eq_eC (n : ℤ) (α : ℝ) :
    (fourier n) ((α : ℝ) : UnitAddCircle) = eC (α * (n:ℝ)) := by
  rw [fourier_coe_apply]
  unfold LeanLab.ExceptionalSet.U1539.eC
  congr 1
  push_cast
  ring


/-- The transform of the modulated kernel is the translate of the transform. -/
private lemma fourier_modulated (K : ℝ → ℂ) (v : ℝ) (n : ℤ) :
    FourierTransform.fourier (fun x : ℝ => K x * eC (-(x * v))) ((n:ℝ)) = ftR K (v + (n:ℝ)) := by
  rw [fourier_eq_integral_eC, ftR_eq_fourier K, fourier_eq_integral_eC]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h2 : eC (-(x * (n:ℝ))) * eC (-(x * v)) = eC (-(x * (v + (n:ℝ)))) := by
    rw [eC_add]
    congr 1
    ring
  calc eC (-(x * (n:ℝ))) * (K x * eC (-(x * v)))
      = (eC (-(x * (n:ℝ))) * eC (-(x * v))) * K x := by ring
    _ = eC (-(x * (v + (n:ℝ)))) * K x := by rw [h2]


/-- The shift of the kernel is dominated by the integral of the slacked kernel. -/
private lemma K_shift_le_slack_integral (K : ℝ → ℂ) (hK : Integrable K) (φ : ℝ → ℂ)
    (hφcont : Continuous φ) (B R : ℝ) (hB : 0 ≤ B)
    (hφdec : ∀ t : ℝ, ‖φ t‖ ≤ B / (1 + t ^ 2))
    (hφfour : ∀ x : ℝ, K x = ∫ y, φ y * K (x - y))
    (hker : ∀ n : ℤ,
      Integrable (fun z : ℝ => B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖))
    (x : ℝ) (hx : |x| ≤ R) (n : ℤ) :
    ‖K (x + (n:ℝ))‖ ≤ ∫ z, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖ := by
  have hφB : ∀ t : ℝ, ‖φ t‖ ≤ B := by
    intro t
    refine (hφdec t).trans ?_
    have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
    rw [div_le_iff₀ hpos]
    nlinarith [hB]
  have h1 : K (x + (n:ℝ)) = ∫ y, φ y * K (x + (n:ℝ) - y) := hφfour _
  calc ‖K (x + (n:ℝ))‖ = ‖∫ y, φ y * K (x + (n:ℝ) - y)‖ := by rw [h1]
    _ ≤ ∫ y, ‖φ y * K (x + (n:ℝ) - y)‖ := norm_integral_le_integral_norm _
    _ = ∫ y, ‖φ y‖ * ‖K (x + (n:ℝ) - y)‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [norm_mul]
    _ = ∫ z, ‖φ (x + (n:ℝ) - z)‖ * ‖K z‖ := by
        have hcv : (∫ y : ℝ, ‖φ y‖ * ‖K (x + (n:ℝ) - y)‖)
            = ∫ z : ℝ, ‖φ (x + (n:ℝ) - z)‖ * ‖K z‖ := by
          simpa using (MeasureTheory.integral_sub_left_eq_self
            (fun z : ℝ => ‖φ (x + (n:ℝ) - z)‖ * ‖K z‖) (volume : Measure ℝ) (x + (n:ℝ)))
        exact hcv
    _ ≤ ∫ z, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖ := by
        refine integral_mono_ae ?_ (hker n) (Filter.Eventually.of_forall fun z => ?_)
        · refine Integrable.mono' (hK.norm.const_mul B) ?_ ?_
          · exact (((hφcont.comp (show Continuous fun z : ℝ => x + (n:ℝ) - z by fun_prop)).norm).aestronglyMeasurable).mul
              hK.norm.aestronglyMeasurable
          · filter_upwards with z
            rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_norm]
            exact mul_le_mul_of_nonneg_right (hφB _) (norm_nonneg _)
        · exact phi_slack_le φ B R hB hφdec K x hx n z


/-- The slacked kernel family has bounded finite sums. -/
private lemma slack_integral_sum_le (K : ℝ → ℂ) (hK : Integrable K) (B R : ℝ) (hB : 0 ≤ B)
    (hR : 0 ≤ R)
    (hker : ∀ n : ℤ,
      Integrable (fun z : ℝ => B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖))
    (s : Finset ℤ) :
    ∑ n ∈ s, ∫ z, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖
      ≤ B * (4 * (1 + R ^ 2)) * 17 * ∫ z, ‖K z‖ := by
  have hsumint : ∑ n ∈ s, ∫ z, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖
      = ∫ z, ∑ n ∈ s, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖ := by
    refine (integral_finsetSum s ?_).symm
    intro n _
    exact hker n
  rw [hsumint]
  have hinner : ∀ z : ℝ, ∑ n ∈ s, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖
      ≤ B * (4 * (1 + R ^ 2)) * 17 * ‖K z‖ := by
    intro z
    have h1 : ∑ n ∈ s, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖
        = (∑ n ∈ s, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹) * ‖K z‖ := by
      rw [Finset.sum_mul]
    rw [h1]
    have hstep1 : ∑ n ∈ s, (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹
        ≤ (4 * (1 + R ^ 2)) * ∑ n ∈ s, (1 + ((n:ℝ) - z) ^ 2)⁻¹ := by
      calc ∑ n ∈ s, (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹
          ≤ ∑ n ∈ s, (4 * (1 + R ^ 2)) * (1 + ((n:ℝ) - z) ^ 2)⁻¹ :=
            Finset.sum_le_sum fun n _ => inv_slack_le ((n:ℝ) - z) R hR
        _ = (4 * (1 + R ^ 2)) * ∑ n ∈ s, (1 + ((n:ℝ) - z) ^ 2)⁻¹ := (Finset.mul_sum ..).symm
    have hstep2 : ∑ n ∈ s, (1 + ((n:ℝ) - z) ^ 2)⁻¹ ≤ 17 := by
      rw [show (∑ n ∈ s, (1 + ((n:ℝ) - z) ^ 2)⁻¹)
          = ∑ n ∈ s, (1 + ((-z) + (n:ℝ)) ^ 2)⁻¹ from
        Finset.sum_congr rfl fun n _ => by
          congr 2
          ring]
      exact sum_inv_one_add_sq_shift (-z) s
    have hpos4 : (0:ℝ) ≤ 4 * (1 + R ^ 2) := by positivity
    have h2 : ∑ n ∈ s, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ ≤ B * (4 * (1 + R ^ 2)) * 17 := by
      calc ∑ n ∈ s, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹
          = B * ∑ n ∈ s, (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ := (Finset.mul_sum ..).symm
        _ ≤ B * ((4 * (1 + R ^ 2)) * ∑ n ∈ s, (1 + ((n:ℝ) - z) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left hstep1 hB
        _ ≤ B * ((4 * (1 + R ^ 2)) * 17) := by
            refine mul_le_mul_of_nonneg_left ?_ hB
            exact mul_le_mul_of_nonneg_left hstep2 hpos4
        _ = B * (4 * (1 + R ^ 2)) * 17 := by ring
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have hint1 : Integrable
      (fun z : ℝ => ∑ n ∈ s, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖) :=
    integrable_finsetSum s (fun n _ => hker n)
  have hint2 : Integrable (fun z : ℝ => B * (4 * (1 + R ^ 2)) * 17 * ‖K z‖) :=
    hK.norm.const_mul _
  calc ∫ z, (∑ n ∈ s, B * (1 + max 0 (|(n:ℝ) - z| - R) ^ 2)⁻¹ * ‖K z‖)
      ≤ ∫ z, B * (4 * (1 + R ^ 2)) * 17 * ‖K z‖ :=
        integral_mono_ae hint1 hint2 (Filter.Eventually.of_forall hinner)
    _ = B * (4 * (1 + R ^ 2)) * 17 * ∫ z, ‖K z‖ := integral_const_mul ..


/-- LEAF. Poisson summation step: the sum of the modulated integer shifts of `K` equals the
sum of the Fourier transform of `K` at the shifted frequencies `v + m`, each carrying the
phase `eC (α * m)`. This is the analytic half of the proof, and it is where the
integrability of `K` is used. -/
theorem leaf_poisson_summation (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
      ∑' m : ℤ, eC (α * (m : ℝ)) * ftR K (v + (m : ℝ)) := by
  set g : C(ℝ, ℂ) :=
    ⟨fun x => K x * eC (-(x * v)),
      hcont.mul (eC_continuous.comp (by fun_prop : Continuous fun x : ℝ => -(x * v)))⟩ with hg
  have hnorm : ∀ Cc : TopologicalSpace.Compacts ℝ,
      Summable fun n : ℤ => ‖(g.comp (ContinuousMap.addRight n)).restrict Cc‖ := by
    intro Cc
    obtain ⟨φ, B, hB, hφint, hφcont, hφdec, hφfour⟩ := K_eq_convolution K hK hcont hsupp
    obtain ⟨R, hR⟩ := Cc.isCompact.isBounded.subset_closedBall (0:ℝ)
    set R' := max R 0 with hR'
    have hR'0 : 0 ≤ R' := le_max_right _ _
    have hsub : (Cc : Set ℝ) ⊆ Set.Icc (-R') R' := by
      intro x hx
      have h1 : x ∈ Metric.closedBall (0:ℝ) R := hR hx
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
      have h2 : |x| ≤ R' := le_trans h1 (le_max_left R 0)
      exact Set.mem_Icc.mpr ⟨by linarith [abs_le.mp h2], by linarith [abs_le.mp h2]⟩
    have hker : ∀ n : ℤ,
        Integrable (fun z : ℝ => B * (1 + max 0 (|(n:ℝ) - z| - R') ^ 2)⁻¹ * ‖K z‖) := by
      intro n
      have hcont1 : Continuous fun z : ℝ => B * (1 + max 0 (|(n:ℝ) - z| - R') ^ 2)⁻¹ := by
        have hc : Continuous fun t : ℝ => B * (1 + max 0 (|t| - R') ^ 2)⁻¹ := by
          have h1 : Continuous fun t : ℝ => (1 + max 0 (|t| - R') ^ 2) := by fun_prop
          exact continuous_const.mul (h1.inv₀ fun t => ne_of_gt (by positivity))
        have hcomp' : Continuous
            fun z : ℝ => (fun t : ℝ => B * (1 + max 0 (|t| - R') ^ 2)⁻¹) ((n:ℝ) - z) :=
          hc.comp (show Continuous fun z : ℝ => (n:ℝ) - z by fun_prop)
        exact hcomp'
      refine Integrable.mono' (hK.norm.const_mul B) ?_ ?_
      · exact hcont1.aestronglyMeasurable.mul hK.norm.aestronglyMeasurable
      · filter_upwards with z
        have h1 : (1 + max 0 (|(n:ℝ) - z| - R') ^ 2)⁻¹ ≤ 1 := by
          rw [inv_le_one₀ (by positivity)]
          have h2 : (0:ℝ) ≤ max 0 (|(n:ℝ) - z| - R') ^ 2 := by positivity
          linarith
        have h2 : ‖B * (1 + max 0 (|(n:ℝ) - z| - R') ^ 2)⁻¹ * ‖K z‖‖
            = B * (1 + max 0 (|(n:ℝ) - z| - R') ^ 2)⁻¹ * ‖K z‖ := by
          rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hB,
            abs_of_nonneg (inv_nonneg.mpr (by positivity)), norm_norm]
        rw [h2]
        have h3 : B * (1 + max 0 (|(n:ℝ) - z| - R') ^ 2)⁻¹ * ‖K z‖ ≤ B * 1 * ‖K z‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hB) (norm_nonneg (K z))
        linarith [h3]
    have hb_nonneg : ∀ n : ℤ,
        (0:ℝ) ≤ ∫ z, B * (1 + max 0 (|(n:ℝ) - z| - R') ^ 2)⁻¹ * ‖K z‖ := by
      intro n
      refine integral_nonneg fun z => ?_
      have h1 : (0:ℝ) ≤ (1 + max 0 (|(n:ℝ) - z| - R') ^ 2)⁻¹ := by positivity
      have h2 : (0:ℝ) ≤ B * (1 + max 0 (|(n:ℝ) - z| - R') ^ 2)⁻¹ := by positivity
      exact mul_nonneg h2 (norm_nonneg _)
    have hbsum : Summable fun n : ℤ =>
        ∫ z, B * (1 + max 0 (|(n:ℝ) - z| - R') ^ 2)⁻¹ * ‖K z‖ :=
      summable_of_sum_le hb_nonneg (fun s => slack_integral_sum_le K hK B R' hB hR'0 hker s)
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hbsum
    refine (ContinuousMap.norm_le _ (hb_nonneg n)).mpr (fun x => ?_)
    have hx' : |(x:ℝ)| ≤ R' := by
      have hx := hsub x.2
      rw [Set.mem_Icc] at hx
      exact abs_le.mpr ⟨hx.1, hx.2⟩
    have hval : ((g.comp (ContinuousMap.addRight n)).restrict Cc) x
        = K ((x:ℝ) + (n:ℝ)) * eC (-(((x:ℝ) + (n:ℝ)) * v)) := rfl
    rw [hval, norm_mul, eC_norm, mul_one]
    exact K_shift_le_slack_integral K hK φ hφcont B R' hB hφdec hφfour hker (x:ℝ) hx' n
  have hsum : Summable fun n : ℤ => FourierTransform.fourier (g : ℝ → ℂ) n := by
    have hzero : ∀ n : ℤ, n ∉ ({-⌊v⌋, -(⌊v⌋ + 1)} : Finset ℤ) →
        FourierTransform.fourier (g : ℝ → ℂ) n = 0 := by
      intro n hn
      have h1 : n ≠ -⌊v⌋ := by
        intro h; exact hn (by simp [h])
      have h2 : n ≠ -(⌊v⌋ + 1) := by
        intro h; exact hn (by simp [h])
      have hend : ∀ ξ : ℝ, 1 ≤ |ξ| → ftR K ξ = 0 := by
        have hclosed : IsClosed {ξ : ℝ | ftR K ξ = 0} :=
          isClosed_eq (continuous_ftR K hK) continuous_const
        have hsub : {ξ : ℝ | 1 < |ξ|} ⊆ {ξ : ℝ | ftR K ξ = 0} := fun ξ hξ => hsupp ξ hξ
        have hclos : closure {ξ : ℝ | 1 < |ξ|} ⊆ {ξ : ℝ | ftR K ξ = 0} :=
          hclosed.closure_subset_iff.mpr hsub
        have hclosure : closure {ξ : ℝ | 1 < |ξ|} = {ξ : ℝ | 1 ≤ |ξ|} := by
          have hset : {ξ : ℝ | 1 < |ξ|} = Set.Ioi (1 : ℝ) ∪ Set.Iio (-1 : ℝ) := by
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioi, Set.mem_Iio, lt_abs, lt_neg]
          rw [hset, closure_union, closure_Ioi, closure_Iio]
          ext x
          simp only [Set.mem_union, Set.mem_Ici, Set.mem_Iic, Set.mem_setOf_eq, le_abs, le_neg]
        intro ξ hξ
        exact hclos (by rw [hclosure]; exact hξ)
      have hidx : 1 ≤ |v + (n : ℝ)| := by
        have hdecomp : v = (⌊v⌋ : ℝ) + Int.fract v := (Int.floor_add_fract v).symm
        have hfr0 : 0 ≤ Int.fract v := Int.fract_nonneg v
        have hfr1 : Int.fract v < 1 := Int.fract_lt_one v
        set j : ℤ := ⌊v⌋ + n with hjdef
        have hj0 : j ≠ 0 := by
          intro h
          apply h1
          have : (⌊v⌋ + n : ℤ) = 0 := h
          omega
        have hj1 : j ≠ -1 := by
          intro h
          apply h2
          have : (⌊v⌋ + n : ℤ) = -(⌊v⌋ + 1) := by omega
          omega
        have hveq : v + (n : ℝ) = Int.fract v + (j : ℝ) := by
          have hfr : (⌊v⌋ : ℝ) + Int.fract v = v := Int.floor_add_fract v
          have hjj : (j : ℝ) = (⌊v⌋ : ℝ) + (n : ℝ) := by
            rw [hjdef]; push_cast; ring
          linarith
        rcases lt_or_ge j 1 with hlt | hge
        · have hjle : j ≤ -2 := by omega
          have hjle' : (j : ℝ) ≤ -2 := by exact_mod_cast hjle
          have hneg : v + (n : ℝ) < -1 := by rw [hveq]; linarith
          rw [abs_of_neg (by linarith)]
          linarith
        · have hge' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hge
          have hnn : 0 ≤ v + (n : ℝ) := by rw [hveq]; linarith
          rw [abs_of_nonneg hnn]
          linarith
      have hg' : (g : ℝ → ℂ) = fun x => K x * eC (-(x * v)) := rfl
      rw [hg', fourier_modulated K v n, hend _ hidx]
    exact summable_of_ne_finset_zero hzero
  have hp := Real.tsum_eq_tsum_fourier hnorm hsum α
  have hleft : (∑' n : ℤ, K (α + n) * eC (-((α + n) * v)))
      = ∑' n : ℤ, (g : ℝ → ℂ) (α + n) := rfl
  rw [hleft, hp]
  refine tsum_congr fun n => ?_
  have hg' : (g : ℝ → ℂ) = fun x => K x * eC (-(x * v)) := rfl
  rw [hg', fourier_modulated K v n, fourier_coe_eq_eC]
  ring


/-- LEAF. Endpoint step: the Fourier transform of `K` vanishes on the closed unit pair of
frequencies `±1` as well. The support hypothesis gives this only for `1 < |α|`; the values at
`|α| = 1` follow from continuity of `α ↦ ftR K α`, which integrability of `K` supplies. -/
theorem leaf_poisson_endpoint (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    ∀ ξ : ℝ, 1 ≤ |ξ| → ftR K ξ = 0 := by
  have hcont' : Continuous (ftR K) := continuous_ftR K hK
  have hclosed : IsClosed {ξ : ℝ | ftR K ξ = 0} := isClosed_eq hcont' continuous_const
  have hsub : {ξ : ℝ | 1 < |ξ|} ⊆ {ξ : ℝ | ftR K ξ = 0} := fun ξ hξ => hsupp ξ hξ
  have hclos : closure {ξ : ℝ | 1 < |ξ|} ⊆ {ξ : ℝ | ftR K ξ = 0} :=
    hclosed.closure_subset_iff.mpr hsub
  have hclosure : closure {ξ : ℝ | 1 < |ξ|} = {ξ : ℝ | 1 ≤ |ξ|} := by
    have hset : {ξ : ℝ | 1 < |ξ|} = Set.Ioi (1 : ℝ) ∪ Set.Iio (-1 : ℝ) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioi, Set.mem_Iio, lt_abs, lt_neg]
    rw [hset, closure_union, closure_Ioi, closure_Iio]
    ext x
    simp only [Set.mem_union, Set.mem_Ici, Set.mem_Iic, Set.mem_setOf_eq, le_abs, le_neg]
  intro ξ hξ
  exact hclos (by rw [hclosure]; exact hξ)


/-- LEAF. Index step: every integer shift `m` other than `-⌊v⌋` and `-(⌊v⌋ + 1)` puts the
frequency `v + m` at distance at least `1` from the origin. This is the only point where the
floor and fractional part of `v` are used. -/
theorem leaf_poisson_index (v : ℝ) :
    ∀ m : ℤ, m ≠ -⌊v⌋ → m ≠ -(⌊v⌋ + 1) → 1 ≤ |v + (m : ℝ)| := by
  intro m hm1 hm2
  have hdecomp : v = (⌊v⌋ : ℝ) + Int.fract v := (Int.floor_add_fract v).symm
  have hfr0 : 0 ≤ Int.fract v := Int.fract_nonneg v
  have hfr1 : Int.fract v < 1 := Int.fract_lt_one v
  set j : ℤ := ⌊v⌋ + m with hjdef
  have hj0 : j ≠ 0 := by
    intro h
    apply hm1
    have : (⌊v⌋ + m : ℤ) = 0 := h
    omega
  have hj1 : j ≠ -1 := by
    intro h
    apply hm2
    have : (⌊v⌋ + m : ℤ) = -(⌊v⌋ + 1) := by omega
    omega
  have hveq : v + (m : ℝ) = Int.fract v + (j : ℝ) := by
    have hfr : (⌊v⌋ : ℝ) + Int.fract v = v := Int.floor_add_fract v
    have hjj : (j : ℝ) = (⌊v⌋ : ℝ) + (m : ℝ) := by
      rw [hjdef]; push_cast; ring
    linarith
  rcases lt_or_ge j 1 with hlt | hge
  · have hjle : j ≤ -2 := by omega
    have hjle' : (j : ℝ) ≤ -2 := by exact_mod_cast hjle
    have hneg : v + (m : ℝ) < -1 := by rw [hveq]; linarith
    rw [abs_of_neg (by linarith)]
    linarith
  · have hge' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hge
    have hnn : 0 ≤ v + (m : ℝ) := by rw [hveq]; linarith
    rw [abs_of_nonneg hnn]
    linarith


/-- LEAF. Collapse step: by the endpoint and index steps, all but the shifts `-⌊v⌋` and
`-(⌊v⌋ + 1)` drop out of the Fourier series, and the two survivors are the terms of the
right-hand side, since `v + (-⌊v⌋) = Int.fract v` and `v + (-(⌊v⌋ + 1)) = Int.fract v - 1`. -/
theorem leaf_poisson_collapse (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' m : ℤ, eC (α * (m : ℝ)) * ftR K (v + (m : ℝ))) =
      eC (-(α * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) +
        eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1) := by
  have hzero : ∀ m : ℤ, m ∉ ({-⌊v⌋, -(⌊v⌋ + 1)} : Finset ℤ) →
      eC (α * (m : ℝ)) * ftR K (v + (m : ℝ)) = 0 := by
    intro m hm
    have hm1 : m ≠ -⌊v⌋ := by
      intro h; exact hm (by simp [h])
    have hm2 : m ≠ -(⌊v⌋ + 1) := by
      intro h; exact hm (by simp [h])
    have h1 := leaf_poisson_index v m hm1 hm2
    rw [leaf_poisson_endpoint K hK hcont hsupp _ h1, mul_zero]
  rw [tsum_eq_sum hzero]
  have hne : (-⌊v⌋ : ℤ) ≠ -(⌊v⌋ + 1) := by omega
  rw [Finset.sum_pair hne]
  have hfr : (⌊v⌋ : ℝ) + Int.fract v = v := Int.floor_add_fract v
  have e1 : v + ((-⌊v⌋ : ℤ) : ℝ) = Int.fract v := by push_cast; linarith
  have e2 : v + ((-(⌊v⌋ + 1) : ℤ) : ℝ) = Int.fract v - 1 := by push_cast; linarith
  rw [e1, e2]
  have p1 : α * ((-⌊v⌋ : ℤ) : ℝ) = -(α * (⌊v⌋ : ℝ)) := by push_cast; ring
  have p2 : α * ((-(⌊v⌋ + 1) : ℤ) : ℝ) = -(α * ((⌊v⌋ + 1 : ℤ) : ℝ)) := by push_cast; ring
  rw [p1, p2]


/-- Assembly: the sealed statement, from the summation leaf and the collapse leaf. -/
theorem leaf_poisson_split (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
      eC (-(α * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) +
        eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1) := by
  rw [leaf_poisson_summation K hK hcont hsupp v α,
    leaf_poisson_collapse K hK hcont hsupp v α]

end LeanLab.ExceptionalSet.Decomp371d
