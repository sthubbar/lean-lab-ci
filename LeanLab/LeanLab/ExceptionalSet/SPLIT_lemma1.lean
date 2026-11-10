/-
Split of `lemma1`, the Poisson summation identity of this folder, into the three steps
of its written proof: the integrability of the modulated product, the fold of the real
line into the unit interval by the period of `h`, and the reduction of the folded
kernel sum to its two adjacent Fourier frequencies.

`lemma1_split` below states `Lemma1` unchanged and is assembled from the three leaves,
so it carries no `sorry` of its own. Each leaf carries exactly one step.

AI wrote this Lean code, checked only by the Lean kernel. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.State1539

namespace LeanLab.ExceptionalSet.U1539

open Real MeasureTheory Polynomial
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Leaves -/

open scoped FourierTransform SchwartzMap Convolution

/-! ### Kernel helpers (def-free) -/

private theorem ftR_eq_fourier (K : ℝ → ℂ) : ftR K = 𝓕 K := by
  funext α
  rw [ftR, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with β
  simp only [eC, smul_eq_mul]
  have hexp : Complex.exp (2 * ↑π * Complex.I * ↑(-(α * β)))
      = Complex.exp (↑(-(π * β * α * 2)) * Complex.I) := by
    congr 1
    push_cast
    ring
  have hexp2 : Complex.exp (↑(-(π * β * α * 2)) * Complex.I)
      = Complex.exp (↑(-2 * π * β * α) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [hexp, hexp2, mul_comm]

private theorem fourier_cont_of_integrable (K : ℝ → ℂ) (hK : Integrable K) :
    Continuous (𝓕 K) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hK

private theorem fourier_integrable_of_support (K : ℝ → ℂ) (hK : Integrable K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) : Integrable (𝓕 K) := by
  have hcont : Continuous (𝓕 K) := fourier_cont_of_integrable K hK
  have hsupp' : ∀ x : ℝ, x ∉ Set.Icc (-1:ℝ) 1 → 𝓕 K x = 0 := by
    intro x hx
    rw [← ftR_eq_fourier]
    apply hsupp
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hind : Integrable (Set.indicator (Set.Icc (-1:ℝ) 1) (𝓕 K)) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  refine hind.congr (Filter.Eventually.of_forall (fun x => ?_))
  by_cases hx : x ∈ Set.Icc (-1:ℝ) 1
  · simp [hx]
  · simp [hx, hsupp' x hx]

private theorem zeta_succ_nat_le : ∑' k : ℕ, (1:ℝ) / ((k:ℝ)+1)^2 ≤ 3 := by
  have h := (hasSum_nat_add_iff' (f := fun m : ℕ => (1:ℝ)/(m:ℝ)^2) 1).mpr hasSum_zeta_two
  have hz : (∑ i ∈ Finset.range 1, (1:ℝ)/(i:ℝ)^2) = 0 := by simp
  rw [hz, sub_zero] at h
  have h' : HasSum (fun k : ℕ => (1:ℝ) / ((k:ℝ)+1)^2) (π^2/6) := by
    simpa [Nat.cast_add, Nat.cast_one] using h
  rw [h'.tsum_eq]
  nlinarith [Real.pi_lt_four, Real.pi_pos]

private theorem zeta_succ_nat_summable : Summable (fun k : ℕ => (1:ℝ) / ((k:ℝ)+1)^2) := by
  have h := (hasSum_nat_add_iff' (f := fun m : ℕ => (1:ℝ)/(m:ℝ)^2) 1).mpr hasSum_zeta_two
  exact h.summable.congr (fun k => by simp [Nat.cast_add, Nat.cast_one])

private theorem tsum_one_div_one_add_sq_le : ∑' k : ℕ, (1:ℝ) / (1 + (k:ℝ)^2) ≤ 6 := by
  have hcomp : ∀ k : ℕ, (1:ℝ) / (1 + (k:ℝ)^2) ≤ 2 / ((k:ℝ)+1)^2 := by
    intro k
    have h1 : (0:ℝ) < 1 + (k:ℝ)^2 := by positivity
    have h2 : (0:ℝ) < ((k:ℝ)+1)^2 := by positivity
    rw [div_le_div_iff₀ h1 h2]
    nlinarith [sq_nonneg ((k:ℝ) - 1)]
  have h2s : Summable (fun k : ℕ => 2 / ((k:ℝ)+1)^2) := by
    have h := zeta_succ_nat_summable.mul_left 2
    refine h.congr (fun k => ?_)
    simp only [div_eq_mul_inv]
    ring
  have hs : Summable (fun k : ℕ => (1:ℝ) / (1 + (k:ℝ)^2)) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hcomp h2s
  have hle := hs.tsum_le_tsum hcomp h2s
  have h3 : ∑' k : ℕ, 2 / ((k:ℝ)+1)^2 = 2 * ∑' k : ℕ, (1:ℝ) / ((k:ℝ)+1)^2 := by
    have hfun : (fun k : ℕ => 2 / ((k:ℝ)+1)^2) = (fun k : ℕ => 2 * (1 / ((k:ℝ)+1)^2)) := by
      funext k
      simp only [div_eq_mul_inv]
      ring
    rw [hfun, tsum_mul_left]
  rw [h3] at hle
  nlinarith [zeta_succ_nat_le]

private theorem kernel_exists :
    ∃ (Φ : ℝ → ℂ) (D : ℝ), 0 < D ∧ Integrable Φ ∧ Continuous Φ ∧
      (∀ x : ℝ, ‖Φ x‖ ≤ D / (1 + x^2)) ∧ (∀ ξ : ℝ, |ξ| ≤ 1 → 𝓕 Φ ξ = 1) := by
  let bump : ContDiffBump (0:ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let psi : ℝ → ℂ := fun x => (bump x : ℂ)
  have psi_cs : HasCompactSupport psi :=
    bump.hasCompactSupport.comp_left (g := fun r : ℝ => (r:ℂ)) (by simp)
  have psi_cd : ContDiff ℝ (⊤ : ℕ∞) psi := Complex.ofRealCLM.contDiff.comp bump.contDiff
  have psi_int : Integrable psi := psi_cd.continuous.integrable_of_hasCompactSupport psi_cs
  have psi_one : ∀ x : ℝ, |x| ≤ 1 → psi x = 1 := by
    intro x hx
    have h : x ∈ Metric.closedBall (0:ℝ) 1 := by simpa [Real.dist_eq, sub_zero] using hx
    simp only [psi, bump.one_of_mem_closedBall h, Complex.ofReal_one]
  let psiS : SchwartzMap ℝ ℂ := HasCompactSupport.toSchwartzMap psi_cs psi_cd
  let Phi : ℝ → ℂ := 𝓕 psi
  have Phi_eq : ((𝓕 psiS : SchwartzMap ℝ ℂ) : ℝ → ℂ) = Phi := rfl
  have Phi_int : Integrable Phi := (𝓕 psiS).integrable
  have Phi_cont : Continuous Phi := (𝓕 psiS).continuous
  have Phi_ft : ∀ ξ : ℝ, |ξ| ≤ 1 → 𝓕 Phi ξ = 1 := by
    intro ξ hξ
    change 𝓕 (𝓕 psi) ξ = 1
    have hinv : 𝓕⁻ (𝓕 psi) = psi :=
      Continuous.fourierInv_fourier_eq psi_cd.continuous psi_int Phi_int
    have h2 : ∀ y : ℝ, 𝓕 (𝓕 psi) y = psi (-y) := by
      intro y
      have h3 := congr_fun hinv (-y)
      rw [fourierInv_eq_fourier_neg] at h3
      simpa using h3
    rw [h2 ξ]
    exact psi_one (-ξ) (by simpa using hξ)
  obtain ⟨d0, hd0pos, hd0⟩ := SchwartzMap.decay (𝓕 psiS) 0 0
  obtain ⟨d2, hd2pos, hd2⟩ := SchwartzMap.decay (𝓕 psiS) 2 0
  let D : ℝ := 2 * max d0 d2
  have hDpos : 0 < D := by
    have : (0:ℝ) < max d0 d2 := lt_of_lt_of_le hd0pos (le_max_left _ _)
    simp only [D]; linarith
  have hDmax : (0:ℝ) < max d0 d2 := lt_of_lt_of_le hd0pos (le_max_left _ _)
  have hdec : ∀ x : ℝ, ‖Phi x‖ ≤ D / (1 + x^2) := by
    intro x
    have h0 : ‖Phi x‖ ≤ max d0 d2 := by
      have h := hd0 x
      simp only [norm_iteratedFDeriv_zero] at h
      rw [Phi_eq] at h
      simpa using h.trans (le_max_left _ _)
    have hDm : D = 2 * max d0 d2 := rfl
    rcases le_total |x| 1 with hx | hx
    · have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [h0, hDmax, hx2, hDm]
    · have hx2 : 1 ≤ x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
      have h2 : ‖Phi x‖ * x^2 ≤ d2 := by
        have h := hd2 x
        simp only [norm_iteratedFDeriv_zero] at h
        rw [Phi_eq] at h
        have h' : ‖x‖ ^ 2 * ‖Phi x‖ ≤ d2 := h
        rw [Real.norm_eq_abs, sq_abs] at h'
        calc ‖Phi x‖ * x^2 = x^2 * ‖Phi x‖ := by ring
          _ ≤ d2 := h'
      rw [le_div_iff₀ (by positivity)]
      nlinarith [h2, le_max_right d0 d2, hDmax, hx2, hDm]
  have hper : ∀ u : ℝ, ∑' n : ℤ, ‖Phi (u + n)‖ ≤ 10 * D := by
    have core : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → ∑' n : ℤ, ‖Phi (τ + n)‖ ≤ 10 * D := by
      intro τ hτ0 hτ1
      have hpos : ∀ k : ℕ, ‖Phi (τ + (((k:ℤ) + 1 : ℤ) : ℝ))‖ ≤ D * (1 / ((k:ℝ)+1)^2) := by
        intro k
        have hargk : τ + ((((k:ℤ) + 1 : ℤ)) : ℝ) = τ + ((k:ℝ) + 1) := by push_cast; ring
        rw [hargk]
        have h1 : (0:ℝ) < 1 + (τ + ((k:ℝ) + 1))^2 := by positivity
        have h2 : (0:ℝ) < ((k:ℝ)+1)^2 := by positivity
        have h3 : ((k:ℝ)+1)^2 ≤ 1 + (τ + ((k:ℝ) + 1))^2 := by nlinarith
        calc ‖Phi (τ + ((k:ℝ) + 1))‖ ≤ D / (1 + (τ + ((k:ℝ) + 1))^2) := hdec _
          _ ≤ D / ((k:ℝ)+1)^2 := div_le_div_of_nonneg_left hDpos.le h2 h3
          _ = D * (1 / ((k:ℝ)+1)^2) := by rw [mul_one_div]
      have hneg : ∀ k : ℕ, ‖Phi (τ + ((-(((k:ℤ) + 1)) : ℤ) : ℝ))‖ ≤ D * (2 / ((k:ℝ)+1)^2) := by
        intro k
        have hargk : τ + ((-(((k:ℤ) + 1)) : ℤ) : ℝ) = τ - ((k:ℝ) + 1) := by push_cast; ring
        rw [hargk]
        have h1 : (0:ℝ) < 1 + (τ - ((k:ℝ) + 1))^2 := by positivity
        have h2 : (0:ℝ) < ((k:ℝ)+1)^2 := by positivity
        have h3 : ((k:ℝ)+1)^2 ≤ 2 * (1 + (τ - ((k:ℝ) + 1))^2) := by
          nlinarith [sq_nonneg ((k:ℝ) - 1), sq_nonneg (τ - ((k:ℝ)+1)), sq_nonneg (k:ℝ)]
        have h4 : ‖Phi (τ - ((k:ℝ) + 1))‖ ≤ D / (1 + (τ - ((k:ℝ) + 1))^2) := hdec _
        calc ‖Phi (τ - ((k:ℝ) + 1))‖ ≤ D / (1 + (τ - ((k:ℝ) + 1))^2) := h4
          _ ≤ D * (2 / ((k:ℝ)+1)^2) := by
              rw [div_le_iff₀ h1]
              have hsplit : D * (2 / ((k:ℝ)+1)^2) * (1 + (τ - ((k:ℝ) + 1))^2)
                  = 2 * D * (1 + (τ - ((k:ℝ) + 1))^2) / ((k:ℝ)+1)^2 := by ring
              rw [hsplit, le_div_iff₀ h2]
              nlinarith
      have hsumpos : Summable (fun k : ℕ => ‖Phi (τ + (((k:ℤ) + 1 : ℤ) : ℝ))‖) := by
        have h2s : Summable (fun k : ℕ => D * (1 / ((k:ℝ)+1)^2)) := by
          have h := zeta_succ_nat_summable.mul_left D
          refine h.congr (fun k => ?_)
          simp only [div_eq_mul_inv]
          try ring
        exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) hpos h2s
      have hsumneg : Summable (fun k : ℕ => ‖Phi (τ + ((-(((k:ℤ) + 1)) : ℤ) : ℝ))‖) := by
        have h2s : Summable (fun k : ℕ => D * (2 / ((k:ℝ)+1)^2)) := by
          have h := zeta_succ_nat_summable.mul_left (2 * D)
          refine h.congr (fun k => ?_)
          simp only [div_eq_mul_inv]
          try ring
        exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) hneg h2s
      have hkey := tsum_of_add_one_of_neg_add_one (f := fun n : ℤ => ‖Phi (τ + n)‖) hsumpos hsumneg
      rw [hkey]
      have hp : ∑' k : ℕ, ‖Phi (τ + (((k:ℤ) + 1 : ℤ) : ℝ))‖ ≤ 3 * D := by
        have h2s : Summable (fun k : ℕ => D * (1 / ((k:ℝ)+1)^2)) := by
          have h := zeta_succ_nat_summable.mul_left D
          refine h.congr (fun k => ?_)
          simp only [div_eq_mul_inv]
          try ring
        have hle := hsumpos.tsum_le_tsum hpos h2s
        have hval : ∑' k : ℕ, D * (1 / ((k:ℝ)+1)^2) = D * ∑' k : ℕ, (1:ℝ) / ((k:ℝ)+1)^2 := by
          rw [tsum_mul_left]
        rw [hval] at hle
        nlinarith [zeta_succ_nat_le, hDpos]
      have hn : ∑' k : ℕ, ‖Phi (τ + ((-(((k:ℤ) + 1)) : ℤ) : ℝ))‖ ≤ 6 * D := by
        have h2s : Summable (fun k : ℕ => D * (2 / ((k:ℝ)+1)^2)) := by
          have h := zeta_succ_nat_summable.mul_left (2 * D)
          refine h.congr (fun k => ?_)
          simp only [div_eq_mul_inv]
          try ring
        have hle := hsumneg.tsum_le_tsum hneg h2s
        have hval : ∑' k : ℕ, D * (2 / ((k:ℝ)+1)^2) = 2 * D * ∑' k : ℕ, (1:ℝ) / ((k:ℝ)+1)^2 := by
          have hfun : (fun k : ℕ => D * (2 / ((k:ℝ)+1)^2))
              = (fun k : ℕ => (2 * D) * (1 / ((k:ℝ)+1)^2)) := by
            funext k
            simp only [div_eq_mul_inv]
            ring
          rw [hfun, tsum_mul_left]
        rw [hval] at hle
        nlinarith [zeta_succ_nat_le, hDpos]
      have h0 : ‖Phi (τ + ((0:ℤ) : ℝ))‖ ≤ D := by
        have harg : τ + ((0:ℤ) : ℝ) = τ := by push_cast; ring
        rw [harg]
        have h1 : (0:ℝ) < 1 + τ^2 := by positivity
        have hD := hdec τ
        calc ‖Phi τ‖ ≤ D / (1 + τ^2) := hD
          _ ≤ D := by
              rw [div_le_iff₀ h1]
              nlinarith [hDpos]
      have hs := add_le_add (add_le_add hp h0) hn
      linarith
    intro u
    have hu : u = Int.fract u + (⌊u⌋ : ℝ) := by rw [Int.fract_add_floor]
    have hτ1 : Int.fract u ≤ 1 := (Int.fract_lt_one u).le
    have harg : ∀ n : ℤ, u + (n:ℝ) = Int.fract u + ((n + ⌊u⌋ : ℤ) : ℝ) := by
      intro n
      conv_lhs => rw [hu]
      push_cast
      ring
    calc ∑' n : ℤ, ‖Phi (u + n)‖
        = ∑' n : ℤ, ‖Phi (Int.fract u + ((n + ⌊u⌋ : ℤ) : ℝ))‖ := by
          apply tsum_congr; intro n; rw [harg n]
      _ = ∑' n : ℤ, ‖Phi (Int.fract u + (n:ℝ))‖ :=
          (Equiv.addRight ⌊u⌋).tsum_eq (fun n : ℤ => ‖Phi (Int.fract u + (n:ℝ))‖)
      _ ≤ 10 * D := core (Int.fract u) (Int.fract_nonneg u) hτ1
  exact ⟨Phi, D, hDpos, Phi_int, Phi_cont, hdec, Phi_ft⟩


private theorem eq_convolution_of_kernel (K Φ : ℝ → ℂ) (D : ℝ) (hD : 0 < D) (hK : Integrable K)
    (hcont : Continuous K) (hΦint : Integrable Φ) (hΦcont : Continuous Φ)
    (hdec : ∀ x : ℝ, ‖Φ x‖ ≤ D / (1 + x^2))
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0)
    (hΦft : ∀ ξ : ℝ, |ξ| ≤ 1 → 𝓕 Φ ξ = 1) :
    K = K ⋆[ContinuousLinearMap.mul ℂ ℂ] Φ := by
  have hKft_int : Integrable (𝓕 K) := fourier_integrable_of_support K hK hsupp
  have hconv_int : Integrable (K ⋆[ContinuousLinearMap.mul ℂ ℂ] Φ) :=
    Integrable.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hK hΦint
  have hbdd : ∀ x : ℝ, ‖Φ x‖ ≤ D := by
    intro x
    have h1 : (0:ℝ) < 1 + x^2 := by positivity
    calc ‖Φ x‖ ≤ D / (1 + x^2) := hdec x
      _ ≤ D := by rw [div_le_iff₀ h1]; nlinarith [hD.le, sq_nonneg x]
  have hBdd : BddAbove (Set.range fun x => ‖Φ x‖) :=
    ⟨D, by rintro _ ⟨x, rfl⟩; exact hbdd x⟩
  have hconv_cont : Continuous (K ⋆[ContinuousLinearMap.mul ℂ ℂ] Φ) :=
    BddAbove.continuous_convolution_right_of_integrable (L := ContinuousLinearMap.mul ℂ ℂ)
      hBdd hK hΦcont
  have hft : 𝓕 (K ⋆[ContinuousLinearMap.mul ℂ ℂ] Φ) = 𝓕 K := by
    funext ξ
    rw [Real.fourier_mul_convolution_eq hK hΦint ξ]
    by_cases hξ : |ξ| ≤ 1
    · rw [hΦft ξ hξ, mul_one]
    · have h0 : 𝓕 K ξ = 0 := by
        rw [← ftR_eq_fourier]
        exact hsupp ξ (not_le.mp hξ)
      rw [h0, zero_mul]
  have h1 : 𝓕⁻ (𝓕 K) = K := Continuous.fourierInv_fourier_eq hcont hK hKft_int
  have h2 : 𝓕⁻ (𝓕 (K ⋆[ContinuousLinearMap.mul ℂ ℂ] Φ)) = K ⋆[ContinuousLinearMap.mul ℂ ℂ] Φ :=
    Continuous.fourierInv_fourier_eq hconv_cont hconv_int (hft ▸ hKft_int)
  rw [hft] at h2
  rw [h2] at h1
  exact h1.symm

open scoped ENNReal

private theorem mp_neg : MeasurePreserving (fun t : ℝ => -t) volume volume :=
  ⟨measurable_neg, Measure.map_neg_eq_self volume⟩

private theorem mp_reflect (x : ℝ) : MeasurePreserving (fun t : ℝ => x - t) volume volume := by
  have h : MeasurePreserving ((fun s : ℝ => s + x) ∘ (fun t : ℝ => -t)) volume volume :=
    (measurePreserving_add_right volume x).comp mp_neg
  convert h using 1
  funext t
  simp only [Function.comp_apply]
  ring

private theorem emb_reflect (x : ℝ) : MeasurableEmbedding (fun t : ℝ => x - t) := by
  have h : MeasurableEmbedding ((fun s : ℝ => s + x) ∘ (fun t : ℝ => -t)) :=
    (measurableEmbedding_addRight x).comp measurableEmbedding_neg
  convert h using 1
  funext t
  simp only [Function.comp_apply]
  ring

private theorem lintegral_Ioc_reflect (f : ℝ → ℝ≥0∞) (x : ℝ) :
    ∫⁻ t in Set.Ioc (0:ℝ) 1, f (x - t) = ∫⁻ s in Set.Ico (x - 1) x, f s := by
  have himg : (fun t : ℝ => x - t) '' Set.Ioc (0:ℝ) 1 = Set.Ico (x - 1) x := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      simp only [Set.mem_Ioc] at ht
      simp only [Set.mem_Ico]
      constructor <;> linarith
    · intro hy
      simp only [Set.mem_Ico] at hy
      refine ⟨x - y, ?_, by ring⟩
      simp only [Set.mem_Ioc]
      constructor <;> linarith
  rw [(mp_reflect x).setLIntegral_comp_emb (emb_reflect x) f (Set.Ioc (0:ℝ) 1), himg]

private theorem tsum_lintegral_Ioc_shift (f : ℝ → ℝ≥0∞) (b : ℝ) :
    ∑' n : ℤ, ∫⁻ x in Set.Ioc (b + n) (b + n + 1), f x = ∫⁻ x, f x := by
  symm
  rw [← lintegral_iUnion (μ := volume) (s := fun n : ℤ => Set.Ioc (b + n) (b + n + 1))
    (fun n => measurableSet_Ioc) (Set.pairwise_disjoint_Ioc_add_intCast (a := b)) f,
    iUnion_Ioc_add_intCast]
  simp

private theorem tsum_lintegral_Ico_shift (f : ℝ → ℝ≥0∞) (b : ℝ) :
    ∑' n : ℤ, ∫⁻ x in Set.Ico (b + n) (b + n + 1), f x = ∫⁻ x, f x := by
  symm
  rw [← lintegral_iUnion (μ := volume) (s := fun n : ℤ => Set.Ico (b + n) (b + n + 1))
    (fun n => measurableSet_Ico) (Set.pairwise_disjoint_Ico_add_intCast (a := b)) f,
    iUnion_Ico_add_intCast]
  simp

private theorem lintegral_Ioc_shift (f : ℝ → ℝ≥0∞) (c : ℝ) :
    ∫⁻ x in Set.Ioc (0:ℝ) 1, f (x + c) = ∫⁻ x in Set.Ioc c (c + 1), f x := by
  have hmp : MeasurePreserving (fun x : ℝ => x + c) volume volume :=
    measurePreserving_add_right volume c
  have himg : (fun x : ℝ => x + c) '' Set.Ioc (0:ℝ) 1 = Set.Ioc c (c + 1) := by
    ext y
    simp only [Set.mem_image, Set.mem_Ioc]
    constructor
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨y - c, ⟨by linarith, by linarith⟩, by ring⟩
  rw [hmp.setLIntegral_comp_emb (measurableEmbedding_addRight c) f (Set.Ioc (0:ℝ) 1), himg]

private theorem lintegral_periodic_mul {h g : ℝ → ℝ≥0∞} (hh : AEMeasurable h volume)
    (hg : AEMeasurable g volume) (hper : Function.Periodic h 1) :
    ∫⁻ α, h α * g α = ∫⁻ β in Set.Ioc (0:ℝ) 1, h β * (∑' m : ℤ, g (β + m)) := by
  have htile : ∫⁻ α, h α * g α
      = ∑' m : ℤ, ∫⁻ α in Set.Ioc ((0:ℝ) + m) ((0:ℝ) + m + 1), h α * g α := by
    rw [← lintegral_iUnion (μ := volume) (s := fun m : ℤ => Set.Ioc ((0:ℝ) + m) ((0:ℝ) + m + 1))
      (fun m => measurableSet_Ioc) (Set.pairwise_disjoint_Ioc_add_intCast (a := (0:ℝ))) (fun a => h a * g a)]
    simp only [zero_add, iUnion_Ioc_intCast, Measure.restrict_univ]
  have hpiece : ∀ m : ℤ, (∫⁻ α in Set.Ioc ((0:ℝ) + m) ((0:ℝ) + m + 1), h α * g α)
      = ∫⁻ β in Set.Ioc (0:ℝ) 1, h β * g (β + m) := by
    intro m
    have h1 := lintegral_Ioc_shift (fun α => h α * g α) (m:ℝ)
    rw [zero_add, ← h1]
    apply lintegral_congr
    intro β
    have hp : h (β + (m:ℝ)) = h β := by simpa using hper.int_mul m β
    rw [hp]
  rw [htile, funext hpiece]
  have hfun : (fun β : ℝ => h β * (∑' m : ℤ, g (β + m)))
      = (fun β : ℝ => ∑' m : ℤ, h β * g (β + m)) := by
    funext β
    rw [ENNReal.tsum_mul_left]
  rw [hfun]
  have hm : ∀ m : ℤ, AEMeasurable (fun β : ℝ => h β * g (β + m))
      (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    intro m
    have hgm : AEMeasurable (fun β : ℝ => g (β + m)) volume :=
      hg.comp_quasiMeasurePreserving (measurePreserving_add_right volume (m:ℝ)).quasiMeasurePreserving
    exact ((hh.mul hgm).mono_measure Measure.restrict_le_self)
  rw [← lintegral_tsum hm]

private theorem eq_convolution_of_kernel' (K Φ : ℝ → ℂ) (D : ℝ) (hD : 0 < D) (hK : Integrable K)
    (hcont : Continuous K) (hΦint : Integrable Φ) (hΦcont : Continuous Φ)
    (hdec : ∀ x : ℝ, ‖Φ x‖ ≤ D / (1 + x^2))
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0)
    (hΦft : ∀ ξ : ℝ, |ξ| ≤ 1 → 𝓕 Φ ξ = 1) :
    K = Φ ⋆[ContinuousLinearMap.mul ℂ ℂ] K := by
  have hKft_int : Integrable (𝓕 K) := fourier_integrable_of_support K hK hsupp
  have hconv_int : Integrable (Φ ⋆[ContinuousLinearMap.mul ℂ ℂ] K) :=
    Integrable.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hΦint hK
  have hbdd : ∀ x : ℝ, ‖Φ x‖ ≤ D := by
    intro x
    have h1 : (0:ℝ) < 1 + x^2 := by positivity
    calc ‖Φ x‖ ≤ D / (1 + x^2) := hdec x
      _ ≤ D := by rw [div_le_iff₀ h1]; nlinarith [hD.le, sq_nonneg x]
  have hBdd : BddAbove (Set.range fun x => ‖Φ x‖) :=
    ⟨D, by rintro _ ⟨x, rfl⟩; exact hbdd x⟩
  have hconv_cont : Continuous (Φ ⋆[ContinuousLinearMap.mul ℂ ℂ] K) :=
    BddAbove.continuous_convolution_left_of_integrable (L := ContinuousLinearMap.mul ℂ ℂ)
      hBdd hΦcont hK
  have hft : 𝓕 (Φ ⋆[ContinuousLinearMap.mul ℂ ℂ] K) = 𝓕 K := by
    funext ξ
    rw [Real.fourier_mul_convolution_eq (f₁ := Φ) (f₂ := K) hΦint hK ξ]
    by_cases hξ : |ξ| ≤ 1
    · rw [hΦft ξ hξ, one_mul]
    · have h0 : 𝓕 K ξ = 0 := by
        rw [← ftR_eq_fourier]
        exact hsupp ξ (not_le.mp hξ)
      rw [h0, mul_zero]
  have h1 : 𝓕⁻ (𝓕 K) = K := Continuous.fourierInv_fourier_eq hcont hK hKft_int
  have h2 : 𝓕⁻ (𝓕 (Φ ⋆[ContinuousLinearMap.mul ℂ ℂ] K)) = Φ ⋆[ContinuousLinearMap.mul ℂ ℂ] K :=
    Continuous.fourierInv_fourier_eq hconv_cont hconv_int (hft ▸ hKft_int)
  rw [hft, h1] at h2
  exact h2



private theorem knorm_bound (K Φ : ℝ → ℂ) (D : ℝ) (hD : 0 < D) (hK : Integrable K)
    (hΦint : Integrable Φ) (hΦcont : Continuous Φ)
    (hdec : ∀ x : ℝ, ‖Φ x‖ ≤ D / (1 + x^2))
    (hconv : K = Φ ⋆[ContinuousLinearMap.mul ℂ ℂ] K) :
    ∀ x : ℝ, ‖K x‖ₑ ≤ ∫⁻ t, ‖K (x - t)‖ₑ * ‖Φ t‖ₑ := by
  intro x
  have hbdd : ∀ t : ℝ, ‖Φ t‖ ≤ D := by
    intro t
    have h1 : (0:ℝ) < 1 + t^2 := by positivity
    calc ‖Φ t‖ ≤ D / (1 + t^2) := hdec t
      _ ≤ D := by rw [div_le_iff₀ h1]; nlinarith [hD.le, sq_nonneg t]
  have hx : K x = ∫ t, Φ t * K (x - t) := by
    have h := congr_fun hconv x
    simpa [convolution_def, ContinuousLinearMap.mul_apply'] using h
  have hint : Integrable (fun t : ℝ => ‖K (x - t)‖ * ‖Φ t‖) := by
    have h1 : Integrable (fun t : ℝ => ‖K (x - t)‖) :=
      (mp_reflect x).integrable_comp_of_integrable hK.norm
    exact h1.mul_bdd hΦcont.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbdd t))
  have hcoe : ‖K x‖ₑ = ENNReal.ofReal ‖K x‖ := by
    simp [enorm_eq_nnnorm, Real.nnnorm_of_nonneg (norm_nonneg _)]
  calc ‖K x‖ₑ = ENNReal.ofReal ‖K x‖ := hcoe
    _ ≤ ENNReal.ofReal (∫ t, ‖K (x - t)‖ * ‖Φ t‖) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hx]
        calc ‖∫ t, Φ t * K (x - t)‖ ≤ ∫ t, ‖Φ t * K (x - t)‖ :=
              norm_integral_le_integral_norm _
          _ = ∫ t, ‖K (x - t)‖ * ‖Φ t‖ := by
              apply integral_congr_ae
              filter_upwards with t
              simp only [norm_mul]
              ring
    _ = ∫⁻ t, ‖K (x - t)‖ₑ * ‖Φ t‖ₑ := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        · apply lintegral_congr
          intro t
          simp
        · filter_upwards with t
          positivity

private theorem swap_step (h K Φ : ℝ → ℂ) (hmh : AEMeasurable (fun x : ℝ => ‖h x‖ₑ) volume)
    (hK : Integrable K) (hcont : Continuous K) (hΦcont : Continuous Φ)
    (hbound : ∀ x : ℝ, ‖K x‖ₑ ≤ ∫⁻ t, ‖K (x - t)‖ₑ * ‖Φ t‖ₑ) :
    ∫⁻ x, ‖h x‖ₑ * ‖K x‖ₑ
      ≤ ∫⁻ t, ‖Φ t‖ₑ * (∫⁻ x, ‖h x‖ₑ * ‖K (x - t)‖ₑ) := by
  have hmK : AEMeasurable (fun p : ℝ × ℝ => ‖K (p.1 - p.2)‖ₑ) (volume.prod volume) :=
    ((hcont.measurable.comp (by fun_prop : Measurable (fun p : ℝ × ℝ => p.1 - p.2))).enorm).aemeasurable
  have hmh' : AEMeasurable (fun p : ℝ × ℝ => ‖h p.1‖ₑ) (volume.prod volume) :=
    hmh.comp_quasiMeasurePreserving
      (by fun_prop : QuasiMeasurePreserving Prod.fst (volume.prod volume) volume)
  have hmΦ : AEMeasurable (fun p : ℝ × ℝ => ‖Φ p.2‖ₑ) (volume.prod volume) :=
    ((hΦcont.measurable.enorm).comp (by fun_prop : Measurable (fun p : ℝ × ℝ => p.2))).aemeasurable
  have hm : ∀ x : ℝ, AEMeasurable (fun t : ℝ => ‖K (x - t)‖ₑ * ‖Φ t‖ₑ) volume := by
    intro x
    have a : AEMeasurable (fun t : ℝ => ‖K (x - t)‖ₑ) volume :=
      ((hcont.measurable.comp (by fun_prop : Measurable (fun t : ℝ => x - t))).enorm).aemeasurable
    exact a.mul hΦcont.measurable.enorm.aemeasurable
  have hm2 : ∀ t : ℝ, AEMeasurable (fun x : ℝ => ‖h x‖ₑ * ‖K (x - t)‖ₑ) volume := by
    intro t
    have b : AEMeasurable (fun x : ℝ => ‖K (x - t)‖ₑ) volume :=
      ((hcont.measurable.comp (by fun_prop : Measurable (fun x : ℝ => x - t))).enorm).aemeasurable
    exact hmh.mul b
  refine (lintegral_mono (fun x => mul_le_mul_right (hbound x) (‖h x‖ₑ))).trans_eq ?_
  trans ∫⁻ x, ∫⁻ t, ‖h x‖ₑ * (‖K (x - t)‖ₑ * ‖Φ t‖ₑ)
  · apply lintegral_congr
    intro x
    exact (lintegral_const_mul'' (‖h x‖ₑ) (hm x)).symm
  · rw [lintegral_lintegral_swap (f := fun x t : ℝ => ‖h x‖ₑ * (‖K (x - t)‖ₑ * ‖Φ t‖ₑ))
      (hmh'.mul (hmK.mul hmΦ))]
    apply lintegral_congr
    intro t
    trans (∫⁻ x, (‖h x‖ₑ * ‖K (x - t)‖ₑ) * ‖Φ t‖ₑ)
    · apply lintegral_congr
      intro x
      ring
    · rw [lintegral_mul_const'' (‖Φ t‖ₑ) (hm2 t), mul_comm]

private theorem W_periodic (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hcont : Continuous K) :
    Function.Periodic (fun t : ℝ => ∫⁻ x, ‖h x‖ₑ * ‖K (x - t)‖ₑ) 1 := by
  intro t
  show (∫⁻ x, ‖h x‖ₑ * ‖K (x - (t + 1))‖ₑ) = ∫⁻ x, ‖h x‖ₑ * ‖K (x - t)‖ₑ
  have hshift : (∫⁻ x, ‖h x‖ₑ * ‖K (x - (t + 1))‖ₑ)
      = ∫⁻ x, ‖h (x + 1)‖ₑ * ‖K (x + 1 - (t + 1))‖ₑ := by
    rw [lintegral_add_right_eq_self (fun y : ℝ => ‖h y‖ₑ * ‖K (y - (t + 1))‖ₑ) 1]
  rw [hshift]
  apply lintegral_congr
  intro x
  have hp : h (x + 1) = h x := by simpa using hper x
  rw [hp]
  congr 2
  ring

private theorem W_mass (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hmh : AEMeasurable (fun x : ℝ => ‖h x‖ₑ) volume) (hcont : Continuous K)
    (hK : Integrable K) :
    ∫⁻ τ in Set.Ioc (0:ℝ) 1, (∫⁻ x, ‖h x‖ₑ * ‖K (x - τ)‖ₑ)
      = (∫⁻ β in Set.Ioc (0:ℝ) 1, ‖h β‖ₑ) * (∫⁻ s, ‖K s‖ₑ) := by
  -- joint measurability
  have hmK : AEMeasurable (fun p : ℝ × ℝ => ‖K (p.1 - p.2)‖ₑ) (volume.prod volume) :=
    ((hcont.measurable.comp (by fun_prop : Measurable (fun p : ℝ × ℝ => p.1 - p.2))).enorm).aemeasurable
  have hmhs : AEMeasurable (fun p : ℝ × ℝ => ‖h p.2‖ₑ) (volume.prod volume) :=
    hmh.comp_quasiMeasurePreserving
      (by fun_prop : QuasiMeasurePreserving Prod.snd (volume.prod volume) volume)
  have hjoint : AEMeasurable (Function.uncurry (fun τ x : ℝ => ‖h x‖ₑ * ‖K (x - τ)‖ₑ))
      ((volume.restrict (Set.Ioc (0:ℝ) 1)).prod volume) := by
    have hle : (volume.restrict (Set.Ioc (0:ℝ) 1)).prod (volume : Measure ℝ)
        ≤ (volume : Measure ℝ).prod volume :=
      Measure.prod_mono Measure.restrict_le_self (le_refl (volume : Measure ℝ))
    have hmK' : AEMeasurable (fun p : ℝ × ℝ => ‖K (p.2 - p.1)‖ₑ) (volume.prod volume) :=
      ((hcont.measurable.comp (by fun_prop : Measurable (fun p : ℝ × ℝ => p.2 - p.1))).enorm).aemeasurable
    have hh := (hmhs.mul hmK').mono_measure hle
    rw [show ((fun p : ℝ × ℝ => ‖h p.2‖ₑ) * (fun p : ℝ × ℝ => ‖K (p.2 - p.1)‖ₑ))
        = (fun p : ℝ × ℝ => ‖h p.2‖ₑ * ‖K (p.2 - p.1)‖ₑ) from rfl] at hh
    exact hh
  -- W measurability (needed later)
  have hWmeas : AEMeasurable (fun x : ℝ => (∫⁻ τ in Set.Ioc (0:ℝ) 1, ‖K (x - τ)‖ₑ)) volume := by
    have h2 : AEMeasurable (Function.uncurry (fun x τ : ℝ => ‖K (x - τ)‖ₑ))
        (volume.prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
      have hle : (volume : Measure ℝ).prod (volume.restrict (Set.Ioc (0:ℝ) 1))
          ≤ (volume : Measure ℝ).prod volume :=
        Measure.prod_mono (le_refl (volume : Measure ℝ)) Measure.restrict_le_self
      have h := hmK.mono_measure hle
      exact h
    exact h2.lintegral_prod_right
  -- step A: Tonelli
  have hA : ∫⁻ τ in Set.Ioc (0:ℝ) 1, (∫⁻ x, ‖h x‖ₑ * ‖K (x - τ)‖ₑ)
      = ∫⁻ x, ∫⁻ τ in Set.Ioc (0:ℝ) 1, ‖h x‖ₑ * ‖K (x - τ)‖ₑ := by
    rw [lintegral_lintegral_swap (μ := volume.restrict (Set.Ioc (0:ℝ) 1)) (ν := volume) hjoint]
  rw [hA]
  -- step B: pull out ‖h x‖ and reflect
  have hB : ∀ x : ℝ, (∫⁻ τ in Set.Ioc (0:ℝ) 1, ‖h x‖ₑ * ‖K (x - τ)‖ₑ)
      = ‖h x‖ₑ * (∫⁻ s in Set.Ico (x - 1) x, ‖K s‖ₑ) := by
    intro x
    have hm1 : AEMeasurable (fun τ : ℝ => ‖K (x - τ)‖ₑ) volume :=
      ((hcont.measurable.comp (by fun_prop : Measurable (fun τ : ℝ => x - τ))).enorm).aemeasurable
    rw [lintegral_const_mul'' (μ := volume.restrict (Set.Ioc (0:ℝ) 1)) (‖h x‖ₑ)
      (hm1.mono_measure Measure.restrict_le_self)]
    rw [lintegral_Ioc_reflect (fun s => ‖K s‖ₑ) x]
  simp only [hB]
  -- step C: periodic decomposition in x
  have hgmeas : AEMeasurable (fun x : ℝ => ∫⁻ s in Set.Ico (x - 1) x, ‖K s‖ₑ) volume := by
    have := hWmeas
    convert this using 2 with x
    exact (lintegral_Ioc_reflect (fun s => ‖K s‖ₑ) x).symm
  have hper' : Function.Periodic (fun x : ℝ => ‖h x‖ₑ) 1 :=
    fun x => congrArg (fun z => ‖z‖ₑ) (hper x)
  rw [lintegral_periodic_mul hmh hgmeas hper']
  -- step D: the tsum of the sliding windows
  have hD : ∀ β : ℝ, ∑' m : ℤ, (∫⁻ s in Set.Ico (β + m - 1) (β + m), ‖K s‖ₑ) = ∫⁻ s, ‖K s‖ₑ := by
    intro β
    have hbase := tsum_lintegral_Ico_shift (fun s : ℝ => ‖K s‖ₑ) (β - 1)
    rw [← hbase]
    apply tsum_congr
    intro m
    congr 2 <;> ring
  simp only [hD]
  -- step E: pull out the constant
  have hmK' : AEMeasurable (fun β : ℝ => ‖h β‖ₑ) volume := hmh
  rw [lintegral_mul_const'' (μ := volume.restrict (Set.Ioc (0:ℝ) 1)) (∫⁻ s, ‖K s‖ₑ)
    (hmK'.mono_measure Measure.restrict_le_self), mul_comm]

private theorem periodic_aestronglyMeasurable (h : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) : AEStronglyMeasurable h volume := by
  have hInt_all : ∀ n : ℤ, IntervalIntegrable h volume (n:ℝ) ((n:ℝ) + 1) :=
    fun n => hper.intervalIntegrable₀ (by norm_num) hh (n:ℝ) ((n:ℝ) + 1)
  have hcover : (Set.univ : Set ℝ) = ⋃ n : ℤ, Set.Ioc (n:ℝ) ((n:ℝ) + 1) := by
    rw [← iUnion_Ioc_intCast]
  rw [← Measure.restrict_univ (μ := (volume : Measure ℝ)), hcover,
    aestronglyMeasurable_iUnion_iff]
  intro n
  exact (hInt_all n).aestronglyMeasurable

private theorem lintegral_Ioc_lt_top_of_intervalIntegrable (h : ℝ → ℂ)
    (hh : IntervalIntegrable h volume 0 1) :
    ∫⁻ x in Set.Ioc (0:ℝ) 1, ‖h x‖ₑ < ⊤ :=
  hasFiniteIntegral_iff_enorm.mp hh.1.hasFiniteIntegral

-- ENNReal version of the two one-sided bounds
private theorem enorm_tsum_pos_le (Φ : ℝ → ℂ) (D τ : ℝ) (hD : 0 ≤ D)
    (hdec : ∀ x : ℝ, ‖Φ x‖ ≤ D / (1 + x^2)) (hτ : 0 ≤ τ) :
    ∑' k : ℕ, ‖Φ (τ + (((k:ℤ) + 1 : ℤ) : ℝ))‖ₑ ≤ ENNReal.ofReal (3 * D) := by
  have hterm : ∀ k : ℕ, ‖Φ (τ + (((k:ℤ) + 1 : ℤ) : ℝ))‖ₑ
      ≤ ENNReal.ofReal (D * (1 / ((k:ℝ)+1)^2)) := by
    intro k
    have harg : τ + ((((k:ℤ) + 1 : ℤ)) : ℝ) = τ + ((k:ℝ) + 1) := by push_cast; ring
    have hcoe : ∀ z : ℂ, ‖z‖ₑ = ENNReal.ofReal ‖z‖ := fun z => by simp [enorm_eq_nnnorm]
    rw [harg, hcoe]
    apply ENNReal.ofReal_le_ofReal
    have h1 : (0:ℝ) < 1 + (τ + ((k:ℝ) + 1))^2 := by positivity
    have h2 : (0:ℝ) < ((k:ℝ)+1)^2 := by positivity
    have h3 : ((k:ℝ)+1)^2 ≤ 1 + (τ + ((k:ℝ) + 1))^2 := by nlinarith
    calc ‖Φ (τ + ((k:ℝ) + 1))‖ ≤ D / (1 + (τ + ((k:ℝ) + 1))^2) := hdec _
      _ ≤ D / ((k:ℝ)+1)^2 := div_le_div_of_nonneg_left hD h2 h3
      _ = D * (1 / ((k:ℝ)+1)^2) := by rw [mul_one_div]
  refine (ENNReal.tsum_le_tsum hterm).trans ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) (zeta_succ_nat_summable.mul_left D)]
  apply ENNReal.ofReal_le_ofReal
  have hle : ∑' k : ℕ, D * (1 / ((k:ℝ)+1)^2) = D * ∑' k : ℕ, (1:ℝ) / ((k:ℝ)+1)^2 := by
    rw [tsum_mul_left]
  rw [hle]
  nlinarith [zeta_succ_nat_le, hD]

private theorem enorm_tsum_neg_le (Φ : ℝ → ℂ) (D τ : ℝ) (hD : 0 ≤ D)
    (hdec : ∀ x : ℝ, ‖Φ x‖ ≤ D / (1 + x^2)) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    ∑' k : ℕ, ‖Φ (τ + ((-(((k:ℤ) + 1)) : ℤ) : ℝ))‖ₑ ≤ ENNReal.ofReal (6 * D) := by
  have hterm : ∀ k : ℕ, ‖Φ (τ + ((-(((k:ℤ) + 1)) : ℤ) : ℝ))‖ₑ
      ≤ ENNReal.ofReal (D * (2 / ((k:ℝ)+1)^2)) := by
    intro k
    have harg : τ + ((-(((k:ℤ) + 1)) : ℤ) : ℝ) = τ - ((k:ℝ) + 1) := by push_cast; ring
    have hcoe : ∀ z : ℂ, ‖z‖ₑ = ENNReal.ofReal ‖z‖ := fun z => by simp [enorm_eq_nnnorm]
    rw [harg, hcoe]
    apply ENNReal.ofReal_le_ofReal
    have h1 : (0:ℝ) < 1 + (τ - ((k:ℝ) + 1))^2 := by positivity
    have h2 : (0:ℝ) < ((k:ℝ)+1)^2 := by positivity
    have h3 : ((k:ℝ)+1)^2 ≤ 2 * (1 + (τ - ((k:ℝ) + 1))^2) := by
      nlinarith [sq_nonneg ((k:ℝ) - 1), sq_nonneg (τ - ((k:ℝ)+1)), sq_nonneg (k:ℝ)]
    calc ‖Φ (τ - ((k:ℝ) + 1))‖ ≤ D / (1 + (τ - ((k:ℝ) + 1))^2) := hdec _
      _ ≤ D * (2 / ((k:ℝ)+1)^2) := by
          rw [div_le_iff₀ h1]
          have hsplit : D * (2 / ((k:ℝ)+1)^2) * (1 + (τ - ((k:ℝ) + 1))^2)
              = 2 * D * (1 + (τ - ((k:ℝ) + 1))^2) / ((k:ℝ)+1)^2 := by ring
          rw [hsplit, le_div_iff₀ h2]
          nlinarith
  refine (ENNReal.tsum_le_tsum hterm).trans ?_
  have hsum2 : Summable (fun k : ℕ => D * (2 / ((k:ℝ)+1)^2)) := by
    have h := zeta_succ_nat_summable.mul_left (2 * D)
    refine h.congr (fun k => ?_)
    simp only [div_eq_mul_inv]
    ring
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum2]
  apply ENNReal.ofReal_le_ofReal
  have hle : ∑' k : ℕ, D * (2 / ((k:ℝ)+1)^2) = 2 * D * ∑' k : ℕ, (1:ℝ) / ((k:ℝ)+1)^2 := by
    have hfun : (fun k : ℕ => D * (2 / ((k:ℝ)+1)^2))
        = (fun k : ℕ => (2 * D) * (1 / ((k:ℝ)+1)^2)) := by
      funext k
      simp only [div_eq_mul_inv]
      ring
    rw [hfun, tsum_mul_left]
  rw [hle]
  nlinarith [zeta_succ_nat_le, hD]

private theorem phi_periodisation_enorm (Φ : ℝ → ℂ) (D : ℝ) (hD : 0 < D)
    (hdec : ∀ x : ℝ, ‖Φ x‖ ≤ D / (1 + x^2)) :
    ∀ u : ℝ, ∑' n : ℤ, ‖Φ (u + n)‖ₑ ≤ ENNReal.ofReal (10 * D) := by
  have hcoe : ∀ z : ℂ, ‖z‖ₑ = ENNReal.ofReal ‖z‖ := fun z => by simp [enorm_eq_nnnorm]
  have core : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → ∑' n : ℤ, ‖Φ (τ + n)‖ₑ ≤ ENNReal.ofReal (10 * D) := by
    intro τ hτ0 hτ1
    have hkey := tsum_of_add_one_of_neg_add_one (f := fun n : ℤ => ‖Φ (τ + n)‖ₑ)
      ENNReal.summable ENNReal.summable
    rw [hkey]
    have hp := enorm_tsum_pos_le Φ D τ hD.le hdec hτ0
    have hn := enorm_tsum_neg_le Φ D τ hD.le hdec hτ0 hτ1
    have h0 : ‖Φ (τ + ((0:ℤ) : ℝ))‖ₑ ≤ ENNReal.ofReal D := by
      have harg : τ + ((0:ℤ) : ℝ) = τ := by push_cast; ring
      rw [harg, hcoe]
      apply ENNReal.ofReal_le_ofReal
      have h1 : (0:ℝ) < 1 + τ^2 := by positivity
      calc ‖Φ τ‖ ≤ D / (1 + τ^2) := hdec τ
        _ ≤ D := by
            rw [div_le_iff₀ h1]
            nlinarith [hD.le, sq_nonneg τ]
    have hs := add_le_add (add_le_add hp h0) hn
    refine hs.trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    linarith
  intro u
  have hu : u = Int.fract u + (⌊u⌋ : ℝ) := by rw [Int.fract_add_floor]
  have harg : ∀ n : ℤ, u + (n:ℝ) = Int.fract u + ((n + ⌊u⌋ : ℤ) : ℝ) := by
    intro n
    conv_lhs => rw [hu]
    push_cast
    ring
  calc ∑' n : ℤ, ‖Φ (u + n)‖ₑ
      = ∑' n : ℤ, ‖Φ (Int.fract u + ((n + ⌊u⌋ : ℤ) : ℝ))‖ₑ := by
        apply tsum_congr; intro n; rw [harg n]
    _ = ∑' n : ℤ, ‖Φ (Int.fract u + (n:ℝ))‖ₑ :=
        (Equiv.addRight ⌊u⌋).tsum_eq (fun n : ℤ => ‖Φ (Int.fract u + (n:ℝ))‖ₑ)
    _ ≤ ENNReal.ofReal (10 * D) := core (Int.fract u) (Int.fract_nonneg u) (Int.fract_lt_one u).le

/-- LEAF. Step 1 of the proof, the integrability of the integrand: for periodic `h`
that is interval integrable on `[0,1]` and for `K` integrable, continuous and with
Fourier transform vanishing outside `[-1,1]`, the modulated product
`α ↦ h α * K α * e(-αv)` is integrable on the whole line.

This is the step that uses the compact Fourier support of `K`: it bounds `K` by the
`L¹` norm of its transform and then controls the unbounded periodic factor `h` one
unit interval at a time. It is stated with no periodization, no `tsum` and no Fourier
coefficient on the right, so it is strictly weaker than the split's main statement. -/
theorem leaf_modulated_product_integrable (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v : ℝ) :
    Integrable (fun α : ℝ => h α * K α * eC (-(α * v))) := by
  obtain ⟨Φ, D, hDpos, hΦint, hΦcont, hdec, hΦft⟩ := kernel_exists
  have hmh : AEMeasurable (fun x : ℝ => ‖h x‖ₑ) volume :=
    (periodic_aestronglyMeasurable h hper hh).aemeasurable.enorm
  have hh1 : ∫⁻ x in Set.Ioc (0:ℝ) 1, ‖h x‖ₑ < ⊤ :=
    lintegral_Ioc_lt_top_of_intervalIntegrable h hh
  have hconv : K = Φ ⋆[ContinuousLinearMap.mul ℂ ℂ] K :=
    eq_convolution_of_kernel' K Φ D hDpos hK hcont hΦint hΦcont hdec hsupp hΦft
  have hbound : ∀ x : ℝ, ‖K x‖ₑ ≤ ∫⁻ t, ‖K (x - t)‖ₑ * ‖Φ t‖ₑ :=
    knorm_bound K Φ D hDpos hK hΦint hΦcont hdec hconv
  have hperE : ∀ u : ℝ, ∑' n : ℤ, ‖Φ (u + n)‖ₑ ≤ ENNReal.ofReal (10 * D) :=
    phi_periodisation_enorm Φ D hDpos hdec
  have hWper : Function.Periodic (fun t : ℝ => ∫⁻ x, ‖h x‖ₑ * ‖K (x - t)‖ₑ) 1 :=
    W_periodic h K hper hcont
  have hWmass : ∫⁻ τ in Set.Ioc (0:ℝ) 1, (∫⁻ x, ‖h x‖ₑ * ‖K (x - τ)‖ₑ)
      = (∫⁻ β in Set.Ioc (0:ℝ) 1, ‖h β‖ₑ) * (∫⁻ s, ‖K s‖ₑ) :=
    W_mass h K hper hmh hcont hK
  have hWmeas : AEMeasurable (fun t : ℝ => ∫⁻ x, ‖h x‖ₑ * ‖K (x - t)‖ₑ) volume := by
    have hj : AEMeasurable (Function.uncurry (fun t x : ℝ => ‖h x‖ₑ * ‖K (x - t)‖ₑ))
        (volume.prod volume) := by
      have h1 : AEMeasurable (fun p : ℝ × ℝ => ‖h p.2‖ₑ) (volume.prod volume) :=
        hmh.comp_quasiMeasurePreserving
          (by fun_prop : QuasiMeasurePreserving Prod.snd (volume.prod volume) volume)
      have h2 : AEMeasurable (fun p : ℝ × ℝ => ‖K (p.2 - p.1)‖ₑ) (volume.prod volume) :=
        ((hcont.measurable.comp (by fun_prop : Measurable (fun p : ℝ × ℝ => p.2 - p.1))).enorm).aemeasurable
      have h3 := h1.mul h2
      rw [show ((fun p : ℝ × ℝ => ‖h p.2‖ₑ) * (fun p : ℝ × ℝ => ‖K (p.2 - p.1)‖ₑ))
          = (fun p : ℝ × ℝ => ‖h p.2‖ₑ * ‖K (p.2 - p.1)‖ₑ) from rfl] at h3
      exact h3
    exact hj.lintegral_prod_right
  have hPhi2 : ∫⁻ t, ‖Φ t‖ₑ * (∫⁻ x, ‖h x‖ₑ * ‖K (x - t)‖ₑ) < ⊤ := by
    have hstep := lintegral_periodic_mul hWmeas (hΦcont.measurable.enorm.aemeasurable) hWper
    have hcomm : (∫⁻ t, ‖Φ t‖ₑ * (∫⁻ x, ‖h x‖ₑ * ‖K (x - t)‖ₑ))
        = ∫⁻ t, (∫⁻ x, ‖h x‖ₑ * ‖K (x - t)‖ₑ) * ‖Φ t‖ₑ := by
      apply lintegral_congr
      intro t
      ring
    rw [hcomm, hstep]
    have hmono : ∫⁻ τ in Set.Ioc (0:ℝ) 1,
          (∫⁻ x, ‖h x‖ₑ * ‖K (x - τ)‖ₑ) * (∑' m : ℤ, ‖Φ (τ + m)‖ₑ)
        ≤ ∫⁻ τ in Set.Ioc (0:ℝ) 1,
          (∫⁻ x, ‖h x‖ₑ * ‖K (x - τ)‖ₑ) * ENNReal.ofReal (10 * D) := by
      apply lintegral_mono
      intro τ
      exact mul_le_mul_right (hperE τ) _
    refine lt_of_le_of_lt hmono ?_
    rw [lintegral_mul_const'' (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
      (ENNReal.ofReal (10 * D)) (hWmeas.mono_measure Measure.restrict_le_self), hWmass]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top hh1 (hasFiniteIntegral_iff_enorm.mp hK.hasFiniteIntegral))
      ENNReal.ofReal_lt_top
  have hchain : ∫⁻ x, ‖h x‖ₑ * ‖K x‖ₑ < ⊤ :=
    lt_of_le_of_lt (swap_step h K Φ hmh hK hcont hΦcont hbound) hPhi2
  have h1 : Integrable (fun α : ℝ => h α * K α) :=
    ⟨(periodic_aestronglyMeasurable h hper hh).mul hcont.aestronglyMeasurable,
      hasFiniteIntegral_iff_enorm.mpr (by simpa [enorm_mul] using hchain)⟩
  have hcont_e : Continuous fun α : ℝ => eC (-(α * v)) := by
    have hc : Continuous eC := by unfold eC; fun_prop
    exact hc.comp (by fun_prop)
  refine h1.mul_bdd (c := 1) hcont_e.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun α => ?_))
  rw [norm_eC]

private theorem fold_pointwise (h K : ℝ → ℂ) (hper : Function.Periodic h 1) (v α : ℝ) :
    (∑' n : ℤ, h (α + n) * K (α + n) * eC (-((α + n) * v))) =
      h α * (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) := by
  have hterm : ∀ n : ℤ,
      h (α + n) * K (α + n) * eC (-((α + n) * v))
        = h α * (K (α + n) * eC (-((α + n) * v))) := by
    intro n
    have hp : h (α + (n : ℝ)) = h α := by
      simpa using hper.int_mul n α
    rw [hp, mul_assoc]
  calc (∑' n : ℤ, h (α + n) * K (α + n) * eC (-((α + n) * v)))
      = ∑' n : ℤ, h α * (K (α + n) * eC (-((α + n) * v))) := tsum_congr hterm
    _ = h α * ∑' n : ℤ, K (α + n) * eC (-((α + n) * v)) := tsum_mul_left

/-- LEAF. Step 2 of the proof, the fold: with the modulated product integrable, the
integral of `h α * K α * e(-αv)` over the whole real line equals the integral over one
period `[0,1]` of `h α` against the sum of the integer translates of `K` modulated at
`v`. The period of `h` is what moves it out of the sum. -/
theorem leaf_fold (h K : ℝ → ℂ) (hper : Function.Periodic h 1) (v : ℝ)
    (hg : Integrable (fun α : ℝ => h α * K α * eC (-(α * v)))) :
    (∫ α, h α * K α * eC (-(α * v))) =
      ∫ α in (0 : ℝ)..1, h α * (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) := by
  set g : ℝ → ℂ := fun α => h α * K α * eC (-(α * v)) with hgdef
  -- (A) the whole line is the sum of its unit translates
  have hA : HasSum (fun n : ℤ => ∫ α in (0 : ℝ)..1, g (α + n)) (∫ α, g α) :=
    hg.hasSum_intervalIntegral_comp_add_int
  -- (B) on the restricted measure
  have hB : ∀ n : ℤ, (∫ α in (0 : ℝ)..1, g (α + n))
      = ∫ α, g (α + n) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro n
    rw [intervalIntegral.integral_of_le zero_le_one]
  -- (C) summability of the shifted norms
  have hnorm : Summable (fun n : ℤ => ∫ α, ‖g (α + n)‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    have h1 : HasSum (fun n : ℤ => ∫ α in (0 : ℝ)..1, ‖g (α + n)‖) (∫ α, ‖g α‖) :=
      hg.norm.hasSum_intervalIntegral_comp_add_int
    have h2 : (fun n : ℤ => ∫ α in (0 : ℝ)..1, ‖g (α + n)‖)
        = (fun n : ℤ => ∫ α, ‖g (α + n)‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
      funext n
      rw [intervalIntegral.integral_of_le zero_le_one]
    rw [h2] at h1
    exact h1.summable
  -- (D) interchange sum and integral over one period
  have hint : ∀ n : ℤ, Integrable (fun α : ℝ => g (α + n))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro n
    have hgn : Integrable (fun α : ℝ => g (α + n)) := by
      simpa [sub_eq_add_neg, add_comm] using hg.comp_sub_right (-(n : ℝ))
    exact hgn.mono_measure (Measure.restrict_le_self)
  have hD := hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (F := fun n : ℤ => fun α : ℝ => g (α + n))
    hint hnorm
  -- the two HasSums have the same summand
  have hsummand : ∀ n : ℤ, (∫ α in (0 : ℝ)..1, g (α + n))
      = ∫ α, g (α + n) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := hB
  have hA' : HasSum (fun n : ℤ => ∫ α, g (α + n) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
      (∫ α, g α) := by
    have := hA
    rwa [funext hsummand] at this
  have huniq : (∫ α, g α) = ∫ α, (∑' n : ℤ, g (α + n)) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hA'.unique hD
  rw [huniq]
  -- identify the restricted integral with the interval integral
  rw [intervalIntegral.integral_of_le zero_le_one]
  -- and the pointwise sum with the folded kernel
  refine integral_congr_ae (Filter.Eventually.of_forall (fun α => ?_))
  exact fold_pointwise h K hper v α

/-- LEAF. Step 3 of the proof, the Poisson evaluation of the folded kernel: for every
shift `α` the sum of the integer translates of `K` modulated at `v` reduces to the two
adjacent Fourier frequencies of `v`, with the coefficients `ftR K (Int.fract v)` and
`ftR K (Int.fract v - 1)`. Only the translate sums survive, so no `h` appears here. -/
theorem leaf_poisson (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
      eC (-(α * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) +
        eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1) := by
  sorry

/-! ### Assembly -/

/-- Lemma 1 from the three leaves above: the unchanged statement of `lemma1`. -/
theorem lemma1_split : Lemma1 := by
  intro h K hper hh hK hcont hsupp v
  have hg := leaf_modulated_product_integrable h K hper hh hK hcont hsupp v
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
      rw [leaf_fold h K hper v hg]
      apply intervalIntegral.integral_congr
      intro α hα
      dsimp only
      rw [leaf_poisson K hK hcont hsupp v α]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add
        (hg0.mul_const (ftR K (Int.fract v)))
        (hg1.mul_const (ftR K (Int.fract v - 1))),
        intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
      unfold hcheck
      ring

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.lemma1_split
