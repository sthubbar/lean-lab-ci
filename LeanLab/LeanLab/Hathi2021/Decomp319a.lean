/-
P0101 Hu 2019, DOI https://doi.org/10.4064/aa190121-10-4.
Supply split of Decomp115.analytic_lower_bound, pages 192 to 199.
The three analytic inputs stay open. The sealed original file is unchanged.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Decomp115

open Finset Real MeasureTheory Filter Topology LeanLab.Hathi2021.Decomp115

namespace LeanLab.Hathi2021.Decomp319a

/-- Page 192. The common logarithmic scale L. -/
noncomputable def L (n₁ : ℕ) : ℝ := Decomp115.logScale n₁

/-- Page 192. The lower cutoff for prime and prime square variables. -/
noncomputable def cutoff (n₁ n : ℕ) : ℝ := (n : ℝ) * L n₁ ^ (-9 : ℤ)

/-- Page 192. The additive character e of t equals exp of 2 pi i t. -/
noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-- Page 192. The prime exponential sum S with the strict lower cutoff. -/
noncomputable def S (n₁ n : ℕ) (α : ℝ) : ℂ :=
  ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧ cutoff n₁ n < (p : ℝ)),
    (Real.log p : ℂ) * e (p * α)

/-- Page 192. The prime square exponential sum T. -/
noncomputable def T (n₁ n : ℕ) (α : ℝ) : ℂ :=
  ∑ p ∈ (range (n + 1)).filter (fun p : ℕ =>
    p.Prime ∧ cutoff n₁ n < (p : ℝ) ^ 2 ∧ p ^ 2 ≤ n),
    (Real.log p : ℂ) * e (p ^ 2 * α)

/-- Page 192. The shared sum G over positive exponents from 4 through L. -/
noncomputable def G (n₁ : ℕ) (α : ℝ) : ℂ :=
  ∑ ν ∈ Icc 4 ⌊L n₁⌋₊, e ((2 : ℝ) ^ ν * α)

/-- Page 192. Fix the small arc parameter at one part in ten to power twenty. -/
noncomputable def arcP (n : ℕ) : ℝ := (n : ℝ) ^ (1 / 6 - 1 / 10 ^ 20 : ℝ)

/-- Page 192. The rational arc denominator parameter uses the common L. -/
noncomputable def arcQ (n₁ n : ℕ) : ℝ := (n : ℝ) * L n₁ ^ (-10 : ℤ) / arcP n

/-- Page 192. Major arcs are rational neighborhoods modulo one.
The integer translate includes the neighborhood of zero on the unit square. -/
noncomputable def majorOne (n₁ n : ℕ) : Set ℝ :=
  {α | ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ arcP n ∧
    ∃ a : ℕ, a < q ∧ Nat.Coprime a q ∧
      ∃ z : ℤ, |α - (a : ℝ) / q - z| ≤ 1 / ((q : ℝ) * arcQ n₁ n)}

/-- Page 193. The major region is the product of the two one dimensional regions. -/
noncomputable def major (n₁ n₂ : ℕ) : Set (ℝ × ℝ) :=
  (majorOne n₁ n₁) ×ˢ (majorOne n₁ n₂)

/-- Page 192, Lemma 2.3 on page 194. The large G exceptional region. -/
noncomputable def exceptional (n₁ : ℕ) : Set (ℝ × ℝ) :=
  {α | (PairLinnik.lam : ℝ) * L n₁ ≤ ‖G n₁ (α.1 + α.2)‖}

/-- Page 193. The full two dimensional Fourier integrand at k equal to 82. -/
noncomputable def integrand (n₁ n₂ : ℕ) (α : ℝ × ℝ) : ℂ :=
  S n₁ n₁ α.1 * T n₁ n₁ α.1 ^ 2 *
    S n₁ n₂ α.2 * T n₁ n₂ α.2 ^ 2 *
      G n₁ (α.1 + α.2) ^ 82 * e (-(α.1 * n₁ + α.2 * n₂))

/-- Page 193. Integrate over a region inside the unit square and take the real part. -/
noncomputable def arcIntegral (n₁ n₂ : ℕ) (A : Set (ℝ × ℝ)) : ℝ :=
  (∫ α in (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∩ A,
    integrand n₁ n₂ α).re

/-- Page 193. The major arc contribution R1. -/
noncomputable def R1 (n₁ n₂ : ℕ) : ℝ := arcIntegral n₁ n₂ (major n₁ n₂)

/-- Page 193. The exceptional minor arc contribution R2. -/
noncomputable def R2 (n₁ n₂ : ℕ) : ℝ :=
  arcIntegral n₁ n₂ ((major n₁ n₂)ᶜ ∩ exceptional n₁)

/-- Page 193. The remaining minor arc contribution R3. -/
noncomputable def R3 (n₁ n₂ : ℕ) : ℝ :=
  arcIntegral n₁ n₂ ((major n₁ n₂)ᶜ ∩ (exceptional n₁)ᶜ)

/-- Page 193. The paper count on the same finite ambient set as the enlarged count.
The restrictions match the exponential sums with strict lower prime cutoffs. -/
noncomputable def restrictedCount (n₁ n₂ : ℕ) : ℝ := by
  classical
  exact ∑ x : (Fin 6 → Fin (n₁ + 1)) × (Fin 82 → Fin (n₁ + 1)),
    if Decomp115.PairWitness n₁ n₂ (fun i => (x.1 i).val) (fun i => (x.2 i).val) ∧
      (∀ j, 4 ≤ (x.2 j).val ∧ ((x.2 j).val : ℝ) ≤ L n₁) ∧
      cutoff n₁ n₁ < ((x.1 0).val : ℝ) ∧
      cutoff n₁ n₁ < ((x.1 1).val : ℝ) ^ 2 ∧
      cutoff n₁ n₁ < ((x.1 2).val : ℝ) ^ 2 ∧
      cutoff n₁ n₂ < ((x.1 3).val : ℝ) ∧
      cutoff n₁ n₂ < ((x.1 4).val : ℝ) ^ 2 ∧
      cutoff n₁ n₂ < ((x.1 5).val : ℝ) ^ 2
    then ∏ i : Fin 6, Real.log ((x.1 i).val : ℝ) else 0

/-- Page 193. Restricting the nonnegative solution weights lowers the count. -/
theorem restrictedCount_le (n₁ n₂ : ℕ) :
    restrictedCount n₁ n₂ ≤ Decomp115.weightedCount n₁ n₂ := by
  classical
  unfold restrictedCount Decomp115.weightedCount
  apply Finset.sum_le_sum
  intro x _
  split_ifs with h h' h'
  · exact le_rfl
  · exact (h' h.1).elim
  · exact (Decomp115.prime_weight_pos _ h'.1).le
  · exact le_rfl

/-- Page 199. The common nonnegative scale N1 N2 L to power 82. -/
noncomputable def scale (n₁ n₂ : ℕ) : ℝ := (n₁ : ℝ) * n₂ * L n₁ ^ 82

/-- Page 199. The scale is nonnegative even outside the eventual domain. -/
theorem scale_nonneg (n₁ n₂ : ℕ) : 0 ≤ scale n₁ n₂ := by
  unfold scale
  positivity

/-- Page 192. Every value of the additive character has norm one. -/
theorem norm_e (t : ℝ) : ‖e t‖ = 1 := by
  have h : 2 * Real.pi * Complex.I * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e, h]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Pages 194 and 199. The trivial bound for G counts its allowed exponents. -/
theorem norm_G_le_card (n₁ : ℕ) (α : ℝ) :
    ‖G n₁ α‖ ≤ ((Icc 4 ⌊L n₁⌋₊).card : ℝ) := by
  unfold G
  calc
    ‖∑ ν ∈ Icc 4 ⌊L n₁⌋₊, e ((2 : ℝ) ^ ν * α)‖ ≤
        ∑ ν ∈ Icc 4 ⌊L n₁⌋₊, ‖e ((2 : ℝ) ^ ν * α)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_e, sum_const, nsmul_eq_mul, mul_one]

/-- Pages 194 and 199. On the eventual domain, the trivial G bound is L. -/
theorem norm_G_le (n₁ : ℕ) (hn₁ : 16 ≤ n₁) (α : ℝ) : ‖G n₁ α‖ ≤ L n₁ := by
  have hL : 0 ≤ L n₁ := (Decomp115.logScale_pos n₁ hn₁).le
  have hc : (Icc 4 ⌊L n₁⌋₊).card ≤ ⌊L n₁⌋₊ := by
    rw [Nat.card_Icc]
    omega
  exact (norm_G_le_card n₁ α).trans
    ((by exact_mod_cast hc : ((Icc 4 ⌊L n₁⌋₊).card : ℝ) ≤ ⌊L n₁⌋₊).trans (Nat.floor_le hL))

/-- Page 193. The finite Fourier integrand is continuous on the real plane. -/
theorem continuous_integrand (n₁ n₂ : ℕ) : Continuous (integrand n₁ n₂) := by
  unfold integrand S T G e
  fun_prop

/-- Page 193. The full integrand is integrable on the unit square. -/
theorem integrableOn_integrand (n₁ n₂ : ℕ) :
    IntegrableOn (integrand n₁ n₂) (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  exact (continuous_integrand n₁ n₂).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)

/-- Page 192. The countable union of rational arc neighborhoods is measurable. -/
theorem measurableSet_majorOne (n₁ n : ℕ) : MeasurableSet (majorOne n₁ n) := by
  unfold majorOne
  simp only [Set.ofPred_exists, Set.ofPred_and]
  measurability

/-- Page 193. The product major region is measurable. -/
theorem measurableSet_major (n₁ n₂ : ℕ) : MeasurableSet (major n₁ n₂) :=
  (measurableSet_majorOne n₁ n₁).prod (measurableSet_majorOne n₁ n₂)

/-- Page 192. The exceptional region is measurable by continuity of G. -/
theorem measurableSet_exceptional (n₁ : ℕ) : MeasurableSet (exceptional n₁) := by
  have hc : Continuous (fun α : ℝ × ℝ => ‖G n₁ (α.1 + α.2)‖) := by
    unfold G e
    fun_prop
  exact (isClosed_le continuous_const hc).measurableSet

/-- Page 193. The three actual arc contributions sum to the full Fourier integral. -/
theorem arcs_sum_eq_integral (n₁ n₂ : ℕ) :
    R1 n₁ n₂ + R2 n₁ n₂ + R3 n₁ n₂ =
      (∫ α in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, integrand n₁ n₂ α).re := by
  let U := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  let M := major n₁ n₂
  let E := exceptional n₁
  have hf := integrableOn_integrand n₁ n₂
  have hM := measurableSet_major n₁ n₂
  have hE := measurableSet_exceptional n₁
  have hsplit := integral_inter_add_sdiff hM hf
  have hrest := integral_inter_add_sdiff hE (hf.mono_set (Set.sdiff_subset : U \ M ⊆ U))
  have h₁ : U \ M = U ∩ Mᶜ := by ext x; simp
  have h₂ : (U \ M) ∩ E = U ∩ (Mᶜ ∩ E) := by ext x; simp [and_assoc]
  have h₃ : (U \ M) \ E = U ∩ (Mᶜ ∩ Eᶜ) := by ext x; simp [and_assoc]
  rw [h₂, h₃] at hrest
  rw [h₁] at hsplit
  have h := congrArg Complex.re hsplit
  have hr := congrArg Complex.re hrest
  change R1 n₁ n₂ + (∫ α in U ∩ Mᶜ, integrand n₁ n₂ α).re = _ at h
  change R2 n₁ n₂ + R3 n₁ n₂ = (∫ α in U ∩ Mᶜ, integrand n₁ n₂ α).re at hr
  linarith


/-- Page 192. The common logarithmic scale tends to infinity. -/
theorem tendsto_L_atTop : Tendsto L atTop atTop := by
  have hz : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hp : ∀ᶠ x : ℝ in atTop, 0 < Real.log x / x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (lt_trans zero_lt_one hx)
  have hwithin : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz, hp⟩
  have hr : Tendsto (fun x : ℝ => x / Real.log x) atTop atTop := by
    have h := hwithin.inv_tendsto_nhdsGT_zero
    change Tendsto (fun x : ℝ => (Real.log x / x)⁻¹) atTop atTop at h
    simpa only [inv_div] using h
  have hL : Tendsto (fun x : ℝ => Real.log (x / Real.log x) / Real.log 2) atTop atTop :=
    Tendsto.atTop_div_const (Real.log_pos (by norm_num)) (Real.tendsto_log_atTop.comp hr)
  exact hL.comp tendsto_natCast_atTop_atTop

/-- Pages 196 and 199. A loss of one power of L is absorbed into any positive tolerance. -/
theorem lower_order_error_le (K δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ, N₀ ≤ n₁ →
      K * ((n₁ : ℝ) * n₂ * L n₁ ^ 81) ≤ δ * scale n₁ n₂ := by
  obtain ⟨N₀, hN⟩ := eventually_atTop.mp (tendsto_L_atTop.eventually (eventually_ge_atTop (max 1 (K / δ))))
  refine ⟨N₀, ?_⟩
  intro n₁ n₂ hn₁
  have hb := hN n₁ hn₁
  have hpos : 0 ≤ L n₁ := le_trans (by norm_num) ((le_max_left _ _).trans hb)
  have hK : K ≤ δ * L n₁ := by
    have := (div_le_iff₀ hδ).mp ((le_max_right _ _).trans hb)
    linarith
  calc
    K * ((n₁ : ℝ) * n₂ * L n₁ ^ 81) ≤
        (δ * L n₁) * ((n₁ : ℝ) * n₂ * L n₁ ^ 81) :=
      mul_le_mul_of_nonneg_right hK (by positivity)
    _ = δ * scale n₁ n₂ := by
      unfold scale
      rw [show (82 : ℕ) = 81 + 1 by decide, pow_succ]
      ring

/-- Lemma 2.4, page 196. CONDITIONAL ON the explicit order bound for R2. -/
theorem exceptional_arc_small_of_order_bound (C δ K : ℝ) (hδ : 0 < δ)
    (hbound : ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      |R2 n₁ n₂| ≤ K * ((n₁ : ℝ) * n₂ * L n₁ ^ 81)) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      |R2 n₁ n₂| ≤ δ * scale n₁ n₂ := by
  obtain ⟨N₁, h₁⟩ := hbound
  obtain ⟨N₂, h₂⟩ := lower_order_error_le K δ hδ
  refine ⟨max N₁ N₂, ?_⟩
  intro n₁ n₂ ho₁ ho₂ hn hlt hratio
  exact (h₁ n₁ n₂ ho₁ ho₂ ((le_max_left _ _).trans hn) hlt hratio).trans
    (h₂ n₁ n₂ (((le_max_right _ _).trans hn).trans hlt.le))


/-- Page 193. Orthogonality of an integer frequency on one unit interval. -/
theorem integral_e_int (m : ℤ) :
    (∫ α in (0 : ℝ)..1, e ((m : ℝ) * α)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · simp [hm, e]
  · let c : ℂ := 2 * Real.pi * Complex.I * m
    have hc : c ≠ 0 := by
      dsimp [c]
      apply mul_ne_zero
      · exact mul_ne_zero (by exact_mod_cast (mul_ne_zero (by norm_num) Real.pi_ne_zero)) Complex.I_ne_zero
      · exact_mod_cast hm
    have hform : (fun α : ℝ => e ((m : ℝ) * α)) =
        (fun α : ℝ => Complex.exp (c * α)) := by
      funext α
      unfold e c
      push_cast
      congr 1
      ring
    have hper : Complex.exp c = 1 := by
      have heq : c = (m : ℂ) * (2 * Real.pi * Complex.I) := by dsimp [c]; ring
      rw [heq]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [hform, integral_exp_mul_complex hc]
    simp [hm, hper]

/-- Page 193. Every restricted prime solution has a nonnegative logarithmic weight. -/
theorem restrictedCount_nonneg (n₁ n₂ : ℕ) : 0 ≤ restrictedCount n₁ n₂ := by
  classical
  unfold restrictedCount
  apply Finset.sum_nonneg
  intro x _
  split_ifs with h
  · exact (Decomp115.prime_weight_pos _ h.1.1).le
  · exact le_rfl

/-- Page 193. Integer frequency orthogonality for the unit interval as a measurable set. -/
theorem setIntegral_e_int (m : ℤ) :
    (∫ α in Set.Icc (0 : ℝ) 1, e ((m : ℝ) * α)) = if m = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integral_e_int m

/-- Page 193. Orthogonality of two independent integer frequencies on the unit square. -/
theorem fourier_kernel_integral (m n : ℤ) :
    (∫ α in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      e ((m : ℝ) * α.1) * e ((n : ℝ) * α.2)) =
      (if m = 0 then 1 else 0) * (if n = 0 then 1 else 0) := by
  have h := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun x : ℝ => e ((m : ℝ) * x)) (fun y : ℝ => e ((n : ℝ) * y))
    (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl]
  rw [setIntegral_e_int, setIntegral_e_int] at h
  exact h

/-- Page 193. A finite Fourier sum integrates to its joint zero frequency coefficient. -/
theorem fourier_finite_sum {ι : Type*} [Fintype ι] (w : ι → ℂ) (m n : ι → ℤ) :
    (∫ α in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      ∑ i, w i * (e ((m i : ℝ) * α.1) * e ((n i : ℝ) * α.2))) =
      ∑ i, if m i = 0 ∧ n i = 0 then w i else 0 := by
  classical
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul, fourier_kernel_integral]
    split_ifs <;> simp_all
  · intro i _
    have hc : Continuous (fun α : ℝ × ℝ =>
        w i * (e ((m i : ℝ) * α.1) * e ((n i : ℝ) * α.2))) := by
      unfold e
      fun_prop
    exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

/-- Page 193. Six prime coordinates and 82 shared exponent coordinates bounded by n1. -/
abbrev Tuple (n₁ : ℕ) := (Fin 6 → Fin (n₁ + 1)) × (Fin 82 → Fin (n₁ + 1))

/-- Display 1.1, page 192. The natural sum represented by the first three primes. -/
def leftTotal (n₁ : ℕ) (x : Tuple n₁) : ℕ :=
  (x.1 0).val + (x.1 1).val ^ 2 + (x.1 2).val ^ 2 + ∑ i, 2 ^ (x.2 i).val

/-- Display 1.1, page 192. The natural sum represented by the last three primes. -/
def rightTotal (n₁ : ℕ) (x : Tuple n₁) : ℕ :=
  (x.1 3).val + (x.1 4).val ^ 2 + (x.1 5).val ^ 2 + ∑ i, 2 ^ (x.2 i).val

/-- Page 193. The first integer Fourier frequency is the represented sum minus n1. -/
def leftFrequency (n₁ : ℕ) (x : Tuple n₁) : ℤ := (leftTotal n₁ x : ℤ) - n₁

/-- Page 193. The second integer Fourier frequency is the represented sum minus n2. -/
def rightFrequency (n₁ n₂ : ℕ) (x : Tuple n₁) : ℤ := (rightTotal n₁ x : ℤ) - n₂

/-- Pages 192 and 193. The six prime log weights with the S, T and G cutoffs, before imposing either representation equality. -/
noncomputable def rawWeight (n₁ n₂ : ℕ) (x : Tuple n₁) : ℂ :=
  if (∀ i, (x.1 i).val.Prime) ∧
      (∀ j, 4 ≤ (x.2 j).val ∧ ((x.2 j).val : ℝ) ≤ L n₁) ∧
      cutoff n₁ n₁ < ((x.1 0).val : ℝ) ∧
      cutoff n₁ n₁ < ((x.1 1).val : ℝ) ^ 2 ∧
      cutoff n₁ n₁ < ((x.1 2).val : ℝ) ^ 2 ∧
      cutoff n₁ n₂ < ((x.1 3).val : ℝ) ∧
      cutoff n₁ n₂ < ((x.1 4).val : ℝ) ^ 2 ∧
      cutoff n₁ n₂ < ((x.1 5).val : ℝ) ^ 2 ∧
      (x.1 1).val ^ 2 ≤ n₁ ∧ (x.1 2).val ^ 2 ≤ n₁ ∧
      (x.1 3).val ≤ n₂ ∧ (x.1 4).val ^ 2 ≤ n₂ ∧ (x.1 5).val ^ 2 ≤ n₂
    then ∏ i : Fin 6, (Real.log ((x.1 i).val : ℝ) : ℂ) else 0

/-- Page 193. Selecting joint zero frequencies from the restricted tuple weights gives the restricted solution count. -/
theorem selected_weight_sum (n₁ n₂ : ℕ) :
    (∑ x : Tuple n₁,
      if leftFrequency n₁ x = 0 ∧ rightFrequency n₁ n₂ x = 0
      then rawWeight n₁ n₂ x else 0) = (restrictedCount n₁ n₂ : ℂ) := by
  classical
  unfold restrictedCount
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x _
  let P : Prop := (∀ i, (x.1 i).val.Prime) ∧
      (∀ j, 4 ≤ (x.2 j).val ∧ ((x.2 j).val : ℝ) ≤ L n₁) ∧
      cutoff n₁ n₁ < ((x.1 0).val : ℝ) ∧
      cutoff n₁ n₁ < ((x.1 1).val : ℝ) ^ 2 ∧
      cutoff n₁ n₁ < ((x.1 2).val : ℝ) ^ 2 ∧
      cutoff n₁ n₂ < ((x.1 3).val : ℝ) ∧
      cutoff n₁ n₂ < ((x.1 4).val : ℝ) ^ 2 ∧
      cutoff n₁ n₂ < ((x.1 5).val : ℝ) ^ 2 ∧
      (x.1 1).val ^ 2 ≤ n₁ ∧ (x.1 2).val ^ 2 ≤ n₁ ∧
      (x.1 3).val ≤ n₂ ∧ (x.1 4).val ^ 2 ≤ n₂ ∧ (x.1 5).val ^ 2 ≤ n₂
  let Q : Prop :=
    Decomp115.PairWitness n₁ n₂ (fun i => (x.1 i).val) (fun i => (x.2 i).val) ∧
      (∀ j, 4 ≤ (x.2 j).val ∧ ((x.2 j).val : ℝ) ≤ L n₁) ∧
      cutoff n₁ n₁ < ((x.1 0).val : ℝ) ∧
      cutoff n₁ n₁ < ((x.1 1).val : ℝ) ^ 2 ∧
      cutoff n₁ n₁ < ((x.1 2).val : ℝ) ^ 2 ∧
      cutoff n₁ n₂ < ((x.1 3).val : ℝ) ∧
      cutoff n₁ n₂ < ((x.1 4).val : ℝ) ^ 2 ∧
      cutoff n₁ n₂ < ((x.1 5).val : ℝ) ^ 2
  have hPQ : ((leftFrequency n₁ x = 0 ∧ rightFrequency n₁ n₂ x = 0) ∧ P) ↔ Q := by
    constructor
    · rintro ⟨⟨hl, hr⟩, hp, hν, hc₀, hc₁, hc₂, hc₃, hc₄, hc₅, _⟩
      have hl' : leftTotal n₁ x = n₁ := by
        exact_mod_cast (sub_eq_zero.mp hl)
      have hr' : rightTotal n₁ x = n₂ := by
        exact_mod_cast (sub_eq_zero.mp hr)
      refine ⟨⟨hp, ?_, hl'.symm, hr'.symm⟩, hν, hc₀, hc₁, hc₂, hc₃, hc₄, hc₅⟩
      intro i
      exact le_trans (by norm_num : (1 : ℕ) ≤ 4) (hν i).1
    · rintro ⟨⟨hp, hνpos, hl, hr⟩, hν, hc₀, hc₁, hc₂, hc₃, hc₄, hc₅⟩
      have hl' : leftTotal n₁ x = n₁ := hl.symm
      have hr' : rightTotal n₁ x = n₂ := hr.symm
      refine ⟨⟨?_, ?_⟩, hp, hν, hc₀, hc₁, hc₂, hc₃, hc₄, hc₅, ?_, ?_, ?_, ?_, ?_⟩
      · unfold leftFrequency
        rw [hl']; simp
      · unfold rightFrequency
        rw [hr']; simp
      all_goals dsimp only [leftTotal, rightTotal] at hl' hr'
      all_goals omega
  rw [apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_prod, Complex.ofReal_zero]
  change (if leftFrequency n₁ x = 0 ∧ rightFrequency n₁ n₂ x = 0 then
      if P then ∏ i : Fin 6, (Real.log ((x.1 i).val : ℝ) : ℂ) else 0 else 0) =
    if Q then ∏ i : Fin 6, (Real.log ((x.1 i).val : ℝ) : ℂ) else 0
  simp only [← hPQ]
  by_cases hz : leftFrequency n₁ x = 0 ∧ rightFrequency n₁ n₂ x = 0 <;>
    by_cases hp : P <;> simp [hz, hp]

/-- Theorem 1.1 domain, page 192. Comparable odd pairs exist beyond every threshold. -/
theorem pair_domain_unbounded (C : ℝ) (hC : 1 < C) (N : ℕ) :
    ∃ n₁ n₂ : ℕ, Odd n₁ ∧ Odd n₂ ∧ N ≤ n₂ ∧ n₂ < n₁ ∧ (n₁ : ℝ) ≤ C * n₂ := by
  obtain ⟨t, ht⟩ := exists_nat_gt (max (N : ℝ) (2 / (C - 1)))
  have htN : N < t := by exact_mod_cast ((le_max_left _ _).trans_lt ht)
  have hCt : (2 : ℝ) < (t : ℝ) * (C - 1) :=
    (div_lt_iff₀ (by linarith : 0 < C - 1)).mp ((le_max_right _ _).trans_lt ht)
  refine ⟨2 * t + 3, 2 * t + 1, ⟨t + 1, by omega⟩, ⟨t, by omega⟩, by omega, by omega, ?_⟩
  push_cast
  nlinarith


/-- Page 192. The logarithmic scale is at most the ambient integer for n at least 16. -/
theorem L_le_nat (n : ℕ) (hn : 16 ≤ n) : L n ≤ n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog16 : (1 : ℝ) ≤ Real.log 16 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    have := Real.log_two_gt_d9
    norm_num
    linarith
  have hlogge : (1 : ℝ) ≤ Real.log n :=
    hlog16.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
  have hlogpos : (0 : ℝ) < Real.log n := lt_of_lt_of_le zero_lt_one hlogge
  have hratio : (n : ℝ) / Real.log n ≤ n := by
    rw [div_le_iff₀ hlogpos]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlogge hnpos.le
  have hhalf : Real.log (n : ℝ) ≤ n / 2 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hnpos (by norm_num : (0 : ℝ) < 2))
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [Real.log_div hnpos.ne' (by norm_num)] at h
    linarith
  change Real.log ((n : ℝ) / Real.log n) / Real.log 2 ≤ n
  rw [div_le_iff₀ htwo]
  calc
    Real.log ((n : ℝ) / Real.log n) ≤ Real.log n :=
      Real.log_le_log (div_pos hnpos hlogpos) hratio
    _ ≤ n / 2 := hhalf
    _ ≤ n * Real.log 2 := by
      have hhalf2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      simpa only [div_eq_mul_inv, one_div, one_mul] using mul_le_mul_of_nonneg_left hhalf2 hnpos.le

/-- Pages 192 and 193. Embed S into the common finite prime coordinate range, with an explicit upper cutoff. -/
theorem S_eq_fin (n₁ n : ℕ) (hn : n ≤ n₁) (α : ℝ) :
    S n₁ n α = ∑ p : Fin (n₁ + 1),
      if p.val.Prime ∧ cutoff n₁ n < (p.val : ℝ) ∧ p.val ≤ n
      then (Real.log p.val : ℂ) * e (p.val * α) else 0 := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun p : ℕ =>
    if p.Prime ∧ cutoff n₁ n < (p : ℝ) ∧ p ≤ n
    then (Real.log p : ℂ) * e (p * α) else 0)]
  calc
    S n₁ n α = ∑ p ∈ range (n + 1),
        if p.Prime ∧ cutoff n₁ n < (p : ℝ) ∧ p ≤ n
        then (Real.log p : ℂ) * e (p * α) else 0 := by
      unfold S
      rw [sum_filter]
      apply sum_congr rfl
      intro p hp
      have hp' : p ≤ n := by simpa only [mem_range, Nat.lt_succ_iff] using hp
      simp only [hp', and_true]
    _ = _ := by
      apply sum_subset (range_mono (by omega))
      intro p hp hpn
      have hgt : n < p := by simp only [mem_range] at hpn; omega
      simp [not_le.mpr hgt]

/-- Pages 192 and 193. Embed T into the common finite prime coordinate range using the prime square upper bound. -/
theorem T_eq_fin (n₁ n : ℕ) (hn : n ≤ n₁) (α : ℝ) :
    T n₁ n α = ∑ p : Fin (n₁ + 1),
      if p.val.Prime ∧ cutoff n₁ n < (p.val : ℝ) ^ 2 ∧ p.val ^ 2 ≤ n
      then (Real.log p.val : ℂ) * e (p.val ^ 2 * α) else 0 := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun p : ℕ =>
    if p.Prime ∧ cutoff n₁ n < (p : ℝ) ^ 2 ∧ p ^ 2 ≤ n
    then (Real.log p : ℂ) * e (p ^ 2 * α) else 0)]
  unfold T
  rw [sum_filter]
  apply sum_subset (range_mono (by omega))
  intro p hp hpn
  have hgt : n < p := by simp only [mem_range] at hpn; omega
  have hsq : p ≤ p ^ 2 := Nat.le_self_pow two_ne_zero p
  have hnot : ¬ p ^ 2 ≤ n := by omega
  simp [hnot]

/-- Pages 192 and 193. Embed G into the common finite exponent coordinate range without losing an allowed exponent. -/
theorem G_eq_fin (n₁ : ℕ) (hn₁ : 16 ≤ n₁) (α : ℝ) :
    G n₁ α = ∑ ν : Fin (n₁ + 1),
      if 4 ≤ ν.val ∧ (ν.val : ℝ) ≤ L n₁ then e ((2 : ℝ) ^ ν.val * α) else 0 := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun ν : ℕ =>
    if 4 ≤ ν ∧ (ν : ℝ) ≤ L n₁ then e ((2 : ℝ) ^ ν * α) else 0)]
  unfold G
  rw [← sum_filter]
  have hL : 0 ≤ L n₁ := (Decomp115.logScale_pos n₁ hn₁).le
  have hfloor : ⌊L n₁⌋₊ ≤ n₁ := by
    have h := (Nat.floor_le hL).trans (L_le_nat n₁ hn₁)
    exact_mod_cast h
  apply sum_congr
  · ext ν
    simp only [mem_Icc, mem_filter, mem_range]
    rw [← Nat.le_floor_iff hL]
    omega
  · intro ν _
    rfl


/-- Page 193. The additive character turns addition of real phases into multiplication. -/
theorem e_add (s t : ℝ) : e (s + t) = e s * e t := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Page 193. The character of a finite sum is the product of the characters. -/
theorem e_sum {ι : Type*} [Fintype ι] (f : ι → ℝ) : e (∑ i, f i) = ∏ i, e (f i) := by
  unfold e
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

/-- Page 193. The prime and shared exponent phases combine into the two integer residual frequencies. -/
theorem tuple_phase (n₁ n₂ : ℕ) (x : Tuple n₁) (α : ℝ × ℝ) :
    (e ((x.1 0).val * α.1) * e (((x.1 1).val : ℝ) ^ 2 * α.1) *
      e (((x.1 2).val : ℝ) ^ 2 * α.1) * e ((x.1 3).val * α.2) *
      e (((x.1 4).val : ℝ) ^ 2 * α.2) * e (((x.1 5).val : ℝ) ^ 2 * α.2)) *
      (∏ j, e ((2 : ℝ) ^ (x.2 j).val * (α.1 + α.2))) *
      e (-(α.1 * n₁ + α.2 * n₂)) =
        e ((leftFrequency n₁ x : ℝ) * α.1) * e ((rightFrequency n₁ n₂ x : ℝ) * α.2) := by
  rw [← e_sum]
  simp_rw [← e_add]
  congr 1
  unfold leftFrequency rightFrequency leftTotal rightTotal
  push_cast
  rw [← Finset.sum_mul]
  ring

/-- Page 193, unnumbered display for R before the arc estimates.
Expand the finite products S, T and G into the common bounded tuple space.
This is a pointwise finite algebra identity, with no integration or asymptotic estimate. -/
theorem integrand_eq_raw_sum (n₁ n₂ : ℕ) (hn₂ : 16 ≤ n₂) (horder : n₂ < n₁)
    (α : ℝ × ℝ) :
    integrand n₁ n₂ α =
      ∑ x : Tuple n₁, rawWeight n₁ n₂ x *
        (e ((leftFrequency n₁ x : ℝ) * α.1) * e ((rightFrequency n₁ n₂ x : ℝ) * α.2)) := by
  classical
  have hn₁ : 16 ≤ n₁ := by omega
  let d (i : Fin 6) : ℕ := if i.val = 0 ∨ i.val = 3 then 1 else 2
  let size (i : Fin 6) : ℕ := if i.val < 3 then n₁ else n₂
  let arg (i : Fin 6) : ℝ := if i.val < 3 then α.1 else α.2
  let P (i : Fin 6) (p : Fin (n₁ + 1)) : Prop :=
    p.val.Prime ∧ cutoff n₁ (size i) < (p.val : ℝ) ^ d i ∧ p.val ^ d i ≤ size i
  let F (i : Fin 6) (p : Fin (n₁ + 1)) : ℂ :=
    if P i p then (Real.log p.val : ℂ) * e ((p.val : ℝ) ^ d i * arg i) else 0
  let Q (ν : Fin (n₁ + 1)) : Prop := 4 ≤ ν.val ∧ (ν.val : ℝ) ≤ L n₁
  let H (ν : Fin (n₁ + 1)) : ℂ := if Q ν then e ((2 : ℝ) ^ ν.val * (α.1 + α.2)) else 0
  have hF0 : (∑ p, F 0 p) = S n₁ n₁ α.1 := by
    simpa [F, P, d, size, arg] using (S_eq_fin n₁ n₁ le_rfl α.1).symm
  have hF1 : (∑ p, F 1 p) = T n₁ n₁ α.1 := by
    simpa [F, P, d, size, arg] using (T_eq_fin n₁ n₁ le_rfl α.1).symm
  have hF2 : (∑ p, F 2 p) = T n₁ n₁ α.1 := by
    simpa [F, P, d, size, arg] using (T_eq_fin n₁ n₁ le_rfl α.1).symm
  have hF3 : (∑ p, F 3 p) = S n₁ n₂ α.2 := by
    simpa [F, P, d, size, arg] using (S_eq_fin n₁ n₂ horder.le α.2).symm
  have hF4 : (∑ p, F 4 p) = T n₁ n₂ α.2 := by
    simpa [F, P, d, size, arg] using (T_eq_fin n₁ n₂ horder.le α.2).symm
  have hF5 : (∑ p, F 5 p) = T n₁ n₂ α.2 := by
    simpa [F, P, d, size, arg] using (T_eq_fin n₁ n₂ horder.le α.2).symm
  have hFprod : (∏ i : Fin 6, ∑ p, F i p) =
      S n₁ n₁ α.1 * T n₁ n₁ α.1 ^ 2 * S n₁ n₂ α.2 * T n₁ n₂ α.2 ^ 2 := by
    calc
      (∏ i : Fin 6, ∑ p, F i p) = (∑ p, F 0 p) * (∑ p, F 1 p) * (∑ p, F 2 p) * (∑ p, F 3 p) * (∑ p, F 4 p) * (∑ p, F 5 p) := by
        simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
        change (∑ p, F 0 p) * ((∑ p, F 1 p) * ((∑ p, F 2 p) *
          ((∑ p, F 3 p) * ((∑ p, F 4 p) * (∑ p, F 5 p))))) = _
        ring
      _ = _ := by rw [hF0, hF1, hF2, hF3, hF4, hF5]; ring
  have hG : G n₁ (α.1 + α.2) = ∑ ν, H ν := by
    simpa [H, Q] using G_eq_fin n₁ hn₁ (α.1 + α.2)
  unfold integrand
  rw [← hFprod, hG, Fintype.prod_sum, Fintype.sum_pow]
  simp_rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro ν _
  have hP6 : (∀ i : Fin 6, P i (p i)) ↔
      ((p 0).val.Prime ∧ cutoff n₁ n₁ < ((p 0).val : ℝ) ∧ (p 0).val ≤ n₁) ∧
      ((p 1).val.Prime ∧ cutoff n₁ n₁ < ((p 1).val : ℝ) ^ 2 ∧ (p 1).val ^ 2 ≤ n₁) ∧
      ((p 2).val.Prime ∧ cutoff n₁ n₁ < ((p 2).val : ℝ) ^ 2 ∧ (p 2).val ^ 2 ≤ n₁) ∧
      ((p 3).val.Prime ∧ cutoff n₁ n₂ < ((p 3).val : ℝ) ∧ (p 3).val ≤ n₂) ∧
      ((p 4).val.Prime ∧ cutoff n₁ n₂ < ((p 4).val : ℝ) ^ 2 ∧ (p 4).val ^ 2 ≤ n₂) ∧
      ((p 5).val.Prime ∧ cutoff n₁ n₂ < ((p 5).val : ℝ) ^ 2 ∧ (p 5).val ^ 2 ≤ n₂) := by
    simp [P, d, size, Fin.forall_fin_succ]
  have hPrime6 : (∀ i : Fin 6, (p i).val.Prime) ↔
      (p 0).val.Prime ∧ (p 1).val.Prime ∧ (p 2).val.Prime ∧ (p 3).val.Prime ∧ (p 4).val.Prime ∧ (p 5).val.Prime := by
    simp [Fin.forall_fin_succ]
  have h0 : (p 0).val ≤ n₁ := Nat.le_of_lt_succ (p 0).isLt
  have hmask : ((∀ i : Fin 6, P i (p i)) ∧ ∀ j : Fin 82, Q (ν j)) ↔
      (∀ i, (p i).val.Prime) ∧
      (∀ j, 4 ≤ (ν j).val ∧ ((ν j).val : ℝ) ≤ L n₁) ∧
      cutoff n₁ n₁ < ((p 0).val : ℝ) ∧
      cutoff n₁ n₁ < ((p 1).val : ℝ) ^ 2 ∧
      cutoff n₁ n₁ < ((p 2).val : ℝ) ^ 2 ∧
      cutoff n₁ n₂ < ((p 3).val : ℝ) ∧
      cutoff n₁ n₂ < ((p 4).val : ℝ) ^ 2 ∧
      cutoff n₁ n₂ < ((p 5).val : ℝ) ^ 2 ∧
      (p 1).val ^ 2 ≤ n₁ ∧ (p 2).val ^ 2 ≤ n₁ ∧
      (p 3).val ≤ n₂ ∧ (p 4).val ^ 2 ≤ n₂ ∧ (p 5).val ^ 2 ≤ n₂ := by
    rw [hP6, hPrime6]
    dsimp only [Q]
    simp only [h0, and_true]
    tauto
  simp only [F, H]
  rw [Fintype.prod_ite_zero, Fintype.prod_ite_zero]
  simp only [rawWeight, ← hmask]
  by_cases hp : ∀ i : Fin 6, P i (p i)
  · by_cases hν : ∀ j : Fin 82, Q (ν j)
    · simp only [ite_eq_left hp, ite_eq_left hν, ite_eq_left (And.intro hp hν)]
      rw [Finset.prod_mul_distrib]
      have hphase :
          (∏ i : Fin 6, e (((p i).val : ℝ) ^ d i * arg i)) *
            (∏ j : Fin 82, e ((2 : ℝ) ^ (ν j).val * (α.1 + α.2))) *
            e (-(α.1 * n₁ + α.2 * n₂)) =
          e ((leftFrequency n₁ (p, ν) : ℝ) * α.1) *
            e ((rightFrequency n₁ n₂ (p, ν) : ℝ) * α.2) := by
        have h6 : (∏ i : Fin 6, e (((p i).val : ℝ) ^ d i * arg i)) =
            e ((p 0).val * α.1) * e (((p 1).val : ℝ) ^ 2 * α.1) *
            e (((p 2).val : ℝ) ^ 2 * α.1) * e ((p 3).val * α.2) *
            e (((p 4).val : ℝ) ^ 2 * α.2) * e (((p 5).val : ℝ) ^ 2 * α.2) := by
          simp [d, arg, Fin.prod_univ_succ]
          ring
        rw [h6]
        exact tuple_phase n₁ n₂ (p, ν) α
      calc
        _ = (∏ i : Fin 6, (Real.log (p i).val : ℂ)) *
            ((∏ i : Fin 6, e (((p i).val : ℝ) ^ d i * arg i)) *
              (∏ j : Fin 82, e ((2 : ℝ) ^ (ν j).val * (α.1 + α.2))) *
                e (-(α.1 * n₁ + α.2 * n₂))) := by ring
        _ = _ := by rw [hphase]
    · simp [hp, hν]
  · simp [hp]

/-- Page 193, the finite Fourier count identity before splitting into arcs.
Finite Fourier orthogonality applied to the exact finite product expansion. -/
theorem restrictedCount_eq_integral (n₁ n₂ : ℕ) (hn₂ : 16 ≤ n₂) (horder : n₂ < n₁) :
    restrictedCount n₁ n₂ =
      (∫ α in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, integrand n₁ n₂ α).re := by
  have hfun := funext (integrand_eq_raw_sum n₁ n₂ hn₂ horder)
  rw [hfun, fourier_finite_sum, selected_weight_sum]
  rfl

/-- Page 193, displayed decomposition R equals R1 plus R2 plus R3.
This combines the exact Fourier count identity with the measurable partition.
This is finite Fourier orthogonality and partition of the unit square.
It does not include any prime distribution estimate. -/
theorem restrictedCount_eq_arcs (n₁ n₂ : ℕ) (hn₂ : 16 ≤ n₂) (horder : n₂ < n₁) :
    restrictedCount n₁ n₂ = R1 n₁ n₂ + R2 n₁ n₂ + R3 n₁ n₂ := by
  rw [restrictedCount_eq_integral n₁ n₂ hn₂ horder, arcs_sum_eq_integral]

set_option maxRecDepth 2000 in
/-- Helper for pages 192 and 193. The strict cutoff count is positive at an
explicit unequal odd pair. The prime triples are 5,3,3 and 3,3,3 and all 82
shared exponents equal 4. This checks a nonzero instance of the actual count. -/
theorem restrictedCount_example : 0 < restrictedCount 1335 1333 := by
  classical
  have hlogpos : 0 < Real.log (1335 : ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log (1335 : ℝ) ≤ 11 := by
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 1335)
      (by norm_num : (1335 : ℝ) ≤ 2 ^ 11)
    rw [Real.log_pow] at hm
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hm htwo
    linarith
  have hL : (4 : ℝ) ≤ L 1335 := by
    unfold L logScale
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    have hratio : (16 : ℝ) ≤ 1335 / Real.log 1335 := by
      apply (le_div_iff₀ hlogpos).2
      linarith
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hratio
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    rw [h16] at hm
    exact hm
  have hcut (n : ℕ) (hn : n ≤ 1335) : cutoff 1335 n < 3 := by
    unfold cutoff
    have hp : 0 < L 1335 := by linarith
    have hpow : (4 : ℝ) ^ 9 ≤ L 1335 ^ 9 := by gcongr
    rw [zpow_neg, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (pow_pos hp 9)).2
    have hn' : (n : ℝ) ≤ 1335 := by exact_mod_cast hn
    norm_num at hpow
    linarith
  let p : Fin 6 → Fin (1335 + 1) := fun i => if i = 0 then ⟨5, by norm_num⟩ else ⟨3, by norm_num⟩
  let ν : Fin 82 → Fin (1335 + 1) := fun _ => ⟨4, by norm_num⟩
  have hprime : ∀ i, (p i).val.Prime := by
    intro i
    dsimp [p]
    split_ifs <;> norm_num
  have hw : PairWitness 1335 1333 (fun i => (p i).val) (fun i => (ν i).val) := by
    refine ⟨hprime, ?_, ?_, ?_⟩
    · intro i; norm_num [ν]
    · norm_num [p, ν]
    · norm_num [p, ν]
  let w (x : Tuple 1335) : ℝ :=
    if Decomp115.PairWitness 1335 1333 (fun i => (x.1 i).val) (fun i => (x.2 i).val) ∧
      (∀ j, 4 ≤ (x.2 j).val ∧ ((x.2 j).val : ℝ) ≤ L 1335) ∧
      cutoff 1335 1335 < ((x.1 0).val : ℝ) ∧
      cutoff 1335 1335 < ((x.1 1).val : ℝ) ^ 2 ∧
      cutoff 1335 1335 < ((x.1 2).val : ℝ) ^ 2 ∧
      cutoff 1335 1333 < ((x.1 3).val : ℝ) ∧
      cutoff 1335 1333 < ((x.1 4).val : ℝ) ^ 2 ∧
      cutoff 1335 1333 < ((x.1 5).val : ℝ) ^ 2
    then ∏ i : Fin 6, Real.log ((x.1 i).val : ℝ) else 0
  have hmask : PairWitness 1335 1333 (fun i => (p i).val) (fun i => (ν i).val) ∧
      (∀ j, 4 ≤ (ν j).val ∧ ((ν j).val : ℝ) ≤ L 1335) ∧
      cutoff 1335 1335 < ((p 0).val : ℝ) ∧
      cutoff 1335 1335 < ((p 1).val : ℝ) ^ 2 ∧
      cutoff 1335 1335 < ((p 2).val : ℝ) ^ 2 ∧
      cutoff 1335 1333 < ((p 3).val : ℝ) ∧
      cutoff 1335 1333 < ((p 4).val : ℝ) ^ 2 ∧
      cutoff 1335 1333 < ((p 5).val : ℝ) ^ 2 := by
    refine ⟨hw, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j; exact ⟨by norm_num [ν], hL⟩
    all_goals norm_num [p]; first | linarith [hcut 1335 (by omega)] | linarith [hcut 1333 (by omega)]
  have hpos : 0 < w (p, ν) := by
    dsimp only [w]
    rw [if_pos hmask]
    exact prime_weight_pos _ hprime
  have hsum : w (p, ν) ≤ ∑ y : Tuple 1335, w y := by
    apply Finset.single_le_sum _ (Finset.mem_univ (p, ν))
    intro y _
    dsimp only [w]
    split_ifs with hy
    · exact (prime_weight_pos _ hy.1.1).le
    · exact le_rfl
  change w (p, ν) ≤ restrictedCount 1335 1333 at hsum
  exact hpos.trans_le hsum

/-- LEAF. Page 194, the R1 display in Lemma 2.2 at k equal to 82.
The major arc coefficient is kept separate from both minor arc estimates. -/
theorem major_arc_lower (C δ : ℝ) (hC : 1 < C) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      (556388 / 100000 * Real.pi ^ 2 / 16 - δ) * scale n₁ n₂ ≤ R1 n₁ n₂ := by
  sorry

/-- LEAF. Pages 194 to 196, the R2 display in Lemma 2.4 with k equal to 82.
The absolute real exceptional contribution has order N1 N2 L to power 81.
The three elementary limit steps are proved separately. -/
theorem exceptional_arc_order_bound (C : ℝ) (hC : 1 < C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      |R2 n₁ n₂| ≤ K * ((n₁ : ℝ) * n₂ * L n₁ ^ 81) := by
  sorry

/-- Pages 194 to 196, Lemma 2.4 at k equal to 82.
The exceptional contribution divided by N1 N2 L to power 82 tends to zero. -/
theorem exceptional_arc_small (C δ : ℝ) (hC : 1 < C) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      |R2 n₁ n₂| ≤ δ * scale n₁ n₂ := by
  obtain ⟨K, _, hbound⟩ := exceptional_arc_order_bound C hC
  exact exceptional_arc_small_of_order_bound C δ K hδ hbound

/-- LEAF. Pages 196 to 199, the R3 display in Lemma 2.5 at k equal to 82.
The constant 10823.8 and its unresolved rounding questions are inherited
from the sealed target. This is an open input, not a certified constant. -/
theorem remaining_arc_upper (C δ : ℝ) (hC : 1 < C) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      |R3 n₁ n₂| ≤ ((108238 / 10) * (PairLinnik.lam : ℝ) ^ (82 - 16) + δ) *
        scale n₁ n₂ := by
  sorry

/-- Page 199. The exact sealed leaf statement assembled from three analytic leaves.
CONDITIONAL ON the three separate analytic arc estimates. -/
theorem analytic_lower_bound (C ε : ℝ) (hC : 1 < C) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      (PairLinnik.margin101 (108238 / 10) 82 - ε) *
        ((n₁ : ℝ) * n₂ * logScale n₁ ^ 82) ≤ weightedCount n₁ n₂ := by
  obtain ⟨N₁, h₁⟩ := major_arc_lower C (ε / 3) hC (by positivity)
  obtain ⟨N₂, h₂⟩ := exceptional_arc_small C (ε / 3) hC (by positivity)
  obtain ⟨N₃, h₃⟩ := remaining_arc_upper C (ε / 3) hC (by positivity)
  refine ⟨max 16 (max N₁ (max N₂ N₃)), ?_⟩
  intro n₁ n₂ ho₁ ho₂ hn hlt hratio
  have h16 : 16 ≤ n₂ := (le_max_left _ _).trans hn
  have hN₁ : N₁ ≤ n₂ := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hn
  have hN₂ : N₂ ≤ n₂ :=
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hn
  have hN₃ : N₃ ≤ n₂ :=
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)).trans hn
  have hm := h₁ n₁ n₂ ho₁ ho₂ hN₁ hlt hratio
  have he := h₂ n₁ n₂ ho₁ ho₂ hN₂ hlt hratio
  have hr := h₃ n₁ n₂ ho₁ ho₂ hN₃ hlt hratio
  have hdecomp := restrictedCount_eq_arcs n₁ n₂ h16 hlt
  have hcount := restrictedCount_le n₁ n₂
  have helo := neg_abs_le (R2 n₁ n₂)
  have hrlo := neg_abs_le (R3 n₁ n₂)
  change (PairLinnik.margin101 (108238 / 10) 82 - ε) * scale n₁ n₂ ≤ _
  unfold PairLinnik.margin101
  nlinarith

end LeanLab.Hathi2021.Decomp319a
