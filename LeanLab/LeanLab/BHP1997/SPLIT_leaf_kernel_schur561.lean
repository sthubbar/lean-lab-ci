/-
Split of theorem leaf_kernel_schur561 in LeanLab.BHP1997.Decomp561e: the
periodic even-frequency kernel reduction of display 2.10. The finite
geometric kernel bound for one even progression is already available; what is
split here is the fibre-count comparison for the even frequency set, the
finite Fourier double integral rearrangement of the minor arc sum, the shift
read back of the weighted short energy, and the two integral Cauchy steps.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561e

set_option autoImplicit false

namespace LeanLab.BHP1997.Decomp561e
open Classical Complex Thm2 MeasureTheory Set Decomp561d

/-- The kernel majorant is nonnegative once its height is. -/
private lemma kernelWeight561_nonneg {H : ℝ} (hH : 0 ≤ H) (t : ℝ) :
    0 ≤ kernelWeight561 H t := by
  unfold kernelWeight561
  split_ifs with h
  · exact hH
  · exact le_min hH (by positivity)

/-- The even integers of a Nat interval are exactly twice a full interval of
halves: the fibre-count reindexing behind display 2.10. -/
private lemma image_two_mul_Icc (A B : ℕ) :
    (Finset.Icc ((A + 1) / 2) (B / 2)).image (fun k => 2 * k)
      = (Finset.Icc A B).filter Even := by
  ext N
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨by omega, by omega⟩, even_iff_exists_two_mul.mpr ⟨k, rfl⟩⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp h3
    exact ⟨k, ⟨by omega, by omega⟩, hk.symm⟩

/-- The fibre count: the even frequencies of the closed integer range from the
ceiling of x to the floor of x plus H are an even progression of at most H
terms, and its exact periodic Dirichlet kernel is at most the kernel majorant. -/
private lemma kernel_bound_even_Icc (A B : ℕ) (H : ℝ) (hH : 2 ≤ H)
    (hBA : (B : ℝ) - (A : ℝ) ≤ H) (u : ℝ) :
    ‖∑ N ∈ (Finset.Icc A B).filter Even,
        @fourier 1 (N : ℤ) (u : AddCircle (1 : ℝ))‖ ≤
      kernelWeight561 H u := by
  have hH0 : 0 ≤ H := by linarith
  have hinj : Set.InjOn (fun k : ℕ => 2 * k) ↑(Finset.Icc ((A + 1) / 2) (B / 2)) := by
    intro p _ q _ hpq
    have hpq' : 2 * p = 2 * q := hpq
    omega
  by_cases hAB : A ≤ B
  · set n : ℕ := B / 2 + 1 - (A + 1) / 2 with hn
    have hstep :
        (∑ N ∈ (Finset.Icc A B).filter Even,
            @fourier 1 (N : ℤ) (u : AddCircle (1 : ℝ)))
          = ∑ j ∈ Finset.range n,
              @fourier 1 ((2 * ((A + 1) / 2 + j) : ℕ) : ℤ) (u : AddCircle (1 : ℝ)) := by
      rw [← image_two_mul_Icc A B, Finset.sum_image hinj,
        ← Finset.Ico_add_one_right_eq_Icc,
        Finset.sum_Ico_eq_sum_range
          (f := fun k => @fourier 1 ((2 * k : ℕ) : ℤ) (u : AddCircle (1 : ℝ)))
          ((A + 1) / 2) (B / 2 + 1)]
    have hcast : ∀ j : ℕ,
        @fourier 1 ((2 * ((A + 1) / 2 + j) : ℕ) : ℤ) (u : AddCircle (1 : ℝ))
          = @fourier 1 (2 * ((((A + 1) / 2 : ℕ) : ℤ) + (j : ℤ))) (u : AddCircle (1 : ℝ)) := by
      intro j
      congr 1
    have hcastn : ((n : ℕ) : ℝ) = (((B / 2 : ℕ)) : ℝ) + 1 - (((A + 1) / 2 : ℕ) : ℝ) := by
      have h1 : (A + 1) / 2 ≤ B / 2 + 1 := by omega
      rw [hn, Nat.cast_sub h1, Nat.cast_add, Nat.cast_one]
    have hAn : ((A : ℝ)) / 2 ≤ (((A + 1) / 2 : ℕ) : ℝ) := by
      have h2 : A ≤ 2 * ((A + 1) / 2) := by omega
      have h3 : (A : ℝ) ≤ 2 * ((((A + 1) / 2 : ℕ)) : ℝ) := by exact_mod_cast h2
      linarith
    have hBn : (((B / 2 : ℕ)) : ℝ) ≤ (B : ℝ) / 2 := Nat.cast_div_le
    have hnH : ((n : ℕ) : ℝ) ≤ H := by
      rw [hcastn]
      linarith
    have hker := Decomp561c.even_frequency_kernel_bound561 ((A + 1) / 2) n u
    have hmain : ‖∑ j ∈ Finset.range n,
        @fourier 1 ((2 * ((A + 1) / 2 + j) : ℕ) : ℤ) (u : AddCircle (1 : ℝ))‖ ≤
        kernelWeight561 H u := by
      have hEq : (∑ j ∈ Finset.range n,
          @fourier 1 ((2 * ((A + 1) / 2 + j) : ℕ) : ℤ) (u : AddCircle (1 : ℝ)))
          = ∑ j ∈ Finset.range n,
              @fourier 1 (2 * ((((A + 1) / 2 : ℕ) : ℤ) + (j : ℤ))) (u : AddCircle (1 : ℝ)) :=
        Finset.sum_congr rfl (fun j _ => hcast j)
      rw [hEq]
      refine hker.trans ?_
      by_cases hd : ‖((2 * u : ℝ) : AddCircle (1 : ℝ))‖ = 0
      · rw [if_pos hd, kernelWeight561, if_pos hd]
        exact hnH
      · rw [if_neg hd, kernelWeight561, if_neg hd]
        exact min_le_min hnH le_rfl
    rw [hstep]
    exact hmain
  · have hemp : (Finset.Icc A B).filter Even = ∅ := by
      rw [Finset.Icc_eq_empty_iff.mpr (by omega)]
      simp
    rw [hemp]
    simp only [Finset.sum_empty, norm_zero]
    exact kernelWeight561_nonneg hH0 u

/-- The gap between the floor and the ceiling endpoints of the frequency range
is at most the fibre length P, both for positive and for negative x. -/
private lemma floor_ceil_gap (x P : ℝ) (hP : 0 ≤ P) :
    ((⌊x + P⌋₊ : ℕ) : ℝ) - ((⌈x⌉₊ : ℕ) : ℝ) ≤ P := by
  by_cases hx : 0 ≤ x
  · have h1 : ((⌊x + P⌋₊ : ℕ) : ℝ) ≤ x + P := Nat.floor_le (by linarith)
    have h2 : x ≤ ((⌈x⌉₊ : ℕ) : ℝ) := Nat.le_ceil x
    linarith
  · have hmono : ((⌊x + P⌋₊ : ℕ) : ℝ) ≤ ((⌊P⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast Nat.floor_le_floor (by linarith : x + P ≤ P)
    have h1 : ((⌊x + P⌋₊ : ℕ) : ℝ) ≤ P := hmono.trans (Nat.floor_le hP)
    have hz : ⌈x⌉₊ = 0 := by
      rw [Nat.ceil_eq_zero]
      linarith
    rw [hz]
    simp only [Nat.cast_zero]
    linarith

/-- LEAF. Fibre count and pointwise kernel bound. The even frequencies in the
closed integer range from the ceiling of x to the floor of x plus H form a
single even arithmetic progression of at most H terms, so the exact periodic
Dirichlet kernel of that finite progression is at most kernelWeight561 H, both
at resonance and away from it. This is a finite trigonometric inequality with
no energy, no minor arc and no constant K in it. -/
theorem leaf_even_frequency_kernel561 (ε x : ℝ)
    (hH : 2 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) :
    ∀ u : ℝ, ‖∑ N ∈ frequencies512 ε x,
        @fourier 1 (N : ℤ) (u : AddCircle (1 : ℝ))‖ ≤
      kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) u := by
  intro u
  exact kernel_bound_even_Icc ⌈x⌉₊
    ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊
    (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) hH
    (floor_ceil_gap x _ (by linarith)) u


/-- Nonnegative sectional Cauchy for real functions with integrable squares. -/
private lemma integral_mul_le_sqrt_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) :
    (∫ x, f x * g x ∂μ) ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff])
    hf0 hg0 (by simpa using hf) (by simpa using hg)
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using h

/-- The periodic kernel majorant is even in its second argument. -/
private lemma kernelWeight561_sub_comm (H t s : ℝ) :
    kernelWeight561 H (t - s) = kernelWeight561 H (s - t) := by
  unfold kernelWeight561
  have h : ((2 * (t - s) : ℝ) : AddCircle (1 : ℝ)) =
      -((2 * (s - t) : ℝ) : AddCircle (1 : ℝ)) := by
    rw [show 2 * (t - s) = -(2 * (s - t)) by ring, AddCircle.coe_neg]
  rw [h, norm_neg]

/-- The kernel majorant is bounded by its height. -/
private lemma kernelWeight561_le {H : ℝ} (hH : 0 ≤ H) (t : ℝ) :
    kernelWeight561 H t ≤ H := by
  unfold kernelWeight561
  split_ifs with h
  · exact le_rfl
  · exact min_le_left _ _

/-- The finite polynomial is continuous in the additive variable. -/
private lemma continuous_polynomial512 (S : Finset ℕ) (a : ℕ → ℂ) :
    Continuous fun t : ℝ => polynomial512 S a t := by
  unfold polynomial512
  exact continuous_finsetSum _ fun k _ =>
    ((fourier (k : ℤ)).continuous.comp (by fun_prop)).const_mul (a k)

/-- The periodic kernel majorant is measurable. -/
private lemma measurable_kernelWeight561 (H : ℝ) :
    Measurable fun u : ℝ => kernelWeight561 H u := by
  have hc : Measurable fun u : ℝ => ‖((2 * u : ℝ) : AddCircle (1 : ℝ))‖ := by
    fun_prop
  unfold kernelWeight561
  exact Measurable.ite (measurableSet_eq_fun hc measurable_const)
    measurable_const (measurable_const.min (measurable_const.div hc))

/-- LEAF. The finite Fourier double integral rearrangement. Expanding each
squared modulus of the minor arc sum and summing the characters over the even
frequency set turns the minor error into one double integral of the two
polynomial moduli against the pointwise kernel. Only the modulus of the
summed kernel is used, so this step is an integral rearrangement plus a
triangle inequality and it carries no constant and no weighted energy bound. -/
theorem leaf_minor_kernel_double_integral561 (ε D x : ℝ) (a b : ℕ → ℂ)
    (hH : 2 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))))
    (hkern : ∀ u : ℝ, ‖∑ N ∈ frequencies512 ε x,
        @fourier 1 (N : ℤ) (u : AddCircle (1 : ℝ))‖ ≤
      kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) u) :
    minorError512 ε D x a b ≤
      ∫ t in minor512 ε D x, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ * ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a s‖ * ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ * ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ *
          kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s) := by
  set H : ℝ := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) with hHdef
  have hH0 : 0 ≤ H := by linarith
  set m : Set ℝ := minor512 ε D x with hmdef
  set Sa : Finset ℕ := Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊ with hSadef
  set Sb : Finset ℕ := Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊ with hSbdef
  set F : ℝ → ℂ := fun t => polynomial512 Sa a t * polynomial512 Sb b t with hFdef
  set X : ℕ → ℝ → ℂ := fun N t => @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ)) with hXdef
  set G : ℕ → ℝ × ℝ → ℂ := fun N z => (F z.1 * X N z.1) * (starRingEnd ℂ) (F z.2 * X N z.2) with hGdef
  set Wf : ℝ × ℝ → ℝ := fun z => ‖polynomial512 Sa a z.1‖ * ‖polynomial512 Sa a z.2‖ *
      ‖polynomial512 Sb b z.1‖ * ‖polynomial512 Sb b z.2‖ * kernelWeight561 H (z.1 - z.2) with hWdef
  set μ : MeasureTheory.Measure (ℝ × ℝ) :=
    (volume.restrict m).prod (volume.restrict m) with hμdef
  set a₀ : ℝ := 1 / (order512 ε x : ℝ) with ha₀def
  set b₀ : ℝ := 1 + 1 / (order512 ε x : ℝ) with hb₀def
  have hmp : m ⊆ period512 ε x := fun s hs => hs.1
  have hsub : period512 ε x ⊆ Icc a₀ b₀ := by
    intro y hy
    exact ⟨le_of_lt hy.1, hy.2⟩
  have hmIcc : m ⊆ Icc a₀ b₀ := fun s hs => hsub (hmp hs)
  have hperfin : volume (period512 ε x) < ⊤ :=
    (measure_mono hsub).trans_lt isCompact_Icc.measure_lt_top
  have hmfin : volume m < ⊤ := (measure_mono hmp).trans_lt hperfin
  haveI hνfin : IsFiniteMeasure (volume.restrict m) := isFiniteMeasure_restrict.2 hmfin.ne
  haveI : IsFiniteMeasure μ := by
    rw [hμdef]
    infer_instance
  have hfun : ∀ (N : ℕ) (t : ℝ), integrand512 ε x a b N t = F t * X N t := by
    intro N t
    simp only [integrand512, hFdef, hXdef]
    ring
  -- continuity and integrability of the double integrand
  have hFc : Continuous F := (continuous_polynomial512 Sa a).mul (continuous_polynomial512 Sb b)
  have hXc : ∀ N : ℕ, Continuous (X N) := fun N =>
    (fourier (-(N : ℤ))).continuous.comp (by fun_prop)
  have hGc : ∀ N : ℕ, Continuous (G N) := by
    intro N
    have h1 : Continuous fun z : ℝ × ℝ => F z.1 * X N z.1 :=
      (hFc.mul (hXc N)).comp continuous_fst
    have h2 : Continuous fun z : ℝ × ℝ => (starRingEnd ℂ) (F z.2 * X N z.2) :=
      (continuous_conj).comp ((hFc.mul (hXc N)).comp continuous_snd)
    exact h1.mul h2
  have hGint : ∀ N : ℕ, Integrable (G N) μ := by
    intro N
    have hbox : IntegrableOn (G N) (Icc a₀ b₀ ×ˢ Icc a₀ b₀) :=
      (hGc N).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hmono : IntegrableOn (G N) (m ×ˢ m) :=
      hbox.mono_set (fun z hz => ⟨hmIcc hz.1, hmIcc hz.2⟩)
    rw [hμdef, MeasureTheory.Measure.prod_restrict]
    exact hmono
  -- the per-frequency identity
  have hstep : ∀ N ∈ frequencies512 ε x,
      ‖∫ t in m, F t * X N t‖ ^ 2 = (∫ z, G N z ∂μ).re := by
    intro N _
    have hconj : (starRingEnd ℂ) (∫ t in m, F t * X N t)
        = ∫ t in m, (starRingEnd ℂ) (F t * X N t) := (integral_conj).symm
    have hprod : (∫ t in m, F t * X N t) * (∫ t in m, (starRingEnd ℂ) (F t * X N t))
        = ∫ z, G N z ∂μ := by
      rw [← MeasureTheory.integral_prod_mul (μ := volume.restrict m) (ν := volume.restrict m)
        (f := fun t => F t * X N t) (g := fun t => (starRingEnd ℂ) (F t * X N t))]
    have hsq : ‖∫ t in m, F t * X N t‖ ^ 2
        = ((∫ t in m, F t * X N t) * (starRingEnd ℂ) (∫ t in m, F t * X N t)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
    rw [hsq, hconj, hprod]
  -- sum the identities
  have hId : ∫ z, ∑ N ∈ frequencies512 ε x, G N z ∂μ
      = ∑ N ∈ frequencies512 ε x, ∫ z, G N z ∂μ :=
    integral_finset_sum _ (fun N _ => hGint N)
  have hsum : (∑ N ∈ frequencies512 ε x, ‖∫ t in m, F t * X N t‖ ^ 2)
      = (∫ z, ∑ N ∈ frequencies512 ε x, G N z ∂μ).re := by
    calc (∑ N ∈ frequencies512 ε x, ‖∫ t in m, F t * X N t‖ ^ 2)
        = ∑ N ∈ frequencies512 ε x, (∫ z, G N z ∂μ).re := Finset.sum_congr rfl hstep
      _ = (∑ N ∈ frequencies512 ε x, ∫ z, G N z ∂μ).re :=
          (map_sum Complex.reCLM _ _).symm
      _ = (∫ z, ∑ N ∈ frequencies512 ε x, G N z ∂μ).re := by rw [hId]
  -- pointwise identification of the summed characters
  have hkey : ∀ (N : ℕ) (p q : ℝ), X N p * (starRingEnd ℂ) (X N q)
      = @fourier 1 (N : ℤ) ((q - p : ℝ) : AddCircle (1 : ℝ)) := by
    intro N p q
    have h1 : (starRingEnd ℂ) (X N q) = @fourier 1 (N : ℤ) ((q : ℝ) : AddCircle (1 : ℝ)) := by
      rw [hXdef]
      simp only
      rw [fourier_neg]
      simp
    rw [h1, hXdef]
    simp only
    rw [fourier_coe_apply (n := -(N : ℤ)) (x := p) (T := 1),
      fourier_coe_apply (n := (N : ℤ)) (x := q) (T := 1),
      fourier_coe_apply (n := (N : ℤ)) (x := q - p) (T := 1),
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hGs : ∀ z : ℝ × ℝ, ∑ N ∈ frequencies512 ε x, G N z
      = F z.1 * (starRingEnd ℂ) (F z.2) * (∑ N ∈ frequencies512 ε x, @fourier 1 (N : ℤ) (z.2 - z.1)) := by
    intro z
    have h1 : ∀ N : ℕ, G N z = F z.1 * (starRingEnd ℂ) (F z.2) * (X N z.1 * (starRingEnd ℂ) (X N z.2)) := by
      intro N
      rw [hGdef]
      simp only
      rw [map_mul]
      ring
    have h2 : ∀ N : ℕ, X N z.1 * (starRingEnd ℂ) (X N z.2) = @fourier 1 (N : ℤ) (z.2 - z.1) := by
      intro N
      have := hkey N z.1 z.2
      simpa using this
    calc ∑ N ∈ frequencies512 ε x, G N z
        = ∑ N ∈ frequencies512 ε x, F z.1 * (starRingEnd ℂ) (F z.2) * (X N z.1 * (starRingEnd ℂ) (X N z.2)) :=
          Finset.sum_congr rfl (fun N _ => h1 N)
      _ = F z.1 * (starRingEnd ℂ) (F z.2) * ∑ N ∈ frequencies512 ε x, (X N z.1 * (starRingEnd ℂ) (X N z.2)) := by
          rw [Finset.mul_sum]
      _ = F z.1 * (starRingEnd ℂ) (F z.2) * (∑ N ∈ frequencies512 ε x, @fourier 1 (N : ℤ) (z.2 - z.1)) := by
          rw [Finset.sum_congr rfl (fun N _ => h2 N)]
  -- the pointwise bound against the kernel majorant
  have hpt : ∀ z : ℝ × ℝ, ‖∑ N ∈ frequencies512 ε x, G N z‖ ≤ Wf z := by
    intro z
    have h1 : ‖∑ N ∈ frequencies512 ε x, G N z‖
        = ‖F z.1‖ * ‖F z.2‖ * ‖∑ N ∈ frequencies512 ε x, @fourier 1 (N : ℤ) (z.2 - z.1)‖ := by
      rw [hGs z, norm_mul, norm_mul, norm_conj]
    have h2 : ‖∑ N ∈ frequencies512 ε x, @fourier 1 (N : ℤ) (z.2 - z.1)‖
        ≤ kernelWeight561 H (z.1 - z.2) := by
      have h3 := hkern (z.2 - z.1)
      rwa [← kernelWeight561_sub_comm H z.1 z.2] at h3
    have h4 : ‖F z.1‖ = ‖polynomial512 Sa a z.1‖ * ‖polynomial512 Sb b z.1‖ := by
      rw [hFdef]; simp only; rw [norm_mul]
    have h5 : ‖F z.2‖ = ‖polynomial512 Sa a z.2‖ * ‖polynomial512 Sb b z.2‖ := by
      rw [hFdef]; simp only; rw [norm_mul]
    have h6 : ‖F z.1‖ * ‖F z.2‖ * kernelWeight561 H (z.1 - z.2) = Wf z := by
      rw [h4, h5, hWdef]
      ring
    calc ‖∑ N ∈ frequencies512 ε x, G N z‖
        = ‖F z.1‖ * ‖F z.2‖ * ‖∑ N ∈ frequencies512 ε x, @fourier 1 (N : ℤ) (z.2 - z.1)‖ := h1
      _ ≤ ‖F z.1‖ * ‖F z.2‖ * kernelWeight561 H (z.1 - z.2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Wf z := h6
  -- integrability of the majorant
  set Ca : ℝ := ∑ k ∈ Sa, ‖a k‖ with hCadef
  set Cb : ℝ := ∑ k ∈ Sb, ‖b k‖ with hCbdef
  have hpolyA : ∀ t : ℝ, ‖polynomial512 Sa a t‖ ≤ Ca := by
    intro t
    rw [polynomial512, hCadef]
    calc ‖∑ k ∈ Sa, a k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))‖
        ≤ ∑ k ∈ Sa, ‖a k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
      _ = ∑ k ∈ Sa, ‖a k‖ := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  have hpolyB : ∀ t : ℝ, ‖polynomial512 Sb b t‖ ≤ Cb := by
    intro t
    rw [polynomial512, hCbdef]
    calc ‖∑ k ∈ Sb, b k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))‖
        ≤ ∑ k ∈ Sb, ‖b k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
      _ = ∑ k ∈ Sb, ‖b k‖ := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  have hCa : 0 ≤ Ca := by rw [hCadef]; positivity
  have hCb : 0 ≤ Cb := by rw [hCbdef]; positivity
  have hWmeas : AEStronglyMeasurable Wf μ := by
    have hk : Measurable fun z : ℝ × ℝ => kernelWeight561 H (z.1 - z.2) :=
      (measurable_kernelWeight561 H).comp (measurable_fst.sub measurable_snd)
    have hA1 : Measurable fun z : ℝ × ℝ => ‖polynomial512 Sa a z.1‖ :=
      (continuous_polynomial512 Sa a).norm.measurable.comp measurable_fst
    have hA2 : Measurable fun z : ℝ × ℝ => ‖polynomial512 Sa a z.2‖ :=
      (continuous_polynomial512 Sa a).norm.measurable.comp measurable_snd
    have hB1 : Measurable fun z : ℝ × ℝ => ‖polynomial512 Sb b z.1‖ :=
      (continuous_polynomial512 Sb b).norm.measurable.comp measurable_fst
    have hB2 : Measurable fun z : ℝ × ℝ => ‖polynomial512 Sb b z.2‖ :=
      (continuous_polynomial512 Sb b).norm.measurable.comp measurable_snd
    have hm' : Measurable Wf := by
      rw [hWdef]
      exact ((((hA1.mul hA2).mul hB1).mul hB2).mul hk)
    exact hm'.aestronglyMeasurable
  have hWint : Integrable Wf μ := by
    have hbd : ∀ᵐ z ∂μ, ‖Wf z‖ ≤ Ca * Ca * Cb * Cb * H := by
      refine Filter.Eventually.of_forall fun z => ?_
      have h1 : Wf z = ‖polynomial512 Sa a z.1‖ * ‖polynomial512 Sa a z.2‖ *
          ‖polynomial512 Sb b z.1‖ * ‖polynomial512 Sb b z.2‖ * kernelWeight561 H (z.1 - z.2) := by
        rw [hWdef]
      have hk0 : 0 ≤ kernelWeight561 H (z.1 - z.2) := kernelWeight561_nonneg hH0 _
      have hkH : kernelWeight561 H (z.1 - z.2) ≤ H := kernelWeight561_le hH0 _
      have h1' : ‖polynomial512 Sa a z.1‖ ≤ Ca := hpolyA z.1
      have h2' : ‖polynomial512 Sa a z.2‖ ≤ Ca := hpolyA z.2
      have h3' : ‖polynomial512 Sb b z.1‖ ≤ Cb := hpolyB z.1
      have h4' : ‖polynomial512 Sb b z.2‖ ≤ Cb := hpolyB z.2
      have hn0 : (0:ℝ) ≤ ‖polynomial512 Sa a z.1‖ := norm_nonneg _
      have hn1 : (0:ℝ) ≤ ‖polynomial512 Sa a z.2‖ := norm_nonneg _
      have hn2 : (0:ℝ) ≤ ‖polynomial512 Sb b z.1‖ := norm_nonneg _
      have hn3 : (0:ℝ) ≤ ‖polynomial512 Sb b z.2‖ := norm_nonneg _
      have hnn : (0:ℝ) ≤ ‖polynomial512 Sa a z.1‖ * ‖polynomial512 Sa a z.2‖ *
          ‖polynomial512 Sb b z.1‖ * ‖polynomial512 Sb b z.2‖ := by positivity
      rw [h1, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hA' : ‖polynomial512 Sa a z.1‖ * ‖polynomial512 Sa a z.2‖ ≤ Ca * Ca :=
        mul_le_mul h1' h2' hn1 hCa
      have hB' : ‖polynomial512 Sb b z.1‖ * ‖polynomial512 Sb b z.2‖ ≤ Cb * Cb :=
        mul_le_mul h3' h4' hn3 hCb
      have hcc : (0:ℝ) ≤ Ca * Ca := by positivity
      have hcc2 : (0:ℝ) ≤ Cb * Cb := by positivity
      have hprod' : ‖polynomial512 Sa a z.1‖ * ‖polynomial512 Sa a z.2‖ *
          ‖polynomial512 Sb b z.1‖ * ‖polynomial512 Sb b z.2‖ ≤ Ca * Ca * Cb * Cb := by
        calc ‖polynomial512 Sa a z.1‖ * ‖polynomial512 Sa a z.2‖ *
              ‖polynomial512 Sb b z.1‖ * ‖polynomial512 Sb b z.2‖
            = (‖polynomial512 Sa a z.1‖ * ‖polynomial512 Sa a z.2‖) *
              (‖polynomial512 Sb b z.1‖ * ‖polynomial512 Sb b z.2‖) := by ring
          _ ≤ (Ca * Ca) * (Cb * Cb) := mul_le_mul hA' hB' (by positivity) hcc
          _ = Ca * Ca * Cb * Cb := by ring
      calc ‖polynomial512 Sa a z.1‖ * ‖polynomial512 Sa a z.2‖ *
            ‖polynomial512 Sb b z.1‖ * ‖polynomial512 Sb b z.2‖ * kernelWeight561 H (z.1 - z.2)
          ≤ (Ca * Ca * Cb * Cb) * H :=
            mul_le_mul hprod' hkH hk0 (by positivity)
        _ = Ca * Ca * Cb * Cb * H := by ring
    exact (integrable_const (Ca * Ca * Cb * Cb * H)).mono' hWmeas hbd
  -- assemble
  have hsumGc : Continuous fun z : ℝ × ℝ => ∑ N ∈ frequencies512 ε x, G N z :=
    continuous_finsetSum _ (fun N _ => hGc N)
  have hSGint : Integrable (fun z : ℝ × ℝ => ‖∑ N ∈ frequencies512 ε x, G N z‖) μ := by
    refine hWint.mono' hsumGc.norm.measurable.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hpt z
  have hfinal : (∫ z, ∑ N ∈ frequencies512 ε x, G N z ∂μ).re
      ≤ ∫ z, Wf z ∂μ := by
    refine (Complex.re_le_norm _).trans ?_
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono hSGint hWint (fun z => hpt z))
  have hFub : (∫ z, Wf z ∂μ) = ∫ t in m, ∫ s in m, Wf (t, s) :=
    integral_prod Wf hWint
  have hminor : minorError512 ε D x a b
      = ∑ N ∈ frequencies512 ε x, ‖∫ t in m, F t * X N t‖ ^ 2 := by
    simp only [minorError512, ← hmdef, hfun]
  calc minorError512 ε D x a b
      = ∑ N ∈ frequencies512 ε x, ‖∫ t in m, F t * X N t‖ ^ 2 := hminor
    _ = (∫ z, ∑ N ∈ frequencies512 ε x, G N z ∂μ).re := hsum
    _ ≤ ∫ z, Wf z ∂μ := hfinal
    _ = ∫ t in m, ∫ s in m, Wf (t, s) := hFub
    _ = ∫ t in m, ∫ s in m, ‖polynomial512 Sa a t‖ * ‖polynomial512 Sa a s‖ *
          ‖polynomial512 Sb b t‖ * ‖polynomial512 Sb b s‖ * kernelWeight561 H (t - s) := by
        simp only [hWdef]


/-- LEAF. The shifted short energy step, one Cauchy inequality. For every
shift t the short polynomial modulus squared against the kernel at t minus s
is controlled by the square root of the complete short energy times the square
root of the uniform weighted energy bound W. The kernel is even, so the shift
may be read on either side, and the two Cauchy factors are the modulus of the
short polynomial and that modulus times the kernel. -/
theorem leaf_shifted_short_energy561 (ε D x : ℝ) (b : ℕ → ℂ)
    (hH : 2 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (W : ℝ) (hW : 0 ≤ W)
    (hWE : ∀ ζ : ℝ, weightedEnergy561 ε D x b ζ ≤ W) :
    ∀ t : ℝ, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ ^ 2 * kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s) ≤
      Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W := by
  intro t
  set H : ℝ := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) with hHdef
  have hH0 : 0 ≤ H := by linarith
  set m : Set ℝ := minor512 ε D x with hmdef
  set sb : Finset ℕ := Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊ with hsbdef
  set f : ℝ → ℝ := fun s => ‖polynomial512 sb b s‖ with hfdef
  set g : ℝ → ℝ := fun s => ‖polynomial512 sb b s‖ * kernelWeight561 H (t - s) with hgdef
  have hfc : Continuous f := (continuous_polynomial512 sb b).norm
  have hf0 : ∀ s, 0 ≤ f s := fun s => norm_nonneg _
  have hg0 : ∀ s, 0 ≤ g s :=
    fun s => mul_nonneg (norm_nonneg _) (kernelWeight561_nonneg hH0 _)
  have hmp : m ⊆ period512 ε x := fun s hs => hs.1
  have hsub : period512 ε x ⊆ Icc (1 / (order512 ε x : ℝ)) (1 + 1 / (order512 ε x : ℝ)) := by
    intro y hy
    exact ⟨le_of_lt hy.1, hy.2⟩
  have hperfin : volume (period512 ε x) < ⊤ :=
    (measure_mono hsub).trans_lt isCompact_Icc.measure_lt_top
  haveI : IsFiniteMeasure (volume.restrict m) :=
    isFiniteMeasure_restrict.2 ((measure_mono hmp).trans_lt hperfin).ne
  have hperInt : IntegrableOn (fun s => f s ^ 2) (period512 ε x) := by
    have h1 : IntegrableOn (fun s => f s ^ 2) (Icc (1 / (order512 ε x : ℝ))
        (1 + 1 / (order512 ε x : ℝ))) := (hfc.pow 2).integrableOn_Icc
    exact h1.mono_set hsub
  have hfInt : IntegrableOn (fun s => f s ^ 2) m := hperInt.mono_set hmp
  have hfmem : MemLp f 2 (volume.restrict m) :=
    (memLp_two_iff_integrable_sq hfc.aestronglyMeasurable).2 hfInt
  have hkmeas : Measurable fun s : ℝ => kernelWeight561 H (t - s) :=
    (measurable_kernelWeight561 H).comp (measurable_const.sub measurable_id)
  have hgmeas : AEStronglyMeasurable g (volume.restrict m) := by
    have h1 : Measurable g := by
      have h2 : Measurable fun s : ℝ => ‖polynomial512 sb b s‖ := hfc.measurable
      have h3 : Measurable fun s : ℝ => ‖polynomial512 sb b s‖ * kernelWeight561 H (t - s) :=
        h2.mul hkmeas
      exact h3
    exact h1.aestronglyMeasurable
  have hgInt : Integrable (fun s => g s ^ 2) (volume.restrict m) := by
    have hbd : ∀ᵐ s ∂(volume.restrict m), ‖g s ^ 2‖ ≤ H ^ 2 * f s ^ 2 := by
      refine Filter.Eventually.of_forall fun s => ?_
      have h1 : g s ^ 2 = f s ^ 2 * kernelWeight561 H (t - s) ^ 2 := by
        rw [hgdef]
        simp only
        rw [mul_pow]
      have h3 : kernelWeight561 H (t - s) ^ 2 ≤ H ^ 2 := by
        have h4 := kernelWeight561_le hH0 (t - s)
        nlinarith [kernelWeight561_nonneg hH0 (t - s)]
      have h4 : (0 : ℝ) ≤ f s ^ 2 := sq_nonneg _
      rw [h1, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc f s ^ 2 * kernelWeight561 H (t - s) ^ 2 ≤ f s ^ 2 * H ^ 2 :=
            mul_le_mul_of_nonneg_left h3 h4
        _ = H ^ 2 * f s ^ 2 := by ring
    exact (hfInt.const_mul (H ^ 2)).mono' (hgmeas.pow 2) hbd
  have hgmem : MemLp g 2 (volume.restrict m) :=
    (memLp_two_iff_integrable_sq hgmeas).2 hgInt
  have hA : (∫ s in m, f s ^ 2) ≤ shortEnergy561 ε x b :=
    setIntegral_mono_set hperInt (Filter.Eventually.of_forall fun s => sq_nonneg (f s))
      (Filter.Eventually.of_forall fun s hs => hmp hs)
  have hB : (∫ s in m, g s ^ 2) ≤ W := by
    have hrew : (fun s => g s ^ 2) =
        fun s => f s ^ 2 * kernelWeight561 H (s - t) ^ 2 := by
      funext s
      have h1 : g s ^ 2 = f s ^ 2 * kernelWeight561 H (t - s) ^ 2 := by
        rw [hgdef]
        simp only
        rw [mul_pow]
      rw [h1, kernelWeight561_sub_comm H t s]
    rw [hrew]
    exact hWE t
  have hCS := integral_mul_le_sqrt_sq hfmem hgmem
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
  calc (∫ s in m, ‖polynomial512 sb b s‖ ^ 2 * kernelWeight561 H (t - s))
      = ∫ s in m, f s * g s := by
        simp only [hfdef, hgdef]
        congr 1 with s
        ring
    _ ≤ Real.sqrt (∫ s in m, f s ^ 2) * Real.sqrt (∫ s in m, g s ^ 2) := hCS
    _ ≤ Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W :=
        mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- LEAF. The second Cauchy step, the Schur comparison. Splitting the product of
the four moduli as long at t with short at s against short at t with long at s,
then swapping the two integration variables in one factor, leaves a single
double integral of the long modulus squared times the shifted short energy.
Feeding in the shifted short energy bound gives the target comparison with a
universal constant. The energy bound is an explicit hypothesis, so this leaf is
strictly weaker than the target. -/
theorem leaf_schur_kernel_comparison561 :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ε D x : ℝ, ∀ a b : ℕ → ℂ,
      2 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) →
      ∀ W : ℝ, 0 ≤ W →
      (∀ t : ℝ, ∫ s in minor512 ε D x,
          ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ ^ 2 * kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s) ≤
        Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W) →
      ∫ t in minor512 ε D x, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ * ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a s‖ * ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ * ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ *
          kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s) ≤
        K * longEnergy561 ε x a * Real.sqrt (shortEnergy561 ε x b) *
          Real.sqrt W := by
  refine ⟨1, le_refl 1, ?_⟩
  intro ε D x a b hH W hW hshort
  rw [one_mul]
  set H : ℝ := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) with hHdef
  have hH0 : 0 ≤ H := by linarith
  set m : Set ℝ := minor512 ε D x with hmdef
  set Sa : Finset ℕ := Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊ with hSadef
  set Sb : Finset ℕ := Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊ with hSbdef
  set A : ℝ → ℝ := fun t => ‖polynomial512 Sa a t‖ with hAdef
  set B : ℝ → ℝ := fun t => ‖polynomial512 Sb b t‖ with hBdef
  set ν : MeasureTheory.Measure ℝ := volume.restrict m with hνdef
  set μ : MeasureTheory.Measure (ℝ × ℝ) := ν.prod ν with hμdef
  set KW : ℝ × ℝ → ℝ := fun z => kernelWeight561 H (z.1 - z.2) with hKWdef
  set F₂ : ℝ × ℝ → ℝ := fun z => (A z.1 * B z.2) ^ 2 * KW z with hF2def
  set G₂ : ℝ × ℝ → ℝ := fun z => (A z.2 * B z.1) ^ 2 * KW z with hG2def
  set Ψ : ℝ × ℝ → ℝ := fun z => A z.1 * A z.2 * B z.1 * B z.2 * KW z with hΨdef
  set f : ℝ × ℝ → ℝ := fun z => A z.1 * B z.2 * Real.sqrt (KW z) with hfdef
  set g : ℝ × ℝ → ℝ := fun z => A z.2 * B z.1 * Real.sqrt (KW z) with hgdef
  set S : ℝ := Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  have hA0 : ∀ t : ℝ, 0 ≤ A t := fun t => norm_nonneg _
  have hB0 : ∀ t : ℝ, 0 ≤ B t := fun t => norm_nonneg _
  set a₀ : ℝ := 1 / (order512 ε x : ℝ) with ha₀def
  set b₀ : ℝ := 1 + 1 / (order512 ε x : ℝ) with hb₀def
  have hmp : m ⊆ period512 ε x := fun s hs => hs.1
  have hsub : period512 ε x ⊆ Icc a₀ b₀ := fun y hy => ⟨le_of_lt hy.1, hy.2⟩
  have hmIcc : m ⊆ Icc a₀ b₀ := fun s hs => hsub (hmp hs)
  have hperfin : volume (period512 ε x) < ⊤ :=
    (measure_mono hsub).trans_lt isCompact_Icc.measure_lt_top
  have hmfin : volume m < ⊤ := (measure_mono hmp).trans_lt hperfin
  haveI : IsFiniteMeasure ν := by
    rw [hνdef]
    exact isFiniteMeasure_restrict.2 hmfin.ne
  haveI : IsFiniteMeasure μ := by
    rw [hμdef]
    infer_instance
  have hAc : Continuous A := (continuous_polynomial512 Sa a).norm
  have hBc : Continuous B := (continuous_polynomial512 Sb b).norm
  set Ca : ℝ := ∑ k ∈ Sa, ‖a k‖ with hCadef
  set Cb : ℝ := ∑ k ∈ Sb, ‖b k‖ with hCbdef
  have hpolyA : ∀ t : ℝ, A t ≤ Ca := by
    intro t
    rw [show A t = ‖polynomial512 Sa a t‖ from by rw [hAdef]]
    rw [polynomial512, hCadef]
    calc ‖∑ k ∈ Sa, a k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))‖
        ≤ ∑ k ∈ Sa, ‖a k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
      _ = ∑ k ∈ Sa, ‖a k‖ := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  have hpolyB : ∀ t : ℝ, B t ≤ Cb := by
    intro t
    rw [show B t = ‖polynomial512 Sb b t‖ from by rw [hBdef]]
    rw [polynomial512, hCbdef]
    calc ‖∑ k ∈ Sb, b k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))‖
        ≤ ∑ k ∈ Sb, ‖b k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
      _ = ∑ k ∈ Sb, ‖b k‖ := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  have hCa : 0 ≤ Ca := by rw [hCadef]; positivity
  have hCb : 0 ≤ Cb := by rw [hCbdef]; positivity
  have hKWmeas : Measurable KW := by
    rw [hKWdef]
    exact (measurable_kernelWeight561 H).comp (measurable_fst.sub measurable_snd)
  have hAmeas1 : Measurable fun z : ℝ × ℝ => A z.1 := hAc.measurable.comp measurable_fst
  have hAmeas2 : Measurable fun z : ℝ × ℝ => A z.2 := hAc.measurable.comp measurable_snd
  have hBmeas1 : Measurable fun z : ℝ × ℝ => B z.1 := hBc.measurable.comp measurable_fst
  have hBmeas2 : Measurable fun z : ℝ × ℝ => B z.2 := hBc.measurable.comp measurable_snd
  have hKW0 : ∀ z : ℝ × ℝ, 0 ≤ KW z := fun z => kernelWeight561_nonneg hH0 _
  have hKWH : ∀ z : ℝ × ℝ, KW z ≤ H := fun z => kernelWeight561_le hH0 _
  have hF2meas : AEStronglyMeasurable F₂ μ := by
    have h : Measurable F₂ := by
      rw [hF2def]
      exact ((((hAmeas1.mul hBmeas2).pow_const 2).mul hKWmeas))
    exact h.aestronglyMeasurable
  have hG2meas : AEStronglyMeasurable G₂ μ := by
    have h : Measurable G₂ := by
      rw [hG2def]
      exact ((((hAmeas2.mul hBmeas1).pow_const 2).mul hKWmeas))
    exact h.aestronglyMeasurable
  have hfmeas : AEStronglyMeasurable f μ := by
    have h : Measurable f := by
      rw [hfdef]
      exact (((hAmeas1.mul hBmeas2).mul hKWmeas.sqrt))
    exact h.aestronglyMeasurable
  have hgmeas : AEStronglyMeasurable g μ := by
    have h : Measurable g := by
      rw [hgdef]
      exact (((hAmeas2.mul hBmeas1).mul hKWmeas.sqrt))
    exact h.aestronglyMeasurable
  have hΨmeas : AEStronglyMeasurable Ψ μ := by
    have h : Measurable Ψ := by
      rw [hΨdef]
      exact ((((hAmeas1.mul hAmeas2).mul hBmeas1).mul hBmeas2).mul hKWmeas)
    exact h.aestronglyMeasurable
  have hF2int : Integrable F₂ μ := by
    have hbd : ∀ᵐ z ∂μ, ‖F₂ z‖ ≤ (Ca * Cb) ^ 2 * H := by
      refine Filter.Eventually.of_forall fun z => ?_
      have h1 : F₂ z = (A z.1 * B z.2) ^ 2 * KW z := by rw [hF2def]
      have hAB : A z.1 * B z.2 ≤ Ca * Cb :=
        mul_le_mul (hpolyA z.1) (hpolyB z.2) (hB0 z.2) hCa
      have hAB0 : (0:ℝ) ≤ A z.1 * B z.2 := mul_nonneg (hA0 _) (hB0 _)
      have hsq : (A z.1 * B z.2) ^ 2 ≤ (Ca * Cb) ^ 2 := by nlinarith [hAB, hAB0, hCa, hCb]
      rw [h1, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hKW0 z))]
      exact mul_le_mul hsq (hKWH z) (hKW0 z) (sq_nonneg _)
    exact (integrable_const ((Ca * Cb) ^ 2 * H)).mono' hF2meas hbd
  have hG2int : Integrable G₂ μ := by
    have hbd : ∀ᵐ z ∂μ, ‖G₂ z‖ ≤ (Ca * Cb) ^ 2 * H := by
      refine Filter.Eventually.of_forall fun z => ?_
      have h1 : G₂ z = (A z.2 * B z.1) ^ 2 * KW z := by rw [hG2def]
      have hAB : A z.2 * B z.1 ≤ Ca * Cb :=
        mul_le_mul (hpolyA z.2) (hpolyB z.1) (hB0 z.1) hCa
      have hAB0 : (0:ℝ) ≤ A z.2 * B z.1 := mul_nonneg (hA0 _) (hB0 _)
      have hsq : (A z.2 * B z.1) ^ 2 ≤ (Ca * Cb) ^ 2 := by nlinarith [hAB, hAB0, hCa, hCb]
      rw [h1, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hKW0 z))]
      exact mul_le_mul hsq (hKWH z) (hKW0 z) (sq_nonneg _)
    exact (integrable_const ((Ca * Cb) ^ 2 * H)).mono' hG2meas hbd
  have hΨint : Integrable Ψ μ := by
    have hbd : ∀ᵐ z ∂μ, ‖Ψ z‖ ≤ Ca * Ca * Cb * Cb * H := by
      refine Filter.Eventually.of_forall fun z => ?_
      have h1 : Ψ z = A z.1 * A z.2 * B z.1 * B z.2 * KW z := by rw [hΨdef]
      have hAA : A z.1 * A z.2 ≤ Ca * Ca :=
        mul_le_mul (hpolyA z.1) (hpolyA z.2) (hA0 z.2) hCa
      have hBB : B z.1 * B z.2 ≤ Cb * Cb :=
        mul_le_mul (hpolyB z.1) (hpolyB z.2) (hB0 z.2) hCb
      have hcc : (0:ℝ) ≤ Ca * Ca := by positivity
      have hprod : A z.1 * A z.2 * B z.1 * B z.2 ≤ Ca * Ca * Cb * Cb := by
        calc A z.1 * A z.2 * B z.1 * B z.2 = (A z.1 * A z.2) * (B z.1 * B z.2) := by ring
          _ ≤ (Ca * Ca) * (Cb * Cb) := mul_le_mul hAA hBB (by positivity) hcc
          _ = Ca * Ca * Cb * Cb := by ring
      rw [h1, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hA0 _) (hA0 _)) (hB0 _)) (hB0 _)) (hKW0 z))]
      exact mul_le_mul hprod (hKWH z) (hKW0 z) (by positivity)
    exact (integrable_const (Ca * Ca * Cb * Cb * H)).mono' hΨmeas hbd
  have hshort' : ∀ t : ℝ, (∫ s, B s ^ 2 * kernelWeight561 H (t - s) ∂ν) ≤ S := by
    intro t
    have h := hshort t
    rw [hSdef]
    rwa [show (∫ s, B s ^ 2 * kernelWeight561 H (t - s) ∂ν)
        = ∫ s in minor512 ε D x,
            ‖polynomial512 Sb b s‖ ^ 2 * kernelWeight561 H (t - s) from by
      rw [hBdef, hνdef, ← hmdef]] at h
  have hfacA : ∀ t : ℝ, (∫ s, (A t * B s) ^ 2 * KW (t, s) ∂ν)
      = A t ^ 2 * (∫ s, B s ^ 2 * kernelWeight561 H (t - s) ∂ν) := by
    intro t
    rw [show (fun s : ℝ => (A t * B s) ^ 2 * KW (t, s))
        = fun s : ℝ => A t ^ 2 * (B s ^ 2 * kernelWeight561 H (t - s)) from by
      funext s
      rw [hKWdef]
      simp only
      ring]
    rw [integral_const_mul]
  have hfacB : ∀ s : ℝ, (∫ t, (A s * B t) ^ 2 * KW (t, s) ∂ν)
      = A s ^ 2 * (∫ t, B t ^ 2 * kernelWeight561 H (t - s) ∂ν) := by
    intro s
    rw [show (fun t : ℝ => (A s * B t) ^ 2 * KW (t, s))
        = fun t : ℝ => A s ^ 2 * (B t ^ 2 * kernelWeight561 H (t - s)) from by
      funext t
      rw [hKWdef]
      simp only
      ring]
    rw [integral_const_mul]
  have hsecA : Integrable (fun t => A t ^ 2 * (∫ s, B s ^ 2 * kernelWeight561 H (t - s) ∂ν)) ν := by
    have h0 : Integrable (fun t => ∫ s, (A t * B s) ^ 2 * KW (t, s) ∂ν) ν :=
      hF2int.integral_prod_left
    exact h0.congr (Filter.Eventually.of_forall fun t => hfacA t)
  have hsecB : Integrable (fun s => A s ^ 2 * (∫ t, B t ^ 2 * kernelWeight561 H (t - s) ∂ν)) ν := by
    have h0 : Integrable (fun s => ∫ t, (A s * B t) ^ 2 * KW (t, s) ∂ν) ν :=
      hG2int.integral_prod_right
    exact h0.congr (Filter.Eventually.of_forall fun s => hfacB s)
  have hSI : Integrable (fun t => A t ^ 2 * S) ν := by
    rw [hνdef]
    have h1 : IntegrableOn (fun t => A t ^ 2 * S) (Icc a₀ b₀) :=
      ((hAc.pow 2).mul (continuous_const : Continuous fun _ : ℝ => S)).integrableOn_Icc
    exact h1.mono_set hmIcc
  have hAperInt : IntegrableOn (fun t => A t ^ 2) (period512 ε x) := by
    have h1 : IntegrableOn (fun t => A t ^ 2) (Icc a₀ b₀) := (hAc.pow 2).integrableOn_Icc
    exact h1.mono_set hsub
  have hAle : (∫ t, A t ^ 2 ∂ν) ≤ longEnergy561 ε x a := by
    rw [hνdef]
    exact setIntegral_mono_set hAperInt
      (Filter.Eventually.of_forall fun t => sq_nonneg (A t))
      (Filter.Eventually.of_forall fun t ht => hmp ht)
  have hcapA : (∫ z, F₂ z ∂μ) ≤ longEnergy561 ε x a * S := by
    have h1 : (∫ z, F₂ z ∂μ) = ∫ t, ∫ s, (A t * B s) ^ 2 * KW (t, s) ∂ν ∂ν := by
      rw [hF2def]
      exact integral_prod (μ := ν) (ν := ν)
        (fun z : ℝ × ℝ => (A z.1 * B z.2) ^ 2 * KW z) hF2int
    have h2 : (∫ t, ∫ s, (A t * B s) ^ 2 * KW (t, s) ∂ν ∂ν)
        = ∫ t, A t ^ 2 * (∫ s, B s ^ 2 * kernelWeight561 H (t - s) ∂ν) ∂ν := by
      simp only [hfacA]
    have h3 : (∫ t, A t ^ 2 * (∫ s, B s ^ 2 * kernelWeight561 H (t - s) ∂ν) ∂ν)
        ≤ ∫ t, A t ^ 2 * S ∂ν :=
      integral_mono hsecA hSI (fun t =>
        mul_le_mul_of_nonneg_left (hshort' t) (sq_nonneg (A t)))
    have h4 : (∫ t, A t ^ 2 * S ∂ν) = (∫ t, A t ^ 2 ∂ν) * S := by
      rw [integral_mul_const]
    calc (∫ z, F₂ z ∂μ) = ∫ t, ∫ s, (A t * B s) ^ 2 * KW (t, s) ∂ν ∂ν := h1
      _ = ∫ t, A t ^ 2 * (∫ s, B s ^ 2 * kernelWeight561 H (t - s) ∂ν) ∂ν := h2
      _ ≤ ∫ t, A t ^ 2 * S ∂ν := h3
      _ = (∫ t, A t ^ 2 ∂ν) * S := h4
      _ ≤ longEnergy561 ε x a * S := mul_le_mul_of_nonneg_right hAle hS0
  have hcapB : (∫ z, G₂ z ∂μ) ≤ longEnergy561 ε x a * S := by
    have h1 : (∫ z, G₂ z ∂μ) = ∫ s, ∫ t, (A s * B t) ^ 2 * KW (t, s) ∂ν ∂ν := by
      rw [hG2def]
      exact integral_prod_symm (μ := ν) (ν := ν)
        (fun z : ℝ × ℝ => (A z.2 * B z.1) ^ 2 * KW z) hG2int
    have h2 : (∫ s, ∫ t, (A s * B t) ^ 2 * KW (t, s) ∂ν ∂ν)
        = ∫ s, A s ^ 2 * (∫ t, B t ^ 2 * kernelWeight561 H (t - s) ∂ν) ∂ν := by
      simp only [hfacB]
    have hswap : ∀ s : ℝ, (∫ t, B t ^ 2 * kernelWeight561 H (t - s) ∂ν)
        = ∫ t, B t ^ 2 * kernelWeight561 H (s - t) ∂ν := by
      intro s
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [kernelWeight561_sub_comm H t s]
    have h3 : (∫ s, A s ^ 2 * (∫ t, B t ^ 2 * kernelWeight561 H (t - s) ∂ν) ∂ν)
        ≤ ∫ s, A s ^ 2 * S ∂ν := by
      refine integral_mono hsecB hSI (fun s => ?_)
      rw [hswap s]
      exact mul_le_mul_of_nonneg_left (hshort' s) (sq_nonneg (A s))
    have h4 : (∫ s, A s ^ 2 * S ∂ν) = (∫ s, A s ^ 2 ∂ν) * S := by
      rw [integral_mul_const]
    calc (∫ z, G₂ z ∂μ) = ∫ s, ∫ t, (A s * B t) ^ 2 * KW (t, s) ∂ν ∂ν := h1
      _ = ∫ s, A s ^ 2 * (∫ t, B t ^ 2 * kernelWeight561 H (t - s) ∂ν) ∂ν := h2
      _ ≤ ∫ s, A s ^ 2 * S ∂ν := h3
      _ = (∫ s, A s ^ 2 ∂ν) * S := h4
      _ ≤ longEnergy561 ε x a * S := mul_le_mul_of_nonneg_right hAle hS0
  have hf2eq : (fun z : ℝ × ℝ => f z ^ 2) = F₂ := by
    funext z
    rw [hfdef, hF2def]
    simp only
    rw [mul_pow, Real.sq_sqrt (hKW0 z)]
  have hg2eq : (fun z : ℝ × ℝ => g z ^ 2) = G₂ := by
    funext z
    rw [hgdef, hG2def]
    simp only
    rw [mul_pow, Real.sq_sqrt (hKW0 z)]
  have hfmem : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfmeas).mpr (hf2eq ▸ hF2int)
  have hgmem : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgmeas).mpr (hg2eq ▸ hG2int)
  have hfg : (fun z : ℝ × ℝ => f z * g z) = Ψ := by
    funext z
    rw [hfdef, hgdef, hΨdef]
    simp only
    have hsq : Real.sqrt (KW z) * Real.sqrt (KW z) = KW z := Real.mul_self_sqrt (hKW0 z)
    calc A z.1 * B z.2 * Real.sqrt (KW z) * (A z.2 * B z.1 * Real.sqrt (KW z))
        = A z.1 * A z.2 * B z.1 * B z.2 * (Real.sqrt (KW z) * Real.sqrt (KW z)) := by ring
      _ = A z.1 * A z.2 * B z.1 * B z.2 * KW z := by rw [hsq]
  have hfnn : ∀ᵐ z ∂μ, 0 ≤ f z := Filter.Eventually.of_forall fun z => by
    simp only [hfdef]
    exact mul_nonneg (mul_nonneg (hA0 z.1) (hB0 z.2)) (Real.sqrt_nonneg _)
  have hgnn : ∀ᵐ z ∂μ, 0 ≤ g z := Filter.Eventually.of_forall fun z => by
    simp only [hgdef]
    exact mul_nonneg (mul_nonneg (hA0 z.2) (hB0 z.1)) (Real.sqrt_nonneg _)
  have hcs : (∫ z, Ψ z ∂μ) ≤
      Real.sqrt (∫ z, F₂ z ∂μ) * Real.sqrt (∫ z, G₂ z ∂μ) := by
    rw [← hfg, ← hf2eq, ← hg2eq]
    exact integral_mul_le_sqrt_sq hfmem hgmem hfnn hgnn
  rw [← integral_prod (μ := ν) (ν := ν) Ψ hΨint]
  refine hcs.trans ?_
  have h1 : Real.sqrt (∫ z, F₂ z ∂μ) ≤ Real.sqrt (longEnergy561 ε x a * S) :=
    Real.sqrt_le_sqrt hcapA
  have h2 : Real.sqrt (∫ z, G₂ z ∂μ) ≤ Real.sqrt (longEnergy561 ε x a * S) :=
    Real.sqrt_le_sqrt hcapB
  have hLE0 : 0 ≤ longEnergy561 ε x a :=
    (integral_nonneg fun t => sq_nonneg (A t)).trans hAle
  calc Real.sqrt (∫ z, F₂ z ∂μ) * Real.sqrt (∫ z, G₂ z ∂μ)
      ≤ Real.sqrt (longEnergy561 ε x a * S) * Real.sqrt (longEnergy561 ε x a * S) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = longEnergy561 ε x a * S := Real.mul_self_sqrt (by positivity)
    _ = longEnergy561 ε x a * Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W := by
        rw [hSdef]; ring


/-- Display 2.10, the exact expanded kernel reduction. CONDITIONAL ON the fibre
count, double integral rearrangement, shifted short energy and Schur comparison
leaves. No direct admission occurs in this assembly. -/
theorem leaf_kernel_schur561_split :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ε D x : ℝ, ∀ a b : ℕ → ℂ,
      2 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) →
      ∀ W : ℝ, 0 ≤ W → (∀ ζ : ℝ, weightedEnergy561 ε D x b ζ ≤ W) →
        minorError512 ε D x a b ≤
          K * longEnergy561 ε x a * Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W := by
  obtain ⟨K, hK, hQ⟩ := leaf_schur_kernel_comparison561
  refine ⟨K, hK, ?_⟩
  intro ε D x a b hH W hW hWE
  exact (leaf_minor_kernel_double_integral561 ε D x a b hH
          (leaf_even_frequency_kernel561 ε x hH)).trans
    (hQ ε D x a b hH W hW (leaf_shifted_short_energy561 ε D x b hH W hW hWE))

end LeanLab.BHP1997.Decomp561e
