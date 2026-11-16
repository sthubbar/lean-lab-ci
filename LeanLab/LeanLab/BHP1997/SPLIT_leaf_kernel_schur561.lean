/-
Split of theorem leaf_kernel_schur561 in LeanLab.BHP1997.Decomp561e: the
periodic even-frequency kernel reduction of display 2.10. The finite
geometric kernel bound for one even progression is already available; what is
split here is the fibre-count comparison for the even frequency set, the
finite Fourier double integral rearrangement of the minor arc sum, the shift
read back of the weighted short energy, and the two integral Cauchy steps.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.KernelData635

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
  let H : ℝ := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))
  have hH0 : 0 ≤ H := by dsimp [H]; linarith
  let m : Set ℝ := minor512 ε D x
  let μ : Measure ℝ := volume.restrict m
  let sa := Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊
  let sb := Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊
  let A : ℝ → ℝ := fun t => ‖polynomial512 sa a t‖
  let B : ℝ → ℝ := fun t => ‖polynomial512 sb b t‖
  let f : ℝ → ℂ := fun t => polynomial512 sa a t * polynomial512 sb b t
  let K := frequencies512 ε x
  let G : ℕ → ℝ → ℂ := fun N t => f t * @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))
  let J : ℕ → ℂ := fun N => ∫ t, G N t ∂μ
  have hAc : Continuous A := (continuous_polynomial512 sa a).norm
  have hBc : Continuous B := (continuous_polynomial512 sb b).norm
  have hA0 (t : ℝ) : 0 ≤ A t := norm_nonneg _
  have hB0 (t : ℝ) : 0 ≤ B t := norm_nonneg _
  have hmp : m ⊆ period512 ε x := fun t ht => ht.1
  have hpc : period512 ε x ⊆
      Icc (1 / (order512 ε x : ℝ)) (1 + 1 / (order512 ε x : ℝ)) :=
    fun t ht => ⟨ht.1.le, ht.2⟩
  have hpfin : volume (period512 ε x) < ⊤ :=
    (measure_mono hpc).trans_lt isCompact_Icc.measure_lt_top
  haveI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.2 ((measure_mono hmp).trans_lt hpfin).ne
  have hbound (s : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
      ‖polynomial512 s c t‖ ≤ ∑ n ∈ s, ‖c n‖ := by
    unfold polynomial512
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  let aa : ℝ := ∑ n ∈ sa, ‖a n‖
  let bb : ℝ := ∑ n ∈ sb, ‖b n‖
  have haa0 : 0 ≤ aa := Finset.sum_nonneg fun n hn => norm_nonneg _
  have hbb0 : 0 ≤ bb := Finset.sum_nonneg fun n hn => norm_nonneg _
  have hGc (N : ℕ) : Continuous (G N) :=
    ((continuous_polynomial512 sa a).mul (continuous_polynomial512 sb b)).mul
      ((map_continuous (fourier _)).comp (AddCircle.continuous_mk' 1))
  have hGb (N : ℕ) (t : ℝ) : ‖G N t‖ ≤ aa * bb := by
    dsimp only [G, f]
    rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one, norm_mul]
    exact mul_le_mul (hbound sa a t) (hbound sb b t) (norm_nonneg _) haa0
  have hGi (N : ℕ) : Integrable (G N) μ :=
    Integrable.of_bound (hGc N).aestronglyMeasurable (aa * bb)
      (Filter.Eventually.of_forall (hGb N))
  have hGci (N : ℕ) : Integrable (fun s => (starRingEnd ℂ) (G N s)) μ := by
    have hc : Continuous (fun s => (starRingEnd ℂ) (G N s)) := by fun_prop
    apply Integrable.of_bound hc.aestronglyMeasurable (aa * bb)
    exact Filter.Eventually.of_forall fun s => by simpa only [norm_conj] using hGb N s
  have hchar (N : ℕ) (t s : ℝ) :
      @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ)) *
        (starRingEnd ℂ) (@fourier 1 (-(N : ℤ)) (s : AddCircle (1 : ℝ))) =
      @fourier 1 (N : ℤ) ((s - t : ℝ) : AddCircle (1 : ℝ)) := by
    simp only [fourier_coe_apply, div_one, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    push_cast
    simp only [map_div₀, map_neg, map_mul, map_natCast, map_intCast, map_ofNat,
      map_one, div_one, conj_I, conj_ofReal]
    ring
  have hmatrix (t s : ℝ) :
      (∑ N ∈ K, G N t * (starRingEnd ℂ) (G N s)) =
        (f t * (starRingEnd ℂ) (f s)) * ∑ N ∈ K,
          @fourier 1 (N : ℤ) ((s - t : ℝ) : AddCircle (1 : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro N hN
    dsimp only [G]
    rw [map_mul]
    calc (f t * @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) *
        ((starRingEnd ℂ) (f s) * (starRingEnd ℂ) (@fourier 1 (-(N : ℤ)) (s : AddCircle (1 : ℝ)))) =
        (f t * (starRingEnd ℂ) (f s)) * (@fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ)) *
          (starRingEnd ℂ) (@fourier 1 (-(N : ℤ)) (s : AddCircle (1 : ℝ)))) := by ring
      _ = _ := by rw [hchar]
  have hsingle (N : ℕ) :
      (∫ t, ∫ s, G N t * (starRingEnd ℂ) (G N s) ∂μ ∂μ) = ((‖J N‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [integral_const_mul, integral_conj, integral_mul_const]
    change J N * (starRingEnd ℂ) (J N) = _
    rw [RCLike.mul_conj]
    exact (map_pow (algebraMap ℝ ℂ) ‖J N‖ 2).symm
  have hinner (t : ℝ) :
      (∫ s, ∑ N ∈ K, G N t * (starRingEnd ℂ) (G N s) ∂μ) =
        ∑ N ∈ K, ∫ s, G N t * (starRingEnd ℂ) (G N s) ∂μ :=
    integral_finsetSum K (fun N hN => (hGci N).const_mul (G N t))
  have hdouble :
      (∫ t, ∫ s, ∑ N ∈ K, G N t * (starRingEnd ℂ) (G N s) ∂μ ∂μ) =
        ∑ N ∈ K, ((‖J N‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hinner]
    rw [integral_finsetSum K]
    · exact Finset.sum_congr rfl fun N hN => hsingle N
    · intro N hN
      simp_rw [integral_const_mul, integral_conj]
      exact (hGi N).mul_const ((starRingEnd ℂ) (J N))
  have hcx : ((minorError512 ε D x a b : ℝ) : ℂ) =
      ∫ t, ∫ s, ∑ N ∈ K, G N t * (starRingEnd ℂ) (G N s) ∂μ ∂μ := by
    rw [hdouble]
    change ((∑ N ∈ K, ‖J N‖ ^ 2 : ℝ) : ℂ) = ∑ N ∈ K, ((‖J N‖ ^ 2 : ℝ) : ℂ)
    push_cast
    rfl
  let R : ℝ → ℝ → ℝ := fun t s => A t * A s * B t * B s * kernelWeight561 H (t - s)
  have hR0 (t s : ℝ) : 0 ≤ R t s := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hA0 _) (hA0 _))
      (hB0 _)) (hB0 _)) (kernelWeight561_nonneg hH0 _)
  have hRm : Measurable (Function.uncurry R) := by
    exact ((((hAc.measurable.comp measurable_fst).mul (hAc.measurable.comp measurable_snd)).mul
      (hBc.measurable.comp measurable_fst)).mul (hBc.measurable.comp measurable_snd)).mul
      ((measurable_kernelWeight561 H).comp (measurable_fst.sub measurable_snd))
  have hRi : Integrable (Function.uncurry R) (μ.prod μ) := by
    apply Integrable.of_bound hRm.aestronglyMeasurable (aa * aa * bb * bb * H)
    filter_upwards [] with p
    change ‖R p.1 p.2‖ ≤ aa * aa * bb * bb * H
    rw [Real.norm_eq_abs, abs_of_nonneg (hR0 p.1 p.2)]
    exact mul_le_mul
      (mul_le_mul (mul_le_mul
        (mul_le_mul (hbound sa a p.1) (hbound sa a p.2) (hA0 _) haa0)
        (hbound sb b p.1) (hB0 _) (mul_nonneg haa0 haa0))
        (hbound sb b p.2) (hB0 _) (mul_nonneg (mul_nonneg haa0 haa0) hbb0))
      (kernelWeight561_le hH0 _) (kernelWeight561_nonneg hH0 _)
      (mul_nonneg (mul_nonneg (mul_nonneg haa0 haa0) hbb0) hbb0)
  have hpoint (t s : ℝ) : ‖∑ N ∈ K, G N t * (starRingEnd ℂ) (G N s)‖ ≤ R t s := by
    rw [hmatrix, norm_mul, norm_mul, norm_conj]
    have h := mul_le_mul_of_nonneg_left (hkern (s - t))
      (mul_nonneg (norm_nonneg (f t)) (norm_nonneg (f s)))
    rw [kernelWeight561_sub_comm H s t] at h
    dsimp only [R, A, B, f] at h ⊢
    simp only [norm_mul] at h ⊢
    convert h using 1 <;> ring
  have hm0 : 0 ≤ minorError512 ε D x a b := Finset.sum_nonneg fun N hN => sq_nonneg _
  have heq : minorError512 ε D x a b =
      ‖∫ t, ∫ s, ∑ N ∈ K, G N t * (starRingEnd ℂ) (G N s) ∂μ ∂μ‖ := by
    rw [← hcx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm0]
  change minorError512 ε D x a b ≤ ∫ t, ∫ s, R t s ∂μ ∂μ
  rw [heq]
  calc
    ‖∫ t, ∫ s, ∑ N ∈ K, G N t * (starRingEnd ℂ) (G N s) ∂μ ∂μ‖ ≤
        ∫ t, ‖∫ s, ∑ N ∈ K, G N t * (starRingEnd ℂ) (G N s) ∂μ‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t, ∫ s, R t s ∂μ ∂μ := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun t => norm_nonneg _) hRi.integral_prod_left
      filter_upwards [hRi.prod_right_ae] with t ht
      calc
        ‖∫ s, ∑ N ∈ K, G N t * (starRingEnd ℂ) (G N s) ∂μ‖ ≤
            ∫ s, ‖∑ N ∈ K, G N t * (starRingEnd ℂ) (G N s)‖ ∂μ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ s, R t s ∂μ := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun s => norm_nonneg _) ht
          (Filter.Eventually.of_forall (hpoint t))



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
  refine ⟨1, le_rfl, ?_⟩
  intro ε D x a b hH W hW hsec
  let H : ℝ := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))
  have hH0 : 0 ≤ H := by dsimp [H]; linarith
  let m : Set ℝ := minor512 ε D x
  let μ : Measure ℝ := volume.restrict m
  let sa := Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊
  let sb := Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊
  let A : ℝ → ℝ := fun t => ‖polynomial512 sa a t‖
  let B : ℝ → ℝ := fun t => ‖polynomial512 sb b t‖
  let C : ℝ := Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hAc : Continuous A := (continuous_polynomial512 sa a).norm
  have hBc : Continuous B := (continuous_polynomial512 sb b).norm
  have hA0 (t : ℝ) : 0 ≤ A t := norm_nonneg _
  have hB0 (t : ℝ) : 0 ≤ B t := norm_nonneg _
  have hmp : m ⊆ period512 ε x := fun t ht => ht.1
  have hpc : period512 ε x ⊆
      Icc (1 / (order512 ε x : ℝ)) (1 + 1 / (order512 ε x : ℝ)) :=
    fun t ht => ⟨ht.1.le, ht.2⟩
  have hpfin : volume (period512 ε x) < ⊤ :=
    (measure_mono hpc).trans_lt isCompact_Icc.measure_lt_top
  haveI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.2 ((measure_mono hmp).trans_lt hpfin).ne
  have hbound (s : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
      ‖polynomial512 s c t‖ ≤ ∑ n ∈ s, ‖c n‖ := by
    unfold polynomial512
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  let aa : ℝ := ∑ n ∈ sa, ‖a n‖
  let bb : ℝ := ∑ n ∈ sb, ‖b n‖
  have haa0 : 0 ≤ aa := Finset.sum_nonneg fun n hn => norm_nonneg _
  have hbb0 : 0 ≤ bb := Finset.sum_nonneg fun n hn => norm_nonneg _
  let F : ℝ → ℝ → ℝ := fun t s => A t ^ 2 * B s ^ 2 * kernelWeight561 H (t - s)
  let Q : ℝ → ℝ → ℝ := fun t s => A t * A s * B t * B s * kernelWeight561 H (t - s)
  have hF0 (t s : ℝ) : 0 ≤ F t s := by
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (kernelWeight561_nonneg hH0 _)
  have hQ0 (t s : ℝ) : 0 ≤ Q t s := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hA0 _) (hA0 _))
      (hB0 _)) (hB0 _)) (kernelWeight561_nonneg hH0 _)
  have hFm : Measurable (Function.uncurry F) := by
    exact (((hAc.measurable.comp measurable_fst).pow_const 2).mul
      ((hBc.measurable.comp measurable_snd).pow_const 2)).mul
      ((measurable_kernelWeight561 H).comp (measurable_fst.sub measurable_snd))
  have hFi : Integrable (Function.uncurry F) (μ.prod μ) := by
    refine Integrable.of_bound hFm.aestronglyMeasurable (aa ^ 2 * bb ^ 2 * H) ?_
    filter_upwards [] with p
    change ‖F p.1 p.2‖ ≤ aa ^ 2 * bb ^ 2 * H
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 p.1 p.2)]
    apply mul_le_mul
    · exact mul_le_mul
        (pow_le_pow_left₀ (hA0 _) (hbound sa a p.1) 2)
        (pow_le_pow_left₀ (hB0 _) (hbound sb b p.2) 2)
        (sq_nonneg _) (sq_nonneg _)
    · exact kernelWeight561_le hH0 _
    · exact kernelWeight561_nonneg hH0 _
    · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hYoung (t s : ℝ) : Q t s ≤ (1 / 2 : ℝ) * (F t s + F s t) := by
    have h := sq_nonneg (A t * B s - A s * B t)
    calc Q t s = ((A t * B s) * (A s * B t)) * kernelWeight561 H (t - s) := by
          dsimp [Q]; ring
      _ ≤ (((A t * B s) ^ 2 + (A s * B t) ^ 2) / 2) *
          kernelWeight561 H (t - s) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [h]) (kernelWeight561_nonneg hH0 _)
      _ = (1 / 2 : ℝ) * (F t s + F s t) := by
        dsimp [F]
        rw [kernelWeight561_sub_comm H s t]
        ring
  have hLi : Integrable (fun t => ∫ s, F t s ∂μ) μ := hFi.integral_prod_left
  have hRi : Integrable (fun t => ∫ s, F s t ∂μ) μ := hFi.integral_prod_right
  have hfirst : (∫ t, ∫ s, Q t s ∂μ ∂μ) ≤ (∫ t, ∫ s, F t s ∂μ ∂μ) := by
    have hstep : (∫ t, ∫ s, Q t s ∂μ ∂μ) ≤
        ∫ t, (1 / 2 : ℝ) * ((∫ s, F t s ∂μ) + (∫ s, F s t ∂μ)) ∂μ := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun t => integral_nonneg (hQ0 t))
        ((hLi.add hRi).const_mul (1 / 2))
      filter_upwards [hFi.prod_right_ae, hFi.prod_left_ae] with t ht hs
      change Integrable (fun s => F t s) μ at ht
      change Integrable (fun s => F s t) μ at hs
      have hinner := integral_mono_of_nonneg
        (Filter.Eventually.of_forall (hQ0 t)) ((ht.add hs).const_mul (1 / 2))
        (Filter.Eventually.of_forall (hYoung t))
      change (∫ s, Q t s ∂μ) ≤ (1 / 2 : ℝ) * ((∫ s, F t s ∂μ) + (∫ s, F s t ∂μ))
      change (∫ s, Q t s ∂μ) ≤ ∫ s, (1 / 2 : ℝ) * (F t s + F s t) ∂μ at hinner
      rw [integral_const_mul, integral_add ht hs] at hinner
      exact hinner
    rw [integral_const_mul, integral_add hLi hRi,
      ← integral_integral_swap hFi] at hstep
    linarith
  have hAp : IntegrableOn (fun t => A t ^ 2) (period512 ε x) :=
    ((hAc.pow 2).integrableOn_Icc).mono_set hpc
  have hAi : Integrable (fun t => A t ^ 2) μ := hAp.mono_set hmp
  have hAM : (∫ t, A t ^ 2 ∂μ) ≤ longEnergy561 ε x a :=
    setIntegral_mono_set hAp (Filter.Eventually.of_forall fun t => sq_nonneg (A t))
      (Filter.Eventually.of_forall fun t ht => hmp ht)
  have hBnd : (∫ t, ∫ s, F t s ∂μ ∂μ) ≤ (∫ t, A t ^ 2 * C ∂μ) := by
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => integral_nonneg (hF0 t)) (hAi.mul_const C)
    filter_upwards [] with t
    have hst := hsec t
    change (∫ s, F t s ∂μ) ≤ A t ^ 2 * C
    dsimp only [F]
    simp_rw [mul_assoc, integral_const_mul]
    exact mul_le_mul_of_nonneg_left hst (sq_nonneg _)
  have hsecond : (∫ t, ∫ s, F t s ∂μ ∂μ) ≤ longEnergy561 ε x a * C := by
    calc
      (∫ t, ∫ s, F t s ∂μ ∂μ) ≤ (∫ t, A t ^ 2 * C ∂μ) := hBnd
      _ = (∫ t, A t ^ 2 ∂μ) * C := integral_mul_const C _
      _ ≤ longEnergy561 ε x a * C := mul_le_mul_of_nonneg_right hAM hC
  change (∫ t, ∫ s, Q t s ∂μ ∂μ) ≤
    1 * longEnergy561 ε x a * Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W
  simpa only [one_mul, mul_assoc] using hfirst.trans hsecond

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
