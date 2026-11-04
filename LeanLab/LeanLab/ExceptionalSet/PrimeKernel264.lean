import LeanLab.ExceptionalSet.KernelTransform264
import LeanLab.ExceptionalSet.State1539

/-
Finite prime expansion for the kernel integral of Brudern and Perelli 1998.
Source: page 357 displays 5 and 6.
AI wrote the Lean code. Goldbach is open.
-/

open MeasureTheory Finset
open LeanLab.ExceptionalSet.U1539
open LeanLab.ExceptionalSet.BrudernPerelli1998

namespace LeanLab.ExceptionalSet.PrimeKernel264

/-- A unit modulus exponential preserves integrability of the paper kernel. -/
theorem kernel_phase_integrable {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (v : ℝ) :
    Integrable (fun α : ℝ => (Kfun Δ α : ℂ) * eC (-(v * α))) := by
  apply (KernelTransform264.Kfun_integrable hΔ hΔ1).mul_bdd
    (c := 1)
  · apply Continuous.aestronglyMeasurable
    unfold eC
    fun_prop
  · filter_upwards with α
    rw [norm_eC]

/-- Integrating a finite exponential sum against the kernel evaluates its finite Fourier sum. -/
theorem integral_finite_phase {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ν : ι → ℝ)
    {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (v : ℝ) :
    (∫ α : ℝ, (∑ n ∈ s, a n * eC (α * ν n)) * (Kfun Δ α : ℂ) * eC (-(v * α))) =
      ∑ n ∈ s, a n * ftR (fun α : ℝ => (Kfun Δ α : ℂ)) (v - ν n) := by
  have he (x y : ℝ) : eC x * eC y = eC (x + y) := by
    unfold eC
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpoint (α : ℝ) :
      (∑ n ∈ s, a n * eC (α * ν n)) * (Kfun Δ α : ℂ) * eC (-(v * α)) =
      ∑ n ∈ s, a n * ((Kfun Δ α : ℂ) * eC (-((v - ν n) * α))) := by
    rw [sum_mul, sum_mul]
    apply sum_congr rfl
    intro n hn
    have hp : α * ν n + -(v * α) = -((v - ν n) * α) := by ring
    rw [show a n * eC (α * ν n) * (Kfun Δ α : ℂ) * eC (-(v * α)) =
      a n * ((Kfun Δ α : ℂ) * (eC (α * ν n) * eC (-(v * α)))) by ring, he, hp]
  simp_rw [hpoint]
  rw [integral_finsetSum s (fun n _ => (kernel_phase_integrable hΔ hΔ1 (v - ν n)).const_mul (a n))]
  apply sum_congr rfl
  intro n hn
  rw [integral_const_mul]
  rfl

/-- The square of the prime sum is the finite prime pair exponential sum. -/
theorem Sp_sq (P X α : ℝ) :
    Sp P X α ^ 2 =
      ∑ r ∈ (((Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime).product
        ((Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime)),
        ((Real.log r.1 : ℂ) * (Real.log r.2 : ℂ)) * eC (α * ((r.1 + r.2 : ℕ) : ℝ)) := by
  have he (x y : ℝ) : eC x * eC y = eC (x + y) := by
    unfold eC
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [Sp, pow_two, Finset.product_eq_sprod, Finset.sum_product, sum_mul]
  apply sum_congr rfl
  intro p hp
  rw [mul_sum]
  apply sum_congr rfl
  intro q hq
  have harg : α * (p : ℝ) + α * q = α * ((p + q : ℕ) : ℝ) := by push_cast; ring
  rw [show (Real.log p : ℂ) * eC (α * p) * ((Real.log q : ℂ) * eC (α * q)) =
    ((Real.log p : ℂ) * (Real.log q : ℂ)) * (eC (α * p) * eC (α * q)) by ring, he, harg]

/-- If the prime range excludes two, the total kernel integral is zero at a nonsolution. -/
theorem total_integral_zero {γ Δ P X : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hP : 2 ≤ P)
    (n : ℕ) (hn : ¬ Solvable γ n) :
    (∫ α : ℝ, Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * F γ n))) = 0 := by
  have hphase (α : ℝ) : -(α * F γ n) = -(F γ n * α) := by ring
  simp_rw [Sp_sq, hphase]
  rw [integral_finite_phase _ _ _ hΔ hΔ1]
  apply sum_eq_zero
  intro r hr
  rcases mem_product.mp hr with ⟨hp, hq⟩
  have hp' := (mem_filter.mp hp).2
  have hq' := (mem_filter.mp hq).2
  have hpf := (mem_Ioc.mp (mem_filter.mp hp).1).1
  have hqf := (mem_Ioc.mp (mem_filter.mp hq).1).1
  have hfloor : 2 ≤ ⌊P⌋₊ := Nat.le_floor hP
  have hpodd : Odd r.1 := Nat.odd_iff.mpr (hp'.eq_two_or_odd.resolve_left (by omega))
  have hqodd : Odd r.2 := Nat.odd_iff.mpr (hq'.eq_two_or_odd.resolve_left (by omega))
  have habs : 1 ≤ |F γ n - ((r.1 + r.2 : ℕ) : ℝ)| := by
    by_contra h
    apply hn
    refine ⟨r.1, r.2, hp', hq', hpodd, hqodd, ?_⟩
    rw [abs_sub_comm]
    exact lt_of_not_ge h
  rw [KernelTransform264.ftR_Kfun_zero hΔ hΔ1 habs, mul_zero]

/-- The full prime square kernel integrand is integrable. -/
theorem total_integrable {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (P X v : ℝ) :
    Integrable (fun α : ℝ => Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * v))) := by
  let s := (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime
  let B : ℝ := ∑ p ∈ s, ‖(Real.log p : ℂ)‖
  have hs (α : ℝ) : ‖Sp P X α‖ ≤ B := by
    change ‖∑ p ∈ s, (Real.log p : ℂ) * eC (α * p)‖ ≤ B
    refine (norm_sum_le _ _).trans ?_
    apply sum_le_sum
    intro p hp
    rw [norm_mul, norm_eC, mul_one]
  have hbound (α : ℝ) : ‖Sp P X α ^ 2 * eC (-(α * v))‖ ≤ B ^ 2 := by
    rw [norm_mul, norm_pow, norm_eC, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) (hs α) 2
  have hc : Continuous (fun α : ℝ => Sp P X α ^ 2 * eC (-(α * v))) := by
    unfold Sp eC
    fun_prop
  have hi := (KernelTransform264.Kfun_integrable hΔ hΔ1).mul_bdd
    hc.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  convert hi using 1
  funext α
  ring

/-- The major arc set is measurable. -/
theorem measurableSet_majorArcs (P X : ℝ) : MeasurableSet (majorArcs P X) := by
  unfold majorArcs
  measurability

/-- On a nonsolution, the major integral real part is bounded by the minor integral norm. -/
theorem nonsolution_split {A : Set ℝ} (hA : MeasurableSet A)
    {γ Δ P X : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hP : 2 ≤ P)
    (n : ℕ) (hn : ¬ Solvable γ n) :
    (∫ α in A, Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * F γ n))).re ≤
      ‖∫ α in Aᶜ, Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * F γ n))‖ := by
  have hi := integral_add_compl hA (total_integrable hΔ hΔ1 P X (F γ n))
  rw [total_integral_zero hΔ hΔ1 hP n hn] at hi
  have he := eq_neg_of_add_eq_zero_left hi
  calc
    _ ≤ ‖∫ α in A, Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * F γ n))‖ :=
      Complex.re_le_norm _
    _ = _ := by rw [he, norm_neg]

/-- The paper window parameters eventually satisfy the elementary split inequalities. -/
theorem split_parameters_eventually (γ δ κ c₀ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hδ : 0 < δ) (hκ : 0 < κ) (hc₀ : 0 < c₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      2 ≤ F γ N ^ (6 * δ) ∧
      0 < calE γ κ N ^ (-(1 / 8 : ℝ)) ∧ calE γ κ N ^ (-(1 / 8 : ℝ)) < 1 ∧
      calE γ κ N ^ (-(1 / 3 : ℝ)) < c₀ * calE γ κ N ^ (-(1 / 10 : ℝ)) := by
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log N) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hF : Filter.Tendsto (fun N : ℕ => F γ N) Filter.atTop Filter.atTop := by
    exact Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog)
  have hP : Filter.Tendsto (fun N : ℕ => F γ N ^ (6 * δ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 6 * δ)).comp hF
  have hE : Filter.Tendsto (fun N : ℕ => calE γ κ N) Filter.atTop Filter.atTop := by
    exact Real.tendsto_exp_atTop.comp
      (((tendsto_rpow_atTop (by linarith : 0 < 3 - 2 * γ)).comp hlog).const_mul_atTop hκ)
  have hsmall : Filter.Tendsto (fun N : ℕ => calE γ κ N ^ (-(7 / 30 : ℝ)))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : 0 < (7 / 30 : ℝ))).comp hE
  apply Filter.eventually_atTop.mp
  filter_upwards [hP.eventually_ge_atTop 2, hE.eventually_ge_atTop 2,
    hsmall.eventually (gt_mem_nhds hc₀)] with N hPN hEN hSN
  have hpos : 0 < calE γ κ N := Real.exp_pos _
  refine ⟨hPN, Real.rpow_pos_of_pos hpos _,
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num), ?_⟩
  have he : calE γ κ N ^ (-(1 / 3 : ℝ)) =
      calE γ κ N ^ (-(7 / 30 : ℝ)) * calE γ κ N ^ (-(1 / 10 : ℝ)) := by
    rw [← Real.rpow_add hpos]
    norm_num
  rw [he]
  exact mul_lt_mul_of_pos_right hSN (Real.rpow_pos_of_pos hpos _)

end LeanLab.ExceptionalSet.PrimeKernel264
