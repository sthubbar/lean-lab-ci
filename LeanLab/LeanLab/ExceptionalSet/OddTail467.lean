import LeanLab.ExceptionalSet.OddKernel467
import LeanLab.ExceptionalSet.PrimeTail385

/-!
P0082 page368, the tail removal after display34.
The shifted kernel has inverse square decay with twice the old constant.
The existing unit energy and tail summation results then apply directly.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.OddTail467
open Real MeasureTheory Set ComplexConjugate
open LeanLab.ExceptionalSet.U1539 (Sp Kfun eC)
open LeanLab.ExceptionalSet.OddKernel467 (evenKernel)

/-- P0082 page367 after display31. The phase has unit norm. -/
theorem norm_evenKernel (Δ α : ℝ) :
    ‖evenKernel Δ α‖ = (1 / 2 : ℝ) * |Kfun Δ ((1 / 2) * α)| := by
  simp [evenKernel, U1539.norm_eC, Complex.norm_real, Real.norm_eq_abs]

/-- P0082 page368 tail removal. The shifted kernel has explicit inverse square decay. -/
theorem evenKernel_inverse_square (Δ α : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hα : α ≠ 0) :
    ‖evenKernel Δ α‖ ≤ 2 / (Δ * (Real.pi * α) ^ 2) := by
  rw [norm_evenKernel]
  have h := mul_le_mul_of_nonneg_left
    (KernelTail385.kernel_abs_le_inverse_square Δ ((1 / 2) * α) hΔ hΔ1
      (mul_ne_zero (by norm_num) hα)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  convert h using 1
  field_simp [hΔ.ne', Real.pi_ne_zero, hα]

/-- P0082 page368 tail removal. This is the shifted prime integrand. -/
noncomputable def integrand (P X Δ v α : ℝ) : ℂ :=
  Sp P X α ^ 2 * evenKernel Δ α * eC (-(α * v))

/-- P0082 page368 tail removal. The finite prime square is bounded, so the shifted
integrable kernel gives an integrable prime expression. -/
theorem total_integrable (P X Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    Integrable (integrand P X Δ v) := by
  let s := (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime
  let B : ℝ := ∑ p ∈ s, ‖(Real.log p : ℂ)‖
  have hs (α : ℝ) : ‖Sp P X α‖ ≤ B := by
    change ‖∑ p ∈ s, (Real.log p : ℂ) * eC (α * p)‖ ≤ B
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro p hp
    rw [norm_mul, U1539.norm_eC, mul_one]
  have hbound (α : ℝ) : ‖Sp P X α ^ 2 * eC (-(α * v))‖ ≤ B ^ 2 := by
    rw [norm_mul, norm_pow, U1539.norm_eC, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) (hs α) 2
  have hc : Continuous (fun α : ℝ => Sp P X α ^ 2 * eC (-(α * v))) := by
    unfold Sp eC
    fun_prop
  have hi := (OddKernel467.evenKernel_integrable Δ hΔ hΔ1).mul_bdd
    hc.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  convert hi using 1
  funext α
  simp only [integrand]
  ring

/-- P0082 page368 tail removal. Reflection preserves the absolute integrand. -/
theorem norm_integrand_neg (P X Δ v x : ℝ) :
    ‖integrand P X Δ v (-x)‖ = ‖integrand P X Δ v x‖ := by
  have he (t : ℝ) : conj (eC t) = eC (-t) := BG2026.conj_eC t
  have hs : Sp P X (-x) = conj (Sp P X x) := by
    simp only [Sp, map_sum, map_mul, Complex.conj_ofReal, he, neg_mul]
  have hk : Kfun Δ (-((1 / 2) * x)) = Kfun Δ ((1 / 2) * x) := by
    simp only [Kfun, mul_neg, Real.sinc_neg]
  simp only [integrand, norm_mul, norm_pow, U1539.norm_eC, mul_one,
    norm_evenKernel, mul_neg, hs, Complex.norm_conj, hk]

/-- P0082 page368 tail removal. Prime energy on each unit block gives the
inverse square block estimate with an explicit constant. -/
theorem prime_block_le (P X Δ a v : ℝ) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (ha : 0 < a) :
    (∫ α in a..a + 1, ‖integrand P X Δ v α‖) ≤
      2 * (Real.log 4 * X * Real.log X) / (Δ * (Real.pi * a) ^ 2) := by
  let B : ℝ := 2 / (Δ * (Real.pi * a) ^ 2)
  have hden : 0 < Δ * (Real.pi * a) ^ 2 := by positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint (x : ℝ) (hx : x ∈ Icc a (a + 1)) :
      ‖integrand P X Δ v x‖ ≤ ‖Sp P X x‖ ^ 2 * B := by
    have hx0 : 0 < x := ha.trans_le hx.1
    have hsq := pow_le_pow_left₀ (mul_pos Real.pi_pos ha).le
      (mul_le_mul_of_nonneg_left hx.1 Real.pi_pos.le) 2
    have hk : ‖evenKernel Δ x‖ ≤ B :=
      (evenKernel_inverse_square Δ x hΔ hΔ1 hx0.ne').trans
        (div_le_div_of_nonneg_left (by norm_num) hden
          (mul_le_mul_of_nonneg_left hsq hΔ.le))
    simpa only [integrand, norm_mul, norm_pow, U1539.norm_eC, mul_one] using
      mul_le_mul_of_nonneg_left hk (sq_nonneg ‖Sp P X x‖)
  have hc : Continuous (integrand P X Δ v) := by
    unfold integrand
    exact (((by unfold Sp eC; fun_prop : Continuous (Sp P X)).pow 2).mul
      (OddKernel467.evenKernel_continuous Δ)).mul (by unfold eC; fun_prop)
  have hp : Continuous (fun x : ℝ => ‖Sp P X x‖ ^ 2) := by unfold Sp eC; fun_prop
  calc (∫ x in a..a + 1, ‖integrand P X Δ v x‖)
      ≤ ∫ x in a..a + 1, ‖Sp P X x‖ ^ 2 * B :=
        intervalIntegral.integral_mono_on (by linarith) (hc.norm.intervalIntegrable _ _)
          ((hp.mul_const B).intervalIntegrable _ _) hpoint
    _ = (∫ x in a..a + 1, ‖Sp P X x‖ ^ 2) * B := by
      rw [intervalIntegral.integral_mul_const]
    _ ≤ (Real.log 4 * X * Real.log X) * B :=
      mul_le_mul_of_nonneg_right (PrimeEnergy385.prime_energy_le P X a hX) hB
    _ = _ := by dsimp [B]; ring

/-- The positive prime kernel tail at an integer cutoff, P0082 page368 after display34. -/
theorem positive_tail_le (P X Δ v : ℝ) (hX : 2 ≤ X) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (K : ℕ) (hK : 2 ≤ K) :
    (∫ α in Ioi (K : ℝ), ‖integrand P X Δ v α‖) ≤
      (2 * (Real.log 4 * X * Real.log X)) / (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) := by
  let A := 2 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2)
  have hLX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hf : Integrable (fun α => ‖integrand P X Δ v α‖) :=
    (total_integrable P X Δ v hΔ hΔ1).norm
  have hb (k : ℕ) (hk : K ≤ k) :
      (∫ α in (k : ℝ)..(k : ℝ) + 1, ‖integrand P X Δ v α‖) ≤ A / (k : ℝ) ^ 2 := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    simpa only [A, div_div, mul_pow, mul_assoc] using
      prime_block_le P X Δ k v hX hΔ hΔ1 hk0
  simpa only [A, div_div] using
    TailPartition385.integral_Ioi_le_of_blocks _ hf K hK A hA hb

/-- Both prime kernel tails at an integer cutoff, P0082 page368 after display34. -/
theorem outside_nat_tail_le (P X Δ v : ℝ) (hX : 2 ≤ X) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (K : ℕ) (hK : 2 ≤ K) :
    (∫ α in (Icc (-(K : ℝ)) (K : ℝ))ᶜ, ‖integrand P X Δ v α‖) ≤
      4 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) := by
  have hf : Integrable (fun α => ‖integrand P X Δ v α‖) :=
    (total_integrable P X Δ v hΔ hΔ1).norm
  have hn : (∫ α in Iio (-(K : ℝ)), ‖integrand P X Δ v α‖) =
      (∫ α in Ioi (K : ℝ), ‖integrand P X Δ v α‖) := by
    rw [← integral_Iic_eq_integral_Iio,
      ← integral_comp_neg_Ioi (K : ℝ) (fun α => ‖integrand P X Δ v α‖)]
    exact setIntegral_congr_fun measurableSet_Ioi (fun α _ => norm_integrand_neg P X Δ v α)
  have hd : Disjoint (Iio (-(K : ℝ))) (Ioi (K : ℝ)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have h1 : x < -(K : ℝ) := hx
    have h2 : (K : ℝ) < x := hy
    have h0 := Nat.cast_nonneg (α := ℝ) K
    linarith
  have hset : (Icc (-(K : ℝ)) (K : ℝ))ᶜ = Iio (-(K : ℝ)) ∪ Ioi (K : ℝ) := by
    ext x
    simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]
  rw [hset, setIntegral_union hd measurableSet_Ioi hf.integrableOn hf.integrableOn, hn]
  have h := positive_tail_le P X Δ v hX hΔ hΔ1 K hK
  calc _ ≤ (2 * (Real.log 4 * X * Real.log X)) / (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) +
      (2 * (Real.log 4 * X * Real.log X)) / (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) := add_le_add h h
    _ = _ := by ring

/-- The explicit real cutoff tail bound in P0082 page368 after display34. -/
theorem outside_real_tail_le (P X Δ v T : ℝ) (hX : 2 ≤ X) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hT : 4 ≤ T) :
    (∫ α in (Icc (-T) T)ᶜ, ‖integrand P X Δ v α‖) ≤
      8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T) := by
  let K : ℕ := ⌊T⌋₊
  have hK : 2 ≤ K := Nat.le_floor (by norm_num; linarith)
  have hfloor : (K : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hlt : T < (K : ℝ) + 1 := Nat.lt_floor_add_one T
  have hcomp : T ≤ 2 * ((K : ℝ) - 1) := by linarith
  have hf : Integrable (fun α => ‖integrand P X Δ v α‖) :=
    (total_integrable P X Δ v hΔ hΔ1).norm
  have hsub : (Icc (-T) T)ᶜ ⊆ (Icc (-(K : ℝ)) (K : ℝ))ᶜ := by
    intro x hx hmem
    exact hx ⟨(neg_le_neg hfloor).trans hmem.1, hmem.2.trans hfloor⟩
  have hmono : (∫ α in (Icc (-T) T)ᶜ, ‖integrand P X Δ v α‖) ≤
      (∫ α in (Icc (-(K : ℝ)) (K : ℝ))ᶜ, ‖integrand P X Δ v α‖) :=
    setIntegral_mono_set hf.integrableOn (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      hsub.eventuallySubset
  refine hmono.trans ((outside_nat_tail_le P X Δ v hX hΔ hΔ1 K hK).trans ?_)
  have hK1 : 0 < (K : ℝ) - 1 := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hd1 : 0 < Δ * Real.pi ^ 2 * ((K : ℝ) - 1) := by positivity
  have hd2 : 0 < Δ * Real.pi ^ 2 * T := by positivity
  apply (div_le_div_iff₀ hd1 hd2).mpr
  have hLX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hm := mul_le_mul_of_nonneg_left hcomp
    (show 0 ≤ 4 * (Real.log 4 * X * Real.log X) * (Δ * Real.pi ^ 2) by positivity)
  nlinarith only [hm]

/-- Restricting any integration set to the real cutoff loses at most the absolute tail.
Source: P0082 page368 after display34. -/
theorem truncation_error_le (P X Δ v T : ℝ) (hX : 2 ≤ X) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hT : 4 ≤ T) (M : Set ℝ) :
    ‖(∫ α in M, integrand P X Δ v α) -
        (∫ α in M ∩ Icc (-T) T, integrand P X Δ v α)‖ ≤
      8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T) := by
  have hf : Integrable (integrand P X Δ v) :=
    total_integrable P X Δ v hΔ hΔ1
  have he := integral_inter_add_sdiff (t := Icc (-T) T) measurableSet_Icc
    (show IntegrableOn (integrand P X Δ v) M from hf.integrableOn)
  have hd : (∫ α in M, integrand P X Δ v α) -
      (∫ α in M ∩ Icc (-T) T, integrand P X Δ v α) =
      ∫ α in M \ Icc (-T) T, integrand P X Δ v α := by
    rw [← he]; abel
  rw [hd]
  refine (norm_integral_le_integral_norm _).trans (le_trans ?_
    (outside_real_tail_le P X Δ v T hX hΔ hΔ1 hT))
  exact setIntegral_mono_set hf.norm.integrableOn
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (show M \ Icc (-T) T ⊆ (Icc (-T) T)ᶜ from fun _ h => h.2).eventuallySubset

end LeanLab.ExceptionalSet.OddTail467
