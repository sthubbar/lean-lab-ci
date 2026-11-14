import LeanLab.ExceptionalSet.OddKernel467
import LeanLab.ExceptionalSet.Fejer467
import LeanLab.ExceptionalSet.UpJ200.PrimeTail385
import LeanLab.ExceptionalSet.UpJ200.Decomp467a
import LeanLab.ExceptionalSet.UpJ200.Moment385

/-!
P0082 pages366 to369. Upstream access to the shifted odd coefficient transfers.
Existing declarations keep their names and statements when moved here.
Source: https://doi.org/10.5802/aif.1621
AI wrote the Lean code. Goldbach is open.
-/


namespace LeanLab.ExceptionalSet.Decomp371a
open Real Finset
open LeanLab.ExceptionalSet.U1539 (Sp eC majorArcs)

/-- P0082 page 357, the prime sum preceding display 6. Its integer frequencies
make it periodic with period one, as required by the Fourier coefficient argument. -/
theorem Sp_periodic (P X : ℝ) : Function.Periodic (Sp P X) 1 := by
  intro α
  unfold Sp
  apply Finset.sum_congr rfl
  intro p hp
  have he : eC ((α + 1) * (p : ℝ)) = eC (α * (p : ℝ)) := by
    unfold eC
    push_cast
    rw [show (2 * (Real.pi : ℂ) * Complex.I * (((α : ℂ) + 1) * (p : ℂ))) =
      2 * (Real.pi : ℂ) * Complex.I * ((α : ℂ) * (p : ℂ)) + (p : ℂ) * (2 * Real.pi * Complex.I) by ring]
    rw [Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  rw [he]


/-- P0082 page 357 major arc definition. Translation by one shifts the integer
numerator by its denominator and preserves both coprimality and arc width. -/
theorem majorArcs_periodic (P X : ℝ) : Function.Periodic (majorArcs P X) 1 := by
  intro α
  apply propext
  constructor
  · rintro ⟨q, a, hq, hqP, hcop, hclose⟩
    refine ⟨q, a - q, hq, hqP, ?_, ?_⟩
    · simpa only [Int.gcd_sub_self_left] using hcop
    · convert hclose using 1 <;> push_cast <;> congr 1 <;> ring
  · rintro ⟨q, a, hq, hqP, hcop, hclose⟩
    refine ⟨q, a + q, hq, hqP, ?_, ?_⟩
    · simpa only [Int.gcd_add_self_left] using hcop
    · convert hclose using 1 <;> push_cast <;> congr 1 <;> ring

end LeanLab.ExceptionalSet.Decomp371a


namespace LeanLab.ExceptionalSet.Decomp404a
open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539

/-- P0082 page 357 display 8. The major arc indicator times S squared
is integrable on one period. -/
theorem major_intervalIntegrable (P X : ℝ) :
    IntervalIntegrable ((majorArcs P X).indicator (fun α => Sp P X α ^ 2)) volume 0 1 := by
  have hc : Continuous (fun α : ℝ => Sp P X α ^ 2) := by
    unfold Sp eC
    fun_prop
  exact ⟨(hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
    (PrimeKernel264.measurableSet_majorArcs P X),
    by simp⟩


/-- P0082 page 357 display 7. The Fourier coefficient of the indicated
prime square is precisely R1 with the same integer frequency. -/
theorem major_hcheck (P X : ℝ) (m : ℤ) :
    hcheck ((majorArcs P X).indicator (fun α => Sp P X α ^ 2)) m = R1 P X m := by
  classical
  unfold hcheck R1
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have he : (fun α : ℝ => (majorArcs P X).indicator (fun α => Sp P X α ^ 2) α *
      eC (-(α * m))) = (majorArcs P X).indicator (fun α => Sp P X α ^ 2 * eC (-(α * m))) := by
    ext α
    by_cases hα : α ∈ majorArcs P X <;> simp [hα]
  rw [he, ← integral_Icc_eq_integral_Ioc,
    setIntegral_indicator (PrimeKernel264.measurableSet_majorArcs P X), Set.inter_comm]

end LeanLab.ExceptionalSet.Decomp404a


namespace LeanLab.ExceptionalSet.OddCoefficient467
open Real Finset MeasureTheory
open LeanLab.ExceptionalSet.U1539 (Sp eC R1 majorArcs hcheck)

/-- P0082 page366 display28. R2 is the Fourier coefficient of the minor
arc indicator times the square of the prime sum on one period. -/
noncomputable def minorCoefficient (P X : ℝ) (m : ℤ) : ℂ :=
  hcheck ((majorArcs P X)ᶜ.indicator (fun α => Sp P X α ^ 2)) m

/-- P0082 page366 before display28. The full prime square has zero
Fourier coefficient at an odd integer when the prime range excludes two. -/
theorem prime_square_odd_coefficient (P X : ℝ) (hP : 2 ≤ P) (m : ℤ) (hm : Odd m) :
    hcheck (fun α => Sp P X α ^ 2) m = 0 := by
  classical
  let s := (Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime
  have he (α : ℝ) : Sp P X α ^ 2 * eC (-(α * m)) =
      ∑ p ∈ s, ∑ q ∈ s, ((Real.log p : ℂ) * (Real.log q : ℂ)) *
        BG2026.eC ((((p : ℤ) + q - m : ℤ) : ℝ) * α) := by
    rw [PrimeKernel264.Sp_sq, Finset.product_eq_sprod, sum_product, sum_mul]
    apply sum_congr rfl
    intro p hp
    rw [sum_mul]
    apply sum_congr rfl
    intro q hq
    change ((Real.log p : ℂ) * (Real.log q : ℂ)) *
      eC (α * ((p + q : ℕ) : ℝ)) * eC (-(α * m)) =
        ((Real.log p : ℂ) * (Real.log q : ℂ)) * eC ((((p : ℤ) + q - m : ℤ) : ℝ) * α)
    rw [mul_assoc, ← Fejer467.phase_add]
    congr 2
    push_cast
    ring
  unfold hcheck
  simp_rw [he]
  rw [BG2026.integral_double_sum]
  apply sum_eq_zero
  intro p hp
  apply sum_eq_zero
  intro q hq
  have hp' := (mem_filter.mp hp).2
  have hq' := (mem_filter.mp hq).2
  have hpf := (mem_Ioc.mp (mem_filter.mp hp).1).1
  have hqf := (mem_Ioc.mp (mem_filter.mp hq).1).1
  have hfloor : 2 ≤ ⌊P⌋₊ := Nat.le_floor hP
  have hpodd : Odd p := Nat.odd_iff.mpr (hp'.eq_two_or_odd.resolve_left (by omega))
  have hqodd : Odd q := Nat.odd_iff.mpr (hq'.eq_two_or_odd.resolve_left (by omega))
  have hne : (p : ℤ) + q - m ≠ 0 := by
    intro hf
    have hsum : Even (((p + q : ℕ) : ℤ)) :=
      (Int.even_coe_nat _).mpr (hpodd.add_odd hqodd)
    have hmeq : m = ((p + q : ℕ) : ℤ) := by push_cast; omega
    apply (Int.not_even_iff_odd.mpr hm)
    rwa [hmeq]
  simp only [hne, ite_false, mul_zero]

/-- P0082 page366 display28. The minor arc indicator times the prime
square is integrable on one period. -/
theorem minor_intervalIntegrable (P X : ℝ) :
    IntervalIntegrable ((majorArcs P X)ᶜ.indicator (fun α => Sp P X α ^ 2)) volume 0 1 := by
  have hc : Continuous (fun α : ℝ => Sp P X α ^ 2) := by unfold Sp eC; fun_prop
  exact ⟨(hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
    (PrimeKernel264.measurableSet_majorArcs P X).compl, by simp⟩

/-- P0082 page366 display28. Major and minor coefficients add to the
full coefficient because the two indicators partition one period. -/
theorem major_add_minor_coefficient (P X : ℝ) (m : ℤ) :
    R1 P X m + minorCoefficient P X m = hcheck (fun α => Sp P X α ^ 2) m := by
  classical
  rw [← Decomp404a.major_hcheck]
  unfold minorCoefficient hcheck
  have hc : Continuous (fun α : ℝ => eC (-(α * m))) := by unfold eC; fun_prop
  rw [← intervalIntegral.integral_add
    ((Decomp404a.major_intervalIntegrable P X).mul_continuousOn hc.continuousOn)
    ((minor_intervalIntegrable P X).mul_continuousOn hc.continuousOn)]
  apply intervalIntegral.integral_congr
  intro α hα
  by_cases ha : α ∈ majorArcs P X <;> simp [ha]

/-- P0082 page366 display28. At an odd integer, the minor coefficient
is the negative of the major coefficient. -/
theorem odd_minor_eq_neg_major (P X : ℝ) (hP : 2 ≤ P) (m : ℤ) (hm : Odd m) :
    minorCoefficient P X m = -R1 P X m := by
  have hh := major_add_minor_coefficient P X m
  rw [prime_square_odd_coefficient P X hP m hm] at hh
  linear_combination hh

/-- P0082 page367 final display. The shifted kernel isolates the upper
adjacent minor coefficient with the printed trapezoid weight. -/
theorem weighted_minor_identity (P X Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (∫ α in (majorArcs P X)ᶜ,
      Sp P X α ^ 2 * OddKernel467.evenKernel Δ α * eC (-(α * v))) =
        (KernelTransform264.weight Δ (2 * Int.fract v - 1) : ℂ) *
          minorCoefficient P X (⌊v⌋ + 1) := by
  classical
  let h : ℝ → ℂ := (majorArcs P X)ᶜ.indicator (fun α => Sp P X α ^ 2)
  have hper : Function.Periodic h 1 := by
    intro α
    have hm : α + 1 ∈ majorArcs P X ↔ α ∈ majorArcs P X :=
      Iff.of_eq (Decomp371a.majorArcs_periodic P X α)
    simp only [h, Set.indicator_apply, Set.mem_compl_iff, hm, Decomp371a.Sp_periodic P X α]
  have hh := OddKernel467.weighted_adjacent_identity h hper (minor_intervalIntegrable P X)
    Δ v hΔ hΔ1
  have he : (fun α : ℝ => h α * OddKernel467.evenKernel Δ α * eC (-(α * v))) =
      (majorArcs P X)ᶜ.indicator (fun α =>
        Sp P X α ^ 2 * OddKernel467.evenKernel Δ α * eC (-(α * v))) := by
    ext α
    by_cases ha : α ∈ majorArcs P X <;> simp [h, ha]
  rw [he, integral_indicator (PrimeKernel264.measurableSet_majorArcs P X).compl] at hh
  exact hh

/-- P0082 page367 final display and page368 boundary paragraph. Away
from the fractional boundary, an odd upper neighbor gives minus its major coefficient. -/
theorem plateau_odd_major_identity (P X Δ v : ℝ) (hP : 2 ≤ P)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hm : Odd (⌊v⌋ + 1))
    (hleft : Δ / 2 ≤ Int.fract v) (hright : Int.fract v ≤ 1 - Δ / 2) :
    (∫ α in (majorArcs P X)ᶜ,
      Sp P X α ^ 2 * OddKernel467.evenKernel Δ α * eC (-(α * v))) =
        -R1 P X (⌊v⌋ + 1) := by
  rw [weighted_minor_identity P X Δ v hΔ hΔ1]
  have hp : |2 * Int.fract v - 1| ≤ 1 - Δ := by rw [abs_le]; constructor <;> linarith
  rw [KernelTransform264.weight_one hΔ hΔ1 hp]
  simp only [Complex.ofReal_one, one_mul]
  exact odd_minor_eq_neg_major P X hP _ hm

end LeanLab.ExceptionalSet.OddCoefficient467


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
      mul_le_mul_of_nonneg_right (UpJ200.PrimeEnergy385.prime_energy_le P X a hX) hB
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
    UpJ200.TailPartition385.integral_Ioi_le_of_blocks _ hf K hK A hA hb

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


namespace LeanLab.ExceptionalSet.Decomp483a

open Real Finset MeasureTheory
open LeanLab.ExceptionalSet.U1539 (Sp R1 eC majorArcs hcheck)
open LeanLab.ExceptionalSet.OddCoefficient467 (minorCoefficient)

/-- P0082 page368 before display33. Each minor coefficient is bounded by
one period of the prime square mass, with Mathlib's explicit Chebyshev constant. -/
theorem minorCoefficient_norm_le (P X : ℝ) (hX : 2 ≤ X) (m : ℤ) :
    ‖minorCoefficient P X m‖ ≤ Real.log 4 * X * Real.log X := by
  classical
  unfold minorCoefficient hcheck
  refine (intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 1)
    (Filter.Eventually.of_forall (fun α _ => ?_))
    (show IntervalIntegrable (fun α => ‖Sp P X α‖ ^ 2) volume 0 1 from
      (by unfold Sp eC; fun_prop : Continuous (fun α : ℝ => ‖Sp P X α‖ ^ 2)).intervalIntegrable _ _)).trans ?_
  · by_cases ha : α ∈ majorArcs P X
    · simp [ha]
    · simp [ha, norm_pow, U1539.norm_eC]
  · simpa only [zero_add] using UpJ200.PrimeEnergy385.prime_energy_le P X 0 hX

/-- P0082 page368 displays32 and33. For an arbitrary finite index set
whose upper adjacent integer is odd, the major coefficient moment is bounded
by the full shifted minor moment and the explicit fractional boundary mass. -/
theorem odd_upper_moment_transfer (P X Δ : ℝ) (hP : 2 ≤ P) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (s : Finset ℕ) (v : ℕ → ℝ)
    (hodd : ∀ n ∈ s, Odd (⌊v n⌋ + 1)) :
    (∑ n ∈ s, ‖R1 P X (⌊v n⌋ + 1)‖ ^ 2) ≤
      (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ,
        OddTail467.integrand P X Δ (v n) α‖ ^ 2) +
      (((s.filter (fun n => Int.fract (v n) < Δ / 2 ∨
        1 - Δ / 2 < Int.fract (v n))).card : ℝ) *
          (Real.log 4 * X * Real.log X) ^ 2) := by
  classical
  let bad := fun n => Int.fract (v n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (v n)
  let f := fun n => ‖R1 P X (⌊v n⌋ + 1)‖ ^ 2
  let g := fun n => ‖∫ α in (majorArcs P X)ᶜ,
    OddTail467.integrand P X Δ (v n) α‖ ^ 2
  have hb (n : ℕ) (hn : n ∈ s) : f n ≤ (Real.log 4 * X * Real.log X) ^ 2 := by
    have h := minorCoefficient_norm_le P X hX (⌊v n⌋ + 1)
    rw [OddCoefficient467.odd_minor_eq_neg_major P X hP _ (hodd n hn), norm_neg] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hg (n : ℕ) (hn : n ∈ s) (hgood : ¬ bad n) : f n = g n := by
    have hl : Δ / 2 ≤ Int.fract (v n) := le_of_not_gt (fun h => hgood (Or.inl h))
    have hr : Int.fract (v n) ≤ 1 - Δ / 2 := le_of_not_gt (fun h => hgood (Or.inr h))
    have hi := OddCoefficient467.plateau_odd_major_identity P X Δ (v n)
      hP hΔ hΔ1 (hodd n hn) hl hr
    dsimp only [f, g, OddTail467.integrand]
    rw [hi, norm_neg]
  change (∑ n ∈ s, f n) ≤ (∑ n ∈ s, g n) + _
  rw [← sum_filter_add_sum_filter_not s bad f]
  have hbad : ∑ n ∈ s.filter bad, f n ≤
      ((s.filter bad).card : ℝ) * (Real.log 4 * X * Real.log X) ^ 2 := by
    calc _ ≤ ∑ n ∈ s.filter bad, (Real.log 4 * X * Real.log X) ^ 2 :=
        sum_le_sum (fun n hn => hb n (mem_filter.mp hn).1)
      _ = _ := by simp
  have hgood : ∑ n ∈ s.filter (fun n => ¬ bad n), f n ≤ ∑ n ∈ s, g n := by
    calc _ = ∑ n ∈ s.filter (fun n => ¬ bad n), g n :=
        sum_congr rfl (fun n hn => hg n (mem_filter.mp hn).1 (mem_filter.mp hn).2)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun n _ _ => sq_nonneg _)
  exact (add_le_add hbad hgood).trans_eq (by dsimp [bad]; ring)


/-- P0082 page368 tail removal before display35. The existing absolute tail
bound controls the second moment on every finite index set. -/
theorem shifted_truncation_moment (P X Δ T : ℝ) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hT : 4 ≤ T) (s : Finset ℕ) (v : ℕ → ℝ) :
    (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ,
      OddTail467.integrand P X Δ (v n) α‖ ^ 2) ≤
      2 * (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ ∩ Set.Icc (-T) T,
        OddTail467.integrand P X Δ (v n) α‖ ^ 2) +
      2 * (s.card : ℝ) *
        (8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T)) ^ 2 := by
  let τ := 8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T)
  have hp (n : ℕ) :
      ‖∫ α in (majorArcs P X)ᶜ, OddTail467.integrand P X Δ (v n) α‖ ^ 2 ≤
        2 * ‖∫ α in (majorArcs P X)ᶜ ∩ Set.Icc (-T) T,
          OddTail467.integrand P X Δ (v n) α‖ ^ 2 + 2 * τ ^ 2 := by
    let a := ∫ α in (majorArcs P X)ᶜ, OddTail467.integrand P X Δ (v n) α
    let b := ∫ α in (majorArcs P X)ᶜ ∩ Set.Icc (-T) T,
      OddTail467.integrand P X Δ (v n) α
    have ht : ‖a - b‖ ≤ τ := OddTail467.truncation_error_le P X Δ (v n) T
      hX hΔ hΔ1 hT _
    have hnorm : ‖a‖ ≤ ‖b‖ + τ := by
      calc ‖a‖ = ‖b + (a - b)‖ := by congr 1; abel
        _ ≤ ‖b‖ + ‖a - b‖ := norm_add_le _ _
        _ ≤ ‖b‖ + τ := by linarith [ht]
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
      (add_sq_le.trans_eq (by ring))
  calc _ ≤ ∑ n ∈ s,
      (2 * ‖∫ α in (majorArcs P X)ᶜ ∩ Set.Icc (-T) T,
        OddTail467.integrand P X Δ (v n) α‖ ^ 2 + 2 * τ ^ 2) :=
      sum_le_sum (fun n _ => hp n)
    _ = _ := by rw [sum_add_distrib, ← mul_sum]; simp [τ]; ring

/-- P0082 page367 display30 and the indicated cognate kernel argument.
Subtracting one from the phase frequency extracts the lower adjacent odd coefficient. -/
theorem odd_lower_moment_transfer (P X Δ : ℝ) (hP : 2 ≤ P) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (s : Finset ℕ) (v : ℕ → ℝ)
    (hodd : ∀ n ∈ s, Odd ⌊v n⌋) :
    (∑ n ∈ s, ‖R1 P X ⌊v n⌋‖ ^ 2) ≤
      (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ,
        OddTail467.integrand P X Δ (v n - 1) α‖ ^ 2) +
      (((s.filter (fun n => Int.fract (v n) < Δ / 2 ∨
        1 - Δ / 2 < Int.fract (v n))).card : ℝ) *
          (Real.log 4 * X * Real.log X) ^ 2) := by
  simpa only [Int.floor_sub_one, sub_add_cancel, Int.fract_sub_one] using
    odd_upper_moment_transfer P X Δ hP hX hΔ hΔ1 s (fun n => v n - 1)
      (fun n hn => by simpa only [Int.floor_sub_one, sub_add_cancel] using hodd n hn)


/-- P0082 page368 display35. The upper adjacent moment reduces to the
truncated shifted moment, an explicit tail mass and a fractional boundary mass. -/
theorem odd_upper_truncated_moment (P X Δ T : ℝ) (hP : 2 ≤ P) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hT : 4 ≤ T) (s : Finset ℕ) (v : ℕ → ℝ)
    (hodd : ∀ n ∈ s, Odd (⌊v n⌋ + 1)) :
    (∑ n ∈ s, ‖R1 P X (⌊v n⌋ + 1)‖ ^ 2) ≤
      2 * (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ ∩ Set.Icc (-T) T,
        OddTail467.integrand P X Δ (v n) α‖ ^ 2) +
      2 * (s.card : ℝ) *
        (8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T)) ^ 2 +
      (((s.filter (fun n => Int.fract (v n) < Δ / 2 ∨
        1 - Δ / 2 < Int.fract (v n))).card : ℝ) *
          (Real.log 4 * X * Real.log X) ^ 2) := by
  have hu := odd_upper_moment_transfer P X Δ hP hX hΔ hΔ1 s v hodd
  have ht := shifted_truncation_moment P X Δ T hX hΔ hΔ1 hT s v
  linarith only [hu, ht]


/-- P0082 page367 display30 and page368 display35, the lower adjacent case.
Only the phase frequency changes in the same boundary and tail transfer. -/
theorem odd_lower_truncated_moment (P X Δ T : ℝ) (hP : 2 ≤ P) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hT : 4 ≤ T) (s : Finset ℕ) (v : ℕ → ℝ)
    (hodd : ∀ n ∈ s, Odd ⌊v n⌋) :
    (∑ n ∈ s, ‖R1 P X ⌊v n⌋‖ ^ 2) ≤
      2 * (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ ∩ Set.Icc (-T) T,
        OddTail467.integrand P X Δ (v n - 1) α‖ ^ 2) +
      2 * (s.card : ℝ) *
        (8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T)) ^ 2 +
      (((s.filter (fun n => Int.fract (v n) < Δ / 2 ∨
        1 - Δ / 2 < Int.fract (v n))).card : ℝ) *
          (Real.log 4 * X * Real.log X) ^ 2) := by
  simpa only [Int.floor_sub_one, sub_add_cancel, Int.fract_sub_one] using
    odd_upper_truncated_moment P X Δ T hP hX hΔ hΔ1 hT s (fun n => v n - 1)
      (fun n hn => by simpa only [Int.floor_sub_one, sub_add_cancel] using hodd n hn)

end LeanLab.ExceptionalSet.Decomp483a


namespace LeanLab.ExceptionalSet.Decomp483c
open Real Finset MeasureTheory ComplexConjugate
open LeanLab.ExceptionalSet.U1539 (Sp eC)

/-- P0082 page369 display37, derived absolute form. The shifted finite moment
is bounded by the explicit phase weighted Gram integral. Its integrability is included. -/
theorem shifted_moment_gram_bound (P X Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (s : Finset ℕ) (v : ℕ → ℝ) (A : Set ℝ) :
    let G := fun α : ℝ => Sp P X α ^ 2 * OddKernel467.evenKernel Δ α
    Integrable (fun z : ℝ × ℝ => ‖G z.1‖ * ‖G z.2‖ *
      ‖∑ n ∈ s, eC ((z.2 - z.1) * v n)‖)
      ((volume.restrict A).prod (volume.restrict A)) ∧
    (∑ n ∈ s, ‖∫ α in A, OddTail467.integrand P X Δ (v n) α‖ ^ 2) ≤
      ∫ z : ℝ × ℝ, ‖G z.1‖ * ‖G z.2‖ *
        ‖∑ n ∈ s, eC ((z.2 - z.1) * v n)‖
        ∂(volume.restrict A).prod (volume.restrict A) := by
  dsimp only
  let G := fun α : ℝ => Sp P X α ^ 2 * OddKernel467.evenKernel Δ α
  let f := fun n α => G α * eC (-(α * v n))
  have hf (n : ℕ) (_ : n ∈ s) : IntegrableOn (f n) A :=
    (OddTail467.total_integrable P X Δ (v n) hΔ hΔ1).integrableOn
  have hconj (t : ℝ) : conj (eC t) = eC (-t) := BG2026.conj_eC t
  have hpoint (α β : ℝ) :
      (∑ n ∈ s, f n α * conj (f n β)) =
        G α * conj (G β) * ∑ n ∈ s, eC ((β - α) * v n) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    dsimp only [f]
    rw [map_mul, hconj]
    rw [show G α * eC (-(α * v n)) * (conj (G β) * eC (-(-(β * v n)))) =
      (G α * conj (G β)) * (eC (-(α * v n)) * eC (-(-(β * v n)))) by ring,
      ← Fejer467.phase_add]
    congr 2
    ring
  have habs (z : ℝ × ℝ) :
      ‖∑ n ∈ s, f n z.1 * conj (f n z.2)‖ =
        ‖G z.1‖ * ‖G z.2‖ * ‖∑ n ∈ s, eC ((z.2 - z.1) * v n)‖ := by
    rw [hpoint]
    simp only [norm_mul, Complex.norm_conj]
  have hfc (n : ℕ) (hn : n ∈ s) :
      IntegrableOn (fun α => conj (f n α)) A := by
    have hc := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (hf n hn)
    exact hc.congr (Filter.Eventually.of_forall (fun α => Complex.conjCLE_apply (f n α)))
  have hi : Integrable (fun z : ℝ × ℝ => ∑ n ∈ s, f n z.1 * conj (f n z.2))
      ((volume.restrict A).prod (volume.restrict A)) :=
    integrable_finsetSum s (fun n hn => (hf n hn).mul_prod (hfc n hn))
  refine ⟨hi.norm.congr (Filter.Eventually.of_forall habs), ?_⟩
  calc _ ≤ ∫ z : ℝ × ℝ, ‖∑ n ∈ s, f n z.1 * conj (f n z.2)‖
      ∂(volume.restrict A).prod (volume.restrict A) :=
        UpJ200.Moment385.moment_le_absolute_gram s A f hf
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall habs)

/-- P0082 page369 display38, auxiliary negative result about the existing
coarse weighted energy supply. Its inverse Delta loss cancels the entire
small phase saving at the printed width. This does not refute the paper estimate. -/
theorem coarse_energy_no_saving (E : ℝ) (hE : 1 < E) :
    E ^ (-(2 / 3 : ℝ)) / (E ^ (-(1 / 3 : ℝ))) ^ 2 = 1 ∧
      E ^ (-(1 / 3 : ℝ)) < E ^ (-(2 / 3 : ℝ)) / (E ^ (-(1 / 3 : ℝ))) ^ 2 := by
  have hE0 : 0 < E := zero_lt_one.trans hE
  have heq : E ^ (-(2 / 3 : ℝ)) / (E ^ (-(1 / 3 : ℝ))) ^ 2 = 1 := by
    rw [← Real.rpow_mul_natCast hE0.le, ← Real.rpow_sub hE0]
    norm_num
  refine ⟨heq, ?_⟩
  rw [heq]
  exact Real.rpow_lt_one_of_one_lt_of_neg hE (by norm_num)

end LeanLab.ExceptionalSet.Decomp483c

namespace LeanLab.ExceptionalSet.Decomp483d
open Real MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (Sp)

/-- P0082 page365 before display24 and page369 display38. A symmetric
integer interval contains twice its radius many periods of prime energy. -/
theorem prime_energy_symmetric_nat (P X : ℝ) (hX : 2 ≤ X) (K : ℕ) :
    (∫ α in (-(K : ℝ))..(K : ℝ), ‖Sp P X α‖ ^ 2) ≤
      2 * K * (Real.log 4 * X * Real.log X) := by
  have hc : Continuous (fun α => ‖Sp P X α‖ ^ 2) := by unfold Sp U1539.eC; fun_prop
  have hp : Function.Periodic (fun α => ‖Sp P X α‖ ^ 2) 1 := by
    intro α
    dsimp only
    rw [Decomp371a.Sp_periodic P X α]
  have he := hp.intervalIntegral_add_zsmul_eq (2 * (K : ℤ)) (-(K : ℝ))
    (fun a b => hc.intervalIntegrable a b)
  have hend : -(K : ℝ) + (2 * (K : ℤ)) • (1 : ℝ) = (K : ℝ) := by
    simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    ring
  rw [hend] at he
  calc _ = (2 * (K : ℤ)) • (∫ α in (-(K : ℝ))..(-(K : ℝ)) + 1, ‖Sp P X α‖ ^ 2) := he
    _ = 2 * (K : ℝ) * (∫ α in (-(K : ℝ))..(-(K : ℝ)) + 1, ‖Sp P X α‖ ^ 2) := by
      simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left (UpJ200.PrimeEnergy385.prime_energy_le P X (-(K : ℝ)) hX)
      (by positivity)

/-- P0082 page369 display38, auxiliary explicit cutoff bound. The compact
part uses the shifted kernel bound one. The two tails use OddTail467. -/
theorem shifted_weighted_mass_cutoff (P X Δ : ℝ) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (K : ℕ) (hK : 2 ≤ K) :
    (∫ α : ℝ, ‖Sp P X α ^ 2 * OddKernel467.evenKernel Δ α‖) ≤
      2 * K * (Real.log 4 * X * Real.log X) +
      4 * (Real.log 4 * X * Real.log X) /
        (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) := by
  let A := Real.log 4 * X * Real.log X
  let g := fun α : ℝ => ‖Sp P X α ^ 2 * OddKernel467.evenKernel Δ α‖
  have hg : Integrable g := by
    simpa only [g, OddTail467.integrand, norm_mul, U1539.norm_eC, mul_one] using
      (OddTail467.total_integrable P X Δ 0 hΔ hΔ1).norm
  have hc : Continuous (fun α : ℝ => ‖Sp P X α‖ ^ 2) := by unfold Sp U1539.eC; fun_prop
  have hgc : Continuous g := by
    exact (((by unfold Sp U1539.eC; fun_prop : Continuous (Sp P X)).pow 2).mul
      (OddKernel467.evenKernel_continuous Δ)).norm
  have hk (α : ℝ) : ‖OddKernel467.evenKernel Δ α‖ ≤ 1 := by
    rw [OddTail467.norm_evenKernel]
    have h := KernelTail385.kernel_abs_le_two_sub Δ ((1 / 2) * α) hΔ hΔ1
    linarith
  have hab : -(K : ℝ) ≤ (K : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) K]
  have hcenter : (∫ α in Icc (-(K : ℝ)) (K : ℝ), g α) ≤ 2 * K * A := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    calc
      _ ≤ ∫ α in (-(K : ℝ))..(K : ℝ), ‖Sp P X α‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on hab (hgc.intervalIntegrable _ _)
          (hc.intervalIntegrable _ _)
        intro α hα
        dsimp only [g]
        rw [norm_mul, norm_pow]
        exact mul_le_of_le_one_right (sq_nonneg _) (hk α)
      _ ≤ _ := prime_energy_symmetric_nat P X hX K
  have htail : (∫ α in (Icc (-(K : ℝ)) (K : ℝ))ᶜ, g α) ≤
      4 * A / (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) := by
    simpa only [g, A, OddTail467.integrand, norm_mul, U1539.norm_eC, mul_one] using
      OddTail467.outside_nat_tail_le P X Δ 0 hX hΔ hΔ1 K hK
  have hs := integral_add_compl (μ := volume) (s := Icc (-(K : ℝ)) (K : ℝ))
    measurableSet_Icc hg
  change (∫ α, g α) ≤ _
  rw [← hs]
  exact add_le_add hcenter htail

/-- P0082 page369 display38, derived weaker weighted mass bound. Choosing
an integer cutoff near one over square root Delta improves the old inverse Delta loss. -/
theorem shifted_weighted_mass_sqrt (P X Δ : ℝ) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (∫ α : ℝ, ‖Sp P X α ^ 2 * OddKernel467.evenKernel Δ α‖) ≤
      7 * (Real.log 4 * X * Real.log X) / Real.sqrt Δ := by
  let d := Real.sqrt Δ
  let A := Real.log 4 * X * Real.log X
  let K : ℕ := ⌈1 / d⌉₊ + 1
  have hd : 0 < d := Real.sqrt_pos.mpr hΔ
  have hd1 : d ≤ 1 := Real.sqrt_le_one.mpr hΔ1.le
  have hsq : d ^ 2 = Δ := Real.sq_sqrt hΔ.le
  have ht0 : 0 < 1 / d := by positivity
  have ht1 : 1 ≤ 1 / d := (one_le_div hd).mpr hd1
  have hceil : 1 ≤ ⌈1 / d⌉₊ := Nat.one_le_ceil_iff.mpr ht0
  have hK : 2 ≤ K := by dsimp only [K]; omega
  have hKu : (K : ℝ) ≤ 3 / d := by
    have h := (Nat.ceil_lt_add_one ht0.le).le
    dsimp only [K]
    push_cast
    rw [show 3 / d = 3 * (1 / d) by ring]
    linarith only [h, ht1]
  have hKl : 1 / d ≤ (K : ℝ) - 1 := by
    have h := Nat.le_ceil (1 / d)
    dsimp only [K]
    push_cast
    linarith
  have hA : 0 ≤ A := by
    dsimp only [A]
    have hL : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
    positivity
  have hprod : d ≤ Δ * ((K : ℝ) - 1) := by
    calc d = Δ * (1 / d) := by rw [← hsq]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hKl hΔ.le
  have hpi : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hden : 4 * d ≤ Δ * Real.pi ^ 2 * ((K : ℝ) - 1) := by
    calc _ ≤ Real.pi ^ 2 * d := mul_le_mul_of_nonneg_right hpi hd.le
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_left hprod (sq_nonneg Real.pi) using 1; ring
  have hden0 : 0 < Δ * Real.pi ^ 2 * ((K : ℝ) - 1) := (by positivity : 0 < 4 * d).trans_le hden
  have htail : 4 * A / (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) ≤ A / d := by
    apply (div_le_div_iff₀ hden0 hd).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hden hA]
  have hcenter : 2 * K * A ≤ 6 * A / d := by
    calc _ ≤ 2 * (3 / d) * A := by gcongr
      _ = _ := by ring
  calc _ ≤ 2 * K * A + 4 * A / (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) :=
      shifted_weighted_mass_cutoff P X Δ hX hΔ hΔ1 K hK
    _ ≤ 6 * A / d + A / d := add_le_add hcenter htail
    _ = _ := by dsimp only [A, d]; ring

end LeanLab.ExceptionalSet.Decomp483d

namespace LeanLab.ExceptionalSet.UpJ200.Decomp539a
open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (Sp eC nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- P0082 page368 display36 and page369 odd parity counterpart. -/
noncomputable def parityPhase (γ : ℝ) (N : ℕ) (j : ℤ) (t : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + j)), eC (t * (F γ n - j))

/-- P0082 page370 display41, exact parity filter before smoothing. -/
theorem parity_filter_expansion (s : Finset ℕ) (v : ℕ → ℤ) (f : ℕ → ℂ) :
    (∑ n ∈ s.filter (fun n => Even (v n)), f n) =
      (1 / 2 : ℂ) * ((∑ n ∈ s, f n) + ∑ n ∈ s, (-1 : ℂ) ^ (v n) * f n) := by
  classical
  rw [Finset.sum_filter, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [neg_one_zpow_eq_ite]
  split_ifs <;> ring

/-- P0082 page369 display37. The common integer shift has unit norm. -/
theorem parityPhase_shift (γ : ℝ) (N : ℕ) (j : ℤ) (t : ℝ) :
    ‖parityPhase γ N j t‖ =
      ‖∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + j)), eC (t * F γ n)‖ := by
  have he (n : ℕ) : eC (t * (F γ n - j)) = eC (-(t * j)) * eC (t * F γ n) := by
    rw [← Fejer467.phase_add]
    congr 1
    ring
  simp only [parityPhase, he, ← Finset.mul_sum, norm_mul, U1539.norm_eC, one_mul]

/-- P0082 page369 before display39, the trivial finite phase bound. -/
theorem parityPhase_le (γ : ℝ) (N : ℕ) (j : ℤ) (t : ℝ) : ‖parityPhase γ N j t‖ ≤ N := by
  unfold parityPhase
  calc
    _ ≤ ∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + j)),
        ‖eC (t * (F γ n - j))‖ := norm_sum_le _ _
    _ = (((Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + j))).card : ℝ) := by simp [U1539.norm_eC]
    _ ≤ N := by
      exact_mod_cast (Finset.card_filter_le _ _).trans
        (by rw [Nat.card_Ioc]; omega : (Finset.Ioc (N / 2) N).card ≤ N)

/-- P0082 page369 display38, the nonnegative prime kernel mass. -/
noncomputable def mass (P X Δ : ℝ) (α : ℝ) : ℝ :=
  ‖Sp P X α ^ 2 * OddKernel467.evenKernel Δ α‖

/-- P0082 page369 display38, integrability before splitting pairs. -/
theorem mass_integrable (P X Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) : Integrable (mass P X Δ) := by
  change Integrable (fun α => ‖Sp P X α ^ 2 * OddKernel467.evenKernel Δ α‖)
  simpa only [ OddTail467.integrand, norm_mul, U1539.norm_eC, mul_one] using
    (OddTail467.total_integrable P X Δ 0 hΔ hΔ1).norm

/-- P0082 page369 below display37. A bounded phase costs its bound times mass squared. -/
theorem small_phase_integral (g : ℝ → ℝ) (H : ℝ × ℝ → ℝ)
    (hg : Integrable g) (hg0 : ∀ x, 0 ≤ g x) (V : ℝ) (hV : 0 ≤ V)
    (hH0 : ∀ z, 0 ≤ H z) (S : Set (ℝ × ℝ)) (hH : ∀ z ∈ S, H z ≤ V) :
    (∫ z in S, g z.1 * g z.2 * H z) ≤ V * (∫ x, g x) ^ 2 := by
  calc
    _ ≤ ∫ z in S, V * (g z.1 * g z.2) := by
      apply setIntegral_mono_of_nonneg
      · intro z hz
        exact mul_nonneg (mul_nonneg (hg0 _) (hg0 _)) (hH0 z)
      · intro z hz
        nlinarith only [mul_le_mul_of_nonneg_left (hH z hz) (mul_nonneg (hg0 z.1) (hg0 z.2))]
      · exact ((hg.mul_prod hg).const_mul V).integrableOn
    _ ≤ ∫ z : ℝ × ℝ, V * (g z.1 * g z.2) :=
      setIntegral_le_integral ((hg.mul_prod hg).const_mul V)
        (Filter.Eventually.of_forall (fun z => mul_nonneg hV (mul_nonneg (hg0 _) (hg0 _))))
    _ = _ := by
      rw [integral_const_mul]
      change V * (∫ z : ℝ × ℝ, g z.1 * g z.2 ∂volume.prod volume) = _
      rw [integral_prod_mul]
      ring

end LeanLab.ExceptionalSet.UpJ200.Decomp539a

namespace LeanLab.ExceptionalSet.UpJ200.Decomp539a
open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (Sp eC nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- P0082 page369 displays37 and38, the requested small phase margin. -/
theorem small_phase_budget (E A M : ℝ) (N : ℕ) (hE : 1 ≤ E) (hA : 0 ≤ A)
    (hM : 0 ≤ M) (hbound : M ≤ 7 * A / Real.sqrt (E ^ (-(5 / 12 : ℝ)))) :
    N * E ^ (-(5 / 6 : ℝ)) * M ^ 2 ≤ 49 * N * A ^ 2 * E ^ (-(5 / 12 : ℝ)) := by
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have hs : (Real.sqrt (E ^ (-(5 / 12 : ℝ)))) ^ 2 = E ^ (-(5 / 12 : ℝ)) :=
    Real.sq_sqrt (Real.rpow_nonneg hE0.le _)
  have he : E ^ (-(5 / 6 : ℝ)) / E ^ (-(5 / 12 : ℝ)) = E ^ (-(5 / 12 : ℝ)) := by
    rw [← Real.rpow_sub hE0]
    norm_num
  calc
    _ ≤ N * E ^ (-(5 / 6 : ℝ)) * (7 * A / Real.sqrt (E ^ (-(5 / 12 : ℝ)))) ^ 2 := by
      gcongr
    _ = 49 * N * A ^ 2 * E ^ (-(5 / 12 : ℝ)) := by
      rw [div_pow, hs]
      calc
        _ = 49 * N * A ^ 2 * (E ^ (-(5 / 6 : ℝ)) / E ^ (-(5 / 12 : ℝ))) := by ring
        _ = _ := by rw [he]

/-- P0082 page369 display38, logarithmic absorption at the free width. -/
theorem small_phase_log_budget (E X : ℝ) (N : ℕ) (hE : 1 ≤ E)
    (hlog : Real.log X ^ 2 ≤ E ^ (1 / 12 : ℝ)) :
    49 * N * (Real.log 4 * X * Real.log X) ^ 2 * E ^ (-(5 / 12 : ℝ)) ≤
      (49 * Real.log 4 ^ 2) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have hh : Real.log X ^ 2 * E ^ (-(5 / 12 : ℝ)) ≤ E ^ (-(1 / 3 : ℝ)) := by
    calc
      _ ≤ E ^ (1 / 12 : ℝ) * E ^ (-(5 / 12 : ℝ)) :=
        mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hE0.le _)
      _ = _ := by rw [← Real.rpow_add hE0]; norm_num
  calc
    _ = (49 * Real.log 4 ^ 2) * N * X ^ 2 * (Real.log X ^ 2 * E ^ (-(5 / 12 : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)

/-- P0082 page369 display39, the phase window bounds the half integer index. -/
theorem half_integer_height (E t r : ℝ) (h : ℤ) (hr : r ≤ 1)
    (ht : |t| ≤ 2 * E ^ (2 / 3 : ℝ)) (hgap : |t - h / 2| ≤ r)
    (hmargin : 4 * E ^ (2 / 3 : ℝ) + 2 ≤ E ^ (3 / 4 : ℝ)) :
    (|h| : ℝ) ≤ E ^ (3 / 4 : ℝ) := by
  have hab : |(h : ℝ) / 2| ≤ |t| + |t - (h : ℝ) / 2| := by
    calc
      _ = |t - (t - (h : ℝ) / 2)| := by congr 1; ring
      _ ≤ _ := abs_sub t (t - (h : ℝ) / 2)
  have hh : |(h : ℝ)| = 2 * |(h : ℝ) / 2| := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
  rw [hh]
  linarith

/-- P0082 page369 display39, a finite family of strips has total length at most
its cardinality times twice its radius, regardless of overlap. -/
theorem strip_volume (s : Finset ℤ) (a r : ℝ) (hr : 0 ≤ r) :
    volume.real (⋃ h ∈ s, Set.Icc (a + h / 2 - r) (a + h / 2 + r)) ≤
      (s.card : ℝ) * (2 * r) := by
  calc
    _ ≤ ∑ h ∈ s, volume.real (Set.Icc (a + h / 2 - r) (a + h / 2 + r)) :=
      measureReal_biUnion_finset_le _ _
    _ = _ := by
      simp only [Real.volume_real_Icc]
      have hlen (h : ℤ) : max (a + h / 2 + r - (a + h / 2 - r)) 0 = 2 * r := by
        rw [show a + h / 2 + r - (a + h / 2 - r) = 2 * r by ring, max_eq_left (by linarith)]
      simp only [hlen, Finset.sum_const, nsmul_eq_mul]

end LeanLab.ExceptionalSet.UpJ200.Decomp539a

namespace LeanLab.ExceptionalSet.UpJ200.Decomp539a
open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (Sp eC nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- P0082 page369 display37, exact measurable large and small phase split. -/
theorem phase_pair_split (A : Set ℝ) (g : ℝ × ℝ → ℝ) (H : ℝ × ℝ → ℝ)
    (hH : Continuous H) (V : ℝ)
    (hg : Integrable g ((volume.restrict A).prod (volume.restrict A))) :
    (∫ z : ℝ × ℝ, g z ∂(volume.restrict A).prod (volume.restrict A)) =
      (∫ a in A, ∫ b in A ∩ {b | H (a, b) ≤ V}, g (a, b)) +
      (∫ a in A, ∫ b in A ∩ {b | V < H (a, b)}, g (a, b)) := by
  let D : Set (ℝ × ℝ) := {z | H z ≤ V}
  have hD : MeasurableSet D := measurableSet_le hH.measurable measurable_const
  have hd := hg.indicator hD
  have hn := hg.indicator hD.compl
  have he : g = (fun z => D.indicator g z + Dᶜ.indicator g z) := by
    ext z
    by_cases hz : z ∈ D <;> simp [hz]
  conv_lhs => rw [he]
  rw [integral_add hd hn, integral_prod _ hd, integral_prod _ hn]
  congr 1
  · apply integral_congr_ae
    filter_upwards with a
    have hs : MeasurableSet {b : ℝ | H (a, b) ≤ V} :=
      measurableSet_le (hH.comp (continuous_const.prodMk continuous_id)).measurable measurable_const
    have hf : (fun b => D.indicator g (a, b)) =
        ({b | H (a, b) ≤ V}).indicator (fun b => g (a, b)) := by ext b; rfl
    rw [hf, setIntegral_indicator hs]
  · apply integral_congr_ae
    filter_upwards with a
    have hs : MeasurableSet {b : ℝ | V < H (a, b)} :=
      measurableSet_lt measurable_const (hH.comp (continuous_const.prodMk continuous_id)).measurable
    have hf : (fun b => Dᶜ.indicator g (a, b)) =
        ({b | V < H (a, b)}).indicator (fun b => g (a, b)) := by
      ext b
      simp only [D, Set.indicator_apply, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    rw [hf, setIntegral_indicator hs]

/-- P0082 page369 below display37, the small phase contribution on any window. -/
theorem small_phase_part (A : Set ℝ) (g : ℝ → ℝ) (H : ℝ × ℝ → ℝ)
    (hg : IntegrableOn g A) (hg0 : ∀ x, 0 ≤ g x) (hH0 : ∀ z, 0 ≤ H z)
    (V : ℝ) (hV : 0 ≤ V) :
    (∫ a in A, ∫ b in A ∩ {b | H (a, b) ≤ V}, g a * g b * H (a, b)) ≤
      V * (∫ a in A, g a) ^ 2 := by
  have hi (a : ℝ) :
      (∫ b in A ∩ {b | H (a, b) ≤ V}, g a * g b * H (a, b)) ≤
        g a * V * (∫ b in A, g b) := by
    calc
      _ ≤ ∫ b in A ∩ {b | H (a, b) ≤ V}, g a * V * g b := by
        apply setIntegral_mono_of_nonneg
        · intro b hb
          exact mul_nonneg (mul_nonneg (hg0 _) (hg0 _)) (hH0 _)
        · intro b hb
          nlinarith only [mul_le_mul_of_nonneg_left hb.2 (mul_nonneg (hg0 a) (hg0 b))]
        · exact (hg.mono_set inter_subset_left).const_mul _
      _ ≤ ∫ b in A, g a * V * g b :=
        setIntegral_mono_set (hg.const_mul _)
          (Filter.Eventually.of_forall (fun b => mul_nonneg (mul_nonneg (hg0 a) hV) (hg0 b)))
          inter_subset_left.eventuallySubset
      _ = _ := integral_const_mul _ _
  calc
    _ ≤ ∫ a in A, g a * V * (∫ b in A, g b) := by
      apply setIntegral_mono_of_nonneg
      · intro a ha
        exact integral_nonneg (fun b => mul_nonneg (mul_nonneg (hg0 _) (hg0 _)) (hH0 _))
      · intro a ha
        exact hi a
      · exact (hg.mul_const V).mul_const _
    _ = _ := by rw [integral_mul_const, integral_mul_const]; ring

/-- P0082 page369 display39. The large phase contribution reduces to an inner
weighted prime mass on the localized set. -/
theorem large_phase_part (A : Set ℝ) (g : ℝ → ℝ) (H : ℝ × ℝ → ℝ)
    (hg : IntegrableOn g A) (hg0 : ∀ x, 0 ≤ g x) (hH0 : ∀ z, 0 ≤ H z)
    (V T Q : ℝ) (hT : 0 ≤ T)
    (hH : ∀ a ∈ A, ∀ b ∈ A, H (a, b) ≤ T)
    (hinner : ∀ a ∈ A, (∫ b in A ∩ {b | V < H (a, b)}, g b) ≤ Q) :
    (∫ a in A, ∫ b in A ∩ {b | V < H (a, b)}, g a * g b * H (a, b)) ≤
      T * Q * (∫ a in A, g a) := by
  have hi (a : ℝ) (ha : a ∈ A) :
      (∫ b in A ∩ {b | V < H (a, b)}, g a * g b * H (a, b)) ≤ g a * T * Q := by
    calc
      _ ≤ ∫ b in A ∩ {b | V < H (a, b)}, g a * T * g b := by
        apply setIntegral_mono_of_nonneg
        · intro b hb
          exact mul_nonneg (mul_nonneg (hg0 _) (hg0 _)) (hH0 _)
        · intro b hb
          nlinarith only [mul_le_mul_of_nonneg_left (hH a ha b hb.1)
            (mul_nonneg (hg0 a) (hg0 b))]
        · exact (hg.mono_set inter_subset_left).const_mul _
      _ = g a * T * (∫ b in A ∩ {b | V < H (a, b)}, g b) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hinner a ha) (mul_nonneg (hg0 a) hT)
  calc
    _ ≤ ∫ a in A, g a * T * Q := by
      apply setIntegral_mono_of_nonneg
      · intro a ha
        exact integral_nonneg (fun b => mul_nonneg (mul_nonneg (hg0 _) (hg0 _)) (hH0 _))
      · exact hi
      · exact (hg.mul_const T).mul_const Q
    _ = _ := by rw [integral_mul_const, integral_mul_const]; ring

end LeanLab.ExceptionalSet.UpJ200.Decomp539a

namespace LeanLab.ExceptionalSet.UpJ200.Decomp539a
open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (Sp eC nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- P0082 page369 display39, finite strip mass from a pointwise prime bound. -/
theorem strip_mass_bound (s : Finset ℤ) (a r B : ℝ) (hr : 0 ≤ r) (hB : 0 ≤ B)
    (A S : Set ℝ) (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x)
    (hgb : ∀ x ∈ A, g x ≤ B) (hSA : S ⊆ A)
    (hS : S ⊆ ⋃ h ∈ s, Set.Icc (a + h / 2 - r) (a + h / 2 + r)) :
    (∫ x in S, g x) ≤ B * (s.card : ℝ) * (2 * r) := by
  let U := ⋃ h ∈ s, Set.Icc (a + h / 2 - r) (a + h / 2 + r)
  have hfin : volume U ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (measure_biUnion_finset_le _ _)
      (ENNReal.sum_lt_top.mpr (fun h hh => by simp [Real.volume_Icc]))
  have hSfin : volume S < ⊤ := (measure_mono hS).trans_lt (lt_top_iff_ne_top.mpr hfin)
  have hn : ‖∫ x in S, g x‖ ≤ B * volume.real S :=
    norm_setIntegral_le_of_norm_le_const hSfin
      (fun x hx => by rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact hgb x (hSA hx))
  calc
    _ ≤ B * volume.real S := (le_norm_self _).trans hn
    _ ≤ B * volume.real U := mul_le_mul_of_nonneg_left (measureReal_mono hS hfin) hB
    _ ≤ B * ((s.card : ℝ) * (2 * r)) := mul_le_mul_of_nonneg_left (strip_volume s a r hr) hB
    _ = _ := by ring

/-- P0082 page369 displays37 to39. The localized inner mass gives the full Gram bound. -/
theorem localized_gram_bound (A : Set ℝ) (g : ℝ → ℝ) (H : ℝ × ℝ → ℝ)
    (hg : IntegrableOn g A) (hg0 : ∀ x, 0 ≤ g x) (hH0 : ∀ z, 0 ≤ H z)
    (hHc : Continuous H) (V T Q : ℝ) (hV : 0 ≤ V) (hT : 0 ≤ T)
    (hHi : Integrable (fun z : ℝ × ℝ => g z.1 * g z.2 * H z)
      ((volume.restrict A).prod (volume.restrict A)))
    (hH : ∀ a ∈ A, ∀ b ∈ A, H (a, b) ≤ T)
    (hinner : ∀ a ∈ A, (∫ b in A ∩ {b | V < H (a, b)}, g b) ≤ Q) :
    (∫ z : ℝ × ℝ, g z.1 * g z.2 * H z ∂(volume.restrict A).prod (volume.restrict A)) ≤
      V * (∫ a in A, g a) ^ 2 + T * Q * (∫ a in A, g a) := by
  rw [phase_pair_split A _ H hHc V hHi]
  exact add_le_add (small_phase_part A g H hg hg0 hH0 V hV)
    (large_phase_part A g H hg hg0 hH0 V T Q hT hH hinner)

end LeanLab.ExceptionalSet.UpJ200.Decomp539a

namespace LeanLab.ExceptionalSet.UpJ200.Decomp539a
open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (Sp eC nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- P0082 page369 display39, finite half integer index range. -/
noncomputable def stripIndices (E : ℝ) : Finset ℤ :=
  Finset.Icc (-⌊E ^ (3 / 4 : ℝ)⌋) ⌊E ^ (3 / 4 : ℝ)⌋

/-- P0082 page369 display39, exact containment in the finite index range. -/
theorem mem_stripIndices (E : ℝ) (h : ℤ) (hh : (|h| : ℝ) ≤ E ^ (3 / 4 : ℝ)) :
    h ∈ stripIndices E := by
  have hp : (h : ℝ) ≤ E ^ (3 / 4 : ℝ) := (le_abs_self _).trans hh
  have hn : ((-h : ℤ) : ℝ) ≤ E ^ (3 / 4 : ℝ) := by
    push_cast
    exact (neg_le_abs _).trans hh
  simp only [stripIndices, Finset.mem_Icc]
  exact ⟨by have := Int.le_floor.mpr hn; omega, Int.le_floor.mpr hp⟩

/-- P0082 page369 display39, three times the cutoff bounds its integer count. -/
theorem stripIndices_card (E : ℝ) (hE : 1 ≤ E) :
    ((stripIndices E).card : ℝ) ≤ 3 * E ^ (3 / 4 : ℝ) := by
  have hH : 1 ≤ E ^ (3 / 4 : ℝ) := Real.one_le_rpow hE (by norm_num)
  have hf : 1 ≤ ⌊E ^ (3 / 4 : ℝ)⌋ := Int.le_floor.mpr (by exact_mod_cast hH)
  have hc := Int.card_Icc_of_le _ _ (show -⌊E ^ (3 / 4 : ℝ)⌋ ≤ ⌊E ^ (3 / 4 : ℝ)⌋ + 1 by omega)
  have hcr : ((stripIndices E).card : ℝ) = 2 * (⌊E ^ (3 / 4 : ℝ)⌋ : ℝ) + 1 := by
    dsimp only [stripIndices]
    have hci : ((stripIndices E).card : ℤ) = 2 * ⌊E ^ (3 / 4 : ℝ)⌋ + 1 := by
      dsimp only [stripIndices]
      omega
    exact_mod_cast hci
  rw [hcr]
  linarith [Int.floor_le (E ^ (3 / 4 : ℝ))]

/-- P0082 page369 display38, the shifted kernel has norm at most one. -/
theorem mass_le_prime_square (P X Δ a : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    mass P X Δ a ≤ ‖Sp P X a‖ ^ 2 := by
  have hk := KernelTail385.kernel_abs_le_two_sub Δ ((1 / 2) * a) hΔ hΔ1
  have hn : ‖OddKernel467.evenKernel Δ a‖ ≤ 1 := by rw [OddTail467.norm_evenKernel]; linarith
  dsimp only [mass]
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (sq_nonneg _) hn

/-- P0082 page369 display39, scalar absorption of finite strip losses. -/
theorem strip_prime_budget (E X C δ : ℝ) (hE : 1 ≤ E) (hX : 0 < X) (hC : 0 ≤ C)
    (hlog : Real.log X ^ 2 ≤ E ^ (1 / 12 : ℝ)) (hscale : E ^ (7 / 4 : ℝ) ≤ X ^ (5 * δ)) :
    (C * X ^ (2 - 6 * δ) * Real.log X ^ 8) * (3 * E ^ (3 / 4 : ℝ)) *
      (2 * X ^ (δ - 1)) ≤ 6 * C * X * E ^ (-(2 / 3 : ℝ)) := by
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have hl : Real.log X ^ 8 ≤ E ^ (1 / 3 : ℝ) := by
    have hh := pow_le_pow_left₀ (sq_nonneg (Real.log X)) hlog 4
    rw [← pow_mul, ← Real.rpow_mul_natCast hE0.le] at hh
    norm_num at hh ⊢
    exact hh
  have hs : E ^ (13 / 12 : ℝ) ≤ X ^ (5 * δ) * E ^ (-(2 / 3 : ℝ)) := by
    calc
      _ = E ^ (7 / 4 : ℝ) * E ^ (-(2 / 3 : ℝ)) := by rw [← Real.rpow_add hE0]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hE0.le _)
  calc
    _ ≤ (C * X ^ (2 - 6 * δ) * E ^ (1 / 3 : ℝ)) * (3 * E ^ (3 / 4 : ℝ)) *
        (2 * X ^ (δ - 1)) := by gcongr
    _ = 6 * C * X ^ (1 - 5 * δ) * E ^ (13 / 12 : ℝ) := by
      have hx : X ^ (2 - 6 * δ) * X ^ (δ - 1) = X ^ (1 - 5 * δ) := by
        rw [← Real.rpow_add hX]; congr 1; ring
      have he : E ^ (1 / 3 : ℝ) * E ^ (3 / 4 : ℝ) = E ^ (13 / 12 : ℝ) := by
        rw [← Real.rpow_add hE0]; norm_num
      calc
        _ = 6 * C * (X ^ (2 - 6 * δ) * X ^ (δ - 1)) *
            (E ^ (1 / 3 : ℝ) * E ^ (3 / 4 : ℝ)) := by ring
        _ = _ := by rw [hx, he]
    _ ≤ 6 * C * X ^ (1 - 5 * δ) * (X ^ (5 * δ) * E ^ (-(2 / 3 : ℝ))) := by gcongr
    _ = _ := by
      have hx : X ^ (1 - 5 * δ) * X ^ (5 * δ) = X := by
        rw [← Real.rpow_add hX]; ring_nf; exact Real.rpow_one X
      calc
        _ = 6 * C * (X ^ (1 - 5 * δ) * X ^ (5 * δ)) * E ^ (-(2 / 3 : ℝ)) := by ring
        _ = _ := by rw [hx]

end LeanLab.ExceptionalSet.UpJ200.Decomp539a

namespace LeanLab.ExceptionalSet.UpJ200.Decomp539a
open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (Sp eC nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- P0082 page368 display35, the truncated minor arc window. -/
noncomputable def oddDomain (P X E : ℝ) : Set ℝ :=
  (majorArcs P X)ᶜ ∩ Set.Icc (-(E ^ (2 / 3 : ℝ))) (E ^ (2 / 3 : ℝ))

/-- P0082 page369 display39, the finite union of localized half integer strips. -/
noncomputable def strips (E X δ a : ℝ) : Set ℝ :=
  ⋃ h ∈ stripIndices E, Set.Icc (a + h / 2 - X ^ (δ - 1)) (a + h / 2 + X ^ (δ - 1))

/-- P0082 page369 display39. The proved minor prime supremum and finite strip
volume bound the weighted inner prime energy. -/
theorem prime_strip_inner (E X C δ : ℝ) (hE : 1 ≤ E) (hX : 0 < X) (hC : 0 ≤ C)
    (hΔ1 : E ^ (-(5 / 12 : ℝ)) < 1)
    (hTX : E ^ (2 / 3 : ℝ) ≤ X ^ (6 * δ))
    (hlog : Real.log X ^ 2 ≤ E ^ (1 / 12 : ℝ)) (hscale : E ^ (7 / 4 : ℝ) ≤ X ^ (5 * δ))
    (hminor : ∀ b ∈ UpJ200.Decomp404e.truncatedDomain (X ^ (6 * δ)) X,
      ‖Sp (X ^ (6 * δ)) X b‖ ^ 2 ≤ C * X ^ (2 - 6 * δ) * Real.log X ^ 8) (a : ℝ)
    (S : Set ℝ) (hSA : S ⊆ oddDomain (X ^ (6 * δ)) X E) (hS : S ⊆ strips E X δ a) :
    (∫ b in S, mass (X ^ (6 * δ)) X (E ^ (-(5 / 12 : ℝ))) b) ≤
      6 * C * X * E ^ (-(2 / 3 : ℝ)) := by
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have hΔ : 0 < E ^ (-(5 / 12 : ℝ)) := Real.rpow_pos_of_pos hE0 _
  have hB : 0 ≤ C * X ^ (2 - 6 * δ) * Real.log X ^ 8 := by positivity
  have hb (b : ℝ) (hb : b ∈ oddDomain (X ^ (6 * δ)) X E) :
      mass (X ^ (6 * δ)) X (E ^ (-(5 / 12 : ℝ))) b ≤
        C * X ^ (2 - 6 * δ) * Real.log X ^ 8 := by
    apply (mass_le_prime_square _ _ _ _ hΔ hΔ1).trans
    apply hminor b
    exact ⟨hb.1, ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩⟩
  have hh := strip_mass_bound (stripIndices E) a (X ^ (δ - 1))
    (C * X ^ (2 - 6 * δ) * Real.log X ^ 8) (Real.rpow_nonneg hX.le _) hB
    (oddDomain (X ^ (6 * δ)) X E) S
    (mass (X ^ (6 * δ)) X (E ^ (-(5 / 12 : ℝ)))) (fun b => norm_nonneg _) hb hSA hS
  calc
    _ ≤ _ := hh
    _ ≤ (C * X ^ (2 - 6 * δ) * Real.log X ^ 8) * (3 * E ^ (3 / 4 : ℝ)) *
        (2 * X ^ (δ - 1)) := by gcongr; exact stripIndices_card E hE
    _ ≤ _ := strip_prime_budget E X C δ hE hX hC hlog hscale

/-- P0082 page368 display36. The zero shift is exactly the printed even phase. -/
theorem parityPhase_zero (γ : ℝ) (N : ℕ) (t : ℝ) :
    parityPhase γ N 0 t = U1539.Phie γ N t := by simp [parityPhase, U1539.Phie]

/-- P0082 page369 cognate odd case. The odd phase is bounded by the full
phase plus the even phase after removing its unit norm shift. -/
theorem odd_phase_complement (γ : ℝ) (N : ℕ) (t : ℝ) :
    ‖parityPhase γ N 1 t‖ ≤ ‖Decomp404e.phaseSum γ N t‖ + ‖U1539.Phie γ N t‖  := by
  classical
  rw [parityPhase_shift]
  have hp (n : ℕ) : Even (nu γ n + 1) ↔ ¬ Even (nu γ n) := by
    simp [Int.not_even_iff_odd]
  have hsign (n : ℕ) : (-1 : ℂ) ^ (nu γ n + 1) = -((-1 : ℂ) ^ (nu γ n)) := by
    simp only [neg_one_zpow_eq_ite, hp]
    by_cases h : Even (nu γ n) <;> simp [h]
  have he := parity_filter_expansion (Finset.Ioc (N / 2) N) (nu γ)
    (fun n => eC (t * F γ n))
  have ho := parity_filter_expansion (Finset.Ioc (N / 2) N) (fun n => nu γ n + 1)
    (fun n => eC (t * F γ n))
  simp_rw [hsign, neg_mul] at ho
  rw [Finset.sum_neg_distrib] at ho
  have hid : (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + 1)), eC (t * F γ n)) =
      Decomp404e.phaseSum γ N t - U1539.Phie γ N t := by
    change _ = (∑ n ∈ Finset.Ioc (N / 2) N, eC (t * F γ n)) -
      (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n)), eC (t * F γ n))
    rw [ho, he]
    ring
  rw [hid]
  exact norm_sub_le _ _

/-- P0082 page368 Lemma9 and page369 cognate odd case. Rescale the printed
even localization and use Theorem2 only for the complementary full phase.
CONDITIONAL ON h9 and the cited Karacuba input h10. -/
theorem parity_gap_of_inputs (h9 : U1539.Lemma9) (h10 : U1539.Lemma10)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ j : ℤ, (j = 0 ∨ j = 1) →
          ∀ t : ℝ, |t| ≤ F γ N ^ δ →
            N * calE γ κ N ^ (-(5 / 6 : ℝ)) < ‖parityPhase γ N j t‖ →
            ∃ h : ℤ, |t - h / 2| ≤ F γ N ^ (δ - 1) := by
  obtain ⟨δe, hδe, he⟩ := h9 γ h1 h2
  obtain ⟨δf, hδf, hf⟩ := Decomp467a.far_phase_of_karacuba h10 γ h1 h2
  refine ⟨min δe (3 * δf), lt_min hδe (by positivity), fun δ hδ hδsmall => ?_⟩
  obtain ⟨κe, hκe, Ne, he⟩ := he δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κf, hκf, hf⟩ := hf (δ / 3) (by positivity)
    (by have := hδsmall.trans_le (min_le_right _ _); linarith)
  refine ⟨min (κe / 5) κf, lt_min (by positivity) hκf, fun κ hκ hκsmall => ?_⟩
  have hκe' : κ ≤ κe / 5 := hκsmall.trans (min_le_left _ _)
  obtain ⟨C, hC, Nf, hf⟩ := hf κ hκ (hκsmall.trans (min_le_right _ _))
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hEe : Filter.Tendsto (fun N : ℕ => calE γ κe N) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp
      (((tendsto_rpow_atTop (by linarith : 0 < 3 - 2 * γ)).comp hlog).const_mul_atTop hκe)
  have hE : Filter.Tendsto (fun N : ℕ => calE γ κ N) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp
      (((tendsto_rpow_atTop (by linarith : 0 < 3 - 2 * γ)).comp hlog).const_mul_atTop hκ)
  obtain ⟨Nh, hh⟩ := Filter.eventually_atTop.mp
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp hEe).eventually_ge_atTop 2)
  obtain ⟨Nc, hc⟩ := Filter.eventually_atTop.mp
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hE).eventually_ge_atTop (2 * C))
  refine ⟨max 2 (max Ne (max Nf (max Nh Nc))), fun N hN j hj t ht hlarge => ?_⟩
  have hN2 : 2 ≤ N := by omega
  have hNe : Ne ≤ N := by omega
  have hNf : Nf ≤ N := by omega
  have hNh : Nh ≤ N := by omega
  have hNc : Nc ≤ N := by omega
  have hX1 : 1 ≤ F γ N := by
    apply Real.one_le_exp
    exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
  have hE0 : 0 < calE γ κ N := Real.exp_pos _
  have hEe0 : 0 < calE γ κe N := Real.exp_pos _
  have hcomp : calE γ κe N ^ (-(1 / 6 : ℝ)) ≤ calE γ κ N ^ (-(5 / 6 : ℝ)) := by
    simp only [calE, ← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    have hp : 0 ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) :=
      Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
    nlinarith only [mul_nonneg (show 0 ≤ κe - 5 * κ by linarith) hp]
  have hhalf : calE γ κe N ^ (-(1 / 6 : ℝ)) ≤ 1 / 2 := by
    rw [Real.rpow_neg hEe0.le, inv_eq_one_div]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hEe0 (1 / 6 : ℝ))).mpr
    have hhN : 2 ≤ calE γ κe N ^ (1 / 6 : ℝ) := hh N hNh
    linarith
  have heven : calE γ κe N ^ (-(1 / 3 : ℝ)) ≤ (1 / 2) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
    calc
      _ = calE γ κe N ^ (-(1 / 6 : ℝ)) * calE γ κe N ^ (-(1 / 6 : ℝ)) := by
        rw [← Real.rpow_add hEe0]; norm_num
      _ ≤ _ := mul_le_mul hhalf hcomp (Real.rpow_nonneg hEe0.le _) (by norm_num)
  by_contra hno
  have hsmall : ‖U1539.Phie γ N t‖ ≤ N * calE γ κe N ^ (-(1 / 3 : ℝ)) := by
    apply le_of_not_gt
    intro hbig
    obtain ⟨h, hh, hgap⟩ := he N hNe t ht hbig
    exact hno ⟨h, hgap⟩
  have hsmall' := hsmall.trans (mul_le_mul_of_nonneg_left heven (Nat.cast_nonneg N))
  rcases hj with rfl | rfl
  · rw [parityPhase_zero] at hlarge
    nlinarith [Real.rpow_nonneg hE0.le (-(5 / 6 : ℝ)), Nat.cast_nonneg (α := ℝ) N]
  · have htlow : F γ N ^ (3 * (δ / 3) - 1) < |t| := by
      by_contra hn
      apply hno
      refine ⟨0, ?_⟩
      simpa only [Int.cast_zero, zero_div, sub_zero, show 3 * (δ / 3) - 1 = δ - 1 by ring] using le_of_not_gt hn
    have hthigh : |t| ≤ 2 * F γ N ^ (6 * (δ / 3)) := by
      apply ht.trans
      have hh : F γ N ^ δ ≤ F γ N ^ (6 * (δ / 3)) :=
        Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      linarith [Real.rpow_nonneg (show 0 ≤ F γ N from (Real.exp_pos _).le) (6 * (δ / 3))]
    have hfull := hf N hNf t htlow hthigh
    have hscalar : C * calE γ κ N ^ (-(3 / 2 : ℝ)) ≤
        (1 / 2) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
      have hci : 2 * C ≤ calE γ κ N ^ (2 / 3 : ℝ) := hc N hNc
      have hh := mul_le_mul_of_nonneg_right hci
        (Real.rpow_nonneg hE0.le (-(3 / 2 : ℝ)))
      have hid : calE γ κ N ^ (2 / 3 : ℝ) * calE γ κ N ^ (-(3 / 2 : ℝ)) =
          calE γ κ N ^ (-(5 / 6 : ℝ)) := by rw [← Real.rpow_add hE0]; norm_num
      rw [hid] at hh
      linarith
    have hfull' : ‖Decomp404e.phaseSum γ N t‖ ≤ (N : ℝ) *
        ((1 / 2) * calE γ κ N ^ (-(5 / 6 : ℝ))) := by
      apply hfull.trans
      convert mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg N) using 1 <;> ring
    have hodd := odd_phase_complement γ N t
    linarith

/-- P0082 page368 display36 and Lemma9, page369 after display39.
The existing printed even localization and the Karacuba full phase supply
localize both parities uniformly. CONDITIONAL ON U1539.lemma9 and U1539.lemma10.
The cutoff height follows separately from the actual truncated phase window. -/
theorem leaf_parity_gap (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ j : ℤ, (j = 0 ∨ j = 1) →
          ∀ t : ℝ, |t| ≤ F γ N ^ δ →
            N * calE γ κ N ^ (-(5 / 6 : ℝ)) < ‖parityPhase γ N j t‖ →
            ∃ h : ℤ, |t - h / 2| ≤ F γ N ^ (δ - 1) := by
  exact parity_gap_of_inputs U1539.lemma9 U1539.lemma10 γ h1 h2

end LeanLab.ExceptionalSet.UpJ200.Decomp539a

namespace LeanLab.ExceptionalSet.UpJ200.Decomp539a
open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (Sp eC nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- P0082 page369 displays37 to39. The exact shifted Gram supply is bounded
by its small phase mass and its localized inner prime mass. -/
theorem shifted_moment_from_inner (γ P X Δ : ℝ) (N : ℕ) (j : ℤ) (A : Set ℝ)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (V Q : ℝ) (hV : 0 ≤ V)
    (hinner : ∀ a ∈ A,
      (∫ b in A ∩ {b | V < ‖parityPhase γ N j (b - a)‖}, mass P X Δ b) ≤ Q) :
    (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + j)),
      ‖∫ a in A, OddTail467.integrand P X Δ (F γ n - j) a‖ ^ 2) ≤
      V * (∫ a in A, mass P X Δ a) ^ 2 + N * Q * (∫ a in A, mass P X Δ a) := by
  have hg := Decomp483c.shifted_moment_gram_bound P X Δ hΔ hΔ1
    ((Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + j))) (fun n => F γ n - j) A
  have hc : Continuous (fun z : ℝ × ℝ => ‖parityPhase γ N j (z.2 - z.1)‖) := by
    unfold parityPhase U1539.eC
    fun_prop
  exact hg.2.trans (localized_gram_bound A (mass P X Δ)
    (fun z => ‖parityPhase γ N j (z.2 - z.1)‖)
    (mass_integrable P X Δ hΔ hΔ1).integrableOn (fun a => norm_nonneg _)
    (fun z => norm_nonneg _) hc V N Q hV (Nat.cast_nonneg _) hg.1
    (fun a ha b hb => parityPhase_le γ N j (b - a)) hinner)

/-- P0082 page369 display38, a coarse quarter power envelope for the mass. -/
theorem mass_bound_coarse (E A M : ℝ) (hE : 1 ≤ E) (hA : 0 ≤ A)
    (hM : M ≤ 7 * A / Real.sqrt (E ^ (-(5 / 12 : ℝ)))) :
    M ≤ 7 * A * E ^ (1 / 4 : ℝ) := by
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have he : 7 * A / Real.sqrt (E ^ (-(5 / 12 : ℝ))) = 7 * A * E ^ (5 / 24 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hE0.le, div_eq_mul_inv, ← Real.rpow_neg hE0.le]
    norm_num
  rw [he] at hM
  exact hM.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hE (by norm_num)) (by positivity))

/-- P0082 page369 display39, logarithmic absorption of the localized part. -/
theorem large_phase_budget (E X C M : ℝ) (N : ℕ) (hE : 1 ≤ E) (hX : 0 ≤ X)
    (hC : 0 ≤ C) (hL : 1 ≤ Real.log X)
    (hlog : Real.log X ^ 2 ≤ E ^ (1 / 12 : ℝ))
    (hM : M ≤ 7 * (Real.log 4 * X * Real.log X) / Real.sqrt (E ^ (-(5 / 12 : ℝ)))) :
    N * (6 * C * X * E ^ (-(2 / 3 : ℝ))) * M ≤
      (42 * C * Real.log 4) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have hA : 0 ≤ Real.log 4 * X * Real.log X := by positivity
  have hm := mass_bound_coarse E _ M hE hA hM
  have hl : Real.log X * E ^ (-(5 / 12 : ℝ)) ≤ E ^ (-(1 / 3 : ℝ)) := by
    have hll : Real.log X ≤ Real.log X ^ 2 := by nlinarith
    calc
      _ ≤ E ^ (1 / 12 : ℝ) * E ^ (-(5 / 12 : ℝ)) :=
        mul_le_mul_of_nonneg_right (hll.trans hlog) (Real.rpow_nonneg hE0.le _)
      _ = _ := by rw [← Real.rpow_add hE0]; norm_num
  calc
    _ ≤ N * (6 * C * X * E ^ (-(2 / 3 : ℝ))) *
        (7 * (Real.log 4 * X * Real.log X) * E ^ (1 / 4 : ℝ)) := by gcongr
    _ = (42 * C * Real.log 4) * N * X ^ 2 * (Real.log X * E ^ (-(5 / 12 : ℝ))) := by
      have he : E ^ (-(2 / 3 : ℝ)) * E ^ (1 / 4 : ℝ) = E ^ (-(5 / 12 : ℝ)) := by
        rw [← Real.rpow_add hE0]; norm_num
      calc
        _ = (42 * C * Real.log 4) * N * X ^ 2 *
            (Real.log X * (E ^ (-(2 / 3 : ℝ)) * E ^ (1 / 4 : ℝ))) := by ring
        _ = _ := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)

end LeanLab.ExceptionalSet.UpJ200.Decomp539a

namespace LeanLab.ExceptionalSet.UpJ200.Decomp539a
open Real Finset MeasureTheory Set Filter Topology
open LeanLab.ExceptionalSet.U1539 (Sp eC nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- P0082 pages368 and369, derived eventual margins for the free width,
phase threshold, truncated window and finite half integer cutoff. -/
theorem phase_window_parameters (γ δ κ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      2 ≤ F γ N ∧ 1 < calE γ κ N ∧ 1 ≤ Real.log (F γ N) ∧
      Real.log (F γ N) ^ 2 ≤ calE γ κ N ^ (1 / 12 : ℝ) ∧
      calE γ κ N ^ (7 / 4 : ℝ) ≤ F γ N ^ (5 * δ) ∧
      calE γ κ N ^ (2 / 3 : ℝ) ≤ F γ N ^ (6 * δ) ∧
      2 * calE γ κ N ^ (2 / 3 : ℝ) ≤ F γ N ^ δ ∧
      4 * calE γ κ N ^ (2 / 3 : ℝ) + 2 ≤ calE γ κ N ^ (3 / 4 : ℝ) ∧
      F γ N ^ (δ - 1) ≤ 1 := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hF : Tendsto (fun N : ℕ => F γ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog)
  have hE : Tendsto (fun N : ℕ => calE γ κ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (((tendsto_rpow_atTop (by linarith : 0 < 3 - 2 * γ)).comp hlog).const_mul_atTop hκ)
  obtain ⟨Nl, hl⟩ := Decomp467a.log_F_sq_le_calE_twelfth γ κ h1 h2 hκ
  obtain ⟨Ns, hs⟩ := Decomp404e.calE_power_le_F_power γ κ (7 / 4) (5 * δ) h1 (by positivity)
  obtain ⟨Nt, ht⟩ := Decomp404e.calE_power_le_F_power γ κ (2 / 3) (6 * δ) h1 (by positivity)
  obtain ⟨Na, ha⟩ := Decomp404e.calE_power_le_F_power γ κ (2 / 3) (δ / 2) h1 (by positivity)
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop Nl, eventually_ge_atTop Ns, eventually_ge_atTop Nt,
    eventually_ge_atTop Na, hF.eventually_ge_atTop (Real.exp 1), hE.eventually_ge_atTop 2,
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp hE).eventually_ge_atTop 6),
    (((tendsto_rpow_atTop (by positivity : 0 < δ / 2)).comp hF).eventually_ge_atTop 2)]
    with N hNl hNs hNt hNa hFX hEN hE6 hF2
  change 6 ≤ calE γ κ N ^ (1 / 12 : ℝ) at hE6
  change 2 ≤ F γ N ^ (δ / 2) at hF2
  have hX : 1 ≤ F γ N := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hFX
  have hX0 : 0 < F γ N := Real.exp_pos _
  have hE0 : 0 < calE γ κ N := Real.exp_pos _
  have hE1 : 1 ≤ calE γ κ N := by linarith
  have hL : 1 ≤ Real.log (F γ N) := by
    have := Real.log_le_log (Real.exp_pos 1) hFX
    simpa only [Real.log_exp] using this
  have hX2 : 2 ≤ F γ N := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  refine ⟨hX2, by linarith, hL, hl N hNl, hs N hNs, ?_, ?_, ?_, ?_⟩
  · simpa only [Real.rpow_one] using ht N hNt
  · calc
      _ ≤ 2 * F γ N ^ (δ / 2) := mul_le_mul_of_nonneg_left (ha N hNa) (by norm_num)
      _ ≤ (F γ N ^ (δ / 2)) ^ 2 := by nlinarith
      _ = _ := by rw [← Real.rpow_mul_natCast hX0.le]; congr 1; ring
  · have hEt : 1 ≤ calE γ κ N ^ (2 / 3 : ℝ) := Real.one_le_rpow hE1 (by norm_num)
    calc
      _ ≤ 6 * calE γ κ N ^ (2 / 3 : ℝ) := by linarith
      _ ≤ calE γ κ N ^ (1 / 12 : ℝ) * calE γ κ N ^ (2 / 3 : ℝ) := by gcongr
      _ = _ := by rw [← Real.rpow_add hE0]; norm_num
  · exact Real.rpow_le_one_of_one_le_of_nonpos hX (by linarith)

end LeanLab.ExceptionalSet.UpJ200.Decomp539a


namespace LeanLab.ExceptionalSet.UpJ200.Decomp539a
open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (Sp eC nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- P0082 page368 display35 and page369 displays37 to39.
The parity gap leaf, finite strip volume and proved prime minor supremum
supply the full shifted moment. CONDITIONAL ON leaf_parity_gap. -/
theorem parity_moment_from_gap (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ j : ℤ, (j = 0 ∨ j = 1) →
            (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + j)),
              ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - j) α‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))  := by
  classical
  obtain ⟨δg, hδg, hg⟩ := leaf_parity_gap γ h1 h2
  obtain ⟨δm, hδm, hm⟩ := MinorSup446.leaf_minor_sup_supplied γ h1 h2
  refine ⟨min δg (min δm 1), lt_min hδg (lt_min hδm (by norm_num)), fun δ hδ hδsmall => ?_⟩
  have hδg' : δ < δg := hδsmall.trans_le (min_le_left _ _)
  have hδm' : δ < δm := hδsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := hδsmall.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨κ₀, hκ₀, hg⟩ := hg δ hδ hδg'
  obtain ⟨C, hC, Nm, hm⟩ := hm δ hδ hδm'
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Ng, hg⟩ := hg κ hκ hκsmall
  obtain ⟨Np, hp⟩ := phase_window_parameters γ δ κ h1 h2 hδ hδ1 hκ
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨49 * Real.log 4 ^ 2 + 42 * C * Real.log 4, by positivity,
    max Ng (max Nm Np), fun N hN j hj => ?_⟩
  have hNg : Ng ≤ N := by omega
  have hNm : Nm ≤ N := by omega
  have hNp : Np ≤ N := by omega
  obtain ⟨hX, hE, hL, hl, hs, hTX, htw, hheight, hr⟩ := hp N hNp
  let X := F γ N
  let E := calE γ κ N
  let P := X ^ (6 * δ)
  let Δ := E ^ (-(5 / 12 : ℝ))
  let A := oddDomain P X E
  let M := ∫ a in A, mass P X Δ a
  let V := (N : ℝ) * E ^ (-(5 / 6 : ℝ))
  let Q := 6 * C * X * E ^ (-(2 / 3 : ℝ))
  have hX0 : 0 < X := Real.exp_pos _
  have hE0 : 0 < E := Real.exp_pos _
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hE0 _
  have hΔ1 : Δ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hE (by norm_num)
  have hMi := mass_integrable P X Δ hΔ hΔ1
  have hM0 : 0 ≤ M := integral_nonneg (fun a => norm_nonneg _)
  have hMb : M ≤ 7 * (Real.log 4 * X * Real.log X) / Real.sqrt Δ := by
    apply (setIntegral_le_integral hMi (Filter.Eventually.of_forall (fun a => norm_nonneg _))).trans
    exact Decomp483d.shifted_weighted_mass_sqrt P X Δ hX hΔ hΔ1
  have hinner (a : ℝ) (ha : a ∈ A) :
      (∫ b in A ∩ {b | V < ‖parityPhase γ N j (b - a)‖}, mass P X Δ b) ≤ Q := by
    apply prime_strip_inner E X C δ hE.le hX0 hC.le hΔ1 hTX hl hs (hm N hNm) a
    · exact Set.inter_subset_left
    · intro b hb
      have hbt : |b - a| ≤ 2 * E ^ (2 / 3 : ℝ) := by
        apply abs_le.mpr
        constructor <;> linarith [ha.2.1, ha.2.2, hb.1.2.1, hb.1.2.2]
      obtain ⟨h, hgap⟩ := hg N hNg j hj (b - a) (hbt.trans htw) hb.2
      have hh := half_integer_height E (b - a) (X ^ (δ - 1)) h hr hbt hgap hheight
      have hmem := mem_stripIndices E h hh
      apply Set.mem_iUnion.mpr
      refine ⟨h, Set.mem_iUnion.mpr ⟨hmem, ?_⟩⟩
      have hab := abs_le.mp hgap
      exact ⟨by linarith [hab.1], by linarith [hab.2]⟩
  have hmoment := shifted_moment_from_inner γ P X Δ N j A hΔ hΔ1 V Q (by dsimp [V]; positivity) hinner
  have hsmall := small_phase_budget E (Real.log 4 * X * Real.log X) M N hE.le
    (by positivity) hM0 hMb
  have hsmalllog := small_phase_log_budget E X N hE.le hl
  have hlarge := large_phase_budget E X C M N hE.le hX0.le hC.le hL hl hMb
  change _ ≤ (49 * Real.log 4 ^ 2 + 42 * C * Real.log 4) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ))
  change _ ≤ V * M ^ 2 + N * Q * M at hmoment
  calc
    _ ≤ V * M ^ 2 + N * Q * M := hmoment
    _ ≤ (49 * Real.log 4 ^ 2) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) +
        (42 * C * Real.log 4) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by
      exact add_le_add (hsmall.trans hsmalllog) hlarge
    _ = _ := by ring

end LeanLab.ExceptionalSet.UpJ200.Decomp539a
