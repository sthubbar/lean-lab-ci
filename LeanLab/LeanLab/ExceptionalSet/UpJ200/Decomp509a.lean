import LeanLab.ExceptionalSet.OddKernel467
import LeanLab.ExceptionalSet.Fejer467
import LeanLab.ExceptionalSet.UpJ200.PrimeTail385
import LeanLab.ExceptionalSet.UpJ200.Decomp467a

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

namespace LeanLab.ExceptionalSet.UpJ200.Decomp509a
open Real Finset Filter Topology MeasureTheory
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE R1 majorArcs)

/-- P0082 page368 display33 from page359 Lemma4.
A free boundary width is controlled on the entire half interval.
CONDITIONAL ON the cited discrepancy input U1539.lemma4. -/
theorem full_boundary_at_rate (γ a : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (ha : 0 < a) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
          Int.fract (F γ n) < calE γ κ N ^ (-a) ∨
            1 - calE γ κ N ^ (-a) < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-a) := by
  classical
  obtain ⟨κa, A, hκa, hdisc⟩ := LeanLab.ExceptionalSet.U1539.lemma4 γ h1 h2
  refine ⟨κa / a, by positivity, fun κ hκ hκsmall => ?_⟩
  let B := 2 * |A| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hE : Tendsto (fun N : ℕ => calE γ κ N) atTop atTop := by
    exact Real.tendsto_exp_atTop.comp
      (((tendsto_rpow_atTop (by linarith : 0 < 3 - 2 * γ)).comp hlog).const_mul_atTop hκ)
  obtain ⟨NE, hNE⟩ := eventually_atTop.mp (hE.eventually_ge_atTop 2)
  refine ⟨B, hB, max 16 NE, fun N hN => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hE1 : 1 < calE γ κ N := lt_of_lt_of_le (by norm_num) (hNE N ((le_max_right _ _).trans hN))
  let Δ := calE γ κ N ^ (-a)
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hΔ1 : Δ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hE1 (by linarith)
  have hF1 : 1 < F γ N := by
    rw [F]
    exact Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos hL _)
  have hα : F γ N ^ (-(1 / 2 : ℝ)) < |(1 : ℝ)| := by
    simpa using Real.rpow_lt_one_of_one_lt_of_neg hF1 (by norm_num : -(1 / 2 : ℝ) < 0)
  have hlo := hdisc N hN1 1 hα (by norm_num) Δ 0 (by norm_num) hΔ hΔ1.le
  have hhi := hdisc N hN1 1 hα (by norm_num) 1 (1 - Δ) (by linarith) (by linarith) le_rfl
  simp only [one_mul, sub_zero, sub_sub_cancel] at hlo hhi
  have herr : Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) ≤ Δ := by
    dsimp [Δ, calE]
    rw [← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    have hp : 0 ≤ Real.log N ^ (3 - 2 * γ) := (Real.rpow_pos_of_pos hL _).le
    have hsmall : κ * a ≤ κa := (le_div_iff₀ ha).mp hκsmall
    nlinarith [mul_le_mul_of_nonneg_right hsmall hp]
  let L := (Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
    0 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < Δ)
  let R := (Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
    1 - Δ ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < 1)
  have hsubset : (Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
      Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n)) ⊆ L ∪ R := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnW, hn⟩
    have hnI := hnW
    rcases hn with hn | hn
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnI, Int.fract_nonneg _, hn⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnI, hn.le, Int.fract_lt_one _⟩)
  have hcard : (((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
      Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n))).card : ℝ) ≤ L.card + R.card := by
    exact_mod_cast (Finset.card_le_card hsubset).trans (Finset.card_union_le L R)
  have hl : (L.card : ℝ) ≤ Δ * N / 2 + |A| * N * Δ := by
    have ha := (abs_le.mp hlo).2
    change (L.card : ℝ) - Δ * N / 2 ≤ _ at ha
    have hbound : A * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) ≤ |A| * N * Δ := by
      calc _ ≤ |A| * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) := by gcongr; exact le_abs_self _
           _ ≤ _ := by gcongr
    linarith
  have hr : (R.card : ℝ) ≤ Δ * N / 2 + |A| * N * Δ := by
    have ha := (abs_le.mp hhi).2
    change (R.card : ℝ) - Δ * N / 2 ≤ _ at ha
    have hbound : A * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) ≤ |A| * N * Δ := by
      calc _ ≤ |A| * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) := by gcongr; exact le_abs_self _
           _ ≤ _ := by gcongr
    linarith
  calc
    _ ≤ (L.card : ℝ) + R.card := hcard
    _ ≤ (Δ * N / 2 + |A| * N * Δ) + (Δ * N / 2 + |A| * N * Δ) := add_le_add hl hr
    _ = _ := by dsimp [B]; ring


/-- P0082 page368 displays33 to35, derived error margin.
The free width E to minus five twelfths and height E to two thirds
leave enough decay for the two logarithms in both error terms. -/
theorem shifted_error_budget (X E B : ℝ) (N : ℕ)
    (hE : 1 ≤ E) (hB : 0 ≤ B)
    (hlog : Real.log X ^ 2 ≤ E ^ (1 / 12 : ℝ)) :
    2 * N * (8 * (Real.log 4 * X * Real.log X) /
      (E ^ (-(5 / 12 : ℝ)) * Real.pi ^ 2 * E ^ (2 / 3 : ℝ))) ^ 2 +
      (B * N * E ^ (-(5 / 12 : ℝ))) * (Real.log 4 * X * Real.log X) ^ 2 ≤
        (128 * Real.log 4 ^ 2 / Real.pi ^ 4 + B * Real.log 4 ^ 2) *
          N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have ht : (E ^ (-(5 / 12 : ℝ)) * E ^ (2 / 3 : ℝ)) ^ 2 = E ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hE0, ← Real.rpow_mul_natCast hE0.le]
    norm_num
  have htail : (8 * (Real.log 4 * X * Real.log X) /
      (E ^ (-(5 / 12 : ℝ)) * Real.pi ^ 2 * E ^ (2 / 3 : ℝ))) ^ 2 =
      (64 * Real.log 4 ^ 2 / Real.pi ^ 4) * X ^ 2 * Real.log X ^ 2 *
        E ^ (-(1 / 2 : ℝ)) := by
    conv_rhs => rw [Real.rpow_neg hE0.le]
    rw [div_pow]
    have hd : (E ^ (-(5 / 12 : ℝ)) * Real.pi ^ 2 * E ^ (2 / 3 : ℝ)) ^ 2 =
        Real.pi ^ 4 * E ^ (1 / 2 : ℝ) := by
      calc _ = Real.pi ^ 4 * (E ^ (-(5 / 12 : ℝ)) * E ^ (2 / 3 : ℝ)) ^ 2 := by ring
           _ = _ := by rw [ht]
    rw [hd]
    ring
  have hp (a : ℝ) :
      Real.log X ^ 2 * E ^ a ≤ E ^ (a + 1 / 12) := by
    calc _ ≤ E ^ (1 / 12 : ℝ) * E ^ a :=
        mul_le_mul_of_nonneg_right hlog (Real.rpow_pos_of_pos hE0 _).le
         _ = _ := by rw [← Real.rpow_add hE0]; congr 1; ring
  have htlog : Real.log X ^ 2 * E ^ (-(1 / 2 : ℝ)) ≤ E ^ (-(1 / 3 : ℝ)) := by
    refine (hp (-(1 / 2 : ℝ))).trans ?_
    exact Real.rpow_le_rpow_of_exponent_le hE (by norm_num)
  have hblog : Real.log X ^ 2 * E ^ (-(5 / 12 : ℝ)) ≤ E ^ (-(1 / 3 : ℝ)) := by
    convert hp (-(5 / 12 : ℝ)) using 1 <;> norm_num
  rw [htail]
  calc
    _ = (128 * Real.log 4 ^ 2 / Real.pi ^ 4) * N * X ^ 2 *
          (Real.log X ^ 2 * E ^ (-(1 / 2 : ℝ))) +
        (B * Real.log 4 ^ 2) * N * X ^ 2 *
          (Real.log X ^ 2 * E ^ (-(5 / 12 : ℝ))) := by ring
    _ ≤ (128 * Real.log 4 ^ 2 / Real.pi ^ 4) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) +
        (B * Real.log 4 ^ 2) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left htlog (by positivity)
      · exact mul_le_mul_of_nonneg_left hblog (by positivity)
    _ = _ := by ring


/-- LEAF: P0082 page368 display35 and page369 displays37 to39.
The full parity sets retain cancellation. The free width and height have
extra logarithmic margins. Only this truncated sparse moment remains analytic. -/
theorem leaf_shifted_parity_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ j : ℤ, (j = 0 ∨ j = 1) →
            (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + j)),
              ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - j) α‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  sorry

/-- P0082 page367 displays29 and30 from page368 display35.
The full interval discrepancy bound and explicit tail budget discharge all
boundary and truncation steps. CONDITIONAL ON the shifted analytic moment
and the cited discrepancy input U1539.lemma4. -/
theorem parity_moment_from_shifted (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ j : ℤ, (j = 0 ∨ j = 1) →
            (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + j)),
              ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n - j + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨δ₀, hδ₀, hm⟩ := leaf_shifted_parity_moment γ h1 h2
  obtain ⟨κb, hκb, hb⟩ := full_boundary_at_rate γ (5 / 12) h1 h2 (by norm_num)
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κm, hκm, hm⟩ := hm δ hδ hδsmall
  refine ⟨min κm κb, lt_min hκm hκb, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Bm, hBm, Nm, hm⟩ := hm κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Bb, hBb, Nb, hb⟩ := hb κ hκ (hκsmall.trans (min_le_right _ _))
  obtain ⟨Np, hp⟩ := TailParameters385.tail_parameters_eventually γ h1 h2 δ κ hδ hκ
  obtain ⟨Nl, hl⟩ := Decomp467a.log_F_sq_le_calE_twelfth γ κ h1 h2 hκ
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hEtop : Tendsto (fun N : ℕ => calE γ κ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (((tendsto_rpow_atTop (by linarith : 0 < 3 - 2 * γ)).comp hlog).const_mul_atTop hκ)
  obtain ⟨Ne, he⟩ := eventually_atTop.mp (hEtop.eventually_ge_atTop 2)
  obtain ⟨Nt, ht⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hEtop).eventually_ge_atTop 4)
  refine ⟨2 * Bm + 128 * Real.log 4 ^ 2 / Real.pi ^ 4 + Bb * Real.log 4 ^ 2,
    by positivity, max Nm (max Nb (max Np (max Nl (max Ne Nt)))), fun N hN j hj => ?_⟩
  have hNm : Nm ≤ N := by omega
  have hNb : Nb ≤ N := by omega
  have hNp : Np ≤ N := by omega
  have hNl : Nl ≤ N := by omega
  have hNe : Ne ≤ N := by omega
  have hNt : Nt ≤ N := by omega
  let X := F γ N
  let E := calE γ κ N
  let P := X ^ (6 * δ)
  let Δ := E ^ (-(5 / 12 : ℝ))
  let T := E ^ (2 / 3 : ℝ)
  let s := (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + j))
  have hX : 2 ≤ X := (hp N hNp).1
  have hP : 2 ≤ P := by have := (hp N hNp).2.1; dsimp [P, X]; linarith
  have hE : 1 < E := lt_of_lt_of_le (by norm_num) (he N hNe)
  have hE0 : 0 < E := lt_trans zero_lt_one hE
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hE0 _
  have hΔ1 : Δ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hE (by norm_num)
  have hT : 4 ≤ T := ht N hNt
  have hodd (n : ℕ) (hn : n ∈ s) : Odd (⌊F γ n - (j : ℝ)⌋ + 1) := by
    rw [Int.floor_sub_intCast]
    change Odd (nu γ n - j + 1)
    obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hn).2
    exact ⟨k - j, by omega⟩
  have htransfer := Decomp483a.odd_upper_truncated_moment P X Δ T hP hX hΔ hΔ1 hT s
    (fun n => F γ n - j) hodd
  simp_rw [Int.floor_sub_intCast, show ∀ n : ℕ, ⌊F γ n⌋ = nu γ n from fun _ => rfl] at htransfer
  have hcard : (s.card : ℝ) ≤ N := by
    exact_mod_cast (Finset.card_filter_le _ _).trans
      (by rw [Nat.card_Ioc]; omega : (Finset.Ioc (N / 2) N).card ≤ N)
  have hsub : s.filter (fun n : ℕ => Int.fract (F γ n - j) < Δ / 2 ∨
      1 - Δ / 2 < Int.fract (F γ n - j)) ⊆
      (Finset.Ioc (N / 2) N).filter (fun n : ℕ => Int.fract (F γ n) < Δ ∨
        1 - Δ < Int.fract (F γ n)) := by
    intro n hn
    obtain ⟨hns, hn⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_filter.mp hns).1, ?_⟩
    simp only [Int.fract_sub_intCast] at hn
    rcases hn with hn | hn
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hboundary : ((s.filter (fun n : ℕ => Int.fract (F γ n - j) < Δ / 2 ∨
      1 - Δ / 2 < Int.fract (F γ n - j))).card : ℝ) ≤ Bb * N * Δ := by
    exact (Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)).trans (hb N hNb)
  have herrors := shifted_error_budget X E Bb N hE.le hBb.le (hl N hNl)
  have htail : 2 * (s.card : ℝ) *
      (8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T)) ^ 2 ≤
      2 * N * (8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T)) ^ 2 := by
    gcongr
  have hboundaryTerm := mul_le_mul_of_nonneg_right hboundary
    (sq_nonneg (Real.log 4 * X * Real.log X))
  have hmoment := hm N hNm j hj
  change (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ ∩ Set.Icc (-T) T,
    OddTail467.integrand P X Δ (F γ n - j) α‖ ^ 2) ≤
      Bm * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) at hmoment
  change _ ≤ (2 * Bm + 128 * Real.log 4 ^ 2 / Real.pi ^ 4 + Bb * Real.log 4 ^ 2) *
    N * X ^ 2 * E ^ (-(1 / 3 : ℝ))
  calc
    _ ≤ 2 * (Bm * N * X ^ 2 * E ^ (-(1 / 3 : ℝ))) +
        (128 * Real.log 4 ^ 2 / Real.pi ^ 4 + Bb * Real.log 4 ^ 2) *
          N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by
      dsimp only [P, X, E, Δ, T, s] at htransfer htail hboundaryTerm herrors hmoment ⊢
      linarith only [htransfer, htail, hboundaryTerm, herrors, hmoment]
    _ = _ := by ring

end LeanLab.ExceptionalSet.UpJ200.Decomp509a
