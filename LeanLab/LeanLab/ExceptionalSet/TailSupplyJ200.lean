import LeanLab.ExceptionalSet.MajorSupplyJ200
import LeanLab.ExceptionalSet.BG2026MinorCont
import LeanLab.ExceptionalSet.KernelTail385

/-!
Upstream supply of the minor arc tail estimate for `DecompJ200.leaf_minor_tail`.
Source: P0082, Brüdern and Perelli 1998, https://doi.org/10.5802/aif.1621, page 365 display 24,
with the parameters of pages 354, 355, 357 and 359.
The four sections below are copies of `PrimeEnergy385`, `TailPartition385`, `PrimeTail385` and
`TailParameters385`, placed here so that `DecompJ200` can import them without an import cycle:
the originals reach `DecompJ200` through `Decomp371a` and `Decomp371b`, although they use from
there only `Decomp371a.Sp_periodic`, copied as `MajorSupplyJ200.Sp_periodic`.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.TailSupplyJ200

/-! ### Copy of `PrimeEnergy385` -/

namespace PrimeEnergy

open Real Finset MeasureTheory ComplexConjugate
open LeanLab.ExceptionalSet.U1539 (Sp)

/-- Parseval for the finite prime sum of P0082 page 357 and page 365. -/
theorem prime_energy (P X : ℝ) :
    (∫ α in (0 : ℝ)..1, ‖Sp P X α‖ ^ 2) =
      ∑ p ∈ (Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p ^ 2 := by
  let s := (Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime
  have he (α : ℝ) : Sp P X α = ∑ n ∈ s, (Real.log n : ℂ) * BG2026.eC (n * α) := by
    unfold Sp
    apply sum_congr rfl
    intro n hn
    unfold U1539.eC BG2026.eC
    push_cast
    ring_nf
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have he2 (α : ℝ) : ((‖Sp P X α‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ s, ∑ m ∈ s, ((Real.log n : ℂ) * Real.log m) *
        BG2026.eC (((n - m : ℤ) : ℝ) * α) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', he, map_sum, sum_mul_sum]
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro m hm
    rw [map_mul, Complex.conj_ofReal, BG2026.conj_eC]
    have hx : BG2026.eC (n * α) * BG2026.eC (-(m * α)) =
        BG2026.eC (((n - m : ℤ) : ℝ) * α) := by
      unfold BG2026.eC
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← hx]
    ring
  simp_rw [he2]
  rw [BG2026.integral_double_sum]
  push_cast
  apply sum_congr rfl
  intro n hn
  rw [sum_eq_single n]
  · simp
    ring
  · intro m hm hmn
    rw [ite_eq_right (by omega)]
    simp
  · intro h
    exact absurd hn h

/-- Every unit interval has the same prime sum energy.
Source: P0082 page 365, periodicity in the estimate before display 24. -/
theorem prime_energy_shift (P X a : ℝ) :
    (∫ α in a..a + 1, ‖Sp P X α‖ ^ 2) =
      ∑ p ∈ (Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p ^ 2 := by
  have hp : Function.Periodic (fun α => ‖Sp P X α‖ ^ 2) 1 := by
    intro α
    dsimp only
    rw [MajorSupplyJ200.Sp_periodic P X α]
  have hi : (∫ α in a..a + 1, ‖Sp P X α‖ ^ 2) =
      (∫ α in (0 : ℝ)..1, ‖Sp P X α‖ ^ 2) := by
    simpa only [zero_add] using hp.intervalIntegral_add_eq a 0
  exact hi.trans (prime_energy P X)

/-- The uniform prime sum mass bound used on P0082 page 365.
The explicit constant log 4 comes from Mathlib's Chebyshev theta bound. -/
theorem prime_energy_le (P X a : ℝ) (hX : 2 ≤ X) :
    (∫ α in a..a + 1, ‖Sp P X α‖ ^ 2) ≤ Real.log 4 * X * Real.log X := by
  classical
  rw [prime_energy_shift]
  let s := (Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime
  have hX0 : 0 ≤ X := by linarith
  have hLX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hsum : (∑ p ∈ s, Real.log p) ≤ Chebyshev.theta X := by
    unfold Chebyshev.theta
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rcases mem_filter.mp hp with ⟨hI, hprime⟩
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hI).1,
        (mem_Ioc.mp hI).2⟩, hprime⟩
    · intro p hp _
      have hp1 := (mem_filter.mp hp).2.one_lt.le
      exact Real.log_nonneg (by exact_mod_cast hp1)
  have hterm (p : ℕ) (hp : p ∈ s) : Real.log p ^ 2 ≤ Real.log X * Real.log p := by
    have hprime := (mem_filter.mp hp).2
    have hLp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
    have hpfloor : (p : ℝ) ≤ ⌊X⌋₊ := by
      exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).2
    have hpX : (p : ℝ) ≤ X := hpfloor.trans (Nat.floor_le hX0)
    have hL := Real.log_le_log (by exact_mod_cast hprime.pos) hpX
    nlinarith [mul_nonneg hLp (sub_nonneg.mpr hL)]
  calc ∑ p ∈ s, Real.log p ^ 2 ≤ ∑ p ∈ s, Real.log X * Real.log p := sum_le_sum hterm
    _ = Real.log X * ∑ p ∈ s, Real.log p := (mul_sum _ _ _).symm
    _ ≤ Real.log X * Chebyshev.theta X := mul_le_mul_of_nonneg_left hsum hLX
    _ ≤ Real.log X * (Real.log 4 * X) :=
      mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x hX0) hLX
    _ = _ := by ring

/-- The prime weighted unit interval bound before P0082 page 365 display 24.
It is uniform in the real phase frequency v and in the prime lower cutoff P. -/
theorem prime_kernel_block_le (P X Δ a v : ℝ) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (ha : 0 < a) :
    (∫ α in a..a + 1,
      ‖Sp P X α ^ 2 * (U1539.Kfun Δ α : ℂ) * U1539.eC (-(α * v))‖) ≤
        (Real.log 4 * X * Real.log X) / (Δ * (Real.pi * a) ^ 2) := by
  have hg : Continuous (fun α => Sp P X α ^ 2 * U1539.eC (-(α * v))) := by
    unfold Sp U1539.eC
    fun_prop
  have hm : (∫ α in a..a + 1, ‖Sp P X α ^ 2 * U1539.eC (-(α * v))‖) ≤
      Real.log 4 * X * Real.log X := by
    simp only [norm_mul, norm_pow, U1539.norm_eC, mul_one]
    exact prime_energy_le P X a hX
  calc (∫ α in a..a + 1,
      ‖Sp P X α ^ 2 * (U1539.Kfun Δ α : ℂ) * U1539.eC (-(α * v))‖)
      = ∫ α in a..a + 1,
          ‖(Sp P X α ^ 2 * U1539.eC (-(α * v))) * (U1539.Kfun Δ α : ℂ)‖ := by
        apply intervalIntegral.integral_congr
        intro α hα
        simp only [mul_assoc, mul_left_comm, mul_comm]
    _ ≤ _ := KernelTail385.block_kernel_norm_le _ hg Δ a _ hΔ hΔ1 ha hm

end PrimeEnergy

/-! ### Copy of `TailPartition385` -/

namespace TailPartition

open Real MeasureTheory Set Filter

/-- An integrable function on a half line splits into its consecutive unit blocks.
Source: P0082 page 365, summation over k before display 24. -/
theorem hasSum_Ioi_blocks (f : ℝ → ℝ) (hf : Integrable f) (a : ℝ) :
    HasSum (fun n : ℕ => ∫ x in a + n..a + n + 1, f x) (∫ x in Ioi a, f x) := by
  have hu : (⋃ n : ℕ, Ioc (a + n) (a + n + 1)) = Ioi a := by
    have hmin (n : ℕ) : a + (0 : ℕ) ≤ a + n := by
      simpa only [Nat.cast_zero, add_zero] using
        (le_add_of_nonneg_right (Nat.cast_nonneg n) : a ≤ a + (n : ℝ))
    have hnb : ¬ BddAbove (range (fun n : ℕ => a + (n : ℝ))) := by
      rintro ⟨b, hb⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (b - a)
      have hle := hb (mem_range_self n)
      linarith
    simpa only [bot_eq_zero, Nat.cast_zero, add_zero, Order.succ_eq_add_one,
      Nat.cast_add, Nat.cast_one, add_assoc] using
      (iUnion_Ioc_map_succ_eq_Ioi hmin hnb)
  have hd : Pairwise (fun i j : ℕ => Disjoint (Ioc (a + i) (a + i + 1)) (Ioc (a + j) (a + j + 1))) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · have hc : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
      apply disjoint_left.mpr
      intro x hi hj
      have := hi.2
      have := hj.1
      linarith
    · have hc : (j : ℝ) + 1 ≤ i := by exact_mod_cast (show j + 1 ≤ i by omega)
      apply disjoint_left.mpr
      intro x hi hj
      have := hi.1
      have := hj.2
      linarith
  have hs : HasSum (fun n : ℕ => ∫ x in a + n..a + n + 1, f x) (∫ x in Ioi a, f x) := by
    simp_rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right zero_le_one)]
    rw [← hu]
    exact hasSum_integral_iUnion (fun _ => measurableSet_Ioc) hd hf.integrableOn
  exact hs

/-- The half line integral is the sum of its unit blocks, P0082 page 365. -/
theorem integral_Ioi_eq_tsum_blocks (f : ℝ → ℝ) (hf : Integrable f) (a : ℝ) :
    (∫ x in Ioi a, f x) = ∑' n : ℕ, ∫ x in a + n..a + n + 1, f x :=
  (hasSum_Ioi_blocks f hf a).tsum_eq.symm

/-- The inverse square tail used on P0082 page 365 before display 24. -/
theorem reciprocal_square_tail (K : ℕ) (hK : 2 ≤ K) :
    (∑' n : ℕ, 1 / (((n + K : ℕ) : ℝ) ^ 2)) ≤ 1 / ((K : ℝ) - 1) := by
  have hc : 0 < ((K - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < K - 1)
  have ha : AntitoneOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ici ((K - 1 : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hc.trans_le hx) hxy (by norm_num)
  have hi : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi ((K - 1 : ℕ) : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hc
  have hn : ∀ x ∈ Ioi ((K - 1 : ℕ) : ℝ), 0 ≤ x ^ (-2 : ℝ) :=
    fun x hx => Real.rpow_nonneg (hc.trans hx).le _
  have hs := AntitoneOn.tsum_comp_add_le_integral (K - 1) ha hi hn
  have he (n : ℕ) : (((n + (K - 1) + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) =
      1 / (((n + K : ℕ) : ℝ) ^ 2) := by
    rw [show n + (K - 1) + 1 = n + K by omega,
      Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two, one_div]
  simp_rw [he] at hs
  rw [integral_Ioi_rpow_of_lt (by norm_num) hc] at hs
  norm_num [Real.rpow_neg_one] at hs
  simpa [Nat.cast_sub (show 1 ≤ K by omega), one_div] using hs

/-- A uniform inverse square unit bound gives the half line integral estimate.
Source: P0082 page 365, the summation before display 24. -/
theorem integral_Ioi_le_of_blocks (f : ℝ → ℝ) (hf : Integrable f)
    (K : ℕ) (hK : 2 ≤ K) (A : ℝ) (hA : 0 ≤ A)
    (hblock : ∀ k : ℕ, K ≤ k → (∫ x in (k : ℝ)..(k : ℝ) + 1, f x) ≤ A / (k : ℝ) ^ 2) :
    (∫ x in Ioi (K : ℝ), f x) ≤ A / ((K : ℝ) - 1) := by
  have hs : Summable (fun n : ℕ => 1 / (((n + K : ℕ) : ℝ) ^ 2)) := by
    exact (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      (fun i j h => by omega)
  have hsA : Summable (fun n : ℕ => A / (((n + K : ℕ) : ℝ) ^ 2)) := by
    simpa only [mul_one_div] using hs.mul_left A
  have hl := hasSum_Ioi_blocks f hf (K : ℝ)
  have hp (n : ℕ) : (∫ x in (K : ℝ) + n..(K : ℝ) + n + 1, f x) ≤
      A / (((n + K : ℕ) : ℝ) ^ 2) := by
    simpa only [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
      hblock (n + K) (by omega)
  calc (∫ x in Ioi (K : ℝ), f x)
      = ∑' n : ℕ, ∫ x in (K : ℝ) + n..(K : ℝ) + n + 1, f x := hl.tsum_eq.symm
    _ ≤ ∑' n : ℕ, A / (((n + K : ℕ) : ℝ) ^ 2) := Summable.tsum_le_tsum hp hl.summable hsA
    _ = A * ∑' n : ℕ, 1 / (((n + K : ℕ) : ℝ) ^ 2) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      ring
    _ ≤ A * (1 / ((K : ℝ) - 1)) := mul_le_mul_of_nonneg_left (reciprocal_square_tail K hK) hA
    _ = _ := by ring

end TailPartition

/-! ### Copy of `PrimeTail385` -/

namespace PrimeTail

open Real MeasureTheory Set ComplexConjugate
open LeanLab.ExceptionalSet.U1539 (Sp Kfun eC)

noncomputable section

/-- The prime kernel integrand in P0082 page 357 display 6. -/
def integrand (P X Δ v α : ℝ) : ℂ :=
  Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * v))

/-- Reflection preserves the absolute integrand, independently of the phase frequency.
Source: P0082 page 356 display 3 and page 365, the two tails. -/
theorem norm_integrand_neg (P X Δ v x : ℝ) :
    ‖integrand P X Δ v (-x)‖ = ‖integrand P X Δ v x‖ := by
  have he (t : ℝ) : conj (eC t) = eC (-t) := BG2026.conj_eC t
  have hs : Sp P X (-x) = conj (Sp P X x) := by
    simp only [Sp, map_sum, map_mul, Complex.conj_ofReal, he, neg_mul]
  have hk : Kfun Δ (-x) = Kfun Δ x := by
    simp only [Kfun, mul_neg, Real.sinc_neg]
  simp only [integrand, norm_mul, norm_pow, U1539.norm_eC, mul_one]
  rw [hs, Complex.norm_conj, hk]

/-- The positive prime kernel tail at an integer cutoff, P0082 page 365 before display 24. -/
theorem positive_tail_le (P X Δ v : ℝ) (hX : 2 ≤ X) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (K : ℕ) (hK : 2 ≤ K) :
    (∫ α in Ioi (K : ℝ), ‖integrand P X Δ v α‖) ≤
      (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) := by
  let A := (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2)
  have hLX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hf : Integrable (fun α => ‖integrand P X Δ v α‖) :=
    (PrimeKernel264.total_integrable hΔ hΔ1 P X v).norm
  have hb (k : ℕ) (hk : K ≤ k) :
      (∫ α in (k : ℝ)..(k : ℝ) + 1, ‖integrand P X Δ v α‖) ≤ A / (k : ℝ) ^ 2 := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    simpa only [integrand, A, div_div, mul_pow, mul_assoc] using
      PrimeEnergy.prime_kernel_block_le P X Δ k v hX hΔ hΔ1 hk0
  simpa only [A, div_div] using
    TailPartition.integral_Ioi_le_of_blocks _ hf K hK A hA hb

/-- Both prime kernel tails at an integer cutoff, P0082 page 365 before display 24. -/
theorem outside_nat_tail_le (P X Δ v : ℝ) (hX : 2 ≤ X) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (K : ℕ) (hK : 2 ≤ K) :
    (∫ α in (Icc (-(K : ℝ)) (K : ℝ))ᶜ, ‖integrand P X Δ v α‖) ≤
      2 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) := by
  have hf : Integrable (fun α => ‖integrand P X Δ v α‖) :=
    (PrimeKernel264.total_integrable hΔ hΔ1 P X v).norm
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
  calc _ ≤ (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) +
      (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) := add_le_add h h
    _ = _ := by ring

/-- The explicit real cutoff tail bound in P0082 page 365 display 24. -/
theorem outside_real_tail_le (P X Δ v T : ℝ) (hX : 2 ≤ X) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hT : 4 ≤ T) :
    (∫ α in (Icc (-T) T)ᶜ, ‖integrand P X Δ v α‖) ≤
      4 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T) := by
  let K : ℕ := ⌊T⌋₊
  have hK : 2 ≤ K := Nat.le_floor (by norm_num; linarith)
  have hfloor : (K : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hlt : T < (K : ℝ) + 1 := Nat.lt_floor_add_one T
  have hcomp : T ≤ 2 * ((K : ℝ) - 1) := by linarith
  have hf : Integrable (fun α => ‖integrand P X Δ v α‖) :=
    (PrimeKernel264.total_integrable hΔ hΔ1 P X v).norm
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
    (show 0 ≤ 2 * (Real.log 4 * X * Real.log X) * (Δ * Real.pi ^ 2) by positivity)
  nlinarith only [hm]

/-- Restricting any integration set to the real cutoff loses at most the absolute tail.
Source: P0082 page 365 display 24. -/
theorem truncation_error_le (P X Δ v T : ℝ) (hX : 2 ≤ X) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hT : 4 ≤ T) (M : Set ℝ) :
    ‖(∫ α in M, integrand P X Δ v α) -
        (∫ α in M ∩ Icc (-T) T, integrand P X Δ v α)‖ ≤
      4 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T) := by
  have hf : Integrable (integrand P X Δ v) :=
    PrimeKernel264.total_integrable hΔ hΔ1 P X v
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

end

end PrimeTail

/-! ### Copy of `TailParameters385` -/

namespace TailParameters

open Real Filter Topology MeasureTheory Set
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE majorArcs)

/-- The larger logarithmic power absorbs the smaller exponential and logarithmic factor.
Source: P0082 page 365, display 24 with the parameters on pages 354, 355, 357 and 359. -/
theorem eventually_tail_factor (γ s δ κ : ℝ) (hγ : 0 < γ) (hs : s < γ) (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in atTop,
      8 * Real.log 4 * t ^ γ * Real.exp ((11 / 24 : ℝ) * κ * t ^ s) ≤
        Real.exp (6 * δ * t ^ γ) := by
  have hr : Tendsto (fun t : ℝ => ((11 / 24 : ℝ) * κ) * t ^ (s - γ)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by linarith : 0 < γ - s)).const_mul
      ((11 / 24 : ℝ) * κ) using 1 <;> congr 2 <;> ring
  have hb := hr.eventually_le_const (show 0 < 3 * δ by positivity)
  have hp := ((isLittleO_rpow_exp_pos_mul_atTop (1 : ℝ)
    (show 0 < 3 * δ by positivity)).const_mul_left (8 * Real.log 4)).bound
      (show (0 : ℝ) < 1 by norm_num)
  have hp' := (tendsto_rpow_atTop hγ).eventually hp
  filter_upwards [hb, hp', eventually_gt_atTop (0 : ℝ)] with t ht hp ht0
  have htγ := Real.rpow_pos_of_pos ht0 γ
  have hd : (11 / 24 : ℝ) * κ * t ^ s ≤ 3 * δ * t ^ γ := by
    rw [Real.rpow_sub ht0] at ht
    exact (div_le_iff₀ htγ).mp (by simpa only [mul_div_assoc] using ht)
  have hp2 : 8 * Real.log 4 * t ^ γ ≤ Real.exp (3 * δ * t ^ γ) := by
    simpa only [Real.rpow_one, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (show 0 ≤ 8 * Real.log 4 * t ^ γ by positivity),
      abs_of_pos (Real.exp_pos _)] using hp
  calc
    _ ≤ Real.exp (3 * δ * t ^ γ) * Real.exp (3 * δ * t ^ γ) :=
      mul_le_mul hp2 (Real.exp_le_exp.mpr hd) (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The paper parameters eventually put the explicit discarded tail below half the level.
Source: P0082 page 365 display 24 and pages 354, 355, 357 and 359, the parameter definitions. -/
theorem tail_parameters_eventually (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (δ κ : ℝ) (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      2 ≤ F γ N ∧ 4 ≤ F γ N ^ (6 * δ) ∧
      0 < calE γ κ N ^ (-(1 / 8 : ℝ)) ∧ calE γ κ N ^ (-(1 / 8 : ℝ)) < 1 ∧
      4 * (Real.log 4 * F γ N * Real.log (F γ N)) /
          (calE γ κ N ^ (-(1 / 8 : ℝ)) * Real.pi ^ 2 * F γ N ^ (6 * δ)) ≤
        F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) / 2 := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hF : Tendsto (fun N : ℕ => F γ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog)
  have hP : Tendsto (fun N : ℕ => F γ N ^ (6 * δ)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 6 * δ)).comp hF
  have hE : Tendsto (fun N : ℕ => calE γ κ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (((tendsto_rpow_atTop (by linarith : 0 < 3 - 2 * γ)).comp hlog).const_mul_atTop hκ)
  have hb := hlog.eventually
    (eventually_tail_factor γ (3 - 2 * γ) δ κ (by linarith) (by linarith) hδ)
  apply Filter.eventually_atTop.mp
  filter_upwards [hb, hF.eventually_ge_atTop 2, hP.eventually_ge_atTop 4,
    hE.eventually_ge_atTop 2] with N hb hX hP hE
  have hX0 : 0 < F γ N := Real.exp_pos _
  have hE0 : 0 < calE γ κ N := Real.exp_pos _
  have hd0 : 0 < calE γ κ N ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos hE0 _
  have hP0 : 0 < F γ N ^ (6 * δ) := Real.rpow_pos_of_pos hX0 _
  refine ⟨hX, hP, hd0,
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num), ?_⟩
  have hfac : 8 * Real.log 4 * Real.log (F γ N) * calE γ κ N ^ (11 / 24 : ℝ) ≤
      F γ N ^ (6 * δ) := by
    simp only [F, calE, Real.log_exp, ← Real.exp_mul]
    convert hb using 1 <;> congr 1 <;> ring
  have hid : calE γ κ N ^ (11 / 24 : ℝ) *
      (calE γ κ N ^ (-(1 / 3 : ℝ)) * calE γ κ N ^ (-(1 / 8 : ℝ))) = 1 := by
    rw [← Real.rpow_add hE0, ← Real.rpow_add hE0]
    norm_num
  have hc : 8 * Real.log 4 * Real.log (F γ N) ≤
      F γ N ^ (6 * δ) *
        (calE γ κ N ^ (-(1 / 3 : ℝ)) * calE γ κ N ^ (-(1 / 8 : ℝ))) := by
    calc
      _ = (8 * Real.log 4 * Real.log (F γ N) * calE γ κ N ^ (11 / 24 : ℝ)) *
          (calE γ κ N ^ (-(1 / 3 : ℝ)) * calE γ κ N ^ (-(1 / 8 : ℝ))) := by
        calc
          _ = (8 * Real.log 4 * Real.log (F γ N)) *
              (calE γ κ N ^ (11 / 24 : ℝ) *
                (calE γ κ N ^ (-(1 / 3 : ℝ)) * calE γ κ N ^ (-(1 / 8 : ℝ)))) := by
            rw [hid, mul_one]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfac (by positivity)
  have hpi : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hcpi := hc.trans (le_mul_of_one_le_right (by positivity) hpi)
  have hscaled := mul_le_mul_of_nonneg_left hcpi hX0.le
  apply (div_le_iff₀ (show 0 < calE γ κ N ^ (-(1 / 8 : ℝ)) * Real.pi ^ 2 *
    F γ N ^ (6 * δ) by positivity)).mpr
  nlinarith only [hscaled]

end TailParameters

end LeanLab.ExceptionalSet.TailSupplyJ200
