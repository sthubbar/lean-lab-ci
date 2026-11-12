import Mathlib
import LeanLab.ExceptionalSet.EvenMinorSupplyJ200

/-!
Sorry-free supply for the kernel moment of P0082 page 368, from the right side of display (32)
through the tail removal after (34) and the squaring (37), at the inner scale of
`LEAF_display29_steps`.
Source: P0082, J. Bruedern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378.

The files `TailPartition385`, `PrimeEnergy385`, `OddTail467` and `Moment385` hold the same
statements, but each of them imports `Decomp371a` and so reaches `DecompJ200`, which imports the
leaf file `LEAF_display29_steps`. The proofs are copied here verbatim, under this namespace, so
that the leaf file can use them without an import cycle.

AI wrote this Lean code. Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.KernelMomentSupplyJ200

open Real MeasureTheory Set Filter ComplexConjugate
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (Sp Kfun eC majorArcs calE Phie)
open LeanLab.ExceptionalSet.OddKernel467 (evenKernel)

/-- Every unit interval has the prime energy bound of P0082 page 368 before (33).
Copy of `PrimeEnergy385.prime_energy_le`, by periodicity from
`EvenMinorSupplyJ200.prime_energy_le`. -/
theorem prime_energy_shift_le (P X a : ℝ) (hX : 2 ≤ X) :
    (∫ α in a..a + 1, ‖Sp P X α‖ ^ 2) ≤ Real.log 4 * X * Real.log X := by
  have hp : Function.Periodic (fun α => ‖Sp P X α‖ ^ 2) 1 := by
    intro α
    dsimp only
    rw [MajorSupplyJ200.Sp_periodic P X α]
  have hi : (∫ α in a..a + 1, ‖Sp P X α‖ ^ 2) =
      (∫ α in (0 : ℝ)..1, ‖Sp P X α‖ ^ 2) := by
    simpa only [zero_add] using hp.intervalIntegral_add_eq a 0
  rw [hi]
  exact EvenMinorSupplyJ200.prime_energy_le P X hX

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
      mul_le_mul_of_nonneg_right (prime_energy_shift_le P X a hX) hB
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
    integral_Ioi_le_of_blocks _ hf K hK A hA hb

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

/-- Squaring finitely many integrals gives their Gram integral on the product measure.
Source: P0082 page 365, the expansion from display 25 to display 26. -/
theorem moment_gram (s : Finset ℕ) (A : Set ℝ) (f : ℕ → ℝ → ℂ)
    (hf : ∀ n ∈ s, IntegrableOn (f n) A) :
    (∑ n ∈ s, ‖∫ x in A, f n x‖ ^ 2) =
      (∫ z : ℝ × ℝ, ∑ n ∈ s, f n z.1 * conj (f n z.2)
        ∂(volume.restrict A).prod (volume.restrict A)).re := by
  have hfc (n : ℕ) (hn : n ∈ s) :
      Integrable (fun x => conj (f n x)) (volume.restrict A) := by
    have hi := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (hf n hn)
    exact hi.congr (Filter.Eventually.of_forall (fun x => Complex.conjCLE_apply (f n x)))
  rw [integral_finsetSum s (fun n hn => (hf n hn).mul_prod (hfc n hn))]
  have hprod (n : ℕ) :
      (∫ z : ℝ × ℝ, f n z.1 * conj (f n z.2)
        ∂(volume.restrict A).prod (volume.restrict A)) =
      (∫ x in A, f n x) * conj (∫ x in A, f n x) := by
    simpa only [integral_conj] using
      integral_prod_mul (μ := volume.restrict A) (ν := volume.restrict A)
        (f n) (fun x => conj (f n x))
  simp_rw [hprod, Complex.mul_conj']
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  norm_cast

/-- The absolute Gram integral bounds the finite squared integral moment.
Source: P0082 pages 365 and 366, displays 26 and 27. -/
theorem moment_le_absolute_gram (s : Finset ℕ) (A : Set ℝ) (f : ℕ → ℝ → ℂ)
    (hf : ∀ n ∈ s, IntegrableOn (f n) A) :
    (∑ n ∈ s, ‖∫ x in A, f n x‖ ^ 2) ≤
      ∫ z : ℝ × ℝ, ‖∑ n ∈ s, f n z.1 * conj (f n z.2)‖
        ∂(volume.restrict A).prod (volume.restrict A) := by
  rw [moment_gram s A f hf]
  exact (Complex.re_le_norm _).trans (norm_integral_le_integral_norm _)


/-- `e(a) e(b) = e(a + b)`. -/
theorem eC_mul_eC (a b : ℝ) : eC a * eC b = eC (a + b) := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Gram kernel of the squaring (37) on P0082 page 368 factors: the `n` sum of
`f_n(α) conj f_n(β)` with `f_n = S² K_e e(-α v_n)` has norm
`|S(α)² K_e(α)| |S(β)² K_e(β)| |Σ_n e((β - α) v_n)|`. -/
theorem norm_gram_sum (P X Δ : ℝ) (s : Finset ℕ) (v : ℕ → ℝ) (α β : ℝ) :
    ‖∑ n ∈ s, integrand P X Δ (v n) α * conj (integrand P X Δ (v n) β)‖ =
      ‖Sp P X α ^ 2 * evenKernel Δ α‖ * ‖Sp P X β ^ 2 * evenKernel Δ β‖ *
        ‖∑ n ∈ s, eC ((β - α) * v n)‖ := by
  have he (n : ℕ) : integrand P X Δ (v n) α * conj (integrand P X Δ (v n) β) =
      (Sp P X α ^ 2 * evenKernel Δ α) * conj (Sp P X β ^ 2 * evenKernel Δ β) *
        eC ((β - α) * v n) := by
    have hc (t : ℝ) : conj (eC t) = eC (-t) := BG2026.conj_eC t
    simp only [integrand, map_mul, hc]
    have h2 : eC (-(α * v n)) * eC (-(-(β * v n))) = eC ((β - α) * v n) := by
      rw [eC_mul_eC]; congr 1; ring
    rw [← h2]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, norm_mul, norm_mul, Complex.norm_conj]

/-- If `‖a - b‖ ≤ τ` then `‖a‖² ≤ 2‖b‖² + 2τ²`. -/
theorem norm_sq_le_of_sub (a b : ℂ) (τ : ℝ) (h : ‖a - b‖ ≤ τ) :
    ‖a‖ ^ 2 ≤ 2 * ‖b‖ ^ 2 + 2 * τ ^ 2 := by
  have h1 : ‖a‖ ≤ ‖b‖ + τ := by
    have h3 : ‖a‖ ≤ ‖b‖ + ‖a - b‖ := by
      calc ‖a‖ = ‖b + (a - b)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith
  have h0 : 0 ≤ ‖a‖ := norm_nonneg _
  have hb : 0 ≤ ‖b‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖b‖ - τ)]

/-- P0082 page 368, the tail removal after (34) and the squaring (37) for any finite index
set `s`, any phases `v n`, any integration set `M` and any cutoff `T ≥ 4`: the second moment
of the kernel integrals is at most twice the absolute double integral of
`|S(α)² K_e(α)| |S(β)² K_e(β)| |Σ_n e((β - α) v_n)|` over `(M ∩ [-T, T])²` plus twice
`#s` times the square of the tail bound `8 log 4 X log X / (Δ π² T)`. -/
theorem moment_tail_gram (P X Δ T : ℝ) (hX : 2 ≤ X) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hT : 4 ≤ T) (M : Set ℝ) (s : Finset ℕ) (v : ℕ → ℝ) :
    (∑ n ∈ s, ‖∫ α in M, integrand P X Δ (v n) α‖ ^ 2) ≤
      2 * (∫ z : ℝ × ℝ, ‖Sp P X z.1 ^ 2 * evenKernel Δ z.1‖ *
          ‖Sp P X z.2 ^ 2 * evenKernel Δ z.2‖ * ‖∑ n ∈ s, eC ((z.2 - z.1) * v n)‖
          ∂(volume.restrict (M ∩ Icc (-T) T)).prod (volume.restrict (M ∩ Icc (-T) T))) +
        2 * s.card * (8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T)) ^ 2 := by
  set τ := 8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T)
  set A := M ∩ Icc (-T) T
  have hterm (n : ℕ) : ‖∫ α in M, integrand P X Δ (v n) α‖ ^ 2 ≤
      2 * ‖∫ α in A, integrand P X Δ (v n) α‖ ^ 2 + 2 * τ ^ 2 :=
    norm_sq_le_of_sub _ _ τ (truncation_error_le P X Δ (v n) T hX hΔ hΔ1 hT M)
  have hg := moment_le_absolute_gram s A (fun n => integrand P X Δ (v n))
    (fun n _ => (total_integrable P X Δ (v n) hΔ hΔ1).integrableOn)
  simp_rw [norm_gram_sum] at hg
  calc (∑ n ∈ s, ‖∫ α in M, integrand P X Δ (v n) α‖ ^ 2)
      ≤ ∑ n ∈ s, (2 * ‖∫ α in A, integrand P X Δ (v n) α‖ ^ 2 + 2 * τ ^ 2) :=
        Finset.sum_le_sum (fun n _ => hterm n)
    _ = 2 * (∑ n ∈ s, ‖∫ α in A, integrand P X Δ (v n) α‖ ^ 2) + 2 * s.card * τ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ _ := by gcongr

/-- `ℰ = exp(κ (log N)^{3-2γ}) ≥ 4` for large `N`, so the cutoff `Y = ℰ` is admissible in
`truncation_error_le`. -/
theorem four_le_calE (γ κ : ℝ) (h2 : γ < 3 / 2) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 4 ≤ calE γ κ N := by
  have ha : 0 < 3 - 2 * γ := by linarith
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_atTop ha).comp hlog
  apply eventually_atTop.mp
  filter_upwards [ht.eventually (eventually_ge_atTop (2 / κ))] with N hN
  change 2 / κ ≤ Real.log N ^ (3 - 2 * γ) at hN
  have h2k : 2 ≤ κ * Real.log N ^ (3 - 2 * γ) := by
    rw [div_le_iff₀ hκ] at hN
    linarith
  have he : (4 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (1 : ℝ)
    have h := Real.exp_one_gt_d9
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  exact he.trans (Real.exp_le_exp.mpr h2k)

/-- The exponent arithmetic of the tail term at the inner scale: with `Δ = ℰ^{-2/3}`, cutoff
`ℰ ≥ 1` and `(log X)² ≤ ℰ^{1/4}`, the squared tail bound is at most
`64 (log 4)² X² ℰ^{-1/3}`. -/
theorem tail_sq_le (X E : ℝ) (hX : 2 ≤ X) (hE : 1 ≤ E)
    (hlog : Real.log X ^ 2 ≤ E ^ (1 / 4 : ℝ)) :
    (8 * (Real.log 4 * X * Real.log X) / (E ^ (-(2 / 3 : ℝ)) * Real.pi ^ 2 * E)) ^ 2 ≤
      64 * Real.log 4 ^ 2 * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by
  have hE0 : 0 < E := by linarith
  set u := E ^ (1 / 3 : ℝ) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hE0 _
  have hden : E ^ (-(2 / 3 : ℝ)) * E = u := by
    rw [hu]
    conv_lhs => rw [show E ^ (-(2 / 3 : ℝ)) * E = E ^ (-(2 / 3 : ℝ)) * E ^ (1 : ℝ) by
      rw [Real.rpow_one]]
    rw [← Real.rpow_add hE0]
    norm_num
  have hneg : E ^ (-(1 / 3 : ℝ)) = u⁻¹ := by rw [hu, Real.rpow_neg hE0.le]
  have hq : E ^ (1 / 4 : ℝ) ≤ u :=
    Real.rpow_le_rpow_of_exponent_le hE (by norm_num)
  have hL : Real.log X ^ 2 ≤ u := hlog.trans hq
  have hpi : 1 ≤ Real.pi ^ 2 := by
    have := Real.pi_gt_three
    nlinarith
  rw [hneg, show E ^ (-(2 / 3 : ℝ)) * Real.pi ^ 2 * E = Real.pi ^ 2 * u by rw [← hden]; ring]
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hX0 : 0 ≤ X := by linarith
  rw [div_pow, mul_pow, mul_pow, mul_pow, mul_pow]
  rw [div_le_iff₀ (by positivity)]
  have hA : 0 ≤ 8 ^ 2 * Real.log 4 ^ 2 * X ^ 2 := by positivity
  have hpi4 : 1 ≤ (Real.pi ^ 2) ^ 2 := by nlinarith
  calc 8 ^ 2 * (Real.log 4 ^ 2 * X ^ 2 * Real.log X ^ 2)
      = (8 ^ 2 * Real.log 4 ^ 2 * X ^ 2) * Real.log X ^ 2 := by ring
    _ ≤ (8 ^ 2 * Real.log 4 ^ 2 * X ^ 2) * u := mul_le_mul_of_nonneg_left hL hA
    _ ≤ (8 ^ 2 * Real.log 4 ^ 2 * X ^ 2) * u * (Real.pi ^ 2) ^ 2 :=
        le_mul_of_one_le_right (by positivity) hpi4
    _ = 64 * Real.log 4 ^ 2 * X ^ 2 * u⁻¹ * ((Real.pi ^ 2) ^ 2 * u ^ 2) := by
        field_simp
        ring

/- The next three theorems are verbatim copies of `Decomp483d`, which reaches `DecompJ200`. -/

/-- P0082 page365 before display24 and page369 display38. A symmetric
integer interval contains twice its radius many periods of prime energy. -/
theorem prime_energy_symmetric_nat (P X : ℝ) (hX : 2 ≤ X) (K : ℕ) :
    (∫ α in (-(K : ℝ))..(K : ℝ), ‖Sp P X α‖ ^ 2) ≤
      2 * K * (Real.log 4 * X * Real.log X) := by
  have hc : Continuous (fun α => ‖Sp P X α‖ ^ 2) := by unfold Sp U1539.eC; fun_prop
  have hp : Function.Periodic (fun α => ‖Sp P X α‖ ^ 2) 1 := by
    intro α
    dsimp only
    rw [MajorSupplyJ200.Sp_periodic P X α]
  have he := hp.intervalIntegral_add_zsmul_eq (2 * (K : ℤ)) (-(K : ℝ))
    (fun a b => hc.intervalIntegrable a b)
  have hend : -(K : ℝ) + (2 * (K : ℤ)) • (1 : ℝ) = (K : ℝ) := by
    simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    ring
  rw [hend] at he
  calc _ = (2 * (K : ℤ)) • (∫ α in (-(K : ℝ))..(-(K : ℝ)) + 1, ‖Sp P X α‖ ^ 2) := he
    _ = 2 * (K : ℝ) * (∫ α in (-(K : ℝ))..(-(K : ℝ)) + 1, ‖Sp P X α‖ ^ 2) := by
      simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left (prime_energy_shift_le P X (-(K : ℝ)) hX)
      (by positivity)

/-- P0082 page369 display38, auxiliary explicit cutoff bound. The compact
part uses the shifted kernel bound one. The two tails use  -/
theorem shifted_weighted_mass_cutoff (P X Δ : ℝ) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (K : ℕ) (hK : 2 ≤ K) :
    (∫ α : ℝ, ‖Sp P X α ^ 2 * OddKernel467.evenKernel Δ α‖) ≤
      2 * K * (Real.log 4 * X * Real.log X) +
      4 * (Real.log 4 * X * Real.log X) /
        (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) := by
  let A := Real.log 4 * X * Real.log X
  let g := fun α : ℝ => ‖Sp P X α ^ 2 * OddKernel467.evenKernel Δ α‖
  have hg : Integrable g := by
    simpa only [g, integrand, norm_mul, U1539.norm_eC, mul_one] using
      (total_integrable P X Δ 0 hΔ hΔ1).norm
  have hc : Continuous (fun α : ℝ => ‖Sp P X α‖ ^ 2) := by unfold Sp U1539.eC; fun_prop
  have hgc : Continuous g := by
    exact (((by unfold Sp U1539.eC; fun_prop : Continuous (Sp P X)).pow 2).mul
      (OddKernel467.evenKernel_continuous Δ)).norm
  have hk (α : ℝ) : ‖OddKernel467.evenKernel Δ α‖ ≤ 1 := by
    rw [norm_evenKernel]
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
    simpa only [g, A, integrand, norm_mul, U1539.norm_eC, mul_one] using
      outside_nat_tail_le P X Δ 0 hX hΔ hΔ1 K hK
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


/-- `ℰ(2κ)^{-2/3} = ℰ(κ)^{-4/3}`, the threshold `N ℰ'^{-2/3}` of page 369 at `ℰ' = ℰ(2κ)`. -/
theorem calE_two_mul_twothirds (γ κ : ℝ) (N : ℕ) :
    calE γ (2 * κ) N ^ (-(2 / 3 : ℝ)) = calE γ κ N ^ (-(4 / 3 : ℝ)) := by
  simp only [calE, ← Real.exp_mul]
  congr 1
  ring

/-- P0082 page 369, the split at the size of `Φ_e`: for nonnegative `g` and `φ` and a threshold
`T₀ ≥ 0`, the double integral of `g(α) g(β) φ(α, β)` is at most `T₀ (∫ g)²` plus the part where
`φ > T₀`. -/
theorem gram_split (μ : Measure ℝ) [SFinite μ] (g : ℝ → ℝ) (φ : ℝ × ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x)
    (hφm : Measurable φ) (hgi : Integrable g μ)
    (hint : Integrable (fun z : ℝ × ℝ => g z.1 * g z.2 * φ z) (μ.prod μ))
    (T₀ : ℝ) (hT₀ : 0 ≤ T₀) :
    (∫ z, g z.1 * g z.2 * φ z ∂μ.prod μ) ≤
      T₀ * (∫ x, g x ∂μ) ^ 2 +
        ∫ z, {z : ℝ × ℝ | T₀ < φ z}.indicator (fun z => g z.1 * g z.2 * φ z) z ∂μ.prod μ := by
  have hms : MeasurableSet {z : ℝ × ℝ | T₀ < φ z} := measurableSet_lt measurable_const hφm
  have hgg : Integrable (fun z : ℝ × ℝ => g z.1 * g z.2) (μ.prod μ) := hgi.mul_prod hgi
  have hsplit : (∫ z, g z.1 * g z.2 * φ z ∂μ.prod μ) ≤
      ∫ z, (T₀ * (g z.1 * g z.2) +
        {z : ℝ × ℝ | T₀ < φ z}.indicator (fun z => g z.1 * g z.2 * φ z) z) ∂μ.prod μ := by
    apply integral_mono hint ((hgg.const_mul T₀).add (hint.indicator hms))
    intro z
    have hp : 0 ≤ g z.1 * g z.2 := mul_nonneg (hg0 _) (hg0 _)
    show g z.1 * g z.2 * φ z ≤ T₀ * (g z.1 * g z.2) +
      {z : ℝ × ℝ | T₀ < φ z}.indicator (fun z => g z.1 * g z.2 * φ z) z
    by_cases hz : T₀ < φ z
    · rw [Set.indicator_of_mem (show z ∈ {z : ℝ × ℝ | T₀ < φ z} from hz)]
      have : 0 ≤ T₀ * (g z.1 * g z.2) := mul_nonneg hT₀ hp
      linarith
    · rw [Set.indicator_of_notMem (show z ∉ {z : ℝ × ℝ | T₀ < φ z} from hz), add_zero]
      have hz' : φ z ≤ T₀ := le_of_not_gt hz
      nlinarith
  rw [integral_add (hgg.const_mul T₀) (hint.indicator hms), integral_const_mul,
    integral_prod_mul (μ := μ) (ν := μ) g g] at hsplit
  simpa only [sq] using hsplit

/-- The exponent arithmetic of the small `Φ_e` part on page 369: with `Δ = ℰ^{-2/3}`, the
threshold `N ℰ^{-4/3}`, an `L¹` mass at most `7 log 4 X log X / Δ^{1/2}` and
`(log X)² ≤ ℰ^{1/4}`, the small part is at most `49 (log 4)² N X² ℰ^{-1/3}`. -/
theorem small_part_le (N X E L : ℝ) (hN : 0 ≤ N) (hX : 2 ≤ X) (hE : 1 ≤ E)
    (hlog : Real.log X ^ 2 ≤ E ^ (1 / 4 : ℝ)) (hL0 : 0 ≤ L)
    (hL : L ≤ 7 * (Real.log 4 * X * Real.log X) / Real.sqrt (E ^ (-(2 / 3 : ℝ)))) :
    N * E ^ (-(4 / 3 : ℝ)) * L ^ 2 ≤ 49 * Real.log 4 ^ 2 * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by
  have hE0 : 0 < E := by linarith
  set u := E ^ (1 / 3 : ℝ) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hE0 _
  have hpow (r : ℝ) : E ^ (r / 3) = u ^ r := by
    rw [hu, ← Real.rpow_mul hE0.le]; congr 1; ring
  have h43 : E ^ (-(4 / 3 : ℝ)) = (u ^ 4)⁻¹ := by
    rw [show (-(4 / 3 : ℝ)) = (-4) / 3 by norm_num, hpow, Real.rpow_neg hu0.le]
    norm_cast
  have h13 : E ^ (-(1 / 3 : ℝ)) = u⁻¹ := by rw [hu, Real.rpow_neg hE0.le]
  have h23 : Real.sqrt (E ^ (-(2 / 3 : ℝ))) = u⁻¹ := by
    rw [show (-(2 / 3 : ℝ)) = (-2) / 3 by norm_num, hpow, Real.rpow_neg hu0.le,
      Real.sqrt_inv]
    norm_cast
    rw [Real.sqrt_sq hu0.le]
  have hq : E ^ (1 / 4 : ℝ) ≤ u := Real.rpow_le_rpow_of_exponent_le hE (by norm_num)
  have hlX : Real.log X ^ 2 ≤ u := hlog.trans hq
  rw [h23, div_inv_eq_mul] at hL
  rw [h43, h13]
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hX0 : 0 ≤ X := by linarith
  have hLX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hL2 : L ^ 2 ≤ (7 * (Real.log 4 * X * Real.log X) * u) ^ 2 :=
    pow_le_pow_left₀ hL0 hL 2
  have hA : 0 ≤ 49 * Real.log 4 ^ 2 * N * X ^ 2 := by positivity
  calc N * (u ^ 4)⁻¹ * L ^ 2 ≤ N * (u ^ 4)⁻¹ * (7 * (Real.log 4 * X * Real.log X) * u) ^ 2 :=
        mul_le_mul_of_nonneg_left hL2 (by positivity)
    _ = (49 * Real.log 4 ^ 2 * N * X ^ 2) * Real.log X ^ 2 * (u ^ 2)⁻¹ := by
        field_simp
        ring
    _ ≤ (49 * Real.log 4 ^ 2 * N * X ^ 2) * u * (u ^ 2)⁻¹ := by gcongr
    _ = _ := by field_simp

end LeanLab.ExceptionalSet.KernelMomentSupplyJ200
