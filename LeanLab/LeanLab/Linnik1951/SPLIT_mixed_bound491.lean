/-
Split of mixed_bound491 into four leaves. The mixed character term of equation
3.4 is cut into the count of nonprincipal characters at one modulus, the
principal conjugate Gauss coefficient, the mixed character mass over the local
window at the sixth power of the logarithm, and the estimate for one ordered
character pair. The assembly at the end has no sorry and does not use the split
statement.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp491b
import LeanLab.ChebyshevExplicit.PiUpperSharp

namespace LeanLab.Linnik1951

open Finset MeasureTheory
open Filter
open scoped Topology

/-- LEAF. Counting step of equation 5.5. The number of nonprincipal characters
at a positive modulus is at most the totient of that modulus. At modulus one the
filtered set is empty, so the bound reads zero at most one. No estimate on the
characters themselves and no integral occurs here. -/
theorem mixed_card491 (q : ℕ) [NeZero q] :
    (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card ≤ q.totient := by
  classical
  have hle : (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card ≤
      (univ : Finset (DirichletCharacter ℂ q)).card := Finset.card_filter_le _ _
  rw [Finset.card_univ] at hle
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  omega

/-- LEAF. Modulus step of equation 5.5. The conjugate Gauss coefficient of the
principal character at a positive modulus is the Moebius value at the modulus in
absolute value, hence has norm at most one. It carries no frequency, no size of
N, and no character other than the principal one. -/
theorem mixed_principal_gauss491 (q : ℕ) (hq : 1 ≤ q) :
    ‖conjugateGauss491 q (1 : DirichletCharacter ℂ q)‖ ≤ 1 := by
  have hone : conjugateGauss491 q (1 : DirichletCharacter ℂ q) =
      star (signedRamanujan491 q 1) := by
    unfold conjugateGauss491 signedRamanujan491
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    have hcop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
    have hunit : IsUnit ((a : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr hcop
    rw [MulChar.one_apply hunit, one_mul]
    congr 1
    push_cast
    ring
  rw [hone, norm_star, signedRamanujan_toNat491 q 1 (by norm_num)]
  have hto : (Int.toNat 1 : ℕ) = 1 := rfl
  rw [hto,
    LeanLab.Perelli1996.Ramanujan103.ramanujanSum_coprime q 1 (by omega)
      (Nat.coprime_one_right q)]
  have hmu : ((|ArithmeticFunction.moebius q| : ℤ) : ℝ) ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
  calc ‖((ArithmeticFunction.moebius q : ℤ) : ℂ)‖
      = |((ArithmeticFunction.moebius q : ℤ) : ℝ)| := Complex.norm_intCast _
    _ = ((|ArithmeticFunction.moebius q| : ℤ) : ℝ) := by rw [Int.cast_abs]
    _ ≤ 1 := hmu

/-! ### Transplanted machinery (from SPLIT_doubled_system_expansion435) -/

private lemma integral_exp_int_freq (k : ℤ) (a : ℝ) :
    (∫ β in a..(a + 1),
        Complex.exp ((-(2 * Real.pi * β * (k : ℝ)) : ℝ) * Complex.I)) =
      if k = 0 then 1 else 0 := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    simp
  · have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have hc : (((-(2 * Real.pi * (k : ℝ)) : ℝ)) : ℂ) * Complex.I ≠ 0 := by
      simp [Complex.I_ne_zero, hpi, hk']
    rw [if_neg hk]
    have hform : ∀ β : ℝ, Complex.exp ((-(2 * Real.pi * β * (k : ℝ)) : ℝ) * Complex.I)
        = Complex.exp ((((-(2 * Real.pi * (k : ℝ)) : ℝ)) : ℂ) * Complex.I * β) := by
      intro β
      congr 1
      push_cast
      ring
    simp_rw [hform]
    rw [integral_exp_mul_complex hc]
    have hper : Complex.exp ((((-(2 * Real.pi * (k : ℝ)) : ℝ)) : ℂ) * Complex.I) = 1 := by
      have h := Complex.exp_int_mul_two_pi_mul_I (-k)
      have hcast : ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
          = (((-(2 * Real.pi * (k : ℝ)) : ℝ)) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [hcast] at h
      exact h
    have hend : Complex.exp ((((-(2 * Real.pi * (k : ℝ)) : ℝ)) : ℂ) * Complex.I * ((a + 1 : ℝ) : ℂ))
        = Complex.exp ((((-(2 * Real.pi * (k : ℝ)) : ℝ)) : ℂ) * Complex.I * (a : ℂ)) := by
      rw [show ((((-(2 * Real.pi * (k : ℝ)) : ℝ)) : ℂ) * Complex.I * ((a + 1 : ℝ) : ℂ))
          = ((((-(2 * Real.pi * (k : ℝ)) : ℝ)) : ℂ) * Complex.I * (a : ℂ))
            + ((((-(2 * Real.pi * (k : ℝ)) : ℝ)) : ℂ) * Complex.I) by
        push_cast
        ring,
        Complex.exp_add, hper, mul_one]
    rw [hend, sub_self, zero_div]

/-- The frequency-`k` exponential is continuous. -/
private lemma continuous_exp_int_freq (k : ℤ) :
    Continuous fun β : ℝ =>
      Complex.exp ((-(2 * Real.pi * β * (k : ℝ)) : ℝ) * Complex.I) := by
  have hin : Continuous fun β : ℝ => (((-(2 * Real.pi * β * (k : ℝ)) : ℝ)) : ℂ) * Complex.I := by
    fun_prop
  exact Complex.continuous_exp.comp hin

private lemma intervalIntegrable_exp_int_freq (k : ℤ) (a : ℝ) :
    IntervalIntegrable (fun β : ℝ =>
      Complex.exp ((-(2 * Real.pi * β * (k : ℝ)) : ℝ) * Complex.I)) volume a (a + 1) :=
  (continuous_exp_int_freq k).intervalIntegrable _ _

/-- **Finite Parseval.** The mean square of a finite exponential sum over any
interval of length one is the sum of the squared coefficients. -/
private lemma integral_normSq_finset_exp (b : ℕ → ℂ) (M : ℕ) (a : ℝ) :
    (∫ β in a..(a + 1),
        ‖∑ m ∈ Finset.range M,
          b m * Complex.exp ((-(2 * Real.pi * β * (m : ℝ)) : ℝ) * Complex.I)‖ ^ 2) =
      ∑ m ∈ Finset.range M, ‖b m‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have hexp : ∀ β : ℝ,
      ((‖∑ m ∈ Finset.range M,
          b m * Complex.exp ((-(2 * Real.pi * β * (m : ℝ)) : ℝ) * Complex.I)‖ ^ 2 : ℝ) : ℂ)
        = ∑ m ∈ Finset.range M, ∑ m' ∈ Finset.range M,
            b m * (starRingEnd ℂ) (b m') *
              Complex.exp ((-(2 * Real.pi * β * (((m : ℤ) - (m' : ℤ) : ℤ) : ℝ)) : ℝ) *
                Complex.I) := by
    intro β
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
    have hconj : (starRingEnd ℂ)
        (Complex.exp ((-(2 * Real.pi * β * (m' : ℝ)) : ℝ) * Complex.I))
        = Complex.exp (((2 * Real.pi * β * (m' : ℝ)) : ℝ) * Complex.I) := by
      rw [← Complex.exp_conj]
      congr 1
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
      push_cast
      ring
    rw [map_mul, hconj]
    have hE : Complex.exp ((-(2 * Real.pi * β * (m : ℝ)) : ℝ) * Complex.I) *
        Complex.exp (((2 * Real.pi * β * (m' : ℝ)) : ℝ) * Complex.I)
        = Complex.exp ((-(2 * Real.pi * β * (((m : ℤ) - (m' : ℤ) : ℤ) : ℝ)) : ℝ) *
            Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc b m * Complex.exp ((-(2 * Real.pi * β * (m : ℝ)) : ℝ) * Complex.I) *
          ((starRingEnd ℂ) (b m') *
            Complex.exp (((2 * Real.pi * β * (m' : ℝ)) : ℝ) * Complex.I))
        = b m * (starRingEnd ℂ) (b m') *
            (Complex.exp ((-(2 * Real.pi * β * (m : ℝ)) : ℝ) * Complex.I) *
              Complex.exp (((2 * Real.pi * β * (m' : ℝ)) : ℝ) * Complex.I)) := by ring
      _ = _ := by rw [hE]
  simp_rw [hexp]
  have hint : ∀ (m m' : ℕ), IntervalIntegrable (fun β : ℝ =>
      b m * (starRingEnd ℂ) (b m') *
        Complex.exp ((-(2 * Real.pi * β * (((m : ℤ) - (m' : ℤ) : ℤ) : ℝ)) : ℝ) * Complex.I))
      volume a (a + 1) := fun m m' =>
    (continuous_const.mul (continuous_exp_int_freq _)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum (f := fun m β => ∑ m' ∈ Finset.range M,
      b m * (starRingEnd ℂ) (b m') *
        Complex.exp ((-(2 * Real.pi * β * (((m : ℤ) - (m' : ℤ) : ℤ) : ℝ)) : ℝ) * Complex.I))
    fun m _ => (continuous_finsetSum _ fun m' _ =>
      (continuous_const.mul (continuous_exp_int_freq _))).intervalIntegrable _ _]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [intervalIntegral.integral_finsetSum (f := fun m' β =>
      b m * (starRingEnd ℂ) (b m') *
        Complex.exp ((-(2 * Real.pi * β * (((m : ℤ) - (m' : ℤ) : ℤ) : ℝ)) : ℝ) * Complex.I))
    fun m' _ => hint m m']
  simp_rw [intervalIntegral.integral_const_mul, integral_exp_int_freq]
  rw [Finset.sum_eq_single m]
  · simp only [sub_self, if_true, mul_one]
    rw [Complex.mul_conj', Complex.ofReal_pow]
  · intro m' _ hm'
    have hsub : (((m : ℤ) - (m' : ℤ) : ℤ)) ≠ 0 := by
      intro h
      apply hm'
      omega
    simp [hsub]
  · intro h
    exact absurd hm h
/-! ### Summability of the damped exponential series -/

private lemma summable_exp_decay (N : ℕ) (hN : 0 < N) :
    Summable fun n : ℕ => Real.exp (-((n : ℝ) / N)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : Real.exp (-(1 / (N : ℝ))) < 1 := by
    have h := Real.exp_lt_exp (x := -(1 / (N : ℝ))) (y := 0) |>.mpr (by
      have h1 : (0 : ℝ) < 1 / (N : ℝ) := by positivity
      linarith)
    rwa [Real.exp_zero] at h
  refine (summable_geometric_of_lt_one (Real.exp_pos _).le hq).congr (fun n => ?_)
  rw [← Real.exp_nat_mul]
  congr 1
  have hNne : (N : ℝ) ≠ 0 := by positivity
  field_simp

private lemma exp_decay_le_one (N : ℕ) (hN : 0 < N) (n : ℕ) :
    Real.exp (-((n : ℝ) / N)) ≤ 1 := by
  have hq : Real.exp (-((n : ℝ) / N)) ≤ Real.exp 0 := by
    rw [Real.exp_le_exp]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have h2 : (0 : ℝ) ≤ (n : ℝ) / N := by positivity
    linarith
  rwa [Real.exp_zero] at hq

private lemma summable_prime_indicator (b : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n)
    (hb : Summable b) :
    Summable fun n : ℕ => if n.Prime then b n else 0 :=
  hb.of_nonneg_of_le (g := fun n : ℕ => if n.Prime then b n else 0)
    (fun n => by split <;> simp [hb0 n]) (fun n => by split <;> simp [hb0 n])

/-- The unit-modulus exponential of a real frequency. -/
private lemma norm_exp_unit (β x : ℝ) :
    ‖Complex.exp ((-(2 * Real.pi * β * x) : ℝ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

private lemma norm_mul_unit (b : ℂ) (n : ℕ) (β : ℝ) :
    ‖b * Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖ = ‖b‖ := by
  rw [norm_mul, norm_exp_unit, mul_one]

/-- Continuity of the damped exponential sum. -/
private lemma continuous_tsum_exp (b : ℕ → ℂ) (hb : Summable fun n => ‖b n‖) :
    Continuous fun z : ℝ => ∑' n : ℕ,
      b n * Complex.exp ((-(2 * Real.pi * z * (n : ℝ)) : ℝ) * Complex.I) := by
  refine continuous_tsum (u := fun n : ℕ => ‖b n‖)
    (f := fun n z => b n * Complex.exp ((-(2 * Real.pi * z * (n : ℝ)) : ℝ) * Complex.I))
    (fun n => ?_) hb (fun n z => ?_)
  · exact continuous_const.mul (continuous_exp_int_freq (n : ℤ))
  · rw [norm_mul_unit]

/-- **Infinite square mass.** For summable complex coefficients of modulus at most
one, the mean square of the exponential sum over any interval of length one is at
most the sum of the squared moduli. -/
private lemma integral_normSq_tsum_le (b : ℕ → ℂ) (hb1 : ∀ n, ‖b n‖ ≤ 1)
    (hb : Summable fun n => ‖b n‖) (a : ℝ) :
    (∫ β in a..(a + 1),
        ‖∑' n : ℕ, b n *
          Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖ ^ 2) ≤
      ∑' n : ℕ, ‖b n‖ ^ 2 := by
  classical
  have hbs : Summable b := hb.of_norm
  have hSd0 : (0 : ℝ) ≤ ∑' n : ℕ, ‖b n‖ := tsum_nonneg fun n => norm_nonneg _
  have hbs2 : Summable fun n : ℕ => ‖b n‖ ^ 2 :=
    hb.of_nonneg_of_le (g := fun n : ℕ => ‖b n‖ ^ 2) (fun n => sq_nonneg _) (fun n => by
      rw [sq]
      exact mul_le_of_le_one_right (norm_nonneg _) (hb1 n))
  have hcont := continuous_tsum_exp b hb
  set Sd : ℝ := ∑' n : ℕ, ‖b n‖ with hSS
  have hSd0' : (0 : ℝ) ≤ Sd := by rw [hSS]; exact hSd0
  have hsM0 : ∀ (M : ℕ) (β : ℝ),
      ‖∑ n ∈ Finset.range M, b n *
          Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖ ≤ Sd := by
    intro M β
    have h1 : ‖∑ n ∈ Finset.range M, b n *
        Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖ ≤
        ∑ n ∈ Finset.range M, ‖b n‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun n _ => norm_mul_unit (b n) n β
    have h2 : ∑ n ∈ Finset.range M, ‖b n‖ ≤ Sd := by
      rw [hSS]
      exact hb.sum_le_tsum _ (fun i _ => norm_nonneg _)
    exact h1.trans h2
  have htail : ∀ (M : ℕ) (β : ℝ),
      ‖(∑' n : ℕ, b n * Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)) -
          ∑ n ∈ Finset.range M, b n *
            Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖ ≤
        ∑' i : ℕ, ‖b (i + M)‖ := by
    intro M β
    have hshift : Summable fun i : ℕ => ‖b (i + M)‖ :=
      hb.comp_injective (f := fun n : ℕ => ‖b n‖) (fun x y hxy => Nat.add_right_cancel hxy)
    have hx : Summable fun n : ℕ =>
        b n * Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I) :=
      hb.of_norm_bounded (g := fun n : ℕ => ‖b n‖) (fun n => by rw [norm_mul_unit])
    have heq : (∑' n : ℕ, b n * Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)) -
        ∑ n ∈ Finset.range M, b n *
          Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I) =
        ∑' i : ℕ, b (i + M) *
          Complex.exp ((-(2 * Real.pi * β * (((i + M : ℕ) : ℝ))) : ℝ) * Complex.I) := by
      have h := hx.sum_add_tsum_nat_add M
      rw [← h]
      ring
    rw [heq]
    have hsum2 : Summable fun i : ℕ =>
        ‖b (i + M) * Complex.exp ((-(2 * Real.pi * β * (((i + M : ℕ) : ℝ))) : ℝ) * Complex.I)‖ :=
      hx.norm.comp_injective (f := fun n : ℕ =>
          ‖b n * Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖)
        (fun x y hxy => Nat.add_right_cancel hxy)
    refine (norm_tsum_le_tsum_norm hsum2).trans ?_
    refine hsum2.tsum_le_tsum (fun i => ?_) hshift
    rw [norm_mul_unit]
  have hFpt : ∀ (M : ℕ) (β : ℝ),
      ‖∑' n : ℕ, b n * Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖ ≤
        ‖∑ n ∈ Finset.range M, b n *
            Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖ +
          ∑' i : ℕ, ‖b (i + M)‖ := by
    intro M β
    have h1 := htail M β
    have h2 : (∑' n : ℕ, b n * Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)) =
        (∑ n ∈ Finset.range M, b n *
            Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)) +
          ((∑' n : ℕ, b n * Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)) -
            ∑ n ∈ Finset.range M, b n *
              Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)) := by ring
    calc ‖∑' n : ℕ, b n * Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖
        = ‖(∑ n ∈ Finset.range M, b n *
              Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)) +
            ((∑' n : ℕ, b n * Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)) -
              ∑ n ∈ Finset.range M, b n *
                Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I))‖ := by
          conv_lhs => rw [h2]
      _ ≤ ‖∑ n ∈ Finset.range M, b n *
              Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖ +
            ‖(∑' n : ℕ, b n * Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)) -
              ∑ n ∈ Finset.range M, b n *
                Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl h1
  -- the estimate at each truncation
  have hbound : ∀ M : ℕ,
      (∫ β in a..(a + 1),
        ‖∑' n : ℕ, b n *
          Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖ ^ 2) ≤
      (∑ n ∈ Finset.range M, ‖b n‖ ^ 2) +
        (2 * (∑' i : ℕ, ‖b (i + M)‖) * Sd + (∑' i : ℕ, ‖b (i + M)‖) ^ 2) := by
    intro M
    set V : ℝ := ∑' i : ℕ, ‖b (i + M)‖ with hV
    have hV0 : 0 ≤ V := tsum_nonneg fun i => norm_nonneg _
    set sMv : ℝ → ℂ := fun β => ∑ n ∈ Finset.range M,
      b n * Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I) with hsMdef
    have hcM : Continuous sMv := continuous_finsetSum _ fun n _ =>
      continuous_const.mul (continuous_exp_int_freq (n : ℤ))
    have hpt2 : ∀ β : ℝ, ‖∑' n : ℕ, b n *
        Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖ ^ 2 ≤
        ‖sMv β‖ ^ 2 + (2 * V * Sd + V ^ 2) := by
      intro β
      have h1 := hFpt M β
      have h2 := hsM0 M β
      rw [← hV] at h1
      have h1' : ‖∑' n : ℕ, b n *
          Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖ ≤ ‖sMv β‖ + V := h1
      have hnf : (0 : ℝ) ≤ ‖∑' n : ℕ, b n *
          Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖ := norm_nonneg _
      have hA0 : (0 : ℝ) ≤ ‖sMv β‖ := norm_nonneg _
      have hsq : ‖∑' n : ℕ, b n *
          Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖ ^ 2 ≤
          (‖sMv β‖ + V) ^ 2 := by nlinarith [h1', hnf, hA0, hV0]
      nlinarith [hsq, h2, hA0, hV0, hSd0']
    have hcf : Continuous fun β : ℝ => ‖∑' n : ℕ, b n *
        Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖ ^ 2 :=
      (hcont.norm).pow 2
    have hi1 : IntervalIntegrable (fun β : ℝ => ‖∑' n : ℕ, b n *
        Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖ ^ 2) volume a (a + 1) :=
      hcf.intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun β : ℝ => ‖sMv β‖ ^ 2 + (2 * V * Sd + V ^ 2))
        volume a (a + 1) :=
      (((hcM.norm).pow 2).intervalIntegrable _ _).add intervalIntegrable_const
    have hmono : (∫ β in a..(a + 1), ‖∑' n : ℕ, b n *
        Complex.exp ((-(2 * Real.pi * β * (n : ℝ)) : ℝ) * Complex.I)‖ ^ 2) ≤
        ∫ β in a..(a + 1), (‖sMv β‖ ^ 2 + (2 * V * Sd + V ^ 2)) :=
      intervalIntegral.integral_mono (a := a) (b := a + 1) (by linarith) hi1 hi2 hpt2
    have hsplit_int : (∫ β in a..(a + 1), (‖sMv β‖ ^ 2 + (2 * V * Sd + V ^ 2))) =
        (∫ β in a..(a + 1), ‖sMv β‖ ^ 2) + (2 * V * Sd + V ^ 2) := by
      rw [intervalIntegral.integral_add (f := fun β : ℝ => ‖sMv β‖ ^ 2)
        (g := fun _ : ℝ => 2 * V * Sd + V ^ 2)
        (((hcM.norm).pow 2).intervalIntegrable _ _) intervalIntegrable_const,
        intervalIntegral.integral_const]
      simp
    have hpars : (∫ β in a..(a + 1), ‖sMv β‖ ^ 2) = ∑ n ∈ Finset.range M, ‖b n‖ ^ 2 := by
      have h := integral_normSq_finset_exp b M a
      have h' : (∫ β in a..(a + 1), ‖sMv β‖ ^ 2) =
          ∫ β in a..(a + 1), ‖∑ m ∈ Finset.range M, b m *
            Complex.exp ((-(2 * Real.pi * β * (m : ℝ)) : ℝ) * Complex.I)‖ ^ 2 := by
        simp only [hsMdef]
      rw [h', h]
    rw [hsplit_int, hpars] at hmono
    rw [hV]
    exact hmono
  -- pass to the limit
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hV : Filter.Tendsto (fun M : ℕ => ∑' i : ℕ, ‖b (i + M)‖) Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun M : ℕ => Sd - ∑ n ∈ Finset.range M, ‖b n‖)
        Filter.atTop (𝓝 (Sd - Sd)) :=
      tendsto_const_nhds.sub hb.hasSum.tendsto_sum_nat
    have h1' : Filter.Tendsto (fun M : ℕ => Sd - ∑ n ∈ Finset.range M, ‖b n‖)
        Filter.atTop (𝓝 0) := by simpa using h1
    refine h1'.congr (fun M => ?_)
    have h2 := hb.sum_add_tsum_nat_add M
    have hSd : Sd = ∑' n : ℕ, ‖b n‖ := hSS
    rw [hSd]
    linarith
  have herr : ∀ᶠ M : ℕ in Filter.atTop,
      2 * (∑' i : ℕ, ‖b (i + M)‖) * Sd + (∑' i : ℕ, ‖b (i + M)‖) ^ 2 < ε := by
    have h2 : Filter.Tendsto (fun M : ℕ =>
        2 * (∑' i : ℕ, ‖b (i + M)‖) * Sd + (∑' i : ℕ, ‖b (i + M)‖) ^ 2) Filter.atTop
        (𝓝 (2 * 0 * Sd + 0 ^ 2)) :=
      ((hV.const_mul 2).mul_const _).add (hV.pow 2)
    refine h2.eventually (Iio_mem_nhds ?_)
    simpa using hε
  obtain ⟨M, hM⟩ := herr.exists
  have h1 := hbound M
  have h2 : (∑ n ∈ Finset.range M, ‖b n‖ ^ 2) ≤ ∑' n : ℕ, ‖b n‖ ^ 2 :=
    hbs2.sum_le_tsum _ (fun i _ => sq_nonneg _)
  linarith
/-- `exp 1 < 3`. -/
private lemma exp_one_lt_three : Real.exp 1 < 3 := by
  have h := Real.exp_one_lt_d9
  linarith

/-- `6 ≤ log n` for `n ≥ 1000`. -/
private lemma six_le_log (n : ℕ) (hn : 1000 ≤ n) : 6 ≤ Real.log (n : ℝ) := by
  have hx : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have h1000 : (6 : ℝ) ≤ Real.log 1000 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h6 : Real.exp 6 = Real.exp 1 ^ 6 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h6]
    have h3 : Real.exp 1 ^ 6 ≤ 3 ^ 6 := by
      exact pow_le_pow_left₀ (Real.exp_pos 1).le exp_one_lt_three.le 6
    have : (3 : ℝ) ^ 6 = 729 := by norm_num
    linarith
  have hle : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  exact h1000.trans (Real.log_le_log (by norm_num) hle)

/-- `0.69 < log 2`. -/
private lemma log_two_gt : (0.69 : ℝ) < Real.log 2 := by
  have h := Real.log_two_gt_d9
  linarith

/-- The explicit Chebyshev bound in a clean form: `π n ≤ 300 n / log n` for `n ≥ 1000`. -/
private lemma pi_le_clean (n : ℕ) (hn : 1000 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ 300 * ((n : ℝ) / Real.log (n : ℝ)) := by
  have hx : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hxpos : (0 : ℝ) < n := by linarith
  have hL6 : 6 ≤ Real.log (n : ℝ) := six_le_log n hn
  have hL0 : 0 < Real.log (n : ℝ) := by linarith
  have hlog2 : (0.69 : ℝ) < Real.log 2 := log_two_gt
  have hlog4 : (0.4 : ℝ) ≤ (Real.log 2) ^ 2 := by nlinarith
  -- `log n ≤ 2 √n`
  have hlogsqrt : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    have h := Real.log_le_rpow_div (x := (n : ℝ)) (ε := (1 : ℝ) / 2) hxpos.le (by norm_num)
    have h2 : (n : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (n : ℝ) := by
      simpa using Real.rpow_div_two_eq_sqrt (x := (n : ℝ)) 1 hxpos.le
    rw [h2] at h
    have h3 : Real.sqrt (n : ℝ) / ((1 : ℝ) / 2) = 2 * Real.sqrt (n : ℝ) := by ring
    rw [h3] at h
    exact h
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  -- `√n ≤ 2 n / log n`
  have hLn : Real.log (n : ℝ) ≤ (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hxpos
    linarith
  have hsqrtle : Real.sqrt (n : ℝ) ≤ 2 * ((n : ℝ) / Real.log (n : ℝ)) := by
    rw [show (2 : ℝ) * ((n : ℝ) / Real.log (n : ℝ)) = 2 * (n : ℝ) / Real.log (n : ℝ) by
      rw [mul_div_assoc]]
    rw [le_div_iff₀ hL0]
    have h2 : Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) * (2 * Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogsqrt hs0
    have h3 : Real.sqrt (n : ℝ) * (2 * Real.sqrt (n : ℝ)) = 2 * (n : ℝ) := by
      rw [mul_comm (Real.sqrt (n : ℝ)), mul_assoc, Real.mul_self_sqrt hxpos.le]
    linarith [h2, h3]
  -- `log n ≤ 4 n / log n`
  have hLle : Real.log (n : ℝ) ≤ 4 * ((n : ℝ) / Real.log (n : ℝ)) := by
    rw [show (4 : ℝ) * ((n : ℝ) / Real.log (n : ℝ)) = 4 * (n : ℝ) / Real.log (n : ℝ) by
      rw [mul_div_assoc]]
    rw [le_div_iff₀ hL0]
    have h2 : Real.log (n : ℝ) * Real.log (n : ℝ) ≤
        (2 * Real.sqrt (n : ℝ)) * (2 * Real.sqrt (n : ℝ)) := by
      refine mul_le_mul hlogsqrt hlogsqrt hL0.le (by linarith [hlogsqrt, hL0])
    have h3 : (2 * Real.sqrt (n : ℝ)) * (2 * Real.sqrt (n : ℝ)) = 4 * (n : ℝ) := by
      rw [show (2 * Real.sqrt (n : ℝ)) * (2 * Real.sqrt (n : ℝ)) =
        4 * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) by ring]
      rw [Real.mul_self_sqrt hxpos.le]
    linarith [h2, h3]
  -- `log 2 ≥ 0.69` gives `√n / (log 2)² ≤ 2.2 √n`
  have hsqrt3 : Real.sqrt (n : ℝ) / (Real.log 2) ^ 2 ≤ 2.51 * Real.sqrt (n : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hs0, hlog4]
  -- `n / log n ≥ 1`
  have ht1 : 1 ≤ (n : ℝ) / Real.log (n : ℝ) := by
    rw [le_div_iff₀ hL0]
    nlinarith [hLn, hx]
  have h4 : 4 * Real.log (n : ℝ) ≤ 16 * ((n : ℝ) / Real.log (n : ℝ)) := by linarith [hLle]
  have h5 : 1.1062 * (n : ℝ).sqrt / (Real.log 2) ^ 2 ≤
      5.6 * ((n : ℝ) / Real.log (n : ℝ)) := by
    have he : 1.1062 * (n : ℝ).sqrt / (Real.log 2) ^ 2 =
        1.1062 * (Real.sqrt (n : ℝ) / (Real.log 2) ^ 2) := by ring
    rw [he]
    have h1 : 1.1062 * (Real.sqrt (n : ℝ) / (Real.log 2) ^ 2) ≤
        1.1062 * (2.51 * Real.sqrt (n : ℝ)) := by linarith [hsqrt3]
    have h2 : 1.1062 * (2.51 * Real.sqrt (n : ℝ)) ≤ 2.78 * Real.sqrt (n : ℝ) := by
      nlinarith [hs0]
    have h3 : 2.78 * Real.sqrt (n : ℝ) ≤ 5.6 * ((n : ℝ) / Real.log (n : ℝ)) := by
      nlinarith [hsqrtle]
    linarith [h1, h2, h3]
  have h6 : 4.4248 * (n : ℝ) / (Real.log (n : ℝ)) ^ 2 ≤
      ((n : ℝ) / Real.log (n : ℝ)) := by
    have hL2 : (0 : ℝ) < (Real.log (n : ℝ)) ^ 2 := by positivity
    rw [div_le_iff₀ hL2]
    have h1 : ((n : ℝ) / Real.log (n : ℝ)) * (Real.log (n : ℝ)) ^ 2 =
        (n : ℝ) * Real.log (n : ℝ) := by
      field_simp
    rw [h1]
    have hL6' := hL6
    nlinarith [hL6', hxpos]
  have h7 : (160 : ℝ) / Real.log 2 - 2 * Real.log 2 ≤ 267 * ((n : ℝ) / Real.log (n : ℝ)) := by
    have h1 : (160 : ℝ) / Real.log 2 - 2 * Real.log 2 ≤ 267 := by
      rw [div_sub' (by positivity), div_le_iff₀ (by positivity)]
      nlinarith [hlog2]
    nlinarith [h1, ht1]
  have h := LeanLab.ChebyshevExplicit.pi_le_11062_sharp n (by omega)
  have e1 : 1.1062 * (n : ℝ) / Real.log (n : ℝ) = 1.1062 * ((n : ℝ) / Real.log (n : ℝ)) := by
    ring
  linarith [h, h4, h5, h6, h7, e1]

/-- `∑_{i<I} 2^i exp(-2·2^i) ≤ 2`. -/
private lemma sum_two_pow_exp_le (I : ℕ) :
    ∑ i ∈ Finset.range I, (2 : ℝ) ^ i * Real.exp (-(2 * (2 : ℝ) ^ i)) ≤ 2 := by
  have hterm : ∀ i : ℕ, (2 : ℝ) ^ i * Real.exp (-(2 * (2 : ℝ) ^ i)) ≤ (1 / 2) ^ i := by
    intro i
    set y : ℝ := (2 : ℝ) ^ i with hy
    have hy0 : 0 < y := by positivity
    have hye : y ≤ Real.exp y := by
      have := Real.add_one_le_exp y
      linarith
    have hsq : y ^ 2 ≤ Real.exp (2 * y) := by
      have h1 : y ^ 2 ≤ (Real.exp y) ^ 2 := pow_le_pow_left₀ hy0.le hye 2
      have h2 : (Real.exp y) ^ 2 = Real.exp (2 * y) := by
        rw [pow_two, ← Real.exp_add]
        ring_nf
      linarith [h1, h2.le, h2.ge]
    have hstep : y * Real.exp (-(2 * y)) = y ^ 2 * Real.exp (-(2 * y)) / y := by
      field_simp
    rw [hstep]
    have h6 : y ^ 2 * Real.exp (-(2 * y)) / y ≤
        Real.exp (2 * y) * Real.exp (-(2 * y)) / y := by
      refine div_le_div_of_nonneg_right ?_ hy0.le
      exact mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    have h7 : Real.exp (2 * y) * Real.exp (-(2 * y)) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    have h8 : (1 : ℝ) / y = (1 / 2) ^ i := by
      rw [hy, one_div_pow]
    calc y ^ 2 * Real.exp (-(2 * y)) / y
        ≤ Real.exp (2 * y) * Real.exp (-(2 * y)) / y := h6
      _ = 1 / y := by rw [h7]
      _ = (1 / 2) ^ i := h8
  calc ∑ i ∈ Finset.range I, (2 : ℝ) ^ i * Real.exp (-(2 * (2 : ℝ) ^ i))
      ≤ ∑ i ∈ Finset.range I, (1 / 2 : ℝ) ^ i := Finset.sum_le_sum fun i _ => hterm i
    _ ≤ 2 := by
      rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
      have h2 : ((1 / 2 : ℝ) ^ I - 1) / (1 / 2 - 1) = 2 * (1 - (1 / 2) ^ I) := by
        field_simp
        ring
      rw [h2]
      have h3 : (0 : ℝ) < (1 / 2 : ℝ) ^ I := by positivity
      nlinarith

/-- `∑_{n<N+1} [n prime] = π N`. -/
private lemma sum_indicator_prime_range (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (if n.Prime then (1 : ℝ) else 0) =
      (Nat.primeCounting N : ℝ) := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← Nat.primesLE_eq_filter_range, Nat.primesLE_card_eq_primeCounting]

/-- **The damped prime square sum is `O(N / log N)`.** -/
private lemma prime_square_sum_le (N : ℕ) (hN : 1000 ≤ N) :
    (∑' n : ℕ, if n.Prime then Real.exp (-(2 * (n : ℝ) / N)) else 0) ≤
      2000 * ((N : ℝ) / Real.log (N : ℝ)) := by
  classical
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hNge : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hL6 : 6 ≤ Real.log (N : ℝ) := six_le_log N hN
  have hL0 : (0 : ℝ) < Real.log (N : ℝ) := by linarith
  -- summability
  have hb0 : ∀ n : ℕ, 0 ≤ Real.exp (-(2 * (n : ℝ) / N)) := fun n => (Real.exp_pos _).le
  have hbs : Summable fun n : ℕ => Real.exp (-(2 * (n : ℝ) / N)) := by
    refine (summable_exp_decay N (by omega)).of_nonneg_of_le (g := fun n : ℕ =>
      Real.exp (-(2 * (n : ℝ) / N))) (fun n => (Real.exp_pos _).le) (fun n => ?_)
    refine Real.exp_le_exp.mpr ?_
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hx2 : (0 : ℝ) ≤ (n : ℝ) / N := by positivity
    rw [show 2 * (n : ℝ) / N = 2 * ((n : ℝ) / N) by ring]
    linarith
  have ha : Summable fun n : ℕ => if n.Prime then Real.exp (-(2 * (n : ℝ) / N)) else 0 :=
    summable_prime_indicator _ hb0 hbs
  -- one dyadic block
  have hblock : ∀ i : ℕ,
      ∑ n ∈ Finset.Ioc (N * 2 ^ i) (N * 2 ^ (i + 1)),
          (if n.Prime then Real.exp (-(2 * (n : ℝ) / N)) else 0) ≤
        (Nat.primeCounting (N * 2 ^ (i + 1)) : ℝ) * Real.exp (-(2 * (2 : ℝ) ^ i)) := by
    intro i
    have hE0 : 0 ≤ Real.exp (-(2 * (2 : ℝ) ^ i)) := (Real.exp_pos _).le
    have step1 : ∑ n ∈ Finset.Ioc (N * 2 ^ i) (N * 2 ^ (i + 1)),
          (if n.Prime then Real.exp (-(2 * (n : ℝ) / N)) else 0) ≤
        ∑ n ∈ Finset.Ioc (N * 2 ^ i) (N * 2 ^ (i + 1)),
          (if n.Prime then Real.exp (-(2 * (2 : ℝ) ^ i)) else 0) := by
      refine Finset.sum_le_sum fun n hn => ?_
      by_cases hp : n.Prime
      · rw [if_pos hp, if_pos hp]
        refine Real.exp_le_exp.mpr ?_
        have hlt : (N * 2 ^ i : ℕ) < n := (Finset.mem_Ioc.mp hn).1
        have h1 : ((N * 2 ^ i : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hlt
        have h2 : ((N * 2 ^ i : ℕ) : ℝ) = (N : ℝ) * (2 : ℝ) ^ i := by push_cast; ring
        have h3 : (0 : ℝ) < (N : ℝ) := hNpos
        have h4 : (2 : ℝ) ^ i < (n : ℝ) / N := by
          rw [lt_div_iff₀ h3]
          rw [h2] at h1
          linarith
        rw [show 2 * (n : ℝ) / N = 2 * ((n : ℝ) / N) by ring]
        linarith
      · rw [if_neg hp, if_neg hp]
    have step2 : ∑ n ∈ Finset.Ioc (N * 2 ^ i) (N * 2 ^ (i + 1)),
          (if n.Prime then Real.exp (-(2 * (2 : ℝ) ^ i)) else 0) =
        Real.exp (-(2 * (2 : ℝ) ^ i)) *
          (((Finset.Ioc (N * 2 ^ i) (N * 2 ^ (i + 1))).filter Nat.Prime).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      ring
    have step3 : (((Finset.Ioc (N * 2 ^ i) (N * 2 ^ (i + 1))).filter Nat.Prime).card : ℝ) ≤
        (Nat.primeCounting (N * 2 ^ (i + 1)) : ℝ) := by
      have h1 : ((Finset.Ioc (N * 2 ^ i) (N * 2 ^ (i + 1))).filter Nat.Prime).card ≤
          Nat.primeCounting (N * 2 ^ (i + 1)) := by
        rw [← Nat.primesLE_card_eq_primeCounting]
        refine Finset.card_le_card ?_
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [Nat.mem_primesLE]
        exact ⟨(Finset.mem_Ioc.mp hn.1).2, hn.2⟩
      exact_mod_cast h1
    calc ∑ n ∈ Finset.Ioc (N * 2 ^ i) (N * 2 ^ (i + 1)),
          (if n.Prime then Real.exp (-(2 * (n : ℝ) / N)) else 0)
        ≤ ∑ n ∈ Finset.Ioc (N * 2 ^ i) (N * 2 ^ (i + 1)),
          (if n.Prime then Real.exp (-(2 * (2 : ℝ) ^ i)) else 0) := step1
      _ = Real.exp (-(2 * (2 : ℝ) ^ i)) *
          (((Finset.Ioc (N * 2 ^ i) (N * 2 ^ (i + 1))).filter Nat.Prime).card : ℝ) := step2
      _ ≤ Real.exp (-(2 * (2 : ℝ) ^ i)) *
          (Nat.primeCounting (N * 2 ^ (i + 1)) : ℝ) := by
          refine mul_le_mul_of_nonneg_left step3 hE0
      _ = (Nat.primeCounting (N * 2 ^ (i + 1)) : ℝ) * Real.exp (-(2 * (2 : ℝ) ^ i)) := by ring
  -- the dyadic induction
  have hind : ∀ I : ℕ,
      ∑ n ∈ Finset.range (N * 2 ^ I + 1),
          (if n.Prime then Real.exp (-(2 * (n : ℝ) / N)) else 0) ≤
        (Nat.primeCounting N : ℝ) +
          ∑ i ∈ Finset.range I,
            ((Nat.primeCounting (N * 2 ^ (i + 1)) : ℝ) * Real.exp (-(2 * (2 : ℝ) ^ i))) := by
    intro I
    induction I with
    | zero =>
        have h0 : N * 2 ^ 0 = N := by rw [pow_zero, mul_one]
        rw [h0]
        simp only [Finset.range_zero, Finset.sum_empty, add_zero]
        calc ∑ n ∈ Finset.range (N + 1),
              (if n.Prime then Real.exp (-(2 * (n : ℝ) / N)) else 0)
            ≤ ∑ n ∈ Finset.range (N + 1), (if n.Prime then (1 : ℝ) else 0) := by
              refine Finset.sum_le_sum fun n _ => ?_
              by_cases hp : n.Prime
              · rw [if_pos hp, if_pos hp]
                rw [← Real.exp_zero, Real.exp_le_exp]
                have hx2 : (0 : ℝ) ≤ (n : ℝ) / N := by positivity
                rw [show 2 * (n : ℝ) / N = 2 * ((n : ℝ) / N) by ring]
                linarith
              · rw [if_neg hp, if_neg hp]
          _ = (Nat.primeCounting N : ℝ) := sum_indicator_prime_range N
    | succ I ih =>
        conv_rhs => rw [Finset.sum_range_succ]
        have hpow : N * 2 ^ (I + 1) = 2 * (N * 2 ^ I) := by
          rw [pow_succ]; ring
        have hmono : N * 2 ^ I ≤ N * 2 ^ (I + 1) := by
          rw [hpow]; omega
        have hunion : Finset.range (N * 2 ^ (I + 1) + 1) =
            Finset.range (N * 2 ^ I + 1) ∪ Finset.Ioc (N * 2 ^ I) (N * 2 ^ (I + 1)) := by
          rw [hpow]
          ext n
          simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]
          omega
        have hdisj : Disjoint (Finset.range (N * 2 ^ I + 1))
            (Finset.Ioc (N * 2 ^ I) (N * 2 ^ (I + 1))) := by
          refine Finset.disjoint_left.mpr fun x hx hx' => ?_
          simp only [Finset.mem_range] at hx
          simp only [Finset.mem_Ioc] at hx'
          omega
        rw [hunion, Finset.sum_union hdisj]
        have hb := hblock I
        linarith [ih, hb]
  -- partial sums
  have hpartial : ∀ K : ℕ,
      ∑ n ∈ Finset.range K, (if n.Prime then Real.exp (-(2 * (n : ℝ) / N)) else 0) ≤
        2000 * ((N : ℝ) / Real.log (N : ℝ)) := by
    intro K
    have hKN : K ≤ N * 2 ^ K + 1 := by
      have h1 : K ≤ 2 ^ K := Nat.le_of_lt K.lt_two_pow_self
      have h2 : (2 : ℕ) ^ K ≤ N * 2 ^ K := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hsub : Finset.range K ⊆ Finset.range (N * 2 ^ K + 1) := by
      intro n hn
      simp only [Finset.mem_range] at hn ⊢
      omega
    have hstep1 : ∑ n ∈ Finset.range K, (if n.Prime then Real.exp (-(2 * (n : ℝ) / N)) else 0) ≤
        ∑ n ∈ Finset.range (N * 2 ^ K + 1),
          (if n.Prime then Real.exp (-(2 * (n : ℝ) / N)) else 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by
        by_cases hp : i.Prime
        · rw [if_pos hp]; exact (Real.exp_pos _).le
        · rw [if_neg hp])
    have hsum_le : ∑ i ∈ Finset.range K,
          ((Nat.primeCounting (N * 2 ^ (i + 1)) : ℝ) * Real.exp (-(2 * (2 : ℝ) ^ i))) ≤
        (600 * ((N : ℝ) / Real.log (N : ℝ))) *
          ∑ i ∈ Finset.range K, (2 : ℝ) ^ i * Real.exp (-(2 * (2 : ℝ) ^ i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have hpi : (Nat.primeCounting (N * 2 ^ (i + 1)) : ℝ) ≤
          300 * (((N * 2 ^ (i + 1) : ℕ) : ℝ) / Real.log ((N * 2 ^ (i + 1) : ℕ) : ℝ)) :=
        pi_le_clean _ (by
          have h1 : (2 : ℕ) ^ (i + 1) ≥ 1 := Nat.one_le_two_pow
          have h2 : N * 2 ^ (i + 1) ≥ N * 1 := Nat.mul_le_mul_left N h1
          omega)
      have hcast : ((N * 2 ^ (i + 1) : ℕ) : ℝ) = (N : ℝ) * (2 : ℝ) ^ (i + 1) := by
        push_cast
        ring
      have hlog : Real.log (N : ℝ) ≤ Real.log ((N * 2 ^ (i + 1) : ℕ) : ℝ) := by
        refine Real.log_le_log hNpos ?_
        rw [hcast]
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (i + 1) := one_le_pow₀ (by norm_num)
        nlinarith [hNpos]
      have hdiv : (((N * 2 ^ (i + 1) : ℕ) : ℝ) / Real.log ((N * 2 ^ (i + 1) : ℕ) : ℝ)) ≤
          (((N * 2 ^ (i + 1) : ℕ) : ℝ) / Real.log (N : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) hL0 hlog
      have hpi' : (Nat.primeCounting (N * 2 ^ (i + 1)) : ℝ) ≤
          300 * (((N * 2 ^ (i + 1) : ℕ) : ℝ) / Real.log (N : ℝ)) := by
        calc (Nat.primeCounting (N * 2 ^ (i + 1)) : ℝ) ≤
            300 * (((N * 2 ^ (i + 1) : ℕ) : ℝ) / Real.log ((N * 2 ^ (i + 1) : ℕ) : ℝ)) := hpi
          _ ≤ 300 * (((N * 2 ^ (i + 1) : ℕ) : ℝ) / Real.log (N : ℝ)) := by
              have h := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0:ℝ) ≤ 300)
              linarith [h]
      have hE0 : 0 ≤ Real.exp (-(2 * (2 : ℝ) ^ i)) := (Real.exp_pos _).le
      have h1 : (Nat.primeCounting (N * 2 ^ (i + 1)) : ℝ) * Real.exp (-(2 * (2 : ℝ) ^ i)) ≤
          (300 * (((N * 2 ^ (i + 1) : ℕ) : ℝ) / Real.log (N : ℝ))) *
            Real.exp (-(2 * (2 : ℝ) ^ i)) :=
        mul_le_mul_of_nonneg_right hpi' hE0
      have h2 : (300 * (((N * 2 ^ (i + 1) : ℕ) : ℝ) / Real.log (N : ℝ))) *
            Real.exp (-(2 * (2 : ℝ) ^ i)) =
          (600 * ((N : ℝ) / Real.log (N : ℝ))) *
            ((2 : ℝ) ^ i * Real.exp (-(2 * (2 : ℝ) ^ i))) := by
        rw [hcast, pow_succ]
        field_simp
        ring
      linarith [h1, h2.le, h2.ge]
    have hsum_bound : (600 * ((N : ℝ) / Real.log (N : ℝ))) *
          ∑ i ∈ Finset.range K, (2 : ℝ) ^ i * Real.exp (-(2 * (2 : ℝ) ^ i)) ≤
        (600 * ((N : ℝ) / Real.log (N : ℝ))) * 2 := by
      refine mul_le_mul_of_nonneg_left (sum_two_pow_exp_le K) ?_
      have : (0 : ℝ) < (N : ℝ) / Real.log (N : ℝ) := by positivity
      linarith
    have hpiN : (Nat.primeCounting N : ℝ) ≤ 300 * ((N : ℝ) / Real.log (N : ℝ)) :=
      pi_le_clean N hN
    have hfin : (600 * ((N : ℝ) / Real.log (N : ℝ))) * 2 +
        (Nat.primeCounting N : ℝ) ≤ 2000 * ((N : ℝ) / Real.log (N : ℝ)) := by
      have hLn : Real.log (N : ℝ) ≤ (N : ℝ) := by
        have h := Real.log_le_sub_one_of_pos hNpos
        linarith
      have ht : 1 ≤ (N : ℝ) / Real.log (N : ℝ) := by
        rw [le_div_iff₀ hL0]; nlinarith
      nlinarith [hpiN, ht]
    calc ∑ n ∈ Finset.range K, (if n.Prime then Real.exp (-(2 * (n : ℝ) / N)) else 0)
        ≤ (Nat.primeCounting N : ℝ) +
            ∑ i ∈ Finset.range K,
              ((Nat.primeCounting (N * 2 ^ (i + 1)) : ℝ) * Real.exp (-(2 * (2 : ℝ) ^ i))) :=
          hstep1.trans (hind K)
      _ ≤ (Nat.primeCounting N : ℝ) +
            (600 * ((N : ℝ) / Real.log (N : ℝ))) *
              ∑ i ∈ Finset.range K, (2 : ℝ) ^ i * Real.exp (-(2 * (2 : ℝ) ^ i)) := by
          linarith [hsum_le]
      _ ≤ 2000 * ((N : ℝ) / Real.log (N : ℝ)) := by linarith [hsum_bound, hfin]
  refine le_of_tendsto_of_tendsto ha.hasSum.tendsto_sum_nat tendsto_const_nhds ?_
  filter_upwards with K using hpartial K

/-- The squared damping factors over the primes are the doubly damped prime sum. -/
private lemma prime_squares_eq (N : ℕ) :
    (∑' n : ℕ, (if n.Prime then Real.exp (-((n : ℝ) / N)) else 0) ^ 2) =
      ∑' n : ℕ, if n.Prime then Real.exp (-(2 * (n : ℝ) / N)) else 0 := by
  refine tsum_congr fun n => ?_
  by_cases hp : n.Prime
  · rw [if_pos hp, if_pos hp, sq, ← Real.exp_add]
    congr 1
    ring
  · rw [if_neg hp, if_neg hp]
    norm_num

/-- Crude bound: the doubly damped prime sum is at most `N`. -/
private lemma prime_square_sum_crude (N : ℕ) (hN : 2 ≤ N) :
    (∑' n : ℕ, if n.Prime then Real.exp (-(2 * (n : ℝ) / N)) else 0) ≤ N := by
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hb0 : ∀ n : ℕ, 0 ≤ Real.exp (-(2 * (n : ℝ) / N)) := fun n => (Real.exp_pos _).le
  have hbs : Summable fun n : ℕ => Real.exp (-(2 * (n : ℝ) / N)) := by
    refine (summable_exp_decay N (by omega)).of_nonneg_of_le (g := fun n : ℕ =>
      Real.exp (-(2 * (n : ℝ) / N))) (fun n => (Real.exp_pos _).le) (fun n => ?_)
    refine Real.exp_le_exp.mpr ?_
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hx2 : (0 : ℝ) ≤ (n : ℝ) / N := by positivity
    rw [show 2 * (n : ℝ) / N = 2 * ((n : ℝ) / N) by ring]
    linarith
  -- the geometric sum
  set r : ℝ := Real.exp (-(2 / (N : ℝ))) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr]
    have h := Real.exp_lt_exp (x := -(2 / (N : ℝ))) (y := 0) |>.mpr (by
      have h1 : (0 : ℝ) < 2 / (N : ℝ) := by positivity
      linarith)
    rwa [Real.exp_zero] at h
  have hsum_eq : (∑' n : ℕ, Real.exp (-(2 * (n : ℝ) / N))) = ∑' n : ℕ, r ^ n := by
    refine tsum_congr fun n => ?_
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    field_simp
  have hgeo : (∑' n : ℕ, r ^ n) = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
  -- `1 + 2/N ≤ exp (2/N) = r⁻¹`
  have hrne : r ≠ 0 := (Real.exp_pos _).ne'
  have hrinv : r⁻¹ = Real.exp (2 / (N : ℝ)) := by
    rw [hr, ← Real.exp_neg]
    congr 1
    ring
  have hexp : 1 + 2 / (N : ℝ) ≤ r⁻¹ := by
    rw [hrinv]
    have h := Real.add_one_le_exp (2 / (N : ℝ))
    linarith
  have ha0 : (0 : ℝ) < 1 + 2 / (N : ℝ) := by positivity
  have hrle : r ≤ 1 / (1 + 2 / (N : ℝ)) := by
    have h := one_div_le_one_div_of_le ha0 hexp
    rwa [one_div, inv_inv] at h
  have hNr : 1 / (1 + 2 / (N : ℝ)) = (N : ℝ) / ((N : ℝ) + 2) := by
    field_simp
  have hrle' : r ≤ (N : ℝ) / ((N : ℝ) + 2) := by
    rw [← hNr]; exact hrle
  have hpos : (0 : ℝ) < 1 - r := by
    have h2 : (N : ℝ) / ((N : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    linarith
  have hgoal : (1 - r)⁻¹ ≤ (N : ℝ) := by
    rw [← one_div, div_le_iff₀ hpos]
    have h2 : (N : ℝ) * (1 - r) ≥ (N : ℝ) * (1 - (N : ℝ) / ((N : ℝ) + 2)) := by
      have : 0 ≤ (N : ℝ) := hNpos.le
      nlinarith [hrle']
    have h3 : (N : ℝ) * (1 - (N : ℝ) / ((N : ℝ) + 2)) = 2 * (N : ℝ) / ((N : ℝ) + 2) := by
      field_simp
      ring
    have h4 : 1 ≤ 2 * (N : ℝ) / ((N : ℝ) + 2) := by
      rw [le_div_iff₀ (by positivity)]
      have : (2 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    linarith
  have hle : (∑' n : ℕ, if n.Prime then Real.exp (-(2 * (n : ℝ) / N)) else 0) ≤
      ∑' n : ℕ, Real.exp (-(2 * (n : ℝ) / N)) := by
    refine Summable.tsum_le_tsum (f := fun n : ℕ => if n.Prime then Real.exp (-(2 * (n : ℝ) / N)) else 0)
      (g := fun n : ℕ => Real.exp (-(2 * (n : ℝ) / N))) (fun n => ?_)
      (summable_prime_indicator _ hb0 hbs) hbs
    by_cases hp : n.Prime
    · simp [if_pos hp]
    · rw [if_neg hp]; positivity
  calc (∑' n : ℕ, if n.Prime then Real.exp (-(2 * (n : ℝ) / N)) else 0)
      ≤ ∑' n : ℕ, Real.exp (-(2 * (n : ℝ) / N)) := hle
    _ = ∑' n : ℕ, r ^ n := hsum_eq
    _ = (1 - r)⁻¹ := hgeo
    _ ≤ (N : ℝ) := hgoal


/-- `log 1000 ≤ 8`. -/
private lemma log_1000_le : Real.log 1000 ≤ 8 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h8 : Real.exp 8 = Real.exp 1 ^ 8 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h8]
  have h : (2.7182818283 : ℝ) ^ 8 ≤ Real.exp 1 ^ 8 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 8
  have h2 : (1000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 8 := by norm_num
  linarith

/-- The mass of the damped prime exponential sum on an interval of length one is
`O(N / log N)`. -/
private lemma prime_exp_integral_le (N : ℕ) (hN : 3 ≤ N) (a : ℝ) :
    (∫ z in a..(a + 1),
        ‖∑' n : ℕ, (((if n.Prime then Real.exp (-((n : ℝ) / N)) else 0) : ℝ) : ℂ) *
          Complex.exp ((-(2 * Real.pi * z * (n : ℝ)) : ℝ) * Complex.I)‖ ^ 2) ≤
      2000 * ((N : ℝ) / Real.log N) := by
  classical
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hN1 : 0 < N := by omega
  have hb1 : ∀ n : ℕ, ‖(((if n.Prime then Real.exp (-((n : ℝ) / N)) else 0) : ℝ) : ℂ)‖ ≤ 1 := by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by by_cases hp : n.Prime <;> simp only [hp, if_true, if_false] <;> positivity)]
    by_cases hp : n.Prime
    · rw [if_pos hp]; exact exp_decay_le_one N hN1 n
    · rw [if_neg hp]; norm_num
  have hbs : Summable fun n : ℕ => ‖(((if n.Prime then Real.exp (-((n : ℝ) / N)) else 0) : ℝ) : ℂ)‖ := by
    refine (summable_exp_decay N hN1).of_nonneg_of_le (g := fun n : ℕ =>
      ‖(((if n.Prime then Real.exp (-((n : ℝ) / N)) else 0) : ℝ) : ℂ)‖)
      (fun n => norm_nonneg _) (fun n => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by by_cases hp : n.Prime <;> simp only [hp, if_true, if_false] <;> positivity)]
    by_cases hp : n.Prime
    · simp only [if_pos hp]; exact le_rfl
    · rw [if_neg hp]; exact (Real.exp_pos _).le
  have h := integral_normSq_tsum_le (fun n : ℕ =>
    (((if n.Prime then Real.exp (-((n : ℝ) / N)) else 0) : ℝ) : ℂ)) hb1 hbs a
  have hsq : (∑' n : ℕ, ‖(((if n.Prime then Real.exp (-((n : ℝ) / N)) else 0) : ℝ) : ℂ)‖ ^ 2) =
      ∑' n : ℕ, (if n.Prime then Real.exp (-((n : ℝ) / N)) else 0) ^ 2 := by
    refine tsum_congr fun n => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hsq, prime_squares_eq N] at h
  by_cases hbig : 1000 ≤ N
  · exact h.trans (prime_square_sum_le N hbig)
  · have hsmall : N ≤ 1000 := by omega
    have hcrude := prime_square_sum_crude N (by omega)
    have hlog : Real.log (N : ℝ) ≤ 2000 := by
      have h1 : Real.log (N : ℝ) ≤ Real.log 1000 := by
        refine Real.log_le_log hNpos ?_
        exact_mod_cast hsmall
      linarith [log_1000_le]
    have hlog0 : 0 < Real.log (N : ℝ) := by
      have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
      have h := Real.log_pos (by linarith : (1 : ℝ) < N)
      linarith
    have hlast : (N : ℝ) ≤ 2000 * ((N : ℝ) / Real.log (N : ℝ)) := by
      rw [mul_div_assoc', le_div_iff₀ hlog0]
      nlinarith [hlog, hNpos]
    exact h.trans (hcrude.trans hlast)

/-! ### The single-denominator leaf -/

private lemma summable_norm_indicator (N : ℕ) (hN : 0 < N) :
    Summable fun n : ℕ => ‖(((if n.Prime then Real.exp (-((n : ℝ) / N)) else 0) : ℝ) : ℂ)‖ := by
  refine (summable_exp_decay N hN).of_nonneg_of_le (g := fun n : ℕ =>
    ‖(((if n.Prime then Real.exp (-((n : ℝ) / N)) else 0) : ℝ) : ℂ)‖)
    (fun n => norm_nonneg _) (fun n => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by by_cases hp : n.Prime <;> simp only [hp, if_true, if_false] <;> positivity)]
  by_cases hp : n.Prime
  · simp only [if_pos hp]; exact le_rfl
  · rw [if_neg hp]; exact (Real.exp_pos _).le

/-- `primeFourier111` as a sum with the prime indicator over `ℕ`. -/
private lemma primeFourier_eq_indicator (N : ℕ) (α : ℝ) :
    primeFourier111 N α =
      ∑' n : ℕ, (((if n.Prime then Real.exp (-((n : ℝ) / N)) else 0) : ℝ) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * (n : ℝ)) : ℝ) * Complex.I) := by
  classical
  rw [primeFourier111]
  simp only [neg_div]
  have h1 : (∑' p : Nat.Primes, (Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * (((p : ℕ)) : ℝ)) : ℝ) * Complex.I)) =
      ∑' x : {n : ℕ // Nat.Prime n}, (Real.exp (-(((x : ℕ) : ℝ) / N)) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * (((x : ℕ)) : ℝ)) : ℝ) * Complex.I) := rfl
  rw [h1]
  have h2 := tsum_subtype {n : ℕ | Nat.Prime n} (fun n : ℕ =>
    (Real.exp (-((n : ℝ) / N)) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (n : ℝ)) : ℝ) * Complex.I))
  refine h2.trans ?_
  refine tsum_congr fun n => ?_
  rw [Set.indicator_apply]
  simp only [Set.mem_setOf_eq]
  by_cases hp : n.Prime
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp]
    simp only [Complex.ofReal_zero, zero_mul]

/-! ### The principal square mass

The character series is a `ℕ`-indexed exponential series with coefficients that
vanish off the primes and have modulus at most the damping factor. The mean square
over one period is then at most the doubly damped prime sum, which is `O(N/log N)`
by the Chebyshev bound above. Periodicity moves any sub-interval of one period into
a full period. -/

/-- `characterPrime280` as a zero-extended prime series over `ℕ`.
Carried from `Linnik1951.Principal442.character_series_nat442` (earlier pass). -/
private lemma characterPrime_eq_indicator (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N : ℕ) (α : ℝ) :
    characterPrime280 χ N α =
      ∑' n : ℕ, (((if n.Prime then χ n * (Real.exp (-(n : ℝ) / N) : ℂ) else 0)) *
        Complex.exp ((-(2 * Real.pi * α * (n : ℝ)) : ℝ) * Complex.I)) := by
  classical
  let f : ℕ → ℂ := fun n => if n.Prime then
    χ n * (Real.exp (-(n : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (n : ℝ)) : ℝ) * Complex.I) else 0
  have hsupp : Function.support f ⊆ Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro n hn
    by_cases hp : n.Prime
    · exact ⟨⟨n, hp⟩, rfl⟩
    · exact absurd (by dsimp only [f]; simp [hp] : f n = 0) hn
  calc
    characterPrime280 χ N α = ∑' p : Nat.Primes, f (p : ℕ) := by
      unfold characterPrime280
      apply tsum_congr
      intro p
      dsimp only [f]
      rw [if_pos p.property]
    _ = ∑' n : ℕ, f n := Nat.Primes.coe_nat_injective.tsum_eq hsupp
    _ = ∑' n : ℕ, (((if n.Prime then χ n * (Real.exp (-(n : ℝ) / N) : ℂ) else 0)) *
        Complex.exp ((-(2 * Real.pi * α * (n : ℝ)) : ℝ) * Complex.I)) := by
      apply tsum_congr
      intro n
      by_cases hn : n.Prime <;> (dsimp only [f]; simp [hn])

/-- The character series has period one. -/
private lemma character_periodic_435 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N : ℕ) : Function.Periodic (characterPrime280 χ N) 1 := by
  intro α
  unfold characterPrime280
  apply tsum_congr
  intro p
  congr 1
  have he : ((-(2 * Real.pi * (α + 1) * (p : ℕ)) : ℝ) : ℂ) * Complex.I =
      ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) : ℂ) * Complex.I +
        ((-((p : ℕ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) := by
    push_cast
    ring
  rw [he, Complex.exp_add]
  have hp : Complex.exp ((-((p : ℕ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I (-((p : ℕ) : ℤ)) using 1 <;> push_cast <;> ring
  rw [hp, mul_one]

/-- Mean square of any character series over an interval of length one. -/
private lemma character_integral_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N : ℕ) (hN : 3 ≤ N) (a : ℝ) :
    (∫ z in a..(a + 1), ‖characterPrime280 χ N z‖ ^ 2) ≤
      2000 * ((N : ℝ) / Real.log N) := by
  classical
  have hN1 : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  set b : ℕ → ℂ := fun n =>
    if n.Prime then χ n * (Real.exp (-(n : ℝ) / N) : ℂ) else 0 with hb
  have hbnP : ∀ n : ℕ, n.Prime → b n = χ n * (Real.exp (-(n : ℝ) / N) : ℂ) := by
    intro n hn
    simp [hb, hn]
  have hbnN : ∀ n : ℕ, ¬ n.Prime → b n = 0 := by
    intro n hn
    simp [hb, hn]
  have hb1 : ∀ n : ℕ, ‖b n‖ ≤ 1 := by
    intro n
    by_cases hp : n.Prime
    · rw [hbnP n hp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have hc : ‖χ n‖ ≤ 1 := χ.norm_le_one n
      have hd : Real.exp (-(n : ℝ) / N) ≤ 1 := by
        rw [neg_div]
        exact exp_decay_le_one N hN1 n
      have hd0 : (0 : ℝ) ≤ Real.exp (-(n : ℝ) / N) := (Real.exp_pos _).le
      nlinarith
    · rw [hbnN n hp]
      simp
  have hbs : Summable fun n : ℕ => ‖b n‖ := by
    refine (summable_exp_decay N hN1).of_nonneg_of_le (fun n => norm_nonneg _) ?_
    intro n
    by_cases hp : n.Prime
    · rw [hbnP n hp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), neg_div]
      calc ‖χ n‖ * Real.exp (-((n : ℝ) / N)) ≤ 1 * Real.exp (-((n : ℝ) / N)) :=
            mul_le_mul_of_nonneg_right (χ.norm_le_one n) (Real.exp_pos _).le
        _ = _ := one_mul _
    · rw [hbnN n hp]
      simp only [norm_zero]
      exact (Real.exp_pos _).le
  have h := integral_normSq_tsum_le b hb1 hbs a
  have hrew : (∫ z in a..(a + 1), ‖characterPrime280 χ N z‖ ^ 2) =
      ∫ z in a..(a + 1),
        ‖∑' n : ℕ, b n *
          Complex.exp ((-(2 * Real.pi * z * (n : ℝ)) : ℝ) * Complex.I)‖ ^ 2 := by
    refine intervalIntegral.integral_congr fun z _ => ?_
    simp only [hb]
    rw [characterPrime_eq_indicator]
  rw [hrew]
  refine h.trans ?_
  have hb2 : ∀ n : ℕ,
      ‖b n‖ ^ 2 ≤ (if n.Prime then Real.exp (-(2 * (n : ℝ) / N)) else 0) := by
    intro n
    by_cases hp : n.Prime
    · rw [hbnP n hp, if_pos hp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have hc : ‖χ n‖ ^ 2 ≤ 1 := by
        have h1 := χ.norm_le_one n
        have h2 := norm_nonneg (χ n)
        nlinarith
      have he : Real.exp (-(n : ℝ) / N) ^ 2 = Real.exp (-(2 * (n : ℝ) / N)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      calc (‖χ n‖ * Real.exp (-(n : ℝ) / N)) ^ 2 =
            ‖χ n‖ ^ 2 * Real.exp (-(n : ℝ) / N) ^ 2 := by ring
        _ ≤ 1 * Real.exp (-(n : ℝ) / N) ^ 2 :=
            mul_le_mul_of_nonneg_right hc (by positivity)
        _ = _ := by rw [one_mul, he]
    · rw [hbnN n hp, if_neg hp]
      simp
  have hs2 : Summable fun n : ℕ => ‖b n‖ ^ 2 :=
    hbs.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => by
      rw [sq]
      exact mul_le_of_le_one_right (norm_nonneg _) (hb1 n))
  have hexp2 : Summable fun n : ℕ => Real.exp (-(2 * (n : ℝ) / N)) := by
    refine (summable_exp_decay N hN1).of_nonneg_of_le (fun n => (Real.exp_pos _).le) ?_
    intro n
    refine Real.exp_le_exp.mpr ?_
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hx : (0 : ℝ) ≤ (n : ℝ) / N := div_nonneg hn hNpos.le
    rw [show -(2 * (n : ℝ) / N) = -2 * ((n : ℝ) / N) by ring,
      show -((n : ℝ) / N) = -1 * ((n : ℝ) / N) by ring]
    nlinarith
  have hind : Summable fun n : ℕ => if n.Prime then Real.exp (-(2 * (n : ℝ) / N)) else 0 :=
    summable_prime_indicator _ (fun n => (Real.exp_pos _).le) hexp2
  have hle := hs2.tsum_le_tsum hb2 hind
  refine hle.trans ?_
  by_cases hbig : 1000 ≤ N
  · exact prime_square_sum_le N hbig
  · have hsmall : N ≤ 1000 := by omega
    have hcrude := prime_square_sum_crude N (by omega)
    have hlog : Real.log (N : ℝ) ≤ 2000 := by
      have h1 : Real.log (N : ℝ) ≤ Real.log 1000 := by
        refine Real.log_le_log hNpos ?_
        exact_mod_cast hsmall
      linarith [log_1000_le]
    have hlog0 : 0 < Real.log (N : ℝ) := by
      have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
      have h := Real.log_pos (by linarith : (1 : ℝ) < N)
      linarith
    have hlast : (N : ℝ) ≤ 2000 * ((N : ℝ) / Real.log (N : ℝ)) := by
      rw [mul_div_assoc', le_div_iff₀ hlog0]
      nlinarith [hlog, hNpos]
    exact hcrude.trans hlast

/-- LEAF. The principal square mass of page 159 before equation 5.3 with the
logarithmic saving: for the trivial character the square integral over any
interval of radius at most one half is at most a constant times N over log N.
This is the full period square sum, so the saving is the reciprocal of log N and
no power of N is lost. Unconditional, for every modulus. -/
theorem principal_mass435 :
    ∃ P : ℝ, 0 < P ∧ ∀ (N q : ℕ) [NeZero q] (r : ℝ), 3 ≤ N → 0 ≤ r → r ≤ 1 / 2 →
      (∫ z in -r..r, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) ≤
        P * ((N : ℝ) / Real.log N) := by


  classical
  refine ⟨2000, by norm_num, ?_⟩
  intro N q _ r hN hr hrh
  have hN1 : 1 ≤ N := by omega
  have hc : Continuous fun z : ℝ =>
      ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 :=
    (continuous_character_prime357 (1 : DirichletCharacter ℂ q) N hN1).norm.pow 2
  have hper : Function.Periodic (fun z : ℝ =>
      ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) 1 :=
    (character_periodic_435 q (1 : DirichletCharacter ℂ q) N).comp (fun z => ‖z‖ ^ 2)
  have hi := intervalIntegral.integral_mono_interval (μ := MeasureTheory.volume)
    (show -(1 / 2 : ℝ) ≤ -r by linarith) (show -r ≤ r by linarith) hrh
    (Filter.Eventually.of_forall (fun z => sq_nonneg
      ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖))
    (hc.intervalIntegrable (-(1 / 2 : ℝ)) (1 / 2))
  have he : (∫ z in -(1 / 2 : ℝ)..(1 / 2),
        ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) =
      ∫ z in (0 : ℝ)..1, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 := by
    have h := hper.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
    rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num,
      show (0 : ℝ) + 1 = 1 by norm_num] at h
    exact h
  have hpi : (∫ z in (0 : ℝ)..1,
        ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) ≤
      2000 * ((N : ℝ) / Real.log N) := by
    have h := character_integral_le q (1 : DirichletCharacter ℂ q) N hN 0
    rw [show (0 : ℝ) + 1 = 1 by norm_num] at h
    exact h
  exact hi.trans (he.trans_le hpi)

/-! ### Leaf `mixed_mass491` -/

/-- Arithmetic step: the product of the square roots of the principal and the
nonprincipal mass is at most the stated constant times `N log^6 N / sqrt R`. -/
private lemma sqrt_mass_le_491 (N R P B : ℝ) (hN : 0 < N) (hR : 0 < R)
    (hP : 0 < P) (hB : 0 < B) (hlog : 0 < Real.log N) :
    Real.sqrt (P * (N / Real.log N)) * Real.sqrt (B * N / R * Real.log N ^ 13)
      ≤ Real.sqrt (P * B) * N * Real.log N ^ 6 / Real.sqrt R := by
  rw [← Real.sqrt_mul (by positivity)]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have hrootR := Real.sq_sqrt hR.le
  have hrootPB := Real.sq_sqrt (show (0 : ℝ) ≤ P * B by positivity)
  have he : (Real.sqrt (P * B) * N * Real.log N ^ 6 / Real.sqrt R) ^ 2 =
      P * B * N ^ 2 / R * Real.log N ^ 12 := by
    rw [div_pow, mul_pow, mul_pow, hrootPB, hrootR]
    ring
  rw [he]
  have hl0 : Real.log N ≠ 0 := hlog.ne'
  have hR0 : R ≠ 0 := hR.ne'
  have hL : P * (N / Real.log N) * (B * N / R * Real.log N ^ 13) =
      P * B * N ^ 2 / R * Real.log N ^ 12 := by
    field_simp
  exact hL.le


/-- LEAF. Mass step of equation 5.5. The mixed character mass of one
nonprincipal character: the integral of the principal character prime series
against the nonprincipal one over the local window is at most the scale N times
the sixth power of the logarithm of N over the square root of q times tau. This
is the sixth power form of the mixed mass and it carries no conjugate Gauss
coefficient, no residue sum and no outer character sum. -/
theorem mixed_mass491 (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            ‖characterPrime280 (1 : DirichletCharacter ℂ q) N α‖ *
              ‖characterPrime280 χ N α‖) ≤
            C * (N : ℝ) * Real.log N ^ 6 /
              Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  obtain ⟨B, hB, NB, hb⟩ := hM
  obtain ⟨P, hP, hmass⟩ := principal_mass435
  refine ⟨Real.sqrt (P * B), Real.sqrt_pos.mpr (by positivity), max 128 (max 4 NB), ?_⟩
  intro N hN q hq hqQ χ hχ
  have hN128 : 128 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNB : NB < N := lt_of_le_of_lt (le_trans (le_max_right (a := 4) (b := NB))
    (le_max_right (a := 128) (b := max 4 NB))) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN3 : 3 ≤ N := by omega
  have hl : 1 ≤ Real.log N := by
    have hN3' : (3 : ℝ) < N := by exact_mod_cast (show 3 < N by omega)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.trans hN3').le
  have hlog0 : 0 < Real.log N := by linarith
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set R : ℝ := (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) with hR
  have hτ1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) := Real.one_le_rpow hNr (by norm_num)
  have hRp : 0 < R := by dsimp [R]; positivity
  have hR2 : 2 ≤ R := by
    have hτ2 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) := by
      have hn : (128 : ℝ) ≤ N := by exact_mod_cast hN128.le
      have hh := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 128) hn
        (by norm_num : (0 : ℝ) ≤ 1 / 7)
      have he : (128 : ℝ) ^ (1 / 7 : ℝ) = 2 := by
        rw [show (128 : ℝ) = 2 ^ (7 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      rwa [he] at hh
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
    dsimp [R]
    nlinarith
  have hq7 : (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) :=
    hqQ.trans (Real.rpow_le_rpow_of_exponent_le hNr (by norm_num))
  set r : ℝ := 1 / R with hrdef
  have hr : 0 < r := by positivity
  have hrh : r ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hR2
  haveI : NeZero q := ⟨by omega⟩
  have hpcont := continuous_character_prime357 (1 : DirichletCharacter ℂ q) N (by omega)
  have hncont := continuous_character_prime357 χ N (by omega)
  have hpLp : MemLp (characterPrime280 (1 : DirichletCharacter ℂ q) N) 2
      (volume.restrict (Set.Ioc (-r) r)) :=
    (memLp_two_iff_integrable_sq_norm hpcont.aestronglyMeasurable).mpr
      ((hpcont.norm.pow 2).intervalIntegrable (-r) r).1
  have hnLp : MemLp (characterPrime280 χ N) 2
      (volume.restrict (Set.Ioc (-r) r)) :=
    (memLp_two_iff_integrable_sq_norm hncont.aestronglyMeasurable).mpr
      ((hncont.norm.pow 2).intervalIntegrable (-r) r).1
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Set.Ioc (-r) r))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ : (2 : ℝ).HolderConjugate 2)
    (Filter.Eventually.of_forall
      (fun α => norm_nonneg (characterPrime280 (1 : DirichletCharacter ℂ q) N α)))
    (Filter.Eventually.of_forall (fun α => norm_nonneg (characterPrime280 χ N α)))
    (by norm_num; exact hpLp.norm) (by norm_num; exact hnLp.norm)
  norm_num only [Real.rpow_two] at hcs
  simp_rw [← Real.sqrt_eq_rpow] at hcs
  rw [← intervalIntegral.integral_of_le (show -r ≤ r by linarith),
    ← intervalIntegral.integral_of_le (show -r ≤ r by linarith),
    ← intervalIntegral.integral_of_le (show -r ≤ r by linarith)] at hcs
  have hp : (∫ α in -r..r, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N α‖ ^ 2) ≤
      P * ((N : ℝ) / Real.log N) :=
    hmass N q r hN3 hr.le hrh
  have hn : (∫ α in -r..r, ‖characterPrime280 χ N α‖ ^ 2) ≤
      B * (N : ℝ) / R * Real.log N ^ 13 := hb N hNB q hq hq7 χ hχ
  have hprod := sqrt_mass_le_491 N R P B hNp hRp hP hB hlog0
  have hfinal := (mul_le_mul (Real.sqrt_le_sqrt hp) (Real.sqrt_le_sqrt hn)
    (Real.sqrt_nonneg _) (by positivity)).trans hprod
  refine hcs.trans ?_
  exact hfinal

/-- LEAF. Pair step of equation 5.5. One nonprincipal character contributes, in
its two orders with the principal character, at most the scale N times the sixth
power of the logarithm of N divided by the totient of q and by the square root of
q times tau. This is the per character form of the displayed mixed bound; it
carries the two conjugate Gauss coefficients, the residue sum and the two
integrals. -/
theorem mixed_pair_bound491 (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        ∀ n : ℤ, ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖characterPair491 N q n 1 χ + characterPair491 N q n χ 1‖ ≤
            C * (N : ℝ) * Real.log N ^ 6 /
              ((q.totient : ℝ) * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- The four leaves together give the mixed character estimate of equation 5.5:
the term is a sum over the nonprincipal characters of pairs of ordered character
pairs, so the triangle inequality, the count of those characters and the per
character estimate give the displayed bound. -/
theorem mixed_bound491_split (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        letI : NeZero q := ⟨by omega⟩
        ∀ n : ℤ, ‖mixedTerm491 N q n‖ ≤
          C * (N : ℝ) * Real.log N ^ 6 /
            Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  obtain ⟨C, hC, N0, hle⟩ := mixed_pair_bound491 hM
  refine ⟨2 * C, by positivity, N0, ?_⟩
  intro N hN q hq hqQ
  classical
  letI : NeZero q := ⟨by omega⟩
  intro n
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hτpos : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hRpos : (0 : ℝ) < (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by positivity
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hstep : ∀ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)),
      ‖characterPair491 N q n 1 χ + characterPair491 N q n χ 1‖ ≤
        C * (N : ℝ) * Real.log N ^ 6 /
          ((q.totient : ℝ) * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
    intro χ hχ
    exact hle N hN q hq hqQ n χ (by simpa using hχ)
  have hcard : (((univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℕ) : ℝ) ≤
      (q.totient : ℝ) := by
    exact_mod_cast mixed_card491 q
  have hBnn : (0 : ℝ) ≤ C * (N : ℝ) * Real.log N ^ 6 /
      ((q.totient : ℝ) * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
    apply div_nonneg
    · positivity
    · positivity
  have hnorm : ‖mixedTerm491 N q n‖ ≤
      ∑ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)),
        ‖characterPair491 N q n 1 χ + characterPair491 N q n χ 1‖ := by
    simp only [mixedTerm491]
    exact norm_sum_le _ _
  have hfirst : ∑ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)),
        ‖characterPair491 N q n 1 χ + characterPair491 N q n χ 1‖ ≤
      ((univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) *
        (C * (N : ℝ) * Real.log N ^ 6 /
          ((q.totient : ℝ) * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := by
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  have harith : (q.totient : ℝ) * (C * (N : ℝ) * Real.log N ^ 6 /
      ((q.totient : ℝ) * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) =
      C * (N : ℝ) * Real.log N ^ 6 /
        Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    have hs : Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ≠ 0 :=
      (Real.sqrt_pos.mpr hRpos).ne'
    field_simp [hφpos.ne', hs]
  have hright : (0 : ℝ) ≤ C * (N : ℝ) * Real.log N ^ 6 /
      Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    apply div_nonneg
    · positivity
    · exact (Real.sqrt_pos.mpr hRpos).le
  calc ‖mixedTerm491 N q n‖
      ≤ ∑ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)),
          ‖characterPair491 N q n 1 χ + characterPair491 N q n χ 1‖ := hnorm
    _ ≤ ((univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) *
          (C * (N : ℝ) * Real.log N ^ 6 /
            ((q.totient : ℝ) * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := hfirst
    _ ≤ (q.totient : ℝ) * (C * (N : ℝ) * Real.log N ^ 6 /
          ((q.totient : ℝ) * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) :=
        mul_le_mul_of_nonneg_right hcard hBnn
    _ = C * (N : ℝ) * Real.log N ^ 6 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := harith
    _ ≤ 2 * C * (N : ℝ) * Real.log N ^ 6 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
        have heq : 2 * C * (N : ℝ) * Real.log N ^ 6 /
              Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) =
            2 * (C * (N : ℝ) * Real.log N ^ 6 /
              Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by ring
        rw [heq]
        linarith

end LeanLab.Linnik1951
