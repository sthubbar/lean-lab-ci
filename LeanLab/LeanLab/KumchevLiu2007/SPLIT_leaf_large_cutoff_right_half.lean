/-
Split of `leaf_large_cutoff_right_half` of
`LeanLab.KumchevLiu2007.SPLIT_lemma34_first_sum` along the proof of
Kumchev and Liu 2007, P0088, pages 11 to 12, Lemma 3.4, with
x = Y / 2, y = H, (m, k) = (1, k) and z the cut-off, as applied on page 15
after display 52. This is the right half [Y / 2, Y] of the t window; the left
half is split the same way in `Lemma34FirstSumCases.lean`, with x = Y / 4.

The steps follow the paper:

* page 11, first display of the proof: Phi(k, z) opened by the Moebius
  function, `Lemma34MoebiusOpen.roughWeight_eq_moebius_sum`.
* page 11, display 42: dyadic blocks d ~ D, at the cost of the square of the
  number of blocks, with A + 2 in place of A. Proved here.
* page 11, Case 1, D at most L^B: Lemma 3.1, LEAF `leaf_lemma31_type_one_right`.
* page 11, Case 2, L^B up to y x^(-1/2) L^(-B) with x = Y / 2: Lemma 3.2, LEAF
  `leaf_lemma32_type_two_right`.
* page 12, Case 3, D above y x^(-1/2) L^(-B): LEAF `leaf_case3_block_right`.

The Moebius opening and the block weight helpers are proved copies, with the
suffix _rh, of `Lemma34MoebiusOpen.roughWeight_eq_moebius_sum` and of
`block_weight_eq` and `norm_block_coeff_le` of `Lemma34FirstSumCases.lean`,
because those two modules are not built in this checkout.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SPLIT_lemma34_first_sum
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace LeanLab.KumchevLiu2007.Eq33RouteD

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology ArithmeticFunction
attribute [local instance] Classical.propDecidable


/-- P0088 page 11, first display of the proof of Lemma 3.4, for one k: for a
positive integer k, Phi(k, z) is the sum of the Moebius function over the
divisors d of k all of whose prime factors are below z. -/
theorem roughWeight_eq_moebius_sum_rh (z : ℝ) (k : ℕ) (hk : 0 < k) :
    roughWeight z k =
      ∑ d ∈ k.divisors.filter (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
  set P : Finset ℕ := k.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) with hP
  set r : ℕ := ∏ p ∈ P, p with hr
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hrk : r ∣ k :=
    Finset.prod_primes_dvd k (fun p hp => (hPprime p hp).prime)
      (fun p hp => Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
  have hr0 : r ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hPprime p hp).ne_zero)
  have hmemP : ∀ p : ℕ, p.Prime → p ∣ r → p ∈ P := by
    intro p hp hpr
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hpr
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp (hPprime q hq)).mp hpq
    rw [this]; exact hq
  have hsub : r.divisors ⊆
      k.divisors.filter (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z) := by
    intro d hd
    have hdr : d ∣ r := Nat.dvd_of_mem_divisors hd
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdr.trans hrk, hk.ne'⟩, ?_⟩
    intro p hp hpd
    exact (Finset.mem_filter.mp (hmemP p hp (hpd.trans hdr))).2
  have hstep1 : ∑ d ∈ r.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) =
      ∑ d ∈ k.divisors.filter (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
    apply Finset.sum_subset hsub
    intro d hd hnd
    obtain ⟨hdk, hsm⟩ := Finset.mem_filter.mp hd
    by_contra hne
    have hmu : ArithmeticFunction.moebius d ≠ 0 := by
      intro h0; apply hne; rw [h0]; simp
    have hsq : Squarefree d := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu
    have hdr : d ∣ r := by
      rw [← Nat.prod_primeFactors_of_squarefree hsq]
      apply Finset.prod_dvd_prod_of_subset
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      refine Finset.mem_filter.mpr ⟨?_, hsm p hpp hpd⟩
      exact Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans (Nat.dvd_of_mem_divisors hdk), hk.ne'⟩
    exact hnd (Nat.mem_divisors.mpr ⟨hdr, hr0⟩)
  have hstep2 : ∑ d ∈ r.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) =
      if r = 1 then 1 else 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℂ => f r)
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
      ArithmeticFunction.intCoe_apply] at h
    exact h
  rw [← hstep1, hstep2]
  unfold roughWeight
  have hiff : (∀ p : ℕ, p.Prime → p ∣ k → z ≤ (p : ℝ)) ↔ r = 1 := by
    constructor
    · intro h
      have hPe : P = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
        have := h p (Nat.prime_of_mem_primeFactors hp1) (Nat.dvd_of_mem_primeFactors hp1)
        linarith
      rw [hr, hPe, Finset.prod_empty]
    · intro h p hp hpk
      by_contra hlt
      push Not at hlt
      have hpP : p ∈ P :=
        Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpk, hk.ne'⟩, hlt⟩
      have hpr : p ∣ r := Finset.dvd_prod_of_mem _ hpP
      rw [h] at hpr
      exact hp.one_lt.ne' (Nat.dvd_one.mp hpr)
  by_cases hc : ∀ p : ℕ, p.Prime → p ∣ k → z ≤ (p : ℝ)
  · have h1 : r = 1 := hiff.mp hc
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true h1)]
  · have h1 : ¬ r = 1 := fun h => hc (hiff.mpr h)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_right_of_eq_false _ _ (eq_false h1)]

/-- P0088 page 11, Cases 1 and 2 of the proof of Lemma 3.4: the block weight
of display 42 as a sum over the dyadic divisors of the coefficient
mu(d) on the d dividing Pi(z), zero otherwise. -/
theorem block_weight_eq_rh (z : ℝ) (j n : ℕ) :
    (∑ d ∈ (n.divisors.filter
        (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
        (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
      ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
    ∑ m ∈ n.divisors.filter (fun m : ℕ => (2 : ℝ) ^ j ≤ (m : ℝ) ∧ (m : ℝ) < 2 * 2 ^ j),
      (if (∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < z) then
        ((ArithmeticFunction.moebius m : ℤ) : ℂ) else 0) := by
  rw [← Finset.sum_filter, Finset.filter_comm]

/-- The coefficient mu(d) on the d dividing Pi(z), zero otherwise, has norm
at most one, the case c = 0 of the bound tau(d)^c in Lemmas 3.1 and 3.2. -/
theorem norm_block_coeff_le_rh (z : ℝ) (m : ℕ) :
    ‖(if (∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < z) then
        ((ArithmeticFunction.moebius m : ℤ) : ℂ) else 0)‖ ≤ 1 := by
  split_ifs
  · rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · simp

/-- LEAF: P0088 page 10, Lemma 3.1, cited to Liu and Zhan 1997 Lemma 3.1, in
the lab form with x = Y / 2, t over [x, 2x] = [Y / 2, Y], y = H and
M ≤ (Y / 4)^(1/4) L^(-B), inside the paper's range M ≤ x^(1/4) L^(-B).
The double sum over
m ~ M and k of a_m g_t(m k) e(alpha m^2 k^2) is written as the sum over n = m k
of the weight sum over the divisors m ~ M of n of a_m. Class HARD, a cited
type I estimate. QUESTION: the target keeps H up to X^(1 - eps), above the
paper's y ≤ x; this leaf keeps that range. -/
theorem leaf_lemma31_type_one_right (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ v : ℤ, IsCoprime v (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - v| < (H / Real.log X ^ B)⁻¹ →
        ∀ a : ℕ → ℂ, (∀ m : ℕ, ‖a m‖ ≤ 1) →
        ∀ M : ℝ, 1 ≤ M → M ≤ (windowY X ε / 4) ^ (1 / 4 : ℝ) / Real.log X ^ B →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ n ∈ (squareWindow (windowY X ε)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
            (∑ m ∈ n.divisors.filter (fun m : ℕ => M ≤ (m : ℝ) ∧ (m : ℝ) < 2 * M), a m) *
              fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: P0088 page 10, Lemma 3.2, cited to Liu and Zhan 1997 Lemma 3.2, in
the lab form with x = Y / 2, t over [x, 2x] = [Y / 2, Y], y = H and
L^B ≤ M ≤ y x^(-1/2) L^(-B). The double
sum over m ~ M and k of a_m b_k g_t(m k) e(alpha m^2 k^2) is written as the sum
over n = m k of the weight sum over the divisors m ~ M of n of a_m b_(n/m).
Class HARD, a cited type II estimate. QUESTION: the same H range remark as
`leaf_lemma31_type_one_right`. -/
theorem leaf_lemma32_type_two_right (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ v : ℤ, IsCoprime v (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - v| < (H / Real.log X ^ B)⁻¹ →
        ∀ a b : ℕ → ℂ, (∀ m : ℕ, ‖a m‖ ≤ 1) → (∀ k : ℕ, ‖b k‖ ≤ 1) →
        ∀ M : ℝ, Real.log X ^ B ≤ M →
        M ≤ H / Real.sqrt (windowY X ε / 2) / Real.log X ^ B →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ n ∈ (squareWindow (windowY X ε)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
            (∑ m ∈ n.divisors.filter (fun m : ℕ => M ≤ (m : ℝ) ∧ (m : ℝ) < 2 * M),
                a m * b (n / m)) *
              fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: P0088 page 12, Case 3 of the proof of Lemma 3.4, with M = 1: the
dyadic block 2^j ≤ d < 2^(j+1) of display 42 when 2^j exceeds
V = y x^(-1/2) L^(-B), with x = Y / 2, t over [Y / 2, Y] and y = H. The paper
writes
d = d1 p p' d2 with L^B ≤ d1 p < V ≤ d1 p p', removes the side conditions by
Lemma 3.3 and applies Lemma 3.2. Class HARD. -/
theorem leaf_case3_block_right (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ v : ℤ, IsCoprime v (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - v| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ j : ℕ, H / Real.sqrt (windowY X ε / 2) / Real.log X ^ B < (2 : ℝ) ^ j →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ n ∈ (squareWindow (windowY X ε)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (n.divisors.filter
                (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- P0088 page 11, Cases 1 and 2 of the proof of Lemma 3.4: the block weight
of display 42 as a sum over the dyadic divisors of the coefficient
mu(d) on the d dividing Pi(z), zero otherwise. -/
theorem case1_block_right (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ v : ℤ, IsCoprime v (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - v| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, ∀ j : ℕ, (2 : ℝ) ^ j ≤ Real.log X ^ B →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ n ∈ (squareWindow (windowY X ε)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (n.divisors.filter
                (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B0, hB0, hleaf⟩ := leaf_lemma31_type_one_right A hA
  refine ⟨B0, hB0, ?_⟩
  intro B hB ε hε
  obtain ⟨C, X1, hC, hX1, hmain⟩ := hleaf B hB ε hε
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (2 * B) (by norm_num : (0 : ℝ) < 1 / 8)).bound
      (by norm_num : (0 : ℝ) < 1))
  refine ⟨C, max X1 (max T ((4 : ℝ) ^ 12)), hC, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlow hhigh α q v hcop hqP hqQ hclose z j hj
  have hXX1 : X1 ≤ X := (le_max_left _ _).trans hX
  have hXT : T ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hX4 : (4 : ℝ) ^ 12 ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hX2 : 2 ≤ X := hX1.trans hXX1
  have hX0 : 0 < X := by linarith
  have hX1' : 1 ≤ X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hP : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL _
  -- log X ^ (2B) ≤ X ^ (1/8)
  have hlog : Real.log X ^ B * Real.log X ^ B ≤ X ^ (1 / 8 : ℝ) := by
    have h := hT X hXT
    rw [← Real.rpow_add hL, show B + B = 2 * B by ring]
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL (2 * B)),
      abs_of_pos (Real.rpow_pos_of_pos hX0 (1 / 8 : ℝ)), one_mul] using h
  -- X ^ (1/8) ≤ (windowY X ε / 4) ^ (1/4)
  have h4 : (4 : ℝ) ≤ X ^ (1 / 12 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) hX4 (by norm_num : (0 : ℝ) ≤ 1 / 12)
    have e : ((4 : ℝ) ^ 12) ^ (1 / 12 : ℝ) = 4 := by
      rw [show (1 / 12 : ℝ) = ((12 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
    linarith
  have hhalf : X ^ (1 / 2 : ℝ) ≤ windowY X ε / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4), windowY]
    calc X ^ (1 / 2 : ℝ) * 4 ≤ X ^ (1 / 2 : ℝ) * X ^ (1 / 12 : ℝ) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = X ^ (7 / 12 : ℝ) := by rw [← Real.rpow_add hX0]; norm_num
      _ ≤ X ^ (7 / 12 + ε / 2) := Real.rpow_le_rpow_of_exponent_le hX1' (by linarith)
  have hquart : X ^ (1 / 8 : ℝ) ≤ (windowY X ε / 4) ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) hhalf (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rwa [← Real.rpow_mul hX0.le, show (1 / 2 : ℝ) * (1 / 4) = 1 / 8 by norm_num] at h
  have hM : (2 : ℝ) ^ j ≤ (windowY X ε / 4) ^ (1 / 4 : ℝ) / Real.log X ^ B := by
    rw [le_div_iff₀ hP]
    calc (2 : ℝ) ^ j * Real.log X ^ B ≤ Real.log X ^ B * Real.log X ^ B :=
          mul_le_mul_of_nonneg_right hj hP.le
      _ ≤ _ := hlog.trans hquart
  have h := hmain X H hXX1 hlow hhigh α q v hcop hqP hqQ hclose
    (fun m => if (∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < z) then
        ((ArithmeticFunction.moebius m : ℤ) : ℂ) else 0)
    (norm_block_coeff_le_rh z) ((2 : ℝ) ^ j) (one_le_pow₀ (by norm_num)) hM
  simp_rw [block_weight_eq_rh z j]
  exact h

/-- P0088 page 11, Case 2 of the proof of Lemma 3.4, with M = 1: the dyadic
block 2^j ≤ d < 2^(j+1) of display 42 with L^B < 2^j ≤ y x^(-1/2) L^(-B).
Lemma 3.2 applies with a_d = mu(d) on the d dividing Pi(z) and b_k = 1.
CONDITIONAL ON leaf_lemma32_type_two_right. -/
theorem case2_block_right (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ v : ℤ, IsCoprime v (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - v| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, ∀ j : ℕ, Real.log X ^ B < (2 : ℝ) ^ j →
        (2 : ℝ) ^ j ≤ H / Real.sqrt (windowY X ε / 2) / Real.log X ^ B →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ n ∈ (squareWindow (windowY X ε)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (n.divisors.filter
                (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B0, hB0, hleaf⟩ := leaf_lemma32_type_two_right A hA
  refine ⟨B0, hB0, ?_⟩
  intro B hB ε hε
  obtain ⟨C, X0, hC, hX0, hmain⟩ := hleaf B hB ε hε
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X H hX hlow hhigh α q v hcop hqP hqQ hclose z j hj1 hj2
  have h := hmain X H hX hlow hhigh α q v hcop hqP hqQ hclose
    (fun m => if (∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < z) then
        ((ArithmeticFunction.moebius m : ℤ) : ℂ) else 0)
    (fun _ => 1) (norm_block_coeff_le_rh z) (fun _ => by simp) ((2 : ℝ) ^ j) hj1.le hj2
  simp only [mul_one] at h
  simp_rw [block_weight_eq_rh z j]
  exact h

/-- P0088 page 11 to 12, Lemma 3.4 with M = 1, as applied on page 15 to the
first sum of display 52, on the right half [Y / 2, Y] of the window and for
the rough cut-offs 2 < z ≤ Y^(1/6 + eps/2): the statement of
`leaf_large_cutoff_right_half`. The rough weight is opened by the Moebius
function, the divisors are cut into at most 3 log X dyadic blocks, and each
block is Case 1, 2 or 3, each with A + 2 in place of A.
CONDITIONAL ON leaf_lemma31_type_one_right, leaf_lemma32_type_two_right and
leaf_case3_block_right. -/
theorem large_cutoff_right_half_of_cases (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  have hA2 : 0 < A + 2 := by linarith
  obtain ⟨B1, hB1, h1⟩ := case1_block_right (A + 2) hA2
  obtain ⟨B2, hB2, h2⟩ := case2_block_right (A + 2) hA2
  obtain ⟨B3, hB3, h3⟩ := leaf_case3_block_right (A + 2) hA2
  refine ⟨max B1 (max B2 B3), lt_max_of_lt_left hB1, ?_⟩
  intro B hB ε hε
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B (le_trans (le_max_left _ _) hB) ε hε
  obtain ⟨C2, X2, hC2, hX2, k2⟩ :=
    h2 B (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB) ε hε
  obtain ⟨C3, X3, hC3, hX3, k3⟩ :=
    h3 B (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB) ε hε
  set Cm := max C1 (max C2 C3) with hCm
  have hCm0 : 0 < Cm := lt_max_of_lt_left hC1
  refine ⟨(2 + ε) ^ 2 * Cm, max 3 (max X1 (max X2 X3)), by positivity,
    le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro X H hX hlow hup α q a hcop hq1 hq2 hdio z hz2 hzY
  have hX3' : 3 ≤ X := le_trans (le_max_left _ _) hX
  have hXX1 : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXX2 : X2 ≤ X :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hX
  have hXX3 : X3 ≤ X :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hX
  have hHpos : 0 < H := lt_of_lt_of_le (by positivity) hlow
  set L := Real.log X with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hLpos : 0 < L := by linarith
  set Y := windowY X ε with hY
  have hYpos : 0 < Y := by rw [hY]; unfold windowY; positivity
  set N := ⌊Real.sqrt Y⌋₊ with hN
  set J := Nat.log 2 N + 1 with hJdef
  set w : ℕ → ℕ → ℂ := fun j n => ∑ d ∈ (n.divisors.filter
                (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ) with hw
  have hrough : ∀ n ∈ squareWindow Y, roughWeight z n = ∑ j ∈ Finset.range J, w j n := by
    intro n hn
    unfold squareWindow at hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, hlo, -⟩ := hn
    have hsq : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hYpos
    have hn0 : 0 < n := by
      have : (0:ℝ) < n := by linarith
      exact_mod_cast this
    rw [roughWeight_eq_moebius_sum_rh z n hn0]
    apply dyadic_partition
    intro d hd
    have hd' := (Finset.mem_filter.mp hd).1
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd'
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact hn0.ne' (Nat.eq_zero_of_zero_dvd hdn)
    · have h1 : d ≤ n := Nat.le_of_dvd hn0 hdn
      have h2 : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
      exact lt_of_le_of_lt (h1.trans (by omega)) h2
  have hint : (∫ t in (Y / 2)..Y,
          ‖∑ m ∈ (squareWindow Y).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) =
      (∫ t in (Y / 2)..Y,
          ‖∑ m ∈ (squareWindow Y).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ j ∈ Finset.range J, w j m) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    congr 2
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hrough m (Finset.mem_filter.mp hm).1]
  rw [hint]
  set K := Cm * H ^ 2 / L ^ (A + 2) with hK
  have hCK : ∀ Ci : ℝ, Ci ≤ Cm → Ci * H ^ 2 / L ^ (A + 2) ≤ K := fun Ci h => by
    rw [hK]; gcongr
  have hblk : ∀ j ∈ Finset.range J, (∫ t in (Y / 2)..Y,
          ‖∑ m ∈ (squareWindow Y).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            w j m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤ K := by
    intro j _
    by_cases hc1 : (2:ℝ) ^ j ≤ L ^ B
    · exact (k1 X H hXX1 hlow hup α q a hcop hq1 hq2 hdio z j hc1).trans
        (hCK _ (le_max_left _ _))
    · by_cases hc2 : (2:ℝ) ^ j ≤ H / Real.sqrt (Y / 2) / L ^ B
      · exact (k2 X H hXX2 hlow hup α q a hcop hq1 hq2 hdio z j (lt_of_not_ge hc1) hc2).trans
          (hCK _ (le_trans (le_max_left _ _) (le_max_right _ _)))
      · exact (k3 X H hXX3 hlow hup α q a hcop hq1 hq2 hdio z hz2 hzY j
          (lt_of_not_ge hc2)).trans
          (hCK _ (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hmain := dyadic_mean_square_le (squareWindow Y) J w
    (fun m => fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H (Y / 2) Y K
    (by linarith) hblk
  refine hmain.trans ?_
  have hJ : (J : ℝ) ≤ (2 + ε) * L := by
    have hk : (Nat.log 2 N : ℝ) ≤ (7 / 12 + ε / 2) * L := by
      rcases Nat.eq_zero_or_pos N with h0 | hNpos
      · rw [h0]; simp; positivity
      · have hpow : (2:ℝ) ^ (Nat.log 2 N) ≤ (N:ℝ) := by
          exact_mod_cast Nat.pow_log_le_self 2 hNpos.ne'
        have hNs : (N:ℝ) ≤ Real.sqrt Y := Nat.floor_le (Real.sqrt_nonneg _)
        have hlog1 : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log (Real.sqrt Y) := by
          rw [← Real.log_pow]
          exact Real.log_le_log (by positivity) (hpow.trans hNs)
        have hsqrtlog : Real.log (Real.sqrt Y) = (7 / 12 + ε / 2) * L / 2 := by
          rw [Real.log_sqrt hYpos.le, hY]
          unfold windowY
          rw [Real.log_rpow (by linarith)]
        have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
          have := Real.log_two_gt_d9
          linarith
        have hk0 : (0:ℝ) ≤ (Nat.log 2 N : ℝ) := Nat.cast_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left hl2.le hk0]
    rw [hJdef]
    push_cast
    nlinarith
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hLpos A
  have hsplit : L ^ (A + 2) = L ^ A * L ^ 2 := by
    rw [Real.rpow_add hLpos, Real.rpow_two]
  rw [hK, hsplit]
  have hJ2 : (J:ℝ) ^ 2 ≤ ((2 + ε) * L) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hJ 2
  calc (J:ℝ) ^ 2 * (Cm * H ^ 2 / (L ^ A * L ^ 2))
      ≤ ((2 + ε) * L) ^ 2 * (Cm * H ^ 2 / (L ^ A * L ^ 2)) := by gcongr
    _ = (2 + ε) ^ 2 * Cm * H ^ 2 / L ^ A := by field_simp

/-- `leaf_large_cutoff_right_half` from its leaves: the statement is exactly
that of `large_cutoff_right_half_of_cases`. -/
theorem leaf_large_cutoff_right_half_split (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A :=
  large_cutoff_right_half_of_cases A hA

end LeanLab.KumchevLiu2007.Eq33RouteD

#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.leaf_large_cutoff_right_half_split

