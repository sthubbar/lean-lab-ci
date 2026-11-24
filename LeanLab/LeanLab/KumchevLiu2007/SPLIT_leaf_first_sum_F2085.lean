/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130. SPLIT of
`F2085.leaf_first_sum_F2085`, ROUTE BURST S98 burst-20261122, along the proof
of Lemma 3.4 on pages 11 and 12 with x = Y, y = H, (m, k) = (1, m):

* page 11, first display of the proof: Phi(k, z) opened by the Moebius
  function, `roughWeight_eq_moebius_sum_f1`, a proved copy of
  `Eq33RouteD.roughWeight_eq_moebius_sum_rh` of the staged file
  SPLIT_leaf_large_cutoff_right_half.lean, which this module cannot import.
* display 42: dyadic blocks d ~ D = 2^j with `Eq33RouteD.dyadic_partition` and
  the Cauchy inequality `Eq33RouteD.dyadic_mean_square_le`, at the cost of
  the square of the number of blocks, with A + 2 in the block leaves. Proved.
* Case 1, D at most L^B, Lemma 3.1: LEAF `leaf_case1_F2085`.
* Case 2, L^B below D at most V = H Y^(-1/2) L^(-B), Lemma 3.2: LEAF
  `leaf_case2_F2085`.
* Case 3, D above V, Lemma 3.3 then Lemma 3.2: LEAF `leaf_case3_F2085`.

The case leaves keep the t window Y/4 to Y, which is the two windows x to 2x
of the paper with x = Y/4 and x = Y/2; the boundary V is H Y^(-1/2) L^(-B),
within a factor 2 of the paper's y x^(-1/2) L^(-B) for both, a constant
absorbed by B in Lemma 3.2 and in the choice of V in Case 3.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SPLIT_rough_a23_hyp_F2085
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace LeanLab.KumchevLiu2007.F2085

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Task628
open scoped BigOperators Topology ArithmeticFunction
attribute [local instance] Classical.propDecidable

/-- P0088 page 11, first display of the proof of Lemma 3.4, for one k: for a
positive integer k, Phi(k, z) is the sum of the Moebius function over the
divisors d of k all of whose prime factors are below z. -/
theorem roughWeight_eq_moebius_sum_f1 (z : ℝ) (k : ℕ) (hk : 0 < k) :
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

/-- LEAF: P0088 page 11, Case 1 of the proof of Lemma 3.4 with x = Y, y = H,
(m, k) = (1, m), for the dyadic block D = 2^j of the Moebius variable d of
display 42 with D at most L^B: R = D at most x^(1/4) L^(-B) and display 42
follows from Lemma 3.1 of page 10, on the t windows x to 2x with x = Y/4 and
x = Y/2. Range of hypothesis A2.3 on page 7; alpha as in display 41. Class HARD. -/
theorem leaf_case1_F2085 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∀ η : ℝ, 0 < η →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
        windowY X ε ^ (2 / 3 + η) ≤ H → H ≤ windowY X ε →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, z ≤ windowY X ε ^ (1 / 6 + η / 2) →
        ∀ j : ℕ, (2 : ℝ) ^ j ≤ Real.log X ^ B →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (m.divisors.filter
                (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: P0088 page 11, Case 2 of the proof of Lemma 3.4 with x = Y, y = H,
(m, k) = (1, m), for the dyadic block D = 2^j of display 42 with L^B below D at
most V = H Y^(-1/2) L^(-B): display 42 follows from Lemma 3.2 of page 10 with
a_d = mu(d) on d dividing Pi(z) and b_k = 1, on the t windows x to 2x with
x = Y/4 and x = Y/2. Alpha as in display 41. Class HARD. -/
theorem leaf_case2_F2085 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∀ η : ℝ, 0 < η →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
        windowY X ε ^ (2 / 3 + η) ≤ H → H ≤ windowY X ε →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, z ≤ windowY X ε ^ (1 / 6 + η / 2) →
        ∀ j : ℕ, Real.log X ^ B < (2 : ℝ) ^ j →
        (2 : ℝ) ^ j ≤ H / Real.sqrt (windowY X ε) / Real.log X ^ B →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (m.divisors.filter
                (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: P0088 page 12, Case 3 of the proof of Lemma 3.4 with x = Y, y = H,
(m, k) = (1, m), for the dyadic block D = 2^j of display 42 with D above
V = H Y^(-1/2) L^(-B): d = d1 p p' d2 with L^B at most d1 p < V at most d1 p p',
the side conditions removed by Lemma 3.3, then Lemma 3.2. Needs z at most
z1 = Y^(1/6 + eta/2), below y x^(-1/2) L^(-2B). Class HARD. -/
theorem leaf_case3_F2085 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∀ η : ℝ, 0 < η →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
        windowY X ε ^ (2 / 3 + η) ≤ H → H ≤ windowY X ε →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, z ≤ windowY X ε ^ (1 / 6 + η / 2) →
        ∀ j : ℕ, H / Real.sqrt (windowY X ε) / Real.log X ^ B < (2 : ℝ) ^ j →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (m.divisors.filter
                (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry
/-- Assembly: the exact statement of `leaf_first_sum_F2085` from the three
case leaves, by the Moebius opening, the dyadic partition of d and the Cauchy
inequality over at most (2 + eps) log X blocks, with A + 2 in the leaves. -/
theorem leaf_first_sum_F2085_split (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∀ η : ℝ, 0 < η →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
        windowY X ε ^ (2 / 3 + η) ≤ H → H ≤ windowY X ε / Real.log X ^ A →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, z ≤ windowY X ε ^ (1 / 6 + η / 2) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  have hA2 : 0 < A + 2 := by linarith
  obtain ⟨B1, hB1, h1⟩ := leaf_case1_F2085 (A + 2) hA2
  obtain ⟨B2, hB2, h2⟩ := leaf_case2_F2085 (A + 2) hA2
  obtain ⟨B3, hB3, h3⟩ := leaf_case3_F2085 (A + 2) hA2
  refine ⟨max B1 (max B2 B3), lt_max_of_lt_left hB1, ?_⟩
  intro B hB ε hε hε' η hη
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B (le_trans (le_max_left _ _) hB) ε hε hε' η hη
  obtain ⟨C2, X2, hC2, hX2, k2⟩ :=
    h2 B (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB) ε hε hε' η hη
  obtain ⟨C3, X3, hC3, hX3, k3⟩ :=
    h3 B (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB) ε hε hε' η hη
  set Cm := max C1 (max C2 C3) with hCm
  have hCm0 : 0 < Cm := lt_max_of_lt_left hC1
  refine ⟨(2 + ε) ^ 2 * Cm, max 3 (max X1 (max X2 X3)), by positivity,
    le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro X H hX hlow hup0 α q a hcop hq1 hq2 hdio z hzY
  have hX3' : 3 ≤ X := le_trans (le_max_left _ _) hX
  have hXX1 : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXX2 : X2 ≤ X :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hX
  have hXX3 : X3 ≤ X :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hX
  set L := Real.log X with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hLpos : 0 < L := by linarith
  set Y := windowY X ε with hY
  have hYpos : 0 < Y := by rw [hY]; unfold windowY; positivity
  have hup : H ≤ Y := hup0.trans (div_le_self hYpos.le (Real.one_le_rpow hL1 hA.le))
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
    rw [roughWeight_eq_moebius_sum_f1 z n hn0]
    apply Eq33RouteD.dyadic_partition
    intro d hd
    have hd' := (Finset.mem_filter.mp hd).1
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd'
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact hn0.ne' (Nat.eq_zero_of_zero_dvd hdn)
    · have h1 : d ≤ n := Nat.le_of_dvd hn0 hdn
      have h2 : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
      exact lt_of_le_of_lt (h1.trans (by omega)) h2
  have hint : (∫ t in (Y / 4)..Y,
          ‖∑ m ∈ (squareWindow Y).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) =
      (∫ t in (Y / 4)..Y,
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
  have hblk : ∀ j ∈ Finset.range J, (∫ t in (Y / 4)..Y,
          ‖∑ m ∈ (squareWindow Y).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            w j m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤ K := by
    intro j _
    by_cases hc1 : (2:ℝ) ^ j ≤ L ^ B
    · exact (k1 X H hXX1 hlow hup α q a hcop hq1 hq2 hdio z hzY j hc1).trans
        (hCK _ (le_max_left _ _))
    · by_cases hc2 : (2:ℝ) ^ j ≤ H / Real.sqrt Y / L ^ B
      · exact (k2 X H hXX2 hlow hup α q a hcop hq1 hq2 hdio z hzY j
          (lt_of_not_ge hc1) hc2).trans
          (hCK _ (le_trans (le_max_left _ _) (le_max_right _ _)))
      · exact (k3 X H hXX3 hlow hup α q a hcop hq1 hq2 hdio z hzY j
          (lt_of_not_ge hc2)).trans
          (hCK _ (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hmain := Eq33RouteD.dyadic_mean_square_le (squareWindow Y) J w
    (fun m => fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H (Y / 4) Y K
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

/-- The split statement is character for character the parent leaf. -/
example : type_of% @leaf_first_sum_F2085 := leaf_first_sum_F2085_split

end LeanLab.KumchevLiu2007.F2085
