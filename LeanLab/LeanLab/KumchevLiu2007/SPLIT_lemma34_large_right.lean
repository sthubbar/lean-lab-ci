/-
Split of `leaf_large_cutoff_right_half` of `LeanLab.KumchevLiu2007.SPLIT_lemma34_first_sum`,
the genuinely rough case 2 < z ≤ Y^(1/6 + eps/2) of the first sum of display 52
of Kumchev and Liu 2007, P0088, on the half window [Y / 2, Y].

The pieces follow the proof of Lemma 3.4 on pages 11 and 12 of P0088 with
x = Y, y = H, (m, k) = (1, m) and a_1 = 1:

* `roughWeight_eq_sum_moebius`, the first display of the proof: the rough
  indicator Phi(k, z) is the sum of mu(d) over the divisors d of k that divide
  Pi(z), the squarefree d with all prime factors below z. Proved.
* `dyadic` assembly: the divisors d are cut into the blocks d ∼ D with
  D = 2^j, at most 3 log X of them, and the Cauchy inequality reduces the
  estimate to display 42 for one block, with A + 2 in place of A. Proved,
  using `dyadic_partition` and `dyadic_mean_square_le` of Eq33RouteD.
* display 42 in the three cases of the proof. Case 1, D ≤ L^B, is proved
  from the LEAF `leaf_lemma31_liu_zhan`, Lemma 3.1 in the shape of the square
  window. Case 2, L^B ≤ D ≤ y x^(-1/2) L^(-B), is proved from the LEAF
  `leaf_lemma32_liu_zhan`, Lemma 3.2 in the same shape. Case 3,
  D ≥ y x^(-1/2) L^(-B), is proved from the LEAF
  `leaf_case3_reduction_lemma33_core`, the factorisation of d with Lemma 3.3, and
  from `leaf_lemma32_liu_zhan` over dyadic blocks of v; the choice of s,
  `largest_primes_split`, is proved. Lemmas 3.1 and 3.2 of P0088 are
  Lemmas 3.1 and 3.2 of Liu and Zhan 1997.

Here L is log X, not log Y as on page 11; the two differ by the bounded
factor 7/12 + eps/2, which the free exponent B absorbs. The window and the H
range are those of the parent statement; the QUESTION on H above Y recorded
in Eq33RouteD stays open and is carried by each leaf.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Eq33RouteD

namespace LeanLab.KumchevLiu2007.Eq33RouteD.LargeRight1122

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a LeanLab.KumchevLiu2007.Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 11, the first display of the proof of Lemma 3.4, with the
rough indicator Phi of page 4 display 10: for a positive integer m, Phi(m, z)
is the sum of mu(d) over the divisors d of m with d dividing Pi(z), that is
the squarefree divisors all of whose prime factors are below z. -/
theorem roughWeight_eq_sum_moebius (z : ℝ) (m : ℕ) (hm : m ≠ 0) :
    roughWeight z m = ∑ d ∈ m.divisors.filter (fun d : ℕ => Squarefree d ∧
        ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z),
      ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
  set s := m.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) with hs
  set n := ∏ p ∈ s, p with hn
  have hsP : ∀ p ∈ s, p.Prime := fun p hp =>
    (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1
  have hn0 : n ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (hsP p hp).ne_zero
  have hnpf : n.primeFactors = s := Nat.primeFactors_prod hsP
  have hnsq : Squarefree n := by
    rw [hn]
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ fun p hp => (hsP p hp).squarefree
    intro p hp r hr hpr
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hsP p hp) (hsP r hr)).mpr hpr)
  have hnm : n ∣ m := (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans
    (Nat.prod_primeFactors_dvd m)
  have hset : m.divisors.filter (fun d : ℕ => Squarefree d ∧
        ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z) = n.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdm, -⟩, hsq, hp⟩
      have hd0 : d ≠ 0 := hsq.ne_zero
      refine ⟨?_, hn0⟩
      rw [← Nat.prod_primeFactors_of_squarefree hsq, Nat.prod_primeFactors_dvd_iff hn0, hnpf]
      intro p hpd
      obtain ⟨hpp, hpd', -⟩ := Nat.mem_primeFactors.mp hpd
      exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp, hpd'.trans hdm, hm⟩,
        hp p hpp hpd'⟩
    · rintro ⟨hdn, -⟩
      refine ⟨⟨hdn.trans hnm, hm⟩, hnsq.squarefree_of_dvd hdn, fun p hpp hpd => ?_⟩
      have : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans hdn, hn0⟩
      rw [hnpf] at this
      exact (Finset.mem_filter.mp this).2
  rw [hset]
  have hsum : (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
      if n = 1 then 1 else 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℂ => f n)
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
    simpa [ArithmeticFunction.intCoe_apply] using h
  rw [hsum]
  have hiff : n = 1 ↔ ∀ p : ℕ, p.Prime → p ∣ m → z ≤ (p : ℝ) := by
    constructor
    · intro h1 p hpp hpm
      by_contra hlt
      have : p ∈ s := Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp, hpm, hm⟩,
        lt_of_not_ge hlt⟩
      rw [← hnpf, h1] at this
      simp at this
    · intro h
      have hse : s = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        obtain ⟨hpm, hpz⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hpm
        exact absurd (h p hpp hpd) (not_le.mpr hpz)
      rw [hn, hse, Finset.prod_empty]
  unfold roughWeight
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.mpr h1) h2
  · exact absurd (hiff.mp h2) h1
  · rfl

/-- LEAF: P0088 page 10 Lemma 3.1, which is Lemma 3.1 of Liu and Zhan 1997,
with x = Y / 2 and y = H, in the shape of the square window of page 2 display 5:
for coefficients a_d with |a_d| ≤ tau(d)^c and 1 ≤ D ≤ x^(1/4) L^(-B), the
mean square over t of the sum of a_d e(alpha d^2 k^2) over d ∼ D and the k with
t < d^2 k^2 ≤ t + y is O(y^2 L^(-A)). The sum over the pairs (d, k) is written
as the sum over n = dk of the divisor sum of a_d over d ∼ D. Here L is log X;
the factor between log X and log Y and the factor 2^(1/4) between Y and
x = Y / 2 are absorbed by B. Class HARD, cited input. -/
theorem leaf_lemma31_liu_zhan (c : ℕ) (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ w : ℕ → ℂ, (∀ d : ℕ, ‖w d‖ ≤ (d.divisors.card : ℝ) ^ c) →
        ∀ D : ℝ, 1 ≤ D → D * Real.log X ^ B ≤ windowY X ε ^ (1 / 4 : ℝ) →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ m.divisors.filter (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D), w d) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: P0088 page 10 Lemma 3.2, which is Lemma 3.2 of Liu and Zhan 1997,
with x = Y / 2 and y = H, in the shape of the square window of page 2 display 5:
for coefficients a_d and b_k with |a_d| ≤ tau(d)^c, |b_k| ≤ tau(k)^c and
L^B ≤ D ≤ y Y^(-1/2) L^(-B), the mean square over t of the sum of
a_d b_k e(alpha d^2 k^2) over d ∼ D and the k with t < d^2 k^2 ≤ t + y is
O(y^2 L^(-A)). The upper end is written D Y^(1/2) L^B ≤ y, which lies inside
the range y x^(-1/2) L^(-B) of the lemma. Here L is log X. Class HARD, cited
input. -/
theorem leaf_lemma32_liu_zhan (c : ℕ) (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ w v : ℕ → ℂ, (∀ d : ℕ, ‖w d‖ ≤ (d.divisors.card : ℝ) ^ c) →
        (∀ k : ℕ, ‖v k‖ ≤ (k.divisors.card : ℝ) ^ c) →
        ∀ D : ℝ, Real.log X ^ B ≤ D → D * Real.sqrt (windowY X ε) * Real.log X ^ B ≤ H →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ m.divisors.filter (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                w d * v (m / d)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- P0088 page 11, the Moebius block of display 42 as a divisor sum with the
coefficient a_d = mu(d) on the d dividing Pi(z) and zero elsewhere. -/
theorem moebius_block_eq (z D : ℝ) (m : ℕ) :
    (∑ d ∈ (m.divisors.filter (fun d : ℕ => Squarefree d ∧
          ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
        (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
      ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
    ∑ d ∈ m.divisors.filter (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
      (if Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z then
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0) := by
  rw [Finset.filter_filter, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hP : Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z <;>
    by_cases hQ : D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D <;> simp [hP, hQ]

/-- P0088 page 11: the Moebius coefficient of display 42 satisfies the bound
|a_d| ≤ tau(d)^0 of Lemmas 3.1 and 3.2. -/
theorem moebius_coeff_norm_le (z : ℝ) (d : ℕ) :
    ‖(if Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z then
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0)‖ ≤ (d.divisors.card : ℝ) ^ 0 := by
  rw [pow_zero]
  split_ifs
  · have h := ArithmeticFunction.abs_moebius_le_one (n := d)
    rw [Complex.norm_intCast]
    exact_mod_cast h
  · simp

/-- P0088 page 11, proof of Lemma 3.4, display 42 in Case 1, D ≤ L^B,
with x = Y / 2, y = H, M = 1 and a_1 = 1: the block is the convolution
b_r = mu(r) for r ∼ D dividing Pi(z), with R = D ≤ x^(1/4) L^(-B) once X is
large, and Lemma 3.1 applies with c = 0.
CONDITIONAL ON leaf_lemma31_liu_zhan. -/
theorem case1_of_lemma31 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ D : ℝ, 1 ≤ D → D ≤ Real.log X ^ B →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (m.divisors.filter (fun d : ℕ => Squarefree d ∧
                  ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B0, hB0, h⟩ := leaf_lemma31_liu_zhan 0 A hA
  refine ⟨B0, hB0, fun B hB ε hε => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h B hB ε hε
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (2 * B) (by norm_num : (0 : ℝ) < 7 / 48)).bound
      (by norm_num : (0 : ℝ) < 1))
  refine ⟨C, max X0 (max T 3), hC, hX0.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHX α q a hcop hqP hqQ hclose z hz2 hz D hD1 hD2
  have hXa : X0 ≤ X := (le_max_left _ _).trans hX
  have hX3 : 3 ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hX0' : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0']
    linarith [Real.exp_one_lt_d9]
  have hL : 0 < Real.log X := by linarith
  have hlog : Real.log X ^ (2 * B) ≤ X ^ (7 / 48 : ℝ) := by
    have h0 := hT X (((le_max_left _ _).trans (le_max_right _ _)).trans hX)
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL _),
      abs_of_pos (Real.rpow_pos_of_pos hX0' (7 / 48 : ℝ)), one_mul] using h0
  have hY4 : X ^ (7 / 48 : ℝ) ≤ windowY X ε ^ (1 / 4 : ℝ) := by
    rw [windowY, ← Real.rpow_mul hX0'.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hD : D * Real.log X ^ B ≤ windowY X ε ^ (1 / 4 : ℝ) := by
    calc
      D * Real.log X ^ B ≤ Real.log X ^ B * Real.log X ^ B :=
        mul_le_mul_of_nonneg_right hD2 (Real.rpow_nonneg hL.le _)
      _ = Real.log X ^ (2 * B) := by rw [← Real.rpow_add hL]; ring_nf
      _ ≤ _ := hlog.trans hY4
  have e := k X H hXa hH hHX α q a hcop hqP hqQ hclose
    (fun d => if Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z then
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0)
    (moebius_coeff_norm_le z) D hD1 hD
  simpa only [moebius_block_eq] using e

/-- P0088 page 11, proof of Lemma 3.4, display 42 in Case 2,
L^B ≤ D ≤ y x^(-1/2) L^(-B), with x = Y / 2, y = H, M = 1 and a_1 = 1: the block
is the bilinear form with a_d = mu(d) on the d ∼ D dividing Pi(z) and the
trivial convolution b_k = 1, and Lemma 3.2 applies with c = 0.
CONDITIONAL ON leaf_lemma32_liu_zhan. -/
theorem case2_of_lemma32 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ D : ℝ, Real.log X ^ B ≤ D → D * Real.sqrt (windowY X ε) * Real.log X ^ B ≤ H →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (m.divisors.filter (fun d : ℕ => Squarefree d ∧
                  ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B0, hB0, h⟩ := leaf_lemma32_liu_zhan 0 A hA
  refine ⟨B0, hB0, fun B hB ε hε => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h B hB ε hε
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X H hX hH hHX α q a hcop hqP hqQ hclose z hz2 hz D hD1 hD2
  have e := k X H hX hH hHX α q a hcop hqP hqQ hclose
    (fun d => if Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z then
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0)
    (fun _ => (1 : ℂ)) (moebius_coeff_norm_le z) (fun _ => by simp) D hD1 hD2
  simpa only [moebius_block_eq, mul_one] using e

/-- P0088 page 12, Case 3 of the proof of Lemma 3.4, the choice of s: for a
list of integers p1, p2, ... each at least one and below z, whose product is at
least V > 1, some prefix product p1 ... ps is at most V, the next prefix
product p1 ... ps+1 is at least V, and V < z p1 ... ps, that is
z^(-1) V < p1 ... ps. -/
theorem prefix_split : ∀ (l : List ℕ) (z V : ℝ), (∀ p ∈ l, 1 ≤ p ∧ (p : ℝ) < z) →
    1 < V → V ≤ (l.prod : ℝ) →
    ∃ s : ℕ, s < l.length ∧ ((l.take s).prod : ℝ) ≤ V ∧ V ≤ ((l.take (s + 1)).prod : ℝ) ∧
      V < z * ((l.take s).prod : ℝ)
  | [], z, V, _, hV1, hV => by
    simp at hV
    linarith
  | p :: t, z, V, hl, hV1, hV => by
    obtain ⟨hp1, hpz⟩ := hl p (by simp)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
    by_cases hVp : V ≤ (p : ℝ)
    · refine ⟨0, by simp, by simpa using hV1.le, by simpa using hVp, by simpa using hVp.trans_lt hpz⟩
    · rw [not_le] at hVp
      have hV' : 1 < V / p := by rw [lt_div_iff₀ hp0]; linarith
      have hVt : V / p ≤ (t.prod : ℝ) := by
        rw [div_le_iff₀ hp0]
        have : ((p :: t).prod : ℝ) = p * t.prod := by simp
        rw [this] at hV
        linarith
      obtain ⟨s, hs, h1, h2, h3⟩ := prefix_split t z (V / p)
        (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hV' hVt
      refine ⟨s + 1, by simpa using hs, ?_, ?_, ?_⟩
      · simp only [List.take_succ_cons, List.prod_cons, Nat.cast_mul]
        rw [le_div_iff₀ hp0] at h1
        linarith
      · simp only [List.take_succ_cons, List.prod_cons, Nat.cast_mul]
        rw [div_le_iff₀ hp0] at h2
        linarith
      · simp only [List.take_succ_cons, List.prod_cons, Nat.cast_mul]
        rw [div_lt_iff₀ hp0] at h3
        linarith

/-- P0088 page 12, Case 3 of the proof of Lemma 3.4: each d dividing Pi(z)
with d ≥ V > 1 factors as d = p1 ... pr with pr < ... < p1 < z, and there is
s < r with z^(-1) V < p1 ... ps ≤ V ≤ p1 ... ps+1. The primes are listed in
decreasing order. -/
theorem largest_primes_split (d : ℕ) (hd : Squarefree d) (z V : ℝ)
    (hz : ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z) (hV1 : 1 < V) (hVd : V ≤ (d : ℝ)) :
    ∃ s : ℕ, s < (d.primeFactors.sort (· ≥ ·)).length ∧
      (((d.primeFactors.sort (· ≥ ·)).take s).prod : ℝ) ≤ V ∧
      V ≤ (((d.primeFactors.sort (· ≥ ·)).take (s + 1)).prod : ℝ) ∧
      V < z * (((d.primeFactors.sort (· ≥ ·)).take s).prod : ℝ) := by
  have hprod : ((d.primeFactors.sort (· ≥ ·)).prod : ℕ) = d := by
    rw [← Multiset.prod_coe, Finset.sort_eq]
    have h := Nat.prod_primeFactors_of_squarefree hd
    rw [Finset.prod_eq_multiset_prod, Multiset.map_id'] at h
    exact h
  refine prefix_split _ z V (fun p hp => ?_) hV1 (by rw [hprod]; exact hVd)
  rw [Finset.mem_sort] at hp
  obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
  exact ⟨hpp.one_lt.le, hz p hpp hpd⟩

/-- LEAF: P0088 page 12, Case 3 of the proof of Lemma 3.4, the display after
the factorisation d = p1 ... pr with the s of `largest_primes_split`: by
Lemma 3.3, Kumchev Lemma 2.7, the left side of display 42 is at most L^c times
the mean square of a bilinear form in a_v b_u with v = p d1 in [L^B, V], plus
L^c. Both coefficient bounds are written tau^c; v ≤ V is written
v Y^(1/2) L^B ≤ y. No hypothesis on alpha is used. See QUESTION Q3 in the
notes. Class HARD, cited input. -/
theorem leaf_case3_reduction_lemma33_core :
    ∃ c0 : ℕ, ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε →
      ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) → ∀ α : ℝ,
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ D : ℝ, 1 ≤ D → H ≤ D * Real.sqrt (windowY X ε) * Real.log X ^ B →
        H < windowY X ε * Real.log X ^ B →
        ∃ w v : ℕ → ℂ, (∀ d : ℕ, ‖w d‖ ≤ (d.divisors.card : ℝ) ^ c0) ∧
          (∀ k : ℕ, ‖v k‖ ≤ (k.divisors.card : ℝ) ^ c0) ∧
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (m.divisors.filter (fun d : ℕ => Squarefree d ∧
                  ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            Real.log X ^ (c0 : ℝ) *
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ m.divisors.filter (fun d : ℕ => Real.log X ^ B ≤ (d : ℝ) ∧
                (d : ℝ) * Real.sqrt (windowY X ε) * Real.log X ^ B ≤ H),
              w d * v (m / d)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) +
            Real.log X ^ (c0 : ℝ) := by
  sorry

/-- P0088 page 12, the display after the factorisation in Case 3, on the whole
written range of H: for H < Y L^B it is the LEAF
`leaf_case3_reduction_lemma33_core`; for H ≥ Y L^B, outside the range y ≤ x of
the paper, every m of the square window has m Y^(1/2) L^B ≤ H, so v = 1 at
k = 1 and a_v the Moebius block give the left side itself on the right.
CONDITIONAL ON leaf_case3_reduction_lemma33_core. -/
theorem case3_reduction_lemma33 :
    ∃ c0 : ℕ, ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε →
      ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) → ∀ α : ℝ,
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ D : ℝ, 1 ≤ D → H ≤ D * Real.sqrt (windowY X ε) * Real.log X ^ B →
        ∃ w v : ℕ → ℂ, (∀ d : ℕ, ‖w d‖ ≤ (d.divisors.card : ℝ) ^ c0) ∧
          (∀ k : ℕ, ‖v k‖ ≤ (k.divisors.card : ℝ) ^ c0) ∧
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (m.divisors.filter (fun d : ℕ => Squarefree d ∧
                  ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            Real.log X ^ (c0 : ℝ) *
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ m.divisors.filter (fun d : ℕ => Real.log X ^ B ≤ (d : ℝ) ∧
                (d : ℝ) * Real.sqrt (windowY X ε) * Real.log X ^ B ≤ H),
              w d * v (m / d)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) +
            Real.log X ^ (c0 : ℝ) := by
  obtain ⟨c, hcore⟩ := leaf_case3_reduction_lemma33_core
  refine ⟨c + 1, fun B hB ε hε => ?_⟩
  obtain ⟨X1, hX1, k⟩ := hcore B hB ε hε
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop B (by norm_num : (0 : ℝ) < 7 / 24)).bound
      (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨max X1 (max T 3), hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHX α z hz2 hz D hD1 hD3
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXT : T ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hX3 : 3 ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hX0 : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    linarith [Real.exp_one_lt_d9]
  have hL : 0 < Real.log X := by linarith
  have hcard : ∀ n : ℕ, n ≠ 0 → (1 : ℝ) ≤ (n.divisors.card : ℝ) := fun n hn => by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩
  have hLc : 1 ≤ Real.log X ^ ((c + 1 : ℕ) : ℝ) := Real.one_le_rpow hL1 (by positivity)
  by_cases hsmall : H < windowY X ε * Real.log X ^ B
  · obtain ⟨w, v, hw, hv, hb⟩ := k X H hXa hH hHX α z hz2 hz D hD1 hD3 hsmall
    refine ⟨fun d => if d = 0 then 0 else w d, fun k => if k = 0 then 0 else v k, ?_, ?_, ?_⟩
    · intro d
      by_cases h : d = 0
      · simp only [h, if_true, norm_zero]
        positivity
      · simp only [h, if_false]
        exact (hw d).trans (pow_le_pow_right₀ (hcard d h) (Nat.le_succ c))
    · intro k
      by_cases h : k = 0
      · simp only [h, if_true, norm_zero]
        positivity
      · simp only [h, if_false]
        exact (hv k).trans (pow_le_pow_right₀ (hcard k h) (Nat.le_succ c))
    · have heq : ∀ m : ℕ, (∑ d ∈ m.divisors.filter (fun d : ℕ => Real.log X ^ B ≤ (d : ℝ) ∧
            (d : ℝ) * Real.sqrt (windowY X ε) * Real.log X ^ B ≤ H),
            (if d = 0 then 0 else w d) * (if m / d = 0 then 0 else v (m / d))) =
          ∑ d ∈ m.divisors.filter (fun d : ℕ => Real.log X ^ B ≤ (d : ℝ) ∧
            (d : ℝ) * Real.sqrt (windowY X ε) * Real.log X ^ B ≤ H), w d * v (m / d) := by
        intro m
        refine Finset.sum_congr rfl fun d hd => ?_
        obtain ⟨hdm, hm0⟩ := Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1
        have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hm0 hdm
        have hq : m / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdm)
          (Nat.pos_of_ne_zero hd0)).ne'
        simp only [hd0, hq, if_false]
      simp only [heq]
      have hmono : Real.log X ^ (c : ℝ) ≤ Real.log X ^ ((c + 1 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by push_cast; linarith)
      refine hb.trans (add_le_add (mul_le_mul_of_nonneg_right hmono ?_) hmono)
      exact intervalIntegral.integral_nonneg (by
        have : 0 < windowY X ε := by unfold windowY; exact Real.rpow_pos_of_pos hX0 _
        linarith) fun t _ => by positivity
  · have hbig : windowY X ε * Real.log X ^ B ≤ H := not_lt.mp hsmall
    have hY0 : 0 < windowY X ε := by unfold windowY; exact Real.rpow_pos_of_pos hX0 _
    have hsq : X ^ (7 / 24 : ℝ) ≤ Real.sqrt (windowY X ε) := by
      rw [Real.sqrt_eq_rpow, windowY, ← Real.rpow_mul hX0.le]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hlogB : Real.log X ^ B ≤ 1 / 2 * X ^ (7 / 24 : ℝ) := by
      have h0 := hT X hXT
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL _),
        abs_of_pos (Real.rpow_pos_of_pos hX0 (7 / 24 : ℝ))] using h0
    have hLB : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL B
    refine ⟨fun m => ∑ d ∈ (m.divisors.filter (fun d : ℕ => Squarefree d ∧
                  ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ),
      fun k => if k = 1 then 1 else 0, ?_, ?_, ?_⟩
    · intro m
      by_cases hm : m = 0
      · subst hm
        simp
      · refine (norm_sum_le _ _).trans ?_
        calc
          _ ≤ ∑ _d ∈ (m.divisors.filter (fun d : ℕ => Squarefree d ∧
                  ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D), (1 : ℝ) := by
            refine Finset.sum_le_sum fun d _ => ?_
            rw [Complex.norm_intCast]
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          _ ≤ (m.divisors.card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
            exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _)
          _ ≤ (m.divisors.card : ℝ) ^ (c + 1) := by
            simpa using pow_le_pow_right₀ (hcard m hm) (Nat.succ_le_succ (Nat.zero_le c))
    · intro k
      by_cases h : k = 1
      · subst h
        simp
      · simp only [h, if_false, norm_zero]
        positivity
    · have hinner : ∀ m ∈ squareWindow (windowY X ε),
          (∑ d ∈ m.divisors.filter (fun d : ℕ => Real.log X ^ B ≤ (d : ℝ) ∧
            (d : ℝ) * Real.sqrt (windowY X ε) * Real.log X ^ B ≤ H),
            (∑ e ∈ (d.divisors.filter (fun e : ℕ => Squarefree e ∧
                  ∀ p : ℕ, p.Prime → p ∣ e → (p : ℝ) < z)).filter
                (fun e : ℕ => D ≤ (e : ℝ) ∧ (e : ℝ) < 2 * D),
              ((ArithmeticFunction.moebius e : ℤ) : ℂ)) *
              (if m / d = 1 then 1 else 0)) =
          ∑ e ∈ (m.divisors.filter (fun e : ℕ => Squarefree e ∧
                  ∀ p : ℕ, p.Prime → p ∣ e → (p : ℝ) < z)).filter
                (fun e : ℕ => D ≤ (e : ℝ) ∧ (e : ℝ) < 2 * D),
              ((ArithmeticFunction.moebius e : ℤ) : ℂ) := by
        intro m hm
        obtain ⟨-, hm1, hm2⟩ := Finset.mem_filter.mp hm
        have hmpos : (0 : ℝ) < m :=
          lt_of_lt_of_le (by positivity : (0 : ℝ) < Real.sqrt (windowY X ε) / 2) hm1
        have hm0 : m ≠ 0 := by
          rintro rfl
          simp at hmpos
        have hmR : Real.log X ^ B ≤ (m : ℝ) ∧
            (m : ℝ) * Real.sqrt (windowY X ε) * Real.log X ^ B ≤ H := by
          refine ⟨by linarith, ?_⟩
          have hmY : (m : ℝ) * Real.sqrt (windowY X ε) ≤ windowY X ε := by
            have := Real.mul_self_sqrt hY0.le
            nlinarith [Real.sqrt_nonneg (windowY X ε)]
          nlinarith
        rw [Finset.sum_eq_single m]
        · rw [Nat.div_self (Nat.pos_of_ne_zero hm0), if_pos rfl, mul_one]
        · intro d hd hdm
          obtain ⟨hdd, -⟩ := Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1
          have hne : m / d ≠ 1 := by
            intro h1
            apply hdm
            have := Nat.div_mul_cancel hdd
            rw [h1, one_mul] at this
            exact this
          rw [if_neg hne, mul_zero]
        · intro hmn
          exact absurd (Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_rfl, hm0⟩, hmR⟩) hmn
      have hrw : ∀ t : ℝ,
          (∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ m.divisors.filter (fun d : ℕ => Real.log X ^ B ≤ (d : ℝ) ∧
              (d : ℝ) * Real.sqrt (windowY X ε) * Real.log X ^ B ≤ H),
              (∑ e ∈ (d.divisors.filter (fun e : ℕ => Squarefree e ∧
                    ∀ p : ℕ, p.Prime → p ∣ e → (p : ℝ) < z)).filter
                  (fun e : ℕ => D ≤ (e : ℝ) ∧ (e : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius e : ℤ) : ℂ)) *
                (if m / d = 1 then 1 else 0)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) =
          ∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ e ∈ (m.divisors.filter (fun e : ℕ => Squarefree e ∧
                  ∀ p : ℕ, p.Prime → p ∣ e → (p : ℝ) < z)).filter
                (fun e : ℕ => D ≤ (e : ℝ) ∧ (e : ℝ) < 2 * D),
              ((ArithmeticFunction.moebius e : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
        intro t
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [hinner m (Finset.mem_filter.mp hm).1]
      simp only [hrw]
      have hI : 0 ≤ ∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ e ∈ (m.divisors.filter (fun e : ℕ => Squarefree e ∧
                  ∀ p : ℕ, p.Prime → p ∣ e → (p : ℝ) < z)).filter
                (fun e : ℕ => D ≤ (e : ℝ) ∧ (e : ℝ) < 2 * D),
              ((ArithmeticFunction.moebius e : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 :=
        intervalIntegral.integral_nonneg (by linarith) fun t _ => by positivity
      nlinarith

/-- P0088 pages 11 and 12, proof of Lemma 3.4, display 42 in Case 3,
D ≥ V = y x^(-1/2) L^(-B), with x = Y / 2, y = H, M = 1 and a_1 = 1, written
y ≤ D x^(1/2) L^B; the paper factors d = p1 ... pr with the unique s such that
z^(-1) V ≤ p1 ... ps ≤ V ≤ p1 ... ps+1, removes the conditions p' < p,
pp' d1 d2 ∼ D and d1 p p' ≥ V by Lemma 3.3, and applies Lemma 3.2 with
v = p d1 in [L^B, V]. Uses z ≤ y x^(-1/2) L^(-2B). Here the range of v is cut
into dyadic blocks, each bounded by Lemma 3.2 with A + c + 2 in place of A.
CONDITIONAL ON leaf_case3_reduction_lemma33_core and leaf_lemma32_liu_zhan. -/
theorem case3_of_lemma33_lemma32 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ D : ℝ, 1 ≤ D → H ≤ D * Real.sqrt (windowY X ε) * Real.log X ^ B →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (m.divisors.filter (fun d : ℕ => Squarefree d ∧
                  ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨c0, hred⟩ := case3_reduction_lemma33
  obtain ⟨B2, hB2, h2⟩ := leaf_lemma32_liu_zhan c0 (A + c0 + 2) (by positivity)
  refine ⟨B2, hB2, fun B hB ε hε => ?_⟩
  have hBpos : 0 < B := hB2.trans_le hB
  obtain ⟨C', X1, hC', hX1, k⟩ := h2 B hB ε hε
  obtain ⟨X2, hX2, kred⟩ := hred B hBpos ε hε
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop ((c0 : ℝ) + A) (by norm_num : (0 : ℝ) < 7 / 9)).bound
      (by norm_num : (0 : ℝ) < 1))
  refine ⟨9 * C' + 1, max X1 (max X2 (max T 3)), by positivity,
    hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHX α q a hcop hqP hqQ hclose z hz2 hz D hD1 hD3
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hXT : T ≤ X :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hX
  have hX3 : 3 ≤ X :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hX
  have hX0 : 0 < X := by linarith
  have hX1' : 1 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    linarith [Real.exp_one_lt_d9]
  have hL : 0 < Real.log X := by linarith
  have hLB : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL B
  have hε1 := written_range_epsilon_le hX1' hH hHX
  have hY1 : 1 ≤ windowY X ε := by
    unfold windowY
    exact Real.one_le_rpow hX1'.le (by linarith)
  have hYX : windowY X ε ≤ X := by
    unfold windowY
    calc
      X ^ (7 / 12 + ε / 2) ≤ X ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hX1'.le (by linarith)
      _ = X := Real.rpow_one X
  have hsqY : Real.sqrt (windowY X ε) ≤ X := by
    have : Real.sqrt (windowY X ε) ≤ windowY X ε := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    linarith
  have hH1 : X ^ (7 / 18 : ℝ) ≤ H :=
    (Real.rpow_le_rpow_of_exponent_le hX1'.le (by linarith)).trans hH
  have hHpos : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hX0 _) hH1
  obtain ⟨J, hJ1, hJ2⟩ : ∃ J : ℕ, X < (2 : ℝ) ^ J ∧ (J : ℝ) ≤ 3 * Real.log X := by
    refine ⟨⌊Real.logb 2 X⌋₊ + 1, ?_, ?_⟩
    · have h1 : Real.logb 2 X < ((⌊Real.logb 2 X⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast
        exact Nat.lt_floor_add_one _
      have h2 := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) h1
      rwa [Real.rpow_logb (by norm_num) (by norm_num) (by linarith), Real.rpow_natCast] at h2
    · push_cast
      have hlb : 0 ≤ Real.logb 2 X := Real.logb_nonneg (by norm_num) hX1'.le
      have h1 : (⌊Real.logb 2 X⌋₊ : ℝ) ≤ Real.logb 2 X := Nat.floor_le hlb
      have h2 : Real.logb 2 X ≤ 2 * Real.log X := by
        rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
        nlinarith [Real.log_two_gt_d9]
      linarith
  obtain ⟨w, v, hw, hv, hb⟩ := kred X H hXb hH hHX α z hz2 hz D hD1 hD3
  set R : ℕ → Prop := fun d : ℕ => Real.log X ^ B ≤ (d : ℝ) ∧
    (d : ℝ) * Real.sqrt (windowY X ε) * Real.log X ^ B ≤ H with hR
  have hpart : ∀ m ∈ squareWindow (windowY X ε),
      (∑ d ∈ m.divisors.filter R, w d * v (m / d)) =
      ∑ j ∈ Finset.range J, ∑ d ∈ (m.divisors.filter R).filter
          (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j), w d * v (m / d) := by
    intro m hm
    obtain ⟨-, hm1, hm2⟩ := Finset.mem_filter.mp hm
    refine dyadic_partition _ J _ fun d hd => ?_
    obtain ⟨hdm', hdR⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdm, hm0⟩ := Nat.mem_divisors.mp hdm'
    have hdle : (d : ℝ) ≤ m := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdm
    have hlt : (d : ℝ) < (2 : ℝ) ^ J := by linarith
    refine ⟨fun h0 => ?_, by exact_mod_cast hlt⟩
    have := hdR.1
    rw [h0, Nat.cast_zero] at this
    linarith
  have hrw : ∀ t : ℝ,
      (∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        (∑ d ∈ m.divisors.filter R, w d * v (m / d)) *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) =
      ∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        (∑ j ∈ Finset.range J, ∑ d ∈ (m.divisors.filter R).filter
          (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j), w d * v (m / d)) *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
    intro t
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hpart m (Finset.mem_filter.mp hm).1]
  have hAc : Real.log X ^ (A + c0 + 2) =
      Real.log X ^ A * Real.log X ^ (c0 : ℝ) * Real.log X ^ 2 := by
    rw [Real.rpow_add hL, Real.rpow_add hL, Real.rpow_two]
  have hden : 0 < Real.log X ^ (A + c0 + 2) := Real.rpow_pos_of_pos hL _
  set K := C' * H ^ 2 / Real.log X ^ (A + c0 + 2) with hK
  have hK0 : 0 ≤ K := div_nonneg (by positivity) hden.le
  have hYh : windowY X ε / 2 ≤ windowY X ε := by linarith
  have hblocks := dyadic_mean_square_le (squareWindow (windowY X ε)) J
    (fun j m => ∑ d ∈ (m.divisors.filter R).filter
          (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j), w d * v (m / d))
    (fun m : ℕ => (fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) : ℂ))
    H _ _ K hYh (by
      intro j _
      set Dj := max ((2 : ℝ) ^ j) (Real.log X ^ B) with hDj
      by_cases hgood : Dj * Real.sqrt (windowY X ε) * Real.log X ^ B ≤ H
      · have hsame : ∀ m : ℕ, (∑ d ∈ (m.divisors.filter R).filter
            (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j), w d * v (m / d)) =
            ∑ d ∈ m.divisors.filter (fun d : ℕ => Dj ≤ (d : ℝ) ∧ (d : ℝ) < 2 * Dj),
              (if R d ∧ ((2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j) then w d else 0) *
                v (m / d) := by
          intro m
          rw [Finset.filter_filter, Finset.sum_filter, Finset.sum_filter]
          refine Finset.sum_congr rfl fun d _ => ?_
          by_cases hc : R d ∧ ((2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j)
          · have hin : Dj ≤ (d : ℝ) ∧ (d : ℝ) < 2 * Dj :=
              ⟨max_le hc.2.1 hc.1.1, lt_of_lt_of_le hc.2.2
                (by linarith [le_max_left ((2 : ℝ) ^ j) (Real.log X ^ B)])⟩
            simp only [hc, hin, and_self, ite_true]
          · simp only [hc, ite_false, zero_mul, ite_self]
        have e := k X H hXa hH hHX α q a hcop hqP hqQ hclose
          (fun d => if R d ∧ ((2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j) then w d else 0)
          v (fun d => by
            split_ifs
            · exact hw d
            · rw [norm_zero]
              positivity) hv Dj (le_max_right _ _) hgood
        simpa only [hsame] using e
      · have hempty : ∀ m : ℕ, (m.divisors.filter R).filter
            (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j) = ∅ := by
          intro m
          apply Finset.eq_empty_of_forall_notMem
          intro d hd
          obtain ⟨hd1, hd2⟩ := Finset.mem_filter.mp hd
          obtain ⟨-, hdR⟩ := Finset.mem_filter.mp hd1
          apply hgood
          have hDd : Dj ≤ (d : ℝ) := max_le hd2.1 hdR.1
          have hs : 0 ≤ Real.sqrt (windowY X ε) * Real.log X ^ B := by positivity
          calc
            Dj * Real.sqrt (windowY X ε) * Real.log X ^ B =
                Dj * (Real.sqrt (windowY X ε) * Real.log X ^ B) := by ring
            _ ≤ (d : ℝ) * (Real.sqrt (windowY X ε) * Real.log X ^ B) :=
                mul_le_mul_of_nonneg_right hDd hs
            _ = (d : ℝ) * Real.sqrt (windowY X ε) * Real.log X ^ B := by ring
            _ ≤ H := hdR.2
        simp only [hempty, Finset.sum_empty, zero_mul, Finset.sum_const_zero, norm_zero]
        simpa using hK0)
  simp only [← hrw] at hblocks
  have hlog : Real.log X ^ ((c0 : ℝ) + A) ≤ X ^ (7 / 9 : ℝ) := by
    have h0 := hT X hXT
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL _),
      abs_of_pos (Real.rpow_pos_of_pos hX0 (7 / 9 : ℝ)), one_mul] using h0
  have hH2 : X ^ (7 / 9 : ℝ) ≤ H ^ 2 := by
    have : X ^ (7 / 9 : ℝ) = (X ^ (7 / 18 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
      norm_num
    rw [this]
    exact pow_le_pow_left₀ (Real.rpow_pos_of_pos hX0 _).le hH1 2
  have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hL A
  have hLc : 0 < Real.log X ^ (c0 : ℝ) := Real.rpow_pos_of_pos hL _
  have hrem : Real.log X ^ (c0 : ℝ) ≤ H ^ 2 / Real.log X ^ A := by
    rw [le_div_iff₀ hLA, ← Real.rpow_add hL]
    linarith
  have hJsq : (J : ℝ) ^ 2 ≤ 9 * Real.log X ^ 2 := by
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    nlinarith
  have hmain : Real.log X ^ (c0 : ℝ) * ((J : ℝ) ^ 2 * K) ≤ 9 * C' * H ^ 2 / Real.log X ^ A := by
    calc
      Real.log X ^ (c0 : ℝ) * ((J : ℝ) ^ 2 * K) ≤
          Real.log X ^ (c0 : ℝ) * (9 * Real.log X ^ 2 * K) := by
        gcongr
      _ = 9 * C' * H ^ 2 / Real.log X ^ A := by
        rw [hK, hAc]
        field_simp
  calc
    _ ≤ _ := hb
    _ ≤ Real.log X ^ (c0 : ℝ) * ((J : ℝ) ^ 2 * K) + Real.log X ^ (c0 : ℝ) := by
        gcongr
    _ ≤ 9 * C' * H ^ 2 / Real.log X ^ A + H ^ 2 / Real.log X ^ A := add_le_add hmain hrem
    _ = (9 * C' + 1) * H ^ 2 / Real.log X ^ A := by ring

/-- P0088 page 11, the proof of Lemma 3.4 on the half window [Y / 2, Y] for
the rough cutoff 2 < z ≤ Y^(1/6 + eps/2): the Moebius expansion of the first
display, the dyadic blocks d ∼ D of display 42, at most 3 log X of them, and
the three cases. The statement is that of `leaf_large_cutoff_right_half`.
CONDITIONAL ON leaf_lemma31_liu_zhan, leaf_lemma32_liu_zhan and
leaf_case3_reduction_lemma33_core. -/
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
  obtain ⟨B1, hB1, h1⟩ := case1_of_lemma31 (A + 2) (by linarith)
  obtain ⟨B2, hB2, h2⟩ := case2_of_lemma32 (A + 2) (by linarith)
  obtain ⟨B3, hB3, h3⟩ := case3_of_lemma33_lemma32 (A + 2) (by linarith)
  refine ⟨max B1 (max B2 B3), lt_of_lt_of_le hB1 (le_max_left _ _), fun B hB ε hε => ?_⟩
  have hB1' : B1 ≤ B := (le_max_left _ _).trans hB
  have hB2' : B2 ≤ B := ((le_max_left _ _).trans (le_max_right _ _)).trans hB
  have hB3' : B3 ≤ B := ((le_max_right _ _).trans (le_max_right _ _)).trans hB
  have hBpos : 0 < B := hB1.trans_le hB1'
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B hB1' ε hε
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B hB2' ε hε
  obtain ⟨C3, X3, hC3, hX3, k3⟩ := h3 B hB3' ε hε
  set C' := max C1 (max C2 C3) with hC'
  have hC'pos : 0 < C' := lt_of_lt_of_le hC1 (le_max_left _ _)
  refine ⟨9 * C', max X1 (max X2 (max X3 3)), by positivity,
    hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHX α q a hcop hqP hqQ hclose z hz2 hz
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hXc : X3 ≤ X :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hX
  have hX3' : 3 ≤ X :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hX
  have hX1' : 1 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hL : 0 < Real.log X := by linarith
  have hε1 := written_range_epsilon_le hX1' hH hHX
  have hY1 : 1 ≤ windowY X ε := by
    unfold windowY
    exact Real.one_le_rpow hX1'.le (by linarith)
  have hYX : windowY X ε ≤ X := by
    unfold windowY
    calc
      X ^ (7 / 12 + ε / 2) ≤ X ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hX1'.le (by linarith)
      _ = X := Real.rpow_one X
  have hsqY : Real.sqrt (windowY X ε) ≤ X := by
    have : Real.sqrt (windowY X ε) ≤ windowY X ε := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    linarith
  obtain ⟨J, hJ1, hJ2⟩ : ∃ J : ℕ, X < (2 : ℝ) ^ J ∧ (J : ℝ) ≤ 3 * Real.log X := by
    refine ⟨⌊Real.logb 2 X⌋₊ + 1, ?_, ?_⟩
    · have h1 : Real.logb 2 X < ((⌊Real.logb 2 X⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast
        exact Nat.lt_floor_add_one _
      have h2 := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) h1
      rwa [Real.rpow_logb (by norm_num) (by norm_num) (by linarith), Real.rpow_natCast] at h2
    · push_cast
      have hlb : 0 ≤ Real.logb 2 X := Real.logb_nonneg (by norm_num) hX1'.le
      have h1 : (⌊Real.logb 2 X⌋₊ : ℝ) ≤ Real.logb 2 X := Nat.floor_le hlb
      have h2 : Real.logb 2 X ≤ 2 * Real.log X := by
        rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
        nlinarith [Real.log_two_gt_d9]
      linarith
  have hpart : ∀ m ∈ squareWindow (windowY X ε), roughWeight z m =
      ∑ j ∈ Finset.range J, ∑ d ∈ (m.divisors.filter (fun d : ℕ => Squarefree d ∧
          ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
          (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
    intro m hm
    obtain ⟨-, hm1, hm2⟩ := Finset.mem_filter.mp hm
    have hmpos : (0 : ℝ) < m :=
      lt_of_lt_of_le (by positivity : (0 : ℝ) < Real.sqrt (windowY X ε) / 2) hm1
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hmpos
    rw [roughWeight_eq_sum_moebius z m hm0]
    refine dyadic_partition _ J _ fun d hd => ?_
    obtain ⟨hdm, -⟩ := Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1
    have hdle : (d : ℝ) ≤ m := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdm
    have hlt : (d : ℝ) < (2 : ℝ) ^ J := by linarith
    exact ⟨fun h0 => hm0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hdm)), by exact_mod_cast hlt⟩
  have hrw : ∀ t : ℝ,
      (∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) =
      ∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        (∑ j ∈ Finset.range J, ∑ d ∈ (m.divisors.filter (fun d : ℕ => Squarefree d ∧
            ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
            (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
    intro t
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hpart m (Finset.mem_filter.mp hm).1]
  simp only [hrw]
  have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hL A
  have hpow : Real.log X ^ (A + 2) = Real.log X ^ A * Real.log X ^ 2 := by
    rw [Real.rpow_add hL, Real.rpow_two]
  have hden : 0 < Real.log X ^ (A + 2) := Real.rpow_pos_of_pos hL _
  have hq : 0 ≤ H ^ 2 / Real.log X ^ (A + 2) := div_nonneg (sq_nonneg H) hden.le
  have hCi : ∀ Ci : ℝ, Ci ≤ C' → Ci * H ^ 2 / Real.log X ^ (A + 2) ≤
      C' * H ^ 2 / Real.log X ^ (A + 2) := by
    intro Ci hCi
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hCi hq
  have hYh : windowY X ε / 2 ≤ windowY X ε := by linarith
  refine (dyadic_mean_square_le (squareWindow (windowY X ε)) J
    (fun j m => ∑ d ∈ (m.divisors.filter (fun d : ℕ => Squarefree d ∧
            ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
            (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ))
    (fun m : ℕ => (fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) : ℂ))
    H _ _ (C' * H ^ 2 / Real.log X ^ (A + 2)) hYh ?_).trans ?_
  · intro j _
    have hD1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    by_cases c1 : (2 : ℝ) ^ j ≤ Real.log X ^ B
    · exact (k1 X H hXa hH hHX α q a hcop hqP hqQ hclose z hz2 hz _ hD1 c1).trans
        (hCi C1 (le_max_left _ _))
    · by_cases c2 : (2 : ℝ) ^ j * Real.sqrt (windowY X ε) * Real.log X ^ B ≤ H
      · exact (k2 X H hXb hH hHX α q a hcop hqP hqQ hclose z hz2 hz _
          (le_of_lt (not_le.mp c1)) c2).trans
          (hCi C2 ((le_max_left _ _).trans (le_max_right _ _)))
      · exact (k3 X H hXc hH hHX α q a hcop hqP hqQ hclose z hz2 hz _ hD1
          (le_of_lt (not_le.mp c2))).trans
          (hCi C3 ((le_max_right _ _).trans (le_max_right _ _)))
  · rw [hpow]
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have hJsq : (J : ℝ) ^ 2 ≤ 9 * Real.log X ^ 2 := by nlinarith
    have hK : 0 ≤ C' * H ^ 2 / (Real.log X ^ A * Real.log X ^ 2) :=
      div_nonneg (by positivity) (mul_pos hLA (pow_pos hL 2)).le
    calc
      _ ≤ 9 * Real.log X ^ 2 * (C' * H ^ 2 / (Real.log X ^ A * Real.log X ^ 2)) :=
        mul_le_mul_of_nonneg_right hJsq hK
      _ = 9 * C' * H ^ 2 / Real.log X ^ A := by
        field_simp

end LeanLab.KumchevLiu2007.Eq33RouteD.LargeRight1122

#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.LargeRight1122.roughWeight_eq_sum_moebius
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.LargeRight1122.moebius_block_eq
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.LargeRight1122.moebius_coeff_norm_le
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.LargeRight1122.prefix_split
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.LargeRight1122.largest_primes_split
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.LargeRight1122.case1_of_lemma31
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.LargeRight1122.case2_of_lemma32
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.LargeRight1122.case3_reduction_lemma33
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.LargeRight1122.case3_of_lemma33_lemma32
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.LargeRight1122.large_cutoff_right_half_of_cases
