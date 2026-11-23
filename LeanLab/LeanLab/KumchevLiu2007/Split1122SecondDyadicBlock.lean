/-
BURST 2026-11-22, unit P1122-0142. SPLIT of
Prep1121DKLRoughCut.second_dyadic_block along the printed proof of Lemma 3.4.
Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 11 Lemma 3.4 and its proof on
pages 11 and 12, applied on page 15 after display 52 with x = Y, y = H,
(m, k) = (p, m / p) and z = z1 = Y^(1/6 + eps/2).

The parent leaf is the mean square bound for one dyadic block M at most p below
2M of the primes p. This file proves it from three LEAF lemmas, one for each case
of the proof of Lemma 3.4, by the following PROVED steps.

* Large eps. For eps at least 1/6 the cutoff z0 = Y^(1/4) P^(-2) is at most
  z1, so no prime lies between them and the integral is zero.
  Eq33RouteD.interior_integral_le_of_large_eps.
* Empty blocks. For M at least z0, or 2M at most z1, the block holds no prime
  and the integral is zero.
* Page 11, first display of the proof. Phi(m / p, z1) is opened by the Moebius
  function over the divisors d of m / p dividing Pi(z1).
  Eq33RouteD.roughWeight_eq_moebius_sum.
* Page 11, the reduction to display 42. The divisors d are cut into at most
  3 log X dyadic blocks D at most d below 2D, and the mean square of the sum
  over blocks is at most the square of the number of blocks times the largest
  block, Eq33RouteD.dyadic_mean_square_le. The leaves are stated with A + 2 in
  place of A, as in the dyadic reduction of Eq33RouteD.lemma34_second_sum.
* Pages 11 and 12, the three cases on D. Case 1, D at most L^B. Case 2,
  L^B below D at most V. Case 3, D above V. Here L = log X and
  V = H Y^(-1/2) L^(-B), the V of Case 3. The split is exhaustive in D, so
  the bound for one block D follows from the three leaves.

The three leaves are display 42 of the paper for one block D, in the ranges of
the three cases, with the coefficient a_m of Lemma 3.4 the indicator of the
primes p of the block between z1 and z0. They keep every hypothesis of the
parent and add eps below 1/6, the interior conditions M below z0 and z1 below
2M, and the case condition on D. Each is a sub-claim of the parent on a
smaller parameter range, so none trivializes it. They rest on Lemmas 3.1, 3.2
and 3.3 of P0088, which the paper cites to Liu and Zhan 1997 and to Kumchev
2006 Lemma 2.7: a citation wall.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121DKLRoughCut
import LeanLab.KumchevLiu2007.InteriorHalvesAux
import LeanLab.KumchevLiu2007.Lemma34MoebiusOpen

namespace LeanLab.KumchevLiu2007.Split1122SecondDyadicBlock

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: HARD. P0088 page 11, Case 1 of the proof of Lemma 3.4: display 42 for
one dyadic block D at most d below 2D of the divisors d of m / p dividing
Pi(z1), with D at most L^B, L = log X. The convolution b_r of a_m and mu(d)
over d m = r has R = M D at most x^(1/4) L^(-B), and display 42 follows from
Lemma 3.1, cited to Liu and Zhan 1997. Applied with x = Y, y = H,
(m, k) = (p, m / p), z = z1 = Y^(1/6 + eps/2), a_p the indicator of the primes
of the block from z1 to below z0 = Y^(1/4) L^(-2B), in the block range of H. -/
theorem case1_small_D (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, 1 ≤ D → D ≤ Real.log X ^ B →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: HARD. P0088 page 11, Case 2 of the proof of Lemma 3.4: display 42 for
one dyadic block D at most d below 2D of the divisors d of m / p dividing
Pi(z1), with L^B below D at most V = y x^(-1/2) L^(-B), here
V = H / (Y^(1/2) L^B), L = log X. With b_r the sum of a_m over m k = r,
display 42 follows from Lemma 3.2, cited to Liu and Zhan 1997, with the
Moebius coefficient mu(d) on d dividing Pi(z1). Applied with x = Y, y = H,
(m, k) = (p, m / p), z = z1 = Y^(1/6 + eps/2), a_p the indicator of the primes
of the block from z1 to below z0 = Y^(1/4) L^(-2B), in the block range of H. -/
theorem case2_middle_D (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, Real.log X ^ B < D →
        D ≤ H / (Real.sqrt (windowY X ε) * Real.log X ^ B) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: HARD. P0088 page 12, Case 3 of the proof of Lemma 3.4: display 42 for
one dyadic block D at most d below 2D of the divisors d of m / p dividing
Pi(z1), with D above V = y x^(-1/2) L^(-B), here V = H / (Y^(1/2) L^B),
L = log X. Each d is cut at the index s of its prime factors where the prefix
product first reaches V, the conditions p' < p, p p' d1 d2 in the block D and
d1 p p' at least V are removed by Lemma 3.3, cited to Kumchev 2006 Lemma 2.7,
and display 42 follows from Lemma 3.2, cited to Liu and Zhan 1997, with the
variables u = m k p' d2 and v = p d1. Applied with x = Y, y = H,
(m, k) = (p, m / p), z = z1 = Y^(1/6 + eps/2), a_p the indicator of the primes
of the block from z1 to below z0 = Y^(1/4) L^(-2B), in the block range of H. -/
theorem case3_large_D (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, H / (Real.sqrt (windowY X ε) * Real.log X ^ B) < D →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- PROVED from the three case leaves. P0088 page 11, display 42 for one dyadic
block D at least one: the three cases of pages 11 and 12 cover every D. -/
theorem display42_block (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, 1 ≤ D →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := case1_small_D A hA
  obtain ⟨B2, hB2, h2⟩ := case2_middle_D A hA
  obtain ⟨B3, hB3, h3⟩ := case3_large_D A hA
  refine ⟨max B1 (max B2 B3), lt_max_of_lt_left hB1, fun B hB ε hε hε' => ?_⟩
  have hb1 : B1 ≤ B := (le_max_left _ _).trans hB
  have hb2 : B2 ≤ B := ((le_max_left _ _).trans (le_max_right _ _)).trans hB
  have hb3 : B3 ≤ B := ((le_max_right _ _).trans (le_max_right _ _)).trans hB
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B hb1 ε hε hε'
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B hb2 ε hε hε'
  obtain ⟨C3, X3, hC3, hX3, k3⟩ := h3 B hb3 ε hε hε'
  refine ⟨max C1 (max C2 C3), max X1 (max X2 X3), lt_max_of_lt_left hC1,
    hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose M hM htop hlow D hD
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hXc : X3 ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hq : 0 ≤ H ^ 2 / Real.log X ^ A := div_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos hL A).le
  have hkey : ∀ c : ℝ, c * H ^ 2 / Real.log X ^ A = c * (H ^ 2 / Real.log X ^ A) :=
    fun c => by ring
  by_cases hc1 : D ≤ Real.log X ^ B
  · have e := k1 X H hXa hlo hhi α q a hcop hqP hqQ hclose M hM htop hlow D hD hc1
    rw [hkey] at e ⊢
    exact e.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq)
  · push Not at hc1
    by_cases hc2 : D ≤ H / (Real.sqrt (windowY X ε) * Real.log X ^ B)
    · have e := k2 X H hXb hlo hhi α q a hcop hqP hqQ hclose M hM htop hlow D hc1 hc2
      rw [hkey] at e ⊢
      exact e.trans (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right _ _)) hq)
    · push Not at hc2
      have e := k3 X H hXc hlo hhi α q a hcop hqP hqQ hclose M hM htop hlow D hc2
      rw [hkey] at e ⊢
      exact e.trans (mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_max_right _ _)) hq)

/-- PROVED. P0088 page 11, the first display of the proof of Lemma 3.4 followed by
the cut of the divisors d into dyadic blocks: for m below 2^J, the coefficient of
the second sum of display 52 on one block of primes, the sum over p of
Phi(m / p, z1), is the sum over the J dyadic blocks 2^j at most d below 2^(j+1)
of the sum over p and over the divisors d of m / p dividing Pi(z1) of mu(d). -/
theorem block_coeff_eq_sum_dyadic (z1 z0 M : ℝ) (J m : ℕ) (hm : m < 2 ^ J) :
    (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
        z1 ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ m)).filter
        (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
      roughWeight z1 (m / p)) =
    ∑ j ∈ Finset.range J,
      ∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
        z1 ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ m)).filter
        (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
      ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
          (r : ℝ) < z1)).filter
          (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hp1, -⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpr, hpp, -, -, hpm⟩ := Finset.mem_filter.mp hp1
  have hpr' := Finset.mem_range.mp hpr
  have hp2 := hpp.two_le
  have hm0 : 0 < m := by omega
  have hk : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm0 hpm) hpp.pos
  rw [roughWeight_eq_moebius_sum z1 (m / p) hk]
  refine dyadic_partition _ J _ fun d hd => ?_
  have hd' := Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1
  refine ⟨(Nat.pos_of_dvd_of_pos hd'.1 hk).ne', ?_⟩
  exact lt_of_le_of_lt ((Nat.le_of_dvd hk hd'.1).trans (Nat.div_le_self _ _)) hm

/-- PROVED from display42_block. P0088 page 11, the reduction of Lemma 3.4 to
display 42, for one dyadic block of primes in the interior case: eps below 1/6,
M below z0 and z1 below 2M. The divisors d run over at most 3 log X dyadic
blocks, and the mean square over the sum of the blocks is at most the square
of their number times the largest, which costs two powers of log X. -/
theorem interior_core (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B2, hB2, h2⟩ := display42_block (A + 2) (by linarith)
  refine ⟨B2, hB2, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h2 B hB ε hε hε'
  refine ⟨9 * C, max X0 3, by positivity, hX0.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHX α q a hcop hqP hqQ hclose M hM htop hlow
  have hXa : X0 ≤ X := (le_max_left _ _).trans hX
  have hX3 : 3 ≤ X := (le_max_right _ _).trans hX
  have hX1 : 1 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hL : 0 < Real.log X := by linarith
  have hY0 : 0 < windowY X ε := by
    unfold windowY
    exact Real.rpow_pos_of_pos (by linarith) _
  have hYX : windowY X ε ≤ X := by
    unfold windowY
    calc X ^ (7 / 12 + ε / 2) ≤ X ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1.le (by linarith)
      _ = X := Real.rpow_one X
  obtain ⟨J, hJ1, hJ2⟩ : ∃ J : ℕ, X < (2 : ℝ) ^ J ∧ (J : ℝ) ≤ 3 * Real.log X := by
    refine ⟨⌊Real.logb 2 X⌋₊ + 1, ?_, ?_⟩
    · have h1 : Real.logb 2 X < ((⌊Real.logb 2 X⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast
        exact Nat.lt_floor_add_one _
      have h2 := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) h1
      rwa [Real.rpow_logb (by norm_num) (by norm_num) (by linarith), Real.rpow_natCast] at h2
    · push_cast
      have hlb : 0 ≤ Real.logb 2 X := Real.logb_nonneg (by norm_num) hX1.le
      have h1 : (⌊Real.logb 2 X⌋₊ : ℝ) ≤ Real.logb 2 X := Nat.floor_le hlb
      have h2 : Real.logb 2 X ≤ 2 * Real.log X := by
        rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
        nlinarith [Real.log_two_gt_d9]
      linarith
  have hmJ : ∀ m ∈ squareWindow (windowY X ε), m < 2 ^ J := by
    intro m hm
    have hm' := (Finset.mem_filter.mp hm).2.2
    have hs : Real.sqrt (windowY X ε) ≤ X := by
      calc Real.sqrt (windowY X ε) ≤ Real.sqrt X := Real.sqrt_le_sqrt hYX
        _ ≤ X := by
          rw [Real.sqrt_le_left (by linarith)]
          nlinarith
    have : (m : ℝ) < (2 : ℝ) ^ J := by linarith
    exact_mod_cast this
  have hfun : ∀ t : ℝ,
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
            windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
            (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
            p ∣ m)).filter
            (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
          roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 =
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        (∑ j ∈ Finset.range J,
          ∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
            windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
            (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
            p ∣ m)).filter
            (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
          ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
              (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
              (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
            ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 := by
    intro t
    congr 2
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [block_coeff_eq_sum_dyadic _ _ M J m (hmJ m (Finset.mem_filter.mp hm).1)]
  rw [intervalIntegral.integral_congr (fun t _ => hfun t)]
  refine (dyadic_mean_square_le (squareWindow (windowY X ε)) J
    (fun j m => ∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
            windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
            (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
            p ∣ m)).filter
            (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
          ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
              (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
              (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
            ((ArithmeticFunction.moebius d : ℤ) : ℂ))
    (fun m : ℕ => (fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) : ℂ))
    H _ _ (C * H ^ 2 / Real.log X ^ (A + 2)) (by linarith)
    (fun j _ => k X H hXa hH hHX α q a hcop hqP hqQ hclose M hM htop hlow ((2 : ℝ) ^ j)
      (one_le_pow₀ (by norm_num)))).trans ?_
  have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hL A
  have hpow : Real.log X ^ (A + 2) = Real.log X ^ A * Real.log X ^ 2 := by
    rw [Real.rpow_add hL, Real.rpow_two]
  rw [hpow]
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hJsq : (J : ℝ) ^ 2 ≤ 9 * Real.log X ^ 2 := by nlinarith
  have hK : 0 ≤ C * H ^ 2 / (Real.log X ^ A * Real.log X ^ 2) :=
    div_nonneg (by positivity) (mul_pos hLA (pow_pos hL 2)).le
  calc
    _ ≤ 9 * Real.log X ^ 2 * (C * H ^ 2 / (Real.log X ^ A * Real.log X ^ 2)) :=
      mul_le_mul_of_nonneg_right hJsq hK
    _ = 9 * C * H ^ 2 / Real.log X ^ A := by
      field_simp

/-- PROVED from interior_core. The exact statement of
Prep1121DKLRoughCut.second_dyadic_block. The range eps at least 1/6 and the
blocks M at least z0 or 2M at most z1 are empty; the rest is interior_core. -/
theorem second_dyadic_block_of_cases (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := interior_core A hA
  refine ⟨max B1 1, lt_of_lt_of_le hB1 (le_max_left _ _), fun B hB ε hε hε' => ?_⟩
  have hB0 : 0 ≤ B := le_trans zero_le_one ((le_max_right _ _).trans hB)
  by_cases hbig : 1 / 6 ≤ ε
  · refine ⟨1, 3, one_pos, by norm_num, ?_⟩
    intro X H hX _ _ α q a _ _ _ _ M _
    have he : Real.exp 1 ≤ X := by
      have := Real.exp_one_lt_d9
      linarith
    exact interior_integral_le_of_large_eps A ε B X H α M _ _ 1 he hB0 hbig zero_le_one
  · push Not at hbig
    obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hbig
    refine ⟨C1, X1, hC1, hX1, ?_⟩
    intro X H hX hHl hHu α q a hcop hqP hqQ hclose M hM
    have hL : 0 < Real.log X := Real.log_pos (by linarith)
    have hRHS : 0 ≤ C1 * H ^ 2 / Real.log X ^ A :=
      div_nonneg (mul_nonneg hC1.le (sq_nonneg _)) (Real.rpow_pos_of_pos hL A).le
    by_cases htop : M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)
    · by_cases hlow : windowY X ε ^ (1 / 6 + ε / 2) < 2 * M
      · exact k1 X H hX hHl hHu α q a hcop hqP hqQ hclose M hM htop hlow
      · push Not at hlow
        have h0 : ∀ m : ℕ, (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) = 0 := by
          intro m
          apply Finset.sum_eq_zero
          intro p hp
          obtain ⟨hp1, -, hp2M⟩ := Finset.mem_filter.mp hp
          obtain ⟨-, -, hpz1, -, -⟩ := Finset.mem_filter.mp hp1
          linarith
        simp only [h0, zero_mul, Finset.sum_const_zero, norm_zero]
        simpa using hRHS
    · push Not at htop
      have h0 : ∀ m : ℕ, (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
              windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
              (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
              p ∣ m)).filter
              (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
            roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) = 0 := by
        intro m
        apply Finset.sum_eq_zero
        intro p hp
        obtain ⟨hp1, hMp, -⟩ := Finset.mem_filter.mp hp
        obtain ⟨-, -, -, hpz0, -⟩ := Finset.mem_filter.mp hp1
        linarith
      simp only [h0, zero_mul, Finset.sum_const_zero, norm_zero]
      simpa using hRHS

example : type_of% @Prep1121DKLRoughCut.second_dyadic_block := second_dyadic_block_of_cases

end LeanLab.KumchevLiu2007.Split1122SecondDyadicBlock

#print axioms LeanLab.KumchevLiu2007.Split1122SecondDyadicBlock.block_coeff_eq_sum_dyadic
#print axioms LeanLab.KumchevLiu2007.Split1122SecondDyadicBlock.display42_block
#print axioms LeanLab.KumchevLiu2007.Split1122SecondDyadicBlock.interior_core
#print axioms LeanLab.KumchevLiu2007.Split1122SecondDyadicBlock.second_dyadic_block_of_cases
