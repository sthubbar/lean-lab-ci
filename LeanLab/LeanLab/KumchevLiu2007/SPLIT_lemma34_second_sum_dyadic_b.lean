/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130. Second SPLIT of
`Eq33RouteD.lemma34_second_sum_dyadic`, ROUTE BURST S98 burst-20261122. The
first split, SPLIT_lemma34_second_sum_dyadic.lean, cuts on the position of the
block and the half of the t window. This one follows the proof of Lemma 3.4 on
pages 11 and 12 itself:

* `leaf_moebius_rough`, the first display of the proof of Lemma 3.4: the rough
  indicator Phi(k, z) of display 10 is the sum of mu(d) over the divisors d of
  k all of whose prime factors are below z. LEAF, MEDIUM.
* the d sum is cut into dyadic blocks D = 2^j, j below J, J at most 3 log X,
  with `Eq33RouteD.dyadic_partition`, and the Cauchy inequality over the blocks
  is `Eq33RouteD.dyadic_mean_square_le`. Proved here.
* display 42 for one block D, in the three cases of page 11: D at most L^B,
  `leaf_case1_small_D`; L^B < D at most V, `leaf_case2_middle_D`; D above V,
  `leaf_case3_large_D`, where V = H Y^(-1/2) L^(-B). LEAFs, HARD, each with
  A + 2 in place of A to absorb the J squared blocks.

The assembly `lemma34_second_sum_dyadic_split` has no sorry of its own. The
QUESTION of Eq33RouteD about H above Y stays inside the three case leaves,
which keep the whole written range of H.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Eq33RouteD

namespace LeanLab.KumchevLiu2007.Eq33RouteD.SplitB

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 11, the first display of the proof of Lemma 3.4, with
Phi(k, z) of page 4 display 10: for k positive, the rough indicator at z is the
sum of mu(d) over the divisors d of k whose prime factors are all below z,
that is over d dividing both k and Pi(z). Class MEDIUM. -/
theorem leaf_moebius_rough (z : ℝ) (k : ℕ) (hk : 0 < k) :
    roughWeight z k = ∑ d ∈ k.divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
      (r : ℝ) < z), ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
  sorry

/-- LEAF: Case 1 of the proof of Lemma 3.4, P0088 page 11, for the dyadic
block D = 2^j of the Moebius variable d of display 42 with D at most L^B. The
convolution b_r of a_m = the prime indicator and mu(d) has R = MD at most
x^(1/4) L^(-B), and display 42 follows from Lemma 3.1 of page 9. Here x = Y,
y = H, z = z1 = Y^(1/6 + eps/2), M is the dyadic block of the primes p of the
second sum of display 52 on page 15, k = m / (p d), L = log X. Class HARD. -/
theorem leaf_case1_small_D (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        ∀ j : ℕ, (2 : ℝ) ^ j ≤ Real.log X ^ B →
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
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: Case 2 of the proof of Lemma 3.4, P0088 page 11, for the dyadic
block D = 2^j of the Moebius variable d of display 42 with L^B < D at most
V = y x^(-1/2) L^(-B). The convolution b_r = sum over mk = r of a_m is a
divisor bounded coefficient, and display 42 follows from Lemma 3.2 of page 10.
Here x = Y, y = H, z = z1 = Y^(1/6 + eps/2), L = log X. Class HARD. -/
theorem leaf_case2_middle_D (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        ∀ j : ℕ, Real.log X ^ B < (2 : ℝ) ^ j → (2 : ℝ) ^ j ≤ H / (Real.sqrt (windowY X ε) * Real.log X ^ B) →
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
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: Case 3 of the proof of Lemma 3.4, P0088 pages 11 and 12, for the
dyadic block D = 2^j of the Moebius variable d of display 42 with D above
V = y x^(-1/2) L^(-B). The unique factorization d = d1 p p' d2 with
L^B at most d1 p < V at most d1 p p' gives a bilinear form, the summation
conditions are removed by Lemma 3.3 of page 10, and Lemma 3.2 finishes. This
uses z at most y x^(-1/2) L^(-2B), true for z1 in the range of page 16.
Here x = Y, y = H, z = z1 = Y^(1/6 + eps/2), L = log X. Class HARD. -/
theorem leaf_case3_large_D (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        ∀ j : ℕ, H / (Real.sqrt (windowY X ε) * Real.log X ^ B) < (2 : ℝ) ^ j →
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
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- Assembly. The exact statement of `Eq33RouteD.lemma34_second_sum_dyadic`,
from the four leaves above, with no sorry of its own. -/
theorem lemma34_second_sum_dyadic_split (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
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
  obtain ⟨B1, hB1, h1⟩ := leaf_case1_small_D (A + 2) (by linarith)
  obtain ⟨B2, hB2, h2⟩ := leaf_case2_middle_D (A + 2) (by linarith)
  obtain ⟨B3, hB3, h3⟩ := leaf_case3_large_D (A + 2) (by linarith)
  refine ⟨max B1 (max B2 B3), lt_max_of_lt_left hB1, fun B hB ε hε => ?_⟩
  have hBpos : 0 < B := (lt_max_of_lt_left hB1).trans_le hB
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε
  obtain ⟨C2, X2, hC2, hX2, k2⟩ :=
    h2 B (((le_max_left _ _).trans (le_max_right _ _)).trans hB) ε hε
  obtain ⟨C3, X3, hC3, hX3, k3⟩ :=
    h3 B (((le_max_right _ _).trans (le_max_right _ _)).trans hB) ε hε
  refine ⟨9 * (C1 + C2 + C3), max (max X1 X2) (max X3 3), by positivity,
    hX1.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro X H hX hH hHX α q a hcop hqP hqQ hclose M hM
  have hXa : X1 ≤ X := ((le_max_left _ _).trans (le_max_left _ _)).trans hX
  have hXb : X2 ≤ X := ((le_max_right _ _).trans (le_max_left _ _)).trans hX
  have hXc : X3 ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hX3' : 3 ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hX1' : 1 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hL : 0 < Real.log X := by linarith
  have hε1 := written_range_epsilon_le hX1' hH hHX
  have hY1 : 1 ≤ windowY X ε := by
    unfold windowY
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hY0 : 0 < windowY X ε := by linarith
  have hYX : windowY X ε ≤ X := by
    unfold windowY
    calc X ^ (7 / 12 + ε / 2) ≤ X ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1'.le (by linarith)
      _ = X := Real.rpow_one X
  have hsqY : Real.sqrt (windowY X ε) ≤ X := by
    have : Real.sqrt (windowY X ε) ≤ windowY X ε := by
      rw [Real.sqrt_le_iff]
      exact ⟨hY0.le, by nlinarith⟩
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
  have hW : ∀ m ∈ squareWindow (windowY X ε),
      (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
        roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) =
      ∑ j ∈ Finset.range J, (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) := by
    intro m hm
    have hmw := (Finset.mem_filter.mp hm).2
    have hsq0 : 0 < Real.sqrt (windowY X ε) := Real.sqrt_pos.mpr hY0
    have hm0r : (0 : ℝ) < m := lt_of_lt_of_le (half_pos hsq0) hmw.1
    have hm0 : 0 < m := by exact_mod_cast hm0r
    have hmJ : (m : ℝ) < (2 : ℝ) ^ J := by linarith [hmw.2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [Finset.mem_filter] at hp
    obtain ⟨⟨_, hpp, _, _, hpd⟩, _⟩ := hp
    have hk : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm0 hpd) hpp.pos
    rw [leaf_moebius_rough _ _ hk]
    refine dyadic_partition _ J _ fun d hd => ?_
    have hdm := Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1
    have hd0 : d ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1)
    have hdle : d ≤ m := (Nat.le_of_dvd hk hdm.1).trans (Nat.div_le_self m p)
    have hdr : (d : ℝ) ≤ m := by exact_mod_cast hdle
    exact ⟨hd0, by exact_mod_cast (show (d : ℝ) < 2 ^ J by linarith)⟩
  have hfun : (fun t : ℝ => ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) =
      (fun t : ℝ => ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ j ∈ Finset.range J, (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ))) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) := by
    funext t
    congr 2
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hW m (Finset.mem_filter.mp hm).1]
  rw [show (∫ t in windowY X ε / 4..windowY X ε, ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) =
      (∫ t in windowY X ε / 4..windowY X ε, ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ j ∈ Finset.range J, (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ))) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) from
    congrArg (fun F => ∫ t in windowY X ε / 4..windowY X ε, F t) hfun]
  have hLA2 : 0 < Real.log X ^ (A + 2) := Real.rpow_pos_of_pos hL _
  have hH2 : 0 ≤ H ^ 2 := sq_nonneg H
  have hup : ∀ Ci : ℝ, Ci ≤ C1 + C2 + C3 →
      Ci * H ^ 2 / Real.log X ^ (A + 2) ≤ (C1 + C2 + C3) * H ^ 2 / Real.log X ^ (A + 2) :=
    fun Ci hCi => div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCi hH2) hLA2.le
  refine (dyadic_mean_square_le (squareWindow (windowY X ε)) J
    (fun j m => (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)))
    (fun m : ℕ => (fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) : ℂ))
    H _ _ ((C1 + C2 + C3) * H ^ 2 / Real.log X ^ (A + 2)) (by linarith)
    (fun j _ => ?_)).trans ?_
  · by_cases hc1 : (2 : ℝ) ^ j ≤ Real.log X ^ B
    · exact (k1 X H hXa hH hHX α q a hcop hqP hqQ hclose M hM j hc1).trans
        (hup C1 (by linarith))
    · by_cases hc2 : (2 : ℝ) ^ j ≤ H / (Real.sqrt (windowY X ε) * Real.log X ^ B)
      · exact (k2 X H hXb hH hHX α q a hcop hqP hqQ hclose M hM j (not_le.mp hc1) hc2).trans
          (hup C2 (by linarith))
      · exact (k3 X H hXc hH hHX α q a hcop hqP hqQ hclose M hM j (not_le.mp hc2)).trans
          (hup C3 (by linarith))
  · have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hL A
    have hpow : Real.log X ^ (A + 2) = Real.log X ^ A * Real.log X ^ 2 := by
      rw [Real.rpow_add hL, Real.rpow_two]
    rw [hpow]
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have hJsq : (J : ℝ) ^ 2 ≤ 9 * Real.log X ^ 2 := by nlinarith
    have hK : 0 ≤ (C1 + C2 + C3) * H ^ 2 / (Real.log X ^ A * Real.log X ^ 2) :=
      div_nonneg (by positivity) (mul_pos hLA (pow_pos hL 2)).le
    calc (J : ℝ) ^ 2 * ((C1 + C2 + C3) * H ^ 2 / (Real.log X ^ A * Real.log X ^ 2))
        ≤ 9 * Real.log X ^ 2 * ((C1 + C2 + C3) * H ^ 2 / (Real.log X ^ A * Real.log X ^ 2)) :=
          mul_le_mul_of_nonneg_right hJsq hK
      _ = 9 * (C1 + C2 + C3) * H ^ 2 / Real.log X ^ A := by
          field_simp

/-- The split statement is character for character the sealed leaf. -/
example : type_of% @lemma34_second_sum_dyadic := lemma34_second_sum_dyadic_split

end LeanLab.KumchevLiu2007.Eq33RouteD.SplitB
