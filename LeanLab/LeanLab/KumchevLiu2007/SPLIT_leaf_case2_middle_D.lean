/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130. SPLIT of
`Eq33RouteD.SplitB.leaf_case2_middle_D`, ROUTE BURST S98 burst-20261122,
following Case 2 of the proof of Lemma 3.4 on page 11.

* `leaf_lemma32_window`: P0088 Lemma 3.2 of page 10 for a bilinear form with
  the first variable d in one dyadic block, in the window form of the parent
  with x = Y, y = H, c = 1. LEAF, HARD.
* `leaf_case2_convolution`: the rewriting of display 42 in Case 2 with the
  convolution b_u, the number of primes p of the block dividing u.
  Proved here.
* `leaf_case2_coeff_bound`: the bounds of the two coefficients by tau and the
  dyadic support of the d coefficient. Proved here.

The assembly has no sorry of its own. The parent QUESTION about H above Y
stays inside `leaf_lemma32_window`.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SPLIT_lemma34_second_sum_dyadic_b

namespace LeanLab.KumchevLiu2007.Eq33RouteD.SplitB

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-
Numerics for the Lemma 3.2 leaf. The d block is 2^j at most d below 2^(j+1)
with L^B below 2^j at most V = H Y^(-1/2) L^(-B); Lemma 3.2 asks
L^B at most M at most y x^(-1/2) L^(-B) for the block M = 2^j, met with B
replaced by B - 1 once L at least 2, since log Y is at most L = log X. At the
extremes: H = X^(7/18 + eps) gives V = X^(7/72 + 3 eps/4) L^(-B), a positive
power of X, so the range of j is nonempty for large X. Display 41 follows from
the hypotheses on q as in Case 1.
-/
/-- LEAF: P0088 Lemma 3.2 of page 10, with x = Y, y = H, c = 1, L = log X,
applied with B - 1 for B, the variable m of the paper being d in the dyadic
block 2^j at most d below 2^(j+1), L^B below 2^j at most H Y^(-1/2) L^(-B),
and the variable k being n/d. Class HARD. -/
theorem leaf_lemma32_window (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ j : ℕ, Real.log X ^ B < (2 : ℝ) ^ j →
        (2 : ℝ) ^ j ≤ H / (Real.sqrt (windowY X ε) * Real.log X ^ B) →
        ∀ c b : ℕ → ℂ, (∀ d : ℕ, ‖c d‖ ≤ (d.divisors.card : ℝ)) →
        (∀ d : ℕ, c d ≠ 0 → (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j) →
        (∀ k : ℕ, ‖b k‖ ≤ (k.divisors.card : ℝ)) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ m.divisors, c d * b (m / d)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- Proved. Case 2 of the proof of Lemma 3.4, P0088 page 11: for m positive the
double sum over p and over d dividing m/p equals the sum over d dividing m of
mu(d) times the number b_u of primes p of the block dividing u = m/d, which is
the convolution b_r of the paper with a_m the prime indicator. -/
theorem leaf_case2_convolution (Z W M : ℝ) (j m : ℕ) (hm : 0 < m) :
    (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
        Z ≤ (p : ℝ) ∧ (p : ℝ) < W ∧ p ∣ m)).filter
        (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
      ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
        (r : ℝ) < Z)).filter
        (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
    ∑ d ∈ m.divisors,
      (if (∀ r : ℕ, r.Prime → r ∣ d → (r : ℝ) < Z) ∧
          (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j
        then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0) *
      (((m / d).divisors.filter (fun p : ℕ => p.Prime ∧
        Z ≤ (p : ℝ) ∧ (p : ℝ) < W ∧ M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M)).card : ℂ) := by
  have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm
  simp_rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.mul_sum, mul_one]
  rw [Finset.sum_comm' (s := m.divisors) (t' := m.divisors.filter (fun p : ℕ => p.Prime ∧
        Z ≤ (p : ℝ) ∧ (p : ℝ) < W ∧ M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M))
      (s' := fun p => (m / p).divisors)]
  · have hset : ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
        Z ≤ (p : ℝ) ∧ (p : ℝ) < W ∧ p ∣ m)).filter
        (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M) =
        m.divisors.filter (fun p : ℕ => p.Prime ∧
        Z ≤ (p : ℝ) ∧ (p : ℝ) < W ∧ M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨_, h1, h2, h3, h4⟩, h5, h6⟩
        exact ⟨⟨h4, hm0⟩, h1, h2, h3, h5, h6⟩
      · rintro ⟨⟨h4, _⟩, h1, h2, h3, h5, h6⟩
        exact ⟨⟨Nat.lt_succ_of_le (Nat.le_of_dvd hm h4), h1, h2, h3, h4⟩, h5, h6⟩
    rw [hset]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.filter_filter, Finset.sum_filter]
  · intro d p
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdm, _⟩, ⟨hpd, hd0⟩, hP⟩
      have hpm : p ∣ m := hpd.trans (Nat.div_dvd_of_dvd hdm)
      refine ⟨⟨?_, (Nat.div_pos (Nat.le_of_dvd hm hpm) hP.1.pos).ne'⟩, ⟨hpm, hm0⟩, hP⟩
      rw [Nat.dvd_div_iff_mul_dvd hpm, mul_comm, ← Nat.dvd_div_iff_mul_dvd hdm]
      exact hpd
    · rintro ⟨⟨hdp, _⟩, ⟨hpm, _⟩, hP⟩
      have hdm : d ∣ m := hdp.trans (Nat.div_dvd_of_dvd hpm)
      refine ⟨⟨hdm, hm0⟩, ⟨?_, (Nat.div_pos (Nat.le_of_dvd hm hdm) (Nat.pos_of_dvd_of_pos hdm hm |> fun h => by
        rcases Nat.eq_zero_or_pos d with h0 | h0
        · subst h0; simp at hdm; omega
        · exact h0)).ne'⟩, hP⟩
      rw [Nat.dvd_div_iff_mul_dvd hdm, mul_comm, ← Nat.dvd_div_iff_mul_dvd hpm]
      exact hdp

/-- Proved. Case 2 of the proof of Lemma 3.4, P0088 page 11: the coefficient
mu(d) times the indicator of z1 smooth d in the block is bounded by tau(d)
and supported in the block, and the prime count b_u is at most tau(u). -/
theorem leaf_case2_coeff_bound (Z W M : ℝ) (j : ℕ) :
    (∀ d : ℕ, ‖(if (∀ r : ℕ, r.Prime → r ∣ d → (r : ℝ) < Z) ∧
          (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j
        then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0)‖ ≤ (d.divisors.card : ℝ)) ∧
    (∀ d : ℕ, (if (∀ r : ℕ, r.Prime → r ∣ d → (r : ℝ) < Z) ∧
          (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j
        then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0) ≠ 0 →
        (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j) ∧
    (∀ k : ℕ, ‖((k.divisors.filter (fun p : ℕ => p.Prime ∧
        Z ≤ (p : ℝ) ∧ (p : ℝ) < W ∧ M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M)).card : ℂ)‖ ≤
        (k.divisors.card : ℝ)) := by
  refine ⟨fun d => ?_, fun d hd => ?_, fun k => ?_⟩
  · split_ifs with h
    · have hd1 : (1 : ℝ) ≤ d := le_trans (one_le_pow₀ (by norm_num)) h.2.1
      have hd0 : d ≠ 0 := by
        rintro rfl
        norm_num at hd1
      have hc : 1 ≤ d.divisors.card :=
        Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hd0)
      rw [Complex.norm_intCast]
      have h1 : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have h2 : (1 : ℝ) ≤ d.divisors.card := by exact_mod_cast hc
      linarith
    · simp
  · by_contra hc
    exact hd (if_neg (fun h => hc h.2))
  · rw [Complex.norm_natCast]
    exact_mod_cast Finset.card_filter_le _ _

/-- Assembly. The exact statement of `leaf_case2_middle_D`, from the three
leaves above, with no sorry of its own. -/
theorem leaf_case2_middle_D_split (A : ℝ) (hA : 0 < A) :
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
  obtain ⟨B0, hB0, h⟩ := leaf_lemma32_window A hA
  refine ⟨B0, hB0, fun B hB ε hε => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h B hB ε hε
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X H hX hH hHX α q a hcop hqP hqQ hclose M hM j hj1 hj2
  have hY0 : 0 < windowY X ε := by
    unfold windowY
    exact Real.rpow_pos_of_pos (by linarith) _
  set Z : ℝ := windowY X ε ^ (1 / 6 + ε / 2) with hZ
  set W : ℝ := windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) with hWdef
  obtain ⟨hc1, hc2, hb⟩ := leaf_case2_coeff_bound Z W M j
  refine Eq.trans_le ?_ (k X H hX hH hHX α q a hcop hqP hqQ hclose j hj1 hj2
    (fun d : ℕ => if (∀ r : ℕ, r.Prime → r ∣ d → (r : ℝ) < Z) ∧
          (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j
        then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0)
    (fun k : ℕ => ((k.divisors.filter (fun p : ℕ => p.Prime ∧
        Z ≤ (p : ℝ) ∧ (p : ℝ) < W ∧ M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M)).card : ℂ))
    hc1 hc2 hb)
  congr 1
  funext t
  congr 2
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmw := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
  have hsq0 : 0 < Real.sqrt (windowY X ε) := Real.sqrt_pos.mpr hY0
  have hm0r : (0 : ℝ) < m := lt_of_lt_of_le (half_pos hsq0) hmw.1
  have hm0 : 0 < m := by exact_mod_cast hm0r
  rw [leaf_case2_convolution Z W M j m hm0]

/-- The split statement is character for character the parent leaf. -/
example : type_of% @leaf_case2_middle_D := leaf_case2_middle_D_split

end LeanLab.KumchevLiu2007.Eq33RouteD.SplitB
