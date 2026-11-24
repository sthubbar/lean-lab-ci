/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130. SPLIT of
`Eq33RouteD.SplitB.leaf_case1_small_D`, ROUTE BURST S98 burst-20261122,
following Case 1 of the proof of Lemma 3.4 on page 11.

* `leaf_lemma31_window`: P0088 Lemma 3.1 of page 9 for a type I coefficient
  b_r, here in the window form of the parent with x = Y, y = H, c = 1.
  LEAF, HARD.
* `leaf_case1_convolution`: the rewriting of display 42 in Case 1 through the
  convolution b_r of the prime indicator and mu(d). Proved here.
* `leaf_case1_conv_bound`: the bound |b_r| at most tau(r) and the support
  r below W 2^(j+1), W = Y^(1/4) L^(-2B). Proved here.

The assembly `leaf_case1_small_D_split` has no sorry of its own. The parent
QUESTION about H above Y stays inside `leaf_lemma31_window`, which keeps the
written range of H; for H at least Y the window condition m^2 at most t + H
is implied by m below the square root of Y, so the integrand equals the y = Y
integrand of Lemma 3.1.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SPLIT_lemma34_second_sum_dyadic_b

namespace LeanLab.KumchevLiu2007.Eq33RouteD.SplitB

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-
Numerics for the Lemma 3.1 leaf. Range: H at least X^(7/18 + eps) is at least
Y^(1/2) = X^(7/24 + eps/4), as Lemma 3.1 asks. Support: r below
2 Y^(1/4) L^(-B), at most Y^(1/4) (log Y)^(-(B - 1)) once L^(-1) at most 1/2,
and log Y at most L = log X, so Lemma 3.1 applies with B - 1 in place of B on
each of the at most 2L dyadic blocks R of r, and Cauchy over the blocks costs
L^2, absorbed by taking A + 2 in Lemma 3.1. Rational approximation: q at most
H L^(-B) and |q alpha - a| below L^B / H give |alpha - a/q| below q^(-2), and
L^B below q gives (log Y)^(B-1) at most q, which is display 41.
-/
/-- LEAF: P0088 Lemma 3.1 of page 9, with x = Y, y = H, c = 1, L = log X,
applied with B - 1 for B on each dyadic block of the coefficient b_r, the
blocks recombined by Cauchy. Here b_r is supported on 1 at most r below
2 Y^(1/4) L^(-B) and bounded by tau(r), and the inner sum over m with r
dividing m is the sum over m = rk of the paper. Class HARD. -/
theorem leaf_lemma31_window (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ b : ℕ → ℂ, (∀ r : ℕ, ‖b r‖ ≤ (r.divisors.card : ℝ)) →
        (∀ r : ℕ, b r ≠ 0 → 1 ≤ r ∧
          (r : ℝ) < 2 * windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-1 : ℤ)) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ r ∈ m.divisors, b r) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- Proved. Case 1 of the proof of Lemma 3.4, P0088 page 11: the double sum over
p and over d dividing m/p equals the sum over r dividing m of the convolution
b_r = sum over pd = r of the prime indicator times mu(d), for m positive.
Here Z plays z1 and W the upper cut of p. -/
theorem leaf_case1_convolution (Z W M : ℝ) (j m : ℕ) (hm : 0 < m) :
    (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
        Z ≤ (p : ℝ) ∧ (p : ℝ) < W ∧ p ∣ m)).filter
        (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
      ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
        (r : ℝ) < Z)).filter
        (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
    ∑ r ∈ m.divisors, ∑ p ∈ r.divisors.filter (fun p : ℕ => p.Prime ∧
        Z ≤ (p : ℝ) ∧ (p : ℝ) < W ∧ M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
      (if (∀ s : ℕ, s.Prime → s ∣ r / p → (s : ℝ) < Z) ∧
          (2 : ℝ) ^ j ≤ ((r / p : ℕ) : ℝ) ∧ ((r / p : ℕ) : ℝ) < 2 * 2 ^ j
        then ((ArithmeticFunction.moebius (r / p) : ℤ) : ℂ) else 0) := by
  have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm
  rw [Finset.sum_comm' (s := m.divisors) (t' := m.divisors.filter (fun p : ℕ => p.Prime ∧
        Z ≤ (p : ℝ) ∧ (p : ℝ) < W ∧ M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M))
      (s' := fun p => m.divisors.filter (fun r => p ∣ r))]
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
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.mem_filter.mp hp
    have hpm := (Nat.mem_divisors.mp hp'.1).1
    have hp0 : 0 < p := hp'.2.1.pos
    rw [Finset.filter_filter, Finset.sum_filter]
    symm
    refine Finset.sum_nbij' (fun r => r / p) (fun d => p * d) ?_ ?_ ?_ ?_ ?_
    · intro r hr
      simp only [Finset.mem_filter, Nat.mem_divisors] at hr ⊢
      exact ⟨Nat.div_dvd_div hr.2 hr.1.1, (Nat.div_pos (Nat.le_of_dvd hm hpm) hp0).ne'⟩
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      refine ⟨⟨?_, hm0⟩, dvd_mul_right p d⟩
      rw [← Nat.mul_div_cancel' hpm]
      exact Nat.mul_dvd_mul_left p hd.1
    · intro r hr
      simp only [Finset.mem_filter, Nat.mem_divisors] at hr
      exact Nat.mul_div_cancel' hr.2
    · intro d _
      exact Nat.mul_div_cancel_left d hp0
    · intro r _
      rfl
  · intro r p
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hrm, _⟩, ⟨hpr, hr0⟩, hP⟩
      exact ⟨⟨⟨hrm, hm0⟩, hpr⟩, ⟨hpr.trans hrm, hm0⟩, hP⟩
    · rintro ⟨⟨⟨hrm, _⟩, hpr⟩, _, hP⟩
      exact ⟨⟨hrm, hm0⟩, ⟨hpr, fun h => hm0 (Nat.eq_zero_of_zero_dvd (h ▸ hrm))⟩, hP⟩

/-- Proved. Case 1 of the proof of Lemma 3.4, P0088 page 11: the convolution
b_r has |b_r| at most tau(r), and b_r nonzero forces 1 at most r and
r = pd below W 2^(j+1), as p is below W and d below 2^(j+1). -/
theorem leaf_case1_conv_bound (Z W M : ℝ) (j r : ℕ) :
    ‖∑ p ∈ r.divisors.filter (fun p : ℕ => p.Prime ∧
        Z ≤ (p : ℝ) ∧ (p : ℝ) < W ∧ M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
      (if (∀ s : ℕ, s.Prime → s ∣ r / p → (s : ℝ) < Z) ∧
          (2 : ℝ) ^ j ≤ ((r / p : ℕ) : ℝ) ∧ ((r / p : ℕ) : ℝ) < 2 * 2 ^ j
        then ((ArithmeticFunction.moebius (r / p) : ℤ) : ℂ) else 0)‖ ≤
      (r.divisors.card : ℝ) ∧
    ((∑ p ∈ r.divisors.filter (fun p : ℕ => p.Prime ∧
        Z ≤ (p : ℝ) ∧ (p : ℝ) < W ∧ M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
      (if (∀ s : ℕ, s.Prime → s ∣ r / p → (s : ℝ) < Z) ∧
          (2 : ℝ) ^ j ≤ ((r / p : ℕ) : ℝ) ∧ ((r / p : ℕ) : ℝ) < 2 * 2 ^ j
        then ((ArithmeticFunction.moebius (r / p) : ℤ) : ℂ) else 0)) ≠ 0 →
      1 ≤ r ∧ (r : ℝ) < W * (2 * 2 ^ j)) := by
  constructor
  · refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ p ∈ r.divisors.filter (fun p : ℕ => p.Prime ∧
        Z ≤ (p : ℝ) ∧ (p : ℝ) < W ∧ M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
        ‖(if (∀ s : ℕ, s.Prime → s ∣ r / p → (s : ℝ) < Z) ∧
          (2 : ℝ) ^ j ≤ ((r / p : ℕ) : ℝ) ∧ ((r / p : ℕ) : ℝ) < 2 * 2 ^ j
        then ((ArithmeticFunction.moebius (r / p) : ℤ) : ℂ) else 0)‖ ≤ 1 := by
      intro p _
      split_ifs
      · rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      · simp
    refine (Finset.sum_le_sum hterm).trans ?_
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast Finset.card_filter_le _ _
  · intro hne
    obtain ⟨p, hp, hpne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hp' := Finset.mem_filter.mp hp
    have hpr := Nat.mem_divisors.mp hp'.1
    have hc : (∀ s : ℕ, s.Prime → s ∣ r / p → (s : ℝ) < Z) ∧
          (2 : ℝ) ^ j ≤ ((r / p : ℕ) : ℝ) ∧ ((r / p : ℕ) : ℝ) < 2 * 2 ^ j := by
      by_contra hc
      exact hpne (if_neg hc)
    have hr0 : 0 < r := Nat.pos_of_ne_zero hpr.2
    refine ⟨hr0, ?_⟩
    have hrr : r = p * (r / p) := (Nat.mul_div_cancel' hpr.1).symm
    have : (r : ℝ) = (p : ℝ) * ((r / p : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, ← hrr]
    rw [this]
    exact mul_lt_mul'' hp'.2.2.2.1 hc.2.2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Assembly. The exact statement of `leaf_case1_small_D`, from the three
leaves above, with no sorry of its own. -/
theorem leaf_case1_small_D_split (A : ℝ) (hA : 0 < A) :
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
  obtain ⟨B0, hB0, h⟩ := leaf_lemma31_window A hA
  refine ⟨B0, hB0, fun B hB ε hε => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h B hB ε hε
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X H hX hH hHX α q a hcop hqP hqQ hclose M hM j hj
  have hX1 : 1 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX1
  have hLB : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL B
  set Z : ℝ := windowY X ε ^ (1 / 6 + ε / 2) with hZ
  set W : ℝ := windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) with hWdef
  have hY0 : 0 < windowY X ε := by
    unfold windowY
    exact Real.rpow_pos_of_pos (by linarith) _
  have hW : W * (2 * 2 ^ j) ≤
      2 * windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-1 : ℤ) := by
    have hY4 : 0 < windowY X ε ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hY0 _
    rw [hWdef, zpow_neg, zpow_neg, zpow_ofNat, zpow_one]
    rw [show windowY X ε ^ (1 / 4 : ℝ) * ((Real.log X ^ B) ^ 2)⁻¹ * (2 * 2 ^ j)
        = 2 * windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B)⁻¹ * (2 ^ j / Real.log X ^ B) by
      field_simp]
    have h1 : (2 : ℝ) ^ j / Real.log X ^ B ≤ 1 := (div_le_one hLB).mpr hj
    have h2 : 0 ≤ 2 * windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B)⁻¹ := by positivity
    calc 2 * windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B)⁻¹ * (2 ^ j / Real.log X ^ B)
        ≤ 2 * windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = _ := mul_one _
  refine Eq.trans_le ?_ (k X H hX hH hHX α q a hcop hqP hqQ hclose
    (fun r : ℕ => ∑ p ∈ r.divisors.filter (fun p : ℕ => p.Prime ∧
        Z ≤ (p : ℝ) ∧ (p : ℝ) < W ∧ M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
      (if (∀ s : ℕ, s.Prime → s ∣ r / p → (s : ℝ) < Z) ∧
          (2 : ℝ) ^ j ≤ ((r / p : ℕ) : ℝ) ∧ ((r / p : ℕ) : ℝ) < 2 * 2 ^ j
        then ((ArithmeticFunction.moebius (r / p) : ℤ) : ℂ) else 0))
    (fun r => (leaf_case1_conv_bound Z W M j r).1)
    (fun r hr => by
      obtain ⟨h1, h2⟩ := (leaf_case1_conv_bound Z W M j r).2 hr
      exact ⟨h1, h2.trans_le hW⟩))
  congr 1
  funext t
  congr 2
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmw := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
  have hsq0 : 0 < Real.sqrt (windowY X ε) := Real.sqrt_pos.mpr hY0
  have hm0r : (0 : ℝ) < m := lt_of_lt_of_le (half_pos hsq0) hmw.1
  have hm0 : 0 < m := by exact_mod_cast hm0r
  rw [leaf_case1_convolution Z W M j m hm0]

/-- The split statement is character for character the parent leaf. -/
example : type_of% @leaf_case1_small_D := leaf_case1_small_D_split

end LeanLab.KumchevLiu2007.Eq33RouteD.SplitB
