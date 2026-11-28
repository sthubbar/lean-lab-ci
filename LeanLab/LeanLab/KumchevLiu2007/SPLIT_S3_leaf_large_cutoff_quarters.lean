/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 11 Lemma 3.4 as applied on page 15,
burst-20261127 S3-28 and S3-29.

SPLIT of the two open leaves `leaf_lower_quarter_large_cutoff` and
`leaf_upper_quarter_large_cutoff` of SPLIT_leaf_large_cutoff_left_half.lean. There the cut
point `windowY X ε ^ (1 / 6)` is a natural number power with exponent 1 / 6 = 0, so it is
one and each leaf covers every cut-off 2 < z at most Y^(1/6 + eps/2). The twin files
SPLIT_leaf_large_cutoff_left_half_twin.lean and the quarter part files cut the same
estimates at the real sixth root, but they import the target file and so cannot close it.
This file imports only what the target imports and states, per quarter, three leaves:
the small cut-off case below the real sixth root, and above it the prime part and the
composite part of the rough weight, where a z rough integer below the square root of Y
is a prime or a product of two primes at least z. Each leaf restricts the cut-off range
or the coefficient set of the target. The assemblies have the exact target statements.
No new definition. The leaves have the same statements as the twin leaves of
SixthTwin1122 and SixthTwin1122.QuarterParts, under new names.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SPLIT_lemma34_first_sum

namespace LeanLab.KumchevLiu2007.Eq33RouteD.S3Quarters

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a LeanLab.KumchevLiu2007.Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- PROVED. The mean square of a short sum of two coefficient families is at most twice
the sum of the two mean squares, on any interval taken left to right. -/
theorem short_sum_sq_integral_add_le_S3 (S : Finset ℕ) (f g : ℕ → ℂ) (H a b : ℝ)
    (hab : a ≤ b) :
    (∫ t in a..b, ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        (f m + g m)‖ ^ 2) ≤
      2 * (∫ t in a..b, ‖∑ m ∈ S.filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), f m‖ ^ 2) +
      2 * (∫ t in a..b, ‖∑ m ∈ S.filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), g m‖ ^ 2) := by
  have i1 := short_sum_sq_intervalIntegrable S f H a b
  have i2 := short_sum_sq_intervalIntegrable S g H a b
  have i0 := short_sum_sq_intervalIntegrable S (fun m => f m + g m) H a b
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (i1.const_mul 2) (i2.const_mul 2)]
  refine intervalIntegral.integral_mono_on hab i0 ((i1.const_mul 2).add (i2.const_mul 2)) ?_
  intro t _
  rw [Finset.sum_add_distrib]
  set u := ∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), f m
  set v := ∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), g m
  have h := norm_add_le u v
  have hu := norm_nonneg u
  have hv := norm_nonneg v
  have h2 : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

/-- LEAF: P0088 page 11 Lemma 3.4 as applied on page 15 with (m, k) = (1, m) and
x = Y / 4, class HARD. The cut-off z at most the real sixth root of the window Y, on
the lower quarter [Y / 4, 3Y / 8] of the left half. Every size of rough integer may survive the
weight; the cut-off range and the interval are strictly smaller than the target's. -/
theorem leaf_lower_quarter_small_cutoff_real_S3 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ ((1 : ℝ) / 6) →
        (∫ t in (windowY X ε / 4)..(3 * windowY X ε / 8),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: P0088 page 11 Lemma 3.4 as applied on page 15, class HARD, the prime part of
the large cut-off lower quarter [Y / 4, 3Y / 8]: the z rough integers of the square root window that
are prime, so the primes at least z, for z between the real sixth root of Y and
Y^(1/6 + eps/2). The prime short sum is a type II sum by Vaughan's identity. -/
theorem leaf_lower_quarter_large_cutoff_prime_part_S3 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → windowY X ε ^ ((1 : ℝ) / 6) < z →
        z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (windowY X ε / 4)..(3 * windowY X ε / 8),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (if m.Prime then roughWeight z m else 0) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: P0088 page 11 Lemma 3.4 as applied on page 15, class HARD, the composite part
of the large cut-off lower quarter [Y / 4, 3Y / 8]: the z rough integers of the square root window that
are not prime. Since z exceeds the real sixth root of Y these are the products of two
primes at least z, a bilinear form handled by Lemma 3.2 of page 10. -/
theorem leaf_lower_quarter_large_cutoff_two_prime_part_S3 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → windowY X ε ^ ((1 : ℝ) / 6) < z →
        z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (windowY X ε / 4)..(3 * windowY X ε / 8),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (if m.Prime then 0 else roughWeight z m) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- PROVED from the two part leaves: the large cut-off estimate on the lower quarter [Y / 4, 3Y / 8],
cut-off between the real sixth root of Y and Y^(1/6 + eps/2). The rough weight is its
prime part plus its composite part and the square of a sum is at most twice the sum of
squares. -/
theorem lower_quarter_large_cutoff_real_S3 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → windowY X ε ^ ((1 : ℝ) / 6) < z →
        z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (windowY X ε / 4)..(3 * windowY X ε / 8),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := leaf_lower_quarter_large_cutoff_prime_part_S3 A hA
  obtain ⟨B2, hB2, h2⟩ := leaf_lower_quarter_large_cutoff_two_prime_part_S3 A hA
  refine ⟨max B1 B2, lt_of_lt_of_le hB1 (le_max_left _ _), fun B hB ε hε => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε
  refine ⟨2 * C1 + 2 * C2, max X1 X2, by linarith, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHU α q a hcop hqP hqQ hclose z hz hz6 hzY
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := (le_max_right _ _).trans hX
  have e1 := k1 X H hXa hH hHU α q a hcop hqP hqQ hclose z hz hz6 hzY
  have e2 := k2 X H hXb hH hHU α q a hcop hqP hqQ hclose z hz hz6 hzY
  have hY : 0 ≤ windowY X ε := by
    unfold windowY; exact Real.rpow_nonneg (by linarith) _
  have hsplit : ∀ m : ℕ, roughWeight z m *
      fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) =
      (if m.Prime then roughWeight z m else 0) *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) +
      (if m.Prime then 0 else roughWeight z m) *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
    intro m; split_ifs <;> ring
  simp_rw [hsplit]
  refine (short_sum_sq_integral_add_le_S3 _ _ _ H _ _ (by linarith)).trans ?_
  have hk : (2 * C1 + 2 * C2) * H ^ 2 / Real.log X ^ A =
      2 * (C1 * H ^ 2 / Real.log X ^ A) + 2 * (C2 * H ^ 2 / Real.log X ^ A) := by ring
  rw [hk]
  linarith

/-- Assembly: the exact statement of `Eq33RouteD.leaf_lower_quarter_large_cutoff` of
SPLIT_leaf_large_cutoff_left_half.lean, whose natural number cut point
`windowY X ε ^ (1 / 6)` equals one, so it covers every cut-off 2 < z at most
Y^(1/6 + eps/2). Below the real sixth root use the small cut-off leaf, above it the
large cut-off estimate, with the larger constant and threshold. -/
theorem leaf_lower_quarter_large_cutoff_of_leaves_S3 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → windowY X ε ^ (1 / 6) < z →
        z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (windowY X ε / 4)..(3 * windowY X ε / 8),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := leaf_lower_quarter_small_cutoff_real_S3 A hA
  obtain ⟨B2, hB2, h2⟩ := lower_quarter_large_cutoff_real_S3 A hA
  refine ⟨max B1 B2, lt_of_lt_of_le hB1 (le_max_left _ _), fun B hB ε hε => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε
  refine ⟨max C1 C2, max X1 X2, lt_of_lt_of_le hC1 (le_max_left _ _),
    hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHU α q a hcop hqP hqQ hclose z hz _ hzY
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith [hX1.trans hXa])
  have hq : (0 : ℝ) ≤ H ^ 2 / Real.log X ^ A :=
    div_nonneg (by positivity) (Real.rpow_pos_of_pos hL A).le
  have hk : ∀ C : ℝ, C * H ^ 2 / Real.log X ^ A = C * (H ^ 2 / Real.log X ^ A) :=
    fun C => by ring
  rw [hk]
  by_cases hzc : z ≤ windowY X ε ^ ((1 : ℝ) / 6)
  · have e := k1 X H hXa hH hHU α q a hcop hqP hqQ hclose z hz hzc
    rw [hk] at e
    exact e.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq)
  · have e := k2 X H hXb hH hHU α q a hcop hqP hqQ hclose z hz (not_le.mp hzc) hzY
    rw [hk] at e
    exact e.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hq)

/-- LEAF: P0088 page 11 Lemma 3.4 as applied on page 15 with (m, k) = (1, m) and
x = Y / 4, class HARD. The cut-off z at most the real sixth root of the window Y, on
the upper quarter [3Y / 8, Y / 2] of the left half. Every size of rough integer may survive the
weight; the cut-off range and the interval are strictly smaller than the target's. -/
theorem leaf_upper_quarter_small_cutoff_real_S3 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ ((1 : ℝ) / 6) →
        (∫ t in (3 * windowY X ε / 8)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: P0088 page 11 Lemma 3.4 as applied on page 15, class HARD, the prime part of
the large cut-off upper quarter [3Y / 8, Y / 2]: the z rough integers of the square root window that
are prime, so the primes at least z, for z between the real sixth root of Y and
Y^(1/6 + eps/2). The prime short sum is a type II sum by Vaughan's identity. -/
theorem leaf_upper_quarter_large_cutoff_prime_part_S3 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → windowY X ε ^ ((1 : ℝ) / 6) < z →
        z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (3 * windowY X ε / 8)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (if m.Prime then roughWeight z m else 0) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: P0088 page 11 Lemma 3.4 as applied on page 15, class HARD, the composite part
of the large cut-off upper quarter [3Y / 8, Y / 2]: the z rough integers of the square root window that
are not prime. Since z exceeds the real sixth root of Y these are the products of two
primes at least z, a bilinear form handled by Lemma 3.2 of page 10. -/
theorem leaf_upper_quarter_large_cutoff_two_prime_part_S3 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → windowY X ε ^ ((1 : ℝ) / 6) < z →
        z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (3 * windowY X ε / 8)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (if m.Prime then 0 else roughWeight z m) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- PROVED from the two part leaves: the large cut-off estimate on the upper quarter [3Y / 8, Y / 2],
cut-off between the real sixth root of Y and Y^(1/6 + eps/2). The rough weight is its
prime part plus its composite part and the square of a sum is at most twice the sum of
squares. -/
theorem upper_quarter_large_cutoff_real_S3 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → windowY X ε ^ ((1 : ℝ) / 6) < z →
        z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (3 * windowY X ε / 8)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := leaf_upper_quarter_large_cutoff_prime_part_S3 A hA
  obtain ⟨B2, hB2, h2⟩ := leaf_upper_quarter_large_cutoff_two_prime_part_S3 A hA
  refine ⟨max B1 B2, lt_of_lt_of_le hB1 (le_max_left _ _), fun B hB ε hε => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε
  refine ⟨2 * C1 + 2 * C2, max X1 X2, by linarith, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHU α q a hcop hqP hqQ hclose z hz hz6 hzY
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := (le_max_right _ _).trans hX
  have e1 := k1 X H hXa hH hHU α q a hcop hqP hqQ hclose z hz hz6 hzY
  have e2 := k2 X H hXb hH hHU α q a hcop hqP hqQ hclose z hz hz6 hzY
  have hY : 0 ≤ windowY X ε := by
    unfold windowY; exact Real.rpow_nonneg (by linarith) _
  have hsplit : ∀ m : ℕ, roughWeight z m *
      fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) =
      (if m.Prime then roughWeight z m else 0) *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) +
      (if m.Prime then 0 else roughWeight z m) *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
    intro m; split_ifs <;> ring
  simp_rw [hsplit]
  refine (short_sum_sq_integral_add_le_S3 _ _ _ H _ _ (by linarith)).trans ?_
  have hk : (2 * C1 + 2 * C2) * H ^ 2 / Real.log X ^ A =
      2 * (C1 * H ^ 2 / Real.log X ^ A) + 2 * (C2 * H ^ 2 / Real.log X ^ A) := by ring
  rw [hk]
  linarith

/-- Assembly: the exact statement of `Eq33RouteD.leaf_upper_quarter_large_cutoff` of
SPLIT_leaf_large_cutoff_left_half.lean, whose natural number cut point
`windowY X ε ^ (1 / 6)` equals one, so it covers every cut-off 2 < z at most
Y^(1/6 + eps/2). Below the real sixth root use the small cut-off leaf, above it the
large cut-off estimate, with the larger constant and threshold. -/
theorem leaf_upper_quarter_large_cutoff_of_leaves_S3 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → windowY X ε ^ (1 / 6) < z →
        z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (3 * windowY X ε / 8)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := leaf_upper_quarter_small_cutoff_real_S3 A hA
  obtain ⟨B2, hB2, h2⟩ := upper_quarter_large_cutoff_real_S3 A hA
  refine ⟨max B1 B2, lt_of_lt_of_le hB1 (le_max_left _ _), fun B hB ε hε => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε
  refine ⟨max C1 C2, max X1 X2, lt_of_lt_of_le hC1 (le_max_left _ _),
    hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHU α q a hcop hqP hqQ hclose z hz _ hzY
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith [hX1.trans hXa])
  have hq : (0 : ℝ) ≤ H ^ 2 / Real.log X ^ A :=
    div_nonneg (by positivity) (Real.rpow_pos_of_pos hL A).le
  have hk : ∀ C : ℝ, C * H ^ 2 / Real.log X ^ A = C * (H ^ 2 / Real.log X ^ A) :=
    fun C => by ring
  rw [hk]
  by_cases hzc : z ≤ windowY X ε ^ ((1 : ℝ) / 6)
  · have e := k1 X H hXa hH hHU α q a hcop hqP hqQ hclose z hz hzc
    rw [hk] at e
    exact e.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq)
  · have e := k2 X H hXb hH hHU α q a hcop hqP hqQ hclose z hz (not_le.mp hzc) hzY
    rw [hk] at e
    exact e.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hq)

end LeanLab.KumchevLiu2007.Eq33RouteD.S3Quarters

#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.S3Quarters.short_sum_sq_integral_add_le_S3
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.S3Quarters.lower_quarter_large_cutoff_real_S3
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.S3Quarters.upper_quarter_large_cutoff_real_S3
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.S3Quarters.leaf_lower_quarter_large_cutoff_of_leaves_S3
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.S3Quarters.leaf_upper_quarter_large_cutoff_of_leaves_S3
