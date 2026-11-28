/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 11 Lemma 3.4 and page 15, the paragraph
after display 52. burst-20261127 S3-30.

SPLIT of `Eq33RouteD.leaf_right_half_lemma34_instance` of
SPLIT_lemma34_second_sum_dyadic_interior_Leaves.lean. That leaf is Lemma 3.4 with x = Y / 2,
y = H, (m, k) = (p, m / p), on the range [x, 2 x] = [Y / 2, Y], except that its sum keeps the
summation condition m in the square window of Y, that is m^2 below Y, which can bind on
this half since t + H may pass Y. The split follows the leaf's own doc comment:

* LEAF unrestricted: Lemma 3.4 of page 11 itself, the same sum over every m with
  t < m^2 at most t + H. For t in [Y / 2, Y] and H at most Y / 2 these m are at most the
  square root of 2 Y, so the sum runs over a fixed initial range.
* LEAF edge: the same mean square for the part of that sum with m at least the square
  root of Y, the terms the window condition removes. This is the summation condition
  U at most m k below U' that Lemma 3.3 of page 10 removes.
* PROVED assembly: for t in [Y / 2, Y] every m with t < m^2 is at least half the square
  root of Y, so the window sum is the unrestricted sum minus the edge sum, and the square
  of a difference is at most twice the sum of the squares.

No new definition. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.InteriorHalvesAux

namespace LeanLab.KumchevLiu2007.Eq33RouteD.S3RightHalf

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a LeanLab.KumchevLiu2007.Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 11 Lemma 3.4, applied on page 15 to the second sum of display 52, with
x = Y / 2, y = H, (m, k) = (p, m / p), a_p the indicator of the primes of one dyadic block
p ~ M between z1 and z0, and z = w, on [x, 2 x] = [Y / 2, Y], with no summation condition
beyond t < m^2 at most t + H; for these t and H every such m is at most the square root of
2 Y, so the sum is over that initial range. Hypotheses those of Lemma 3.4 with
L = log x: x^(1/2) at most y at most x, display 41, M at most x^(1/4) L^(-2B) and
2 at most z at most y x^(-1/2) L^(-2B). Class HARD. -/
theorem leaf_right_half_lemma34_unrestricted (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ Y z1 z0 w H α : ℝ, ∀ q : ℕ, ∀ a : ℤ, ∀ M : ℝ,
        x0 ≤ Y / 2 → Real.sqrt (Y / 2) ≤ H → H ≤ Y / 2 →
        IsCoprime a (q : ℤ) → Real.log (Y / 2) ^ B ≤ (q : ℝ) →
        (q : ℝ) ≤ H / Real.log (Y / 2) ^ B →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        1 ≤ M → M ≤ (Y / 2) ^ (1 / 4 : ℝ) * (Real.log (Y / 2) ^ B) ^ (-2 : ℤ) →
        2 ≤ w → w ≤ H / Real.sqrt (Y / 2) * (Real.log (Y / 2) ^ B) ^ (-2 : ℤ) →
        (∫ t in (Y / 2)..(Y),
          ‖∑ m ∈ (Finset.range (⌊Real.sqrt (2 * Y)⌋₊ + 1)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                z1 ≤ (p : ℝ) ∧
                (p : ℝ) < z0 ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (w) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log (Y / 2) ^ A := by
  sorry

/-- LEAF: P0088 page 10 Lemma 3.3, the variant with the summation condition U at most m k
below U', as used in the proof of Lemma 3.4 on page 11, applied to the instance of the
previous leaf: the mean square over [Y / 2, Y] of the part of the short sum with m at least
the square root of Y, which is the part the square window of Y removes, has the same bound
y^2 L^(-A). For t at most Y - H this part is empty. Class HARD. -/
theorem leaf_right_half_lemma34_edge (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ Y z1 z0 w H α : ℝ, ∀ q : ℕ, ∀ a : ℤ, ∀ M : ℝ,
        x0 ≤ Y / 2 → Real.sqrt (Y / 2) ≤ H → H ≤ Y / 2 →
        IsCoprime a (q : ℤ) → Real.log (Y / 2) ^ B ≤ (q : ℝ) →
        (q : ℝ) ≤ H / Real.log (Y / 2) ^ B →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        1 ≤ M → M ≤ (Y / 2) ^ (1 / 4 : ℝ) * (Real.log (Y / 2) ^ B) ^ (-2 : ℤ) →
        2 ≤ w → w ≤ H / Real.sqrt (Y / 2) * (Real.log (Y / 2) ^ B) ^ (-2 : ℤ) →
        (∫ t in (Y / 2)..(Y),
          ‖∑ m ∈ ((Finset.range (⌊Real.sqrt (2 * Y)⌋₊ + 1)).filter (fun m : ℕ => Real.sqrt Y ≤ (m : ℝ))).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                z1 ≤ (p : ℝ) ∧
                (p : ℝ) < z0 ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (w) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log (Y / 2) ^ A := by
  sorry

/-- PROVED. For 0 < Y, 0 at most H at most Y / 2 and t in [Y / 2, Y], the short sum over
the square window of Y is the short sum over the range up to the square root of 2 Y minus
its part with m at least the square root of Y. -/
theorem window_sum_eq_sub (Y H t : ℝ) (c : ℕ → ℂ) (hY : 0 < Y) (hH0 : 0 ≤ H)
    (hH : H ≤ Y / 2) (ht1 : Y / 2 ≤ t) (ht2 : t ≤ Y) :
    ∑ m ∈ (squareWindow Y).filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m =
      ∑ m ∈ (Finset.range (⌊Real.sqrt (2 * Y)⌋₊ + 1)).filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m -
      ∑ m ∈ ((Finset.range (⌊Real.sqrt (2 * Y)⌋₊ + 1)).filter (fun m : ℕ => Real.sqrt Y ≤ (m : ℝ))).filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m := by
  have hsY := Real.sq_sqrt hY.le
  have hs0 := Real.sqrt_nonneg Y
  have hrange : ∀ m : ℕ, (m : ℝ) ^ 2 ≤ t + H → m ≤ ⌊Real.sqrt (2 * Y)⌋₊ := by
    intro m hm
    apply Nat.le_floor
    rw [← Real.sqrt_sq (Nat.cast_nonneg m)]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [eq_sub_iff_add_eq, add_comm,
    ← Finset.sum_filter_add_sum_filter_not
      ((Finset.range (⌊Real.sqrt (2 * Y)⌋₊ + 1)).filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H))
      (fun m : ℕ => Real.sqrt Y ≤ (m : ℝ))]
  congr 1
  · congr 1
    ext m
    simp only [Finset.mem_filter]
    tauto
  · congr 1
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, squareWindow, not_le]
    have key1 : t < (m : ℝ) ^ 2 → (m : ℝ) < Real.sqrt Y →
        m < ⌊Real.sqrt Y⌋₊ + 1 ∧ Real.sqrt Y / 2 ≤ (m : ℝ) := by
      intro h1 hlt
      refine ⟨?_, ?_⟩
      · have : m ≤ ⌊Real.sqrt Y⌋₊ := Nat.le_floor hlt.le
        omega
      · by_contra hcon
        push_neg at hcon
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith
    have key2 : (m : ℝ) ^ 2 ≤ t + H → m < ⌊Real.sqrt (2 * Y)⌋₊ + 1 := by
      intro h2
      have := hrange m h2
      omega
    constructor
    · intro h
      have := key2 h.2.2
      tauto
    · intro h
      have := key1 h.1.2.1 h.2
      have := key2 h.1.2.2
      tauto

/-- PROVED. The mean square over [Y / 2, Y] of the window short sum is at most twice the
mean square of the unrestricted short sum plus twice that of its edge part. -/
theorem window_mean_sq_le (Y H : ℝ) (c : ℕ → ℂ) (hY : 0 < Y) (hH0 : 0 ≤ H)
    (hH : H ≤ Y / 2) :
    (∫ t in (Y / 2)..(Y), ‖∑ m ∈ (squareWindow Y).filter
        (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2) ≤
      2 * (∫ t in (Y / 2)..(Y), ‖∑ m ∈ (Finset.range (⌊Real.sqrt (2 * Y)⌋₊ + 1)).filter
        (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2) +
      2 * (∫ t in (Y / 2)..(Y), ‖∑ m ∈ ((Finset.range (⌊Real.sqrt (2 * Y)⌋₊ + 1)).filter (fun m : ℕ => Real.sqrt Y ≤ (m : ℝ))).filter
        (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2) := by
  have i0 := short_sum_sq_intervalIntegrable (squareWindow Y) c H (Y / 2) Y
  have i1 := short_sum_sq_intervalIntegrable (Finset.range (⌊Real.sqrt (2 * Y)⌋₊ + 1)) c H (Y / 2) Y
  have i2 := short_sum_sq_intervalIntegrable ((Finset.range (⌊Real.sqrt (2 * Y)⌋₊ + 1)).filter (fun m : ℕ => Real.sqrt Y ≤ (m : ℝ))) c H (Y / 2) Y
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (i1.const_mul 2) (i2.const_mul 2)]
  refine intervalIntegral.integral_mono_on (by linarith) i0
    ((i1.const_mul 2).add (i2.const_mul 2)) ?_
  intro t ht
  rw [window_sum_eq_sub Y H t c hY hH0 hH ht.1 ht.2]
  set u := ∑ m ∈ (Finset.range (⌊Real.sqrt (2 * Y)⌋₊ + 1)).filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m
  set v := ∑ m ∈ ((Finset.range (⌊Real.sqrt (2 * Y)⌋₊ + 1)).filter (fun m : ℕ => Real.sqrt Y ≤ (m : ℝ))).filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m
  have h := norm_sub_le u v
  have hu := norm_nonneg u
  have hv := norm_nonneg v
  have h2 : ‖u - v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

/-- Assembly: the exact statement of `Eq33RouteD.leaf_right_half_lemma34_instance`, from
the unrestricted Lemma 3.4 leaf and the edge leaf, with constant 2 C1 + 2 C2. -/
theorem leaf_right_half_lemma34_instance_of_leaves (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ Y z1 z0 w H α : ℝ, ∀ q : ℕ, ∀ a : ℤ, ∀ M : ℝ,
        x0 ≤ Y / 2 → Real.sqrt (Y / 2) ≤ H → H ≤ Y / 2 →
        IsCoprime a (q : ℤ) → Real.log (Y / 2) ^ B ≤ (q : ℝ) →
        (q : ℝ) ≤ H / Real.log (Y / 2) ^ B →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        1 ≤ M → M ≤ (Y / 2) ^ (1 / 4 : ℝ) * (Real.log (Y / 2) ^ B) ^ (-2 : ℤ) →
        2 ≤ w → w ≤ H / Real.sqrt (Y / 2) * (Real.log (Y / 2) ^ B) ^ (-2 : ℤ) →
        (∫ t in (Y / 2)..(Y),
          ‖∑ m ∈ (squareWindow (Y)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                z1 ≤ (p : ℝ) ∧
                (p : ℝ) < z0 ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (w) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log (Y / 2) ^ A := by
  obtain ⟨B1, hB1, h1⟩ := leaf_right_half_lemma34_unrestricted A hA
  obtain ⟨B2, hB2, h2⟩ := leaf_right_half_lemma34_edge A hA
  refine ⟨max B1 B2, lt_of_lt_of_le hB1 (le_max_left _ _), fun B hB => ?_⟩
  obtain ⟨C1, x1, hC1, hx1, k1⟩ := h1 B ((le_max_left _ _).trans hB)
  obtain ⟨C2, x2, hC2, hx2, k2⟩ := h2 B ((le_max_right _ _).trans hB)
  refine ⟨2 * C1 + 2 * C2, max x1 x2, by linarith, hx1.trans (le_max_left _ _), ?_⟩
  intro Y z1 z0 w H α q a M hx hsq hHx hcop hq1 hq2 hq3 hM1 hM2 hw1 hw2
  have hxa : x1 ≤ Y / 2 := (le_max_left _ _).trans hx
  have hxb : x2 ≤ Y / 2 := (le_max_right _ _).trans hx
  have e1 := k1 Y z1 z0 w H α q a M hxa hsq hHx hcop hq1 hq2 hq3 hM1 hM2 hw1 hw2
  have e2 := k2 Y z1 z0 w H α q a M hxb hsq hHx hcop hq1 hq2 hq3 hM1 hM2 hw1 hw2
  have hY : 0 < Y := by linarith
  have hH0 : 0 ≤ H := (Real.sqrt_nonneg _).trans hsq
  refine (window_mean_sq_le Y H _ hY hH0 hHx).trans ?_
  have hk : (2 * C1 + 2 * C2) * H ^ 2 / Real.log (Y / 2) ^ A =
      2 * (C1 * H ^ 2 / Real.log (Y / 2) ^ A) + 2 * (C2 * H ^ 2 / Real.log (Y / 2) ^ A) := by
    ring
  rw [hk]
  linarith

end LeanLab.KumchevLiu2007.Eq33RouteD.S3RightHalf

#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.S3RightHalf.window_sum_eq_sub
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.S3RightHalf.window_mean_sq_le
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.S3RightHalf.leaf_right_half_lemma34_instance_of_leaves
