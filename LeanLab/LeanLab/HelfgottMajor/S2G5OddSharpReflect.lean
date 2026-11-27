import LeanLab.HelfgottMajor.S2G5OddSharpPeriod

/-!
Reflection split of the one period odd leaves of `HelfgottMajor/S2G5OddSharpPeriod.lean`,
burst-20261124 agent S2G5.

For an odd character, `χ(-1) = -1`, the partial sums satisfy `S(n) = S(q - 1 - n)` for
`n < q`: the sum over `1 <= m <= q - 1` vanishes, and `m ↦ q - m` turns the tail
`n < m <= q - 1` into minus the head `1 <= m <= q - 1 - n`. This is the symmetry of the odd
sawtooth kernel used in the explicit Polya-Vinogradov argument of P0014's input. It halves
the range of `n`: the two one period leaves are restated for `2 n < q`, and the finite
computation of the small leaf drops to `n <= (q - 1) / 2`.
-/

namespace LeanLab.HelfgottMajor.PolyaVinogradov123
open Real Finset

/-- Partial sums over `Icc 1 N` written over `range N`. -/
theorem s2g5_partial_sum_range {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, χ (m : ZMod q) = ∑ k ∈ range N, χ ((1 + k : ℕ) : ZMod q) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ, Nat.add_comm 1 N]

/-- An odd character has `χ(-1) = -1`. -/
theorem s2g5_neg_one_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (h_odd : χ (-1) ≠ 1) :
    χ (-1) = -1 := by
  have h2 : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; simp
  have : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) h_odd
  · linear_combination h

/-- The odd reflection `S(n) = S(q - 1 - n)` for `n < q`. -/
theorem s2g5_partial_sum_reflect {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (h_odd : χ (-1) ≠ 1)
    (hq : 2 ≤ q) (n : ℕ) (hn : n < q) :
    ∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q) = ∑ m ∈ Finset.Icc 1 (q - 1 - n), χ (m : ZMod q) := by
  have hfull : ∑ a : ZMod q, χ a = 0 := MulChar.sum_eq_zero_of_ne_one (s2g5_ne_one_of_odd χ h_odd)
  have hz : χ (0 : ZMod q) = 0 := by
    have : ¬ IsUnit (0 : ZMod q) := by
      have : Fact (1 < q) := ⟨by omega⟩
      exact not_isUnit_zero
    exact MulChar.map_nonunit χ this
  -- sum over 1..q-1 is zero
  have htot : ∑ k ∈ range (q - 1), χ ((1 + k : ℕ) : ZMod q) = 0 := by
    have hb : ∑ i ∈ range q, χ ((0 + i : ℕ) : ZMod q) = ∑ a : ZMod q, χ a := by
      exact s2g5_sum_consecutive (fun a => χ a) 0
    rw [hfull] at hb
    rw [show range q = range (1 + (q - 1)) by congr 1; omega, Finset.sum_range_add] at hb
    simpa [hz] using hb
  have hsplit := htot
  rw [show q - 1 = n + (q - 1 - n) by omega, Finset.sum_range_add] at hsplit
  rw [s2g5_partial_sum_range, s2g5_partial_sum_range]
  have hrefl : ∑ k ∈ range (q - 1 - n), χ ((1 + (n + k) : ℕ) : ZMod q) =
      - ∑ k ∈ range (q - 1 - n), χ ((1 + k : ℕ) : ZMod q) := by
    rw [← Finset.sum_range_reflect, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_range] at hk
    have hc : ((1 + (n + (q - 1 - n - 1 - k)) : ℕ) : ZMod q) = -((1 + k : ℕ) : ZMod q) := by
      rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
      exact ⟨1, by omega⟩
    rw [hc, show -((1 + k : ℕ) : ZMod q) = (-1) * ((1 + k : ℕ) : ZMod q) by ring, map_mul,
      s2g5_neg_one_eq χ h_odd]
    ring
  rw [hrefl] at hsplit
  linear_combination hsplit

/-- LEAF: sharpened explicit odd Polya-Vinogradov for `q > 1200`, half period, the leaf
`leaf_odd_sharp_bound_large_period` restricted to `2 n < q` after the odd reflection, the
range kept by the Polya Fourier expansion argument of Pomerance 2011 and Frolenkov and
Soundararajan 2013. HARD -/
theorem leaf_odd_sharp_bound_large_half {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (h_odd : χ (-1) ≠ 1) (hq : 1200 < q) (n : ℕ) (hn : 2 * n < q) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * (1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + 17 / 10) := by
  sorry

/-- LEAF: the cutoff free odd bound on `8 <= q <= 1200`, half period, the leaf
`leaf_odd_sharp_bound_small_period` restricted to `2 n < q`: a finite computation over the
odd primitive characters of each modulus and `n <= (q - 1) / 2`. HARD, a large certified
finite computation. -/
theorem leaf_odd_sharp_bound_small_half {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (h_odd : χ (-1) ≠ 1) (hq8 : 8 ≤ q) (hq : q ≤ 1200) (n : ℕ)
    (hn : 2 * n < q) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * (1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + 17 / 10) := by
  sorry

/-- Assembly: exactly the statement of `leaf_odd_sharp_bound_large_period`. -/
theorem leaf_odd_sharp_bound_large_period_split {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (h_odd : χ (-1) ≠ 1) (hq : 1200 < q)
    (n : ℕ) (hn : n < q) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * (1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + 17 / 10) := by
  rcases lt_or_ge (2 * n) q with h | h
  · exact leaf_odd_sharp_bound_large_half χ hχ h_odd hq n h
  · rw [s2g5_partial_sum_reflect χ h_odd (by omega) n hn]
    exact leaf_odd_sharp_bound_large_half χ hχ h_odd hq (q - 1 - n) (by omega)

/-- Assembly: exactly the statement of `leaf_odd_sharp_bound_small_period`. -/
theorem leaf_odd_sharp_bound_small_period_split {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (h_odd : χ (-1) ≠ 1) (hq8 : 8 ≤ q)
    (hq : q ≤ 1200) (n : ℕ) (hn : n < q) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * (1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + 17 / 10) := by
  rcases lt_or_ge (2 * n) q with h | h
  · exact leaf_odd_sharp_bound_small_half χ hχ h_odd hq8 hq n h
  · rw [s2g5_partial_sum_reflect χ h_odd (by omega) n hn]
    exact leaf_odd_sharp_bound_small_half χ hχ h_odd hq8 hq (q - 1 - n) (by omega)

end LeanLab.HelfgottMajor.PolyaVinogradov123
