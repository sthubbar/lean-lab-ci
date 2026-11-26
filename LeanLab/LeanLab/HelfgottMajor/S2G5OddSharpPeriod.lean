import LeanLab.HelfgottMajor.SPLIT_leaf_odd_kernel_truncation

/-!
Periodicity split of the two cutoff free odd leaves of
`HelfgottMajor/SPLIT_leaf_odd_kernel_truncation.lean`, burst-20261124 agent S2G5.

Both `leaf_odd_sharp_bound_large` and `leaf_odd_sharp_bound_small` bound the partial
sums `S(n) = sum_{1 <= m <= n} χ(m)` of an odd primitive character for every `n`. The
explicit Polya-Vinogradov argument of P0014, and every source cited there, first
reduces to one period: a nontrivial character sums to zero over any `q` consecutive
integers, so `S(n + q) = S(n)` and `S(n) = S(n % q)`. That reduction is proved here,
and the two leaves are restated for `n < q` only. For the small leaf this makes the
finite computation literally finite: at most `1200` values of `n` per character.

Numerical check, burst-20261124 S2G5, numpy, all odd primitive characters of every
modulus `8 <= q <= 1600`, composite moduli included, all `n < q`: the ratio of the
largest partial sum to `sqrt q / pi * (1/2 log q + log log q + 17/10)` is at most
`0.7531`, at `q = 11`; on `121 <= q <= 800` at most `0.7427`, on `801 <= q <= 1200` at
most `0.7022`, on `1201 <= q <= 1600` at most `0.7125`. The count of primitive
characters found matched the multiplicative formula on every modulus tested.
-/

namespace LeanLab.HelfgottMajor.PolyaVinogradov123
open Real Finset

/-- A function on `ZMod q` summed over `q` consecutive naturals is its full sum. -/
theorem s2g5_sum_consecutive {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (n : ℕ) :
    ∑ i ∈ range q, f ((n + i : ℕ) : ZMod q) = ∑ a : ZMod q, f a := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => f ((n + i : ℕ) : ZMod q))]
  apply Fintype.sum_bijective (fun i : Fin q => ((n + (i : ℕ) : ℕ) : ZMod q))
  · rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp [ZMod.card]⟩
    intro i j hij
    simp only at hij
    rw [ZMod.natCast_eq_natCast_iff'] at hij
    have hi := i.isLt
    have hj := j.isLt
    apply Fin.ext
    have h1 : Nat.ModEq q (n + (i : ℕ)) (n + (j : ℕ)) := hij
    have h2 : Nat.ModEq q (i : ℕ) (j : ℕ) := Nat.ModEq.add_left_cancel' n h1
    have h3 : (i : ℕ) % q = (j : ℕ) % q := h2
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h3
  · intro i; rfl

/-- Periodicity of the partial sums of a nontrivial character: `S(n + q) = S(n)`. -/
theorem s2g5_partial_sum_add_period {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (h : χ ≠ 1) (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 (n + q), χ (m : ZMod q) = ∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q) := by
  have hI : ∀ N : ℕ, ∑ m ∈ Finset.Icc 1 N, χ (m : ZMod q) =
      ∑ k ∈ range N, χ ((1 + k : ℕ) : ZMod q) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ, Nat.add_comm 1 N]
  rw [hI, hI, Finset.sum_range_add]
  have hb := s2g5_sum_consecutive (fun a => χ a) (1 + n)
  have hz : ∑ k ∈ range q, χ ((1 + (n + k) : ℕ) : ZMod q) = 0 := by
    rw [← MulChar.sum_eq_zero_of_ne_one h, ← hb]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Nat.add_assoc]
  rw [hz, add_zero]

/-- Reduction to one period: `S(n) = S(n % q)` for a nontrivial character. -/
theorem s2g5_partial_sum_mod {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (h : χ ≠ 1) (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q) = ∑ m ∈ Finset.Icc 1 (n % q), χ (m : ZMod q) := by
  have key : ∀ r k : ℕ, ∑ m ∈ Finset.Icc 1 (r + q * k), χ (m : ZMod q) =
      ∑ m ∈ Finset.Icc 1 r, χ (m : ZMod q) := by
    intro r k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, ← Nat.add_assoc, s2g5_partial_sum_add_period χ h, ih]
  conv_lhs => rw [← Nat.mod_add_div n q]
  exact key _ _

/-- An odd character is nontrivial. -/
theorem s2g5_ne_one_of_odd {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (h_odd : χ (-1) ≠ 1) : χ ≠ 1 := by
  intro h; apply h_odd; rw [h]; exact MulChar.one_apply isUnit_one.neg

/-- LEAF: sharpened explicit odd Polya-Vinogradov for `q > 1200`, one period, the leaf
`leaf_odd_sharp_bound_large` of P0014's explicit Polya-Vinogradov input restricted to
`n < q`, the range left after the periodicity reduction that opens the Polya Fourier
expansion argument of Pomerance 2011 and Frolenkov and Soundararajan 2013. HARD -/
theorem leaf_odd_sharp_bound_large_period {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (h_odd : χ (-1) ≠ 1) (hq : 1200 < q) (n : ℕ) (hn : n < q) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * (1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + 17 / 10) := by
  sorry

/-- LEAF: the cutoff free odd bound on `8 <= q <= 1200`, one period, the leaf
`leaf_odd_sharp_bound_small` restricted to `n < q`: a finite computation over the odd
primitive characters of each modulus and the `q` values of `n`. Numerically the ratio is
at most `0.7531`, see the header. HARD, a large certified finite computation. -/
theorem leaf_odd_sharp_bound_small_period {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (h_odd : χ (-1) ≠ 1) (hq8 : 8 ≤ q) (hq : q ≤ 1200) (n : ℕ)
    (hn : n < q) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * (1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + 17 / 10) := by
  sorry

/-- Assembly: exactly the statement of `leaf_odd_sharp_bound_large`, from the one period
leaf and the periodicity reduction. -/
theorem leaf_odd_sharp_bound_large_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (h_odd : χ (-1) ≠ 1) (hq : 1200 < q) (n : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * (1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + 17 / 10) := by
  rw [s2g5_partial_sum_mod χ (s2g5_ne_one_of_odd χ h_odd) n]
  exact leaf_odd_sharp_bound_large_period χ hχ h_odd hq (n % q)
    (Nat.mod_lt n (NeZero.pos q))

/-- Assembly: exactly the statement of `leaf_odd_sharp_bound_small`, from the one period
leaf and the periodicity reduction. -/
theorem leaf_odd_sharp_bound_small_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (h_odd : χ (-1) ≠ 1) (hq8 : 8 ≤ q) (hq : q ≤ 1200) (n : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * (1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + 17 / 10) := by
  rw [s2g5_partial_sum_mod χ (s2g5_ne_one_of_odd χ h_odd) n]
  exact leaf_odd_sharp_bound_small_period χ hχ h_odd hq8 hq (n % q)
    (Nat.mod_lt n (NeZero.pos q))

end LeanLab.HelfgottMajor.PolyaVinogradov123
