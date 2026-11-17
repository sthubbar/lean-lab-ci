import LeanLab.HelfgottMajor.SPLIT_polya_vinogradov_4_20

/-!
Split of the odd branch `leaf_odd_case` of the explicit Polya-Vinogradov inequality for a
primitive character modulo `q > 1`.

The odd branch bounds the supremum over `n` of the norm of the partial sums of an odd primitive
character by `1/(2*pi) * sqrt q * log q + 1/pi * sqrt q * log (log q) + sqrt q`.

The route is the odd sawtooth kernel. The partial sum of `chi` up to `n` is the `H`-truncated
Fourier expansion of that kernel summed against `chi`: the `h`-th coefficient of the odd kernel is
of size `1/(pi*h)`, the Gauss sums attached to a primitive character have norm `sqrt q`, and what the
truncation drops is a kernel error of size `q * log q / H`. Summing the coefficients over the
harmonic range `h <= H` therefore gives `sqrt q / pi` times the harmonic sum plus that error, and the
cutoff `H = ceil (sqrt q * log q)` turns `log H` into `(1/2) log q + log log q` up to the additive
`log 2` that the ceiling costs. Feeding those two estimates and a harmonic sum bound into the display
is where the three coefficients `1/(2*pi)`, `1/pi` and `1` come from.

The lemmas below are exactly those steps:

* `leaf_odd_kernel_truncation` is the kernel step, the truncated Fourier expansion with its error;
* `leaf_log_harmonic_cutoff` is the estimate on the logarithm of the chosen cutoff `H`;
* `leaf_odd_small_modulus` is the finite range `q <= 8`, where the trivial bound on a partial sum of
  a non-principal character together with the explicit values of the right-hand side closes the case.

Everything is assembled in `leaf_odd_case_split`, which has the statement of the odd branch and uses
no hypothesis beyond the ones the display carries.
-/

namespace LeanLab.HelfgottMajor.PolyaVinogradov123
open Real

/-- LEAF: the kernel step of the odd branch. For an odd primitive character modulo `q >= 8` and any
cutoff `H >= 1`, every partial sum of `chi` is bounded by `sqrt q / pi` times the harmonic sum over
`h <= H` plus the truncation error of the odd sawtooth kernel, written here as `(2/5) * q * log q / H`:
the `h`-th coefficient of the odd kernel is at most `1/(pi*h)` and the Gauss sums have norm
`sqrt q`, which gives the harmonic term, and the dropped tail of the kernel is of size `q * log q / H`
with `2/5` a safe constant in front. This is one pointwise estimate in `n`, not the display. -/
theorem leaf_odd_kernel_truncation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_odd : χ (-1) ≠ 1) (hq8 : 8 ≤ q)
    (H : ℕ) (hH : 1 ≤ H) (n : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) +
        2 / 5 * ((q : ℝ) * log (q : ℝ)) / (H : ℝ) := by
  sorry

/-- LEAF: the cutoff estimate. For `q >= 8` the ceiling of `sqrt q * log q` is at most twice
`sqrt q * log q`, because `sqrt q * log q` is at least `4` there, and the logarithm of
`sqrt q * log q` is `log (sqrt q) + log (log q)`, that is `(1/2) log q + log log q`. So the log of the
cutoff is at most `(1/2) log q + log (log q) + log 2`. This is one elementary inequality, not the
display. -/
theorem leaf_log_harmonic_cutoff {q : ℕ} [NeZero q] (hq8 : 8 ≤ q) :
    log (Nat.ceil (sqrt (q : ℝ) * log (q : ℝ)) : ℝ) ≤
      1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + log 2 := by
  have hqR : (8 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq8
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hlog8 : (2 : ℝ) ≤ log 8 := by
    have h8 : log (8 : ℝ) = 3 * log 2 := by
      rw [show ((8 : ℝ)) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    rw [h8]
    nlinarith [Real.log_two_gt_d9]
  have hlogq : (2 : ℝ) ≤ log (q : ℝ) :=
    hlog8.trans ((Real.log_le_log_iff (by norm_num) hqpos).2 hqR)
  have hlogqpos : (0 : ℝ) < log (q : ℝ) := by linarith
  have hsq : (2 : ℝ) ≤ sqrt (q : ℝ) := by
    rw [Real.le_sqrt (by norm_num) hqpos.le]
    nlinarith
  have hsqpos : (0 : ℝ) < sqrt (q : ℝ) := by linarith
  set x : ℝ := sqrt (q : ℝ) * log (q : ℝ) with hxdef
  have hx4 : (4 : ℝ) ≤ x := by rw [hxdef]; nlinarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hceilpos : (0 : ℝ) < (Nat.ceil x : ℝ) := by
    have h : 0 < Nat.ceil x := Nat.ceil_pos.2 hxpos
    exact_mod_cast h
  have hceilhalf : (Nat.ceil x : ℝ) ≤ 2 * x := by
    have h := Nat.ceil_lt_add_one hxpos.le
    linarith
  have hlogx : log x = log (sqrt (q : ℝ)) + log (log (q : ℝ)) := by
    rw [hxdef]
    exact Real.log_mul hsqpos.ne' hlogqpos.ne'
  have key : log (Nat.ceil x : ℝ) ≤ log 2 + (log (sqrt (q : ℝ)) + log (log (q : ℝ))) := by
    calc log (Nat.ceil x : ℝ) ≤ log (2 * x) :=
          (Real.log_le_log_iff hceilpos (by linarith)).2 hceilhalf
      _ = log 2 + log x := Real.log_mul (by norm_num) hxpos.ne'
      _ = log 2 + (log (sqrt (q : ℝ)) + log (log (q : ℝ))) := by rw [hlogx]
  have hsqlog : log (sqrt (q : ℝ)) = 1 / 2 * log (q : ℝ) := by
    rw [Real.log_sqrt hqpos.le]
    ring
  rw [hsqlog] at key
  linarith

/-- The values of a level-`q` character at the natural representative are `q`-periodic. -/
private lemma odd_case_period {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (m : ℕ) :
    χ ((m + q : ℕ) : ZMod q) = χ ((m : ℕ) : ZMod q) := by
  have h : ((m + q : ℕ) : ZMod q) = ((m : ℕ) : ZMod q) := by
    rw [Nat.cast_add, ZMod.natCast_self, add_zero]
  rw [h]

/-- The numerical part of the finite range: for `3 <= k <= 8` the three-term expression of the
display dominates `k / 2`. Every case is a rational comparison with `pi < 3.15` and the standard
bounds `log 2 > 0.6931`, `log 3 >= 1`, together with `log 8 = 3 log 2` and `log (8 / k)` for the
larger moduli. -/
private lemma odd_case_small_arith {k : ℕ} (h3 : 3 ≤ k) (h8 : k ≤ 8) :
    (k : ℝ) / 2 ≤
      1 / (2 * π) * sqrt (k : ℝ) * log (k : ℝ) +
        1 / π * sqrt (k : ℝ) * log (log (k : ℝ)) + sqrt (k : ℝ) := by
  have hπ0 : (0 : ℝ) < π := pi_pos
  have hπu : π < 3.15 := pi_lt_d2
  have hlog3 : (1 : ℝ) ≤ log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  interval_cases k
  · -- q = 3
    have hs : (1.732 : ℝ) ≤ sqrt 3 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    have hl : (1 : ℝ) ≤ log 3 := hlog3
    have hl0 : (0 : ℝ) < log 3 := by linarith
    have hll : (0 : ℝ) ≤ log (log 3) := Real.log_nonneg hl
    have hs0 : (0 : ℝ) < sqrt 3 := by linarith
    have hid : (1 / (2 * π) * sqrt 3 * log 3 + 1 / π * sqrt 3 * log (log 3) + sqrt 3) * π =
        sqrt 3 * log 3 / 2 + sqrt 3 * log (log 3) + sqrt 3 * π := by
      field_simp
    have hkey : (3 : ℝ) / 2 * π ≤
        sqrt 3 * log 3 / 2 + sqrt 3 * log (log 3) + sqrt 3 * π := by
      nlinarith [hs, hs0, hl, hl0, hll, hπu, hπ0]
    refine le_of_mul_le_mul_right ?_ hπ0
    push_cast
    rw [hid]
    exact hkey
  · -- q = 4
    have hs : (2 : ℝ) ≤ sqrt 4 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    have hl : (1 : ℝ) ≤ log 4 := by
      have := (Real.log_le_log_iff (by norm_num : (0:ℝ) < 3) (by norm_num : (0:ℝ) < 4)).2
        (by norm_num : (3:ℝ) ≤ 4)
      linarith
    have hl0 : (0 : ℝ) < log 4 := by linarith
    have hll : (0 : ℝ) ≤ log (log 4) := Real.log_nonneg hl
    have hs0 : (0 : ℝ) < sqrt 4 := by linarith
    have hid : (1 / (2 * π) * sqrt 4 * log 4 + 1 / π * sqrt 4 * log (log 4) + sqrt 4) * π =
        sqrt 4 * log 4 / 2 + sqrt 4 * log (log 4) + sqrt 4 * π := by
      field_simp
    have hkey : (4 : ℝ) / 2 * π ≤
        sqrt 4 * log 4 / 2 + sqrt 4 * log (log 4) + sqrt 4 * π := by
      nlinarith [hs, hs0, hl, hl0, hll, hπu, hπ0]
    refine le_of_mul_le_mul_right ?_ hπ0
    push_cast
    rw [hid]
    exact hkey
  · -- q = 5
    have hs : (2.236 : ℝ) ≤ sqrt 5 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    have hl : (1 : ℝ) ≤ log 5 := by
      have := (Real.log_le_log_iff (by norm_num : (0:ℝ) < 3) (by norm_num : (0:ℝ) < 5)).2
        (by norm_num : (3:ℝ) ≤ 5)
      linarith
    have hl0 : (0 : ℝ) < log 5 := by linarith
    have hll : (0 : ℝ) ≤ log (log 5) := Real.log_nonneg hl
    have hs0 : (0 : ℝ) < sqrt 5 := by linarith
    have hid : (1 / (2 * π) * sqrt 5 * log 5 + 1 / π * sqrt 5 * log (log 5) + sqrt 5) * π =
        sqrt 5 * log 5 / 2 + sqrt 5 * log (log 5) + sqrt 5 * π := by
      field_simp
    have hkey : (5 : ℝ) / 2 * π ≤
        sqrt 5 * log 5 / 2 + sqrt 5 * log (log 5) + sqrt 5 * π := by
      nlinarith [hs, hs0, hl, hl0, hll, hπu, hπ0]
    refine le_of_mul_le_mul_right ?_ hπ0
    push_cast
    rw [hid]
    exact hkey
  · -- q = 6
    have hs : (2.449 : ℝ) ≤ sqrt 6 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    have hl : (1.746 : ℝ) ≤ log 6 := by
      have h8 : log (8 : ℝ) = 3 * log 2 := by
        rw [show ((8 : ℝ)) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
      have hd : log ((8 : ℝ) / 6) = log 8 - log 6 :=
        Real.log_div (by norm_num : (8:ℝ) ≠ 0) (by norm_num : (6:ℝ) ≠ 0)
      have hsub : log ((8 : ℝ) / 6) ≤ 8 / 6 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      have hl2 : (0.6931471803 : ℝ) ≤ log 2 := Real.log_two_gt_d9.le
      rw [h8] at hd
      linarith
    have hl0 : (0 : ℝ) < log 6 := by linarith
    have hll : (0 : ℝ) ≤ log (log 6) := Real.log_nonneg (by linarith)
    have hs0 : (0 : ℝ) < sqrt 6 := by linarith
    have hid : (1 / (2 * π) * sqrt 6 * log 6 + 1 / π * sqrt 6 * log (log 6) + sqrt 6) * π =
        sqrt 6 * log 6 / 2 + sqrt 6 * log (log 6) + sqrt 6 * π := by
      field_simp
    have hkey : (6 : ℝ) / 2 * π ≤
        sqrt 6 * log 6 / 2 + sqrt 6 * log (log 6) + sqrt 6 * π := by
      nlinarith [hs, hs0, hl, hl0, hll, hπu, hπ0]
    refine le_of_mul_le_mul_right ?_ hπ0
    push_cast
    rw [hid]
    exact hkey
  · -- q = 7
    have hs : (2.645 : ℝ) ≤ sqrt 7 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    have hl : (1.936 : ℝ) ≤ log 7 := by
      have h8 : log (8 : ℝ) = 3 * log 2 := by
        rw [show ((8 : ℝ)) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
      have hd : log ((8 : ℝ) / 7) = log 8 - log 7 :=
        Real.log_div (by norm_num : (8:ℝ) ≠ 0) (by norm_num : (7:ℝ) ≠ 0)
      have hsub : log ((8 : ℝ) / 7) ≤ 8 / 7 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      have hl2 : (0.6931471803 : ℝ) ≤ log 2 := Real.log_two_gt_d9.le
      rw [h8] at hd
      linarith
    have hl0 : (0 : ℝ) < log 7 := by linarith
    have hll : (0.3 : ℝ) ≤ log (log 7) := by
      have hbase : (0.3 : ℝ) ≤ log 1.936 := by
        have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 1.936)
        linarith
      have hmono : log 1.936 ≤ log (log 7) :=
        (Real.log_le_log_iff (by norm_num : (0:ℝ) < 1.936) hl0).2 hl
      linarith
    have hs0 : (0 : ℝ) < sqrt 7 := by linarith
    have hid : (1 / (2 * π) * sqrt 7 * log 7 + 1 / π * sqrt 7 * log (log 7) + sqrt 7) * π =
        sqrt 7 * log 7 / 2 + sqrt 7 * log (log 7) + sqrt 7 * π := by
      field_simp
    have hkey : (7 : ℝ) / 2 * π ≤
        sqrt 7 * log 7 / 2 + sqrt 7 * log (log 7) + sqrt 7 * π := by
      nlinarith [hs, hs0, hl, hl0, hll, hπu, hπ0]
    refine le_of_mul_le_mul_right ?_ hπ0
    push_cast
    rw [hid]
    exact hkey
  · -- q = 8
    have hs : (2.828 : ℝ) ≤ sqrt 8 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    have hl : (2.079 : ℝ) ≤ log 8 := by
      have h8 : log (8 : ℝ) = 3 * log 2 := by
        rw [show ((8 : ℝ)) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
      have hl2 : (0.6931471803 : ℝ) ≤ log 2 := Real.log_two_gt_d9.le
      linarith
    have hl0 : (0 : ℝ) < log 8 := by linarith
    have hll : (0.693 : ℝ) ≤ log (log 8) := by
      have h2 : (2 : ℝ) ≤ log 8 := by linarith
      have hmono : log 2 ≤ log (log 8) :=
        (Real.log_le_log_iff (by norm_num : (0:ℝ) < 2) hl0).2 h2
      have hl2 : (0.6931471803 : ℝ) ≤ log 2 := Real.log_two_gt_d9.le
      linarith
    have hs0 : (0 : ℝ) < sqrt 8 := by linarith
    have hid : (1 / (2 * π) * sqrt 8 * log 8 + 1 / π * sqrt 8 * log (log 8) + sqrt 8) * π =
        sqrt 8 * log 8 / 2 + sqrt 8 * log (log 8) + sqrt 8 * π := by
      field_simp
    have hkey : (8 : ℝ) / 2 * π ≤
        sqrt 8 * log 8 / 2 + sqrt 8 * log (log 8) + sqrt 8 * π := by
      nlinarith [hs, hs0, hl, hl0, hll, hπu, hπ0]
    refine le_of_mul_le_mul_right ?_ hπ0
    push_cast
    rw [hid]
    exact hkey

/-- LEAF: the finite range `q <= 8` of the odd branch. For these moduli a partial sum of a
non-principal character is at most `q/2` in norm, and `q/2` is below the right-hand side of the
display for each of `q = 2, ..., 8`, so the display holds there with room to spare. This is a finite
range only and says nothing about `q >= 8`. -/
theorem leaf_odd_small_modulus {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_odd : χ (-1) ≠ 1) (hq8 : q ≤ 8) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  haveI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.2 hq
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq2 : 2 ≤ q := by omega
  -- an odd character takes `-1` to `-1`, hence is antitone under negation
  have hneg1 : χ (-1) = -1 := by
    have h1 : χ (-1) * χ (-1) = (1 : ℂ) := by
      rw [← map_mul, show (-1 : ZMod q) * (-1) = 1 by ring, map_one]
    rcases mul_self_eq_one_iff.mp h1 with h | h
    · exact absurd h h_odd
    · exact h
  have hneg : ∀ x : ZMod q, χ (-x) = -χ x := by
    intro x
    rw [← neg_one_mul x, map_mul, hneg1, neg_one_mul]
  set f : ℕ → ℂ := fun m => χ ((m : ℕ) : ZMod q) with hf
  -- the `q - 1` units of one period cancel in pairs
  have hZ : ∑ m ∈ Finset.Ico 1 q, f m = 0 := by
    have hreflect : ∑ m ∈ Finset.Ico 1 q, f (q - m) = ∑ m ∈ Finset.Ico 1 q, f m := by
      have h := Finset.sum_Ico_reflect (f := f) (k := 1) (m := q) (n := q) (by omega : q ≤ q + 1)
      rw [show q + 1 - q = 1 by omega, show q + 1 - 1 = q by omega] at h
      exact h
    have hneg2 : ∑ m ∈ Finset.Ico 1 q, f (q - m) = -∑ m ∈ Finset.Ico 1 q, f m := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro m hm
      obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.mp hm
      have hcast : ((q - m : ℕ) : ZMod q) = -((m : ℕ) : ZMod q) := by
        rw [eq_neg_iff_add_eq_zero]
        rw [← Nat.cast_add, Nat.sub_add_cancel (le_of_lt hm2), ZMod.natCast_self]
      simp only [hf]
      rw [hcast]
      exact hneg _
    have hSx : ∑ m ∈ Finset.Ico 1 q, f m = -∑ m ∈ Finset.Ico 1 q, f m :=
      hreflect.symm.trans hneg2
    have hfin : (2 : ℂ) * (∑ m ∈ Finset.Ico 1 q, f m) = 0 := by
      have h2 : (∑ m ∈ Finset.Ico 1 q, f m) + (∑ m ∈ Finset.Ico 1 q, f m) = 0 := by
        nth_rewrite 2 [hSx]
        exact add_neg_cancel _
      rw [two_mul]
      exact h2
    exact (mul_eq_zero.mp hfin).resolve_left (by norm_num)
  -- consecutive full blocks of `q` values have the same sum
  have hstep : ∀ j : ℕ, ∑ m ∈ Finset.Ico (j + 1) (j + 1 + q), f m =
      ∑ m ∈ Finset.Ico j (j + q), f m := by
    intro j
    have hA : ∑ m ∈ Finset.Ico j (j + 1), f m = f j := by simp
    have hB : ∑ m ∈ Finset.Ico (j + q) (j + 1 + q), f m = f (j + q) := by
      rw [show j + 1 + q = j + q + 1 by omega]
      simp
    have hp : f (j + q) = f j := odd_case_period χ j
    have h1 : ∑ m ∈ Finset.Ico j (j + 1), f m + ∑ m ∈ Finset.Ico (j + 1) (j + q), f m
        = ∑ m ∈ Finset.Ico j (j + q), f m :=
      Finset.sum_Ico_consecutive f (show j ≤ j + 1 by omega) (show j + 1 ≤ j + q by omega)
    have h2 : ∑ m ∈ Finset.Ico (j + 1) (j + q), f m + ∑ m ∈ Finset.Ico (j + q) (j + 1 + q), f m
        = ∑ m ∈ Finset.Ico (j + 1) (j + 1 + q), f m :=
      Finset.sum_Ico_consecutive f (show j + 1 ≤ j + q by omega) (show j + q ≤ j + 1 + q by omega)
    rw [hA] at h1
    rw [hB] at h2
    calc ∑ m ∈ Finset.Ico (j + 1) (j + 1 + q), f m
        = ∑ m ∈ Finset.Ico (j + 1) (j + q), f m + f (j + q) := h2.symm
      _ = f (j + q) + ∑ m ∈ Finset.Ico (j + 1) (j + q), f m := by rw [add_comm]
      _ = f j + ∑ m ∈ Finset.Ico (j + 1) (j + q), f m := by rw [hp]
      _ = ∑ m ∈ Finset.Ico j (j + q), f m := h1
  have hblock : ∀ j : ℕ, ∑ m ∈ Finset.Ico j (j + q), f m = 0 := by
    intro j
    induction j with
    | zero =>
        have hzero : ∑ m ∈ Finset.Ico 0 (0 + q), f m = 0 := by
          rw [Nat.zero_add, Nat.Ico_zero_eq_range]
          have hsplit : ∑ m ∈ Finset.range 1, f m + ∑ m ∈ Finset.Ico 1 q, f m
              = ∑ m ∈ Finset.range q, f m :=
            Finset.sum_range_add_sum_Ico f (by omega)
          have hf0 : f 0 = 0 := by
            simp only [hf]
            simpa using MulChar.map_zero χ
          have hr1 : ∑ m ∈ Finset.range 1, f m = f 0 := by simp
          rw [hr1, hZ, hf0, zero_add] at hsplit
          exact hsplit.symm
        exact hzero
    | succ k ih =>
        rw [hstep k]
        exact ih
  -- the partial sums are periodic with period `q`
  have hSadd : ∀ n : ℕ, ∑ m ∈ Finset.Icc 1 (n + q), f m = ∑ m ∈ Finset.Icc 1 n, f m := by
    intro n
    have hBl : ∑ m ∈ Finset.Ico (n + 1) (n + q + 1), f m = 0 := by
      rw [show n + q + 1 = n + 1 + q by omega]
      exact hblock (n + 1)
    have hsplit : ∑ m ∈ Finset.Ico 1 (n + 1), f m + ∑ m ∈ Finset.Ico (n + 1) (n + q + 1), f m
        = ∑ m ∈ Finset.Ico 1 (n + q + 1), f m :=
      Finset.sum_Ico_consecutive f (show 1 ≤ n + 1 by omega) (show n + 1 ≤ n + q + 1 by omega)
    rw [hBl, add_zero, Finset.Ico_add_one_right_eq_Icc,
      Finset.Ico_add_one_right_eq_Icc] at hsplit
    exact hsplit.symm
  have hSmod : ∀ n : ℕ, ∑ m ∈ Finset.Icc 1 n, f m = ∑ m ∈ Finset.Icc 1 (n % q), f m := by
    intro n
    set r : ℕ := n % q with hr
    have hdecomp : n = n / q * q + r := by
      rw [hr, mul_comm]
      exact (Nat.div_add_mod n q).symm
    have hgen : ∀ a : ℕ, ∑ m ∈ Finset.Icc 1 (a * q + r), f m = ∑ m ∈ Finset.Icc 1 r, f m := by
      intro a
      induction a with
      | zero => simp
      | succ k ih =>
          rw [show (k + 1) * q + r = (k * q + r) + q by ring, hSadd, ih]
    rw [hdecomp]
    exact hgen (n / q)
  have hbound : ∀ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, f m‖ ≤ (q : ℝ) / 2 := by
    intro n
    rw [hSmod n]
    set r : ℕ := n % q with hr
    have hlt : r < q := by
      rw [hr]
      exact Nat.mod_lt _ (by omega)
    have hA : ‖∑ m ∈ Finset.Icc 1 r, f m‖ ≤ (r : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      have h1 : ∑ m ∈ Finset.Icc 1 r, ‖f m‖ ≤ ∑ _m ∈ Finset.Icc 1 r, (1 : ℝ) :=
        Finset.sum_le_sum (fun m _ => by
          simp only [hf]
          exact DirichletCharacter.norm_le_one χ _)
      have h2 : ∑ _m ∈ Finset.Icc 1 r, (1 : ℝ) = (r : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one, Nat.add_sub_cancel]
      linarith
    have hnil : ∑ m ∈ Finset.Icc 1 r, f m = -∑ m ∈ Finset.Ico (r + 1) q, f m := by
      have hsplit : ∑ m ∈ Finset.Ico 1 (r + 1), f m + ∑ m ∈ Finset.Ico (r + 1) q, f m
          = ∑ m ∈ Finset.Ico 1 q, f m :=
        Finset.sum_Ico_consecutive f (show 1 ≤ r + 1 by omega) (Nat.succ_le_of_lt hlt)
      rw [hZ, Finset.Ico_add_one_right_eq_Icc] at hsplit
      rw [eq_neg_iff_add_eq_zero]
      exact hsplit
    have hB : ‖∑ m ∈ Finset.Icc 1 r, f m‖ ≤ (q : ℝ) - 1 - r := by
      rw [hnil, norm_neg]
      refine (norm_sum_le _ _).trans ?_
      have h1 : ∑ m ∈ Finset.Ico (r + 1) q, ‖f m‖ ≤ ∑ _m ∈ Finset.Ico (r + 1) q, (1 : ℝ) :=
        Finset.sum_le_sum (fun m _ => by
          simp only [hf]
          exact DirichletCharacter.norm_le_one χ _)
      have h2 : ∑ _m ∈ Finset.Ico (r + 1) q, (1 : ℝ) = (q : ℝ) - 1 - r := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one,
          Nat.cast_sub (Nat.succ_le_of_lt hlt)]
        push_cast
        ring
      linarith
    have hmin : min (r : ℝ) ((q : ℝ) - 1 - r) ≤ (q : ℝ) / 2 := by
      rcases le_total (r : ℝ) ((q : ℝ) - 1 - r) with hc | hc
      · rw [min_eq_left hc]
        linarith
      · rw [min_eq_right hc]
        linarith
    linarith [le_min hA hB]
  refine le_trans (ciSup_le hbound) ?_
  -- `q = 2` carries no odd character, so only `3 <= q <= 8` remains
  have hq3 : 3 ≤ q := by
    rcases Nat.lt_or_ge q 3 with h | h
    · have hcases : q = 1 ∨ q = 2 := by omega
      rcases hcases with h1 | h2
      · exact absurd h1 hq
      · exfalso
        have hm1 : (-1 : ZMod 2) = 1 := by decide
        subst h2
        exact h_odd (by rw [hm1]; exact map_one χ)
    · exact h
  exact odd_case_small_arith hq3 hq8

/-- Arithmetic core of the assembly, with `u = sqrt q`, `v = log q` and `w = log log q`: after the
harmonic factor `1 + (v/2 + w + log 2)` and the truncation error `(2/5) * u` are put in, what is left
is `u * (1 + log 2) <= (3/5) * u * pi`, true because `log 2 < 0.694` and `pi > 3`. -/
private lemma odd_case_arith {u v w : ℝ} (hu : 0 ≤ u) :
    u / π * (1 + (1 / 2 * v + w + log 2)) + 2 / 5 * u ≤
      1 / (2 * π) * u * v + 1 / π * u * w + u := by
  have hπ : (0 : ℝ) < π := pi_pos
  have h3 : (3 : ℝ) < π := pi_gt_three
  have hl : log 2 < 0.6931471808 := log_two_lt_d9
  have key : u * (1 + (1 / 2 * v + w + log 2)) + 2 / 5 * (u * π) ≤
      u * v / 2 + u * w + u * π := by
    nlinarith [hu, h3, hl]
  have hπne : π ≠ 0 := ne_of_gt hπ
  field_simp
  nlinarith [key]

/-- The odd branch of the display, assembled from the three leaves: the finite range `q <= 8` is the
first leaf, and for `q >= 8` the kernel leaf is fed the cutoff `H = ceil (sqrt q * log q)`, the
logarithm of the cutoff from the second leaf, the harmonic sum bound `sum 1/h <= 1 + log H`, and the
truncation error `(2/5) * q * log q / H <= (2/5) * sqrt q` which the choice of `H` gives. -/
theorem leaf_odd_case_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_odd : χ (-1) ≠ 1) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  by_cases hsmall : q ≤ 8
  · exact leaf_odd_small_modulus χ hχ hq h_odd hsmall
  have hq8 : 8 ≤ q := Nat.le_of_lt (Nat.lt_of_not_le hsmall)
  have hqR : (8 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq8
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hsqrt2 : (2 : ℝ) ≤ sqrt (q : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (le_of_lt hqpos)]
    nlinarith
  have hlog8 : (2 : ℝ) ≤ log 8 := by
    have h8 : log (8 : ℝ) = 3 * log 2 := by
      rw [show ((8 : ℝ)) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    rw [h8]
    nlinarith [Real.log_two_gt_d9]
  have hlogq : (2 : ℝ) ≤ log (q : ℝ) :=
    hlog8.trans (Real.log_le_log (by norm_num) hqR)
  set H : ℕ := Nat.ceil (sqrt (q : ℝ) * log (q : ℝ)) with hHdef
  have hx4 : (4 : ℝ) ≤ sqrt (q : ℝ) * log (q : ℝ) := by nlinarith
  have hHle : sqrt (q : ℝ) * log (q : ℝ) ≤ (H : ℝ) := by
    rw [hHdef]
    exact Nat.le_ceil _
  have hH1 : 1 ≤ H := by
    rw [hHdef]
    have h : (1 : ℝ) ≤ ((Nat.ceil (sqrt (q : ℝ) * log (q : ℝ))) : ℝ) := by
      linarith [Nat.le_ceil (sqrt (q : ℝ) * log (q : ℝ))]
    exact_mod_cast h
  have hbound : (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      sqrt (q : ℝ) / π * (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) +
        2 / 5 * ((q : ℝ) * log (q : ℝ)) / (H : ℝ) :=
    ciSup_le fun n => leaf_odd_kernel_truncation χ hχ hq h_odd hq8 H hH1 n
  have hharm : (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) ≤ 1 + log (H : ℝ) := by
    have heq : (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) = (harmonic H : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Rat.cast_inv, Rat.cast_natCast]
      simp [one_div]
    rw [heq]
    exact harmonic_le_one_add_log H
  have hlogH : log (H : ℝ) ≤ 1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + log 2 := by
    rw [hHdef]
    exact leaf_log_harmonic_cutoff hq8
  have herr : 2 / 5 * ((q : ℝ) * log (q : ℝ)) / (H : ℝ) ≤ 2 / 5 * sqrt (q : ℝ) := by
    have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH1
    have hxpos : (0 : ℝ) < sqrt (q : ℝ) * log (q : ℝ) := by linarith
    have hqsq : (q : ℝ) = sqrt (q : ℝ) * sqrt (q : ℝ) := by
      rw [Real.mul_self_sqrt (le_of_lt hqpos)]
    rw [div_le_iff₀ hHpos]
    nlinarith [hHle, hxpos, hqsq]
  have hfinal : sqrt (q : ℝ) / π * (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) +
        2 / 5 * ((q : ℝ) * log (q : ℝ)) / (H : ℝ) ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
    have hu : (0 : ℝ) ≤ sqrt (q : ℝ) / π := by positivity
    have h1 : sqrt (q : ℝ) / π * (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) ≤
        sqrt (q : ℝ) / π * (1 + (1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + log 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ hu
      linarith
    have h2 := odd_case_arith (u := sqrt (q : ℝ)) (v := log (q : ℝ)) (w := log (log (q : ℝ)))
      (by positivity)
    linarith
  linarith

end LeanLab.HelfgottMajor.PolyaVinogradov123
