import LeanLab.OpenProblems.SPLIT_route_euler_positive_density

/-!
# Feed1122 split of `route_euler_positive_density` (OpenProblems, State1612), repaired

`SPLIT_route_euler_positive_density.lean` assembles `route_euler_positive_density` from five
leaves, but its LEAF 3, `leaf_second_moment_card`, quantifies over every `R` with the right zero
set and is false; `Feed1122SPLIT_route_euler_positive_densityFalse.lean` on the sibling branch
`claude/OpenProblems-feed1122-SPLIT_route_euler_positive_density` of this burst refutes it in
Lean with `R n = n` on representable `n`.

This file repairs the route as `leaf_first_moment_card` was repaired, by pinning `R` with `hRdef`
to the triangular count of LEAF 1, the number of `k` with `4n + 1 - 2k(k+1)` prime, and it splits
the repaired second moment further.  Writing `R ^ 2 = R (R - 1) + R`:

* the diagonal, the sum of `R` over the representable `n ≤ X`, is PROVED here at most
  `X ^ 2 / (log X) ^ 2`, from `R n ≤ sqrt (2n) + 1` and `(log X) ^ 2 * sqrt X = o(X)`;
* the off diagonal, the sum of `R (R - 1)`, a count of ordered pairs `k ≠ l` with both
  `4n + 1 - 2k(k+1)` and `4n + 1 - 2l(l+1)` prime, is the one LEAF, class HARD.

The assembly reuses the proved LEAF 1, LEAF 2, LEAF 4 and LEAF 5 of the existing split; LEAF 2,
`leaf_first_moment_card`, is sorry free.  So `route_euler_positive_density` now rests on the single
off diagonal leaf below.  No definition is introduced.  AI wrote the Lean code.  Binary Goldbach
is open.
-/

namespace LeanLab.OpenProblems.State1612

open LeanLab
open scoped Classical

/-- The triangular count is at most `sqrt (2n) + 1`: a prime difference forces `2k(k+1) < 4n`. -/
private lemma tri_count_le (n : ℕ) :
    ((Finset.range (4 * n + 2)).filter
        (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card ≤ Nat.sqrt (2 * n) + 1 := by
  calc _ ≤ (Finset.range (Nat.sqrt (2 * n) + 1)).card := by
        apply Finset.card_le_card
        intro k hk
        rw [Finset.mem_filter] at hk
        rw [Finset.mem_range, Nat.lt_succ_iff]
        have h2 := hk.2.two_le
        apply Nat.le_sqrt.mpr
        have : 2 * k * (k + 1) ≤ 4 * n := by omega
        nlinarith
    _ = Nat.sqrt (2 * n) + 1 := Finset.card_range _

/-- `(log X) ^ 2 * (sqrt (2X) + 1) ≤ X` for all large `X`, from `log X = o(X ^ (1/4))`. -/
private lemma log_sq_mul_le :
    ∀ᶠ X : ℕ in Filter.atTop,
      Real.log (X : ℝ) ^ 2 * (Real.sqrt (2 * (X : ℝ)) + 1) ≤ (X : ℝ) := by
  have hlo := (isLittleO_log_rpow_atTop (r := (1 / 4 : ℝ)) (by norm_num)).bound
    (c := 1 / 4) (by norm_num)
  have hlo' := tendsto_natCast_atTop_atTop.eventually hlo
  filter_upwards [hlo', Filter.eventually_ge_atTop 1] with X hX h1
  have hx1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast h1
  have hx0 : (0 : ℝ) ≤ (X : ℝ) := by linarith
  set y := (X : ℝ) ^ (1 / 4 : ℝ) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg hx0 _
  have hy4 : y ^ 4 = (X : ℝ) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  have hy1 : 1 ≤ y := Real.one_le_rpow hx1 (by norm_num)
  have hlog0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hx1
  have hlogy : Real.log (X : ℝ) ≤ y / 4 := by
    have := hX
    rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hy0] at this
    linarith
  have hsq : Real.sqrt (X : ℝ) = y ^ 2 := by
    rw [← hy4, show y ^ 4 = (y ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hs2 : Real.sqrt (2 * (X : ℝ)) ≤ 2 * y ^ 2 := by
    rw [Real.sqrt_mul (by norm_num), hsq]
    have : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith [sq_nonneg y]
  have hL2 : Real.log (X : ℝ) ^ 2 ≤ y ^ 2 / 16 := by nlinarith
  have hA : Real.sqrt (2 * (X : ℝ)) + 1 ≤ 3 * y ^ 2 := by nlinarith
  calc Real.log (X : ℝ) ^ 2 * (Real.sqrt (2 * (X : ℝ)) + 1)
      ≤ (y ^ 2 / 16) * (3 * y ^ 2) :=
        mul_le_mul hL2 hA (by positivity) (by positivity)
    _ = 3 / 16 * y ^ 4 := by ring
    _ ≤ (X : ℝ) := by rw [hy4]; linarith

/-- The diagonal: the sum of `R` over the representable `n ≤ X` is at most `X ^ 2 / (log X) ^ 2`. -/
private lemma diag_bound (R : ℕ → ℕ)
    (hRdef : ∀ n : ℕ, R n = ((Finset.range (4 * n + 2)).filter
        (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card) :
    ∀ᶠ X : ℕ in Filter.atTop,
      Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
          (fun n => (R n : ℝ))
        ≤ (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2 := by
  filter_upwards [log_sq_mul_le, Filter.eventually_ge_atTop 2] with X hX h2
  set s := (Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)) with hs
  have hx0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg _
  have hterm : ∀ n ∈ s, (R n : ℝ) ≤ Real.sqrt (2 * (X : ℝ)) + 1 := by
    intro n hn
    have hnX : n ≤ X := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    have h1 : R n ≤ Nat.sqrt (2 * X) + 1 := by
      rw [hRdef n]
      exact (tri_count_le n).trans (by
        have := Nat.sqrt_le_sqrt (show 2 * n ≤ 2 * X by omega); omega)
    have h2 : ((Nat.sqrt (2 * X) : ℕ) : ℝ) ≤ Real.sqrt (2 * (X : ℝ)) := by
      have := Real.nat_sqrt_le_real_sqrt (a := 2 * X)
      simpa using this
    have h1' : (R n : ℝ) ≤ ((Nat.sqrt (2 * X) : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hcard : (s.card : ℝ) ≤ (X : ℝ) := by
    have : s.card ≤ X := by
      calc s.card ≤ (Finset.Icc 1 X).card := Finset.card_filter_le _ _
        _ = X := by rw [Nat.card_Icc]; omega
    exact_mod_cast this
  have hsum : s.sum (fun n => (R n : ℝ)) ≤ (X : ℝ) * (Real.sqrt (2 * (X : ℝ)) + 1) := by
    calc s.sum (fun n => (R n : ℝ)) ≤ s.sum (fun _ => Real.sqrt (2 * (X : ℝ)) + 1) :=
          Finset.sum_le_sum hterm
      _ = (s.card : ℝ) * (Real.sqrt (2 * (X : ℝ)) + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (X : ℝ) * (Real.sqrt (2 * (X : ℝ)) + 1) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast h2)
  rw [le_div_iff₀ (by positivity)]
  calc s.sum (fun n => (R n : ℝ)) * Real.log (X : ℝ) ^ 2
      ≤ (X : ℝ) * (Real.sqrt (2 * (X : ℝ)) + 1) * Real.log (X : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = (X : ℝ) * (Real.log (X : ℝ) ^ 2 * (Real.sqrt (2 * (X : ℝ)) + 1)) := by ring
    _ ≤ (X : ℝ) * (X : ℝ) := mul_le_mul_of_nonneg_left hX hx0
    _ = (X : ℝ) ^ 2 := by ring

/-- The second moment from the off diagonal leaf: `R ^ 2 = R (R - 1) + R`, and the diagonal sum
of `R` is at most `X ^ 2 / (log X) ^ 2` because `R n ≤ sqrt (2n) + 1`. -/
theorem second_of_offdiag (R : ℕ → ℕ)
    (hRdef : ∀ n : ℕ, R n = ((Finset.range (4 * n + 2)).filter
        (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card)
    (hoff : ∃ b : ℝ, 0 < b ∧ ∀ᶠ X : ℕ in Filter.atTop,
      Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
          (fun n => (R n : ℝ) * ((R n : ℝ) - 1))
        ≤ b * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ X : ℕ in Filter.atTop,
      Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
          (fun n => (R n : ℝ) ^ 2)
        ≤ b * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2 := by
  obtain ⟨b, hb, hev⟩ := hoff
  refine ⟨b + 1, by linarith, ?_⟩
  filter_upwards [hev, diag_bound R hRdef] with X h1 h2
  have hsplit : Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
        (fun n => (R n : ℝ) ^ 2) =
      Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
        (fun n => (R n : ℝ) * ((R n : ℝ) - 1)) +
      Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
        (fun n => (R n : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [hsplit]
  have : (b + 1) * (X : ℝ) ^ 2 / Real.log (X : ℝ) ^ 2 =
      b * (X : ℝ) ^ 2 / Real.log (X : ℝ) ^ 2 + (X : ℝ) ^ 2 / Real.log (X : ℝ) ^ 2 := by ring
  rw [this]
  linarith


/-- LEAF: off diagonal part of the second moment step in the Cauchy-Schwarz route to positive
density.  Class HARD.  For the triangular count `R n`, the number of `k` with `4n + 1 - 2k(k+1)`
prime, the sum of `R n * (R n - 1)` over the representable `n ≤ X` is at most
`b * X ^ 2 / (log X) ^ 2` for a fixed `b > 0` and all large `X`.  The sum counts triples
`(n, k, l)` with `k ≠ l` and both `p = 4n + 1 - 2k(k+1)` and `p + h` prime, where
`h = 2 (k (k+1) - l (l+1)) ≠ 0`; an upper bound sieve, Selberg or Brun, bounds each shift by a
constant times the singular series of `h` times `X / (log X) ^ 2`, there are about `X` pairs
`(k, l)`, and the singular series has bounded mean over them.  The diagonal `k = l` is not part
of this leaf; it is proved above. -/
theorem leaf_offdiag_second_moment (R : ℕ → ℕ)
    (hRdef : ∀ n : ℕ, R n = ((Finset.range (4 * n + 2)).filter
        (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ X : ℕ in Filter.atTop,
      Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
          (fun n => (R n : ℝ) * ((R n : ℝ) - 1))
        ≤ b * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2 := by
  exact?

/-- The repaired second moment, the statement of `leaf_second_moment_card` with `hRdef` added, as
`leaf_first_moment_card` carries it, proved from the off diagonal leaf and the diagonal bound. -/
theorem leaf_second_moment_card_def (R : ℕ → ℕ)
    (hRdef : ∀ n : ℕ, R n = ((Finset.range (4 * n + 2)).filter
        (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card)
    (hR : ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3))) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ X : ℕ in Filter.atTop,
      Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
          (fun n => (R n : ℝ) ^ 2)
        ≤ b * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2 :=
  second_of_offdiag R hRdef (leaf_offdiag_second_moment R hRdef)

/-- The statement of `route_euler_positive_density`, identical, assembled from the proved LEAF 1,
LEAF 2, LEAF 4 and LEAF 5 of `SPLIT_route_euler_positive_density.lean`, the proved diagonal bound,
and the off diagonal leaf above, with no use of the false `leaf_second_moment_card`. -/
theorem route_euler_positive_density_feed1122 :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in Filter.atTop, c * X ≤ ((X - euExc X : ℕ) : ℝ) := by
  obtain ⟨R, hRdef, hR⟩ := leaf_representation_multiplicity
  obtain ⟨a, ha, hfirst⟩ := leaf_first_moment_card R hRdef hR
  obtain ⟨b, hb, hsecond⟩ := leaf_second_moment_card_def R hRdef hR
  obtain ⟨c, hc, hcard⟩ := leaf_cauchy_schwarz_density R hR a b ha hb hfirst hsecond
  refine ⟨c, hc, ?_⟩
  filter_upwards [hcard] with X hX
  rw [← leaf_card_eq_complement X]
  exact hX

end LeanLab.OpenProblems.State1612
