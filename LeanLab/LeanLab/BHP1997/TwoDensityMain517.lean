/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character, the
E2 sum of display 5.15, page 50.

The paper proves 5.17 with the words "a straightforward consequence of the prime number
theorem". For the E2 sum, with the rough cofactor `n3` already replaced by its Buchstab density
at level `p2`, this file carries out the exact part of that consequence and separates the two
analytic parts:

* `two_density_swap_combine`: the sum over `m` in a prefix of J and the sum over the prime pairs
  `p1 p2` are interchanged, and the multiples `m = p1 p2 n` are reindexed by the cofactor `n`;
* `two_cofactor_riemann`, proved in `TwoDensityMain517a.lean`: for each pair the cofactor sum
  over `n` is the average over `m` of the same density at the real point `m / (p1 p2)`. No
  prime number theorem is used; only the pairs with `p1 p2^2 ≤ 2 Y` contribute and there are
  at most `Y ^ (9 / 10)` of them;
* `two_pair_density_pointwise`, in `TwoDensityMain517b.lean`: for each `m` in J the sum over
  the prime pairs, weighted by `1 / (p1 p2)`, is the E2 integral of page 51 with `1` replaced
  by `s = log m / log Z`. This is the prime number theorem with partial summation in `p1` and
  then in `p2`, proved in `TwoDensityMain517c.lean` to `TwoDensityMain517f.lean`; the two
  open leaves are the passages from the integer sums to the integral, one for each variable.

`two_density_main` has exactly the statement of `leaf_two_density_main` of
`LowerPrincipal517f.lean` and is proved from these.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a
import LeanLab.BHP1997.RoughFamily514
import LeanLab.BHP1997.TwoDensityMain517a
import LeanLab.BHP1997.TwoDensityMain517b

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators

/-- P0069 page 51 display 5.17. Real valued form of the reindexing of one subtracted sum of
5.15 by the cofactor: the multiples `m = d * n` of an outer product `d ≥ 1` in `(L, U]`
correspond to the cofactors `n` in `(L / d, U / d]`. -/
theorem two_density_dvd_reindex {d : ℕ} (hd : 1 ≤ d) (L U : ℕ) (g : ℕ → ℝ) :
    ∑ m ∈ Finset.Ioc L U, (if d ∣ m then g m else 0) =
      ∑ n ∈ Finset.Ioc (L / d) (U / d), g (d * n) := by
  have h := Rough514.sum_dvd_reindex hd L U (fun m => ((g m : ℝ) : ℂ))
  have h2 : ((∑ m ∈ Finset.Ioc L U, (if d ∣ m then g m else 0) : ℝ) : ℂ) =
      ((∑ n ∈ Finset.Ioc (L / d) (U / d), g (d * n) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Complex.ofReal_sum, ← h]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  exact_mod_cast h2

/-- P0069 page 51 display 5.17 with page 50 display 5.15. The exact step of the passage from
the E2 sum to its density: interchange the sum over `m` in `(L0, U]` with the sum over the
outer products `d i`, reindex the multiples of `d i` by the cofactor, and split the difference
from the density `D m` into the cofactor comparison, bounded by `EB`, and the pointwise
comparison of the outer sum with the density, bounded by `EA` for each `m`. -/
theorem two_density_swap_combine {ι : Type} (I : Finset ι) (d : ι → ℕ)
    (hd : ∀ i ∈ I, 1 ≤ d i) (f φ : ι → ℕ → ℝ) (D : ℕ → ℝ) (L0 U : ℕ) (EA EB : ℝ)
    (hEA : 0 ≤ EA)
    (hB : |∑ i ∈ I, ((∑ n ∈ Finset.Ioc (L0 / d i) (U / d i), f i n) -
        ∑ m ∈ Finset.Ioc L0 U, φ i m)| ≤ EB)
    (hA : ∀ m ∈ Finset.Ioc L0 U, |(∑ i ∈ I, φ i m) - D m| ≤ EA) :
    |∑ m ∈ Finset.Ioc L0 U,
        ((∑ i ∈ I, if d i ∣ m then f i (m / d i) else 0) - D m)| ≤ EB + U * EA := by
  have hswap : ∑ m ∈ Finset.Ioc L0 U, ∑ i ∈ I, (if d i ∣ m then f i (m / d i) else 0) =
      ∑ i ∈ I, ∑ n ∈ Finset.Ioc (L0 / d i) (U / d i), f i n := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [two_density_dvd_reindex (hd i hi) L0 U (fun m => f i (m / d i))]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Nat.mul_div_cancel_left n (hd i hi)]
  have hc : ∑ i ∈ I, ∑ m ∈ Finset.Ioc L0 U, φ i m =
      ∑ m ∈ Finset.Ioc L0 U, ∑ i ∈ I, φ i m := Finset.sum_comm
  have key : ∑ m ∈ Finset.Ioc L0 U,
        ((∑ i ∈ I, if d i ∣ m then f i (m / d i) else 0) - D m) =
      (∑ i ∈ I, ((∑ n ∈ Finset.Ioc (L0 / d i) (U / d i), f i n) -
        ∑ m ∈ Finset.Ioc L0 U, φ i m)) +
      ∑ m ∈ Finset.Ioc L0 U, ((∑ i ∈ I, φ i m) - D m) := by
    simp only [Finset.sum_sub_distrib]
    linarith [hswap, hc]
  rw [key]
  have h2 : |∑ m ∈ Finset.Ioc L0 U, ((∑ i ∈ I, φ i m) - D m)| ≤ U * EA := by
    calc |∑ m ∈ Finset.Ioc L0 U, ((∑ i ∈ I, φ i m) - D m)|
        ≤ ∑ m ∈ Finset.Ioc L0 U, |(∑ i ∈ I, φ i m) - D m| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Ioc L0 U, EA := Finset.sum_le_sum hA
      _ = ((U - L0 : ℕ) : ℝ) * EA := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      _ ≤ U * EA :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le U L0) hEA
  exact (abs_add_le _ _).trans (add_le_add hB h2)

/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number theorem",
applied to the outer primes `p1`, `p2` of the E2 sum of display 5.15: the statement of
`leaf_two_density_main`. With the rough cofactor `n3 = m / (p1 p2)` replaced by its Buchstab
density at level `p2`, the sum over prime pairs with exponents in E2 has local density
`(1 / log Z) ∫∫_{E2} ω((s - β1 - β2) / β2) / (β1 β2^2)` at `m = Z^s`, with every log power
saved on every prefix of J. CONDITIONAL ON two leaves of
`TwoDensityMain517b.lean`, neither a statement about primes: `leaf_two_pair_riemann_first` and
`leaf_two_pair_riemann_second`, the two one variable passages from the sum over integer pairs
with density `1 / (log a log b)` to the E2 integral of page 51. -/
theorem two_density_main (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ U : ℕ, U ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ U,
        ((∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
              i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
                lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
            if i.1 * i.2 ∣ m then
              ω (Real.log ((m / (i.1 * i.2) : ℕ) : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ)
            else 0) -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨CA, hCA⟩ := two_pair_density_pointwise ω hω hz hε hε8 A hA
  obtain ⟨CB, hCB⟩ := two_cofactor_riemann ω hω hz hε hε8 A hA
  refine ⟨max (max CA CB) (|CB| + 2 * |CA| + 1), fun x hx U hU => ?_⟩
  have hxA : CA ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxB : CB ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hC3 : |CB| + 2 * |CA| + 1 ≤ max (max CA CB) (|CB| + 2 * |CA| + 1) := le_max_right _ _
  have hx1 : (1 : ℝ) ≤ x := by
    have h1 := abs_nonneg CA
    have h2 := abs_nonneg CB
    linarith
  have hYpos : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have hYL : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) := mul_nonneg hYpos.le hL
  have hU' : (U : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    (Nat.cast_le.mpr hU).trans (Nat.floor_le (by positivity))
  have hB' := hCB x hxB U hU
  have hmain := two_density_swap_combine
    (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
      (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
      i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
        lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)))
    (fun i : ℕ × ℕ => i.1 * i.2)
    (fun i hi => by
      have hi' := (Finset.mem_filter.mp hi).2
      exact Nat.mul_pos hi'.1.pos hi'.2.1.pos)
    (fun (i : ℕ × ℕ) (n : ℕ) =>
      ω (Real.log (n : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ))
    (fun (i : ℕ × ℕ) (m : ℕ) =>
      ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ))) / Real.log (i.2 : ℝ)) /
        Real.log (i.2 : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ)))
    (fun m : ℕ => lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
      Real.log (scaleZ ε x))
    ⌊x ^ (11 / 20 + ε)⌋₊ U (|CA| * Real.log x ^ (-A))
    (CB * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    (mul_nonneg (abs_nonneg CA) hL) hB'
    (fun m hm => by
      have hm' := Finset.mem_Ioc.mp hm
      exact (hCA x hxA m hm'.1 (hm'.2.trans hU)).trans
        (mul_le_mul_of_nonneg_right (le_abs_self CA) hL))
  refine hmain.trans ?_
  have h1 : CB * x ^ (11 / 20 + ε) * Real.log x ^ (-A) ≤
      |CB| * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self CB) hYL
  have h2 : (U : ℝ) * (|CA| * Real.log x ^ (-A)) ≤
      2 * |CA| * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
    calc (U : ℝ) * (|CA| * Real.log x ^ (-A))
        ≤ 2 * x ^ (11 / 20 + ε) * (|CA| * Real.log x ^ (-A)) :=
          mul_le_mul_of_nonneg_right hU' (mul_nonneg (abs_nonneg CA) hL)
      _ = 2 * |CA| * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
  have h3 := mul_le_mul_of_nonneg_right hC3 hYL
  have h4 : (|CB| + 2 * |CA| + 1) * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) =
      |CB| * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) +
        2 * |CA| * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) +
        x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by ring
  have h5 : max (max CA CB) (|CB| + 2 * |CA| + 1) * x ^ (11 / 20 + ε) * Real.log x ^ (-A) =
      max (max CA CB) (|CB| + 2 * |CA| + 1) *
        (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
  linarith

end LeanLab.BHP1997.LowerShortC165
