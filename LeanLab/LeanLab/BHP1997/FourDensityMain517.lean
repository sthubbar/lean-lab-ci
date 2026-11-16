/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character, the
E4 sum reached from display 5.15, page 50.

The paper proves 5.17 with the words "a straightforward consequence of the prime number
theorem". For the E4 sum, with the rough cofactor `n5` already replaced by its Buchstab density
at level `p4`, this file carries out the part of that consequence that needs no prime number
theorem, cites the partial summation in the outer primes and names the one remaining part:

* `four_density_swap_combine`: the sum over `m` in a prefix of J and the sum over the prime
  quadruples `p1 p2 p3 p4` are interchanged, and the multiples `m = p1 p2 p3 p4 n` are reindexed
  by the cofactor `n`;
* `four_cofactor_riemann`, PROVED: for each quadruple the cofactor sum over `n` is the average
  over `m` of the same density at the real point `m / (p1 p2 p3 p4)`. Only the quadruples with
  `p1 p2 p3 p4 ^ 2 ≤ U` contribute, each costs `O(U / (p1 p2 p3 p4 ^ 2))`, and `p4` is at least
  `(2 Y) ^ (1 / 10)`;
* `four_quad_density_pointwise`: for each `m` in J the sum over the prime quadruples,
  weighted by `1 / (p1 p2 p3 p4)`, is the E4 integral of page 51 with `1` replaced by
  `s = log m / log Z`. Partial summation in `p1`, `p2`, `p3`, `p4` is proved in
  `FourDensityMain517a.lean` from the prime number theorem, with the jumps of the E4 indicator
  counted in `FourDensityMain517b.lean`. The resulting sum over integer quadruples is
  rewritten in `four_integer_riemann` as a Riemann sum of the integrand of
  `lowerFourDensityAt` on the grid of exponents. The sealed leaf
  `leaf_four_exponent_riemann` is assembled from the four coordinate quadrature leaves in
  `FourExponentQuadrature517`. They use no prime number theorem. All four coordinate estimates are proved.

`four_density_main` has exactly the statement of `leaf_four_density_main` of
`LowerPrincipal517f.lean`. It is proved from the four proved coordinate quadrature estimates.

No new definition in this file. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a
import LeanLab.BHP1997.RoughFamily514
import LeanLab.BHP1997.FourDensityMain517a
import LeanLab.BHP1997.FourExponentQuadrature517

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators

/-- P0069 page 51 display 5.17. Real valued form of the reindexing of one subtracted sum of
5.15 by the cofactor: the multiples `m = d * n` of an outer product `d ≥ 1` in `(L, U]`
correspond to the cofactors `n` in `(L / d, U / d]`. -/
theorem four_density_dvd_reindex {d : ℕ} (hd : 1 ≤ d) (L U : ℕ) (g : ℕ → ℝ) :
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
the E4 sum to its density: interchange the sum over `m` in `(L0, U]` with the sum over the
outer products `d i`, reindex the multiples of `d i` by the cofactor, and split the difference
from the density `D m` into the cofactor comparison, bounded by `EB`, and the pointwise
comparison of the outer sum with the density, bounded by `EA` for each `m`. -/
theorem four_density_swap_combine {ι : Type} (I : Finset ι) (d : ι → ℕ)
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
    rw [four_density_dvd_reindex (hd i hi) L0 U (fun m => f i (m / d i))]
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

/-- P0069 page 51 display 5.17, the cofactor variable `n5` of the E4 sum. Counting the
multiples: the integers below `d * q` fall into `q` full blocks of length `d` on which the
integer quotient by `d` is constant. -/
theorem four_block_sum_mul (d : ℕ) (G : ℕ → ℝ) (q : ℕ) :
    ∑ m ∈ Finset.range (d * q), G (m / d) = d * ∑ n ∈ Finset.range q, G n := by
  induction q with
  | zero => simp
  | succ q ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    have h : ∀ x ∈ Finset.range d, G ((d * q + x) / d) = G q := fun x hx => by
      rw [Nat.mul_add_div hd, Nat.div_eq_of_lt (Finset.mem_range.mp hx), add_zero]
    rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring

/-- P0069 page 51 display 5.17, the cofactor variable `n5` of the E4 sum. A prefix of the
integers ending inside the block of quotient `q` differs from `q + 1` full blocks by at most
one block. -/
theorem four_block_prefix {d : ℕ} (G : ℕ → ℝ) (q r : ℕ) (hr : r < d) :
    |∑ m ∈ Finset.range (d * q + (r + 1)), G (m / d) -
        d * ∑ n ∈ Finset.range (q + 1), G n| ≤ d * |G q| := by
  have hd : 0 < d := by omega
  rw [Finset.sum_range_add, four_block_sum_mul, Finset.sum_range_succ G q]
  have h : ∀ x ∈ Finset.range (r + 1), G ((d * q + x) / d) = G q := fun x hx => by
    have hx' := Finset.mem_range.mp hx
    rw [Nat.mul_add_div hd, Nat.div_eq_of_lt (by omega), add_zero]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have e : (d : ℝ) * ∑ n ∈ Finset.range q, G n + ((r + 1 : ℕ) : ℝ) * G q -
      d * (∑ n ∈ Finset.range q, G n + G q) = -(((d : ℝ) - ((r + 1 : ℕ) : ℝ)) * G q) := by
    ring
  rw [e, abs_neg, abs_mul]
  have h1 : ((r + 1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hr
  have h2 : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_of_nonneg (by linarith)]
  exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)

/-- P0069 page 51 display 5.17, the cofactor variable `n5` of the E4 sum. The sum over `m` in
`(L, U]` of a function of the integer quotient `m / d` is `d` times the sum over the cofactors
`n` in `(L / d, U / d]`, up to the two incomplete blocks at the ends. -/
theorem four_block_Ioc {d : ℕ} (hd : 1 ≤ d) (G : ℕ → ℝ) {L U : ℕ} (hLU : L ≤ U) {B : ℝ}
    (hB : ∀ n : ℕ, n ≤ U / d → |G n| ≤ B) :
    |∑ m ∈ Finset.Ioc L U, G (m / d) - d * ∑ n ∈ Finset.Ioc (L / d) (U / d), G n| ≤
      2 * d * B := by
  have e1 : ∀ a b : ℕ, a ≤ b → ∀ f : ℕ → ℝ, ∑ k ∈ Finset.Ioc a b, f k =
      ∑ k ∈ Finset.range (b + 1), f k - ∑ k ∈ Finset.range (a + 1), f k := by
    intro a b hab f
    have hs : Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [hs, Finset.sum_Ico_eq_sub _ (by omega)]
  have hdiv : L / d ≤ U / d := Nat.div_le_div_right hLU
  have pU := four_block_prefix G (U / d) (U % d) (Nat.mod_lt _ hd)
  have pL := four_block_prefix G (L / d) (L % d) (Nat.mod_lt _ hd)
  have hU : d * (U / d) + (U % d + 1) = U + 1 := by
    have := Nat.div_add_mod U d
    omega
  have hL : d * (L / d) + (L % d + 1) = L + 1 := by
    have := Nat.div_add_mod L d
    omega
  rw [hU] at pU
  rw [hL] at pL
  rw [e1 L U hLU, e1 (L / d) (U / d) hdiv]
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have bU : (d : ℝ) * |G (U / d)| ≤ d * B := mul_le_mul_of_nonneg_left (hB _ le_rfl) hd0
  have bL : (d : ℝ) * |G (L / d)| ≤ d * B := mul_le_mul_of_nonneg_left (hB _ hdiv) hd0
  have e : ∑ k ∈ Finset.range (U + 1), G (k / d) - ∑ k ∈ Finset.range (L + 1), G (k / d) -
      d * (∑ k ∈ Finset.range (U / d + 1), G k - ∑ k ∈ Finset.range (L / d + 1), G k) =
      (∑ k ∈ Finset.range (U + 1), G (k / d) - d * ∑ k ∈ Finset.range (U / d + 1), G k) -
      (∑ k ∈ Finset.range (L + 1), G (k / d) - d * ∑ k ∈ Finset.range (L / d + 1), G k) := by
    ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  linarith

/-- P0069 page 51 display 5.17, the cofactor variable `n5` of the E4 sum. The Buchstab density
at level `p` vanishes at every real point below `p`, by the zero extension of `ω` below 1. -/
theorem four_cofactor_zero {ω : ℝ → ℝ}
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω) {p : ℕ} (hp : 2 ≤ p)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t < p) : ω (Real.log t / Real.log (p : ℝ)) = 0 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  apply hz
  rcases ht0.eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero, zero_div]
    norm_num
  · rw [div_lt_one hlp]
    exact Real.log_lt_log h0 ht

/-- P0069 page 51 display 5.17, the cofactor variable `n5` of the E4 sum. The Buchstab density
at level `p` changes by at most `3 / p` between the real point `m / d` and its integer part:
both values vanish below `p`, and above `p` the function `ω` is 1-Lipschitz and the logarithm
moves by at most `1 / p`. -/
theorem four_cofactor_point {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω) {d p : ℕ} (hd : 1 ≤ d)
    (hp : 2 ≤ p) (m : ℕ) :
    |ω (Real.log ((m / d : ℕ) : ℝ) / Real.log (p : ℝ)) / Real.log (p : ℝ) -
        ω (Real.log ((m : ℝ) / (d : ℝ)) / Real.log (p : ℝ)) / Real.log (p : ℝ)| ≤
      3 / (p : ℝ) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hl2 : (0.69 : ℝ) < Real.log (p : ℝ) := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num) hp2
    linarith
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlow : (((m / d : ℕ) : ℕ) : ℝ) ≤ (m : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hupp : (m : ℝ) / (d : ℝ) < (((m / d : ℕ) : ℕ) : ℝ) + 1 := by
    have h := Nat.lt_mul_div_succ m (show 0 < d by omega)
    have h' : (m : ℝ) < (d : ℝ) * ((((m / d : ℕ) : ℕ) : ℝ) + 1) := by exact_mod_cast h
    rw [div_lt_iff₀ hd0]
    linarith
  generalize (m / d : ℕ) = n at hlow hupp
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  by_cases hn : n < p
  · have hnp : ((n : ℝ)) + 1 ≤ (p : ℝ) := by exact_mod_cast hn
    rw [four_cofactor_zero hz hp hn0 (by linarith),
      four_cofactor_zero hz hp (hn0.trans hlow) (by linarith)]
    simp only [zero_div, sub_zero, abs_zero]
    positivity
  · have hpn : (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast not_lt.mp hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hu : 1 ≤ Real.log (n : ℝ) / Real.log (p : ℝ) := by
      rw [le_div_iff₀ hlp, one_mul]
      exact Real.log_le_log hp0 hpn
    have huv : Real.log (n : ℝ) / Real.log (p : ℝ) ≤
        Real.log ((m : ℝ) / (d : ℝ)) / Real.log (p : ℝ) :=
      div_le_div_of_nonneg_right (Real.log_le_log hnpos hlow) hlp.le
    have hlip := Decomp514a.four_density_buchstab_lipschitz_ordered hω hz hu huv
    have hlog : Real.log ((m : ℝ) / (d : ℝ)) - Real.log (n : ℝ) ≤ 1 / (p : ℝ) := by
      have h1 : Real.log ((m : ℝ) / (d : ℝ)) ≤ Real.log ((n : ℝ) + 1) :=
        Real.log_le_log (by linarith) hupp.le
      have h2 : Real.log (((n : ℝ) + 1) / (n : ℝ)) ≤ ((n : ℝ) + 1) / (n : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by linarith) hnpos.ne'] at h2
      have h3 : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
        rw [add_div, div_self hnpos.ne']
        ring
      have h4 : 1 / (n : ℝ) ≤ 1 / (p : ℝ) := one_div_le_one_div_of_le hp0 hpn
      linarith
    have hdiff : Real.log ((m : ℝ) / (d : ℝ)) / Real.log (p : ℝ) -
        Real.log (n : ℝ) / Real.log (p : ℝ) ≤ 1 / (p : ℝ) / Real.log (p : ℝ) := by
      rw [← sub_div]
      exact div_le_div_of_nonneg_right hlog hlp.le
    rw [← sub_div, abs_div, abs_of_pos hlp, div_le_iff₀ hlp]
    refine hlip.trans (hdiff.trans ?_)
    rw [div_le_iff₀ hlp]
    have h5 : (1 : ℝ) ≤ 3 * (Real.log (p : ℝ) * Real.log (p : ℝ)) := by nlinarith
    have h6 : 0 ≤ 1 / (p : ℝ) := by positivity
    calc 1 / (p : ℝ) = 1 / (p : ℝ) * 1 := by ring
      _ ≤ 1 / (p : ℝ) * (3 * (Real.log (p : ℝ) * Real.log (p : ℝ))) :=
          mul_le_mul_of_nonneg_left h5 h6
      _ = 3 / (p : ℝ) * Real.log (p : ℝ) * Real.log (p : ℝ) := by ring

/-- P0069 page 51 display 5.17, the cofactor variable `n5` of the E4 sum, one outer product
`d` with level `p`. The sum over the cofactors `n` in `(L / d, U / d]` of the Buchstab density
`ω(log n / log p) / log p` is the sum over `m` in `(L, U]` of the same density at the real
point `m / d`, divided by `d`, up to `7 U / (d p)`. Nothing is lost unless `d p ≤ U`. -/
theorem four_cofactor_block {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω) {d p : ℕ} (hd : 1 ≤ d)
    (hp : 2 ≤ p) (L U : ℕ) :
    |(∑ n ∈ Finset.Ioc (L / d) (U / d),
          ω (Real.log (n : ℝ) / Real.log (p : ℝ)) / Real.log (p : ℝ)) -
        ∑ m ∈ Finset.Ioc L U,
          ω (Real.log ((m : ℝ) / (d : ℝ)) / Real.log (p : ℝ)) / Real.log (p : ℝ) / (d : ℝ)| ≤
      7 * (U : ℝ) / ((d : ℝ) * (p : ℝ)) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hU0 : (0 : ℝ) ≤ (U : ℝ) := Nat.cast_nonneg U
  have hlp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hl2 : (0.69 : ℝ) < Real.log (p : ℝ) := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num) hp2
    linarith
  rcases lt_or_ge U L with hUL | hLU
  · rw [Finset.Ioc_eq_empty_of_le hUL.le,
      Finset.Ioc_eq_empty_of_le (Nat.div_le_div_right hUL.le)]
    simp only [Finset.sum_empty, sub_zero, abs_zero]
    positivity
  have hB : ∀ n : ℕ, n ≤ U / d →
      |ω (Real.log (n : ℝ) / Real.log (p : ℝ)) / Real.log (p : ℝ)| ≤
        2 * (U : ℝ) / ((d : ℝ) * (p : ℝ)) := by
    intro n hn
    by_cases hnp : n < p
    · rw [four_cofactor_zero hz hp (Nat.cast_nonneg n) (by exact_mod_cast hnp)]
      simp only [zero_div, abs_zero]
      positivity
    · have h1 : n * d ≤ U := (Nat.le_div_iff_mul_le (by omega)).mp hn
      have h2 : p * d ≤ U := (Nat.mul_le_mul_right d (not_lt.mp hnp)).trans h1
      have h3 : (d : ℝ) * (p : ℝ) ≤ (U : ℝ) := by
        have : ((p * d : ℕ) : ℝ) ≤ (U : ℝ) := by exact_mod_cast h2
        push_cast at this
        linarith
      have h4 : (1 : ℝ) ≤ (U : ℝ) / ((d : ℝ) * (p : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      have h5 := Decomp514a.four_density_buchstab_nonneg hω hz
        (Real.log (n : ℝ) / Real.log (p : ℝ))
      have h6 := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz
        (Real.log (n : ℝ) / Real.log (p : ℝ))
      rw [abs_of_nonneg (div_nonneg h5 hlp.le), div_le_iff₀ hlp]
      have h7 : 2 * (U : ℝ) / ((d : ℝ) * (p : ℝ)) = 2 * ((U : ℝ) / ((d : ℝ) * (p : ℝ))) := by
        ring
      rw [h7]
      nlinarith
  have blk := four_block_Ioc hd
    (fun n : ℕ => ω (Real.log (n : ℝ) / Real.log (p : ℝ)) / Real.log (p : ℝ)) hLU hB
  have pt : |∑ m ∈ Finset.Ioc L U,
      (ω (Real.log ((m / d : ℕ) : ℝ) / Real.log (p : ℝ)) / Real.log (p : ℝ) -
        ω (Real.log ((m : ℝ) / (d : ℝ)) / Real.log (p : ℝ)) / Real.log (p : ℝ))| ≤
      (U : ℝ) * (3 / (p : ℝ)) := by
    calc _ ≤ ∑ m ∈ Finset.Ioc L U,
          |ω (Real.log ((m / d : ℕ) : ℝ) / Real.log (p : ℝ)) / Real.log (p : ℝ) -
            ω (Real.log ((m : ℝ) / (d : ℝ)) / Real.log (p : ℝ)) / Real.log (p : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Ioc L U, 3 / (p : ℝ) :=
          Finset.sum_le_sum fun m _ => four_cofactor_point hω hz hd hp m
      _ = ((U - L : ℕ) : ℝ) * (3 / (p : ℝ)) := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      _ ≤ (U : ℝ) * (3 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le U L) (by positivity)
  have key : (∑ n ∈ Finset.Ioc (L / d) (U / d),
          ω (Real.log (n : ℝ) / Real.log (p : ℝ)) / Real.log (p : ℝ)) -
        ∑ m ∈ Finset.Ioc L U,
          ω (Real.log ((m : ℝ) / (d : ℝ)) / Real.log (p : ℝ)) / Real.log (p : ℝ) / (d : ℝ) =
      1 / (d : ℝ) * (∑ m ∈ Finset.Ioc L U,
        (ω (Real.log ((m / d : ℕ) : ℝ) / Real.log (p : ℝ)) / Real.log (p : ℝ) -
          ω (Real.log ((m : ℝ) / (d : ℝ)) / Real.log (p : ℝ)) / Real.log (p : ℝ))) -
      1 / (d : ℝ) * (∑ m ∈ Finset.Ioc L U,
          ω (Real.log ((m / d : ℕ) : ℝ) / Real.log (p : ℝ)) / Real.log (p : ℝ) -
        d * ∑ n ∈ Finset.Ioc (L / d) (U / d),
          ω (Real.log (n : ℝ) / Real.log (p : ℝ)) / Real.log (p : ℝ)) := by
    have gen : ∀ S a g : ℝ, S - g / (d : ℝ) =
        1 / (d : ℝ) * (a - g) - 1 / (d : ℝ) * (a - d * S) := by
      intro S a g
      field_simp
      ring
    rw [Finset.sum_sub_distrib, ← Finset.sum_div (Finset.Ioc L U) _ (d : ℝ)]
    exact gen _ _ _
  rw [key]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (d : ℝ))]
  have hinv : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
  have t1 := mul_le_mul_of_nonneg_left pt hinv
  have t2 := mul_le_mul_of_nonneg_left blk hinv
  have e1 : 1 / (d : ℝ) * ((U : ℝ) * (3 / (p : ℝ))) = 3 * (U : ℝ) / ((d : ℝ) * (p : ℝ)) := by
    field_simp
  have e2 : 1 / (d : ℝ) * (2 * (d : ℝ) * (2 * (U : ℝ) / ((d : ℝ) * (p : ℝ)))) =
      4 * (U : ℝ) / ((d : ℝ) * (p : ℝ)) := by
    field_simp
    ring
  have e3 : 7 * (U : ℝ) / ((d : ℝ) * (p : ℝ)) =
      3 * (U : ℝ) / ((d : ℝ) * (p : ℝ)) + 4 * (U : ℝ) / ((d : ℝ) * (p : ℝ)) := by ring
  rw [e1] at t1
  rw [e2] at t2
  rw [e3]
  exact add_le_add t1 t2

/-- P0069 page 51 display 5.17, the E4 sum reached from display 5.15, the cofactor variable
`n5`. For each prime quadruple `p1 p2 p3 p4` with exponents in E4 the sum over the cofactors
`n` in `(Y / (p1 p2 p3 p4), U / (p1 p2 p3 p4)]` of the Buchstab density
`ω(log n / log p4) / log p4` is the sum over `m` in `(Y, U]` of the same density at the real
point `m / (p1 p2 p3 p4)`, divided by `p1 p2 p3 p4`. No prime number theorem is used: by
`four_cofactor_block` each quadruple costs at most `7 U / (p1 p2 p3 p4 ^ 2)`, the level `p4` is
at least `(2 Y) ^ (1 / 10)` and the reciprocal sum over the quadruples is a fixed log power, so
a power of `Y` is saved. -/
theorem four_cofactor_riemann (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ U : ℕ, U ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
              i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          ((∑ n ∈ Finset.Ioc (⌊x ^ (11 / 20 + ε)⌋₊ / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2))
                (U / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2)),
              ω (Real.log (n : ℝ) / Real.log (i.2.2.2 : ℝ)) / Real.log (i.2.2.2 : ℝ)) -
            ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ U,
              ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
                  (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
                Real.log (i.2.2.2 : ℝ) /
                  ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ)))| ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, hC1⟩ := log_rpow_lt_rpow (A + 4)
  refine ⟨max (max C1 ((2 : ℝ) ^ 12)) (max (Real.exp 2) 224), fun x hx U hU => ?_⟩
  have hxC1 : C1 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx12 : (2 : ℝ) ^ 12 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hxe : Real.exp 2 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hC224 : (224 : ℝ) ≤ max (max C1 ((2 : ℝ) ^ 12)) (max (Real.exp 2) 224) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx12
  have hxpos : 0 < x := by linarith
  have hY43 : (4 : ℝ) ^ 3 ≤ x ^ (11 / 20 + ε) := by
    refine Decomp514a.four_shortY_ge_of_sq_le hε hx1 ?_
    have h43 : ((4 : ℝ) ^ 3) ^ 2 = (2 : ℝ) ^ 12 := by norm_num
    rw [h43]
    exact hx12
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY43
  have hl2 : 2 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hxe
  have hlpos : 0 < Real.log x := by linarith
  have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    Nat.floor_le (by linarith)
  have hU' : (U : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := (Nat.cast_le.mpr hU).trans hNle
  have hN1 : (1 : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by
    have : 1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; linarith)
    exact_mod_cast this
  -- the level saving
  have hW : x ^ (11 / 200 : ℝ) ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) := by
    have hYge : x ^ (11 / 20 : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by
      have h := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : (11 / 20 : ℝ) ≤ 11 / 20 + ε)
      linarith
    calc x ^ (11 / 200 : ℝ) = (x ^ (11 / 20 : ℝ)) ^ (1 / 10 : ℝ) := by
          rw [← Real.rpow_mul hxpos.le]; norm_num
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hxpos.le _) hYge (by norm_num)
  have hlogW : Real.log x ^ (A + 4) < x ^ (11 / 200 : ℝ) := hC1 x hxC1
  have hsplit : Real.log x ^ (A + 4) = Real.log x ^ A * Real.log x ^ (4 : ℕ) := by
    rw [Real.rpow_add hlpos, ← Real.rpow_natCast]
    norm_num
  have hLA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlpos _
  have hL4 : 0 < Real.log x ^ (4 : ℕ) := pow_pos hlpos 4
  have hWlow : Real.log x ^ A * Real.log x ^ (4 : ℕ) ≤
      (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) := by
    rw [← hsplit]
    exact hlogW.le.trans hW
  have hWpos : 0 < (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) :=
    lt_of_lt_of_le (mul_pos hLA hL4) hWlow
  -- the reciprocal sum
  have hrec := Decomp514a.four_reciprocal_sum_le ⌊2 * x ^ (11 / 20 + ε)⌋₊
    (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
      (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
      (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
      (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
      i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
        i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
        lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
          (expo ε x i.2.2.2))) (Finset.filter_subset _ _)
  have hlogN : 1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * Real.log x := by
    have h1 : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ Real.log (2 * x ^ (11 / 20 + ε)) :=
      Real.log_le_log (by linarith) hNle
    rw [Real.log_mul (by norm_num) hYpos.ne', Real.log_rpow hxpos] at h1
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    have h3 : (11 / 20 + ε) * Real.log x ≤ 3 / 5 * Real.log x :=
      mul_le_mul_of_nonneg_right (by norm_num at hε8 ⊢; linarith) hlpos.le
    linarith
  have hlogN0 : 0 ≤ 1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by
    have := Real.log_nonneg hN1
    linarith
  have hrec2 := hrec.trans (pow_le_pow_left₀ hlogN0 hlogN 4)
  -- each quadruple
  have hterm : ∀ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
              i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
      |(∑ n ∈ Finset.Ioc (⌊x ^ (11 / 20 + ε)⌋₊ / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2))
                (U / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2)),
              ω (Real.log (n : ℝ) / Real.log (i.2.2.2 : ℝ)) / Real.log (i.2.2.2 : ℝ)) -
            ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ U,
              ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
                  (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
                Real.log (i.2.2.2 : ℝ) /
                  ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ))| ≤
        14 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) *
          (1 / ((i.1 * i.2.1 * i.2.2.1 * i.2.2.2 : ℕ) : ℝ)) := by
    intro i hi
    obtain ⟨-, hp1, hp2, hp3, hp4, -, -, -, hreg⟩ := Finset.mem_filter.mp hi
    obtain ⟨-, hb2⟩ := Decomp514a.four_outer_bounds hε hε8 hY43 hp1 hp2 hp3 hp4 hreg
    have hdpos : 1 ≤ i.1 * i.2.1 * i.2.2.1 * i.2.2.2 :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp1.pos hp2.pos) hp3.pos) hp4.pos
    have h := four_cofactor_block hω hz hdpos hp4.two_le ⌊x ^ (11 / 20 + ε)⌋₊ U
    simp only [Nat.cast_mul] at h ⊢
    refine h.trans ?_
    have hd0 : (0 : ℝ) < (i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ) := by
      have : (0 : ℝ) < ((i.1 * i.2.1 * i.2.2.1 * i.2.2.2 : ℕ) : ℝ) := by exact_mod_cast hdpos
      simpa only [Nat.cast_mul] using this
    have hp40 : (0 : ℝ) < (i.2.2.2 : ℝ) := by exact_mod_cast hp4.pos
    rw [div_le_iff₀ (mul_pos hd0 hp40)]
    have hWne := hWpos.ne'
    have hDne := hd0.ne'
    have e : 14 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) *
        (1 / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ))) *
        ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ) * (i.2.2.2 : ℝ)) =
        14 * x ^ (11 / 20 + ε) * ((i.2.2.2 : ℝ) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) := by
      have gen : ∀ K W D q : ℝ, W ≠ 0 → D ≠ 0 → K / W * (1 / D) * (D * q) = K * (q / W) := by
        intro K W D q hW hD
        field_simp
      exact gen _ _ _ _ hWne hDne
    rw [e]
    have h1 : (1 : ℝ) ≤ (i.2.2.2 : ℝ) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) := by
      rw [le_div_iff₀ hWpos, one_mul]
      exact hb2
    nlinarith
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.mul_sum]
  have hK0 : 0 ≤ 14 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) := by
    positivity
  refine (mul_le_mul_of_nonneg_left hrec2 hK0).trans ?_
  have hlogA : Real.log x ^ (-A) = (Real.log x ^ A)⁻¹ := Real.rpow_neg hlpos.le A
  have hfin : 14 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) *
      (2 * Real.log x) ^ 4 ≤ 224 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
    rw [hlogA, div_mul_eq_mul_div, div_le_iff₀ hWpos]
    have hWne := hWpos.ne'
    have hLAne := hLA.ne'
    have e : 224 * x ^ (11 / 20 + ε) * (Real.log x ^ A)⁻¹ *
        (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) =
        224 * x ^ (11 / 20 + ε) * ((2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) / Real.log x ^ A) := by
      have gen : ∀ K W l : ℝ, l ≠ 0 → K * l⁻¹ * W = K * (W / l) := by
        intro K W l hl
        field_simp
      exact gen _ _ _ hLAne
    rw [e]
    have h1 : Real.log x ^ (4 : ℕ) ≤
        (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) / Real.log x ^ A := by
      rw [le_div_iff₀ hLA]
      linarith
    have e2 : 14 * x ^ (11 / 20 + ε) * (2 * Real.log x) ^ 4 =
        224 * x ^ (11 / 20 + ε) * Real.log x ^ (4 : ℕ) := by ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  refine hfin.trans ?_
  have hLn : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hlpos.le _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC224 hYpos.le) hLn

/-- P0069 page 51, display 5.17, the outer primes of the E4 sum. The sum over prime quadruples
is the sum over all integer quadruples weighted by the product of the four prime indicators. -/
theorem four_prime_filter_sum (I : Finset (ℕ × ℕ × ℕ × ℕ)) (R : ℕ × ℕ × ℕ × ℕ → Prop)
    [DecidablePred R]
    [DecidablePred (fun i : ℕ × ℕ × ℕ × ℕ =>
      i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ R i)]
    (Φ : ℕ × ℕ × ℕ × ℕ → ℝ) :
    ∑ i ∈ I.filter (fun i : ℕ × ℕ × ℕ × ℕ =>
        i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ R i), Φ i =
      ∑ i ∈ I.filter R, primeWeight i.1 * primeWeight i.2.1 * primeWeight i.2.2.1 *
        primeWeight i.2.2.2 * Φ i := by
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold primeWeight
  by_cases h1 : i.1.Prime <;> by_cases h2 : i.2.1.Prime <;> by_cases h3 : i.2.2.1.Prime <;>
    by_cases h4 : i.2.2.2.Prime <;> by_cases h5 : R i <;> simp [h1, h2, h3, h4, h5]

/-- P0069 page 51, display 5.17, "partial summation in `p1`, then `p2`, `p3` and `p4`": the
passage from four prime indicators to four densities `1 / log n` changes one variable at a
time. -/
theorem four_hybrid_telescope {ι : Type} (I : Finset ι) (p1 p2 p3 p4 l1 l2 l3 l4 Φ : ι → ℝ) :
    ∑ i ∈ I, p1 i * p2 i * p3 i * p4 i * Φ i - ∑ i ∈ I, l1 i * l2 i * l3 i * l4 i * Φ i =
      ∑ i ∈ I, (p1 i - l1 i) * p2 i * p3 i * p4 i * Φ i +
      ∑ i ∈ I, l1 i * (p2 i - l2 i) * p3 i * p4 i * Φ i +
      ∑ i ∈ I, l1 i * l2 i * (p3 i - l3 i) * p4 i * Φ i +
      ∑ i ∈ I, l1 i * l2 i * l3 i * (p4 i - l4 i) * Φ i := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- P0069 page 51, display 5.17, weight bookkeeping: the density `1 / log n` of the primes is
at most 2 at every natural number, with the convention `1 / 0 = 0` at `n = 0` and `n = 1`. -/
theorem four_inv_log_le_two (n : ℕ) : |1 / Real.log (n : ℝ)| ≤ 2 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have h0 : Real.log (n : ℝ) = 0 := by
      interval_cases n <;> simp
    rw [h0]
    norm_num
  · have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have hl : (1 / 2 : ℝ) < Real.log (n : ℝ) := by
      have h1 := Real.log_two_gt_d9
      have h3 := Real.log_le_log (by norm_num) h2
      linarith
    rw [abs_of_pos (by positivity), div_le_iff₀ (by linarith)]
    linarith

/-- LEAF: P0069 page 51, display 5.17, the E4 integral of page 51 with `1` replaced by `s` as
the limit of its Riemann sums on the grid of exponents. The integrand of `lowerFourDensityAt`,
with its cutoff written out, sampled at the exponents `β = log n / log Z` of the integer
quadruples `n1 > n2 > n3 > n4` with exponents in E4, each point weighted by the mesh
`1 / (n log Z)` of the grid in each variable, sums to the integral at `s = log m / log Z`, with
every log power saved. No prime number theorem is used; a power of `Z` is saved since every `n`
is at least `Z ^ (1 / 10)` and the integrand is Lipschitz off boundedly many hyperplanes: those
of E4, counted in `four_region_jumps`, and the hyperplane where `ω` jumps. The grid box of
`lowerFourDensityAt` contains E4. -/
theorem leaf_four_exponent_riemann (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          (if (Real.log (m : ℝ) / Real.log (scaleZ ε x) - expo ε x i.1 - expo ε x i.2.1 - expo ε x i.2.2.1 -
                expo ε x i.2.2.2) / expo ε x i.2.2.2 < 1 then 0
            else ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - expo ε x i.1 - expo ε x i.2.1 - expo ε x i.2.2.1 -
                expo ε x i.2.2.2) / expo ε x i.2.2.2) /
              (expo ε x i.1 * expo ε x i.2.1 * expo ε x i.2.2.1 * expo ε x i.2.2.2 ^ 2)) *
          (1 / ((i.1 : ℝ) * Real.log (scaleZ ε x)) * (1 / ((i.2.1 : ℝ) * Real.log (scaleZ ε x))) *
            (1 / ((i.2.2.1 : ℝ) * Real.log (scaleZ ε x))) * (1 / ((i.2.2.2 : ℝ) * Real.log (scaleZ ε x))))) -
        lowerFourDensityAt ω ε (Real.log (m : ℝ) / Real.log (scaleZ ε x))| ≤ C * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C0, hC0, hp⟩ := four_exponent_quadrature_power ω hω hz hε hε8
  obtain ⟨X, hX2, hX⟩ := four_exponent_power_absorbs_log A (1/100) C0 (by norm_num)
  refine ⟨max C0 X, fun x hx m hm1 hm2 => ?_⟩
  have hbound := (hp x ((le_max_left C0 X).trans hx) m hm1 hm2).trans
    (hX x ((le_max_right C0 X).trans hx))
  have hx2 : 2 ≤ x := hX2.trans ((le_max_right C0 X).trans hx)
  have hfinal := hbound.trans (le_mul_of_one_le_left
    (Real.rpow_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ x)) (-A))
    (by linarith [le_max_left C0 X] : (1 : ℝ) ≤ max C0 X))
  convert hfinal using 2
  congr 1
  unfold fourExponentMixed
  dsimp only
  refine Finset.sum_congr rfl fun i hi => ?_
  have hr := (Finset.mem_filter.mp hi).2.2.2.2
  simp only [fourExponentKernel, if_pos hr]


/-- P0069 page 51, display 5.17, the E4 sum at one point `m` of J after the prime number
theorem has been applied in each outer variable: the sum over the integer quadruples
`n1 > n2 > n3 > n4` with exponents in E4, each weighted by its density `1 / log n`, is
`1 / log Z` times the Riemann sum of `leaf_four_exponent_riemann`, term by term, since
`log n = β log Z` and `log (m / (n1 n2 n3 n4)) = (s - β1 - β2 - β3 - β4) log Z`; hence it is
`(1 / log Z)` times the E4 integral of page 51 with `1` replaced by `s`. The Riemann sum input
`leaf_four_exponent_riemann` is proved in this file. -/
theorem four_integer_riemann (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          1 / Real.log (i.1 : ℝ) * (1 / Real.log (i.2.1 : ℝ)) * (1 / Real.log (i.2.2.1 : ℝ)) * (1 / Real.log (i.2.2.2 : ℝ)) *
          (ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
              (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
            Real.log (i.2.2.2 : ℝ) /
              ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ)))) -
        lowerFourDensityAt ω ε (Real.log (m : ℝ) / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x)| ≤ C * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C, hC⟩ := leaf_four_exponent_riemann ω hω hz hε hε8 A hA
  refine ⟨max C 1, fun x hx m hm1 hm2 => ?_⟩
  have hxC : C ≤ x := (le_max_left _ _).trans hx
  have hx1 : (1 : ℝ) ≤ x := (le_max_right _ _).trans hx
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have hZ4 : (4 : ℝ) ≤ scaleZ ε x := by
    have h1 : (1 : ℝ) ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx1 (by linarith)
    unfold scaleZ shortY
    linarith
  have hlZ1 : 1 ≤ Real.log (scaleZ ε x) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlZ0 : 0 < Real.log (scaleZ ε x) := by linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.zero_le _).trans_lt hm1
  have hv : ∀ n : ℕ, 1 / 10 ≤ expo ε x n →
      (0 : ℝ) < (n : ℝ) ∧ Real.log (n : ℝ) = expo ε x n * Real.log (scaleZ ε x) ∧ 0 < expo ε x n := by
    intro n h
    have e : Real.log (n : ℝ) = expo ε x n * Real.log (scaleZ ε x) := by
      unfold expo
      rw [div_mul_cancel₀ _ hlZ0.ne']
    have hlog : 0 < Real.log (n : ℝ) := by
      rw [e]
      exact mul_pos (by linarith) hlZ0
    have hn : n ≠ 0 := by
      rintro rfl
      simp at hlog
    exact ⟨by exact_mod_cast Nat.pos_of_ne_zero hn, e, by linarith⟩
  have gen : ∀ W a b c d n1 n2 n3 n4 l : ℝ, a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 → n1 ≠ 0 → n2 ≠ 0 →
      n3 ≠ 0 → n4 ≠ 0 → l ≠ 0 →
      1 / (a * l) * (1 / (b * l)) * (1 / (c * l)) * (1 / (d * l)) *
          (W / (d * l) / (n1 * n2 * n3 * n4)) =
        W / (a * b * c * d ^ 2) *
          (1 / (n1 * l) * (1 / (n2 * l)) * (1 / (n3 * l)) * (1 / (n4 * l))) / l := by
    intro W a b c d n1 n2 n3 n4 l ha hb hc hd h1 h2 h3 h4 hl
    field_simp
  have key : ∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          1 / Real.log (i.1 : ℝ) * (1 / Real.log (i.2.1 : ℝ)) * (1 / Real.log (i.2.2.1 : ℝ)) * (1 / Real.log (i.2.2.2 : ℝ)) *
          (ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
              (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
            Real.log (i.2.2.2 : ℝ) /
              ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ))) =
      (∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          (if (Real.log (m : ℝ) / Real.log (scaleZ ε x) - expo ε x i.1 - expo ε x i.2.1 - expo ε x i.2.2.1 -
                expo ε x i.2.2.2) / expo ε x i.2.2.2 < 1 then 0
            else ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - expo ε x i.1 - expo ε x i.2.1 - expo ε x i.2.2.1 -
                expo ε x i.2.2.2) / expo ε x i.2.2.2) /
              (expo ε x i.1 * expo ε x i.2.1 * expo ε x i.2.2.1 * expo ε x i.2.2.2 ^ 2)) *
          (1 / ((i.1 : ℝ) * Real.log (scaleZ ε x)) * (1 / ((i.2.1 : ℝ) * Real.log (scaleZ ε x))) *
            (1 / ((i.2.2.1 : ℝ) * Real.log (scaleZ ε x))) * (1 / ((i.2.2.2 : ℝ) * Real.log (scaleZ ε x))))) / Real.log (scaleZ ε x) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨-, -, -, -, hR⟩ := Finset.mem_filter.mp hi
    obtain ⟨hd, hdc, hcb, hba, -, -⟩ := Decomp514a.four_density_region_box hε hε8 hR
    obtain ⟨p1, l1, q1⟩ := hv i.1 (by linarith)
    obtain ⟨p2, l2, q2⟩ := hv i.2.1 (by linarith)
    obtain ⟨p3, l3, q3⟩ := hv i.2.2.1 (by linarith)
    obtain ⟨p4, l4, q4⟩ := hv i.2.2.2 (by linarith)
    have hlogq : Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
        (i.2.2.2 : ℝ))) =
        (Real.log (m : ℝ) / Real.log (scaleZ ε x) - expo ε x i.1 - expo ε x i.2.1 - expo ε x i.2.2.1 -
          expo ε x i.2.2.2) * Real.log (scaleZ ε x) := by
      rw [Real.log_div hm0.ne' (by positivity), Real.log_mul (by positivity) p4.ne',
        Real.log_mul (by positivity) p3.ne', Real.log_mul p1.ne' p2.ne', l1, l2, l3, l4]
      field_simp
      ring
    have hu : Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
        (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ) =
        (Real.log (m : ℝ) / Real.log (scaleZ ε x) - expo ε x i.1 - expo ε x i.2.1 - expo ε x i.2.2.1 -
                expo ε x i.2.2.2) / expo ε x i.2.2.2 := by
      rw [hlogq, l4, mul_div_mul_right _ _ hlZ0.ne']
    rw [hu, l1, l2, l3, l4]
    by_cases hlt : (Real.log (m : ℝ) / Real.log (scaleZ ε x) - expo ε x i.1 - expo ε x i.2.1 - expo ε x i.2.2.1 -
                expo ε x i.2.2.2) / expo ε x i.2.2.2 < 1
    · rw [if_pos hlt, hz _ hlt]
      simp
    · rw [if_neg hlt]
      exact gen _ _ _ _ _ _ _ _ _ _ q1.ne' q2.ne' q3.ne' q4.ne' p1.ne' p2.ne' p3.ne' p4.ne'
        hlZ0.ne'
  rw [key, ← sub_div, abs_div, abs_of_pos hlZ0]
  have h := hC x hxC m hm1 hm2
  calc _ ≤ |(∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          (if (Real.log (m : ℝ) / Real.log (scaleZ ε x) - expo ε x i.1 - expo ε x i.2.1 - expo ε x i.2.2.1 -
                expo ε x i.2.2.2) / expo ε x i.2.2.2 < 1 then 0
            else ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - expo ε x i.1 - expo ε x i.2.1 - expo ε x i.2.2.1 -
                expo ε x i.2.2.2) / expo ε x i.2.2.2) /
              (expo ε x i.1 * expo ε x i.2.1 * expo ε x i.2.2.1 * expo ε x i.2.2.2 ^ 2)) *
          (1 / ((i.1 : ℝ) * Real.log (scaleZ ε x)) * (1 / ((i.2.1 : ℝ) * Real.log (scaleZ ε x))) *
            (1 / ((i.2.2.1 : ℝ) * Real.log (scaleZ ε x))) * (1 / ((i.2.2.2 : ℝ) * Real.log (scaleZ ε x))))) -
        lowerFourDensityAt ω ε (Real.log (m : ℝ) / Real.log (scaleZ ε x))| := div_le_self (abs_nonneg _) hlZ1
    _ ≤ C * Real.log x ^ (-A) := h
    _ ≤ max C 1 * Real.log x ^ (-A) := mul_le_mul_of_nonneg_right (le_max_left _ _) hL

/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number theorem",
the outer primes `p1`, `p2`, `p3`, `p4` of the E4 sum reached from display 5.15, at one point
`m` of J. The sum over the prime quadruples with exponents in E4 of
`ω(log (m / (p1 p2 p3 p4)) / log p4) / log p4` weighted by `1 / (p1 p2 p3 p4)` is
`(1 / log Z)` times the E4 integral of page 51 with `1` replaced by `s`, at `m = Z^s`, with
every log power saved. Partial summation in `p1`, `p2`, `p3`, `p4` is `four_transfer_p1` to
`four_transfer_p4` of `FourDensityMain517a.lean`, proved from the prime number theorem.
The Riemann sum input `leaf_four_exponent_riemann` is proved in this file. -/
theorem four_quad_density_pointwise (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
              (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
            Real.log (i.2.2.2 : ℝ) /
              ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ))) -
        lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x)| ≤ C * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, h1⟩ := four_transfer_p1 ω hω hz hε hε8 A hA
  obtain ⟨C2, h2⟩ := four_transfer_p2 ω hω hz hε hε8 A hA
  obtain ⟨C3, h3⟩ := four_transfer_p3 ω hω hz hε hε8 A hA
  obtain ⟨C4, h4⟩ := four_transfer_p4 ω hω hz hε hε8 A hA
  obtain ⟨C5, h5⟩ := four_integer_riemann ω hω hz hε hε8 A hA
  refine ⟨max (max (max C1 C2) (max C3 C4)) (max C5 (|C1| + |C2| + |C3| + |C4| + |C5| + 1)),
    fun x hx m hm1 hm2 => ?_⟩
  have hx1 : C1 ≤ x :=
    (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hx))
  have hx2 : C2 ≤ x :=
    (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hx))
  have hx3 : C3 ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hx))
  have hx4 : C4 ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hx))
  have hx5 : C5 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hC6 : |C1| + |C2| + |C3| + |C4| + |C5| + 1 ≤
      max (max (max C1 C2) (max C3 C4)) (max C5 (|C1| + |C2| + |C3| + |C4| + |C5| + 1)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hxone : (1 : ℝ) ≤ x := by
    have := abs_nonneg C1
    have := abs_nonneg C2
    have := abs_nonneg C3
    have := abs_nonneg C4
    have := abs_nonneg C5
    linarith
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hxone) _
  have pw2 : ∀ n : ℕ, |primeWeight n| ≤ 2 := fun n => by
    unfold primeWeight
    split_ifs <;> norm_num
  have e1 := h1 x hx1 m hm1 hm2 primeWeight primeWeight primeWeight pw2 pw2 pw2
  have e2 := h2 x hx2 m hm1 hm2 (fun n : ℕ => 1 / Real.log (n : ℝ)) primeWeight primeWeight
    four_inv_log_le_two pw2 pw2
  have e3 := h3 x hx3 m hm1 hm2 (fun n : ℕ => 1 / Real.log (n : ℝ))
    (fun n : ℕ => 1 / Real.log (n : ℝ)) primeWeight four_inv_log_le_two four_inv_log_le_two pw2
  have e4 := h4 x hx4 m hm1 hm2 (fun n : ℕ => 1 / Real.log (n : ℝ))
    (fun n : ℕ => 1 / Real.log (n : ℝ)) (fun n : ℕ => 1 / Real.log (n : ℝ))
    four_inv_log_le_two four_inv_log_le_two four_inv_log_le_two
  have e5 := h5 x hx5 m hm1 hm2
  have tel := four_hybrid_telescope
    (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)))
    (fun i : ℕ × ℕ × ℕ × ℕ => primeWeight i.1)
    (fun i : ℕ × ℕ × ℕ × ℕ => primeWeight i.2.1)
    (fun i : ℕ × ℕ × ℕ × ℕ => primeWeight i.2.2.1)
    (fun i : ℕ × ℕ × ℕ × ℕ => primeWeight i.2.2.2)
    (fun i : ℕ × ℕ × ℕ × ℕ => 1 / Real.log (i.1 : ℝ))
    (fun i : ℕ × ℕ × ℕ × ℕ => 1 / Real.log (i.2.1 : ℝ))
    (fun i : ℕ × ℕ × ℕ × ℕ => 1 / Real.log (i.2.2.1 : ℝ))
    (fun i : ℕ × ℕ × ℕ × ℕ => 1 / Real.log (i.2.2.2 : ℝ))
    (fun i : ℕ × ℕ × ℕ × ℕ => (ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
              (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
            Real.log (i.2.2.2 : ℝ) /
              ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ))))
  rw [four_prime_filter_sum]
  have b1 := (abs_le.mp e1)
  have b2 := (abs_le.mp e2)
  have b3 := (abs_le.mp e3)
  have b4 := (abs_le.mp e4)
  have b5 := (abs_le.mp e5)
  have c1 := mul_le_mul_of_nonneg_right (le_abs_self C1) hL
  have c2 := mul_le_mul_of_nonneg_right (le_abs_self C2) hL
  have c3 := mul_le_mul_of_nonneg_right (le_abs_self C3) hL
  have c4 := mul_le_mul_of_nonneg_right (le_abs_self C4) hL
  have c5 := mul_le_mul_of_nonneg_right (le_abs_self C5) hL
  have c6 := mul_le_mul_of_nonneg_right hC6 hL
  have c7 : (|C1| + |C2| + |C3| + |C4| + |C5| + 1) * Real.log x ^ (-A) =
      |C1| * Real.log x ^ (-A) + |C2| * Real.log x ^ (-A) + |C3| * Real.log x ^ (-A) +
        |C4| * Real.log x ^ (-A) + |C5| * Real.log x ^ (-A) + Real.log x ^ (-A) := by ring
  rw [abs_le]
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2]

/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number theorem",
applied to the outer primes `p1`, `p2`, `p3`, `p4` of the E4 sum reached from display 5.15: the
statement of `leaf_four_density_main`. With the rough cofactor `n5 = m / (p1 p2 p3 p4)`
replaced by its Buchstab density at level `p4`, the sum over prime quadruples with exponents in
E4 has local density the E4 integral of page 51 with `1` replaced by `s`, over `log Z`, at
`m = Z^s`, with every log power saved on every prefix of J. The Riemann sum input
`leaf_four_exponent_riemann` is proved in this file. -/
theorem four_density_main (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ U : ℕ, U ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ U,
        ((∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
              i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
                i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
                lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                  (expo ε x i.2.2.2)),
            if i.1 * i.2.1 * i.2.2.1 * i.2.2.2 ∣ m then
              ω (Real.log ((m / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2) : ℕ) : ℝ) /
                  Real.log (i.2.2.2 : ℝ)) / Real.log (i.2.2.2 : ℝ)
            else 0) -
          lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨CA, hCA⟩ := four_quad_density_pointwise ω hω hz hε hε8 A hA
  obtain ⟨CB, hCB⟩ := four_cofactor_riemann ω hω hz hε hε8 A hA
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
  have hmain := four_density_swap_combine
    (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
      (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
      (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
      (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
      i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
        i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
        lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
          (expo ε x i.2.2.2)))
    (fun i : ℕ × ℕ × ℕ × ℕ => i.1 * i.2.1 * i.2.2.1 * i.2.2.2)
    (fun i hi => by
      obtain ⟨-, hp1, hp2, hp3, hp4, -⟩ := Finset.mem_filter.mp hi
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp1.pos hp2.pos) hp3.pos) hp4.pos)
    (fun (i : ℕ × ℕ × ℕ × ℕ) (n : ℕ) =>
      ω (Real.log (n : ℝ) / Real.log (i.2.2.2 : ℝ)) / Real.log (i.2.2.2 : ℝ))
    (fun (i : ℕ × ℕ × ℕ × ℕ) (m : ℕ) =>
      ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
          (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
        Real.log (i.2.2.2 : ℝ) /
          ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ)))
    (fun m : ℕ => lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
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

#print axioms four_cofactor_riemann
#print axioms leaf_four_exponent_riemann
#print axioms four_integer_riemann
#print axioms four_quad_density_pointwise
#print axioms four_density_main

end LeanLab.BHP1997.LowerShortC165
