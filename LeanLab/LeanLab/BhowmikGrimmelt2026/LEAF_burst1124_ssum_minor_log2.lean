/-
Split of `split_leaf_ssum_minor_log2` of SPLIT_minor_bare_family328, burst-20261124 unit S9-27.
P0029 page 16, Proposition 4.1, display 4.8, and page 14 display 4.3 for the major arcs.

The minor arc partial sum bound at logarithm power two follows the route of the proved power
four bound `minor_partial_sum261`: Dirichlet approximation on a minor arc gives a reduced
fraction a over q with R below q at most X over R, by the proved `minor_dirichlet84`; then
display 4.8 at length m. Here:

* `leaf_vaughan_log2_feed1124`: display 4.8 for denominators q at most the length, with the
  logarithm power two in place of the printed power four. HARD. This is the folder QUESTION 2
  input: P0029 prints power four only, and the lab proves power four in
  `vaughan_small_denominator84` from the PNTPort port of Vaughan's argument.
* `vaughan_large_log2_feed1124`: the case q at least the length, PROVED, from the trivial
  bound `ssum_log_bound84`, since the square root of N q is then at least N.
* `ssum_minor_log2_from_leaves`: the exact statement of `split_leaf_ssum_minor_log2`, PROVED
  from the leaf and the two proved pieces.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Minor84

namespace LeanLab.BhowmikGrimmelt2026

open ArithmeticFunction

/-- LEAF: P0029 page 16, Proposition 4.1, display 4.8, for denominators q at most the length N,
with the logarithm power two in place of the printed power four. Class HARD. There is a
nonnegative C such that for every N at least two, every reduced fraction a over q with q from
one to N and the absolute value of alpha minus a over q below one over q squared, the modulus of
S of length N at alpha is at most C times the sum of N over the square root of q, N to the four
fifths and the square root of N q, times log N squared. This is the sufficient input recorded
as folder QUESTION 2: the printed display 4.8 has power four, which the lab proves as
`vaughan_small_denominator84`; power two is not printed in P0029. -/
theorem leaf_vaughan_log2_feed1124 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N q : ℕ), 2 ≤ N → 1 ≤ q → q ≤ N → ∀ (a : ℤ), Int.gcd a q = 1 →
      ∀ α : ℝ, |α - a / q| < 1 / (q : ℝ) ^ 2 →
        ‖Ssum N α‖ ≤ C * (N / Real.sqrt q + (N : ℝ) ^ (4 / 5 : ℝ) + Real.sqrt (N * q)) *
          Real.log N ^ 2 := by
  sorry

/-- PROVED. P0029 page 16, display 4.8 in the trivial range: for q at least the length N the
term the square root of N q is at least N, and the trivial bound N log N of
`ssum_log_bound84` is at most two N times log N squared, as log N is at least one half. -/
theorem vaughan_large_log2_feed1124 {N q : ℕ} (hN : 2 ≤ N) (hqN : N ≤ q) (α : ℝ) :
    ‖Ssum N α‖ ≤ 2 * (N / Real.sqrt q + (N : ℝ) ^ (4 / 5 : ℝ) + Real.sqrt (N * q)) *
      Real.log N ^ 2 := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNq : (N : ℝ) ≤ q := by exact_mod_cast hqN
  have hhalf : (1 / 2 : ℝ) ≤ Real.log N := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ N by exact_mod_cast hN)
    linarith [Real.log_two_gt_d9]
  have hlog : Real.log N ≤ 2 * Real.log N ^ 2 := by nlinarith
  have hs : (N : ℝ) ≤ Real.sqrt (N * q) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [mul_le_mul_of_nonneg_left hNq hN0])
  have hNB : (N : ℝ) ≤ N / Real.sqrt q + (N : ℝ) ^ (4 / 5 : ℝ) + Real.sqrt (N * q) := by
    have h1 : 0 ≤ (N : ℝ) / Real.sqrt q := by positivity
    have h2 : 0 ≤ (N : ℝ) ^ (4 / 5 : ℝ) := by positivity
    linarith
  calc
    _ ≤ N * Real.log N := ssum_log_bound84 N α
    _ ≤ N * (2 * Real.log N ^ 2) := mul_le_mul_of_nonneg_left hlog hN0
    _ = 2 * N * Real.log N ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hNB (by norm_num)) (by positivity)

/-- The exact statement of `split_leaf_ssum_minor_log2`, PROVED from the leaf
`leaf_vaughan_log2_feed1124`, the proved trivial range `vaughan_large_log2_feed1124`
and the proved Dirichlet step `minor_dirichlet84`, along the route of `minor_partial_sum261`. -/
theorem ssum_minor_log2_from_leaves :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ), 2 ≤ X → ∀ R : ℝ, 1 ≤ R → R ≤ X →
      ∀ (m : ℕ), m ≤ X → ∀ α : ℝ, ¬ MajorArc X R α →
        ‖Ssum m α‖ ≤ C * ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) *
          Real.log X ^ 2 := by
  obtain ⟨C₀, hC₀, h₀⟩ := leaf_vaughan_log2_feed1124
  refine ⟨2 * (C₀ + 2), by positivity, ?_⟩
  intro X hX R hR hRX m hm α hminor
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hR0 : 0 < R := by linarith
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
  by_cases hm2 : 2 ≤ m
  · have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hmX : (m : ℝ) ≤ X := by exact_mod_cast hm
    obtain ⟨a, q, hq, hcop, hRq, hqR, happ⟩ := minor_dirichlet84 hX0 hR0 hRX hminor
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR0
    have hsR2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR0.le
    have hfirst : (m : ℝ) / Real.sqrt q ≤ (X : ℝ) / Real.sqrt R :=
      (div_le_div_of_nonneg_right hmX (Real.sqrt_nonneg _)).trans
        (div_le_div_of_nonneg_left hX0.le hsR (Real.sqrt_le_sqrt hRq.le))
    have hlast : Real.sqrt ((m : ℝ) * q) ≤ (X : ℝ) / Real.sqrt R := by
      have hprod : (m : ℝ) * q ≤ ((X : ℝ) / Real.sqrt R) ^ 2 := by
        have hqr : (q : ℝ) * R ≤ X := (le_div_iff₀ hR0).mp hqR
        rw [div_pow, hsR2, le_div_iff₀ hR0]
        nlinarith [mul_le_mul_of_nonneg_left hqr hX0.le,
          mul_le_mul_of_nonneg_right hmX (mul_nonneg hq0.le hR0.le)]
      exact (Real.sqrt_le_sqrt hprod).trans_eq (Real.sqrt_sq (by positivity))
    have hexplicit : ‖Ssum m α‖ ≤ (C₀ + 2) * ((m : ℝ) / Real.sqrt q +
        (m : ℝ) ^ (4 / 5 : ℝ) + Real.sqrt ((m : ℝ) * q)) * Real.log m ^ 2 := by
      have hB : 0 ≤ ((m : ℝ) / Real.sqrt q + (m : ℝ) ^ (4 / 5 : ℝ) +
          Real.sqrt ((m : ℝ) * q)) * Real.log m ^ 2 := by positivity
      rcases le_total q m with hqm | hmq
      · have := h₀ m q hm2 hq hqm a hcop α happ
        nlinarith
      · have := vaughan_large_log2_feed1124 hm2 hmq α
        nlinarith
    have hpow : (m : ℝ) ^ (4 / 5 : ℝ) ≤ (X : ℝ) ^ (4 / 5 : ℝ) :=
      Real.rpow_le_rpow hm0.le hmX (by norm_num)
    have hlog : Real.log (m : ℝ) ^ 2 ≤ Real.log X ^ 2 :=
      pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m)))
        (Real.log_le_log hm0 hmX) 2
    calc
      _ ≤ (C₀ + 2) * ((m : ℝ) / Real.sqrt q + (m : ℝ) ^ (4 / 5 : ℝ) +
          Real.sqrt ((m : ℝ) * q)) * Real.log m ^ 2 := hexplicit
      _ ≤ (C₀ + 2) * (2 * ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ))) *
          Real.log X ^ 2 := by
        apply mul_le_mul _ hlog (by positivity) (by positivity)
        have hXp : 0 ≤ (X : ℝ) ^ (4 / 5 : ℝ) := by positivity
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      _ = _ := by ring
  · have hm01 : m = 0 ∨ m = 1 := by omega
    rcases hm01 with rfl | rfl <;> norm_num [Ssum] <;> positivity

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.leaf_vaughan_log2_feed1124
#print axioms LeanLab.BhowmikGrimmelt2026.vaughan_large_log2_feed1124
#print axioms LeanLab.BhowmikGrimmelt2026.ssum_minor_log2_from_leaves
