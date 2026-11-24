/-
AI wrote the Lean code. Claude, session S88, burst-20261122, OMOS FEED.
Yamada 2015, Explicit Chen's theorem, arXiv 1511.03409v2, Section 5, proof of Theorem 5.1,
eqs 56 to 83, printed pages 13 to 18.
Split of `Yamada.thm51_leaf1` of DecompJ201 into two LEAFs:
* `eq69_lower`: the sieve lower bound eq 69 after Lemmas 5.2 and 5.3, with eqs 65, 68,
  70 to 77 and 80 to 83 inserted;
* `eq79_bound`: eq 79, the second line of eq 69 against V(z), from Lemma 2.2 eq 78 and eqs 63, 64.
Here V(z) is written out as the product of eq 43 at j = 0, and Yamada's lower sieve function
is f₁(s) = s - 2e^γ log(s - 1) on 2 ≤ s ≤ 4, from eq 41 with f₁(2) = 2.
`thm51_leaf1_of_leaves` has exactly the statement of `thm51_leaf1` and no sorry of its own;
it is CONDITIONAL ON the two LEAFs. Chen's theorem is known; binary Goldbach is OPEN.
-/
import LeanLab.ChenExplicit.DecompJ201

open Finset Real
open scoped Classical

namespace LeanLab.ChenExplicit.SplitJ201T51
open LeanLab.ChenExplicit LeanLab.ChenExplicit.Yamada

/-- LEAF: Yamada 2015, eq 69 on page 16, from Lemma 5.2 eq 57, Lemma 5.3 eqs 59 to 62, eq 65 and
eq 68, with the first line of eq 69 evaluated by eqs 70 to 77 on pages 16 and 17 and the third
and fourth lines by eqs 80 to 83 on page 18. With `D, s₁` of eqs 63 and 64 and `u = U_N^(1)`,
eq 44 at `j = 1`, which lies between `U_N` and `U_N (1 + ε₀(N))` by eq 46:
`S(A, P(z)) > |A| V(z) - |A| u (f₁(s₁)/log D + 255.84406/log^{3/2} D)
 - U_N |A| ε₀ (0.3465/log N + 1790.6648/log^{3/2} N) - 10⁻⁶ U_N |A| / log^{3/2} N`.
The last term absorbs the `e^{-27}` term of eq 77 and the `e^{-23}` term of eq 68,
through `|A| > N/log N`, eq 48, and eq 43. Class HARD. -/
theorem eq69_lower (N : ℕ) (hEven : Even N) (hN : exp (exp 36) < (N : ℝ)) :
    ∃ D s u : ℝ,
      4 - 8 * (32 * log (log (N : ℝ)) + 50) / log (N : ℝ) < s ∧ s ≤ 4 ∧
      log D = s * log (zN N) ∧ U N ≤ u ∧ u ≤ U N * (1 + eps0 N) ∧
      (Acard N : ℝ) * (∏ p ∈ (range ⌈zN N⌉₊).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N),
          (1 - 1 / ((p : ℝ) - 1))) -
        (Acard N : ℝ) * u * ((s - 2 * exp eulerMascheroniConstant * log (s - 1)) / log D +
          25584406 / 100000 / (log D * √(log D))) -
        U N * Acard N * eps0 N * (3465 / 10000 / log (N : ℝ) +
          17906648 / 10000 / (log (N : ℝ) * √(log (N : ℝ)))) -
        U N * Acard N / (10 ^ 6 * (log (N : ℝ) * √(log (N : ℝ)))) < (SA N (zN N) : ℝ) := by
  sorry

/-- LEAF: Yamada 2015, eq 79 on pages 17 and 18, from Lemma 2.2 in the form eq 78 and the ranges
eqs 63 and 64: for every `D, s` with `log D = s log z` and `s` in the range of eq 64, and every
`u` between `U_N` and `U_N (1 + ε₀(N))`, `u (f₁(s)/log D + 255.84406/log^{3/2} D) < V(z) +
U_N (-(4e^γ log 3 - 0.1733 ε₀(N))/log N + 736.33192/log^{3/2} N)`. The main terms cancel since
`2 f₁(4) = 8 - 4e^γ log 3`; the bound holds by the margin `736.33192 - 255.84406 · 2^{3/2} (1 + 1/57)`,
about `0.0009`, against second order terms of size `log^{-2} N`. Class HARD. -/
theorem eq79_bound (N : ℕ) (hEven : Even N) (hN : exp (exp 36) < (N : ℝ)) (D s u : ℝ)
    (hs : 4 - 8 * (32 * log (log (N : ℝ)) + 50) / log (N : ℝ) < s) (hs4 : s ≤ 4)
    (hD : log D = s * log (zN N)) (hu : U N ≤ u) (hu1 : u ≤ U N * (1 + eps0 N)) :
    u * ((s - 2 * exp eulerMascheroniConstant * log (s - 1)) / log D +
        25584406 / 100000 / (log D * √(log D))) <
      (∏ p ∈ (range ⌈zN N⌉₊).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N),
          (1 - 1 / ((p : ℝ) - 1))) +
        U N * (-(4 * exp eulerMascheroniConstant * log 3 - 1733 / 10000 * eps0 N) /
          log (N : ℝ) + 73633192 / 100000 / (log (N : ℝ) * √(log (N : ℝ)))) := by
  sorry

/-- Exact statement of `Yamada.thm51_leaf1`, Theorem 5.1 eq 56 in the lab's form.
CONDITIONAL ON `eq69_lower` and `eq79_bound`. -/
theorem thm51_leaf1_of_leaves (N : ℕ) (hEven : Even N) (hN : exp (exp 36) < (N : ℝ)) :
    U N * Acard N / log (N : ℝ) * (4 * exp eulerMascheroniConstant * log 3) < (SA N (zN N) : ℝ) +
    U N * Acard N / log (N : ℝ) * (5198 / 10000 * eps0 N + 7677471 / 10000 / √(log (N : ℝ))) := by
  obtain ⟨D, s, u, hs, hs4, hD, hu, hu1, hA⟩ := eq69_lower N hEven hN
  have hB := eq79_bound N hEven hN D s u hs hs4 hD hu hu1
  set V := ∏ p ∈ (range ⌈zN N⌉₊).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N),
    (1 - 1 / ((p : ℝ) - 1)) with hV
  set L := log (N : ℝ) with hL
  set c := 4 * exp eulerMascheroniConstant * log 3 with hc
  set X := (s - 2 * exp eulerMascheroniConstant * log (s - 1)) / log D +
    25584406 / 100000 / (log D * √(log D)) with hX
  set a : ℝ := (Acard N : ℝ) with ha
  set e := eps0 N with he
  have hLpos : 0 < L := by
    have h1 : exp 36 < L := by
      rw [hL]; simpa using log_lt_log (exp_pos _) hN
    linarith [exp_pos (36 : ℝ)]
  have hsq : 0 < √L := sqrt_pos.mpr hLpos
  have hLL : 0 < L * √L := mul_pos hLpos hsq
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  have hU : 0 ≤ U N := le_trans (by norm_num) (U_ge N)
  have he0 : 0 ≤ e := by
    rw [he]; unfold eps0; positivity
  have he1 : e ≤ 1 / 57 := by
    rw [he]; unfold eps0
    exact one_div_le_one_div_of_le (by norm_num) (le_max_left _ _)
  have hUa : 0 ≤ U N * a := mul_nonneg hU ha0
  -- from eq 79, times |A|
  have hB' : a * u * X ≤ a * (V + U N * (-(c - 1733 / 10000 * e) / L +
      73633192 / 100000 / (L * √L))) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hB.le ha0
  -- the remaining error terms fit 767.7471
  have hk : U N * a * (73633192 / 100000 + 17906648 / 10000 * e + 1 / 10 ^ 6) ≤
      U N * a * (7677471 / 10000) := by
    apply mul_le_mul_of_nonneg_left _ hUa
    nlinarith
  have key : U N * a / L * c - U N * a / L * (5198 / 10000 * e + 7677471 / 10000 / √L) ≤
      a * V - a * (V + U N * (-(c - 1733 / 10000 * e) / L + 73633192 / 100000 / (L * √L))) -
        U N * a * e * (3465 / 10000 / L + 17906648 / 10000 / (L * √L)) -
        U N * a / (10 ^ 6 * (L * √L)) := by
    have hdiff : (a * V - a * (V + U N * (-(c - 1733 / 10000 * e) / L +
          73633192 / 100000 / (L * √L))) -
        U N * a * e * (3465 / 10000 / L + 17906648 / 10000 / (L * √L)) -
        U N * a / (10 ^ 6 * (L * √L))) -
        (U N * a / L * c - U N * a / L * (5198 / 10000 * e + 7677471 / 10000 / √L)) =
        (U N * a * (7677471 / 10000) -
          U N * a * (73633192 / 100000 + 17906648 / 10000 * e + 1 / 10 ^ 6)) / (L * √L) := by
      field_simp
      ring
    have hnn : 0 ≤ (U N * a * (7677471 / 10000) -
          U N * a * (73633192 / 100000 + 17906648 / 10000 * e + 1 / 10 ^ 6)) / (L * √L) :=
      div_nonneg (by linarith) hLL.le
    linarith
  linarith
end LeanLab.ChenExplicit.SplitJ201T51
