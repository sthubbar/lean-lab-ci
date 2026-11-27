/-
LEAF for the grid certificate of BJS Lemma 7 for even n, Bordignon, Johnston and Starichkova,
arXiv 2207.09452v6, papers/P0009.pdf, Section 2.2, last paragraph, page 8, with displays 15,
16, 17 and 21 and c_n of Table 2. The paper bounds f_n on a grid recursively: an upper bound for
f_1, then for n ≥ 2 the left Riemann sum of display 21 applied to upper bounds of f_(n-1), and
it compares the results with 2 e ^ 2 c_n ^ (n - 1) h(x + 1 / 1000) at x = 2 + i / 1000.
Here the Riemann step is 1 / 10000 in place of the paper's 1 / 1000: a float run of the minimal
table with step 1 / 1000 misses the target, see notes/burst-20261124/Cai2002-S9-12-grid-cert.md.
The analytic part, that every such table bounds f_n on the grid, is
grid_table_bound_fine1122e of Split1122bLemma7.lean, PROVED there, and it proves
lemma7_grid_even1122 from this LEAF. The odd case is not split: its statement is suspected
false at n = 33, i = 0, see the same note.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split306Theorem6

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-- LEAF: BJS Section 2.2, last paragraph, page 8, the numerical grid certificate for even n,
Riemann step 1 / 10000: there is a table U n k ≥ 0, x = k / 10000, with
* U 1 k ≥ (3 - x) / x for 1 ≤ x ≤ 3, display 15;
* for 2 ≤ n ≤ 500, x ≥ 1 for odd n, x ≥ 2 for even n, x < n + 2: the Riemann sum of display 21
  with step 1 / 10000 from σ = max(x, 3) for odd n, display 17, and σ = x for even n,
  display 16, of the values U (n - 1), divided by x, is at most U n k;
* for even 4 ≤ n ≤ 500 and x = j / 1000 with 2 ≤ x < n + 2,
  U n (10 j) ≤ 2 e ^ 2 c_n ^ (n - 1) h(x + 1 / 1000), Table 2.
Float check: the minimal table meets the last item with ratio at least 1.002 for every even n,
notes/burst-20261124/Cai2002-S9-12-scripts/grid10.py.
Class HARD: about 500 by 5000000 grid values. -/
theorem lemma7_grid_cert_even1122e : ∃ U : ℕ → ℕ → ℝ,
    (∀ n k, 0 ≤ U n k) ∧
    (∀ k : ℕ, 10000 ≤ k → k ≤ 30000 → (3 - (k : ℝ) / 10000) / ((k : ℝ) / 10000) ≤ U 1 k) ∧
    (∀ n, 2 ≤ n → n ≤ 500 → ∀ k : ℕ, ((Odd n ∧ 10000 ≤ k) ∨ (Even n ∧ 20000 ≤ k)) →
      k < 10000 * (n + 2) →
      (∑ i ∈ range (10000 * (n + 3)),
        U (n - 1) ((if Odd n then max k 30000 else k) + i - 10000)) / (k : ℝ) ≤ U n k) ∧
    (∀ n, 4 ≤ n → n ≤ 500 → Even n → ∀ j : ℕ, 2000 ≤ j → j < 1000 * (n + 2) →
      U n (10 * j) ≤ 2 * exp 2 * bjsC306 n ^ (n - 1) *
        LeanLab.ChenExplicit.hSieve (((j : ℝ) + 1) / 1000)) := by
  sorry

end LeanLab.Cai2002
