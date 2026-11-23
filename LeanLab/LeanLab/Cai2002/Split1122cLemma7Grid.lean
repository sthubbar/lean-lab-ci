/-
Proved pieces of the method of BJS Section 2.2, last paragraph, page 8, of Bordignon,
Johnston and Starichkova, arXiv 2207.09452v6, papers/P0009.pdf, for the grid LEAFs
lemma7_grid_odd1122 and lemma7_grid_even1122 of Split1122bLemma7.lean.
The paper bounds f_n at grid points recursively: f_n(x) is 1 / x times the integral of
f_(n-1)(t - 1) over (σ, ∞), display 16 or 17, and the integral is at most the left
Riemann sum of display 21 with step 1 / 1000. On the single grid x_k = 1 + k / 1000:
* grid_step1122c: one step of that recursion, from displays 16, 17 and 21; for even n it
  uses display 16 with σ = x_k, not the sharper display 20.
* grid_base1122c: display 19 on the grid.
* grid_le_table1122c: any table with U_2 from display 19 and the recursion of
  grid_step1122c bounds f_n at every grid point of its parity domain.
* table_exists1122c: such a table exists.
No LEAF is added. The certificate itself is not stated: S77 found that display 18 with
Table 2 fails at n = 33, s = 1, so lemma7_grid_odd1122 at n = 33, i = 0 is suspected
FALSE; see notes/burst-20261122/Cai2002-lemma7grid.md.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122bLemma7

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-- The starting grid index of the Riemann sum of display 21 for level n at the grid point
x_k = 1 + k / 1000, read on the level n - 1 grid: σ - 1 with σ = max(3, x_k) for odd n,
display 17, and σ = x_k for even n, display 16. -/
theorem grid_cast1122c (a j : ℕ) (ha : 1000 ≤ a) :
    (1 : ℝ) + ((a : ℝ) / 1000) + (j : ℝ) / 1000 - 1 = 1 + ((a - 1000 + j : ℕ) : ℝ) / 1000 := by
  rw [Nat.cast_add, Nat.cast_sub ha]
  push_cast
  ring

/-- One step of the recursion of BJS Section 2.2, page 8: for 3 ≤ n, at the grid point
x_k = 1 + k / 1000, with k ≥ 1000 when n is even, f_n(x_k) is at most 1 / x_k times the
left Riemann sum with step 1 / 1000 of f_(n-1) on the grid, starting at σ - 1 where
σ = max(3, x_k) for odd n by display 17 and σ = x_k for even n by display 16, with the
Riemann bound of display 21. -/
theorem grid_step1122c (n : ℕ) (hn3 : 3 ≤ n) (k : ℕ) (hk : Odd n ∨ 1000 ≤ k) :
    bjsF306 n (1 + (k : ℝ) / 1000) ≤
      (∑ j ∈ range (1000 * (n + 2)),
        bjsF306 (n - 1)
          (1 + (((if Odd n then max k 2000 else k) - 1000 + j : ℕ) : ℝ) / 1000) / 1000) /
        (1 + (k : ℝ) / 1000) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm1 : 1 ≤ m + 1 := by omega
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hx : (0 : ℝ) < 1 + (k : ℝ) / 1000 := by positivity
  have hsub : m + 2 - 1 = m + 1 := by omega
  rw [hsub]
  have hNc : ((1000 * (m + 2 + 2) : ℕ) : ℝ) / 1000 = (m : ℝ) + 4 := by push_cast; ring
  by_cases hodd : Odd (m + 2)
  · have hev : Even (m + 1) := by
      rcases hodd with ⟨r, hr⟩; exact ⟨r, by omega⟩
    simp only [hodd, ite_true]
    by_cases hs3 : 1 + (k : ℝ) / 1000 ≤ 3
    · have hk2 : k ≤ 2000 := by
        have : (k : ℝ) ≤ 2000 := by linarith
        exact_mod_cast this
      have hmax : max k 2000 = 2000 := max_eq_right hk2
      rw [hmax]
      simp only [bjsF306, hodd, hs3, and_self, ite_true]
      apply div_le_div_of_nonneg_right _ hx.le
      have hR := riemann21_fn1122 (m + 1) hm1 3 (1000 * (m + 2 + 2))
        (fun t ht => Or.inr ⟨hev, by linarith⟩) (by rw [hNc]; push_cast; linarith)
      refine hR.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
      congr 2
      rw [show (2000 - 1000 + j : ℕ) = 1000 + j by omega]
      push_cast; ring
    · push Not at hs3
      have hk2 : 2000 < k := by
        have : (2000 : ℝ) < k := by linarith
        exact_mod_cast this
      have hmax : max k 2000 = k := max_eq_left hk2.le
      rw [hmax]
      simp only [bjsF306, hodd, true_and, not_le.mpr hs3, ite_false]
      apply div_le_div_of_nonneg_right _ hx.le
      have hR := riemann21_fn1122 (m + 1) hm1 (1 + (k : ℝ) / 1000) (1000 * (m + 2 + 2))
        (fun t ht => Or.inr ⟨hev, by linarith⟩) (by rw [hNc]; push_cast; linarith)
      refine hR.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
      rw [grid_cast1122c k j (by omega)]
  · have hk1 : 1000 ≤ k := by
      rcases hk with h | h
      · exact absurd h hodd
      · exact h
    have hodd' : Odd (m + 1) := by
      rcases Nat.even_or_odd (m + 2) with h | h
      · rcases h with ⟨r, hr⟩; exact ⟨r - 1, by omega⟩
      · exact absurd h hodd
    simp only [hodd, ite_false]
    have hk1r : (1000 : ℝ) ≤ k := by exact_mod_cast hk1
    simp only [bjsF306, hodd, false_and, ite_false]
    apply div_le_div_of_nonneg_right _ hx.le
    have hR := riemann21_fn1122 (m + 1) hm1 (1 + (k : ℝ) / 1000) (1000 * (m + 2 + 2))
      (fun t ht => Or.inl ⟨hodd', by
        have : (2 : ℝ) ≤ 1 + (k : ℝ) / 1000 := by linarith
        linarith⟩) (by rw [hNc]; push_cast; linarith)
    refine hR.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    rw [grid_cast1122c k j hk1]

/-- BJS display 19 on the grid: for k ≥ 1000, f_2(1 + k / 1000) equals the closed form
(s - 3 log(s - 1) + 3 log 3 - 4) / s for s = 1 + k / 1000 < 4, and 0 from s = 4 on. -/
theorem grid_base1122c (k : ℕ) (hk : 1000 ≤ k) :
    bjsF306 2 (1 + (k : ℝ) / 1000) =
      if k < 3000 then
        ((1 + (k : ℝ) / 1000) - 3 * log ((1 + (k : ℝ) / 1000) - 1) + 3 * log 3 - 4) /
          (1 + (k : ℝ) / 1000)
      else 0 := by
  have hkr : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  split_ifs with h3
  · have h3r : (k : ℝ) < 3000 := by exact_mod_cast h3
    have h19 := lemma7_display19_1122 (1 + (k : ℝ) / 1000) (by linarith) (by linarith)
    rw [eq_div_iff (by positivity), mul_comm]
    exact h19
  · push Not at h3
    have h3r : (3000 : ℝ) ≤ k := by exact_mod_cast h3
    exact fn_support1122 2 (by norm_num) _ (by push_cast; linarith)

/-- The induction of BJS Section 2.2, page 8: a table U with U_2 equal to f_2 by display 19
and satisfying the recursion of grid_step1122c with equality bounds f_n at every grid point
of its parity domain, 2 ≤ n. -/
theorem grid_le_table1122c (U : ℕ → ℕ → ℝ)
    (hbase : ∀ k, 1000 ≤ k → U 2 k =
      if k < 3000 then
        ((1 + (k : ℝ) / 1000) - 3 * log ((1 + (k : ℝ) / 1000) - 1) + 3 * log 3 - 4) /
          (1 + (k : ℝ) / 1000)
      else 0)
    (hrec : ∀ n, 3 ≤ n → ∀ k, (Odd n ∨ 1000 ≤ k) →
      U n k = (∑ j ∈ range (1000 * (n + 2)),
        U (n - 1) ((if Odd n then max k 2000 else k) - 1000 + j) / 1000) /
          (1 + (k : ℝ) / 1000)) :
    ∀ n, 2 ≤ n → ∀ k : ℕ, (Odd n ∨ 1000 ≤ k) → bjsF306 n (1 + (k : ℝ) / 1000) ≤ U n k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn2 k hk
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · have : n = 2 := by omega
      subst this
      have hk1 : 1000 ≤ k := by
        rcases hk with h | h
        · exact absurd h (by decide)
        · exact h
      rw [grid_base1122c k hk1, hbase k hk1]
    · refine (grid_step1122c n h3 k hk).trans ?_
      rw [hrec n h3 k hk]
      have hx : (0 : ℝ) < 1 + (k : ℝ) / 1000 := by positivity
      apply div_le_div_of_nonneg_right _ hx.le
      apply Finset.sum_le_sum
      intro j _
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply ih (n - 1) (by omega) (by omega)
      by_cases hodd : Odd n
      · right
        simp only [hodd, ite_true]
        have := le_max_right k 2000
        omega
      · left
        rcases Nat.even_or_odd n with h | h
        · rcases h with ⟨r, hr⟩; exact ⟨r - 1, by omega⟩
        · exact absurd h hodd

/-- The paper's table exists: defined by recursion on n, U_2 the closed form of display 19
and U_n the Riemann sum recursion of display 21 for n ≥ 3. -/
theorem table_exists1122c : ∃ U : ℕ → ℕ → ℝ,
    (∀ k, 1000 ≤ k → U 2 k =
      if k < 3000 then
        ((1 + (k : ℝ) / 1000) - 3 * log ((1 + (k : ℝ) / 1000) - 1) + 3 * log 3 - 4) /
          (1 + (k : ℝ) / 1000)
      else 0) ∧
    (∀ n, 3 ≤ n → ∀ k, (Odd n ∨ 1000 ≤ k) →
      U n k = (∑ j ∈ range (1000 * (n + 2)),
        U (n - 1) ((if Odd n then max k 2000 else k) - 1000 + j) / 1000) /
          (1 + (k : ℝ) / 1000)) := by
  let B : ℕ → ℝ := fun k =>
    if k < 3000 then
      ((1 + (k : ℝ) / 1000) - 3 * log ((1 + (k : ℝ) / 1000) - 1) + 3 * log 3 - 4) /
        (1 + (k : ℝ) / 1000)
    else 0
  let step : ℕ → (ℕ → ℝ) → ℕ → ℝ := fun n V k =>
    (∑ j ∈ range (1000 * (n + 2)),
      V ((if Odd n then max k 2000 else k) - 1000 + j) / 1000) / (1 + (k : ℝ) / 1000)
  let W : ℕ → ℕ → ℝ := fun r => Nat.rec B (fun r V => step (r + 3) V) r
  refine ⟨fun n => if n < 2 then fun _ => 0 else W (n - 2), ?_, ?_⟩
  · intro k _
    rfl
  · intro n hn k _
    obtain ⟨r, rfl⟩ : ∃ r, n = r + 3 := ⟨n - 3, by omega⟩
    simp only [show ¬ (r + 3 < 2) by omega, show ¬ (r + 3 - 1 < 2) by omega,
      show ¬ (r + 2 < 2) by omega, ite_false, show r + 3 - 2 = r + 1 by omega,
      show r + 3 - 1 - 2 = r by omega, show r + 3 - 1 = r + 2 by omega,
      show r + 2 - 2 = r by omega]
    rfl

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.grid_step1122c
#print axioms LeanLab.Cai2002.grid_le_table1122c
#print axioms LeanLab.Cai2002.table_exists1122c
