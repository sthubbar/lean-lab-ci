/-
Bordignon, Johnston and Starichkova, Theorem 6, pages 4 to 5.
Source: https://arxiv.org/abs/2207.09452
This file records the cited finite support sieve input.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Decomp306b

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-- LEAF. Bordignon, Johnston and Starichkova Theorem 6, pages 4 to 5,
equations 3 to 11 and Table 1. The existing finite support interface retains the
complete Q times D remainder. Its weak bounds follow from the printed strict bounds.
The constants of a table row apply below that row's epsilon as explained on page 5.
This is a cited input, not a proved linear sieve theorem. -/
theorem leaf306_theorem6 : LeanLab.ChenExplicit.Theorem6Stmt := by
  sorry

/-- The cited finite sieve applies to the constructed global functions.
CONDITIONAL ON leaf306_theorem6. Pages 4 to 5, equations 5 and 6. -/
theorem theorem6_for_global306 :
    LeanLab.ChenExplicit.Theorem6 sieveUpper306 sieveLower306 := by
  exact leaf306_theorem6 sieveUpper306 sieveLower306 sieveFns306

/-- Finite cardinality form of Theorem 6 equations 5, 6 and 11, pages 4 to 5.
CONDITIONAL ON Theorem6Stmt. Both bounds retain the exact Q times D remainder.
This applies to ordinary, prime divisor and switched finite supports. -/
theorem theorem6_cardinality306
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt)
    (A : Finset ℕ) (hA : 0 ∉ A)
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative)
    (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q ∈ P)
    (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ 1 / 100000)
    (hdim : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter
        (fun p : ℕ => p ∉ Q ∧ u ≤ (p : ℝ)), (1 - g p)⁻¹ <
          (1 + ε) * (log z / log u)) (D : ℝ) :
    let PP : ℕ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p
    let s : ℝ := log D / log z
    let V : ℝ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)
    let R : ℝ := ∑ d ∈ PP.divisors.filter
      (fun d : ℕ => (d : ℝ) < (∏ q ∈ Q, (q : ℝ)) * D),
      |(((A.filter (fun n => d ∣ n)).card : ℝ) - (A.card : ℝ) * g d)|
    (z ≤ D → ((A.filter (fun n => n.Coprime PP)).card : ℝ) ≤
      (sieveUpper306 s + ε * 106 * exp 2 * LeanLab.ChenExplicit.hSieve s) *
        (A.card : ℝ) * V + R) ∧
    (z ^ 2 ≤ D → (sieveLower306 s - ε * 107 * exp 2 * LeanLab.ChenExplicit.hSieve s) *
      (A.card : ℝ) * V - R ≤ ((A.filter (fun n => n.Coprime PP)).card : ℝ)) := by
  classical
  let a : ℕ → ℝ := fun n => if n ∈ A then 1 else 0
  have h := h6 sieveUpper306 sieveLower306 sieveFns306
    100000 106 107 (by norm_num [LeanLab.ChenExplicit.table1]) ε hε hεmax
    A a hA (fun n => by dsimp [a]; split_ifs <;> norm_num)
    (fun n hn => by simp [a, hn]) P hP z hz (fun _ => g)
    (fun _ => hg) (fun _ => hgp) Q hQ (fun _ => hdim) D
  dsimp only at h ⊢
  have ha (n : ℕ) (hn : n ∈ A) : a n = 1 := by simp [a, hn]
  have hS (PP : ℕ) : (∑ n ∈ A, if n.Coprime PP then a n else 0) =
      ((A.filter (fun n => n.Coprime PP)).card : ℝ) := by
    calc
      _ = ∑ n ∈ A, if n.Coprime PP then (1 : ℝ) else 0 := by
        apply sum_congr rfl
        intro n hn
        rw [ha n hn]
      _ = _ := by rw [sum_boole]
  have hX (v : ℝ) : (∑ n ∈ A, a n * v) = (A.card : ℝ) * v := by
    calc
      _ = ∑ _n ∈ A, v := by
        apply sum_congr rfl
        intro n hn
        rw [ha n hn, one_mul]
      _ = _ := by simp
  have hr (d : ℕ) : (∑ n ∈ A, if d ∣ n then a n else 0) =
      ((A.filter (fun n => d ∣ n)).card : ℝ) := by
    calc
      _ = ∑ n ∈ A, if d ∣ n then (1 : ℝ) else 0 := by
        apply sum_congr rfl
        intro n hn
        rw [ha n hn]
      _ = _ := by rw [sum_boole]
  simp_rw [hS, hX, hr] at h
  simpa only [mul_assoc, Nat.cast_ofNat] using h

#print axioms theorem6_cardinality306

#print axioms leaf306_theorem6
#print axioms theorem6_for_global306
end LeanLab.Cai2002
