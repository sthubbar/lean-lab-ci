import LeanLab.GoldbachShort78.Statements
import LeanLab.GoldbachShort78.BHPBookkeeping

/-!
AI wrote the Lean code, Codex task57. Binary Goldbach is OPEN.
Full input instances from Mathlib's proved Bertrand theorem.
These test the lab's interfaces and claim no new prime or Goldbach bound.
-/

namespace LeanLab.GoldbachShort78

/-- A full nonvacuous instance of PrimesAll, using Bertrand for the integer floor of x. -/
theorem primesAll_one_bertrand : PrimesAll 1 2 := by
  intro x hx
  have hx0 : 0 ≤ x := by linarith
  have hn : 2 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by simpa using hx)
  obtain ⟨p, hp, hpl, hpu⟩ := Nat.exists_prime_lt_and_le_two_mul ⌊x⌋₊ (by omega)
  have hplr : (⌊x⌋₊ : ℝ) + 1 ≤ p := by exact_mod_cast hpl
  have hpur : (p : ℝ) ≤ 2 * (⌊x⌋₊ : ℝ) := by exact_mod_cast hpu
  have hfloor := Nat.floor_le hx0
  have hfloorlt := Nat.lt_floor_add_one x
  refine ⟨p, hp, by linarith, ?_⟩
  rw [Real.rpow_one]
  linarith

/-- A full least-index instance for BHP Lemmas 10 and 11. -/
theorem bhp_least_index_instance :
    IsLeast {j : ℕ | 0 < j ∧ (1 / 2 : ℝ) - 2 * j * (21 / 40 - 1 / 2) ≤ 0} 10 := by
  refine ⟨?_, ?_⟩
  · norm_num
  · intro j hj
    have hjR : (10 : ℝ) ≤ j := by nlinarith [hj.2]
    exact_mod_cast hjR

/-- The printed Lemma 11 gap bound is attained by a full instance of its hypotheses. -/
theorem bhp_lemma11_sharp_instance :
    |(∑ _i ∈ Finset.range 10, (1 / 20 : ℝ)) -
      (1 - (∑ _i ∈ Finset.range 11, (1 / 20 : ℝ)))| = 1 / 20 ∧
    |(∑ _i ∈ Finset.range 10, (1 / 20 : ℝ)) -
      (1 - (∑ _i ∈ Finset.range 11, (1 / 20 : ℝ)))| ≤ 2 * (21 / 40 : ℝ) - 1 := by
  refine ⟨by norm_num, ?_⟩
  have h := bhp_lemma11 (θ := 21 / 40) (α := 0) (ε := 1 / 1000)
    (h := 10) (k := 10) (u := fun _ => 1 / 20)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    bhp_least_index_instance
    (by intro i hi j hj hij; exact le_rfl)
    (by intro i hi; norm_num)
    (by norm_num)
    (by intro hk; norm_num)
    (by norm_num)
  simpa only [zero_add] using h

end LeanLab.GoldbachShort78
