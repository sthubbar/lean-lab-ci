/-
AI-written Lean code, OpenAI Codex, task33, 2026-10-23, T1.
Concrete instances for the statement audit in STATEMENTS.md.
These check elementary hypotheses and finite counts. No cited input is assumed.
Goldbach is open.
-/
import LeanLab.AlmostPrimeSums.Chen1973CRT
import LeanLab.AlmostPrimeSums.Chen1973FiniteSieve
import LeanLab.AlmostPrimeSums.Chen1973LambdaConvolution
import LeanLab.AlmostPrimeSums.Chen1973TheoremII
import LeanLab.AlmostPrimeSums.TogashiUchiyamaScale

open Finset Real
open LeanLab.AlmostPrimeSums
open Chen1973Display24 Chen1973Weights Chen1973FiniteSieve TogashiUchiyamaSection5

noncomputable section
attribute [local instance] Classical.propDecidable

example : Qset 28 = {3} := by decide

example : (S3set 28).card = 4 := by decide

example : (∑ q ∈ Qset 28, 2 * (28 / q ^ 2 + 1) : ℕ) = 8 := by decide

example : (∑ q ∈ Qset 28, ((q : ℝ) ^ 2)⁻¹) ≤ 1 := by
  have h := S3Asymptotic.sum_inv_sq_le 28 1 (by decide)
  norm_num at h ⊢
  exact h

example : sv 2 1 = {1} := by simp [sv]

example : ∀ d ∈ sv 2 1, ∀ e ∈ sv 2 1,
    |((({1, 2, 3} : Finset ℕ).filter (d.lcm e ∣ ·)).card : ℝ) - 3 / ((d.lcm e).totient : ℝ)| ≤ 0 := by
  intro d hd e he
  have hd1 : d = 1 := (mem_Icc.mp (mem_filter.mp hd).1).2.antisymm (mem_Icc.mp (mem_filter.mp hd).1).1
  have he1 : e = 1 := (mem_Icc.mp (mem_filter.mp he).1).2.antisymm (mem_Icc.mp (mem_filter.mp he).1).1
  subst d
  subst e
  norm_num

example : |lamC 2 1 1| = 1 := by rw [lamC_one even_two (by norm_num)]; norm_num

example : lamC 2 1 3 = 0 := lamC_eq_zero_of_not_mem (by simp [sv])

example : ‖Chen1973Lemma4.primSum 15 7‖ ≤ 3 :=
  Chen1973CRT.chen_lemma4_via_CRT (Nat.squarefree_mul_iff.mpr
    ⟨by decide, Nat.prime_three.squarefree, Nat.prime_five.squarefree⟩ : Squarefree (3 * 5)) 7

example : 0 < TogashiUchiyamaScale.a 1 := TogashiUchiyamaScale.a_pos (by norm_num)

example : TogashiUchiyamaScale.Q 2 = 1 := by
  simp [TogashiUchiyamaScale.Q, Nat.prime_two.primeFactors, Finset.filter_singleton]

example : TogashiUchiyamaScale.Cpaper 1 2 = 1 / 8 := by
  simp [TogashiUchiyamaScale.Cpaper, TogashiUchiyamaScale.Q, Nat.prime_two.primeFactors, Finset.filter_singleton]

example : ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 30 ∧ TogashiUchiyamaEpsilon.I ε < 79.3026 :=
  TogashiUchiyamaEpsilon.exists_epsilon
