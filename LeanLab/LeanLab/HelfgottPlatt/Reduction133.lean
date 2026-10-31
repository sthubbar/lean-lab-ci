/-
P0006 page 2, Section 2, bounded numerator Jacobi preprocessing.
This file specifies a binary digit scan for remainder reduction. Cost bounds
count bounded width arithmetic steps. They do not measure Mathlib's Jacobi
implementation or assert a machine runtime. AI wrote the Lean code.
Binary Goldbach is open.
-/
import Mathlib.Data.Nat.Digits.Lemmas
import LeanLab.HelfgottPlatt.Jacobi133
import Mathlib.Tactic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped Asymptotics

namespace LeanLab.HelfgottPlatt.Task133

/-- Page 2, a derived streaming reduction model. Read digits from most
significant to least significant and retain a remainder after each step. -/
def scanResidue (M : ℕ) : List ℕ → ℕ → ℕ
  | [], r => r % M
  | d :: ds, r => scanResidue M ds ((2 * r + d) % M)

/-- Page 2, fixed numerator Jacobi preprocessing. The digit scan computes
the remainder of the represented numeral with an arbitrary initial state. -/
theorem scanResidue_spec (M : ℕ) (ds : List ℕ) (r : ℕ) :
    scanResidue M ds r = (2 ^ ds.length * r + Nat.ofDigits 2 ds.reverse) % M := by
  induction ds generalizing r with
  | nil => simp [scanResidue]
  | cons d ds ih =>
    rw [scanResidue, ih, List.length_cons, List.reverse_cons,
      Nat.ofDigits_append, Nat.ofDigits_singleton, List.length_reverse]
    calc
      _ = (2 ^ ds.length * (2 * r + d) + Nat.ofDigits 2 ds.reverse) % M := by
        simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
      _ = _ := by congr 1; ring

/-- Page 2, bounded width preprocessing. With a state below M and one
binary digit, the next remainder needs at most one subtraction. -/
theorem binary_step {M r d : ℕ} (hr : r < M) (hd : d < 2) :
    (2 * r + d) % M = if 2 * r + d < M then 2 * r + d else 2 * r + d - M := by
  have hu : 2 * r + d < 2 * M := by omega
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega)]
    exact Nat.mod_eq_of_lt (by omega)

/-- Page 2, derived remainder preprocessing on the canonical binary digits. -/
def binaryRemainder (M N : ℕ) : ℕ := scanResidue M (Nat.digits 2 N).reverse 0

/-- Page 2, the binary preprocessing computes the exact required remainder. -/
theorem binaryRemainder_eq (M N : ℕ) : binaryRemainder M N = N % M := by
  simp only [binaryRemainder, scanResidue_spec, Nat.mul_zero, Nat.zero_add,
    List.reverse_reverse, Nat.ofDigits_digits]

/-- Page 2, an instrumented scan model. One step is one remainder update
for one input digit. The base state is already a bounded remainder. -/
def scanWithCost (M : ℕ) : List ℕ → ℕ → ℕ × ℕ
  | [], r => (r, 0)
  | d :: ds, r =>
    let vc := scanWithCost M ds ((2 * r + d) % M)
    (vc.1, vc.2 + 1)

/-- Page 2, explicit scan cost. A bounded initial state gives the same
remainder as scanResidue and exactly one update per input digit. -/
theorem scanWithCost_spec {M r : ℕ} (hr : r < M) (ds : List ℕ) :
    scanWithCost M ds r = (scanResidue M ds r, ds.length) := by
  induction ds generalizing r with
  | nil => simp [scanWithCost, scanResidue, Nat.mod_eq_of_lt hr]
  | cons d ds ih =>
    simp only [scanWithCost, scanResidue, List.length_cons]
    rw [ih (Nat.mod_lt _ (by omega))]

/-- Page 2, whole-number binary reduction with an explicit update counter. -/
def countedRemainder (M N : ℕ) : ℕ × ℕ :=
  scanWithCost M (Nat.digits 2 N).reverse 0

/-- Page 2, canonical reduction and exact digit count in one specification. -/
theorem countedRemainder_spec {M : ℕ} (hM : 0 < M) (N : ℕ) :
    countedRemainder M N = (N % M, (Nat.digits 2 N).length) := by
  rw [countedRemainder, scanWithCost_spec hM, List.length_reverse]
  change (binaryRemainder M N, (Nat.digits 2 N).length) = _
  rw [binaryRemainder_eq]

/-- Page 2, exact binary scan length for a nonzero candidate. -/
theorem countedRemainder_steps {M N : ℕ} (hM : 0 < M) (hN : N ≠ 0) :
    (countedRemainder M N).2 = N.log2 + 1 := by
  rw [countedRemainder_spec hM, Nat.length_digits 2 N (by decide) hN,
    Nat.log2_eq_log_two]

/-- Page 2, explicit logarithmic bound on the number of bounded width
remainder updates. The constant is derived here, not printed in the paper. -/
theorem reduction_steps_le_log {M N : ℕ} (hM : 0 < M) (hN : 2 ≤ N) :
    ((countedRemainder M N).2 : ℝ) ≤ (2 / Real.log 2) * Real.log N := by
  have hpos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : (N.log2 : ℝ) ≤ Real.log N / Real.log 2 := by
    simpa only [Real.logb] using Real.log2_le_logb N
  have hprod := (le_div_iff₀ hpos).mp hlog
  have hlogN : Real.log (2 : ℝ) ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  rw [countedRemainder_steps hM (by omega), Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ 2 * Real.log N / Real.log 2 := (le_div_iff₀ hpos).mpr (by nlinarith)
    _ = (2 / Real.log 2) * Real.log N := by ring

/-- Page 2, the derived preprocessing scan has O of log N bounded width
updates as N grows. This is an arithmetic step count, not a runtime claim. -/
theorem reduction_steps_isBigO {M : ℕ} (hM : 0 < M) :
    (fun N : ℕ => ((countedRemainder M N).2 : ℝ))
      =O[Filter.atTop] (fun N : ℕ => Real.log N) := by
  apply Asymptotics.IsBigO.of_bound (2 / Real.log 2)
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with N hN
  have hn : 0 ≤ ((countedRemainder M N).2 : ℝ) := Nat.cast_nonneg _
  have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn, abs_of_nonneg hl]
    using reduction_steps_le_log hM hN

/-- Page 2, certified connection from the binary scan to the original
witness search. Odd candidates have exactly the same selected witness. -/
theorem binary_witness_search {N B : ℕ} (hN : Odd N) :
    Task98.firstWitness (countedRemainder (jacobiPeriod B) N).1 B =
      Task98.firstWitness N B := by
  rw [countedRemainder_spec (by unfold jacobiPeriod; positivity)]
  exact (firstWitness_mod hN).symm

/-- Page 2, small checks for the remainder and cost models. -/
theorem reduction_instances :
    binaryRemainder 24 41 = 17 ∧ countedRemainder 24 41 = (17, 6) ∧
      scanWithCost 3 [1, 0, 1] 0 = (2, 3) := by
  decide +kernel

end LeanLab.HelfgottPlatt.Task133
