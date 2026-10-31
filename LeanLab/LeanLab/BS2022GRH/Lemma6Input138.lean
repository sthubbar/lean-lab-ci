/-
AI wrote this Lean code for CODEX task138, 2026-10-27.
P0021 journal Lemma 6, display 3 p. 1219, and display 9 p. 1222.
The three analytic bounds are a cited paper statement with an explicit common constant M.
No proof of Lemma6J or value for M is asserted here.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.Mertens138
namespace LeanLab.BS2022GRH.Lemma6Input138
open Real Finset Classical ChenThresholdGRH Decomp138 Mertens138

/-- Lemma 6 and display 3, journal p. 1219, with the paper's common Mertens constant as parameter.
CITED from Rosser and Schoenfeld 1962 Theorem 20, Broadbent et al. Table 15,
and the paper's finite computation in the middle range. -/
def Lemma6J (M : ℝ) : Prop :=
  (∀ x : ℝ, 3 ≤ x → x ≤ 1e12 →
    log (log x) + M ≤ ∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p) ∧
  (∀ x : ℝ, 1e12 < x →
    log (log x) + M - 1.107533e-7 ≤ ∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p) ∧
  (∀ x : ℝ, exp 2753 < x →
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) ≤ log (log x) + M + 2.28975e-9 / log x)

/-- The two lower ranges of Lemma 6 imply its weaker bound uniformly on u at least 400. -/
lemma lower_uniform (M : ℝ) (h6 : Lemma6J M) (u : ℝ) (hu : 400 ≤ u) :
    log (log u) + M - 1.107533e-7 ≤ ∑ p ∈ Nat.primesBelow ⌈u⌉₊, (1 : ℝ) / p := by
  by_cases hsmall : u ≤ 1e12
  · have h := h6.1 u (by linarith) hsmall
    linarith
  · exact h6.2.1 u (lt_of_not_ge hsmall)

/-- Lemma 6 bounds the strict prime sum by comparison with its non-strict prime sum. -/
lemma upper_strict_below (M : ℝ) (h6 : Lemma6J M) (z : ℝ) (hz : exp 2753 < z) :
    (∑ p ∈ Nat.primesBelow ⌈z⌉₊, (1 : ℝ) / p) ≤
      log (log z) + M + 2.28975e-9 / log z := by
  have hz0 : 0 < z := (exp_pos _).trans hz
  have hsub : Nat.primesBelow ⌈z⌉₊ ⊆ Nat.primesLE ⌊z⌋₊ := by
    intro p hp
    obtain ⟨hpceil, hprime⟩ := Nat.mem_primesBelow.mp hp
    have hplt : (p : ℝ) < z := Nat.lt_ceil.mp hpceil
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hz0.le).2 hplt.le, hprime⟩
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans (h6.2.2 z hz)

/-- Exact Lemma 7, CONDITIONAL ON the three-part journal Lemma 6. -/
theorem lemma7J_of_lemma6 (M : ℝ) (h6 : Lemma6J M) : Lemma7J :=
  Mertens138.lemma7J_of_mertens M (upper_strict_below M h6) (lower_uniform M h6)
end LeanLab.BS2022GRH.Lemma6Input138

#print axioms LeanLab.BS2022GRH.Lemma6Input138.lower_uniform

#print axioms LeanLab.BS2022GRH.Lemma6Input138.upper_strict_below

#print axioms LeanLab.BS2022GRH.Lemma6Input138.lemma7J_of_lemma6
