/- AI wrote this Lean code for CODEX task224. Goldbach is open.
Finite numerical inputs named in journal p. 1220 proof of Lemma 6.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.PortedMertens

namespace LeanLab.BS2022GRH.FiniteMertens224
open Real Finset
noncomputable section

/-- LEAF. The Rosser and Schoenfeld Theorem 20 application cited on p. 1220.
Its verified range ends at 1e8. The common M is identified by the port.
https://doi.org/10.1215/ijm/1255631807 -/
theorem rosser_schoenfeld_small (x : ℝ) (hx : 3 ≤ x) (hx8 : x ≤ 1e8) :
    log (log x) + PortedMertens.Mertens.M ≤
      ∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p := by
  sorry

/-- LEAF. The Python 3.7 computation cited on journal p. 1220.
State the finite right endpoints needed for every real strict cutoff.
The paper supplies no kernel certificate in this repository. -/
theorem journal_computation (n : ℕ) (hn8 : 10 ^ 8 ≤ n) (hn12 : n < 10 ^ 12) :
    log (log ((n : ℝ) + 1)) + PortedMertens.Mertens.M ≤
      ∑ p ∈ Nat.primesLE n, (1 : ℝ) / p := by
  sorry

/-- An integer endpoint certificate covers every real point in the computed range. -/
theorem finite_from_integer_endpoints (M : ℝ)
    (hcomp : ∀ n : ℕ, 10 ^ 8 ≤ n → n < 10 ^ 12 →
      log (log ((n : ℝ) + 1)) + M ≤ ∑ p ∈ Nat.primesLE n, (1 : ℝ) / p)
    {x : ℝ} (hx8 : 1e8 < x) (hx12 : x ≤ 1e12) :
    log (log x) + M ≤ ∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p := by
  let n : ℕ := ⌈x⌉₊ - 1
  have hcpos : 1 ≤ ⌈x⌉₊ := by
    have : (0 : ℝ) < x := by linarith
    exact Nat.ceil_pos.mpr this
  have hcn : n + 1 = ⌈x⌉₊ := Nat.sub_add_cancel hcpos
  have hn8 : 10 ^ 8 ≤ n := by
    have : 10 ^ 8 < ⌈x⌉₊ := Nat.lt_ceil.mpr (by norm_num at hx8 ⊢; exact hx8)
    dsimp [n]
    omega
  have hn12 : n < 10 ^ 12 := by
    have : ⌈x⌉₊ ≤ 10 ^ 12 := Nat.ceil_le.mpr (by norm_num at hx12 ⊢; exact hx12)
    omega
  have hxceil : x ≤ (n : ℝ) + 1 := by
    have := Nat.le_ceil x
    rw [← hcn, Nat.cast_add, Nat.cast_one] at this
    exact this
  have hlog : log (log x) ≤ log (log ((n : ℝ) + 1)) := by
    apply log_le_log (log_pos (by linarith : 1 < x))
    exact log_le_log (by linarith : 0 < x) hxceil
  rw [← hcn]
  change log (log x) + M ≤ ∑ p ∈ Nat.primesLE n, (1 : ℝ) / p
  linarith [hcomp n hn8 hn12]

end
end LeanLab.BS2022GRH.FiniteMertens224

#print axioms LeanLab.BS2022GRH.FiniteMertens224.finite_from_integer_endpoints
