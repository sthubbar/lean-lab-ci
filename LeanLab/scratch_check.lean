import LeanLab.LZCesaroShort.Lemma3Coefficients
import LeanLab.PNTPort.StrongPNT.Bridge
import Mathlib

open ArithmeticFunction Chebyshev Filter Topology Finset

namespace LeanLab.LZCesaroShort

-- Abel identity for Lambda * log
lemma abel_lambda_log (n : ℕ) :
    (∑ k ∈ range (n + 1), vonMangoldt k * Real.log (k : ℝ)) =
    ψ (n : ℝ) * Real.log (n : ℝ) -
    ∑ j ∈ range n, ψ (j : ℝ) * (Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ)) := by
  have h := Finset.sum_range_by_parts (f := fun i : ℕ => Real.log (i : ℝ)) (g := vonMangoldt) (n + 1)
  simp only [Nat.add_sub_cancel] at h
  have hsum : ∀ m : ℕ, (∑ k ∈ range (m + 1), vonMangoldt k) = ψ (m : ℝ) :=
    sum_range_vonMangoldt
  simp_rw [hsum] at h
  -- Use ring_nf on both sides or just congr
  have h1 : (∑ i ∈ range (n + 1), Real.log (i : ℝ) * vonMangoldt i) =
      (∑ k ∈ range (n + 1), vonMangoldt k * Real.log (k : ℝ)) := by
    refine sum_congr rfl fun k _ => ?_
    exact mul_comm _ _
  have h2 : Real.log (n : ℝ) * ψ (n : ℝ) = ψ (n : ℝ) * Real.log (n : ℝ) := mul_comm _ _
  have h3 : (∑ x ∈ range n, (Real.log ((x + 1 : ℕ) : ℝ) - Real.log (x : ℝ)) * ψ (x : ℝ)) =
      (∑ j ∈ range n, ψ (j : ℝ) * (Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ))) := by
    refine sum_congr rfl fun j _ => ?_
    exact mul_comm _ _
  calc (∑ k ∈ range (n + 1), vonMangoldt k * Real.log (k : ℝ))
      = (∑ i ∈ range (n + 1), Real.log (i : ℝ) * vonMangoldt i) := h1.symm
    _ = Real.log (n : ℝ) * ψ (n : ℝ) -
          ∑ x ∈ range n, (Real.log ((x + 1 : ℕ) : ℝ) - Real.log (x : ℝ)) * ψ (x : ℝ) := h
    _ = ψ (n : ℝ) * Real.log (n : ℝ) -
          ∑ j ∈ range n, ψ (j : ℝ) * (Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ)) := by
        rw [h2, h3]

end LeanLab.LZCesaroShort
