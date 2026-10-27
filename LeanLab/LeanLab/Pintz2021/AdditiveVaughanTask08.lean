import LeanLab.Pintz2021.Lemma1U1369
import LeanLab.PNTPort.BV.Vaughan

/-!
Additive Vaughan sums for P0054 Lemma 1, display 1.10.
AI wrote the Lean code. Goldbach is open.
The source route is Davenport chapters 24 and 25.
This file proves algebraic helpers. It does not assume VaughanThm31.
-/

namespace LeanLab.Pintz2021.AdditiveVaughanTask08

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.BV
open LeanLab.Pintz2021.Lemma1U1369

noncomputable def V1 (x α : ℝ) (u : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, ((if n ≤ u then Λ n else 0 : ℝ) : ℂ) * e (n * α)

noncomputable def V2 (x α : ℝ) (u v : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, ((∑ p ∈ n.divisorsAntidiagonal,
    ∑ y ∈ p.1.divisorsAntidiagonal,
      (if y.1 ≤ u ∧ y.2 ≤ v then Λ y.1 * (μ y.2 : ℝ) else 0) : ℝ) : ℂ) * e (n * α)

noncomputable def V3 (x α : ℝ) (v : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, ((∑ p ∈ n.divisorsAntidiagonal,
    (if p.1 ≤ v then (μ p.1 : ℝ) * Real.log p.2 else 0) : ℝ) : ℂ) * e (n * α)

noncomputable def V4 (x α : ℝ) (u v : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, ((∑ p ∈ n.divisorsAntidiagonal,
    (if u < p.1 ∧ v < p.2 then
      Λ p.1 * ∑ d ∈ p.2.divisors, (if d ≤ v then (μ d : ℝ) else 0) else 0) : ℝ) : ℂ) *
        e (n * α)

/-- Vaughan's pointwise identity summed against the additive character. -/
theorem VS_decomp (x α : ℝ) (u v : ℕ) (hv : 1 ≤ v) :
    VS x α = V1 x α u - V2 x α u v + V3 x α v - V4 x α u v := by
  have hsum : VS x α = ∑ n ∈ Icc 1 ⌊x⌋₊, ((Λ n : ℝ) : ℂ) * e (n * α) := by
    unfold VS
    symm
    apply sum_subset (Icc_subset_Icc (by omega) le_rfl)
    intro n hn hn'
    have hn0 : n = 0 := by simp only [mem_Icc] at hn hn'; omega
    simp [hn0]
  rw [hsum]
  unfold V1 V2 V3 V4
  rw [← sum_sub_distrib, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun n hn => ?_
  have h := vaughan_identity u v hv n (mem_Icc.mp hn).1
  rw [← sub_mul, ← add_mul, ← sub_mul]
  congr 1
  exact_mod_cast h

end LeanLab.Pintz2021.AdditiveVaughanTask08

#print axioms LeanLab.Pintz2021.AdditiveVaughanTask08.VS_decomp
