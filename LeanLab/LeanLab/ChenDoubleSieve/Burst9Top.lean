import LeanLab.ChenDoubleSieve.Burst8P2
import LeanLab.ChenDoubleSieve.Burst9Psi2
import LeanLab.ChenDoubleSieve.Burst9Matrix

/-!
# Burst 9: Wu 2004 Theorem 1 with the two table leaves split

P0036, J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem,
Acta Arith. 114 (2004), arXiv 0705.1652. AI wrote the Lean code. Binary Goldbach is OPEN;
Theorem 1 is an upper bound for `D(N)`.

`wu2004_thm1_of_p3` has the type of `wu2004_thm1`, `GoldbachUpper 7.8209`, and no sorry of its
own. It is `Burst8P2.wu2004_thm1_of_p2` with two changes.
* The leaf `Burst4Split.integral_matrix_bound` is replaced by
  `Burst9Matrix.integral_matrix_bound_p3`, the same statement from 81 single entry leaves.
* The leaf `Burst4Split.table1_Psi2` is replaced by `Burst9Psi2.table1_Psi2_zero`, applied to
  `zeroExt ω`, the Buchstab function extended by 0 below 1. This is Wu's convention for the
  integrals `I_{2,i}`, page 26, whose arguments can fall below 1. The cited sub-leaves
  `Burst8P2.lemma51` and `Burst8P2.lemma52` hold for every `ω` with `IsBuchstab ω`, so they are
  used with `zeroExt ω`; `zeroExt_isBuchstab` shows that `zeroExt ω` again satisfies Wu's
  definition, Lemma 2.10, page 9.
-/

set_option maxHeartbeats 1000000
noncomputable section
open Real Set MeasureTheory
namespace LeanLab.ChenDoubleSieve.Burst9Top
open Wu04Functional
open Burst8P2

/-- Buchstab's function extended by `0` below `1`, Wu's convention in Lemma 5.2. -/
def zeroExt (ω : ℝ → ℝ) (u : ℝ) : ℝ := if u < 1 then 0 else ω u

/-- `zeroExt ω` vanishes below `1`. PROVED. -/
theorem zeroExt_zero (ω : ℝ → ℝ) : ZeroBelowOne (zeroExt ω) := by
  intro u hu
  simp [zeroExt, hu]

/-- `zeroExt ω` satisfies Wu's definition of Buchstab's function, Lemma 2.10, page 9, whenever
`ω` does: the definition only involves arguments `u ≥ 1`. PROVED. -/
theorem zeroExt_isBuchstab {ω : ℝ → ℝ} (hω : IsBuchstab ω) : IsBuchstab (zeroExt ω) := by
  refine ⟨?_, ?_, ?_⟩
  · refine hω.1.congr fun u hu => ?_
    have hu' : ¬ u < 1 := not_lt.mpr hu
    simp [zeroExt, hu']
  · intro u h1 h2
    have hu' : ¬ u < 1 := not_lt.mpr h1
    simp only [zeroExt, hu', if_false]
    exact hω.2.1 u h1 h2
  · intro u hu
    have hu' : ¬ u - 1 < 1 := by linarith
    have hd := hω.2.2 u hu
    have he : (fun v => v * zeroExt ω v) =ᶠ[nhds u] (fun v => v * ω v) := by
      filter_upwards [Ioi_mem_nhds (show (1 : ℝ) < u by linarith)] with v hv
      have hv' : ¬ v < 1 := not_lt.mpr (le_of_lt hv)
      simp [zeroExt, hv']
    have hval : zeroExt ω (u - 1) = ω (u - 1) := by simp [zeroExt, hu']
    rw [hval]
    exact hd.congr_of_eventuallyEq he

/-- **Wu 2004 Theorem 1 from the burst 9 split.** The exact statement of `wu2004_thm1`.
CONDITIONAL ON the six analytic leaves of `Burst8P2`, `prop1_upper_eps`, `prop1_lower_eps`,
`proposition2_H`, `proposition2_h`, `lemma51`, `lemma52`, the 32 LEAF `I₂` bounds of
`Burst9I2` and the 81 LEAF entries of `Burst9Matrix`. -/
theorem wu2004_thm1_of_p3 : GoldbachUpper 7.8209 := by
  obtain ⟨F, f, ω₀, hF, hω₀⟩ := Task275.standard_functions
  have hω : IsBuchstab (zeroExt ω₀) := zeroExt_isBuchstab hω₀
  have hz : ZeroBelowOne (zeroExt ω₀) := zeroExt_zero ω₀
  obtain ⟨d1, hd1, hC⟩ := corrections_real hF
  obtain ⟨d2, hd2, h1⟩ := proposition1 hF
  obtain ⟨d3, hd3, hA⟩ := corollary1 hF
  obtain ⟨d4, hd4, h3⟩ := proposition3 hF hω
  obtain ⟨d5, hd5, h4⟩ := proposition4 hF hω
  set m := min d1 (min d2 (min d3 (min d4 d5))) with hm
  have hm0 : 0 < m := by
    simp only [hm, lt_min_iff]
    exact ⟨hd1, hd2, hd3, hd4, hd5⟩
  set δ := min (m / 2) (1 / 10000000) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδm : δ < m := (min_le_left _ _).trans_lt (by linarith)
  have hδs : δ ≤ 1 / 10000000 := min_le_right _ _
  have hm1 : m ≤ d1 := min_le_left _ _
  have hm2 : m ≤ d2 := (min_le_right _ _).trans (min_le_left _ _)
  have hm3 : m ≤ d3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm4 : m ≤ d4 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hm5 : m ≤ d5 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨H, h, hR⟩ := hC δ hδ0 (hδm.trans_le hm1)
  have hnn := h1 δ hδ0 (hδm.trans_le hm2) H h hR
  have hanti := hA δ hδ0 (hδm.trans_le hm3) H h hR
  have hp3 := h3 δ hδ0 (hδm.trans_le hm4) H h hR
  have hp4 := h4 δ hδ0 (hδm.trans_le hm5) H h hR
  have hdec : AntitoneOn H (Icc (1 : ℝ) 3) :=
    hanti.mono (Icc_subset_Icc le_rfl (by norm_num))
  have hT : Wu04Discretization.TableInputs H :=
    { nonnegative := fun t ht => (hnn t ⟨ht.1, by linarith [ht.2]⟩).1
      decreasing := hdec
      kernel_nonnegative := fun i t ht => Wu04Table.tableKernel_nonnegative i ht
      kernel_integrable := table_kernel_integrable
      product_integrable := fun i =>
        Burst4Split.product_integrable hdec (table_kernel_integrable i)
      functional := Wu04Table.functional_rows hω hp3 hp4
        (Burst9Psi2.table1_Psi2_zero hω hz) }
  have hx : (223938 / 10000000 : ℝ) ≤ H (2.2 : ℝ) :=
    Wu04Discretization.correction_of_functional H hT Burst9Matrix.integral_matrix_bound_p3
  have hc : (223937 / 10000000 : ℝ) < H 2.2 := by linarith
  obtain ⟨N₀, hN₀⟩ := theorem1_final_display hF hδ0 (by linarith) hR hc
    (ε := 1 / 1000000) (by norm_num)
  refine ⟨N₀, fun N hE hN => (hN₀ N hE hN).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (Burst4Split.final_constant hδ0 hδs) (Θ_nonneg N)

end LeanLab.ChenDoubleSieve.Burst9Top

#print axioms LeanLab.ChenDoubleSieve.Burst9Top.zeroExt_zero
#print axioms LeanLab.ChenDoubleSieve.Burst9Top.zeroExt_isBuchstab
#print axioms LeanLab.ChenDoubleSieve.Burst9Top.wu2004_thm1_of_p3
