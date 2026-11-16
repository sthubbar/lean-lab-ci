/-
An explicit majorant for the kernel mass in P0088 page 7 display 29.
It supplies concrete nonvacuity instances for the minor mean square theorem.
The bound has no logarithmic saving.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp556d

namespace LeanLab.KumchevLiu2007.Task634

open Real Complex MeasureTheory Task556a Task556d
open scoped BigOperators Topology

/-- P0088 page 7 display 29: the kernel mass is nonnegative and at most H
times the square of the number of frequencies. -/
theorem kernelMass_trivial_bounds (Y P H β : ℝ) (hH : 0 < H) :
    0 ≤ kernelMass Y H P β ∧
      kernelMass Y H P β ≤ H * ((squareWindow Y).card : ℝ) ^ 2 := by
  let s := Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H P)ᶜ
  have hs : MeasurableSet s :=
    measurableSet_Ioc.inter (measurableSet_majorArcs H P).compl
  have hf : Continuous (fun α : ℝ => ‖roughSum Y P α‖ ^ 2 * shortKernel H α β) :=
    (Eq33RouteB.continuous_roughSum_sq Y P).mul
      (Eq33RouteB.continuous_shortKernel hH β)
  have hi := hf.integrableOn_Ioc (μ := volume) (a := 0) (b := 1)
  have hsub : s ⊆ Set.Ioc (0 : ℝ) 1 := Set.inter_subset_left
  have hn (α : ℝ) : 0 ≤ ‖roughSum Y P α‖ ^ 2 * shortKernel H α β :=
    mul_nonneg (sq_nonneg _) (shortKernel_nonneg hH α β)
  constructor
  · exact setIntegral_nonneg hs fun α _ => hn α
  · change (∫ α in s, ‖roughSum Y P α‖ ^ 2 * shortKernel H α β) ≤ _
    have hconst := (continuous_const : Continuous
      (fun _ : ℝ => H * ((squareWindow Y).card : ℝ) ^ 2)).integrableOn_Ioc
        (μ := volume) (a := 0) (b := 1)
    calc
      _ ≤ ∫ _α in s, H * ((squareWindow Y).card : ℝ) ^ 2 := by
        apply setIntegral_mono_on (hi.mono_set hsub) (hconst.mono_set hsub) hs
        intro α hα
        have hc := roughSum_norm_le_card Y P α
        have hc0 : (0 : ℝ) ≤ (squareWindow Y).card := Nat.cast_nonneg _
        have hsq : ‖roughSum Y P α‖ ^ 2 ≤ ((squareWindow Y).card : ℝ) ^ 2 := by
          nlinarith [norm_nonneg (roughSum Y P α)]
        calc
          _ ≤ ((squareWindow Y).card : ℝ) ^ 2 * H :=
            mul_le_mul hsq (shortKernel_le hH α β)
              (shortKernel_nonneg hH α β) (sq_nonneg _)
          _ = _ := mul_comm _ _
      _ ≤ ∫ _α in Set.Ioc (0 : ℝ) 1, H * ((squareWindow Y).card : ℝ) ^ 2 :=
        setIntegral_mono_set hconst (Filter.Eventually.of_forall
          (fun _ => mul_nonneg hH.le (sq_nonneg _))) hsub.eventuallyLE
      _ = _ := by simp

end LeanLab.KumchevLiu2007.Task634

#print axioms LeanLab.KumchevLiu2007.Task634.kernelMass_trivial_bounds
