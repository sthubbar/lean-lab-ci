/-
P0070, page 359, equation 7. This is an elementary audit of the missing logarithmic saving.
The Parseval bound alone does not establish Estimate7Wide.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.Decomp1519
import LeanLab.PerelliPintz1992.MainAssembly

namespace LeanLab.PerelliPintz1992.Task76
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992

/-- Every minor arc window is bounded by the full Parseval mean square. -/
theorem minor_window_parseval_bound {N : ℕ} (hN : 2 ≤ N) (A ξ w : ℝ) :
    (∫ α in Ioo (ξ-w) (ξ+w) ∩ minorArcs N A, ‖S N α‖^2) ≤ 8*N*L N^2 := by
  let c : ℝ := 1/((N : ℝ)^(1/2 : ℝ)/2)
  have hsub : Ioo (ξ-w) (ξ+w) ∩ minorArcs N A ⊆ Ioc c (c+1) := by
    intro x hx
    have hI : x ∈ Ioo c (1+c) := hx.2.1
    exact ⟨hI.1,by linarith [hI.2]⟩
  have hi : IntegrableOn (fun α => ‖S N α‖^2) (Ioc c (c+1)) :=
    ((continuous_S N).norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hb := setIntegral_mono_set hi (Eventually.of_forall (fun α => sq_nonneg ‖S N α‖))
    (Eventually.of_forall hsub)
  rw [parseval_T] at hb
  exact hb.trans (psi0_le hN)

/-- The elementary Parseval envelope is larger than every logarithmically saved target.
This compares bounds and makes no lower bound claim about the actual minor arc integral. -/
theorem parseval_envelope_exceeds_target (A C : ℝ) (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop, C*N/L N^(A+1) < 8*N*L N^2 := by
  have hlog : Tendsto (fun N : ℕ => L N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_gt_atTop (max C 1), eventually_ge_atTop 2] with N hL hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL1 : 1 ≤ L N := le_trans (le_max_right _ _) hL.le
  have hLC : C < L N := lt_of_le_of_lt (le_max_left _ _) hL
  have hpow : 1 ≤ L N^(A+1) := Real.one_le_rpow hL1 (by linarith)
  have hLp : 0 < L N^(A+1) := Real.rpow_pos_of_pos (by linarith) _
  rw [div_lt_iff₀ hLp]
  have hbase : C < 8*L N^2 := by nlinarith
  have hCN : C*(N : ℝ) < 8*N*L N^2 := by nlinarith [mul_pos hNp (sub_pos.mpr hbase)]
  have hlarge := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 8*(N : ℝ)*L N^2 by positivity)
  exact hCN.trans_le (by simpa only [mul_one] using hlarge)

end LeanLab.PerelliPintz1992.Task76
