import LeanLab.ChenDoubleSieve.I1Tail
import LeanLab.ChenDoubleSieve.ReducedCertificate

/-!
# Certified tail saving at the Table 1 parameter pairs

Source: https://arxiv.org/pdf/0705.1652, page 22 and Table 1 on page 30.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxRecDepth 100000
noncomputable section
namespace LeanLab.ChenDoubleSieve.Wu04I1
open Wu04Reduced (tableS tableSp volumeHi reducedVolume)
open Wu04Integral (logLowerQ logLowerQ_cast logLower)

def subVolumeLo : Fin 5 → ℚ := ![3018367278/1000000000000, 1658715230/1000000000000, 653006151/1000000000000, 119408116/1000000000000, 0/1000000000000]
def upperI1Tail : Fin 5 → ℚ := ![9457279894/1000000000000, 4575179859/1000000000000, 1585855753/1000000000000, 248836559/1000000000000, 0/1000000000000]

theorem tail_parameters : ∀ i : Fin 5, tableS i ≤ 3 ∧ 3 ≤ tableSp i := by decide +kernel

theorem subVolume_certificate : ∀ i : Fin 5,
    subVolumeLo i ≤ (tableSp i+3)*logLowerQ 16 (tableSp i/3)-2*(tableSp i-3) := by decide +kernel

theorem subVolume_lower (i : Fin 5) :
    (subVolumeLo i : ℝ) ≤ reducedVolume (1/(tableSp i : ℝ)) (1/3) := by
  have hp : (3 : ℝ) ≤ tableSp i := by exact_mod_cast (tail_parameters i).2
  rw [Wu04Reduced.reducedVolume_parameters (by norm_num : (0 : ℝ) < 3) hp]
  have hlog := (Wu04Integral.log_bounds 16 (y := (tableSp i : ℝ)/3)
    ((le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr (by simpa using hp))).1
  have hq : (subVolumeLo i : ℝ) ≤
      (((tableSp i+3)*logLowerQ 16 (tableSp i/3)-2*(tableSp i-3) : ℚ) : ℝ) := by
    exact_mod_cast subVolume_certificate i
  push_cast at hq
  rw [logLowerQ_cast] at hq
  push_cast at hq
  exact hq.trans (sub_le_sub_right (mul_le_mul_of_nonneg_left hlog (by linarith)) _)

theorem upperI1Tail_certificate : ∀ i : Fin 5,
    (5671433/10000000 : ℚ)*volumeHi i - (11433/10000000 : ℚ)*subVolumeLo i ≤ upperI1Tail i := by
  decide +kernel

/-- Certified improved I1 upper bounds, CONDITIONAL ON IsBuchstab only. -/
theorem I1_table_upper_tail {ω : ℝ → ℝ} (hω : Wu04Functional.IsBuchstab ω) (i : Fin 5) :
    Wu04Functional.I1 ω (tableS i : ℝ) (tableSp i : ℝ) ≤ (upperI1Tail i : ℝ) := by
  have hs : (5/2 : ℝ) ≤ tableS i := by
    have hh : ((5/2 : ℚ) : ℝ) ≤ (tableS i : ℝ) := by exact_mod_cast (numerical_parameters i).1
    push_cast at hh
    exact hh
  have hs3 : (tableS i : ℝ) ≤ 3 := by exact_mod_cast (tail_parameters i).1
  have hp3 : (3 : ℝ) ≤ tableSp i := by exact_mod_cast (tail_parameters i).2
  have hp : (0 : ℝ) < tableSp i := by linarith
  have hsp : (tableS i : ℝ) ≤ tableSp i := by exact_mod_cast (numerical_parameters i).2.2
  have hi := I1_le_tail hω hs hs3 hp
  rw [reciprocal_reduction (by linarith : (0 : ℝ) < tableS i) hsp,
    reciprocal_reduction (by norm_num : (0 : ℝ) < 3) hp3] at hi
  have hv := (Wu04Reduced.reducedTable_bounds i).2
  have hw := subVolume_lower i
  have hc1 := mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 5671433/10000000)
  have hc2 := mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 11433/10000000)
  have hb : (5671433/10000000 : ℝ)*(volumeHi i : ℝ) -
      (11433/10000000 : ℝ)*(subVolumeLo i : ℝ) ≤ (upperI1Tail i : ℝ) := by
    have hh : (((5671433/10000000 : ℚ)*volumeHi i - (11433/10000000 : ℚ)*subVolumeLo i : ℚ) : ℝ) ≤ (upperI1Tail i : ℝ) := by
      exact_mod_cast upperI1Tail_certificate i
    push_cast at hh
    exact hh
  linarith

end LeanLab.ChenDoubleSieve.Wu04I1

#print axioms LeanLab.ChenDoubleSieve.Wu04I1.tail_parameters

#print axioms LeanLab.ChenDoubleSieve.Wu04I1.subVolume_certificate

#print axioms LeanLab.ChenDoubleSieve.Wu04I1.subVolume_lower

#print axioms LeanLab.ChenDoubleSieve.Wu04I1.upperI1Tail_certificate

#print axioms LeanLab.ChenDoubleSieve.Wu04I1.I1_table_upper_tail
