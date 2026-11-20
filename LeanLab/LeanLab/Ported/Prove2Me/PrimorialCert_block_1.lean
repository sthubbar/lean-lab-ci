/-
Ported from Prove2Me, mission 0814790f.
Source PrimorialCert_block_1. Author bwdaugherty. Apache 2.0.
Lean 4.33.1 source adapted for Lean 4.35.0.
Derived certificates for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ported.Prove2Me.Def_PrimorialCertData_1

namespace LeanLab.Ported.Prove2Me.Task664

open ThetaSieve
set_option maxRecDepth 100000


namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData1.q0 : (Seg.bok PrimData1.s0) = true := by decide +kernel
theorem PrimData1.q1 : (Seg.bok PrimData1.s1) = true := by decide +kernel
theorem PrimData1.q2 : (Seg.bok PrimData1.s2) = true := by decide +kernel
theorem PrimData1.q3 : (Seg.bok PrimData1.s3) = true := by decide +kernel
theorem PrimData1.q4 : (Seg.bok PrimData1.s4) = true := by decide +kernel
theorem PrimData1.q5 : (Seg.bok PrimData1.s5) = true := by decide +kernel
theorem PrimData1.q6 : (Seg.bok PrimData1.s6) = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem PrimorialCert.block_1 :
    (∀ s ∈ ThetaSieve.PrimData1.segs, (Seg.bok s) = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData1.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData1.segs, 16000001 < (Seg.L s) + 2 * (Seg.W s) → (Seg.hi' s) < ((Seg.L s) - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData1.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData1.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData1.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData1.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData1.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData1.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData1.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData1.q6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩

end LeanLab.Ported.Prove2Me.Task664

-- task664 axiom audit
#print axioms LeanLab.Ported.Prove2Me.Task664.ThetaSieve.PrimData1.q0
#print axioms LeanLab.Ported.Prove2Me.Task664.ThetaSieve.PrimData1.q1
#print axioms LeanLab.Ported.Prove2Me.Task664.ThetaSieve.PrimData1.q2
#print axioms LeanLab.Ported.Prove2Me.Task664.ThetaSieve.PrimData1.q3
#print axioms LeanLab.Ported.Prove2Me.Task664.ThetaSieve.PrimData1.q4
#print axioms LeanLab.Ported.Prove2Me.Task664.ThetaSieve.PrimData1.q5
#print axioms LeanLab.Ported.Prove2Me.Task664.ThetaSieve.PrimData1.q6
#print axioms LeanLab.Ported.Prove2Me.Task664.PrimorialCert.block_1
