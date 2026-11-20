/-
Ported from Prove2Me, mission 0814790f.
Theorem LL_Decomp368b.primorial_c4. Author kmehltretter82. Apache 2.0.
Lean 4.33.1 source adapted for Lean 4.35.0.
Derived certificates for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ported.Prove2Me.LL_Decomp368b_primorial_c3
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Zify
import LeanLab.Ported.Prove2Me.Def_ThetaCertCore
import LeanLab.Ported.Prove2Me.Def_PrimorialCertData_0
import LeanLab.Ported.Prove2Me.PrimorialCert_block_0
import LeanLab.Ported.Prove2Me.Def_PrimorialCertData_1
import LeanLab.Ported.Prove2Me.PrimorialCert_block_1
import LeanLab.Ported.Prove2Me.Def_PrimorialCertData_2
import LeanLab.Ported.Prove2Me.PrimorialCert_block_2
import LeanLab.Ported.Prove2Me.Def_PrimorialCertData_3
import LeanLab.Ported.Prove2Me.PrimorialCert_block_3
import LeanLab.Ported.Prove2Me.Def_PrimorialCertData_4
import LeanLab.Ported.Prove2Me.PrimorialCert_block_4
import LeanLab.Ported.Prove2Me.Def_PrimorialCertData_5
import LeanLab.Ported.Prove2Me.PrimorialCert_block_5
import LeanLab.Ported.Prove2Me.Def_PrimorialCertData_6
import LeanLab.Ported.Prove2Me.PrimorialCert_block_6
import LeanLab.Ported.Prove2Me.Def_PrimorialCertData_7
import LeanLab.Ported.Prove2Me.PrimorialCert_block_7
import LeanLab.Ported.Prove2Me.Def_PrimorialCertData_8
import LeanLab.Ported.Prove2Me.PrimorialCert_block_8

namespace LeanLab.Ported.Prove2Me.Task664


set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false

open Finset Real

namespace PrimC4Cert

open DusartCert ThetaSieve PrimC3Cert

/-! ## Part 5: Base state at 7,995,395 from `PrimorialCert.block_0..8` + kernel cert for `(8M, 16M]` -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def PPrefix : List Seg :=
  PrimData0.segs ++ PrimData1.segs ++ PrimData2.segs ++ PrimData3.segs ++
  PrimData4.segs ++ PrimData5.segs ++ PrimData6.segs ++ PrimData7.segs ++
  [PrimData8.s0, PrimData8.s1, PrimData8.s2, PrimData8.s3, PrimData8.s4]

lemma PPrefix_bok : ∀ x ∈ PPrefix, (Seg.bok x) = true := by
  unfold PPrefix
  have h8 : ∀ x ∈ [PrimData8.s0, PrimData8.s1, PrimData8.s2, PrimData8.s3, PrimData8.s4], (Seg.bok x) = true := by
    intro x hx
    exact (PrimorialCert.block_8).1 x (by
      unfold PrimData8.segs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> tauto)
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2
    ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2
    ⟨(PrimorialCert.block_0).1, (PrimorialCert.block_1).1⟩, (PrimorialCert.block_2).1⟩, (PrimorialCert.block_3).1⟩,
    (PrimorialCert.block_4).1⟩, (PrimorialCert.block_5).1⟩, (PrimorialCert.block_6).1⟩, (PrimorialCert.block_7).1⟩, h8⟩

lemma PPrefix_head : PPrefix = PrimData0.s0 :: PPrefix.tail := rfl
lemma PPrefix_s0 : (Seg.hi PrimData0.s0) = LHi 2 ∧ (Seg.L PrimData0.s0) = 3 := by decide +kernel
lemma PPrefix_chain : chainOK PPrefix = true := by decide +kernel
lemma PPrefix_end_eq :
    (Seg.hi' (chainEnd PrimData0.s0 PPrefix.tail)) = 147436398244268766209164068 ∧
    (Seg.L (chainEnd PrimData0.s0 PPrefix.tail)) + 2 * (Seg.W (chainEnd PrimData0.s0 PPrefix.tail)) = 7995395 := by
  decide +kernel

lemma hiInv_7995395 : ((Q : ℝ) * th ((7995395) - 1) ≤ (147436398244268766209164068 : ℝ)) := by
  have hI0 : ((Q : ℝ) * th (((Seg.L PrimData0.s0)) - 1) ≤ ((Seg.hi PrimData0.s0) : ℝ)) := by
    rw [PPrefix_s0.1, PPrefix_s0.2]; exact HiInv_three
  have hc : chainOK (PrimData0.s0 :: PPrefix.tail) = true := by rw [← PPrefix_head]; exact PPrefix_chain
  have hok : ∀ x ∈ PrimData0.s0 :: PPrefix.tail, (Seg.bok x) = true := by rw [← PPrefix_head]; exact PPrefix_bok
  have h := bchain_hi_sound PPrefix.tail PrimData0.s0 hc hok hI0
  rw [PPrefix_end_eq.1, PPrefix_end_eq.2] at h
  exact h

lemma cval : LLo 68 - LHi 25 = 18458400208034708012 := by decide +kernel
lemma cpos : LHi 25 ≤ LLo 68 := by decide +kernel

theorem cert_c4 :
    primChain 18458400208034708012 8000000 32 2048 62 7995395 147436398244268766209164068 = true := by
  decide +kernel

end PrimC4Cert

theorem LL_Decomp368b.primorial_c4 (n : ℕ) (hn : 8000000 < n) (hn' : n ≤ 16000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  have hQ := PrimC3Cert.primChain_sound 62 7995395 147436398244268766209164068
    PrimC4Cert.cert_c4 PrimC4Cert.hiInv_7995395 n hn (by omega) (by omega)
  have hcq := PrimC3Cert.c_le PrimC4Cert.cpos
  rw [PrimC4Cert.cval] at hcq
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h2 : (ThetaSieve.Q : ℝ) * PrimC3Cert.th n < ThetaSieve.Q * (n * Real.log (68 / 25)) := by
    calc (ThetaSieve.Q : ℝ) * PrimC3Cert.th n < (n : ℝ) * (18458400208034708012 : ℕ) := hQ
      _ ≤ (n : ℝ) * (ThetaSieve.Q * Real.log (68 / 25)) := mul_le_mul_of_nonneg_left hcq hn0
      _ = ThetaSieve.Q * (n * Real.log (68 / 25)) := by ring
  exact PrimC3Cert.primorial_of_theta n (by omega) (lt_of_mul_lt_mul_left h2 (le_of_lt PrimC3Cert.Q_pos))

end LeanLab.Ported.Prove2Me.Task664

-- task664 axiom audit
#print axioms LeanLab.Ported.Prove2Me.Task664.PrimC4Cert.PPrefix_bok
#print axioms LeanLab.Ported.Prove2Me.Task664.PrimC4Cert.PPrefix_head
#print axioms LeanLab.Ported.Prove2Me.Task664.PrimC4Cert.PPrefix_s0
#print axioms LeanLab.Ported.Prove2Me.Task664.PrimC4Cert.PPrefix_chain
#print axioms LeanLab.Ported.Prove2Me.Task664.PrimC4Cert.PPrefix_end_eq
#print axioms LeanLab.Ported.Prove2Me.Task664.PrimC4Cert.hiInv_7995395
#print axioms LeanLab.Ported.Prove2Me.Task664.PrimC4Cert.cval
#print axioms LeanLab.Ported.Prove2Me.Task664.PrimC4Cert.cpos
#print axioms LeanLab.Ported.Prove2Me.Task664.PrimC4Cert.cert_c4
#print axioms LeanLab.Ported.Prove2Me.Task664.LL_Decomp368b.primorial_c4
