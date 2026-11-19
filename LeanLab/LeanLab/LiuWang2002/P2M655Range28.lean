/-
Prove2Me mission 6d14203d. Shared certificate prefix for LL_Decomp551a.primorial_c5_upper_first.
Author bwdaugherty. Accepted 2026-11-17. Apache 2.0.
Source prove2me/LL_Decomp551a_primorial_c5_lower_first.lean and its three siblings.
This prefix ends after block 60 and suffices through 28000000.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Data00
import LeanLab.LiuWang2002.P2M655Data01
import LeanLab.LiuWang2002.P2M655Data02
import LeanLab.LiuWang2002.P2M655Data03
import LeanLab.LiuWang2002.P2M655Data04
import LeanLab.LiuWang2002.P2M655Data05
import LeanLab.LiuWang2002.P2M655Data06
import LeanLab.LiuWang2002.P2M655Data07
import LeanLab.LiuWang2002.P2M655Data08
import LeanLab.LiuWang2002.P2M655Data09
import LeanLab.LiuWang2002.P2M655Data10
import LeanLab.LiuWang2002.P2M655Data11
import LeanLab.LiuWang2002.P2M655Data12
import LeanLab.LiuWang2002.P2M655Data13
import LeanLab.LiuWang2002.P2M655Data14
import LeanLab.LiuWang2002.P2M655Data15
import LeanLab.LiuWang2002.P2M655Data16
import LeanLab.LiuWang2002.P2M655Data17
import LeanLab.LiuWang2002.P2M655Data18
import LeanLab.LiuWang2002.P2M655Data19
import LeanLab.LiuWang2002.P2M655Data20
import LeanLab.LiuWang2002.P2M655Data21
import LeanLab.LiuWang2002.P2M655Data22
import LeanLab.LiuWang2002.P2M655Data23
import LeanLab.LiuWang2002.P2M655Data24
import LeanLab.LiuWang2002.P2M655Data25
import LeanLab.LiuWang2002.P2M655Data26
import LeanLab.LiuWang2002.P2M655Data27
import LeanLab.LiuWang2002.P2M655Data28
import LeanLab.LiuWang2002.P2M655Data29
import LeanLab.LiuWang2002.P2M655Data30
import LeanLab.LiuWang2002.P2M655Data31
import LeanLab.LiuWang2002.P2M655Data32
import LeanLab.LiuWang2002.P2M655Data33
import LeanLab.LiuWang2002.P2M655Data34
import LeanLab.LiuWang2002.P2M655Data35
import LeanLab.LiuWang2002.P2M655Data36
import LeanLab.LiuWang2002.P2M655Data37
import LeanLab.LiuWang2002.P2M655Data38
import LeanLab.LiuWang2002.P2M655Data39
import LeanLab.LiuWang2002.P2M655Data40
import LeanLab.LiuWang2002.P2M655Data41
import LeanLab.LiuWang2002.P2M655Data42
import LeanLab.LiuWang2002.P2M655Data43
import LeanLab.LiuWang2002.P2M655Data44
import LeanLab.LiuWang2002.P2M655Data45
import LeanLab.LiuWang2002.P2M655Data46
import LeanLab.LiuWang2002.P2M655Data47
import LeanLab.LiuWang2002.P2M655Data48
import LeanLab.LiuWang2002.P2M655Data49
import LeanLab.LiuWang2002.P2M655Data50
import LeanLab.LiuWang2002.P2M655Data51
import LeanLab.LiuWang2002.P2M655Data52
import LeanLab.LiuWang2002.P2M655Data53
import LeanLab.LiuWang2002.P2M655Data54
import LeanLab.LiuWang2002.P2M655Data55
import LeanLab.LiuWang2002.P2M655Data56
import LeanLab.LiuWang2002.P2M655Data57
import LeanLab.LiuWang2002.P2M655Data58
import LeanLab.LiuWang2002.P2M655Data59
import LeanLab.LiuWang2002.P2M655Data60

namespace LeanLab.LiuWang2002.P2M655.Range28
open LeanLab.LiuWang2002.P2M655.ThetaSieve
namespace Certificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def PAll : List Seg := ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((PrimData0.segs ++ PrimData1.segs) ++ PrimData2.segs) ++ PrimData3.segs) ++ PrimData4.segs) ++ PrimData5.segs) ++ PrimData6.segs) ++ PrimData7.segs) ++ PrimData8.segs) ++ PrimData9.segs) ++ PrimData10.segs) ++ PrimData11.segs) ++ PrimData12.segs) ++ PrimData13.segs) ++ PrimData14.segs) ++ PrimData15.segs) ++ PrimData16.segs) ++ PrimData17.segs) ++ PrimData18.segs) ++ PrimData19.segs) ++ PrimData20.segs) ++ PrimData21.segs) ++ PrimData22.segs) ++ PrimData23.segs) ++ PrimData24.segs) ++ PrimData25.segs) ++ PrimData26.segs) ++ PrimData27.segs) ++ PrimData28.segs) ++ PrimData29.segs) ++ PrimData30.segs) ++ PrimData31.segs) ++ PrimData32.segs) ++ PrimData33.segs) ++ PrimData34.segs) ++ PrimData35.segs) ++ PrimData36.segs) ++ PrimData37.segs) ++ PrimData38.segs) ++ PrimData39.segs) ++ PrimData40.segs) ++ PrimData41.segs) ++ PrimData42.segs) ++ PrimData43.segs) ++ PrimData44.segs) ++ PrimData45.segs) ++ PrimData46.segs) ++ PrimData47.segs) ++ PrimData48.segs) ++ PrimData49.segs) ++ PrimData50.segs) ++ PrimData51.segs) ++ PrimData52.segs) ++ PrimData53.segs) ++ PrimData54.segs) ++ PrimData55.segs) ++ PrimData56.segs) ++ PrimData57.segs) ++ PrimData58.segs) ++ PrimData59.segs) ++ PrimData60.segs)

theorem PAll_bok : ∀ x ∈ PAll, (Seg.bok x) = true := by
  unfold PAll
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨checked00, checked01⟩, checked02⟩, checked03⟩, checked04⟩, checked05⟩, checked06⟩, checked07⟩, checked08⟩, checked09⟩, checked10⟩, checked11⟩, checked12⟩, checked13⟩, checked14⟩, checked15⟩, checked16⟩, checked17⟩, checked18⟩, checked19⟩, checked20⟩, checked21⟩, checked22⟩, checked23⟩, checked24⟩, checked25⟩, checked26⟩, checked27⟩, checked28⟩, checked29⟩, checked30⟩, checked31⟩, checked32⟩, checked33⟩, checked34⟩, checked35⟩, checked36⟩, checked37⟩, checked38⟩, checked39⟩, checked40⟩, checked41⟩, checked42⟩, checked43⟩, checked44⟩, checked45⟩, checked46⟩, checked47⟩, checked48⟩, checked49⟩, checked50⟩, checked51⟩, checked52⟩, checked53⟩, checked54⟩, checked55⟩, checked56⟩, checked57⟩, checked58⟩, checked59⟩, checked60⟩

theorem PAll_head : PAll = PrimData0.s0 :: PAll.tail := rfl
theorem PAll_s0 : (Seg.lo PrimData0.s0) = LLo 2 ∧ (Seg.hi PrimData0.s0) = LHi 2 ∧ (Seg.L PrimData0.s0) = 3 := by decide +kernel
theorem PAll_chain : chainOK PAll = true := by decide +kernel
theorem cval : LLo 68 - LHi 25 = 18458400208034708012 := by decide +kernel
theorem cpos : LHi 25 ≤ LLo 68 := by decide +kernel
theorem PAll_prim : ∀ x ∈ PAll, 16000001 < (Seg.L x) + 2 * (Seg.W x) → primOK (LLo 68 - LHi 25) x = true := by
  rw [cval]; decide +kernel
theorem PAll_end : 28000000 + 1 ≤ (Seg.L (chainEnd PrimData0.s0 PAll.tail)) + 2 * (Seg.W (chainEnd PrimData0.s0 PAll.tail)) := by decide +kernel

end Certificate

open Certificate in
theorem primorial_range (n : ℕ) (hn : 16000000 < n) (hn' : n ≤ 28000000) : primorial n * 25 ^ n < 68 ^ n := by
  have hok : ∀ x ∈ PrimData0.s0 :: PAll.tail, (Seg.bok x) = true := by rw [← PAll_head]; exact PAll_bok
  have hc : chainOK (PrimData0.s0 :: PAll.tail) = true := by rw [← PAll_head]; exact PAll_chain
  have hp : ∀ x ∈ PrimData0.s0 :: PAll.tail, 16000000 + 1 < (Seg.L x) + 2 * (Seg.W x) → primOK (LLo 68 - LHi 25) x = true := by
    rw [← PAll_head]; intro x hx h; exact PAll_prim x hx (by omega)
  exact primorial_range_of 16000000 28000000 PrimData0.s0 PAll.tail PAll_s0 hc hok hp PAll_end cpos (by norm_num) n hn hn'

end LeanLab.LiuWang2002.P2M655.Range28
#print axioms LeanLab.LiuWang2002.P2M655.Range28.Certificate.PAll_bok
#print axioms LeanLab.LiuWang2002.P2M655.Range28.Certificate.PAll_head
#print axioms LeanLab.LiuWang2002.P2M655.Range28.Certificate.PAll_s0
#print axioms LeanLab.LiuWang2002.P2M655.Range28.Certificate.PAll_chain
#print axioms LeanLab.LiuWang2002.P2M655.Range28.Certificate.cval
#print axioms LeanLab.LiuWang2002.P2M655.Range28.Certificate.cpos
#print axioms LeanLab.LiuWang2002.P2M655.Range28.Certificate.PAll_prim
#print axioms LeanLab.LiuWang2002.P2M655.Range28.Certificate.PAll_end
#print axioms LeanLab.LiuWang2002.P2M655.Range28.primorial_range
