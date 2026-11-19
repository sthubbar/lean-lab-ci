/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_2.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/fc6703d4-a5c0-40ee-9c4a-341e9e259640
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData2.s0 : Seg := ⟨33822898766633561946684472, 33822898766633562588072272, 1835011, 65536, [], 36244736439612024432094106, 36244736439612025119404726⟩
def PrimData2.s1 : Seg := ⟨36244736439612024432094106, 36244736439612025119404726, 1966083, 65536, [], 38657649809743840824688834, 38657649809743841557732323⟩
def PrimData2.s2 : Seg := ⟨38657649809743840824688834, 38657649809743841557732323, 2097155, 65536, [], 41075832242750600004543720, 41075832242750600783469637⟩
def PrimData2.s3 : Seg := ⟨41075832242750600004543720, 41075832242750600783469637, 2228227, 65536, [], 43484589193291898634853182, 43484589193291899459455329⟩
def PrimData2.s4 : Seg := ⟨43484589193291898634853182, 43484589193291899459455329, 2359299, 65536, [], 45899786807720768217807465, 45899786807720769088206278⟩
def PrimData2.s5 : Seg := ⟨45899786807720768217807465, 45899786807720769088206278, 2490371, 65536, [], 48318737117885074966074576, 48318737117885075882345363⟩
def PrimData2.s6 : Seg := ⟨48318737117885074966074576, 48318737117885075882345363, 2621443, 65536, [], 50738232456578986518095520, 50738232456578987480247599⟩

def PrimData2.segs : List Seg := [PrimData2.s0, PrimData2.s1, PrimData2.s2, PrimData2.s3, PrimData2.s4, PrimData2.s5, PrimData2.s6]

end ThetaSieve


namespace ThetaSieve
theorem checked02_s0 : Seg.bok PrimData2.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked02_s0

theorem checked02_s1 : Seg.bok PrimData2.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked02_s1

theorem checked02_s2 : Seg.bok PrimData2.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked02_s2

theorem checked02_s3 : Seg.bok PrimData2.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked02_s3

theorem checked02_s4 : Seg.bok PrimData2.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked02_s4

theorem checked02_s5 : Seg.bok PrimData2.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked02_s5

theorem checked02_s6 : Seg.bok PrimData2.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked02_s6

 theorem checked02 : ∀ s ∈ PrimData2.segs, (Seg.bok s) = true := by
  unfold PrimData2.segs
  exact List.forall_mem_cons.2 ⟨checked02_s0, List.forall_mem_cons.2 ⟨checked02_s1, List.forall_mem_cons.2 ⟨checked02_s2, List.forall_mem_cons.2 ⟨checked02_s3, List.forall_mem_cons.2 ⟨checked02_s4, List.forall_mem_cons.2 ⟨checked02_s5, List.forall_mem_singleton.2 checked02_s6⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked02
