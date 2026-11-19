/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_41.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/0d42b0d3-e209-4c83-b443-6ea23a5c3820
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData41.s0 : Seg := ⟨414082858193282298534260007, 414082858193282306386705667, 22454275, 4096, [], 414235861296060464495522991, 414235861296060472350869407⟩
def PrimData41.s1 : Seg := ⟨414235861296060464495522991, 414235861296060472350869407, 22462467, 4096, [], 414389492244203398967135109, 414389492244203406825394333⟩
def PrimData41.s2 : Seg := ⟨414389492244203398967135109, 414389492244203406825394333, 22470659, 4096, [], 414540003875994454460818913, 414540003875994462321932008⟩
def PrimData41.s3 : Seg := ⟨414540003875994454460818913, 414540003875994462321932008, 22478851, 4096, [], 414693953726901518893315265, 414693953726901526757346953⟩
def PrimData41.s4 : Seg := ⟨414693953726901518893315265, 414693953726901526757346953, 22487043, 4096, [], 414840099902945392725268456, 414840099902945400592069772⟩
def PrimData41.s5 : Seg := ⟨414840099902945392725268456, 414840099902945400592069772, 22495235, 4096, [], 414993744044393961571371543, 414993744044393969441084956⟩
def PrimData41.s6 : Seg := ⟨414993744044393961571371543, 414993744044393969441084956, 22503427, 4096, [], 415140208781181246801662125, 415140208781181254674151967⟩
def PrimData41.s7 : Seg := ⟨415140208781181246801662125, 415140208781181254674151967, 22511619, 4096, [], 415294171813480427906527394, 415294171813480435781936379⟩
def PrimData41.s8 : Seg := ⟨415294171813480427906527394, 415294171813480435781936379, 22519811, 4096, [], 415449387381402513870324882, 415449387381402521748676827⟩
def PrimData41.s9 : Seg := ⟨415449387381402513870324882, 415449387381402521748676827, 22528003, 4096, [], 415603981709518047860068425, 415603981709518055741351364⟩
def PrimData41.s10 : Seg := ⟨415603981709518047860068425, 415603981709518055741351364, 22536195, 4096, [], 415754519162896387147087160, 415754519162896395031224295⟩
def PrimData41.s11 : Seg := ⟨415754519162896387147087160, 415754519162896395031224295, 22544387, 4096, [], 415908183099912399472138370, 415908183099912407359189665⟩
def PrimData41.s12 : Seg := ⟨415908183099912399472138370, 415908183099912407359189665, 22552579, 4096, [], 416061850341406876949787028, 416061850341406884839753009⟩
def PrimData41.s13 : Seg := ⟨416061850341406876949787028, 416061850341406884839753009, 22560771, 4096, [], 416217082638658004401660775, 416217082638658012294571772⟩
def PrimData41.s14 : Seg := ⟨416217082638658004401660775, 416217082638658012294571772, 22568963, 4096, [], 416368570068867614919194764, 416368570068867622814980134⟩
def PrimData41.s15 : Seg := ⟨416368570068867614919194764, 416368570068867622814980134, 22577155, 4096, [], 416519748431129262320079750, 416519748431129270218732511⟩
def PrimData41.s16 : Seg := ⟨416519748431129262320079750, 416519748431129270218732511, 22585347, 4096, [], 416675615373102657309924855, 416675615373102665211534576⟩
def PrimData41.s17 : Seg := ⟨416675615373102657309924855, 416675615373102665211534576, 22593539, 4096, [], 416823051795814744254631712, 416823051795814752159038256⟩
def PrimData41.s18 : Seg := ⟨416823051795814744254631712, 416823051795814752159038256, 22601731, 4096, [], 416972365628077619843441729, 416972365628077627750680094⟩
def PrimData41.s19 : Seg := ⟨416972365628077619843441729, 416972365628077627750680094, 22609923, 4096, [], 417120120748269450050528666, 417120120748269457960569692⟩
def PrimData41.s20 : Seg := ⟨417120120748269450050528666, 417120120748269457960569692, 22618115, 4096, [], 417282248705638323927290883, 417282248705638331840407704⟩
def PrimData41.s21 : Seg := ⟨417282248705638323927290883, 417282248705638331840407704, 22626307, 4096, [], 417435008391147526054289215, 417435008391147533970302537⟩
def PrimData41.s22 : Seg := ⟨417435008391147526054289215, 417435008391147533970302537, 22634499, 4096, [], 417575900185409129701666692, 417575900185409137620353395⟩
def PrimData41.s23 : Seg := ⟨417575900185409129701666692, 417575900185409137620353395, 22642691, 4096, [], 417723980350304774976543794, 417723980350304782898039734⟩
def PrimData41.s24 : Seg := ⟨417723980350304774976543794, 417723980350304782898039734, 22650883, 4096, [], 417872376043385667319478483, 417872376043385675243788562⟩
def PrimData41.s25 : Seg := ⟨417872376043385667319478483, 417872376043385675243788562, 22659075, 4096, [], 418028272960112589089662766, 418028272960112597016929387⟩
def PrimData41.s26 : Seg := ⟨418028272960112589089662766, 418028272960112597016929387, 22667267, 4096, [], 418173550766587315862514387, 418173550766587323792535411⟩
def PrimData41.s27 : Seg := ⟨418173550766587315862514387, 418173550766587323792535411, 22675459, 4096, [], 418330079116869252009052441, 418330079116869259942041729⟩
def PrimData41.s28 : Seg := ⟨418330079116869252009052441, 418330079116869259942041729, 22683651, 4096, [], 418483486527106490664514406, 418483486527106498600412889⟩
def PrimData41.s29 : Seg := ⟨418483486527106490664514406, 418483486527106498600412889, 22691843, 4096, [], 418643770999159645031662592, 418643770999159652970599647⟩
def PrimData41.s30 : Seg := ⟨418643770999159645031662592, 418643770999159652970599647, 22700035, 4096, [], 418792810634697233442535038, 418792810634697241384298680⟩
def PrimData41.s31 : Seg := ⟨418792810634697233442535038, 418792810634697241384298680, 22708227, 4096, [], 418946540273627991842332898, 418946540273627999787011289⟩
def PrimData41.s32 : Seg := ⟨418946540273627991842332898, 418946540273627999787011289, 22716419, 4096, [], 419094648850221600843244879, 419094648850221608790731561⟩
def PrimData41.s33 : Seg := ⟨419094648850221600843244879, 419094648850221608790731561, 22724611, 4096, [], 419247135201992217625142490, 419247135201992225575521799⟩
def PrimData41.s34 : Seg := ⟨419247135201992217625142490, 419247135201992225575521799, 22732803, 4096, [], 419402124588824740579115472, 419402124588824748532434272⟩

def PrimData41.segs : List Seg := [PrimData41.s0, PrimData41.s1, PrimData41.s2, PrimData41.s3, PrimData41.s4, PrimData41.s5, PrimData41.s6, PrimData41.s7, PrimData41.s8, PrimData41.s9, PrimData41.s10, PrimData41.s11, PrimData41.s12, PrimData41.s13, PrimData41.s14, PrimData41.s15, PrimData41.s16, PrimData41.s17, PrimData41.s18, PrimData41.s19, PrimData41.s20, PrimData41.s21, PrimData41.s22, PrimData41.s23, PrimData41.s24, PrimData41.s25, PrimData41.s26, PrimData41.s27, PrimData41.s28, PrimData41.s29, PrimData41.s30, PrimData41.s31, PrimData41.s32, PrimData41.s33, PrimData41.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked41_s0 : Seg.bok PrimData41.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s0

theorem checked41_s1 : Seg.bok PrimData41.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s1

theorem checked41_s2 : Seg.bok PrimData41.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s2

theorem checked41_s3 : Seg.bok PrimData41.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s3

theorem checked41_s4 : Seg.bok PrimData41.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s4

theorem checked41_s5 : Seg.bok PrimData41.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s5

theorem checked41_s6 : Seg.bok PrimData41.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s6

theorem checked41_s7 : Seg.bok PrimData41.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s7

theorem checked41_s8 : Seg.bok PrimData41.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s8

theorem checked41_s9 : Seg.bok PrimData41.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s9

theorem checked41_s10 : Seg.bok PrimData41.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s10

theorem checked41_s11 : Seg.bok PrimData41.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s11

theorem checked41_s12 : Seg.bok PrimData41.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s12

theorem checked41_s13 : Seg.bok PrimData41.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s13

theorem checked41_s14 : Seg.bok PrimData41.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s14

theorem checked41_s15 : Seg.bok PrimData41.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s15

theorem checked41_s16 : Seg.bok PrimData41.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s16

theorem checked41_s17 : Seg.bok PrimData41.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s17

theorem checked41_s18 : Seg.bok PrimData41.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s18

theorem checked41_s19 : Seg.bok PrimData41.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s19

theorem checked41_s20 : Seg.bok PrimData41.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s20

theorem checked41_s21 : Seg.bok PrimData41.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s21

theorem checked41_s22 : Seg.bok PrimData41.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s22

theorem checked41_s23 : Seg.bok PrimData41.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s23

theorem checked41_s24 : Seg.bok PrimData41.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s24

theorem checked41_s25 : Seg.bok PrimData41.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s25

theorem checked41_s26 : Seg.bok PrimData41.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s26

theorem checked41_s27 : Seg.bok PrimData41.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s27

theorem checked41_s28 : Seg.bok PrimData41.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s28

theorem checked41_s29 : Seg.bok PrimData41.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s29

theorem checked41_s30 : Seg.bok PrimData41.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s30

theorem checked41_s31 : Seg.bok PrimData41.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s31

theorem checked41_s32 : Seg.bok PrimData41.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s32

theorem checked41_s33 : Seg.bok PrimData41.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s33

theorem checked41_s34 : Seg.bok PrimData41.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41_s34

 theorem checked41 : ∀ s ∈ PrimData41.segs, (Seg.bok s) = true := by
  unfold PrimData41.segs
  exact List.forall_mem_cons.2 ⟨checked41_s0, List.forall_mem_cons.2 ⟨checked41_s1, List.forall_mem_cons.2 ⟨checked41_s2, List.forall_mem_cons.2 ⟨checked41_s3, List.forall_mem_cons.2 ⟨checked41_s4, List.forall_mem_cons.2 ⟨checked41_s5, List.forall_mem_cons.2 ⟨checked41_s6, List.forall_mem_cons.2 ⟨checked41_s7, List.forall_mem_cons.2 ⟨checked41_s8, List.forall_mem_cons.2 ⟨checked41_s9, List.forall_mem_cons.2 ⟨checked41_s10, List.forall_mem_cons.2 ⟨checked41_s11, List.forall_mem_cons.2 ⟨checked41_s12, List.forall_mem_cons.2 ⟨checked41_s13, List.forall_mem_cons.2 ⟨checked41_s14, List.forall_mem_cons.2 ⟨checked41_s15, List.forall_mem_cons.2 ⟨checked41_s16, List.forall_mem_cons.2 ⟨checked41_s17, List.forall_mem_cons.2 ⟨checked41_s18, List.forall_mem_cons.2 ⟨checked41_s19, List.forall_mem_cons.2 ⟨checked41_s20, List.forall_mem_cons.2 ⟨checked41_s21, List.forall_mem_cons.2 ⟨checked41_s22, List.forall_mem_cons.2 ⟨checked41_s23, List.forall_mem_cons.2 ⟨checked41_s24, List.forall_mem_cons.2 ⟨checked41_s25, List.forall_mem_cons.2 ⟨checked41_s26, List.forall_mem_cons.2 ⟨checked41_s27, List.forall_mem_cons.2 ⟨checked41_s28, List.forall_mem_cons.2 ⟨checked41_s29, List.forall_mem_cons.2 ⟨checked41_s30, List.forall_mem_cons.2 ⟨checked41_s31, List.forall_mem_cons.2 ⟨checked41_s32, List.forall_mem_cons.2 ⟨checked41_s33, List.forall_mem_singleton.2 checked41_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked41
