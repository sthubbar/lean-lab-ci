/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_67.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/6ba8f457-5b03-4ab1-963b-1f01bc98a902
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData67.s0 : Seg := ⟨551607503847923806151755934, 551607503847923816612086999, 29908995, 4096, [], 551758334705560370709436637, 551758334705560381172628180⟩
def PrimData67.s1 : Seg := ⟨551758334705560370709436637, 551758334705560381172628180, 29917187, 4096, [], 551911708292476656858033710, 551911708292476667324135058⟩
def PrimData67.s2 : Seg := ⟨551911708292476656858033710, 551911708292476667324135058, 29925379, 4096, [], 552064766820361533114113557, 552064766820361543583117183⟩
def PrimData67.s3 : Seg := ⟨552064766820361533114113557, 552064766820361543583117183, 29933571, 4096, [], 552223226178279791709898737, 552223226178279802181907193⟩
def PrimData67.s4 : Seg := ⟨552223226178279791709898737, 552223226178279802181907193, 29941763, 4096, [], 552381052911416950977746813, 552381052911416961452749158⟩
def PrimData67.s5 : Seg := ⟨552381052911416950977746813, 552381052911416961452749158, 29949955, 4096, [], 552531578192531590972532427, 552531578192531601450389182⟩
def PrimData67.s6 : Seg := ⟨552531578192531590972532427, 552531578192531601450389182, 29958147, 4096, [], 552679565367560964118424814, 552679565367560974599087621⟩
def PrimData67.s7 : Seg := ⟨552679565367560964118424814, 552679565367560974599087621, 29966339, 4096, [], 552834859061463910836578324, 552834859061463921320186184⟩
def PrimData67.s8 : Seg := ⟨552834859061463910836578324, 552834859061463921320186184, 29974531, 4096, [], 552981580556355374539929321, 552981580556355385026319187⟩
def PrimData67.s9 : Seg := ⟨552981580556355374539929321, 552981580556355385026319187, 29982723, 4096, [], 553141007745808837995311016, 553141007745808848484724908⟩
def PrimData67.s10 : Seg := ⟨553141007745808837995311016, 553141007745808848484724908, 29990915, 4096, [], 553291862591272065470241528, 553291862591272075962516879⟩
def PrimData67.s11 : Seg := ⟨553291862591272065470241528, 553291862591272075962516879, 29999107, 4096, [], 553445260587994460176538790, 553445260587994470671723251⟩
def PrimData67.s12 : Seg := ⟨553445260587994460176538790, 553445260587994470671723251, 30007299, 4096, [], 553600249011934561242463149, 553600249011934571740586375⟩
def PrimData67.s13 : Seg := ⟨553600249011934561242463149, 553600249011934571740586375, 30015491, 4096, [], 553756192690160984829500135, 553756192690160995330580368⟩
def PrimData67.s14 : Seg := ⟨553756192690160984829500135, 553756192690160995330580368, 30023683, 4096, [], 553908009970303018588051993, 553908009970303029092011683⟩
def PrimData67.s15 : Seg := ⟨553908009970303018588051993, 553908009970303029092011683, 30031875, 4096, [], 554054747783117252098672775, 554054747783117262605414740⟩
def PrimData67.s16 : Seg := ⟨554054747783117252098672775, 554054747783117262605414740, 30040067, 4096, [], 554208157909529559886999081, 554208157909529570396648283⟩
def PrimData67.s17 : Seg := ⟨554208157909529559886999081, 554208157909529570396648283, 30048259, 4096, [], 554352359378640507082311349, 554352359378640517594694264⟩
def PrimData67.s18 : Seg := ⟨554352359378640507082311349, 554352359378640517594694264, 30056451, 4096, [], 554508950633364500891931263, 554508950633364511407282657⟩
def PrimData67.s19 : Seg := ⟨554508950633364500891931263, 554508950633364511407282657, 30064643, 4096, [], 554658238785569293961257507, 554658238785569304479439091⟩
def PrimData67.s20 : Seg := ⟨554658238785569293961257507, 554658238785569304479439091, 30072835, 4096, [], 554816423246131209284134453, 554816423246131219805316030⟩
def PrimData67.s21 : Seg := ⟨554816423246131209284134453, 554816423246131219805316030, 30081027, 4096, [], 554976198398454815157865323, 554976198398454825682077325⟩
def PrimData67.s22 : Seg := ⟨554976198398454815157865323, 554976198398454825682077325, 30089219, 4096, [], 555121999497233511858165072, 555121999497233522385141867⟩
def PrimData67.s23 : Seg := ⟨555121999497233511858165072, 555121999497233522385141867, 30097411, 4096, [], 555268120543246568085199132, 555268120543246578614946034⟩
def PrimData67.s24 : Seg := ⟨555268120543246568085199132, 555268120543246578614946034, 30105603, 4096, [], 555417738158753474811827023, 555417738158753485344410404⟩
def PrimData67.s25 : Seg := ⟨555417738158753474811827023, 555417738158753485344410404, 30113795, 4096, [], 555570217157487251778346038, 555570217157487262313819240⟩
def PrimData67.s26 : Seg := ⟨555570217157487251778346038, 555570217157487262313819240, 30121987, 4096, [], 555722698578207811983202034, 555722698578207822521566064⟩
def PrimData67.s27 : Seg := ⟨555722698578207811983202034, 555722698578207822521566064, 30130179, 4096, [], 555877088387597110074045346, 555877088387597120615336621⟩
def PrimData67.s28 : Seg := ⟨555877088387597110074045346, 555877088387597120615336621, 30138371, 4096, [], 556035292843019888062911109, 556035292843019898607201804⟩
def PrimData67.s29 : Seg := ⟨556035292843019888062911109, 556035292843019898607201804, 30146563, 4096, [], 556184286910502394862525412, 556184286910502405409641735⟩
def PrimData67.s30 : Seg := ⟨556184286910502394862525412, 556184286910502405409641735, 30154755, 4096, [], 556330741801719969397651891, 556330741801719979947545560⟩
def PrimData67.s31 : Seg := ⟨556330741801719969397651891, 556330741801719979947545560, 30162947, 4096, [], 556477199036276784270911451, 556477199036276794823582219⟩
def PrimData67.s32 : Seg := ⟨556477199036276784270911451, 556477199036276794823582219, 30171139, 4096, [], 556632236451001369541409754, 556632236451001380097020250⟩
def PrimData67.s33 : Seg := ⟨556632236451001369541409754, 556632236451001380097020250, 30179331, 4096, [], 556784416995611754434660631, 556784416995611764993156236⟩
def PrimData67.s34 : Seg := ⟨556784416995611754434660631, 556784416995611764993156236, 30187523, 4096, [], 556934058246432488492067130, 556934058246432499053399250⟩

def PrimData67.segs : List Seg := [PrimData67.s0, PrimData67.s1, PrimData67.s2, PrimData67.s3, PrimData67.s4, PrimData67.s5, PrimData67.s6, PrimData67.s7, PrimData67.s8, PrimData67.s9, PrimData67.s10, PrimData67.s11, PrimData67.s12, PrimData67.s13, PrimData67.s14, PrimData67.s15, PrimData67.s16, PrimData67.s17, PrimData67.s18, PrimData67.s19, PrimData67.s20, PrimData67.s21, PrimData67.s22, PrimData67.s23, PrimData67.s24, PrimData67.s25, PrimData67.s26, PrimData67.s27, PrimData67.s28, PrimData67.s29, PrimData67.s30, PrimData67.s31, PrimData67.s32, PrimData67.s33, PrimData67.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked67_s0 : Seg.bok PrimData67.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s0

theorem checked67_s1 : Seg.bok PrimData67.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s1

theorem checked67_s2 : Seg.bok PrimData67.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s2

theorem checked67_s3 : Seg.bok PrimData67.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s3

theorem checked67_s4 : Seg.bok PrimData67.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s4

theorem checked67_s5 : Seg.bok PrimData67.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s5

theorem checked67_s6 : Seg.bok PrimData67.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s6

theorem checked67_s7 : Seg.bok PrimData67.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s7

theorem checked67_s8 : Seg.bok PrimData67.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s8

theorem checked67_s9 : Seg.bok PrimData67.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s9

theorem checked67_s10 : Seg.bok PrimData67.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s10

theorem checked67_s11 : Seg.bok PrimData67.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s11

theorem checked67_s12 : Seg.bok PrimData67.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s12

theorem checked67_s13 : Seg.bok PrimData67.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s13

theorem checked67_s14 : Seg.bok PrimData67.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s14

theorem checked67_s15 : Seg.bok PrimData67.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s15

theorem checked67_s16 : Seg.bok PrimData67.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s16

theorem checked67_s17 : Seg.bok PrimData67.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s17

theorem checked67_s18 : Seg.bok PrimData67.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s18

theorem checked67_s19 : Seg.bok PrimData67.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s19

theorem checked67_s20 : Seg.bok PrimData67.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s20

theorem checked67_s21 : Seg.bok PrimData67.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s21

theorem checked67_s22 : Seg.bok PrimData67.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s22

theorem checked67_s23 : Seg.bok PrimData67.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s23

theorem checked67_s24 : Seg.bok PrimData67.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s24

theorem checked67_s25 : Seg.bok PrimData67.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s25

theorem checked67_s26 : Seg.bok PrimData67.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s26

theorem checked67_s27 : Seg.bok PrimData67.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s27

theorem checked67_s28 : Seg.bok PrimData67.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s28

theorem checked67_s29 : Seg.bok PrimData67.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s29

theorem checked67_s30 : Seg.bok PrimData67.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s30

theorem checked67_s31 : Seg.bok PrimData67.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s31

theorem checked67_s32 : Seg.bok PrimData67.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s32

theorem checked67_s33 : Seg.bok PrimData67.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s33

theorem checked67_s34 : Seg.bok PrimData67.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67_s34

 theorem checked67 : ∀ s ∈ PrimData67.segs, (Seg.bok s) = true := by
  unfold PrimData67.segs
  exact List.forall_mem_cons.2 ⟨checked67_s0, List.forall_mem_cons.2 ⟨checked67_s1, List.forall_mem_cons.2 ⟨checked67_s2, List.forall_mem_cons.2 ⟨checked67_s3, List.forall_mem_cons.2 ⟨checked67_s4, List.forall_mem_cons.2 ⟨checked67_s5, List.forall_mem_cons.2 ⟨checked67_s6, List.forall_mem_cons.2 ⟨checked67_s7, List.forall_mem_cons.2 ⟨checked67_s8, List.forall_mem_cons.2 ⟨checked67_s9, List.forall_mem_cons.2 ⟨checked67_s10, List.forall_mem_cons.2 ⟨checked67_s11, List.forall_mem_cons.2 ⟨checked67_s12, List.forall_mem_cons.2 ⟨checked67_s13, List.forall_mem_cons.2 ⟨checked67_s14, List.forall_mem_cons.2 ⟨checked67_s15, List.forall_mem_cons.2 ⟨checked67_s16, List.forall_mem_cons.2 ⟨checked67_s17, List.forall_mem_cons.2 ⟨checked67_s18, List.forall_mem_cons.2 ⟨checked67_s19, List.forall_mem_cons.2 ⟨checked67_s20, List.forall_mem_cons.2 ⟨checked67_s21, List.forall_mem_cons.2 ⟨checked67_s22, List.forall_mem_cons.2 ⟨checked67_s23, List.forall_mem_cons.2 ⟨checked67_s24, List.forall_mem_cons.2 ⟨checked67_s25, List.forall_mem_cons.2 ⟨checked67_s26, List.forall_mem_cons.2 ⟨checked67_s27, List.forall_mem_cons.2 ⟨checked67_s28, List.forall_mem_cons.2 ⟨checked67_s29, List.forall_mem_cons.2 ⟨checked67_s30, List.forall_mem_cons.2 ⟨checked67_s31, List.forall_mem_cons.2 ⟨checked67_s32, List.forall_mem_cons.2 ⟨checked67_s33, List.forall_mem_singleton.2 checked67_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked67
