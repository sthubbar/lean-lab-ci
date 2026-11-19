/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_61.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/cd4f1b20-fda3-459f-b0a3-d630c8e78d09
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData61.s0 : Seg := ⟨519880131265099147414946211, 519880131265099157273623576, 28188675, 4096, [], 520025063593153103434277827, 520025063593153113295703033⟩
def PrimData61.s1 : Seg := ⟨520025063593153103434277827, 520025063593153113295703033, 28196867, 4096, [], 520182656463595094468167202, 520182656463595104332581161⟩
def PrimData61.s2 : Seg := ⟨520182656463595094468167202, 520182656463595104332581161, 28205059, 4096, [], 520334872166316643410937872, 520334872166316653278239448⟩
def PrimData61.s3 : Seg := ⟨520334872166316643410937872, 520334872166316653278239448, 28213251, 4096, [], 520481710579660841985995604, 520481710579660851856082704⟩
def PrimData61.s4 : Seg := ⟨520481710579660841985995604, 520481710579660851856082704, 28221443, 4096, [], 520643425462757503698376613, 520643425462757513571532190⟩
def PrimData61.s5 : Seg := ⟨520643425462757503698376613, 520643425462757513571532190, 28229635, 4096, [], 520795648905024046551219345, 520795648905024056427263579⟩
def PrimData61.s6 : Seg := ⟨520795648905024046551219345, 520795648905024056427263579, 28237827, 4096, [], 520951039712783136765509632, 520951039712783146644502544⟩
def PrimData61.s7 : Seg := ⟨520951039712783136765509632, 520951039712783146644502544, 28246019, 4096, [], 521099470507924679888746405, 521099470507924689770554588⟩
def PrimData61.s8 : Seg := ⟨521099470507924679888746405, 521099470507924689770554588, 28254211, 4096, [], 521247587324819639124154175, 521247587324819649008773255⟩
def PrimData61.s9 : Seg := ⟨521247587324819639124154175, 521247587324819649008773255, 28262403, 4096, [], 521404884964745787479918489, 521404884964745797367522454⟩
def PrimData61.s10 : Seg := ⟨521404884964745787479918489, 521404884964745797367522454, 28270595, 4096, [], 521562501796721594945343042, 521562501796721604835937481⟩
def PrimData61.s11 : Seg := ⟨521562501796721594945343042, 521562501796721604835937481, 28278787, 4096, [], 521706195085260449835118172, 521706195085260459728438458⟩
def PrimData61.s12 : Seg := ⟨521706195085260449835118172, 521706195085260459728438458, 28286979, 4096, [], 521865716294803173714341330, 521865716294803183610688054⟩
def PrimData61.s13 : Seg := ⟨521865716294803173714341330, 521865716294803183610688054, 28295171, 4096, [], 522019542917856202068266448, 522019542917856211967531475⟩
def PrimData61.s14 : Seg := ⟨522019542917856202068266448, 522019542917856211967531475, 28303363, 4096, [], 522170523438293304931351743, 522170523438293314833480641⟩
def PrimData61.s15 : Seg := ⟨522170523438293304931351743, 522170523438293314833480641, 28311555, 4096, [], 522325937875259972756172698, 522325937875259982661250031⟩
def PrimData61.s16 : Seg := ⟨522325937875259972756172698, 522325937875259982661250031, 28319747, 4096, [], 522476923479892867901256983, 522476923479892877809198187⟩
def PrimData61.s17 : Seg := ⟨522476923479892867901256983, 522476923479892877809198187, 28327939, 4096, [], 522626328961273888982285418, 522626328961273898893060847⟩
def PrimData61.s18 : Seg := ⟨522626328961273888982285418, 522626328961273898893060847, 28336131, 4096, [], 522776370010930783554404029, 522776370010930793468026319⟩
def PrimData61.s19 : Seg := ⟨522776370010930783554404029, 522776370010930793468026319, 28344323, 4096, [], 522920082647903456027493826, 522920082647903465943840991⟩
def PrimData61.s20 : Seg := ⟨522920082647903456027493826, 522920082647903465943840991, 28352515, 4096, [], 523068545972503961190744768, 523068545972503971109907690⟩
def PrimData61.s21 : Seg := ⟨523068545972503961190744768, 523068545972503971109907690, 28360707, 4096, [], 523216378720744080561740783, 523216378720744090483708285⟩
def PrimData61.s22 : Seg := ⟨523216378720744080561740783, 523216378720744090483708285, 28368899, 4096, [], 523368329229815632236559337, 523368329229815642161408449⟩
def PrimData61.s23 : Seg := ⟨523368329229815632236559337, 523368329229815642161408449, 28377091, 4096, [], 523513634347312479514498775, 523513634347312489442105082⟩
def PrimData61.s24 : Seg := ⟨523513634347312479514498775, 523513634347312489442105082, 28385283, 4096, [], 523667489455381208292931348, 523667489455381218223454988⟩
def PrimData61.s25 : Seg := ⟨523667489455381208292931348, 523667489455381218223454988, 28393475, 4096, [], 523818814470079664322028279, 523818814470079674255422596⟩
def PrimData61.s26 : Seg := ⟨523818814470079664322028279, 523818814470079674255422596, 28401667, 4096, [], 523969192287684091466805466, 523969192287684101403052476⟩
def PrimData61.s27 : Seg := ⟨523969192287684091466805466, 523969192287684101403052476, 28409859, 4096, [], 524111657876336571900889765, 524111657876336581839837846⟩
def PrimData61.s28 : Seg := ⟨524111657876336571900889765, 524111657876336581839837846, 28418051, 4096, [], 524267422876398316304428233, 524267422876398326246330833⟩
def PrimData61.s29 : Seg := ⟨524267422876398316304428233, 524267422876398326246330833, 28426243, 4096, [], 524421924079699219121310375, 524421924079699229066143677⟩
def PrimData61.s30 : Seg := ⟨524421924079699219121310375, 524421924079699229066143677, 28434435, 4096, [], 524574844881949763095597859, 524574844881949773043330530⟩
def PrimData61.s31 : Seg := ⟨524574844881949763095597859, 524574844881949773043330530, 28442627, 4096, [], 524728084798121176331175681, 524728084798121186281814997⟩
def PrimData61.s32 : Seg := ⟨524728084798121176331175681, 524728084798121186281814997, 28450819, 4096, [], 524877527947096026834072678, 524877527947096036787545987⟩
def PrimData61.s33 : Seg := ⟨524877527947096026834072678, 524877527947096036787545987, 28459011, 4096, [], 525027923458522331921365735, 525027923458522341877689813⟩
def PrimData61.s34 : Seg := ⟨525027923458522331921365735, 525027923458522341877689813, 28467203, 4096, [], 525174521978339806412486561, 525174521978339816371589778⟩

def PrimData61.segs : List Seg := [PrimData61.s0, PrimData61.s1, PrimData61.s2, PrimData61.s3, PrimData61.s4, PrimData61.s5, PrimData61.s6, PrimData61.s7, PrimData61.s8, PrimData61.s9, PrimData61.s10, PrimData61.s11, PrimData61.s12, PrimData61.s13, PrimData61.s14, PrimData61.s15, PrimData61.s16, PrimData61.s17, PrimData61.s18, PrimData61.s19, PrimData61.s20, PrimData61.s21, PrimData61.s22, PrimData61.s23, PrimData61.s24, PrimData61.s25, PrimData61.s26, PrimData61.s27, PrimData61.s28, PrimData61.s29, PrimData61.s30, PrimData61.s31, PrimData61.s32, PrimData61.s33, PrimData61.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked61_s0 : Seg.bok PrimData61.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s0

theorem checked61_s1 : Seg.bok PrimData61.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s1

theorem checked61_s2 : Seg.bok PrimData61.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s2

theorem checked61_s3 : Seg.bok PrimData61.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s3

theorem checked61_s4 : Seg.bok PrimData61.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s4

theorem checked61_s5 : Seg.bok PrimData61.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s5

theorem checked61_s6 : Seg.bok PrimData61.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s6

theorem checked61_s7 : Seg.bok PrimData61.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s7

theorem checked61_s8 : Seg.bok PrimData61.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s8

theorem checked61_s9 : Seg.bok PrimData61.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s9

theorem checked61_s10 : Seg.bok PrimData61.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s10

theorem checked61_s11 : Seg.bok PrimData61.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s11

theorem checked61_s12 : Seg.bok PrimData61.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s12

theorem checked61_s13 : Seg.bok PrimData61.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s13

theorem checked61_s14 : Seg.bok PrimData61.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s14

theorem checked61_s15 : Seg.bok PrimData61.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s15

theorem checked61_s16 : Seg.bok PrimData61.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s16

theorem checked61_s17 : Seg.bok PrimData61.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s17

theorem checked61_s18 : Seg.bok PrimData61.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s18

theorem checked61_s19 : Seg.bok PrimData61.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s19

theorem checked61_s20 : Seg.bok PrimData61.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s20

theorem checked61_s21 : Seg.bok PrimData61.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s21

theorem checked61_s22 : Seg.bok PrimData61.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s22

theorem checked61_s23 : Seg.bok PrimData61.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s23

theorem checked61_s24 : Seg.bok PrimData61.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s24

theorem checked61_s25 : Seg.bok PrimData61.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s25

theorem checked61_s26 : Seg.bok PrimData61.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s26

theorem checked61_s27 : Seg.bok PrimData61.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s27

theorem checked61_s28 : Seg.bok PrimData61.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s28

theorem checked61_s29 : Seg.bok PrimData61.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s29

theorem checked61_s30 : Seg.bok PrimData61.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s30

theorem checked61_s31 : Seg.bok PrimData61.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s31

theorem checked61_s32 : Seg.bok PrimData61.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s32

theorem checked61_s33 : Seg.bok PrimData61.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s33

theorem checked61_s34 : Seg.bok PrimData61.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61_s34

 theorem checked61 : ∀ s ∈ PrimData61.segs, (Seg.bok s) = true := by
  unfold PrimData61.segs
  exact List.forall_mem_cons.2 ⟨checked61_s0, List.forall_mem_cons.2 ⟨checked61_s1, List.forall_mem_cons.2 ⟨checked61_s2, List.forall_mem_cons.2 ⟨checked61_s3, List.forall_mem_cons.2 ⟨checked61_s4, List.forall_mem_cons.2 ⟨checked61_s5, List.forall_mem_cons.2 ⟨checked61_s6, List.forall_mem_cons.2 ⟨checked61_s7, List.forall_mem_cons.2 ⟨checked61_s8, List.forall_mem_cons.2 ⟨checked61_s9, List.forall_mem_cons.2 ⟨checked61_s10, List.forall_mem_cons.2 ⟨checked61_s11, List.forall_mem_cons.2 ⟨checked61_s12, List.forall_mem_cons.2 ⟨checked61_s13, List.forall_mem_cons.2 ⟨checked61_s14, List.forall_mem_cons.2 ⟨checked61_s15, List.forall_mem_cons.2 ⟨checked61_s16, List.forall_mem_cons.2 ⟨checked61_s17, List.forall_mem_cons.2 ⟨checked61_s18, List.forall_mem_cons.2 ⟨checked61_s19, List.forall_mem_cons.2 ⟨checked61_s20, List.forall_mem_cons.2 ⟨checked61_s21, List.forall_mem_cons.2 ⟨checked61_s22, List.forall_mem_cons.2 ⟨checked61_s23, List.forall_mem_cons.2 ⟨checked61_s24, List.forall_mem_cons.2 ⟨checked61_s25, List.forall_mem_cons.2 ⟨checked61_s26, List.forall_mem_cons.2 ⟨checked61_s27, List.forall_mem_cons.2 ⟨checked61_s28, List.forall_mem_cons.2 ⟨checked61_s29, List.forall_mem_cons.2 ⟨checked61_s30, List.forall_mem_cons.2 ⟨checked61_s31, List.forall_mem_cons.2 ⟨checked61_s32, List.forall_mem_cons.2 ⟨checked61_s33, List.forall_mem_singleton.2 checked61_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked61
