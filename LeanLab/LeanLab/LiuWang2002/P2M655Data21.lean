/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_21.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/08c32ad6-f2cb-4c6a-885d-b5caed4ed774
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData21.s0 : Seg := ⟨308325563039865186934554257, 308325563039865192781242494, 16719875, 4096, [], 308477128554959973412713504, 308477128554959979262273230⟩
def PrimData21.s1 : Seg := ⟨308477128554959973412713504, 308477128554959979262273230, 16728067, 4096, [], 308633300874546710417264644, 308633300874546716269784175⟩
def PrimData21.s2 : Seg := ⟨308633300874546710417264644, 308633300874546716269784175, 16736259, 4096, [], 308787329967819457884601553, 308787329967819463740041102⟩
def PrimData21.s3 : Seg := ⟨308787329967819457884601553, 308787329967819463740041102, 16744451, 4096, [], 308933692607769181785965291, 308933692607769187644180530⟩
def PrimData21.s4 : Seg := ⟨308933692607769181785965291, 308933692607769187644180530, 16752643, 4096, [], 309089571797000873846529425, 309089571797000879707702294⟩
def PrimData21.s5 : Seg := ⟨309089571797000873846529425, 309089571797000879707702294, 16760835, 4096, [], 309238704737952354256816946, 309238704737952360120821008⟩
def PrimData21.s6 : Seg := ⟨309238704737952354256816946, 309238704737952360120821008, 16769027, 4096, [], 309392138183360204502500263, 309392138183360210369419150⟩
def PrimData21.s7 : Seg := ⟨309392138183360204502500263, 309392138183360210369419150, 16777219, 4096, [], 309542814250823076024987977, 309542814250823081894771464⟩
def PrimData21.s8 : Seg := ⟨309542814250823076024987977, 309542814250823081894771464, 16785411, 4096, [], 309699325588345192691255080, 309699325588345198564013975⟩
def PrimData21.s9 : Seg := ⟨309699325588345192691255080, 309699325588345198564013975, 16793603, 4096, [], 309854000087575887666896898, 309854000087575893542596209⟩
def PrimData21.s10 : Seg := ⟨309854000087575887666896898, 309854000087575893542596209, 16801795, 4096, [], 310000392856788847337733144, 310000392856788853216215407⟩
def PrimData21.s11 : Seg := ⟨310000392856788847337733144, 310000392856788853216215407, 16809987, 4096, [], 310158145580475816998519707, 310158145580475822880000706⟩
def PrimData21.s12 : Seg := ⟨310158145580475816998519707, 310158145580475822880000706, 16818179, 4096, [], 310307922934428266019659832, 310307922934428271903987935⟩
def PrimData21.s13 : Seg := ⟨310307922934428266019659832, 310307922934428271903987935, 16826371, 4096, [], 310454021568366048968384066, 310454021568366054855489289⟩
def PrimData21.s14 : Seg := ⟨310454021568366048968384066, 310454021568366054855489289, 16834563, 4096, [], 310606570122590480019296748, 310606570122590485909301563⟩
def PrimData21.s15 : Seg := ⟨310606570122590480019296748, 310606570122590485909301563, 16842755, 4096, [], 310754825855706151921034274, 310754825855706157813857033⟩
def PrimData21.s16 : Seg := ⟨310754825855706151921034274, 310754825855706157813857033, 16850947, 4096, [], 310901858145454877490853028, 310901858145454883386470403⟩
def PrimData21.s17 : Seg := ⟨310901858145454877490853028, 310901858145454883386470403, 16859139, 4096, [], 311055340943441815905880134, 311055340943441821804414597⟩
def PrimData21.s18 : Seg := ⟨311055340943441815905880134, 311055340943441821804414597, 16867331, 4096, [], 311210056226583152477860156, 311210056226583158379335035⟩
def PrimData21.s19 : Seg := ⟨311210056226583152477860156, 311210056226583158379335035, 16875523, 4096, [], 311357408425599745305695330, 311357408425599751209970657⟩
def PrimData21.s20 : Seg := ⟨311357408425599745305695330, 311357408425599751209970657, 16883715, 4096, [], 311503536952900784204658679, 311503536952900790111711126⟩
def PrimData21.s21 : Seg := ⟨311503536952900784204658679, 311503536952900790111711126, 16891907, 4096, [], 311657344696604414196556240, 311657344696604420106531607⟩
def PrimData21.s22 : Seg := ⟨311657344696604414196556240, 311657344696604420106531607, 16900099, 4096, [], 311812385001826442787170965, 311812385001826448700092580⟩
def PrimData21.s23 : Seg := ⟨311812385001826442787170965, 311812385001826448700092580, 16908291, 4096, [], 311960368393975532091470437, 311960368393975538007204164⟩
def PrimData21.s24 : Seg := ⟨311960368393975532091470437, 311960368393975538007204164, 16916483, 4096, [], 312109891130082366075914967, 312109891130082371994489966⟩
def PrimData21.s25 : Seg := ⟨312109891130082366075914967, 312109891130082371994489966, 16924675, 4096, [], 312263409783834751900892849, 312263409783834757822384936⟩
def PrimData21.s26 : Seg := ⟨312263409783834751900892849, 312263409783834757822384936, 16932867, 4096, [], 312414783608696678022519879, 312414783608696683946888230⟩
def PrimData21.s27 : Seg := ⟨312414783608696678022519879, 312414783608696683946888230, 16941059, 4096, [], 312571074693802709018612674, 312571074693802714945950601⟩
def PrimData21.s28 : Seg := ⟨312571074693802709018612674, 312571074693802714945950601, 16949251, 4096, [], 312732897541320863276282755, 312732897541320869206695234⟩
def PrimData21.s29 : Seg := ⟨312732897541320863276282755, 312732897541320869206695234, 16957443, 4096, [], 312883977399712566719959927, 312883977399712572653242838⟩
def PrimData21.s30 : Seg := ⟨312883977399712566719959927, 312883977399712572653242838, 16965635, 4096, [], 313035061745224424093206170, 313035061745224430029359513⟩
def PrimData21.s31 : Seg := ⟨313035061745224424093206170, 313035061745224430029359513, 16973827, 4096, [], 313189528392812744372031565, 313189528392812750311119492⟩
def PrimData21.s32 : Seg := ⟨313189528392812744372031565, 313189528392812750311119492, 16982019, 4096, [], 313336014890305080960256609, 313336014890305086902127488⟩
def PrimData21.s33 : Seg := ⟨313336014890305080960256609, 313336014890305086902127488, 16990211, 4096, [], 313493561581853173046246562, 313493561581853178991110345⟩
def PrimData21.s34 : Seg := ⟨313493561581853173046246562, 313493561581853178991110345, 16998403, 4096, [], 313641899375288204660420084, 313641899375288210608101811⟩

def PrimData21.segs : List Seg := [PrimData21.s0, PrimData21.s1, PrimData21.s2, PrimData21.s3, PrimData21.s4, PrimData21.s5, PrimData21.s6, PrimData21.s7, PrimData21.s8, PrimData21.s9, PrimData21.s10, PrimData21.s11, PrimData21.s12, PrimData21.s13, PrimData21.s14, PrimData21.s15, PrimData21.s16, PrimData21.s17, PrimData21.s18, PrimData21.s19, PrimData21.s20, PrimData21.s21, PrimData21.s22, PrimData21.s23, PrimData21.s24, PrimData21.s25, PrimData21.s26, PrimData21.s27, PrimData21.s28, PrimData21.s29, PrimData21.s30, PrimData21.s31, PrimData21.s32, PrimData21.s33, PrimData21.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked21_s0 : Seg.bok PrimData21.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s0

theorem checked21_s1 : Seg.bok PrimData21.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s1

theorem checked21_s2 : Seg.bok PrimData21.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s2

theorem checked21_s3 : Seg.bok PrimData21.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s3

theorem checked21_s4 : Seg.bok PrimData21.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s4

theorem checked21_s5 : Seg.bok PrimData21.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s5

theorem checked21_s6 : Seg.bok PrimData21.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s6

theorem checked21_s7 : Seg.bok PrimData21.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s7

theorem checked21_s8 : Seg.bok PrimData21.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s8

theorem checked21_s9 : Seg.bok PrimData21.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s9

theorem checked21_s10 : Seg.bok PrimData21.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s10

theorem checked21_s11 : Seg.bok PrimData21.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s11

theorem checked21_s12 : Seg.bok PrimData21.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s12

theorem checked21_s13 : Seg.bok PrimData21.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s13

theorem checked21_s14 : Seg.bok PrimData21.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s14

theorem checked21_s15 : Seg.bok PrimData21.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s15

theorem checked21_s16 : Seg.bok PrimData21.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s16

theorem checked21_s17 : Seg.bok PrimData21.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s17

theorem checked21_s18 : Seg.bok PrimData21.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s18

theorem checked21_s19 : Seg.bok PrimData21.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s19

theorem checked21_s20 : Seg.bok PrimData21.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s20

theorem checked21_s21 : Seg.bok PrimData21.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s21

theorem checked21_s22 : Seg.bok PrimData21.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s22

theorem checked21_s23 : Seg.bok PrimData21.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s23

theorem checked21_s24 : Seg.bok PrimData21.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s24

theorem checked21_s25 : Seg.bok PrimData21.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s25

theorem checked21_s26 : Seg.bok PrimData21.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s26

theorem checked21_s27 : Seg.bok PrimData21.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s27

theorem checked21_s28 : Seg.bok PrimData21.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s28

theorem checked21_s29 : Seg.bok PrimData21.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s29

theorem checked21_s30 : Seg.bok PrimData21.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s30

theorem checked21_s31 : Seg.bok PrimData21.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s31

theorem checked21_s32 : Seg.bok PrimData21.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s32

theorem checked21_s33 : Seg.bok PrimData21.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s33

theorem checked21_s34 : Seg.bok PrimData21.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21_s34

 theorem checked21 : ∀ s ∈ PrimData21.segs, (Seg.bok s) = true := by
  unfold PrimData21.segs
  exact List.forall_mem_cons.2 ⟨checked21_s0, List.forall_mem_cons.2 ⟨checked21_s1, List.forall_mem_cons.2 ⟨checked21_s2, List.forall_mem_cons.2 ⟨checked21_s3, List.forall_mem_cons.2 ⟨checked21_s4, List.forall_mem_cons.2 ⟨checked21_s5, List.forall_mem_cons.2 ⟨checked21_s6, List.forall_mem_cons.2 ⟨checked21_s7, List.forall_mem_cons.2 ⟨checked21_s8, List.forall_mem_cons.2 ⟨checked21_s9, List.forall_mem_cons.2 ⟨checked21_s10, List.forall_mem_cons.2 ⟨checked21_s11, List.forall_mem_cons.2 ⟨checked21_s12, List.forall_mem_cons.2 ⟨checked21_s13, List.forall_mem_cons.2 ⟨checked21_s14, List.forall_mem_cons.2 ⟨checked21_s15, List.forall_mem_cons.2 ⟨checked21_s16, List.forall_mem_cons.2 ⟨checked21_s17, List.forall_mem_cons.2 ⟨checked21_s18, List.forall_mem_cons.2 ⟨checked21_s19, List.forall_mem_cons.2 ⟨checked21_s20, List.forall_mem_cons.2 ⟨checked21_s21, List.forall_mem_cons.2 ⟨checked21_s22, List.forall_mem_cons.2 ⟨checked21_s23, List.forall_mem_cons.2 ⟨checked21_s24, List.forall_mem_cons.2 ⟨checked21_s25, List.forall_mem_cons.2 ⟨checked21_s26, List.forall_mem_cons.2 ⟨checked21_s27, List.forall_mem_cons.2 ⟨checked21_s28, List.forall_mem_cons.2 ⟨checked21_s29, List.forall_mem_cons.2 ⟨checked21_s30, List.forall_mem_cons.2 ⟨checked21_s31, List.forall_mem_cons.2 ⟨checked21_s32, List.forall_mem_cons.2 ⟨checked21_s33, List.forall_mem_singleton.2 checked21_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked21
