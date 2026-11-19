/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_27.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/4feb6734-36d3-4d82-afa7-1e4e320f85ef
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData27.s0 : Seg := ⟨340094750587418127673812451, 340094750587418134123150337, 18440195, 4096, [], 340246282416967791980691197, 340246282416967798432903115⟩
def PrimData27.s1 : Seg := ⟨340246282416967791980691197, 340246282416967798432903115, 18448387, 4096, [], 340393497528015360329450068, 340393497528015366784453546⟩
def PrimData27.s2 : Seg := ⟨340393497528015360329450068, 340393497528015366784453546, 18456579, 4096, [], 340548741080366402725963237, 340548741080366409183910827⟩
def PrimData27.s3 : Seg := ⟨340548741080366402725963237, 340548741080366409183910827, 18464771, 4096, [], 340691334359037191763997363, 340691334359037198224647745⟩
def PrimData27.s4 : Seg := ⟨340691334359037191763997363, 340691334359037198224647745, 18472963, 4096, [], 340839795848244440706244484, 340839795848244447169709130⟩
def PrimData27.s5 : Seg := ⟨340839795848244440706244484, 340839795848244447169709130, 18481155, 4096, [], 340989187217168839231739923, 340989187217168845698037562⟩
def PrimData27.s6 : Seg := ⟨340989187217168839231739923, 340989187217168845698037562, 18489347, 4096, [], 341137656519265637675845713, 341137656519265644144958465⟩
def PrimData27.s7 : Seg := ⟨341137656519265637675845713, 341137656519265644144958465, 18497539, 4096, [], 341285512417930631613218665, 341285512417930638085135525⟩
def PrimData27.s8 : Seg := ⟨341285512417930631613218665, 341285512417930638085135525, 18505731, 4096, [], 341432137448983720094804451, 341432137448983726569501924⟩
def PrimData27.s9 : Seg := ⟨341432137448983720094804451, 341432137448983726569501924, 18513923, 4096, [], 341584322798628670097589097, 341584322798628676575174139⟩
def PrimData27.s10 : Seg := ⟨341584322798628670097589097, 341584322798628676575174139, 18522115, 4096, [], 341737747037192978688745779, 341737747037192985169241839⟩
def PrimData27.s11 : Seg := ⟨341737747037192978688745779, 341737747037192985169241839, 18530307, 4096, [], 341888088208523130262769139, 341888088208523136746117659⟩
def PrimData27.s12 : Seg := ⟨341888088208523130262769139, 341888088208523136746117659, 18538499, 4096, [], 342040285660152660072904315, 342040285660152666559140535⟩
def PrimData27.s13 : Seg := ⟨342040285660152660072904315, 342040285660152666559140535, 18546691, 4096, [], 342191869712369646882906258, 342191869712369653372018273⟩
def PrimData27.s14 : Seg := ⟨342191869712369646882906258, 342191869712369653372018273, 18554883, 4096, [], 342338826694029955494924708, 342338826694029961986824328⟩
def PrimData27.s15 : Seg := ⟨342338826694029955494924708, 342338826694029961986824328, 18563075, 4096, [], 342495976078100442719012387, 342495976078100449213892568⟩
def PrimData27.s16 : Seg := ⟨342495976078100442719012387, 342495976078100449213892568, 18571267, 4096, [], 342642940809904877945111646, 342642940809904884442780396⟩
def PrimData27.s17 : Seg := ⟨342642940809904877945111646, 342642940809904884442780396, 18579459, 4096, [], 342800715995720304140170883, 342800715995720310640831890⟩
def PrimData27.s18 : Seg := ⟨342800715995720304140170883, 342800715995720310640831890, 18587651, 4096, [], 342956025176516780582744353, 342956025176516787086352380⟩
def PrimData27.s19 : Seg := ⟨342956025176516780582744353, 342956025176516787086352380, 18595843, 4096, [], 343104854187443977438581522, 343104854187443983945012231⟩
def PrimData27.s20 : Seg := ⟨343104854187443977438581522, 343104854187443983945012231, 18604035, 4096, [], 343258936392063293863558800, 343258936392063300372912982⟩
def PrimData27.s21 : Seg := ⟨343258936392063293863558800, 343258936392063300372912982, 18612227, 4096, [], 343408082011658932352074925, 343408082011658938864258330⟩
def PrimData27.s22 : Seg := ⟨343408082011658932352074925, 343408082011658938864258330, 18620419, 4096, [], 343564025152445976700896801, 343564025152445983216038903⟩
def PrimData27.s23 : Seg := ⟨343564025152445976700896801, 343564025152445983216038903, 18628611, 4096, [], 343713178645454819470479446, 343713178645454825988450538⟩
def PrimData27.s24 : Seg := ⟨343713178645454819470479446, 343713178645454825988450538, 18636803, 4096, [], 343865424159892304891035263, 343865424159892311411893057⟩
def PrimData27.s25 : Seg := ⟨343865424159892304891035263, 343865424159892311411893057, 18644995, 4096, [], 344025394253022840619309073, 344025394253022847143201197⟩
def PrimData27.s26 : Seg := ⟨344025394253022840619309073, 344025394253022847143201197, 18653187, 4096, [], 344177338952067546301566494, 344177338952067552828340149⟩
def PrimData27.s27 : Seg := ⟨344177338952067546301566494, 344177338952067552828340149, 18661379, 4096, [], 344328978792550994424320835, 344328978792551000953970905⟩
def PrimData27.s28 : Seg := ⟨344328978792550994424320835, 344328978792551000953970905, 18669571, 4096, [], 344477534106778096163741383, 344477534106778102696209082⟩
def PrimData27.s29 : Seg := ⟨344477534106778096163741383, 344477534106778102696209082, 18677763, 4096, [], 344623004795892506794908646, 344623004795892513330134534⟩
def PrimData27.s30 : Seg := ⟨344623004795892506794908646, 344623004795892513330134534, 18685955, 4096, [], 344770023695445249853694261, 344770023695445256391708615⟩
def PrimData27.s31 : Seg := ⟨344770023695445249853694261, 344770023695445256391708615, 18694147, 4096, [], 344917664072781458434318240, 344917664072781464975132392⟩
def PrimData27.s32 : Seg := ⟨344917664072781458434318240, 344917664072781464975132392, 18702339, 4096, [], 345071485982301790376763799, 345071485982301796920494881⟩
def PrimData27.s33 : Seg := ⟨345071485982301790376763799, 345071485982301796920494881, 18710531, 4096, [], 345221914108761792932796475, 345221914108761799479380140⟩
def PrimData27.s34 : Seg := ⟨345221914108761792932796475, 345221914108761799479380140, 18718723, 4096, [], 345371419552240618977708317, 345371419552240625527127014⟩

def PrimData27.segs : List Seg := [PrimData27.s0, PrimData27.s1, PrimData27.s2, PrimData27.s3, PrimData27.s4, PrimData27.s5, PrimData27.s6, PrimData27.s7, PrimData27.s8, PrimData27.s9, PrimData27.s10, PrimData27.s11, PrimData27.s12, PrimData27.s13, PrimData27.s14, PrimData27.s15, PrimData27.s16, PrimData27.s17, PrimData27.s18, PrimData27.s19, PrimData27.s20, PrimData27.s21, PrimData27.s22, PrimData27.s23, PrimData27.s24, PrimData27.s25, PrimData27.s26, PrimData27.s27, PrimData27.s28, PrimData27.s29, PrimData27.s30, PrimData27.s31, PrimData27.s32, PrimData27.s33, PrimData27.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked27_s0 : Seg.bok PrimData27.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s0

theorem checked27_s1 : Seg.bok PrimData27.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s1

theorem checked27_s2 : Seg.bok PrimData27.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s2

theorem checked27_s3 : Seg.bok PrimData27.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s3

theorem checked27_s4 : Seg.bok PrimData27.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s4

theorem checked27_s5 : Seg.bok PrimData27.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s5

theorem checked27_s6 : Seg.bok PrimData27.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s6

theorem checked27_s7 : Seg.bok PrimData27.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s7

theorem checked27_s8 : Seg.bok PrimData27.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s8

theorem checked27_s9 : Seg.bok PrimData27.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s9

theorem checked27_s10 : Seg.bok PrimData27.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s10

theorem checked27_s11 : Seg.bok PrimData27.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s11

theorem checked27_s12 : Seg.bok PrimData27.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s12

theorem checked27_s13 : Seg.bok PrimData27.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s13

theorem checked27_s14 : Seg.bok PrimData27.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s14

theorem checked27_s15 : Seg.bok PrimData27.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s15

theorem checked27_s16 : Seg.bok PrimData27.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s16

theorem checked27_s17 : Seg.bok PrimData27.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s17

theorem checked27_s18 : Seg.bok PrimData27.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s18

theorem checked27_s19 : Seg.bok PrimData27.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s19

theorem checked27_s20 : Seg.bok PrimData27.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s20

theorem checked27_s21 : Seg.bok PrimData27.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s21

theorem checked27_s22 : Seg.bok PrimData27.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s22

theorem checked27_s23 : Seg.bok PrimData27.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s23

theorem checked27_s24 : Seg.bok PrimData27.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s24

theorem checked27_s25 : Seg.bok PrimData27.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s25

theorem checked27_s26 : Seg.bok PrimData27.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s26

theorem checked27_s27 : Seg.bok PrimData27.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s27

theorem checked27_s28 : Seg.bok PrimData27.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s28

theorem checked27_s29 : Seg.bok PrimData27.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s29

theorem checked27_s30 : Seg.bok PrimData27.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s30

theorem checked27_s31 : Seg.bok PrimData27.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s31

theorem checked27_s32 : Seg.bok PrimData27.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s32

theorem checked27_s33 : Seg.bok PrimData27.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s33

theorem checked27_s34 : Seg.bok PrimData27.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27_s34

 theorem checked27 : ∀ s ∈ PrimData27.segs, (Seg.bok s) = true := by
  unfold PrimData27.segs
  exact List.forall_mem_cons.2 ⟨checked27_s0, List.forall_mem_cons.2 ⟨checked27_s1, List.forall_mem_cons.2 ⟨checked27_s2, List.forall_mem_cons.2 ⟨checked27_s3, List.forall_mem_cons.2 ⟨checked27_s4, List.forall_mem_cons.2 ⟨checked27_s5, List.forall_mem_cons.2 ⟨checked27_s6, List.forall_mem_cons.2 ⟨checked27_s7, List.forall_mem_cons.2 ⟨checked27_s8, List.forall_mem_cons.2 ⟨checked27_s9, List.forall_mem_cons.2 ⟨checked27_s10, List.forall_mem_cons.2 ⟨checked27_s11, List.forall_mem_cons.2 ⟨checked27_s12, List.forall_mem_cons.2 ⟨checked27_s13, List.forall_mem_cons.2 ⟨checked27_s14, List.forall_mem_cons.2 ⟨checked27_s15, List.forall_mem_cons.2 ⟨checked27_s16, List.forall_mem_cons.2 ⟨checked27_s17, List.forall_mem_cons.2 ⟨checked27_s18, List.forall_mem_cons.2 ⟨checked27_s19, List.forall_mem_cons.2 ⟨checked27_s20, List.forall_mem_cons.2 ⟨checked27_s21, List.forall_mem_cons.2 ⟨checked27_s22, List.forall_mem_cons.2 ⟨checked27_s23, List.forall_mem_cons.2 ⟨checked27_s24, List.forall_mem_cons.2 ⟨checked27_s25, List.forall_mem_cons.2 ⟨checked27_s26, List.forall_mem_cons.2 ⟨checked27_s27, List.forall_mem_cons.2 ⟨checked27_s28, List.forall_mem_cons.2 ⟨checked27_s29, List.forall_mem_cons.2 ⟨checked27_s30, List.forall_mem_cons.2 ⟨checked27_s31, List.forall_mem_cons.2 ⟨checked27_s32, List.forall_mem_cons.2 ⟨checked27_s33, List.forall_mem_singleton.2 checked27_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked27
