/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_39.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/065b488b-9938-451f-81b2-ff807c800f66
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData39.s0 : Seg := ⟨403547232884253220325238886, 403547232884253227977894253, 21880835, 4096, [], 403706549496112121209419353, 403706549496112128865096332⟩
def PrimData39.s1 : Seg := ⟨403706549496112121209419353, 403706549496112128865096332, 21889027, 4096, [], 403850592317528763045908521, 403850592317528770704316828⟩
def PrimData39.s2 : Seg := ⟨403850592317528763045908521, 403850592317528770704316828, 21897219, 4096, [], 404003056646451657633729273, 404003056646451665295029716⟩
def PrimData39.s3 : Seg := ⟨404003056646451657633729273, 404003056646451665295029716, 21905411, 4096, [], 404154277151677153876058128, 404154277151677161540225727⟩
def PrimData39.s4 : Seg := ⟨404154277151677153876058128, 404154277151677161540225727, 21913603, 4096, [], 404307995376436136533950522, 404307995376436144201033115⟩
def PrimData39.s5 : Seg := ⟨404307995376436136533950522, 404307995376436144201033115, 21921795, 4096, [], 404462652443888197373958609, 404462652443888205043974655⟩
def PrimData39.s6 : Seg := ⟨404462652443888197373958609, 404462652443888205043974655, 21929987, 4096, [], 404620119311601126143541649, 404620119311601133816542810⟩
def PrimData39.s7 : Seg := ⟨404620119311601126143541649, 404620119311601133816542810, 21938179, 4096, [], 404776342347398336268449464, 404776342347398343944412954⟩
def PrimData39.s8 : Seg := ⟨404776342347398336268449464, 404776342347398343944412954, 21946371, 4096, [], 404926643993514817369695171, 404926643993514825048507749⟩
def PrimData39.s9 : Seg := ⟨404926643993514817369695171, 404926643993514825048507749, 21954563, 4096, [], 405079131865835768444119797, 405079131865835776125822864⟩
def PrimData39.s10 : Seg := ⟨405079131865835768444119797, 405079131865835776125822864, 21962755, 4096, [], 405224450747928100137291582, 405224450747928107821749835⟩
def PrimData39.s11 : Seg := ⟨405224450747928100137291582, 405224450747928107821749835, 21970947, 4096, [], 405373826821148642885851233, 405373826821148650573141791⟩
def PrimData39.s12 : Seg := ⟨405373826821148642885851233, 405373826821148650573141791, 21979139, 4096, [], 405526948533842491990443819, 405526948533842499680637724⟩
def PrimData39.s13 : Seg := ⟨405526948533842491990443819, 405526948533842499680637724, 21987331, 4096, [], 405676643041675395232979158, 405676643041675402926012903⟩
def PrimData39.s14 : Seg := ⟨405676643041675395232979158, 405676643041675402926012903, 21995523, 4096, [], 405829771487524901608974894, 405829771487524909304912057⟩
def PrimData39.s15 : Seg := ⟨405829771487524901608974894, 405829771487524909304912057, 22003715, 4096, [], 405979472665518857389095410, 405979472665518865087870846⟩
def PrimData39.s16 : Seg := ⟨405979472665518857389095410, 405979472665518865087870846, 22011907, 4096, [], 406127617666307781338723578, 406127617666307789040308129⟩
def PrimData39.s17 : Seg := ⟨406127617666307781338723578, 406127617666307789040308129, 22020099, 4096, [], 406283875074205534433187036, 406283875074205542137735463⟩
def PrimData39.s18 : Seg := ⟨406283875074205534433187036, 406283875074205542137735463, 22028291, 4096, [], 406443566840362738406959242, 406443566840362746114535804⟩
def PrimData39.s19 : Seg := ⟨406443566840362738406959242, 406443566840362746114535804, 22036483, 4096, [], 406597024042698282030130120, 406597024042698289740616781⟩
def PrimData39.s20 : Seg := ⟨406597024042698282030130120, 406597024042698289740616781, 22044675, 4096, [], 406753915609076509314212504, 406753915609076517027673674⟩
def PrimData39.s21 : Seg := ⟨406753915609076509314212504, 406753915609076517027673674, 22052867, 4096, [], 406899269695891416301472952, 406899269695891424017689745⟩
def PrimData39.s22 : Seg := ⟨406899269695891416301472952, 406899269695891424017689745, 22061059, 4096, [], 407044626939085687148442800, 407044626939085694867415727⟩
def PrimData39.s23 : Seg := ⟨407044626939085687148442800, 407044626939085694867415727, 22069251, 4096, [], 407194978260297817630429237, 407194978260297825352253361⟩
def PrimData39.s24 : Seg := ⟨407194978260297817630429237, 407194978260297825352253361, 22077443, 4096, [], 407339094162964407209835207, 407339094162964414934392172⟩
def PrimData39.s25 : Seg := ⟨407339094162964407209835207, 407339094162964414934392172, 22085635, 4096, [], 407482589325336152305401799, 407482589325336160032679190⟩
def PrimData39.s26 : Seg := ⟨407482589325336152305401799, 407482589325336160032679190, 22093827, 4096, [], 407634510322030194170850992, 407634510322030201901009187⟩
def PrimData39.s27 : Seg := ⟨407634510322030194170850992, 407634510322030201901009187, 22102019, 4096, [], 407779883512067355240937140, 407779883512067362973852097⟩
def PrimData39.s28 : Seg := ⟨407779883512067355240937140, 407779883512067362973852097, 22110211, 4096, [], 407933371007328498811652849, 407933371007328506547478709⟩
def PrimData39.s29 : Seg := ⟨407933371007328498811652849, 407933371007328506547478709, 22118403, 4096, [], 408081870311224088149834483, 408081870311224095888476811⟩
def PrimData39.s30 : Seg := ⟨408081870311224088149834483, 408081870311224095888476811, 22126595, 4096, [], 408234740554614180803849550, 408234740554614188545390889⟩
def PrimData39.s31 : Seg := ⟨408234740554614180803849550, 408234740554614188545390889, 22134787, 4096, [], 408384182308529929260359676, 408384182308529937004735681⟩
def PrimData39.s32 : Seg := ⟨408384182308529929260359676, 408384182308529937004735681, 22142979, 4096, [], 408536435226462295450695006, 408536435226462303197959425⟩
def PrimData39.s33 : Seg := ⟨408536435226462295450695006, 408536435226462303197959425, 22151171, 4096, [], 408683387516117119661503555, 408683387516117127411554814⟩
def PrimData39.s34 : Seg := ⟨408683387516117119661503555, 408683387516117127411554814, 22159363, 4096, [], 408835959152611696483367330, 408835959152611704236312835⟩

def PrimData39.segs : List Seg := [PrimData39.s0, PrimData39.s1, PrimData39.s2, PrimData39.s3, PrimData39.s4, PrimData39.s5, PrimData39.s6, PrimData39.s7, PrimData39.s8, PrimData39.s9, PrimData39.s10, PrimData39.s11, PrimData39.s12, PrimData39.s13, PrimData39.s14, PrimData39.s15, PrimData39.s16, PrimData39.s17, PrimData39.s18, PrimData39.s19, PrimData39.s20, PrimData39.s21, PrimData39.s22, PrimData39.s23, PrimData39.s24, PrimData39.s25, PrimData39.s26, PrimData39.s27, PrimData39.s28, PrimData39.s29, PrimData39.s30, PrimData39.s31, PrimData39.s32, PrimData39.s33, PrimData39.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked39_s0 : Seg.bok PrimData39.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s0

theorem checked39_s1 : Seg.bok PrimData39.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s1

theorem checked39_s2 : Seg.bok PrimData39.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s2

theorem checked39_s3 : Seg.bok PrimData39.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s3

theorem checked39_s4 : Seg.bok PrimData39.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s4

theorem checked39_s5 : Seg.bok PrimData39.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s5

theorem checked39_s6 : Seg.bok PrimData39.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s6

theorem checked39_s7 : Seg.bok PrimData39.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s7

theorem checked39_s8 : Seg.bok PrimData39.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s8

theorem checked39_s9 : Seg.bok PrimData39.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s9

theorem checked39_s10 : Seg.bok PrimData39.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s10

theorem checked39_s11 : Seg.bok PrimData39.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s11

theorem checked39_s12 : Seg.bok PrimData39.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s12

theorem checked39_s13 : Seg.bok PrimData39.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s13

theorem checked39_s14 : Seg.bok PrimData39.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s14

theorem checked39_s15 : Seg.bok PrimData39.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s15

theorem checked39_s16 : Seg.bok PrimData39.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s16

theorem checked39_s17 : Seg.bok PrimData39.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s17

theorem checked39_s18 : Seg.bok PrimData39.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s18

theorem checked39_s19 : Seg.bok PrimData39.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s19

theorem checked39_s20 : Seg.bok PrimData39.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s20

theorem checked39_s21 : Seg.bok PrimData39.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s21

theorem checked39_s22 : Seg.bok PrimData39.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s22

theorem checked39_s23 : Seg.bok PrimData39.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s23

theorem checked39_s24 : Seg.bok PrimData39.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s24

theorem checked39_s25 : Seg.bok PrimData39.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s25

theorem checked39_s26 : Seg.bok PrimData39.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s26

theorem checked39_s27 : Seg.bok PrimData39.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s27

theorem checked39_s28 : Seg.bok PrimData39.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s28

theorem checked39_s29 : Seg.bok PrimData39.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s29

theorem checked39_s30 : Seg.bok PrimData39.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s30

theorem checked39_s31 : Seg.bok PrimData39.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s31

theorem checked39_s32 : Seg.bok PrimData39.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s32

theorem checked39_s33 : Seg.bok PrimData39.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s33

theorem checked39_s34 : Seg.bok PrimData39.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39_s34

 theorem checked39 : ∀ s ∈ PrimData39.segs, (Seg.bok s) = true := by
  unfold PrimData39.segs
  exact List.forall_mem_cons.2 ⟨checked39_s0, List.forall_mem_cons.2 ⟨checked39_s1, List.forall_mem_cons.2 ⟨checked39_s2, List.forall_mem_cons.2 ⟨checked39_s3, List.forall_mem_cons.2 ⟨checked39_s4, List.forall_mem_cons.2 ⟨checked39_s5, List.forall_mem_cons.2 ⟨checked39_s6, List.forall_mem_cons.2 ⟨checked39_s7, List.forall_mem_cons.2 ⟨checked39_s8, List.forall_mem_cons.2 ⟨checked39_s9, List.forall_mem_cons.2 ⟨checked39_s10, List.forall_mem_cons.2 ⟨checked39_s11, List.forall_mem_cons.2 ⟨checked39_s12, List.forall_mem_cons.2 ⟨checked39_s13, List.forall_mem_cons.2 ⟨checked39_s14, List.forall_mem_cons.2 ⟨checked39_s15, List.forall_mem_cons.2 ⟨checked39_s16, List.forall_mem_cons.2 ⟨checked39_s17, List.forall_mem_cons.2 ⟨checked39_s18, List.forall_mem_cons.2 ⟨checked39_s19, List.forall_mem_cons.2 ⟨checked39_s20, List.forall_mem_cons.2 ⟨checked39_s21, List.forall_mem_cons.2 ⟨checked39_s22, List.forall_mem_cons.2 ⟨checked39_s23, List.forall_mem_cons.2 ⟨checked39_s24, List.forall_mem_cons.2 ⟨checked39_s25, List.forall_mem_cons.2 ⟨checked39_s26, List.forall_mem_cons.2 ⟨checked39_s27, List.forall_mem_cons.2 ⟨checked39_s28, List.forall_mem_cons.2 ⟨checked39_s29, List.forall_mem_cons.2 ⟨checked39_s30, List.forall_mem_cons.2 ⟨checked39_s31, List.forall_mem_cons.2 ⟨checked39_s32, List.forall_mem_cons.2 ⟨checked39_s33, List.forall_mem_singleton.2 checked39_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked39
