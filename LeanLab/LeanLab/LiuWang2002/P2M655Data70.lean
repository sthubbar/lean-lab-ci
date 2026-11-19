/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_70.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/876812d8-7c67-41f7-bf2a-02083d8cb679
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData70.s0 : Seg := ⟨567536197657974103189865897, 567536197657974113952253738, 30769155, 4096, [], 567685368583490475440530968, 567685368583490486205748453⟩
def PrimData70.s1 : Seg := ⟨567685368583490475440530968, 567685368583490486205748453, 30777347, 4096, [], 567837086337212132173496909, 567837086337212142941593598⟩
def PrimData70.s2 : Seg := ⟨567837086337212132173496909, 567837086337212142941593598, 30785539, 4096, [], 567984671535470702791669005, 567984671535470713562565700⟩
def PrimData70.s3 : Seg := ⟨567984671535470702791669005, 567984671535470713562565700, 30793731, 4096, [], 568137348181509393952540720, 568137348181509404726333184⟩
def PrimData70.s4 : Seg := ⟨568137348181509393952540720, 568137348181509404726333184, 30801923, 4096, [], 568285574054855246386692338, 568285574054855257163297927⟩
def PrimData70.s5 : Seg := ⟨568285574054855246386692338, 568285574054855257163297927, 30810115, 4096, [], 568437619201780905587134590, 568437619201780916366624779⟩
def PrimData70.s6 : Seg := ⟨568437619201780905587134590, 568437619201780916366624779, 30818307, 4096, [], 568593165757468065464781747, 568593165757468076247222861⟩
def PrimData70.s7 : Seg := ⟨568593165757468065464781747, 568593165757468076247222861, 30826499, 4096, [], 568747760386448125230652051, 568747760386448136016026105⟩
def PrimData70.s8 : Seg := ⟨568747760386448125230652051, 568747760386448136016026105, 30834691, 4096, [], 568899494535858366065767785, 568899494535858376854020396⟩
def PrimData70.s9 : Seg := ⟨568899494535858366065767785, 568899494535858376854020396, 30842883, 4096, [], 569045823223898193713129216, 569045823223898204504157537⟩
def PrimData70.s10 : Seg := ⟨569045823223898193713129216, 569045823223898204504157537, 30851075, 4096, [], 569202651805810197767260623, 569202651805810208561263490⟩
def PrimData70.s11 : Seg := ⟨569202651805810197767260623, 569202651805810208561263490, 30859267, 4096, [], 569353756676579189062316942, 569353756676579199859185960⟩
def PrimData70.s12 : Seg := ⟨569353756676579189062316942, 569353756676579199859185960, 30867459, 4096, [], 569508363254957000391793884, 569508363254957011191596442⟩
def PrimData70.s13 : Seg := ⟨569508363254957000391793884, 569508363254957011191596442, 30875651, 4096, [], 569661699679813036814718685, 569661699679813047617429533⟩
def PrimData70.s14 : Seg := ⟨569661699679813036814718685, 569661699679813047617429533, 30883843, 4096, [], 569813447806291401059605046, 569813447806291411865195190⟩
def PrimData70.s15 : Seg := ⟨569813447806291401059605046, 569813447806291411865195190, 30892035, 4096, [], 569963289463174753752403500, 569963289463174764560836022⟩
def PrimData70.s16 : Seg := ⟨569963289463174753752403500, 569963289463174764560836022, 30900227, 4096, [], 570122041354888056106482027, 570122041354888066917926338⟩
def PrimData70.s17 : Seg := ⟨570122041354888056106482027, 570122041354888066917926338, 30908419, 4096, [], 570269660610005714108401158, 570269660610005724922645200⟩
def PrimData70.s18 : Seg := ⟨570269660610005714108401158, 570269660610005724922645200, 30916611, 4096, [], 570415691344037038391180435, 570415691344037049208194771⟩
def PrimData70.s19 : Seg := ⟨570415691344037038391180435, 570415691344037049208194771, 30924803, 4096, [], 570567451142237317950208410, 570567451142237328770102378⟩
def PrimData70.s20 : Seg := ⟨570567451142237317950208410, 570567451142237328770102378, 30932995, 4096, [], 570716349818745603838190011, 570716349818745614660908842⟩
def PrimData70.s21 : Seg := ⟨570716349818745603838190011, 570716349818745614660908842, 30941187, 4096, [], 570872568590423717326431562, 570872568590423728152113608⟩
def PrimData70.s22 : Seg := ⟨570872568590423717326431562, 570872568590423728152113608, 30949379, 4096, [], 571017335720160068842177725, 571017335720160079670605557⟩
def PrimData70.s23 : Seg := ⟨571017335720160068842177725, 571017335720160079670605557, 30957571, 4096, [], 571167832139503169629050031, 571167832139503180460332898⟩
def PrimData70.s24 : Seg := ⟨571167832139503169629050031, 571167832139503180460332898, 30965763, 4096, [], 571313239990849608393046130, 571313239990849619227087130⟩
def PrimData70.s25 : Seg := ⟨571313239990849608393046130, 571313239990849619227087130, 30973955, 4096, [], 571460241006887579844272076, 571460241006887590681102108⟩
def PrimData70.s26 : Seg := ⟨571460241006887579844272076, 571460241006887590681102108, 30982147, 4096, [], 571605653314083711895934666, 571605653314083722735523984⟩
def PrimData70.s27 : Seg := ⟨571605653314083711895934666, 571605653314083722735523984, 30990339, 4096, [], 571759022731472170703837571, 571759022731472181546336030⟩
def PrimData70.s28 : Seg := ⟨571759022731472170703837571, 571759022731472181546336030, 30998531, 4096, [], 571913030887334418474372254, 571913030887334429319792325⟩
def PrimData70.s29 : Seg := ⟨571913030887334418474372254, 571913030887334429319792325, 31006723, 4096, [], 572063222953537315291659030, 572063222953537326139928016⟩
def PrimData70.s30 : Seg := ⟨572063222953537315291659030, 572063222953537326139928016, 31014915, 4096, [], 572213735492470384715569611, 572213735492470395566693717⟩
def PrimData70.s31 : Seg := ⟨572213735492470384715569611, 572213735492470395566693717, 31023107, 4096, [], 572362341028094530313287646, 572362341028094541167231364⟩
def PrimData70.s32 : Seg := ⟨572362341028094530313287646, 572362341028094541167231364, 31031299, 4096, [], 572520813650417806488604268, 572520813650417817345554899⟩
def PrimData70.s33 : Seg := ⟨572520813650417806488604268, 572520813650417817345554899, 31039491, 4096, [], 572660513531447280701274506, 572660513531447291560876087⟩
def PrimData70.s34 : Seg := ⟨572660513531447280701274506, 572660513531447291560876087, 31047683, 4096, [], 572802761390117332550497027, 572802761390117343412797043⟩

def PrimData70.segs : List Seg := [PrimData70.s0, PrimData70.s1, PrimData70.s2, PrimData70.s3, PrimData70.s4, PrimData70.s5, PrimData70.s6, PrimData70.s7, PrimData70.s8, PrimData70.s9, PrimData70.s10, PrimData70.s11, PrimData70.s12, PrimData70.s13, PrimData70.s14, PrimData70.s15, PrimData70.s16, PrimData70.s17, PrimData70.s18, PrimData70.s19, PrimData70.s20, PrimData70.s21, PrimData70.s22, PrimData70.s23, PrimData70.s24, PrimData70.s25, PrimData70.s26, PrimData70.s27, PrimData70.s28, PrimData70.s29, PrimData70.s30, PrimData70.s31, PrimData70.s32, PrimData70.s33, PrimData70.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked70_s0 : Seg.bok PrimData70.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s0

theorem checked70_s1 : Seg.bok PrimData70.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s1

theorem checked70_s2 : Seg.bok PrimData70.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s2

theorem checked70_s3 : Seg.bok PrimData70.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s3

theorem checked70_s4 : Seg.bok PrimData70.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s4

theorem checked70_s5 : Seg.bok PrimData70.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s5

theorem checked70_s6 : Seg.bok PrimData70.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s6

theorem checked70_s7 : Seg.bok PrimData70.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s7

theorem checked70_s8 : Seg.bok PrimData70.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s8

theorem checked70_s9 : Seg.bok PrimData70.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s9

theorem checked70_s10 : Seg.bok PrimData70.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s10

theorem checked70_s11 : Seg.bok PrimData70.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s11

theorem checked70_s12 : Seg.bok PrimData70.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s12

theorem checked70_s13 : Seg.bok PrimData70.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s13

theorem checked70_s14 : Seg.bok PrimData70.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s14

theorem checked70_s15 : Seg.bok PrimData70.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s15

theorem checked70_s16 : Seg.bok PrimData70.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s16

theorem checked70_s17 : Seg.bok PrimData70.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s17

theorem checked70_s18 : Seg.bok PrimData70.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s18

theorem checked70_s19 : Seg.bok PrimData70.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s19

theorem checked70_s20 : Seg.bok PrimData70.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s20

theorem checked70_s21 : Seg.bok PrimData70.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s21

theorem checked70_s22 : Seg.bok PrimData70.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s22

theorem checked70_s23 : Seg.bok PrimData70.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s23

theorem checked70_s24 : Seg.bok PrimData70.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s24

theorem checked70_s25 : Seg.bok PrimData70.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s25

theorem checked70_s26 : Seg.bok PrimData70.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s26

theorem checked70_s27 : Seg.bok PrimData70.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s27

theorem checked70_s28 : Seg.bok PrimData70.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s28

theorem checked70_s29 : Seg.bok PrimData70.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s29

theorem checked70_s30 : Seg.bok PrimData70.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s30

theorem checked70_s31 : Seg.bok PrimData70.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s31

theorem checked70_s32 : Seg.bok PrimData70.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s32

theorem checked70_s33 : Seg.bok PrimData70.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s33

theorem checked70_s34 : Seg.bok PrimData70.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70_s34

 theorem checked70 : ∀ s ∈ PrimData70.segs, (Seg.bok s) = true := by
  unfold PrimData70.segs
  exact List.forall_mem_cons.2 ⟨checked70_s0, List.forall_mem_cons.2 ⟨checked70_s1, List.forall_mem_cons.2 ⟨checked70_s2, List.forall_mem_cons.2 ⟨checked70_s3, List.forall_mem_cons.2 ⟨checked70_s4, List.forall_mem_cons.2 ⟨checked70_s5, List.forall_mem_cons.2 ⟨checked70_s6, List.forall_mem_cons.2 ⟨checked70_s7, List.forall_mem_cons.2 ⟨checked70_s8, List.forall_mem_cons.2 ⟨checked70_s9, List.forall_mem_cons.2 ⟨checked70_s10, List.forall_mem_cons.2 ⟨checked70_s11, List.forall_mem_cons.2 ⟨checked70_s12, List.forall_mem_cons.2 ⟨checked70_s13, List.forall_mem_cons.2 ⟨checked70_s14, List.forall_mem_cons.2 ⟨checked70_s15, List.forall_mem_cons.2 ⟨checked70_s16, List.forall_mem_cons.2 ⟨checked70_s17, List.forall_mem_cons.2 ⟨checked70_s18, List.forall_mem_cons.2 ⟨checked70_s19, List.forall_mem_cons.2 ⟨checked70_s20, List.forall_mem_cons.2 ⟨checked70_s21, List.forall_mem_cons.2 ⟨checked70_s22, List.forall_mem_cons.2 ⟨checked70_s23, List.forall_mem_cons.2 ⟨checked70_s24, List.forall_mem_cons.2 ⟨checked70_s25, List.forall_mem_cons.2 ⟨checked70_s26, List.forall_mem_cons.2 ⟨checked70_s27, List.forall_mem_cons.2 ⟨checked70_s28, List.forall_mem_cons.2 ⟨checked70_s29, List.forall_mem_cons.2 ⟨checked70_s30, List.forall_mem_cons.2 ⟨checked70_s31, List.forall_mem_cons.2 ⟨checked70_s32, List.forall_mem_cons.2 ⟨checked70_s33, List.forall_mem_singleton.2 checked70_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked70
