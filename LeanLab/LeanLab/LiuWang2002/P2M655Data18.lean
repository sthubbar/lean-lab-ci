/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_18.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/dab34a83-d4ae-4125-91bd-963a541c361b
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData18.s0 : Seg := ⟨292478131132665993223673120, 292478131132665998770138892, 15859715, 4096, [], 292631662183760657154198594, 292631662183760662703577174⟩
def PrimData18.s1 : Seg := ⟨292631662183760657154198594, 292631662183760662703577174, 15867907, 4096, [], 292782445366092375796600644, 292782445366092381348839764⟩
def PrimData18.s2 : Seg := ⟨292782445366092375796600644, 292782445366092381348839764, 15876099, 4096, [], 292937209341945981701252542, 292937209341945987256427870⟩
def PrimData18.s3 : Seg := ⟨292937209341945981701252542, 292937209341945987256427870, 15884291, 4096, [], 293086472542188425444586962, 293086472542188431002593600⟩
def PrimData18.s4 : Seg := ⟨293086472542188425444586962, 293086472542188431002593600, 15892483, 4096, [], 293235740472092777374214699, 293235740472092782935052828⟩
def PrimData18.s5 : Seg := ⟨293235740472092777374214699, 293235740472092782935052828, 15900675, 4096, [], 293387460091700393023433249, 293387460091700398587149564⟩
def PrimData18.s6 : Seg := ⟨293387460091700393023433249, 293387460091700398587149564, 15908867, 4096, [], 293531842942121864422366967, 293531842942121869988821523⟩
def PrimData18.s7 : Seg := ⟨293531842942121864422366967, 293531842942121869988821523, 15917059, 4096, [], 293689384172299381658482627, 293689384172299387227925756⟩
def PrimData18.s8 : Seg := ⟨293689384172299381658482627, 293689384172299387227925756, 15925251, 4096, [], 293843565276282710940097763, 293843565276282716512465559⟩
def PrimData18.s9 : Seg := ⟨293843565276282710940097763, 293843565276282716512465559, 15933443, 4096, [], 293992856311430038884456728, 293992856311430044459655906⟩
def PrimData18.s10 : Seg := ⟨293992856311430038884456728, 293992856311430044459655906, 15941635, 4096, [], 294135115497413515503005811, 294135115497413521080902405⟩
def PrimData18.s11 : Seg := ⟨294135115497413515503005811, 294135115497413521080902405, 15949827, 4096, [], 294290840555830285136818930, 294290840555830290717669548⟩
def PrimData18.s12 : Seg := ⟨294290840555830285136818930, 294290840555830290717669548, 15958019, 4096, [], 294443510977450990118482492, 294443510977450995702228814⟩
def PrimData18.s13 : Seg := ⟨294443510977450990118482492, 294443510977450995702228814, 15966211, 4096, [], 294593126435031191294025832, 294593126435031196880609538⟩
def PrimData18.s14 : Seg := ⟨294593126435031191294025832, 294593126435031196880609538, 15974403, 4096, [], 294744276403397555499869397, 294744276403397561089319649⟩
def PrimData18.s15 : Seg := ⟨294744276403397555499869397, 294744276403397561089319649, 15982595, 4096, [], 294896654980589975385620243, 294896654980589980977960369⟩
def PrimData18.s16 : Seg := ⟨294896654980589975385620243, 294896654980589980977960369, 15990787, 4096, [], 295047814312608076931932358, 295047814312608082527139028⟩
def PrimData18.s17 : Seg := ⟨295047814312608076931932358, 295047814312608082527139028, 15998979, 4096, [], 295196224294161909141937475, 295196224294161914739958201⟩
def PrimData18.s18 : Seg := ⟨295196224294161909141937475, 295196224294161914739958201, 16007171, 4096, [], 295347392977557736156341600, 295347392977557741757228870⟩
def PrimData18.s19 : Seg := ⟨295347392977557736156341600, 295347392977557741757228870, 16015363, 4096, [], 295497342234319737413414979, 295497342234319743017145465⟩
def PrimData18.s20 : Seg := ⟨295497342234319737413414979, 295497342234319743017145465, 16023555, 4096, [], 295653722744492818810530269, 295653722744492824417226443⟩
def PrimData18.s21 : Seg := ⟨295653722744492818810530269, 295653722744492824417226443, 16031747, 4096, [], 295799396700871325197209969, 295799396700871330806667714⟩
def PrimData18.s22 : Seg := ⟨295799396700871325197209969, 295799396700871330806667714, 16039939, 4096, [], 295948441671904805345072303, 295948441671904810957355768⟩
def PrimData18.s23 : Seg := ⟨295948441671904805345072303, 295948441671904810957355768, 16048131, 4096, [], 296091982123416560336469075, 296091982123416565951473284⟩
def PrimData18.s24 : Seg := ⟨296091982123416560336469075, 296091982123416565951473284, 16056323, 4096, [], 296241954472786803602122790, 296241954472786809219970218⟩
def PrimData18.s25 : Seg := ⟨296241954472786803602122790, 296241954472786809219970218, 16064515, 4096, [], 296399277169830889343819498, 296399277169830894964650110⟩
def PrimData18.s26 : Seg := ⟨296399277169830889343819498, 296399277169830894964650110, 16072707, 4096, [], 296553543793826257237390194, 296553543793826262861145670⟩
def PrimData18.s27 : Seg := ⟨296553543793826257237390194, 296553543793826262861145670, 16080899, 4096, [], 296702917767602926060617238, 296702917767602931687204266⟩
def PrimData18.s28 : Seg := ⟨296702917767602926060617238, 296702917767602931687204266, 16089091, 4096, [], 296849235257296353894988447, 296849235257296359524348707⟩
def PrimData18.s29 : Seg := ⟨296849235257296353894988447, 296849235257296359524348707, 16097283, 4096, [], 297003210014204664367868839, 297003210014204670000148131⟩
def PrimData18.s30 : Seg := ⟨297003210014204664367868839, 297003210014204670000148131, 16105475, 4096, [], 297153516152829151237248886, 297153516152829156872377226⟩
def PrimData18.s31 : Seg := ⟨297153516152829151237248886, 297153516152829156872377226, 16113667, 4096, [], 297305969796476581662819832, 297305969796476587300838079⟩
def PrimData18.s32 : Seg := ⟨297305969796476581662819832, 297305969796476587300838079, 16121859, 4096, [], 297453529776302518854870642, 297453529776302524495685454⟩
def PrimData18.s33 : Seg := ⟨297453529776302518854870642, 297453529776302524495685454, 16130051, 4096, [], 297603849584999416948831553, 297603849584999422592495418⟩
def PrimData18.s34 : Seg := ⟨297603849584999416948831553, 297603849584999422592495418, 16138243, 4096, [], 297761828040368847247783066, 297761828040368852894441779⟩

def PrimData18.segs : List Seg := [PrimData18.s0, PrimData18.s1, PrimData18.s2, PrimData18.s3, PrimData18.s4, PrimData18.s5, PrimData18.s6, PrimData18.s7, PrimData18.s8, PrimData18.s9, PrimData18.s10, PrimData18.s11, PrimData18.s12, PrimData18.s13, PrimData18.s14, PrimData18.s15, PrimData18.s16, PrimData18.s17, PrimData18.s18, PrimData18.s19, PrimData18.s20, PrimData18.s21, PrimData18.s22, PrimData18.s23, PrimData18.s24, PrimData18.s25, PrimData18.s26, PrimData18.s27, PrimData18.s28, PrimData18.s29, PrimData18.s30, PrimData18.s31, PrimData18.s32, PrimData18.s33, PrimData18.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked18_s0 : Seg.bok PrimData18.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s0

theorem checked18_s1 : Seg.bok PrimData18.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s1

theorem checked18_s2 : Seg.bok PrimData18.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s2

theorem checked18_s3 : Seg.bok PrimData18.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s3

theorem checked18_s4 : Seg.bok PrimData18.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s4

theorem checked18_s5 : Seg.bok PrimData18.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s5

theorem checked18_s6 : Seg.bok PrimData18.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s6

theorem checked18_s7 : Seg.bok PrimData18.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s7

theorem checked18_s8 : Seg.bok PrimData18.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s8

theorem checked18_s9 : Seg.bok PrimData18.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s9

theorem checked18_s10 : Seg.bok PrimData18.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s10

theorem checked18_s11 : Seg.bok PrimData18.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s11

theorem checked18_s12 : Seg.bok PrimData18.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s12

theorem checked18_s13 : Seg.bok PrimData18.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s13

theorem checked18_s14 : Seg.bok PrimData18.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s14

theorem checked18_s15 : Seg.bok PrimData18.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s15

theorem checked18_s16 : Seg.bok PrimData18.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s16

theorem checked18_s17 : Seg.bok PrimData18.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s17

theorem checked18_s18 : Seg.bok PrimData18.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s18

theorem checked18_s19 : Seg.bok PrimData18.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s19

theorem checked18_s20 : Seg.bok PrimData18.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s20

theorem checked18_s21 : Seg.bok PrimData18.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s21

theorem checked18_s22 : Seg.bok PrimData18.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s22

theorem checked18_s23 : Seg.bok PrimData18.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s23

theorem checked18_s24 : Seg.bok PrimData18.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s24

theorem checked18_s25 : Seg.bok PrimData18.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s25

theorem checked18_s26 : Seg.bok PrimData18.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s26

theorem checked18_s27 : Seg.bok PrimData18.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s27

theorem checked18_s28 : Seg.bok PrimData18.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s28

theorem checked18_s29 : Seg.bok PrimData18.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s29

theorem checked18_s30 : Seg.bok PrimData18.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s30

theorem checked18_s31 : Seg.bok PrimData18.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s31

theorem checked18_s32 : Seg.bok PrimData18.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s32

theorem checked18_s33 : Seg.bok PrimData18.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s33

theorem checked18_s34 : Seg.bok PrimData18.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18_s34

 theorem checked18 : ∀ s ∈ PrimData18.segs, (Seg.bok s) = true := by
  unfold PrimData18.segs
  exact List.forall_mem_cons.2 ⟨checked18_s0, List.forall_mem_cons.2 ⟨checked18_s1, List.forall_mem_cons.2 ⟨checked18_s2, List.forall_mem_cons.2 ⟨checked18_s3, List.forall_mem_cons.2 ⟨checked18_s4, List.forall_mem_cons.2 ⟨checked18_s5, List.forall_mem_cons.2 ⟨checked18_s6, List.forall_mem_cons.2 ⟨checked18_s7, List.forall_mem_cons.2 ⟨checked18_s8, List.forall_mem_cons.2 ⟨checked18_s9, List.forall_mem_cons.2 ⟨checked18_s10, List.forall_mem_cons.2 ⟨checked18_s11, List.forall_mem_cons.2 ⟨checked18_s12, List.forall_mem_cons.2 ⟨checked18_s13, List.forall_mem_cons.2 ⟨checked18_s14, List.forall_mem_cons.2 ⟨checked18_s15, List.forall_mem_cons.2 ⟨checked18_s16, List.forall_mem_cons.2 ⟨checked18_s17, List.forall_mem_cons.2 ⟨checked18_s18, List.forall_mem_cons.2 ⟨checked18_s19, List.forall_mem_cons.2 ⟨checked18_s20, List.forall_mem_cons.2 ⟨checked18_s21, List.forall_mem_cons.2 ⟨checked18_s22, List.forall_mem_cons.2 ⟨checked18_s23, List.forall_mem_cons.2 ⟨checked18_s24, List.forall_mem_cons.2 ⟨checked18_s25, List.forall_mem_cons.2 ⟨checked18_s26, List.forall_mem_cons.2 ⟨checked18_s27, List.forall_mem_cons.2 ⟨checked18_s28, List.forall_mem_cons.2 ⟨checked18_s29, List.forall_mem_cons.2 ⟨checked18_s30, List.forall_mem_cons.2 ⟨checked18_s31, List.forall_mem_cons.2 ⟨checked18_s32, List.forall_mem_cons.2 ⟨checked18_s33, List.forall_mem_singleton.2 checked18_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked18
