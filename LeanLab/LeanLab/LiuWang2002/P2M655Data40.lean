/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_40.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/c45c0a07-97de-4691-96e7-916822d89bb4
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData40.s0 : Seg := ⟨408835959152611696483367330, 408835959152611704236312835, 22167555, 4096, [], 408987910073725312961142535, 408987910073725320716970622⟩
def PrimData40.s1 : Seg := ⟨408987910073725312961142535, 408987910073725320716970622, 22175747, 4096, [], 409141112444891092721739703, 409141112444891100480473943⟩
def PrimData40.s2 : Seg := ⟨409141112444891092721739703, 409141112444891100480473943, 22183939, 4096, [], 409287453515273476677008248, 409287453515273484438518393⟩
def PrimData40.s3 : Seg := ⟨409287453515273476677008248, 409287453515273484438518393, 22192131, 4096, [], 409429429278867427679546666, 409429429278867435443749611⟩
def PrimData40.s4 : Seg := ⟨409429429278867427679546666, 409429429278867435443749611, 22200323, 4096, [], 409580769385990622640794242, 409580769385990630407867619⟩
def PrimData40.s5 : Seg := ⟨409580769385990622640794242, 409580769385990630407867619, 22208515, 4096, [], 409729616391678169508532572, 409729616391678177278428999⟩
def PrimData40.s6 : Seg := ⟨409729616391678169508532572, 409729616391678177278428999, 22216707, 4096, [], 409878154646971300519549392, 409878154646971308292263034⟩
def PrimData40.s7 : Seg := ⟨409878154646971300519549392, 409878154646971308292263034, 22224899, 4096, [], 410022015128764674100521001, 410022015128764681875962454⟩
def PrimData40.s8 : Seg := ⟨410022015128764674100521001, 410022015128764681875962454, 22233091, 4096, [], 410176489112388037209948023, 410176489112388044988319223⟩
def PrimData40.s9 : Seg := ⟨410176489112388037209948023, 410176489112388044988319223, 22241283, 4096, [], 410326285346991551886359802, 410326285346991559667572285⟩
def PrimData40.s10 : Seg := ⟨410326285346991551886359802, 410326285346991559667572285, 22249475, 4096, [], 410476708953641020114917954, 410476708953641027898983392⟩
def PrimData40.s11 : Seg := ⟨410476708953641020114917954, 410476708953641027898983392, 22257667, 4096, [], 410630568881390352227700525, 410630568881390360014683799⟩
def PrimData40.s12 : Seg := ⟨410630568881390352227700525, 410630568881390360014683799, 22265859, 4096, [], 410780374907167293243883076, 410780374907167301033708136⟩
def PrimData40.s13 : Seg := ⟨410780374907167293243883076, 410780374907167301033708136, 22274051, 4096, [], 410932368893468118480690243, 410932368893468126273398166⟩
def PrimData40.s14 : Seg := ⟨410932368893468118480690243, 410932368893468126273398166, 22282243, 4096, [], 411078436147908891559809284, 411078436147908899355287549⟩
def PrimData40.s15 : Seg := ⟨411078436147908891559809284, 411078436147908899355287549, 22290435, 4096, [], 411230748868879476056749316, 411230748868879483855115591⟩
def PrimData40.s16 : Seg := ⟨411230748868879476056749316, 411230748868879483855115591, 22298627, 4096, [], 411382440616290867953627077, 411382440616290875754869676⟩
def PrimData40.s17 : Seg := ⟨411382440616290867953627077, 411382440616290875754869676, 22306819, 4096, [], 411533823541445398250572909, 411533823541445406054685069⟩
def PrimData40.s18 : Seg := ⟨411533823541445398250572909, 411533823541445406054685069, 22315011, 4096, [], 411694573835915596336095790, 411694573835915604143256889⟩
def PrimData40.s19 : Seg := ⟨411694573835915596336095790, 411694573835915604143256889, 22323203, 4096, [], 411843466167576847694813576, 411843466167576855504798091⟩
def PrimData40.s20 : Seg := ⟨411843466167576847694813576, 411843466167576855504798091, 22331395, 4096, [], 411989552433640405721279143, 411989552433640413534033794⟩
def PrimData40.s21 : Seg := ⟨411989552433640405721279143, 411989552433640413534033794, 22339587, 4096, [], 412134081037564478631980780, 412134081037564486447475111⟩
def PrimData40.s22 : Seg := ⟨412134081037564478631980780, 412134081037564486447475111, 22347779, 4096, [], 412285480364773216823744422, 412285480364773224642109375⟩
def PrimData40.s23 : Seg := ⟨412285480364773216823744422, 412285480364773224642109375, 22355971, 4096, [], 412433761280762330348496866, 412433761280762338169673634⟩
def PrimData40.s24 : Seg := ⟨412433761280762330348496866, 412433761280762338169673634, 22364163, 4096, [], 412585167174109638030245518, 412585167174109645854293787⟩
def PrimData40.s25 : Seg := ⟨412585167174109638030245518, 412585167174109645854293787, 22372355, 4096, [], 412735327538207364334746596, 412735327538207372161642653⟩
def PrimData40.s26 : Seg := ⟨412735327538207364334746596, 412735327538207372161642653, 22380547, 4096, [], 412882993616242200120112496, 412882993616242207949807498⟩
def PrimData40.s27 : Seg := ⟨412882993616242200120112496, 412882993616242207949807498, 22388739, 4096, [], 413031911730823237423217740, 413031911730823245255735863⟩
def PrimData40.s28 : Seg := ⟨413031911730823237423217740, 413031911730823245255735863, 22396931, 4096, [], 413185203891715009825853041, 413185203891715017661278469⟩
def PrimData40.s29 : Seg := ⟨413185203891715009825853041, 413185203891715017661278469, 22405123, 4096, [], 413340372677461463606103791, 413340372677461471444471542⟩
def PrimData40.s30 : Seg := ⟨413340372677461463606103791, 413340372677461471444471542, 22413315, 4096, [], 413492110480331543444675309, 413492110480331551285920057⟩
def PrimData40.s31 : Seg := ⟨413492110480331543444675309, 413492110480331551285920057, 22421507, 4096, [], 413636670329753016164213434, 413636670329753024008198724⟩
def PrimData40.s32 : Seg := ⟨413636670329753016164213434, 413636670329753024008198724, 22429699, 4096, [], 413784667833596927601377785, 413784667833596935448169603⟩
def PrimData40.s33 : Seg := ⟨413784667833596927601377785, 413784667833596935448169603, 22437891, 4096, [], 413932668568814308560002445, 413932668568814316409600970⟩
def PrimData40.s34 : Seg := ⟨413932668568814308560002445, 413932668568814316409600970, 22446083, 4096, [], 414082858193282298534260007, 414082858193282306386705667⟩

def PrimData40.segs : List Seg := [PrimData40.s0, PrimData40.s1, PrimData40.s2, PrimData40.s3, PrimData40.s4, PrimData40.s5, PrimData40.s6, PrimData40.s7, PrimData40.s8, PrimData40.s9, PrimData40.s10, PrimData40.s11, PrimData40.s12, PrimData40.s13, PrimData40.s14, PrimData40.s15, PrimData40.s16, PrimData40.s17, PrimData40.s18, PrimData40.s19, PrimData40.s20, PrimData40.s21, PrimData40.s22, PrimData40.s23, PrimData40.s24, PrimData40.s25, PrimData40.s26, PrimData40.s27, PrimData40.s28, PrimData40.s29, PrimData40.s30, PrimData40.s31, PrimData40.s32, PrimData40.s33, PrimData40.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked40_s0 : Seg.bok PrimData40.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s0

theorem checked40_s1 : Seg.bok PrimData40.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s1

theorem checked40_s2 : Seg.bok PrimData40.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s2

theorem checked40_s3 : Seg.bok PrimData40.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s3

theorem checked40_s4 : Seg.bok PrimData40.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s4

theorem checked40_s5 : Seg.bok PrimData40.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s5

theorem checked40_s6 : Seg.bok PrimData40.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s6

theorem checked40_s7 : Seg.bok PrimData40.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s7

theorem checked40_s8 : Seg.bok PrimData40.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s8

theorem checked40_s9 : Seg.bok PrimData40.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s9

theorem checked40_s10 : Seg.bok PrimData40.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s10

theorem checked40_s11 : Seg.bok PrimData40.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s11

theorem checked40_s12 : Seg.bok PrimData40.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s12

theorem checked40_s13 : Seg.bok PrimData40.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s13

theorem checked40_s14 : Seg.bok PrimData40.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s14

theorem checked40_s15 : Seg.bok PrimData40.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s15

theorem checked40_s16 : Seg.bok PrimData40.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s16

theorem checked40_s17 : Seg.bok PrimData40.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s17

theorem checked40_s18 : Seg.bok PrimData40.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s18

theorem checked40_s19 : Seg.bok PrimData40.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s19

theorem checked40_s20 : Seg.bok PrimData40.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s20

theorem checked40_s21 : Seg.bok PrimData40.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s21

theorem checked40_s22 : Seg.bok PrimData40.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s22

theorem checked40_s23 : Seg.bok PrimData40.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s23

theorem checked40_s24 : Seg.bok PrimData40.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s24

theorem checked40_s25 : Seg.bok PrimData40.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s25

theorem checked40_s26 : Seg.bok PrimData40.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s26

theorem checked40_s27 : Seg.bok PrimData40.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s27

theorem checked40_s28 : Seg.bok PrimData40.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s28

theorem checked40_s29 : Seg.bok PrimData40.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s29

theorem checked40_s30 : Seg.bok PrimData40.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s30

theorem checked40_s31 : Seg.bok PrimData40.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s31

theorem checked40_s32 : Seg.bok PrimData40.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s32

theorem checked40_s33 : Seg.bok PrimData40.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s33

theorem checked40_s34 : Seg.bok PrimData40.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40_s34

 theorem checked40 : ∀ s ∈ PrimData40.segs, (Seg.bok s) = true := by
  unfold PrimData40.segs
  exact List.forall_mem_cons.2 ⟨checked40_s0, List.forall_mem_cons.2 ⟨checked40_s1, List.forall_mem_cons.2 ⟨checked40_s2, List.forall_mem_cons.2 ⟨checked40_s3, List.forall_mem_cons.2 ⟨checked40_s4, List.forall_mem_cons.2 ⟨checked40_s5, List.forall_mem_cons.2 ⟨checked40_s6, List.forall_mem_cons.2 ⟨checked40_s7, List.forall_mem_cons.2 ⟨checked40_s8, List.forall_mem_cons.2 ⟨checked40_s9, List.forall_mem_cons.2 ⟨checked40_s10, List.forall_mem_cons.2 ⟨checked40_s11, List.forall_mem_cons.2 ⟨checked40_s12, List.forall_mem_cons.2 ⟨checked40_s13, List.forall_mem_cons.2 ⟨checked40_s14, List.forall_mem_cons.2 ⟨checked40_s15, List.forall_mem_cons.2 ⟨checked40_s16, List.forall_mem_cons.2 ⟨checked40_s17, List.forall_mem_cons.2 ⟨checked40_s18, List.forall_mem_cons.2 ⟨checked40_s19, List.forall_mem_cons.2 ⟨checked40_s20, List.forall_mem_cons.2 ⟨checked40_s21, List.forall_mem_cons.2 ⟨checked40_s22, List.forall_mem_cons.2 ⟨checked40_s23, List.forall_mem_cons.2 ⟨checked40_s24, List.forall_mem_cons.2 ⟨checked40_s25, List.forall_mem_cons.2 ⟨checked40_s26, List.forall_mem_cons.2 ⟨checked40_s27, List.forall_mem_cons.2 ⟨checked40_s28, List.forall_mem_cons.2 ⟨checked40_s29, List.forall_mem_cons.2 ⟨checked40_s30, List.forall_mem_cons.2 ⟨checked40_s31, List.forall_mem_cons.2 ⟨checked40_s32, List.forall_mem_cons.2 ⟨checked40_s33, List.forall_mem_singleton.2 checked40_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked40
