/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_53.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/bbd8af97-f014-4c78-a46a-565038a2392e
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData53.s0 : Seg := ⟨477567915713887447061309141, 477567915713887456117635491, 25894915, 4096, [], 477713075686054196522531093, 477713075686054205581611007⟩
def PrimData53.s1 : Seg := ⟨477713075686054196522531093, 477713075686054205581611007, 25903107, 4096, [], 477861387233017644153131990, 477861387233017653215025742⟩
def PrimData53.s2 : Seg := ⟨477861387233017644153131990, 477861387233017653215025742, 25911299, 4096, [], 478014424881069933149030776, 478014424881069942213828045⟩
def PrimData53.s3 : Seg := ⟨478014424881069933149030776, 478014424881069942213828045, 25919491, 4096, [], 478169669700215571261055804, 478169669700215580328798374⟩
def PrimData53.s4 : Seg := ⟨478169669700215571261055804, 478169669700215580328798374, 25927683, 4096, [], 478326491925614198086828023, 478326491925614207157545780⟩
def PrimData53.s5 : Seg := ⟨478326491925614198086828023, 478326491925614207157545780, 25935875, 4096, [], 478477018830081452264886608, 478477018830081461338459764⟩
def PrimData53.s6 : Seg := ⟨478477018830081452264886608, 478477018830081461338459764, 25944067, 4096, [], 478621250209750920556087612, 478621250209750929632395474⟩
def PrimData53.s7 : Seg := ⟨478621250209750920556087612, 478621250209750929632395474, 25952259, 4096, [], 478763909599339652223884086, 478763909599339661302898379⟩
def PrimData53.s8 : Seg := ⟨478763909599339652223884086, 478763909599339661302898379, 25960451, 4096, [], 478918538897433396770923523, 478918538897433405852871065⟩
def PrimData53.s9 : Seg := ⟨478918538897433396770923523, 478918538897433405852871065, 25968643, 4096, [], 479076005472801139168977550, 479076005472801148253910910⟩
def PrimData53.s10 : Seg := ⟨479076005472801139168977550, 479076005472801148253910910, 25976835, 4096, [], 479231585326689523971500681, 479231585326689533059384066⟩
def PrimData53.s11 : Seg := ⟨479231585326689523971500681, 479231585326689533059384066, 25985027, 4096, [], 479387168085512737060088428, 479387168085512746150921757⟩
def PrimData53.s12 : Seg := ⟨479387168085512737060088428, 479387168085512746150921757, 25993219, 4096, [], 479533305162506949771583911, 479533305162506958865189453⟩
def PrimData53.s13 : Seg := ⟨479533305162506949771583911, 479533305162506958865189453, 26001411, 4096, [], 479681019680895170245954718, 479681019680895179342360591⟩
def PrimData53.s14 : Seg := ⟨479681019680895170245954718, 479681019680895179342360591, 26009603, 4096, [], 479832516500516974131303734, 479832516500516983230583340⟩
def PrimData53.s15 : Seg := ⟨479832516500516974131303734, 479832516500516983230583340, 26017795, 4096, [], 479979921531806548442708524, 479979921531806557544782653⟩
def PrimData53.s16 : Seg := ⟨479979921531806548442708524, 479979921531806557544782653, 26025987, 4096, [], 480129849040556111001352690, 480129849040556120106270540⟩
def PrimData53.s17 : Seg := ⟨480129849040556111001352690, 480129849040556120106270540, 26034179, 4096, [], 480288283793051904629218775, 480288283793051913737142507⟩
def PrimData53.s18 : Seg := ⟨480288283793051904629218775, 480288283793051913737142507, 26042371, 4096, [], 480434752013523027665047060, 480434752013523036775747203⟩
def PrimData53.s19 : Seg := ⟨480434752013523027665047060, 480434752013523036775747203, 26050563, 4096, [], 480587522763939165261366010, 480587522763939174374964213⟩
def PrimData53.s20 : Seg := ⟨480587522763939165261366010, 480587522763939174374964213, 26058755, 4096, [], 480742501284388809233918295, 480742501284388818350455814⟩
def PrimData53.s21 : Seg := ⟨480742501284388809233918295, 480742501284388818350455814, 26066947, 4096, [], 480890867646698275485367367, 480890867646698284604718874⟩
def PrimData53.s22 : Seg := ⟨480890867646698275485367367, 480890867646698284604718874, 26075139, 4096, [], 481033881585219081300533744, 481033881585219090422597231⟩
def PrimData53.s23 : Seg := ⟨481033881585219081300533744, 481033881585219090422597231, 26083331, 4096, [], 481191073755939810368584134, 481191073755939819493629347⟩
def PrimData53.s24 : Seg := ⟨481191073755939810368584134, 481191073755939819493629347, 26091523, 4096, [], 481343228476559347630108957, 481343228476559356758038236⟩
def PrimData53.s25 : Seg := ⟨481343228476559347630108957, 481343228476559356758038236, 26099715, 4096, [], 481487825352985169669753312, 481487825352985178800424272⟩
def PrimData53.s26 : Seg := ⟨481487825352985169669753312, 481487825352985178800424272, 26107907, 4096, [], 481638725560015080548244638, 481638725560015089681776581⟩
def PrimData53.s27 : Seg := ⟨481638725560015080548244638, 481638725560015089681776581, 26116099, 4096, [], 481798134555081169549274280, 481798134555081178685829502⟩
def PrimData53.s28 : Seg := ⟨481798134555081169549274280, 481798134555081178685829502, 26124291, 4096, [], 481951875702144195642115557, 481951875702144204781587215⟩
def PrimData53.s29 : Seg := ⟨481951875702144195642115557, 481951875702144204781587215, 26132483, 4096, [], 482101208981583533699877264, 482101208981583542842181219⟩
def PrimData53.s30 : Seg := ⟨482101208981583533699877264, 482101208981583542842181219, 26140675, 4096, [], 482250860059278450669825300, 482250860059278459814967035⟩
def PrimData53.s31 : Seg := ⟨482250860059278450669825300, 482250860059278459814967035, 26148867, 4096, [], 482398938561565413085285334, 482398938561565422233234355⟩
def PrimData53.s32 : Seg := ⟨482398938561565413085285334, 482398938561565422233234355, 26157059, 4096, [], 482555526571481192098789852, 482555526571481201249709184⟩
def PrimData53.s33 : Seg := ⟨482555526571481192098789852, 482555526571481201249709184, 26165251, 4096, [], 482700774859338085434073556, 482700774859338094587747043⟩
def PrimData53.s34 : Seg := ⟨482700774859338085434073556, 482700774859338094587747043, 26173443, 4096, [], 482852957513111965057082194, 482852957513111974213641000⟩

def PrimData53.segs : List Seg := [PrimData53.s0, PrimData53.s1, PrimData53.s2, PrimData53.s3, PrimData53.s4, PrimData53.s5, PrimData53.s6, PrimData53.s7, PrimData53.s8, PrimData53.s9, PrimData53.s10, PrimData53.s11, PrimData53.s12, PrimData53.s13, PrimData53.s14, PrimData53.s15, PrimData53.s16, PrimData53.s17, PrimData53.s18, PrimData53.s19, PrimData53.s20, PrimData53.s21, PrimData53.s22, PrimData53.s23, PrimData53.s24, PrimData53.s25, PrimData53.s26, PrimData53.s27, PrimData53.s28, PrimData53.s29, PrimData53.s30, PrimData53.s31, PrimData53.s32, PrimData53.s33, PrimData53.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked53_s0 : Seg.bok PrimData53.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s0

theorem checked53_s1 : Seg.bok PrimData53.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s1

theorem checked53_s2 : Seg.bok PrimData53.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s2

theorem checked53_s3 : Seg.bok PrimData53.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s3

theorem checked53_s4 : Seg.bok PrimData53.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s4

theorem checked53_s5 : Seg.bok PrimData53.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s5

theorem checked53_s6 : Seg.bok PrimData53.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s6

theorem checked53_s7 : Seg.bok PrimData53.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s7

theorem checked53_s8 : Seg.bok PrimData53.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s8

theorem checked53_s9 : Seg.bok PrimData53.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s9

theorem checked53_s10 : Seg.bok PrimData53.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s10

theorem checked53_s11 : Seg.bok PrimData53.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s11

theorem checked53_s12 : Seg.bok PrimData53.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s12

theorem checked53_s13 : Seg.bok PrimData53.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s13

theorem checked53_s14 : Seg.bok PrimData53.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s14

theorem checked53_s15 : Seg.bok PrimData53.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s15

theorem checked53_s16 : Seg.bok PrimData53.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s16

theorem checked53_s17 : Seg.bok PrimData53.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s17

theorem checked53_s18 : Seg.bok PrimData53.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s18

theorem checked53_s19 : Seg.bok PrimData53.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s19

theorem checked53_s20 : Seg.bok PrimData53.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s20

theorem checked53_s21 : Seg.bok PrimData53.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s21

theorem checked53_s22 : Seg.bok PrimData53.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s22

theorem checked53_s23 : Seg.bok PrimData53.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s23

theorem checked53_s24 : Seg.bok PrimData53.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s24

theorem checked53_s25 : Seg.bok PrimData53.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s25

theorem checked53_s26 : Seg.bok PrimData53.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s26

theorem checked53_s27 : Seg.bok PrimData53.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s27

theorem checked53_s28 : Seg.bok PrimData53.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s28

theorem checked53_s29 : Seg.bok PrimData53.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s29

theorem checked53_s30 : Seg.bok PrimData53.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s30

theorem checked53_s31 : Seg.bok PrimData53.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s31

theorem checked53_s32 : Seg.bok PrimData53.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s32

theorem checked53_s33 : Seg.bok PrimData53.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s33

theorem checked53_s34 : Seg.bok PrimData53.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53_s34

 theorem checked53 : ∀ s ∈ PrimData53.segs, (Seg.bok s) = true := by
  unfold PrimData53.segs
  exact List.forall_mem_cons.2 ⟨checked53_s0, List.forall_mem_cons.2 ⟨checked53_s1, List.forall_mem_cons.2 ⟨checked53_s2, List.forall_mem_cons.2 ⟨checked53_s3, List.forall_mem_cons.2 ⟨checked53_s4, List.forall_mem_cons.2 ⟨checked53_s5, List.forall_mem_cons.2 ⟨checked53_s6, List.forall_mem_cons.2 ⟨checked53_s7, List.forall_mem_cons.2 ⟨checked53_s8, List.forall_mem_cons.2 ⟨checked53_s9, List.forall_mem_cons.2 ⟨checked53_s10, List.forall_mem_cons.2 ⟨checked53_s11, List.forall_mem_cons.2 ⟨checked53_s12, List.forall_mem_cons.2 ⟨checked53_s13, List.forall_mem_cons.2 ⟨checked53_s14, List.forall_mem_cons.2 ⟨checked53_s15, List.forall_mem_cons.2 ⟨checked53_s16, List.forall_mem_cons.2 ⟨checked53_s17, List.forall_mem_cons.2 ⟨checked53_s18, List.forall_mem_cons.2 ⟨checked53_s19, List.forall_mem_cons.2 ⟨checked53_s20, List.forall_mem_cons.2 ⟨checked53_s21, List.forall_mem_cons.2 ⟨checked53_s22, List.forall_mem_cons.2 ⟨checked53_s23, List.forall_mem_cons.2 ⟨checked53_s24, List.forall_mem_cons.2 ⟨checked53_s25, List.forall_mem_cons.2 ⟨checked53_s26, List.forall_mem_cons.2 ⟨checked53_s27, List.forall_mem_cons.2 ⟨checked53_s28, List.forall_mem_cons.2 ⟨checked53_s29, List.forall_mem_cons.2 ⟨checked53_s30, List.forall_mem_cons.2 ⟨checked53_s31, List.forall_mem_cons.2 ⟨checked53_s32, List.forall_mem_cons.2 ⟨checked53_s33, List.forall_mem_singleton.2 checked53_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked53
