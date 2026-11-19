/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_66.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/f852547a-95b5-480d-8de7-34b9a7d4b5c9
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData66.s0 : Seg := ⟨546314065634793531960823446, 546314065634793542320786848, 29622275, 4096, [], 546460369061941597135719341, 546460369061941607498456082⟩
def PrimData66.s1 : Seg := ⟨546460369061941597135719341, 546460369061941607498456082, 29630467, 4096, [], 546607944327694712572799929, 546607944327694722938334012⟩
def PrimData66.s2 : Seg := ⟨546607944327694712572799929, 546607944327694722938334012, 29638659, 4096, [], 546761551976844608259512096, 546761551976844618627958822⟩
def PrimData66.s3 : Seg := ⟨546761551976844608259512096, 546761551976844618627958822, 29646851, 4096, [], 546912623135825274074178993, 546912623135825284445490045⟩
def PrimData66.s4 : Seg := ⟨546912623135825274074178993, 546912623135825284445490045, 29655043, 4096, [], 547065918347543423095836231, 547065918347543433470053619⟩
def PrimData66.s5 : Seg := ⟨547065918347543423095836231, 547065918347543433470053619, 29663235, 4096, [], 547221755167344289139679207, 547221755167344299516851863⟩
def PrimData66.s6 : Seg := ⟨547221755167344289139679207, 547221755167344299516851863, 29671427, 4096, [], 547369977039787869597666266, 547369977039787879977648483⟩
def PrimData66.s7 : Seg := ⟨547369977039787869597666266, 547369977039787879977648483, 29679619, 4096, [], 547517566519575134217002480, 547517566519575144599782609⟩
def PrimData66.s8 : Seg := ⟨547517566519575134217002480, 547517566519575144599782609, 29687811, 4096, [], 547677219612463432807791815, 547677219612463443193599883⟩
def PrimData66.s9 : Seg := ⟨547677219612463432807791815, 547677219612463443193599883, 29696003, 4096, [], 547828305278843453217629529, 547828305278843463606302297⟩
def PrimData66.s10 : Seg := ⟨547828305278843453217629529, 547828305278843463606302297, 29704195, 4096, [], 547982250115002137776571587, 547982250115002148168163348⟩
def PrimData66.s11 : Seg := ⟨547982250115002137776571587, 547982250115002148168163348, 29712387, 4096, [], 548140006390187978787996648, 548140006390187989182580212⟩
def PrimData66.s12 : Seg := ⟨548140006390187978787996648, 548140006390187989182580212, 29720579, 4096, [], 548296495495268648883582656, 548296495495268659281133824⟩
def PrimData66.s13 : Seg := ⟨548296495495268648883582656, 548296495495268659281133824, 29728771, 4096, [], 548448543142213827335755570, 548448543142213837736188753⟩
def PrimData66.s14 : Seg := ⟨548448543142213827335755570, 548448543142213837736188753, 29736963, 4096, [], 548593609707970626514748798, 548593609707970636917931944⟩
def PrimData66.s15 : Seg := ⟨548593609707970626514748798, 548593609707970636917931944, 29745155, 4096, [], 548735186770290787667101857, 548735186770290798072968751⟩
def PrimData66.s16 : Seg := ⟨548735186770290787667101857, 548735186770290798072968751, 29753347, 4096, [], 548885654480712841866892050, 548885654480712852275611513⟩
def PrimData66.s17 : Seg := ⟨548885654480712841866892050, 548885654480712852275611513, 29761539, 4096, [], 549028188422351224749094680, 549028188422351235160516163⟩
def PrimData66.s18 : Seg := ⟨549028188422351224749094680, 549028188422351235160516163, 29769731, 4096, [], 549181518029016257110080107, 549181518029016267524408543⟩
def PrimData66.s19 : Seg := ⟨549181518029016257110080107, 549181518029016267524408543, 29777923, 4096, [], 549332310444643745647416411, 549332310444643756064604377⟩
def PrimData66.s20 : Seg := ⟨549332310444643745647416411, 549332310444643756064604377, 29786115, 4096, [], 549479613192824456008416822, 549479613192824466428397814⟩
def PrimData66.s21 : Seg := ⟨549479613192824456008416822, 549479613192824466428397814, 29794307, 4096, [], 549630727930220994875274513, 549630727930221005298121031⟩
def PrimData66.s22 : Seg := ⟨549630727930220994875274513, 549630727930221005298121031, 29802499, 4096, [], 549777717893339884901041637, 549777717893339895326674764⟩
def PrimData66.s23 : Seg := ⟨549777717893339884901041637, 549777717893339895326674764, 29810691, 4096, [], 549923757769874297030994438, 549923757769874307459396563⟩
def PrimData66.s24 : Seg := ⟨549923757769874297030994438, 549923757769874307459396563, 29818883, 4096, [], 550075514650725396088078924, 550075514650725406519358455⟩
def PrimData66.s25 : Seg := ⟨550075514650725396088078924, 550075514650725406519358455, 29827075, 4096, [], 550227591438774598285266978, 550227591438774608719430365⟩
def PrimData66.s26 : Seg := ⟨550227591438774598285266978, 550227591438774608719430365, 29835267, 4096, [], 550379988160214764750086874, 550379988160214775187139377⟩
def PrimData66.s27 : Seg := ⟨550379988160214764750086874, 550379988160214775187139377, 29843459, 4096, [], 550536832303415137854060167, 550536832303415148294086198⟩
def PrimData66.s28 : Seg := ⟨550536832303415137854060167, 550536832303415148294086198, 29851651, 4096, [], 550696853991008755307657893, 550696853991008765750718598⟩
def PrimData66.s29 : Seg := ⟨550696853991008755307657893, 550696853991008765750718598, 29859843, 4096, [], 550851798115896711423535113, 550851798115896721869533860⟩
def PrimData66.s30 : Seg := ⟨550851798115896711423535113, 550851798115896721869533860, 29868035, 4096, [], 551002616986696511100356561, 551002616986696521549215776⟩
def PrimData66.s31 : Seg := ⟨551002616986696511100356561, 551002616986696521549215776, 29876227, 4096, [], 551155978427372069794961404, 551155978427372080246729132⟩
def PrimData66.s32 : Seg := ⟨551155978427372069794961404, 551155978427372080246729132, 29884419, 4096, [], 551308707212925656848056132, 551308707212925667302719979⟩
def PrimData66.s33 : Seg := ⟨551308707212925656848056132, 551308707212925667302719979, 29892611, 4096, [], 551464296191052592108907435, 551464296191052602566522372⟩
def PrimData66.s34 : Seg := ⟨551464296191052592108907435, 551464296191052602566522372, 29900803, 4096, [], 551607503847923806151755934, 551607503847923816612086999⟩

def PrimData66.segs : List Seg := [PrimData66.s0, PrimData66.s1, PrimData66.s2, PrimData66.s3, PrimData66.s4, PrimData66.s5, PrimData66.s6, PrimData66.s7, PrimData66.s8, PrimData66.s9, PrimData66.s10, PrimData66.s11, PrimData66.s12, PrimData66.s13, PrimData66.s14, PrimData66.s15, PrimData66.s16, PrimData66.s17, PrimData66.s18, PrimData66.s19, PrimData66.s20, PrimData66.s21, PrimData66.s22, PrimData66.s23, PrimData66.s24, PrimData66.s25, PrimData66.s26, PrimData66.s27, PrimData66.s28, PrimData66.s29, PrimData66.s30, PrimData66.s31, PrimData66.s32, PrimData66.s33, PrimData66.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked66_s0 : Seg.bok PrimData66.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s0

theorem checked66_s1 : Seg.bok PrimData66.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s1

theorem checked66_s2 : Seg.bok PrimData66.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s2

theorem checked66_s3 : Seg.bok PrimData66.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s3

theorem checked66_s4 : Seg.bok PrimData66.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s4

theorem checked66_s5 : Seg.bok PrimData66.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s5

theorem checked66_s6 : Seg.bok PrimData66.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s6

theorem checked66_s7 : Seg.bok PrimData66.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s7

theorem checked66_s8 : Seg.bok PrimData66.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s8

theorem checked66_s9 : Seg.bok PrimData66.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s9

theorem checked66_s10 : Seg.bok PrimData66.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s10

theorem checked66_s11 : Seg.bok PrimData66.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s11

theorem checked66_s12 : Seg.bok PrimData66.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s12

theorem checked66_s13 : Seg.bok PrimData66.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s13

theorem checked66_s14 : Seg.bok PrimData66.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s14

theorem checked66_s15 : Seg.bok PrimData66.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s15

theorem checked66_s16 : Seg.bok PrimData66.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s16

theorem checked66_s17 : Seg.bok PrimData66.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s17

theorem checked66_s18 : Seg.bok PrimData66.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s18

theorem checked66_s19 : Seg.bok PrimData66.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s19

theorem checked66_s20 : Seg.bok PrimData66.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s20

theorem checked66_s21 : Seg.bok PrimData66.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s21

theorem checked66_s22 : Seg.bok PrimData66.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s22

theorem checked66_s23 : Seg.bok PrimData66.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s23

theorem checked66_s24 : Seg.bok PrimData66.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s24

theorem checked66_s25 : Seg.bok PrimData66.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s25

theorem checked66_s26 : Seg.bok PrimData66.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s26

theorem checked66_s27 : Seg.bok PrimData66.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s27

theorem checked66_s28 : Seg.bok PrimData66.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s28

theorem checked66_s29 : Seg.bok PrimData66.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s29

theorem checked66_s30 : Seg.bok PrimData66.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s30

theorem checked66_s31 : Seg.bok PrimData66.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s31

theorem checked66_s32 : Seg.bok PrimData66.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s32

theorem checked66_s33 : Seg.bok PrimData66.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s33

theorem checked66_s34 : Seg.bok PrimData66.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66_s34

 theorem checked66 : ∀ s ∈ PrimData66.segs, (Seg.bok s) = true := by
  unfold PrimData66.segs
  exact List.forall_mem_cons.2 ⟨checked66_s0, List.forall_mem_cons.2 ⟨checked66_s1, List.forall_mem_cons.2 ⟨checked66_s2, List.forall_mem_cons.2 ⟨checked66_s3, List.forall_mem_cons.2 ⟨checked66_s4, List.forall_mem_cons.2 ⟨checked66_s5, List.forall_mem_cons.2 ⟨checked66_s6, List.forall_mem_cons.2 ⟨checked66_s7, List.forall_mem_cons.2 ⟨checked66_s8, List.forall_mem_cons.2 ⟨checked66_s9, List.forall_mem_cons.2 ⟨checked66_s10, List.forall_mem_cons.2 ⟨checked66_s11, List.forall_mem_cons.2 ⟨checked66_s12, List.forall_mem_cons.2 ⟨checked66_s13, List.forall_mem_cons.2 ⟨checked66_s14, List.forall_mem_cons.2 ⟨checked66_s15, List.forall_mem_cons.2 ⟨checked66_s16, List.forall_mem_cons.2 ⟨checked66_s17, List.forall_mem_cons.2 ⟨checked66_s18, List.forall_mem_cons.2 ⟨checked66_s19, List.forall_mem_cons.2 ⟨checked66_s20, List.forall_mem_cons.2 ⟨checked66_s21, List.forall_mem_cons.2 ⟨checked66_s22, List.forall_mem_cons.2 ⟨checked66_s23, List.forall_mem_cons.2 ⟨checked66_s24, List.forall_mem_cons.2 ⟨checked66_s25, List.forall_mem_cons.2 ⟨checked66_s26, List.forall_mem_cons.2 ⟨checked66_s27, List.forall_mem_cons.2 ⟨checked66_s28, List.forall_mem_cons.2 ⟨checked66_s29, List.forall_mem_cons.2 ⟨checked66_s30, List.forall_mem_cons.2 ⟨checked66_s31, List.forall_mem_cons.2 ⟨checked66_s32, List.forall_mem_cons.2 ⟨checked66_s33, List.forall_mem_singleton.2 checked66_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked66
