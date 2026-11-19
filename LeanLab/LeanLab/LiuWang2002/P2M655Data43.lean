/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_43.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/4ed291a2-6503-4607-9f52-6c7a26d89ab2
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData43.s0 : Seg := ⟨424700351423881678638417722, 424700351423881686692232531, 23027715, 4096, [], 424849204393728305080384532, 424849204393728313137022645⟩
def PrimData43.s1 : Seg := ⟨424849204393728305080384532, 424849204393728313137022645, 23035907, 4096, [], 425001187741176074971645220, 425001187741176083031165974⟩
def PrimData43.s2 : Seg := ⟨425001187741176074971645220, 425001187741176083031165974, 23044099, 4096, [], 425154425216081016404342937, 425154425216081024466770160⟩
def PrimData43.s3 : Seg := ⟨425154425216081016404342937, 425154425216081024466770160, 23052291, 4096, [], 425304851238227261726476837, 425304851238227269791757482⟩
def PrimData43.s4 : Seg := ⟨425304851238227261726476837, 425304851238227269791757482, 23060483, 4096, [], 425452465769442631241146182, 425452465769442639309226546⟩
def PrimData43.s5 : Seg := ⟨425452465769442631241146182, 425452465769442639309226546, 23068675, 4096, [], 425606025595109812747883158, 425606025595109820818876236⟩
def PrimData43.s6 : Seg := ⟨425606025595109812747883158, 425606025595109820818876236, 23076867, 4096, [], 425751769678263352562591306, 425751769678263360636348534⟩
def PrimData43.s7 : Seg := ⟨425751769678263352562591306, 425751769678263360636348534, 23085059, 4096, [], 425898455122802441535332475, 425898455122802449611871031⟩
def PrimData43.s8 : Seg := ⟨425898455122802441535332475, 425898455122802449611871031, 23093251, 4096, [], 426047958580825193856816311, 426047958580825201936191025⟩
def PrimData43.s9 : Seg := ⟨426047958580825193856816311, 426047958580825201936191025, 23101443, 4096, [], 426203407891356756765487505, 426203407891356764847810638⟩
def PrimData43.s10 : Seg := ⟨426203407891356756765487505, 426203407891356764847810638, 23109635, 4096, [], 426353855947607486306610123, 426353855947607494391786439⟩
def PrimData43.s11 : Seg := ⟨426353855947607486306610123, 426353855947607494391786439, 23117827, 4096, [], 426497113014465312489492177, 426497113014465320577383893⟩
def PrimData43.s12 : Seg := ⟨426497113014465312489492177, 426497113014465320577383893, 23126019, 4096, [], 426645377787711023513890998, 426645377787711031604593859⟩
def PrimData43.s13 : Seg := ⟨426645377787711023513890998, 426645377787711031604593859, 23134211, 4096, [], 426799276032291975738724548, 426799276032291983832345959⟩
def PrimData43.s14 : Seg := ⟨426799276032291975738724548, 426799276032291983832345959, 23142403, 4096, [], 426950362267299827937135892, 426950362267299836033622393⟩
def PrimData43.s15 : Seg := ⟨426950362267299827937135892, 426950362267299836033622393, 23150595, 4096, [], 427106769538059465968303125, 427106769538059474067756315⟩
def PrimData43.s16 : Seg := ⟨427106769538059465968303125, 427106769538059474067756315, 23158787, 4096, [], 427271000625356541660963308, 427271000625356549763531659⟩
def PrimData43.s17 : Seg := ⟨427271000625356541660963308, 427271000625356549763531659, 23166979, 4096, [], 427422409164906962224249847, 427422409164906970329688634⟩
def PrimData43.s18 : Seg := ⟨427422409164906962224249847, 427422409164906970329688634, 23175171, 4096, [], 427568502714390603436874285, 427568502714390611545083153⟩
def PrimData43.s19 : Seg := ⟨427568502714390603436874285, 427568502714390611545083153, 23183363, 4096, [], 427710219507703883833547513, 427710219507703891944442893⟩
def PrimData43.s20 : Seg := ⟨427710219507703883833547513, 427710219507703891944442893, 23191555, 4096, [], 427856944809094088127278692, 427856944809094096240954845⟩
def PrimData43.s21 : Seg := ⟨427856944809094088127278692, 427856944809094096240954845, 23199747, 4096, [], 428006801644156707931352371, 428006801644156716047869319⟩
def PrimData43.s22 : Seg := ⟨428006801644156707931352371, 428006801644156716047869319, 23207939, 4096, [], 428156974526009748040925004, 428156974526009756160289571⟩
def PrimData43.s23 : Seg := ⟨428156974526009748040925004, 428156974526009756160289571, 23216131, 4096, [], 428309653432675642744900807, 428309653432675650867160601⟩
def PrimData43.s24 : Seg := ⟨428309653432675642744900807, 428309653432675650867160601, 23224323, 4096, [], 428458893918429781520043323, 428458893918429789645132009⟩
def PrimData43.s25 : Seg := ⟨428458893918429781520043323, 428458893918429789645132009, 23232515, 4096, [], 428609389010124291302018368, 428609389010124299429960249⟩
def PrimData43.s26 : Seg := ⟨428609389010124291302018368, 428609389010124299429960249, 23240707, 4096, [], 428761138808895277047533206, 428761138808895285178352088⟩
def PrimData43.s27 : Seg := ⟨428761138808895277047533206, 428761138808895285178352088, 23248899, 4096, [], 428909762812683765151890105, 428909762812683773285526988⟩
def PrimData43.s28 : Seg := ⟨428909762812683765151890105, 428909762812683773285526988, 23257091, 4096, [], 429065899480594187518616752, 429065899480594195655214235⟩
def PrimData43.s29 : Seg := ⟨429065899480594187518616752, 429065899480594195655214235, 23265283, 4096, [], 429222352324316007753793621, 429222352324316015893356579⟩
def PrimData43.s30 : Seg := ⟨429222352324316007753793621, 429222352324316015893356579, 23273475, 4096, [], 429376305123993098940090852, 429376305123993107082571645⟩
def PrimData43.s31 : Seg := ⟨429376305123993098940090852, 429376305123993107082571645, 23281667, 4096, [], 429527444780371159389742750, 429527444780371167535089416⟩
def PrimData43.s32 : Seg := ⟨429527444780371159389742750, 429527444780371167535089416, 23289859, 4096, [], 429676397174161538450568108, 429676397174161546598738570⟩
def PrimData43.s33 : Seg := ⟨429676397174161538450568108, 429676397174161546598738570, 23298051, 4096, [], 429831611249275489207844527, 429831611249275497358957384⟩
def PrimData43.s34 : Seg := ⟨429831611249275489207844527, 429831611249275497358957384, 23306243, 4096, [], 429988080272715774049923244, 429988080272715782204002048⟩

def PrimData43.segs : List Seg := [PrimData43.s0, PrimData43.s1, PrimData43.s2, PrimData43.s3, PrimData43.s4, PrimData43.s5, PrimData43.s6, PrimData43.s7, PrimData43.s8, PrimData43.s9, PrimData43.s10, PrimData43.s11, PrimData43.s12, PrimData43.s13, PrimData43.s14, PrimData43.s15, PrimData43.s16, PrimData43.s17, PrimData43.s18, PrimData43.s19, PrimData43.s20, PrimData43.s21, PrimData43.s22, PrimData43.s23, PrimData43.s24, PrimData43.s25, PrimData43.s26, PrimData43.s27, PrimData43.s28, PrimData43.s29, PrimData43.s30, PrimData43.s31, PrimData43.s32, PrimData43.s33, PrimData43.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked43_s0 : Seg.bok PrimData43.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s0

theorem checked43_s1 : Seg.bok PrimData43.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s1

theorem checked43_s2 : Seg.bok PrimData43.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s2

theorem checked43_s3 : Seg.bok PrimData43.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s3

theorem checked43_s4 : Seg.bok PrimData43.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s4

theorem checked43_s5 : Seg.bok PrimData43.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s5

theorem checked43_s6 : Seg.bok PrimData43.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s6

theorem checked43_s7 : Seg.bok PrimData43.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s7

theorem checked43_s8 : Seg.bok PrimData43.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s8

theorem checked43_s9 : Seg.bok PrimData43.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s9

theorem checked43_s10 : Seg.bok PrimData43.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s10

theorem checked43_s11 : Seg.bok PrimData43.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s11

theorem checked43_s12 : Seg.bok PrimData43.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s12

theorem checked43_s13 : Seg.bok PrimData43.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s13

theorem checked43_s14 : Seg.bok PrimData43.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s14

theorem checked43_s15 : Seg.bok PrimData43.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s15

theorem checked43_s16 : Seg.bok PrimData43.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s16

theorem checked43_s17 : Seg.bok PrimData43.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s17

theorem checked43_s18 : Seg.bok PrimData43.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s18

theorem checked43_s19 : Seg.bok PrimData43.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s19

theorem checked43_s20 : Seg.bok PrimData43.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s20

theorem checked43_s21 : Seg.bok PrimData43.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s21

theorem checked43_s22 : Seg.bok PrimData43.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s22

theorem checked43_s23 : Seg.bok PrimData43.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s23

theorem checked43_s24 : Seg.bok PrimData43.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s24

theorem checked43_s25 : Seg.bok PrimData43.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s25

theorem checked43_s26 : Seg.bok PrimData43.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s26

theorem checked43_s27 : Seg.bok PrimData43.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s27

theorem checked43_s28 : Seg.bok PrimData43.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s28

theorem checked43_s29 : Seg.bok PrimData43.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s29

theorem checked43_s30 : Seg.bok PrimData43.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s30

theorem checked43_s31 : Seg.bok PrimData43.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s31

theorem checked43_s32 : Seg.bok PrimData43.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s32

theorem checked43_s33 : Seg.bok PrimData43.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s33

theorem checked43_s34 : Seg.bok PrimData43.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43_s34

 theorem checked43 : ∀ s ∈ PrimData43.segs, (Seg.bok s) = true := by
  unfold PrimData43.segs
  exact List.forall_mem_cons.2 ⟨checked43_s0, List.forall_mem_cons.2 ⟨checked43_s1, List.forall_mem_cons.2 ⟨checked43_s2, List.forall_mem_cons.2 ⟨checked43_s3, List.forall_mem_cons.2 ⟨checked43_s4, List.forall_mem_cons.2 ⟨checked43_s5, List.forall_mem_cons.2 ⟨checked43_s6, List.forall_mem_cons.2 ⟨checked43_s7, List.forall_mem_cons.2 ⟨checked43_s8, List.forall_mem_cons.2 ⟨checked43_s9, List.forall_mem_cons.2 ⟨checked43_s10, List.forall_mem_cons.2 ⟨checked43_s11, List.forall_mem_cons.2 ⟨checked43_s12, List.forall_mem_cons.2 ⟨checked43_s13, List.forall_mem_cons.2 ⟨checked43_s14, List.forall_mem_cons.2 ⟨checked43_s15, List.forall_mem_cons.2 ⟨checked43_s16, List.forall_mem_cons.2 ⟨checked43_s17, List.forall_mem_cons.2 ⟨checked43_s18, List.forall_mem_cons.2 ⟨checked43_s19, List.forall_mem_cons.2 ⟨checked43_s20, List.forall_mem_cons.2 ⟨checked43_s21, List.forall_mem_cons.2 ⟨checked43_s22, List.forall_mem_cons.2 ⟨checked43_s23, List.forall_mem_cons.2 ⟨checked43_s24, List.forall_mem_cons.2 ⟨checked43_s25, List.forall_mem_cons.2 ⟨checked43_s26, List.forall_mem_cons.2 ⟨checked43_s27, List.forall_mem_cons.2 ⟨checked43_s28, List.forall_mem_cons.2 ⟨checked43_s29, List.forall_mem_cons.2 ⟨checked43_s30, List.forall_mem_cons.2 ⟨checked43_s31, List.forall_mem_cons.2 ⟨checked43_s32, List.forall_mem_cons.2 ⟨checked43_s33, List.forall_mem_singleton.2 checked43_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked43
