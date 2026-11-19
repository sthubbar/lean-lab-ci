/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_46.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/a4443ec0-adf9-45b6-ad10-8212a3efc56f
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData46.s0 : Seg := ⟨440536143894211984388836171, 440536143894211992742914444, 23887875, 4096, [], 440689706279407873090760158, 440689706279407881447752846⟩
def PrimData46.s1 : Seg := ⟨440689706279407873090760158, 440689706279407881447752846, 23896067, 4096, [], 440843271818350216076724880, 440843271818350224436631983⟩
def PrimData46.s2 : Seg := ⟨440843271818350216076724880, 440843271818350224436631983, 23904259, 4096, [], 441002795138404449621507485, 441002795138404457984442241⟩
def PrimData46.s3 : Seg := ⟨441002795138404449621507485, 441002795138404457984442241, 23912451, 4096, [], 441153546107825903959638250, 441153546107825912325433475⟩
def PrimData46.s4 : Seg := ⟨441153546107825903959638250, 441153546107825912325433475, 23920643, 4096, [], 441303046527451346484488800, 441303046527451354853120437⟩
def PrimData46.s5 : Seg := ⟨441303046527451346484488800, 441303046527451354853120437, 23928835, 4096, [], 441450669352205797904359806, 441450669352205806275792134⟩
def PrimData46.s6 : Seg := ⟨441450669352205797904359806, 441450669352205806275792134, 23937027, 4096, [], 441606130902596930103764219, 441606130902596938478145954⟩
def PrimData46.s7 : Seg := ⟨441606130902596930103764219, 441606130902596938478145954, 23945219, 4096, [], 441751565606940368294982256, 441751565606940376672124101⟩
def PrimData46.s8 : Seg := ⟨441751565606940368294982256, 441751565606940376672124101, 23953411, 4096, [], 441900137682431352115131461, 441900137682431360495092465⟩
def PrimData46.s9 : Seg := ⟨441900137682431352115131461, 441900137682431360495092465, 23961603, 4096, [], 442051533831847452490406342, 442051533831847460873239965⟩
def PrimData46.s10 : Seg := ⟨442051533831847452490406342, 442051533831847460873239965, 23969795, 4096, [], 442201992635875525335743536, 442201992635875533721432525⟩
def PrimData46.s11 : Seg := ⟨442201992635875525335743536, 442201992635875533721432525, 23977987, 4096, [], 442354648730267842997379667, 442354648730267851385965089⟩
def PrimData46.s12 : Seg := ⟨442354648730267842997379667, 442354648730267851385965089, 23986179, 4096, [], 442509815677638528130344996, 442509815677638536521875451⟩
def PrimData46.s13 : Seg := ⟨442509815677638528130344996, 442509815677638536521875451, 23994371, 4096, [], 442661224001669455737693725, 442661224001669464132096799⟩
def PrimData46.s14 : Seg := ⟨442661224001669455737693725, 442661224001669464132096799, 24002563, 4096, [], 442818904966834905614264381, 442818904966834914011659144⟩
def PrimData46.s15 : Seg := ⟨442818904966834905614264381, 442818904966834914011659144, 24010755, 4096, [], 442964990081371107122107266, 442964990081371115522273803⟩
def PrimData46.s16 : Seg := ⟨442964990081371107122107266, 442964990081371115522273803, 24018947, 4096, [], 443116407493996378454620138, 443116407493996386857659537⟩
def PrimData46.s17 : Seg := ⟨443116407493996378454620138, 443116407493996386857659537, 24027139, 4096, [], 443262184932119742921137304, 443262184932119751326942402⟩
def PrimData46.s18 : Seg := ⟨443262184932119742921137304, 443262184932119751326942402, 24035331, 4096, [], 443423013618439163662425217, 443423013618439172071282025⟩
def PrimData46.s19 : Seg := ⟨443423013618439163662425217, 443423013618439172071282025, 24043523, 4096, [], 443571305098296635727854002, 443571305098296644139523894⟩
def PrimData46.s20 : Seg := ⟨443571305098296635727854002, 443571305098296644139523894, 24051715, 4096, [], 443726496925738142759042418, 443726496925738151173656371⟩
def PrimData46.s21 : Seg := ⟨443726496925738142759042418, 443726496925738151173656371, 24059907, 4096, [], 443876048392931726423206366, 443876048392931734840656974⟩
def PrimData46.s22 : Seg := ⟨443876048392931726423206366, 443876048392931734840656974, 24068099, 4096, [], 444026543441380434846311794, 444026543441380443266617039⟩
def PrimData46.s23 : Seg := ⟨444026543441380434846311794, 444026543441380443266617039, 24076291, 4096, [], 444177982101429819546370901, 444177982101429827969548279⟩
def PrimData46.s24 : Seg := ⟨444177982101429819546370901, 444177982101429827969548279, 24084483, 4096, [], 444324093500446200411521075, 444324093500446208837470227⟩
def PrimData46.s25 : Seg := ⟨444324093500446200411521075, 444324093500446208837470227, 24092675, 4096, [], 444470521423769692709442091, 444470521423769701138168606⟩
def PrimData46.s26 : Seg := ⟨444470521423769692709442091, 444470521423769701138168606, 24100867, 4096, [], 444623536957804529486992004, 444623536957804537918621270⟩
def PrimData46.s27 : Seg := ⟨444623536957804529486992004, 444623536957804537918621270, 24109059, 4096, [], 444776869133957684711172179, 444776869133957693145709056⟩
def PrimData46.s28 : Seg := ⟨444776869133957684711172179, 444776869133957693145709056, 24117251, 4096, [], 444917661618263824483622276, 444917661618263832920829110⟩
def PrimData46.s29 : Seg := ⟨444917661618263824483622276, 444917661618263832920829110, 24125443, 4096, [], 445068491339419547363126018, 445068491339419555803193807⟩
def PrimData46.s30 : Seg := ⟨445068491339419547363126018, 445068491339419555803193807, 24133635, 4096, [], 445216188168193500566962534, 445216188168193509009831500⟩
def PrimData46.s31 : Seg := ⟨445216188168193500566962534, 445216188168193509009831500, 24141827, 4096, [], 445377372233371453783735363, 445377372233371462229661385⟩
def PrimData46.s32 : Seg := ⟨445377372233371453783735363, 445377372233371462229661385, 24150019, 4096, [], 445534796458330457090149622, 445534796458330465539061501⟩
def PrimData46.s33 : Seg := ⟨445534796458330457090149622, 445534796458330465539061501, 24158211, 4096, [], 445690655790639178310216683, 445690655790639186762084531⟩
def PrimData46.s34 : Seg := ⟨445690655790639178310216683, 445690655790639186762084531, 24166403, 4096, [], 445836169196913363735728953, 445836169196913372190355696⟩

def PrimData46.segs : List Seg := [PrimData46.s0, PrimData46.s1, PrimData46.s2, PrimData46.s3, PrimData46.s4, PrimData46.s5, PrimData46.s6, PrimData46.s7, PrimData46.s8, PrimData46.s9, PrimData46.s10, PrimData46.s11, PrimData46.s12, PrimData46.s13, PrimData46.s14, PrimData46.s15, PrimData46.s16, PrimData46.s17, PrimData46.s18, PrimData46.s19, PrimData46.s20, PrimData46.s21, PrimData46.s22, PrimData46.s23, PrimData46.s24, PrimData46.s25, PrimData46.s26, PrimData46.s27, PrimData46.s28, PrimData46.s29, PrimData46.s30, PrimData46.s31, PrimData46.s32, PrimData46.s33, PrimData46.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked46_s0 : Seg.bok PrimData46.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s0

theorem checked46_s1 : Seg.bok PrimData46.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s1

theorem checked46_s2 : Seg.bok PrimData46.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s2

theorem checked46_s3 : Seg.bok PrimData46.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s3

theorem checked46_s4 : Seg.bok PrimData46.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s4

theorem checked46_s5 : Seg.bok PrimData46.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s5

theorem checked46_s6 : Seg.bok PrimData46.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s6

theorem checked46_s7 : Seg.bok PrimData46.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s7

theorem checked46_s8 : Seg.bok PrimData46.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s8

theorem checked46_s9 : Seg.bok PrimData46.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s9

theorem checked46_s10 : Seg.bok PrimData46.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s10

theorem checked46_s11 : Seg.bok PrimData46.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s11

theorem checked46_s12 : Seg.bok PrimData46.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s12

theorem checked46_s13 : Seg.bok PrimData46.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s13

theorem checked46_s14 : Seg.bok PrimData46.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s14

theorem checked46_s15 : Seg.bok PrimData46.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s15

theorem checked46_s16 : Seg.bok PrimData46.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s16

theorem checked46_s17 : Seg.bok PrimData46.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s17

theorem checked46_s18 : Seg.bok PrimData46.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s18

theorem checked46_s19 : Seg.bok PrimData46.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s19

theorem checked46_s20 : Seg.bok PrimData46.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s20

theorem checked46_s21 : Seg.bok PrimData46.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s21

theorem checked46_s22 : Seg.bok PrimData46.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s22

theorem checked46_s23 : Seg.bok PrimData46.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s23

theorem checked46_s24 : Seg.bok PrimData46.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s24

theorem checked46_s25 : Seg.bok PrimData46.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s25

theorem checked46_s26 : Seg.bok PrimData46.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s26

theorem checked46_s27 : Seg.bok PrimData46.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s27

theorem checked46_s28 : Seg.bok PrimData46.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s28

theorem checked46_s29 : Seg.bok PrimData46.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s29

theorem checked46_s30 : Seg.bok PrimData46.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s30

theorem checked46_s31 : Seg.bok PrimData46.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s31

theorem checked46_s32 : Seg.bok PrimData46.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s32

theorem checked46_s33 : Seg.bok PrimData46.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s33

theorem checked46_s34 : Seg.bok PrimData46.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46_s34

 theorem checked46 : ∀ s ∈ PrimData46.segs, (Seg.bok s) = true := by
  unfold PrimData46.segs
  exact List.forall_mem_cons.2 ⟨checked46_s0, List.forall_mem_cons.2 ⟨checked46_s1, List.forall_mem_cons.2 ⟨checked46_s2, List.forall_mem_cons.2 ⟨checked46_s3, List.forall_mem_cons.2 ⟨checked46_s4, List.forall_mem_cons.2 ⟨checked46_s5, List.forall_mem_cons.2 ⟨checked46_s6, List.forall_mem_cons.2 ⟨checked46_s7, List.forall_mem_cons.2 ⟨checked46_s8, List.forall_mem_cons.2 ⟨checked46_s9, List.forall_mem_cons.2 ⟨checked46_s10, List.forall_mem_cons.2 ⟨checked46_s11, List.forall_mem_cons.2 ⟨checked46_s12, List.forall_mem_cons.2 ⟨checked46_s13, List.forall_mem_cons.2 ⟨checked46_s14, List.forall_mem_cons.2 ⟨checked46_s15, List.forall_mem_cons.2 ⟨checked46_s16, List.forall_mem_cons.2 ⟨checked46_s17, List.forall_mem_cons.2 ⟨checked46_s18, List.forall_mem_cons.2 ⟨checked46_s19, List.forall_mem_cons.2 ⟨checked46_s20, List.forall_mem_cons.2 ⟨checked46_s21, List.forall_mem_cons.2 ⟨checked46_s22, List.forall_mem_cons.2 ⟨checked46_s23, List.forall_mem_cons.2 ⟨checked46_s24, List.forall_mem_cons.2 ⟨checked46_s25, List.forall_mem_cons.2 ⟨checked46_s26, List.forall_mem_cons.2 ⟨checked46_s27, List.forall_mem_cons.2 ⟨checked46_s28, List.forall_mem_cons.2 ⟨checked46_s29, List.forall_mem_cons.2 ⟨checked46_s30, List.forall_mem_cons.2 ⟨checked46_s31, List.forall_mem_cons.2 ⟨checked46_s32, List.forall_mem_cons.2 ⟨checked46_s33, List.forall_mem_singleton.2 checked46_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked46
