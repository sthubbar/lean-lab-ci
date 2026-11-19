/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_34.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/19034817-32c8-4f9e-a7d5-bdbd248c2c46
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData34.s0 : Seg := ⟨377081245734728501937619077, 377081245734728509088378880, 20447235, 4096, [], 377237128976175196727922649, 377237128976175203881639109⟩
def PrimData34.s1 : Seg := ⟨377237128976175196727922649, 377237128976175203881639109, 20455427, 4096, [], 377387115793859090126135428, 377387115793859097282696338⟩
def PrimData34.s2 : Seg := ⟨377387115793859090126135428, 377387115793859097282696338, 20463619, 4096, [], 377540211580479999022262346, 377540211580480006181727959⟩
def PrimData34.s3 : Seg := ⟨377540211580479999022262346, 377540211580480006181727959, 20471811, 4096, [], 377690826608993126136276177, 377690826608993133298598871⟩
def PrimData34.s4 : Seg := ⟨377690826608993126136276177, 377690826608993133298598871, 20480003, 4096, [], 377832128630072276328346758, 377832128630072283493349634⟩
def PrimData34.s5 : Seg := ⟨377832128630072276328346758, 377832128630072283493349634, 20488195, 4096, [], 377988962043012587404226941, 377988962043012594572204760⟩
def PrimData34.s6 : Seg := ⟨377988962043012587404226941, 377988962043012594572204760, 20496387, 4096, [], 378143004099857511078890222, 378143004099857518249789792⟩
def PrimData34.s7 : Seg := ⟨378143004099857511078890222, 378143004099857518249789792, 20504579, 4096, [], 378293012289654676830616951, 378293012289654684004361225⟩
def PrimData34.s8 : Seg := ⟨378293012289654676830616951, 378293012289654684004361225, 20512771, 4096, [], 378452341577749648650849217, 378452341577749655827615836⟩
def PrimData34.s9 : Seg := ⟨378452341577749648650849217, 378452341577749655827615836, 20520963, 4096, [], 378602046299278740591610499, 378602046299278747771215316⟩
def PrimData34.s10 : Seg := ⟨378602046299278740591610499, 378602046299278747771215316, 20529155, 4096, [], 378747406248015144671239135, 378747406248015151853600518⟩
def PrimData34.s11 : Seg := ⟨378747406248015144671239135, 378747406248015151853600518, 20537347, 4096, [], 378898049894955736466394942, 378898049894955743651613475⟩
def PrimData34.s12 : Seg := ⟨378898049894955736466394942, 378898049894955743651613475, 20545539, 4096, [], 379049007731127760707911216, 379049007731127767895992530⟩
def PrimData34.s13 : Seg := ⟨379049007731127760707911216, 379049007731127767895992530, 20553731, 4096, [], 379199037259598975185070083, 379199037259598982375997171⟩
def PrimData34.s14 : Seg := ⟨379199037259598975185070083, 379199037259598982375997171, 20561923, 4096, [], 379352797857803785764282369, 379352797857803792958125024⟩
def PrimData34.s15 : Seg := ⟨379352797857803785764282369, 379352797857803792958125024, 20570115, 4096, [], 379507183323382634894375536, 379507183323382642091145707⟩
def PrimData34.s16 : Seg := ⟨379507183323382634894375536, 379507183323382642091145707, 20578307, 4096, [], 379655359660414989174237101, 379655359660414996373816514⟩
def PrimData34.s17 : Seg := ⟨379655359660414989174237101, 379655359660414996373816514, 20586499, 4096, [], 379815344160782412253444436, 379815344160782419456057779⟩
def PrimData34.s18 : Seg := ⟨379815344160782412253444436, 379815344160782419456057779, 20594691, 4096, [], 379962284822160785270495271, 379962284822160792475895494⟩
def PrimData34.s19 : Seg := ⟨379962284822160785270495271, 379962284822160792475895494, 20602883, 4096, [], 380107986361356373044346007, 380107986361356380252509816⟩
def PrimData34.s20 : Seg := ⟨380107986361356373044346007, 380107986361356380252509816, 20611075, 4096, [], 380258351340732407374158755, 380258351340732414585173314⟩
def PrimData34.s21 : Seg := ⟨380258351340732407374158755, 380258351340732414585173314, 20619267, 4096, [], 380416176248955693398038693, 380416176248955700612046467⟩
def PrimData34.s22 : Seg := ⟨380416176248955693398038693, 380416176248955700612046467, 20627459, 4096, [], 380565305582705567047415425, 380565305582705574264251438⟩
def PrimData34.s23 : Seg := ⟨380565305582705567047415425, 380565305582705574264251438, 20635651, 4096, [], 380713817062495814857700188, 380713817062495822077352202⟩
def PrimData34.s24 : Seg := ⟨380713817062495814857700188, 380713817062495822077352202, 20643843, 4096, [], 380867614109726793725574739, 380867614109726800948142945⟩
def PrimData34.s25 : Seg := ⟨380867614109726793725574739, 380867614109726800948142945, 20652035, 4096, [], 381016132621880687697173357, 381016132621880694922559449⟩
def PrimData34.s26 : Seg := ⟨381016132621880687697173357, 381016132621880694922559449, 20660227, 4096, [], 381161236768113147882958415, 381161236768113155111097111⟩
def PrimData34.s27 : Seg := ⟨381161236768113147882958415, 381161236768113155111097111, 20668419, 4096, [], 381320326825476459393587998, 381320326825476466624744384⟩
def PrimData34.s28 : Seg := ⟨381320326825476459393587998, 381320326825476466624744384, 20676611, 4096, [], 381480042091904836818507906, 381480042091904844052694639⟩
def PrimData34.s29 : Seg := ⟨381480042091904836818507906, 381480042091904844052694639, 20684803, 4096, [], 381632303371696448841794762, 381632303371696456078869445⟩
def PrimData34.s30 : Seg := ⟨381632303371696448841794762, 381632303371696456078869445, 20692995, 4096, [], 381785189755802820223554041, 381785189755802827463528570⟩
def PrimData34.s31 : Seg := ⟨381785189755802820223554041, 381785189755802827463528570, 20701187, 4096, [], 381939633433566882029167996, 381939633433566889272070932⟩
def PrimData34.s32 : Seg := ⟨381939633433566882029167996, 381939633433566889272070932, 20709379, 4096, [], 382095323792505153716333226, 382095323792505160962188533⟩
def PrimData34.s33 : Seg := ⟨382095323792505153716333226, 382095323792505160962188533, 20717571, 4096, [], 382245734830431213778164737, 382245734830431221026872521⟩
def PrimData34.s34 : Seg := ⟨382245734830431213778164737, 382245734830431221026872521, 20725763, 4096, [], 382394906263731372932853127, 382394906263731380184389576⟩

def PrimData34.segs : List Seg := [PrimData34.s0, PrimData34.s1, PrimData34.s2, PrimData34.s3, PrimData34.s4, PrimData34.s5, PrimData34.s6, PrimData34.s7, PrimData34.s8, PrimData34.s9, PrimData34.s10, PrimData34.s11, PrimData34.s12, PrimData34.s13, PrimData34.s14, PrimData34.s15, PrimData34.s16, PrimData34.s17, PrimData34.s18, PrimData34.s19, PrimData34.s20, PrimData34.s21, PrimData34.s22, PrimData34.s23, PrimData34.s24, PrimData34.s25, PrimData34.s26, PrimData34.s27, PrimData34.s28, PrimData34.s29, PrimData34.s30, PrimData34.s31, PrimData34.s32, PrimData34.s33, PrimData34.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked34_s0 : Seg.bok PrimData34.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s0

theorem checked34_s1 : Seg.bok PrimData34.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s1

theorem checked34_s2 : Seg.bok PrimData34.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s2

theorem checked34_s3 : Seg.bok PrimData34.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s3

theorem checked34_s4 : Seg.bok PrimData34.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s4

theorem checked34_s5 : Seg.bok PrimData34.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s5

theorem checked34_s6 : Seg.bok PrimData34.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s6

theorem checked34_s7 : Seg.bok PrimData34.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s7

theorem checked34_s8 : Seg.bok PrimData34.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s8

theorem checked34_s9 : Seg.bok PrimData34.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s9

theorem checked34_s10 : Seg.bok PrimData34.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s10

theorem checked34_s11 : Seg.bok PrimData34.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s11

theorem checked34_s12 : Seg.bok PrimData34.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s12

theorem checked34_s13 : Seg.bok PrimData34.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s13

theorem checked34_s14 : Seg.bok PrimData34.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s14

theorem checked34_s15 : Seg.bok PrimData34.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s15

theorem checked34_s16 : Seg.bok PrimData34.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s16

theorem checked34_s17 : Seg.bok PrimData34.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s17

theorem checked34_s18 : Seg.bok PrimData34.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s18

theorem checked34_s19 : Seg.bok PrimData34.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s19

theorem checked34_s20 : Seg.bok PrimData34.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s20

theorem checked34_s21 : Seg.bok PrimData34.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s21

theorem checked34_s22 : Seg.bok PrimData34.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s22

theorem checked34_s23 : Seg.bok PrimData34.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s23

theorem checked34_s24 : Seg.bok PrimData34.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s24

theorem checked34_s25 : Seg.bok PrimData34.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s25

theorem checked34_s26 : Seg.bok PrimData34.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s26

theorem checked34_s27 : Seg.bok PrimData34.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s27

theorem checked34_s28 : Seg.bok PrimData34.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s28

theorem checked34_s29 : Seg.bok PrimData34.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s29

theorem checked34_s30 : Seg.bok PrimData34.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s30

theorem checked34_s31 : Seg.bok PrimData34.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s31

theorem checked34_s32 : Seg.bok PrimData34.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s32

theorem checked34_s33 : Seg.bok PrimData34.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s33

theorem checked34_s34 : Seg.bok PrimData34.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34_s34

 theorem checked34 : ∀ s ∈ PrimData34.segs, (Seg.bok s) = true := by
  unfold PrimData34.segs
  exact List.forall_mem_cons.2 ⟨checked34_s0, List.forall_mem_cons.2 ⟨checked34_s1, List.forall_mem_cons.2 ⟨checked34_s2, List.forall_mem_cons.2 ⟨checked34_s3, List.forall_mem_cons.2 ⟨checked34_s4, List.forall_mem_cons.2 ⟨checked34_s5, List.forall_mem_cons.2 ⟨checked34_s6, List.forall_mem_cons.2 ⟨checked34_s7, List.forall_mem_cons.2 ⟨checked34_s8, List.forall_mem_cons.2 ⟨checked34_s9, List.forall_mem_cons.2 ⟨checked34_s10, List.forall_mem_cons.2 ⟨checked34_s11, List.forall_mem_cons.2 ⟨checked34_s12, List.forall_mem_cons.2 ⟨checked34_s13, List.forall_mem_cons.2 ⟨checked34_s14, List.forall_mem_cons.2 ⟨checked34_s15, List.forall_mem_cons.2 ⟨checked34_s16, List.forall_mem_cons.2 ⟨checked34_s17, List.forall_mem_cons.2 ⟨checked34_s18, List.forall_mem_cons.2 ⟨checked34_s19, List.forall_mem_cons.2 ⟨checked34_s20, List.forall_mem_cons.2 ⟨checked34_s21, List.forall_mem_cons.2 ⟨checked34_s22, List.forall_mem_cons.2 ⟨checked34_s23, List.forall_mem_cons.2 ⟨checked34_s24, List.forall_mem_cons.2 ⟨checked34_s25, List.forall_mem_cons.2 ⟨checked34_s26, List.forall_mem_cons.2 ⟨checked34_s27, List.forall_mem_cons.2 ⟨checked34_s28, List.forall_mem_cons.2 ⟨checked34_s29, List.forall_mem_cons.2 ⟨checked34_s30, List.forall_mem_cons.2 ⟨checked34_s31, List.forall_mem_cons.2 ⟨checked34_s32, List.forall_mem_cons.2 ⟨checked34_s33, List.forall_mem_singleton.2 checked34_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked34
