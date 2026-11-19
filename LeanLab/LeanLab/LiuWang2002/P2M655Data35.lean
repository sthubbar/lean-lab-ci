/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_35.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/625ce2c4-2c1c-4a38-a810-fb17e13b5b87
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData35.s0 : Seg := ⟨382394906263731372932853127, 382394906263731380184389576, 20733955, 4096, [], 382545945882756960293647707, 382545945882756967548048042⟩
def PrimData35.s1 : Seg := ⟨382545945882756960293647707, 382545945882756967548048042, 20742147, 4096, [], 382698232264181989912778439, 382698232264181997170066718⟩
def PrimData35.s2 : Seg := ⟨382698232264181989912778439, 382698232264181997170066718, 20750339, 4096, [], 382847414185948586002010879, 382847414185948593262127578⟩
def PrimData35.s3 : Seg := ⟨382847414185948586002010879, 382847414185948593262127578, 20758531, 4096, [], 383000018451137556277309163, 383000018451137563540319910⟩
def PrimData35.s4 : Seg := ⟨383000018451137556277309163, 383000018451137563540319910, 20766723, 4096, [], 383147031723636495868503655, 383147031723636503134301762⟩
def PrimData35.s5 : Seg := ⟨383147031723636495868503655, 383147031723636503134301762, 20774915, 4096, [], 383298088983242163323912799, 383298088983242170592576727⟩
def PrimData35.s6 : Seg := ⟨383298088983242163323912799, 383298088983242170592576727, 20783107, 4096, [], 383452258159544408653002385, 383452258159544415924590212⟩
def PrimData35.s7 : Seg := ⟨383452258159544408653002385, 383452258159544415924590212, 20791299, 4096, [], 383602390114740531205271838, 383602390114740538479705597⟩
def PrimData35.s8 : Seg := ⟨383602390114740531205271838, 383602390114740538479705597, 20799491, 4096, [], 383751903865690525568658096, 383751903865690532845926459⟩
def PrimData35.s9 : Seg := ⟨383751903865690525568658096, 383751903865690532845926459, 20807683, 4096, [], 383900177732182457128920328, 383900177732182464409000335⟩
def PrimData35.s10 : Seg := ⟨383900177732182457128920328, 383900177732182464409000335, 20815875, 4096, [], 384043792221824110384718864, 384043792221824117667521598⟩
def PrimData35.s11 : Seg := ⟨384043792221824110384718864, 384043792221824117667521598, 20824067, 4096, [], 384190207762405163549910036, 384190207762405170835488290⟩
def PrimData35.s12 : Seg := ⟨384190207762405163549910036, 384190207762405170835488290, 20832259, 4096, [], 384344087645809752214270859, 384344087645809759502766984⟩
def PrimData35.s13 : Seg := ⟨384344087645809752214270859, 384344087645809759502766984, 20840451, 4096, [], 384501390698662008087848473, 384501390698662015379326921⟩
def PrimData35.s14 : Seg := ⟨384501390698662008087848473, 384501390698662015379326921, 20848643, 4096, [], 384647816494169306092841162, 384647816494169313387095378⟩
def PrimData35.s15 : Seg := ⟨384647816494169306092841162, 384647816494169313387095378, 20856835, 4096, [], 384804505138842302695737936, 384804505138842309992963343⟩
def PrimData35.s16 : Seg := ⟨384804505138842302695737936, 384804505138842309992963343, 20865027, 4096, [], 384954357669510027548077618, 384954357669510034848143859⟩
def PrimData35.s17 : Seg := ⟨384954357669510027548077618, 384954357669510034848143859, 20873219, 4096, [], 385110120889883175766580648, 385110120889883183069600300⟩
def PrimData35.s18 : Seg := ⟨385110120889883175766580648, 385110120889883183069600300, 20881411, 4096, [], 385262467707357009370547890, 385262467707357016676456119⟩
def PrimData35.s19 : Seg := ⟨385262467707357009370547890, 385262467707357016676456119, 20889603, 4096, [], 385409532447114260080776881, 385409532447114267389472830⟩
def PrimData35.s20 : Seg := ⟨385409532447114260080776881, 385409532447114267389472830, 20897795, 4096, [], 385559087989565990703848505, 385559087989565998015379802⟩
def PrimData35.s21 : Seg := ⟨385559087989565990703848505, 385559087989565998015379802, 20905987, 4096, [], 385707092369985413010705346, 385707092369985420325041369⟩
def PrimData35.s22 : Seg := ⟨385707092369985413010705346, 385707092369985420325041369, 20914179, 4096, [], 385859453350155803023376073, 385859453350155810340601122⟩
def PrimData35.s23 : Seg := ⟨385859453350155803023376073, 385859453350155810340601122, 20922371, 4096, [], 386011195990828336932058095, 386011195990828344252159096⟩
def PrimData35.s24 : Seg := ⟨386011195990828336932058095, 386011195990828344252159096, 20930563, 4096, [], 386160454459419667130197022, 386160454459419674453126511⟩
def PrimData35.s25 : Seg := ⟨386160454459419667130197022, 386160454459419674453126511, 20938755, 4096, [], 386305362989020182670534949, 386305362989020189996211332⟩
def PrimData35.s26 : Seg := ⟨386305362989020182670534949, 386305362989020189996211332, 20946947, 4096, [], 386459914911008102230001046, 386459914911008109558607385⟩
def PrimData35.s27 : Seg := ⟨386459914911008102230001046, 386459914911008109558607385, 20955139, 4096, [], 386609183771847828069255715, 386609183771847835400690515⟩
def PrimData35.s28 : Seg := ⟨386609183771847828069255715, 386609183771847835400690515, 20963331, 4096, [], 386753169346087908578140621, 386753169346087915912303672⟩
def PrimData35.s29 : Seg := ⟨386753169346087908578140621, 386753169346087915912303672, 20971523, 4096, [], 386909908955265736886731530, 386909908955265744223865466⟩
def PrimData35.s30 : Seg := ⟨386909908955265736886731530, 386909908955265744223865466, 20979715, 4096, [], 387066030159400340433334047, 387066030159400347773427659⟩
def PrimData35.s31 : Seg := ⟨387066030159400340433334047, 387066030159400347773427659, 20987907, 4096, [], 387219666976383377109145688, 387219666976383384452151225⟩
def PrimData35.s32 : Seg := ⟨387219666976383377109145688, 387219666976383384452151225, 20996099, 4096, [], 387367087121160997118154050, 387367087121161004463953630⟩
def PrimData35.s33 : Seg := ⟨387367087121160997118154050, 387367087121161004463953630, 21004291, 4096, [], 387525707333708609928844986, 387525707333708617277651364⟩
def PrimData35.s34 : Seg := ⟨387525707333708609928844986, 387525707333708617277651364, 21012483, 4096, [], 387681220992923415775547678, 387681220992923423127302246⟩

def PrimData35.segs : List Seg := [PrimData35.s0, PrimData35.s1, PrimData35.s2, PrimData35.s3, PrimData35.s4, PrimData35.s5, PrimData35.s6, PrimData35.s7, PrimData35.s8, PrimData35.s9, PrimData35.s10, PrimData35.s11, PrimData35.s12, PrimData35.s13, PrimData35.s14, PrimData35.s15, PrimData35.s16, PrimData35.s17, PrimData35.s18, PrimData35.s19, PrimData35.s20, PrimData35.s21, PrimData35.s22, PrimData35.s23, PrimData35.s24, PrimData35.s25, PrimData35.s26, PrimData35.s27, PrimData35.s28, PrimData35.s29, PrimData35.s30, PrimData35.s31, PrimData35.s32, PrimData35.s33, PrimData35.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked35_s0 : Seg.bok PrimData35.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s0

theorem checked35_s1 : Seg.bok PrimData35.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s1

theorem checked35_s2 : Seg.bok PrimData35.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s2

theorem checked35_s3 : Seg.bok PrimData35.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s3

theorem checked35_s4 : Seg.bok PrimData35.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s4

theorem checked35_s5 : Seg.bok PrimData35.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s5

theorem checked35_s6 : Seg.bok PrimData35.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s6

theorem checked35_s7 : Seg.bok PrimData35.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s7

theorem checked35_s8 : Seg.bok PrimData35.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s8

theorem checked35_s9 : Seg.bok PrimData35.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s9

theorem checked35_s10 : Seg.bok PrimData35.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s10

theorem checked35_s11 : Seg.bok PrimData35.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s11

theorem checked35_s12 : Seg.bok PrimData35.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s12

theorem checked35_s13 : Seg.bok PrimData35.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s13

theorem checked35_s14 : Seg.bok PrimData35.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s14

theorem checked35_s15 : Seg.bok PrimData35.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s15

theorem checked35_s16 : Seg.bok PrimData35.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s16

theorem checked35_s17 : Seg.bok PrimData35.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s17

theorem checked35_s18 : Seg.bok PrimData35.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s18

theorem checked35_s19 : Seg.bok PrimData35.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s19

theorem checked35_s20 : Seg.bok PrimData35.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s20

theorem checked35_s21 : Seg.bok PrimData35.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s21

theorem checked35_s22 : Seg.bok PrimData35.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s22

theorem checked35_s23 : Seg.bok PrimData35.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s23

theorem checked35_s24 : Seg.bok PrimData35.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s24

theorem checked35_s25 : Seg.bok PrimData35.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s25

theorem checked35_s26 : Seg.bok PrimData35.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s26

theorem checked35_s27 : Seg.bok PrimData35.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s27

theorem checked35_s28 : Seg.bok PrimData35.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s28

theorem checked35_s29 : Seg.bok PrimData35.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s29

theorem checked35_s30 : Seg.bok PrimData35.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s30

theorem checked35_s31 : Seg.bok PrimData35.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s31

theorem checked35_s32 : Seg.bok PrimData35.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s32

theorem checked35_s33 : Seg.bok PrimData35.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s33

theorem checked35_s34 : Seg.bok PrimData35.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35_s34

 theorem checked35 : ∀ s ∈ PrimData35.segs, (Seg.bok s) = true := by
  unfold PrimData35.segs
  exact List.forall_mem_cons.2 ⟨checked35_s0, List.forall_mem_cons.2 ⟨checked35_s1, List.forall_mem_cons.2 ⟨checked35_s2, List.forall_mem_cons.2 ⟨checked35_s3, List.forall_mem_cons.2 ⟨checked35_s4, List.forall_mem_cons.2 ⟨checked35_s5, List.forall_mem_cons.2 ⟨checked35_s6, List.forall_mem_cons.2 ⟨checked35_s7, List.forall_mem_cons.2 ⟨checked35_s8, List.forall_mem_cons.2 ⟨checked35_s9, List.forall_mem_cons.2 ⟨checked35_s10, List.forall_mem_cons.2 ⟨checked35_s11, List.forall_mem_cons.2 ⟨checked35_s12, List.forall_mem_cons.2 ⟨checked35_s13, List.forall_mem_cons.2 ⟨checked35_s14, List.forall_mem_cons.2 ⟨checked35_s15, List.forall_mem_cons.2 ⟨checked35_s16, List.forall_mem_cons.2 ⟨checked35_s17, List.forall_mem_cons.2 ⟨checked35_s18, List.forall_mem_cons.2 ⟨checked35_s19, List.forall_mem_cons.2 ⟨checked35_s20, List.forall_mem_cons.2 ⟨checked35_s21, List.forall_mem_cons.2 ⟨checked35_s22, List.forall_mem_cons.2 ⟨checked35_s23, List.forall_mem_cons.2 ⟨checked35_s24, List.forall_mem_cons.2 ⟨checked35_s25, List.forall_mem_cons.2 ⟨checked35_s26, List.forall_mem_cons.2 ⟨checked35_s27, List.forall_mem_cons.2 ⟨checked35_s28, List.forall_mem_cons.2 ⟨checked35_s29, List.forall_mem_cons.2 ⟨checked35_s30, List.forall_mem_cons.2 ⟨checked35_s31, List.forall_mem_cons.2 ⟨checked35_s32, List.forall_mem_cons.2 ⟨checked35_s33, List.forall_mem_singleton.2 checked35_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked35
