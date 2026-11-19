/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_59.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/432d6d5f-8def-47db-bc6c-114cc85372ac
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData59.s0 : Seg := ⟨509314388563109653985733884, 509314388563109663644073328, 27615235, 4096, [], 509464520379360058712213599, 509464520379360068373399477⟩
def PrimData59.s1 : Seg := ⟨509464520379360058712213599, 509464520379360068373399477, 27623427, 4096, [], 509618763759529101117918212, 509618763759529110782029028⟩
def PrimData59.s2 : Seg := ⟨509618763759529101117918212, 509618763759529110782029028, 27631619, 4096, [], 509769532905911025368542308, 509769532905911035035512934⟩
def PrimData59.s3 : Seg := ⟨509769532905911025368542308, 509769532905911035035512934, 27639811, 4096, [], 509916511643596639491156460, 509916511643596649160914724⟩
def PrimData59.s4 : Seg := ⟨509916511643596639491156460, 509916511643596649160914724, 27648003, 4096, [], 510066337752969901116279411, 510066337752969910788879023⟩
def PrimData59.s5 : Seg := ⟨510066337752969901116279411, 510066337752969910788879023, 27656195, 4096, [], 510223436650688468361434533, 510223436650688478037014748⟩
def PrimData59.s6 : Seg := ⟨510223436650688468361434533, 510223436650688478037014748, 27664387, 4096, [], 510367894263036244325379987, 510367894263036254003699930⟩
def PrimData59.s7 : Seg := ⟨510367894263036244325379987, 510367894263036254003699930, 27672579, 4096, [], 510516779864564859704790878, 510516779864564869385934027⟩
def PrimData59.s8 : Seg := ⟨510516779864564859704790878, 510516779864564869385934027, 27680771, 4096, [], 510663771335986065305825101, 510663771335986074989756007⟩
def PrimData59.s9 : Seg := ⟨510663771335986065305825101, 510663771335986074989756007, 27688963, 4096, [], 510811713717502937678809180, 510811713717502947365545469⟩
def PrimData59.s10 : Seg := ⟨510811713717502937678809180, 510811713717502947365545469, 27697155, 4096, [], 510968826169235324103529561, 510968826169235333793246431⟩
def PrimData59.s11 : Seg := ⟨510968826169235324103529561, 510968826169235333793246431, 27705347, 4096, [], 511119934921595720927257471, 511119934921595730619841009⟩
def PrimData59.s12 : Seg := ⟨511119934921595720927257471, 511119934921595730619841009, 27713539, 4096, [], 511262510712061543695658921, 511262510712061553390945974⟩
def PrimData59.s13 : Seg := ⟨511262510712061543695658921, 511262510712061553390945974, 27721731, 4096, [], 511417418293540777322364410, 511417418293540787020588879⟩
def PrimData59.s14 : Seg := ⟨511417418293540777322364410, 511417418293540787020588879, 27729923, 4096, [], 511587819573368158172175800, 511587819573368167873631050⟩
def PrimData59.s15 : Seg := ⟨511587819573368158172175800, 511587819573368167873631050, 27738115, 4096, [], 511741784065850722144625691, 511741784065850731848999793⟩
def PrimData59.s16 : Seg := ⟨511741784065850722144625691, 511741784065850731848999793, 27746307, 4096, [], 511895751221894515795302561, 511895751221894525502597221⟩
def PrimData59.s17 : Seg := ⟨511895751221894515795302561, 511895751221894525502597221, 27754499, 4096, [], 512036126251758650110716998, 512036126251758659820673048⟩
def PrimData59.s18 : Seg := ⟨512036126251758650110716998, 512036126251758659820673048, 27762691, 4096, [], 512188201700018546969676175, 512188201700018556682516470⟩
def PrimData59.s19 : Seg := ⟨512188201700018546969676175, 512188201700018556682516470, 27770883, 4096, [], 512336169616488550188856339, 512336169616488559904501973⟩
def PrimData59.s20 : Seg := ⟨512336169616488550188856339, 512336169616488559904501973, 27779075, 4096, [], 512486353233083671859739406, 512486353233083681578232690⟩
def PrimData59.s21 : Seg := ⟨512486353233083671859739406, 512486353233083681578232690, 27787267, 4096, [], 512632112927602571702742818, 512632112927602581423999909⟩
def PrimData59.s22 : Seg := ⟨512632112927602571702742818, 512632112927602581423999909, 27795459, 4096, [], 512785147426246391600969596, 512785147426246401325129209⟩
def PrimData59.s23 : Seg := ⟨512785147426246391600969596, 512785147426246401325129209, 27803651, 4096, [], 512941030295680565278315276, 512941030295680575005430915⟩
def PrimData59.s24 : Seg := ⟨512941030295680565278315276, 512941030295680575005430915, 27811843, 4096, [], 513089643342575387184439351, 513089643342575396914373207⟩
def PrimData59.s25 : Seg := ⟨513089643342575387184439351, 513089643342575396914373207, 27820035, 4096, [], 513233199658653913040692266, 513233199658653922773347679⟩
def PrimData59.s26 : Seg := ⟨513233199658653913040692266, 513233199658653922773347679, 27828227, 4096, [], 513384031243590134516868671, 513384031243590144252383421⟩
def PrimData59.s27 : Seg := ⟨513384031243590134516868671, 513384031243590144252383421, 27836419, 4096, [], 513528224883450668585462059, 513528224883450678323711205⟩
def PrimData59.s28 : Seg := ⟨513528224883450668585462059, 513528224883450678323711205, 27844611, 4096, [], 513678429195329515806506992, 513678429195329525547604749⟩
def PrimData59.s29 : Seg := ⟨513678429195329515806506992, 513678429195329525547604749, 27852803, 4096, [], 513825157634459030150600658, 513825157634459039894480467⟩
def PrimData59.s30 : Seg := ⟨513825157634459030150600658, 513825157634459039894480467, 27860995, 4096, [], 513977896907972481257187284, 513977896907972491003962874⟩
def PrimData59.s31 : Seg := ⟨513977896907972481257187284, 513977896907972491003962874, 27869187, 4096, [], 514134117391034291595180963, 514134117391034301344918707⟩
def PrimData59.s32 : Seg := ⟨514134117391034291595180963, 514134117391034301344918707, 27877379, 4096, [], 514289708079045204550434905, 514289708079045214303123119⟩
def PrimData59.s33 : Seg := ⟨514289708079045204550434905, 514289708079045214303123119, 27885571, 4096, [], 514430437850545694184160548, 514430437850545703939516656⟩
def PrimData59.s34 : Seg := ⟨514430437850545694184160548, 514430437850545703939516656, 27893763, 4096, [], 514592991377577003739254072, 514592991377577013497693776⟩

def PrimData59.segs : List Seg := [PrimData59.s0, PrimData59.s1, PrimData59.s2, PrimData59.s3, PrimData59.s4, PrimData59.s5, PrimData59.s6, PrimData59.s7, PrimData59.s8, PrimData59.s9, PrimData59.s10, PrimData59.s11, PrimData59.s12, PrimData59.s13, PrimData59.s14, PrimData59.s15, PrimData59.s16, PrimData59.s17, PrimData59.s18, PrimData59.s19, PrimData59.s20, PrimData59.s21, PrimData59.s22, PrimData59.s23, PrimData59.s24, PrimData59.s25, PrimData59.s26, PrimData59.s27, PrimData59.s28, PrimData59.s29, PrimData59.s30, PrimData59.s31, PrimData59.s32, PrimData59.s33, PrimData59.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked59_s0 : Seg.bok PrimData59.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s0

theorem checked59_s1 : Seg.bok PrimData59.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s1

theorem checked59_s2 : Seg.bok PrimData59.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s2

theorem checked59_s3 : Seg.bok PrimData59.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s3

theorem checked59_s4 : Seg.bok PrimData59.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s4

theorem checked59_s5 : Seg.bok PrimData59.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s5

theorem checked59_s6 : Seg.bok PrimData59.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s6

theorem checked59_s7 : Seg.bok PrimData59.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s7

theorem checked59_s8 : Seg.bok PrimData59.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s8

theorem checked59_s9 : Seg.bok PrimData59.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s9

theorem checked59_s10 : Seg.bok PrimData59.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s10

theorem checked59_s11 : Seg.bok PrimData59.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s11

theorem checked59_s12 : Seg.bok PrimData59.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s12

theorem checked59_s13 : Seg.bok PrimData59.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s13

theorem checked59_s14 : Seg.bok PrimData59.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s14

theorem checked59_s15 : Seg.bok PrimData59.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s15

theorem checked59_s16 : Seg.bok PrimData59.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s16

theorem checked59_s17 : Seg.bok PrimData59.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s17

theorem checked59_s18 : Seg.bok PrimData59.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s18

theorem checked59_s19 : Seg.bok PrimData59.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s19

theorem checked59_s20 : Seg.bok PrimData59.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s20

theorem checked59_s21 : Seg.bok PrimData59.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s21

theorem checked59_s22 : Seg.bok PrimData59.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s22

theorem checked59_s23 : Seg.bok PrimData59.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s23

theorem checked59_s24 : Seg.bok PrimData59.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s24

theorem checked59_s25 : Seg.bok PrimData59.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s25

theorem checked59_s26 : Seg.bok PrimData59.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s26

theorem checked59_s27 : Seg.bok PrimData59.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s27

theorem checked59_s28 : Seg.bok PrimData59.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s28

theorem checked59_s29 : Seg.bok PrimData59.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s29

theorem checked59_s30 : Seg.bok PrimData59.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s30

theorem checked59_s31 : Seg.bok PrimData59.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s31

theorem checked59_s32 : Seg.bok PrimData59.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s32

theorem checked59_s33 : Seg.bok PrimData59.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s33

theorem checked59_s34 : Seg.bok PrimData59.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59_s34

 theorem checked59 : ∀ s ∈ PrimData59.segs, (Seg.bok s) = true := by
  unfold PrimData59.segs
  exact List.forall_mem_cons.2 ⟨checked59_s0, List.forall_mem_cons.2 ⟨checked59_s1, List.forall_mem_cons.2 ⟨checked59_s2, List.forall_mem_cons.2 ⟨checked59_s3, List.forall_mem_cons.2 ⟨checked59_s4, List.forall_mem_cons.2 ⟨checked59_s5, List.forall_mem_cons.2 ⟨checked59_s6, List.forall_mem_cons.2 ⟨checked59_s7, List.forall_mem_cons.2 ⟨checked59_s8, List.forall_mem_cons.2 ⟨checked59_s9, List.forall_mem_cons.2 ⟨checked59_s10, List.forall_mem_cons.2 ⟨checked59_s11, List.forall_mem_cons.2 ⟨checked59_s12, List.forall_mem_cons.2 ⟨checked59_s13, List.forall_mem_cons.2 ⟨checked59_s14, List.forall_mem_cons.2 ⟨checked59_s15, List.forall_mem_cons.2 ⟨checked59_s16, List.forall_mem_cons.2 ⟨checked59_s17, List.forall_mem_cons.2 ⟨checked59_s18, List.forall_mem_cons.2 ⟨checked59_s19, List.forall_mem_cons.2 ⟨checked59_s20, List.forall_mem_cons.2 ⟨checked59_s21, List.forall_mem_cons.2 ⟨checked59_s22, List.forall_mem_cons.2 ⟨checked59_s23, List.forall_mem_cons.2 ⟨checked59_s24, List.forall_mem_cons.2 ⟨checked59_s25, List.forall_mem_cons.2 ⟨checked59_s26, List.forall_mem_cons.2 ⟨checked59_s27, List.forall_mem_cons.2 ⟨checked59_s28, List.forall_mem_cons.2 ⟨checked59_s29, List.forall_mem_cons.2 ⟨checked59_s30, List.forall_mem_cons.2 ⟨checked59_s31, List.forall_mem_cons.2 ⟨checked59_s32, List.forall_mem_cons.2 ⟨checked59_s33, List.forall_mem_singleton.2 checked59_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked59
