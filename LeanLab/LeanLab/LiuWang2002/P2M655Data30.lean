/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_30.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/b6ff5a2d-fb9a-4d56-9ef0-7a5348b74e15
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData30.s0 : Seg := ⟨355935122081115487807741748, 355935122081115494557499687, 19300355, 4096, [], 356093255962083279588576411, 356093255962083286341333329⟩
def PrimData30.s1 : Seg := ⟨356093255962083279588576411, 356093255962083286341333329, 19308547, 4096, [], 356247061355460408956457821, 356247061355460415712131827⟩
def PrimData30.s2 : Seg := ⟨356247061355460408956457821, 356247061355460415712131827, 19316739, 4096, [], 356399942258337986375794500, 356399942258337993134368341⟩
def PrimData30.s3 : Seg := ⟨356399942258337986375794500, 356399942258337993134368341, 19324931, 4096, [], 356553136458833546686958596, 356553136458833553448438350⟩
def PrimData30.s4 : Seg := ⟨356553136458833546686958596, 356553136458833553448438350, 19333123, 4096, [], 356700144728692334949365574, 356700144728692341713633637⟩
def PrimData30.s5 : Seg := ⟨356700144728692334949365574, 356700144728692341713633637, 19341315, 4096, [], 356846847180141252371066803, 356846847180141259138117585⟩
def PrimData30.s6 : Seg := ⟨356846847180141252371066803, 356846847180141259138117585, 19349507, 4096, [], 357004076538066344001018297, 357004076538066350771051299⟩
def PrimData30.s7 : Seg := ⟨357004076538066344001018297, 357004076538066350771051299, 19357699, 4096, [], 357156667167880655706242258, 357156667167880662479169286⟩
def PrimData30.s8 : Seg := ⟨357156667167880655706242258, 357156667167880662479169286, 19365891, 4096, [], 357305547389861596629475829, 357305547389861603405226410⟩
def PrimData30.s9 : Seg := ⟨357305547389861596629475829, 357305547389861603405226410, 19374083, 4096, [], 357456288558808207867438361, 357456288558808214646048694⟩
def PrimData30.s10 : Seg := ⟨357456288558808207867438361, 357456288558808214646048694, 19382275, 4096, [], 357620034102464641939588806, 357620034102464648721305091⟩
def PrimData30.s11 : Seg := ⟨357620034102464641939588806, 357620034102464648721305091, 19390467, 4096, [], 357763353727597670782085184, 357763353727597677566519326⟩
def PrimData30.s12 : Seg := ⟨357763353727597670782085184, 357763353727597677566519326, 19398659, 4096, [], 357912868056943336512165252, 357912868056943343299434384⟩
def PrimData30.s13 : Seg := ⟨357912868056943336512165252, 357912868056943343299434384, 19406851, 4096, [], 358072911180992021786936931, 358072911180992028577241100⟩
def PrimData30.s14 : Seg := ⟨358072911180992021786936931, 358072911180992028577241100, 19415043, 4096, [], 358223980874575157665111848, 358223980874575164458280252⟩
def PrimData30.s15 : Seg := ⟨358223980874575157665111848, 358223980874575164458280252, 19423235, 4096, [], 358372887291244013483689730, 358372887291244020279682221⟩
def PrimData30.s16 : Seg := ⟨358372887291244013483689730, 358372887291244020279682221, 19431427, 4096, [], 358529227533982592274322861, 358529227533982599073279682⟩
def PrimData30.s17 : Seg := ⟨358529227533982592274322861, 358529227533982599073279682, 19439619, 4096, [], 358684333269982908557557922, 358684333269982915359455317⟩
def PrimData30.s18 : Seg := ⟨358684333269982908557557922, 358684333269982915359455317, 19447811, 4096, [], 358833250979006077186947730, 358833250979006083991668073⟩
def PrimData30.s19 : Seg := ⟨358833250979006077186947730, 358833250979006083991668073, 19456003, 4096, [], 358985577974540576391945367, 358985577974540583199554458⟩
def PrimData30.s20 : Seg := ⟨358985577974540576391945367, 358985577974540583199554458, 19464195, 4096, [], 359129858907489380813753379, 359129858907489387624097784⟩
def PrimData30.s21 : Seg := ⟨359129858907489380813753379, 359129858907489387624097784, 19472387, 4096, [], 359284670611877652176299076, 359284670611877658989578898⟩
def PrimData30.s22 : Seg := ⟨359284670611877652176299076, 359284670611877658989578898, 19480579, 4096, [], 359428649053359941949642264, 359428649053359948765651450⟩
def PrimData30.s23 : Seg := ⟨359428649053359941949642264, 359428649053359948765651450, 19488771, 4096, [], 359574488994931552865524066, 359574488994931559684297765⟩
def PrimData30.s24 : Seg := ⟨359574488994931552865524066, 359574488994931559684297765, 19496963, 4096, [], 359730860546557481187292376, 359730860546557488009031416⟩
def PrimData30.s25 : Seg := ⟨359730860546557481187292376, 359730860546557488009031416, 19505155, 4096, [], 359877636747758234854518521, 359877636747758241679040481⟩
def PrimData30.s26 : Seg := ⟨359877636747758234854518521, 359877636747758241679040481, 19513347, 4096, [], 360031229119668786582022861, 360031229119668793409456432⟩
def PrimData30.s27 : Seg := ⟨360031229119668786582022861, 360031229119668793409456432, 19521539, 4096, [], 360177702997917096491462994, 360177702997917103321674097⟩
def PrimData30.s28 : Seg := ⟨360177702997917096491462994, 360177702997917103321674097, 19529731, 4096, [], 360327277267478620313434446, 360327277267478627146482289⟩
def PrimData30.s29 : Seg := ⟨360327277267478620313434446, 360327277267478627146482289, 19537923, 4096, [], 360476545570553783475892165, 360476545570553790311770128⟩
def PrimData30.s30 : Seg := ⟨360476545570553783475892165, 360476545570553790311770128, 19546115, 4096, [], 360624269180072609580067796, 360624269180072616418747339⟩
def PrimData30.s31 : Seg := ⟨360624269180072609580067796, 360624269180072616418747339, 19554307, 4096, [], 360769828564465792874004641, 360769828564465799715444370⟩
def PrimData30.s32 : Seg := ⟨360769828564465792874004641, 360769828564465799715444370, 19562499, 4096, [], 360920346899866044314353874, 360920346899866051158648617⟩
def PrimData30.s33 : Seg := ⟨360920346899866044314353874, 360920346899866051158648617, 19570691, 4096, [], 361065294060076972416629238, 361065294060076979263673860⟩
def PrimData30.s34 : Seg := ⟨361065294060076972416629238, 361065294060076979263673860, 19578883, 4096, [], 361210244834022073443681811, 361210244834022080293475875⟩

def PrimData30.segs : List Seg := [PrimData30.s0, PrimData30.s1, PrimData30.s2, PrimData30.s3, PrimData30.s4, PrimData30.s5, PrimData30.s6, PrimData30.s7, PrimData30.s8, PrimData30.s9, PrimData30.s10, PrimData30.s11, PrimData30.s12, PrimData30.s13, PrimData30.s14, PrimData30.s15, PrimData30.s16, PrimData30.s17, PrimData30.s18, PrimData30.s19, PrimData30.s20, PrimData30.s21, PrimData30.s22, PrimData30.s23, PrimData30.s24, PrimData30.s25, PrimData30.s26, PrimData30.s27, PrimData30.s28, PrimData30.s29, PrimData30.s30, PrimData30.s31, PrimData30.s32, PrimData30.s33, PrimData30.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked30_s0 : Seg.bok PrimData30.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s0

theorem checked30_s1 : Seg.bok PrimData30.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s1

theorem checked30_s2 : Seg.bok PrimData30.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s2

theorem checked30_s3 : Seg.bok PrimData30.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s3

theorem checked30_s4 : Seg.bok PrimData30.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s4

theorem checked30_s5 : Seg.bok PrimData30.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s5

theorem checked30_s6 : Seg.bok PrimData30.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s6

theorem checked30_s7 : Seg.bok PrimData30.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s7

theorem checked30_s8 : Seg.bok PrimData30.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s8

theorem checked30_s9 : Seg.bok PrimData30.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s9

theorem checked30_s10 : Seg.bok PrimData30.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s10

theorem checked30_s11 : Seg.bok PrimData30.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s11

theorem checked30_s12 : Seg.bok PrimData30.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s12

theorem checked30_s13 : Seg.bok PrimData30.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s13

theorem checked30_s14 : Seg.bok PrimData30.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s14

theorem checked30_s15 : Seg.bok PrimData30.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s15

theorem checked30_s16 : Seg.bok PrimData30.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s16

theorem checked30_s17 : Seg.bok PrimData30.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s17

theorem checked30_s18 : Seg.bok PrimData30.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s18

theorem checked30_s19 : Seg.bok PrimData30.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s19

theorem checked30_s20 : Seg.bok PrimData30.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s20

theorem checked30_s21 : Seg.bok PrimData30.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s21

theorem checked30_s22 : Seg.bok PrimData30.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s22

theorem checked30_s23 : Seg.bok PrimData30.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s23

theorem checked30_s24 : Seg.bok PrimData30.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s24

theorem checked30_s25 : Seg.bok PrimData30.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s25

theorem checked30_s26 : Seg.bok PrimData30.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s26

theorem checked30_s27 : Seg.bok PrimData30.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s27

theorem checked30_s28 : Seg.bok PrimData30.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s28

theorem checked30_s29 : Seg.bok PrimData30.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s29

theorem checked30_s30 : Seg.bok PrimData30.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s30

theorem checked30_s31 : Seg.bok PrimData30.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s31

theorem checked30_s32 : Seg.bok PrimData30.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s32

theorem checked30_s33 : Seg.bok PrimData30.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s33

theorem checked30_s34 : Seg.bok PrimData30.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30_s34

 theorem checked30 : ∀ s ∈ PrimData30.segs, (Seg.bok s) = true := by
  unfold PrimData30.segs
  exact List.forall_mem_cons.2 ⟨checked30_s0, List.forall_mem_cons.2 ⟨checked30_s1, List.forall_mem_cons.2 ⟨checked30_s2, List.forall_mem_cons.2 ⟨checked30_s3, List.forall_mem_cons.2 ⟨checked30_s4, List.forall_mem_cons.2 ⟨checked30_s5, List.forall_mem_cons.2 ⟨checked30_s6, List.forall_mem_cons.2 ⟨checked30_s7, List.forall_mem_cons.2 ⟨checked30_s8, List.forall_mem_cons.2 ⟨checked30_s9, List.forall_mem_cons.2 ⟨checked30_s10, List.forall_mem_cons.2 ⟨checked30_s11, List.forall_mem_cons.2 ⟨checked30_s12, List.forall_mem_cons.2 ⟨checked30_s13, List.forall_mem_cons.2 ⟨checked30_s14, List.forall_mem_cons.2 ⟨checked30_s15, List.forall_mem_cons.2 ⟨checked30_s16, List.forall_mem_cons.2 ⟨checked30_s17, List.forall_mem_cons.2 ⟨checked30_s18, List.forall_mem_cons.2 ⟨checked30_s19, List.forall_mem_cons.2 ⟨checked30_s20, List.forall_mem_cons.2 ⟨checked30_s21, List.forall_mem_cons.2 ⟨checked30_s22, List.forall_mem_cons.2 ⟨checked30_s23, List.forall_mem_cons.2 ⟨checked30_s24, List.forall_mem_cons.2 ⟨checked30_s25, List.forall_mem_cons.2 ⟨checked30_s26, List.forall_mem_cons.2 ⟨checked30_s27, List.forall_mem_cons.2 ⟨checked30_s28, List.forall_mem_cons.2 ⟨checked30_s29, List.forall_mem_cons.2 ⟨checked30_s30, List.forall_mem_cons.2 ⟨checked30_s31, List.forall_mem_cons.2 ⟨checked30_s32, List.forall_mem_cons.2 ⟨checked30_s33, List.forall_mem_singleton.2 checked30_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked30
