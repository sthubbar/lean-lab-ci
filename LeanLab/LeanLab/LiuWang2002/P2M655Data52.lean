/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_52.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/d47da5c4-ab39-45de-8b88-dcb8c3d14050
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData52.s0 : Seg := ⟨472262690349139783654416108, 472262690349139792610137856, 25608195, 4096, [], 472413105165197807388140612, 472413105165197816346715559⟩
def PrimData52.s1 : Seg := ⟨472413105165197807388140612, 472413105165197816346715559, 25616387, 4096, [], 472561320055098037644188359, 472561320055098046605573539⟩
def PrimData52.s2 : Seg := ⟨472561320055098037644188359, 472561320055098046605573539, 25624579, 4096, [], 472711111101711337640555981, 472711111101711346604781557⟩
def PrimData52.s3 : Seg := ⟨472711111101711337640555981, 472711111101711346604781557, 25632771, 4096, [], 472872548596881046643742800, 472872548596881055611029172⟩
def PrimData52.s4 : Seg := ⟨472872548596881046643742800, 472872548596881055611029172, 25640963, 4096, [], 473023604077012936526073705, 473023604077012945496225516⟩
def PrimData52.s5 : Seg := ⟨473023604077012936526073705, 473023604077012945496225516, 25649155, 4096, [], 473171200558776097107479409, 473171200558776106080428904⟩
def PrimData52.s6 : Seg := ⟨473171200558776097107479409, 473171200558776106080428904, 25657347, 4096, [], 473314393896949012328526732, 473314393896949021304191481⟩
def PrimData52.s7 : Seg := ⟨473314393896949012328526732, 473314393896949021304191481, 25665539, 4096, [], 473457904618988748312934867, 473457904618988757291320696⟩
def PrimData52.s8 : Seg := ⟨473457904618988748312934867, 473457904618988757291320696, 25673731, 4096, [], 473613692268884749767440296, 473613692268884758748780278⟩
def PrimData52.s9 : Seg := ⟨473613692268884749767440296, 473613692268884758748780278, 25681923, 4096, [], 473769482777008583950582873, 473769482777008592934877040⟩
def PrimData52.s10 : Seg := ⟨473769482777008583950582873, 473769482777008592934877040, 25690115, 4096, [], 473915519491123293495179124, 473915519491123302482241795⟩
def PrimData52.s11 : Seg := ⟨473915519491123293495179124, 473915519491123302482241795, 25698307, 4096, [], 474070686348658054278967308, 474070686348658063268972968⟩
def PrimData52.s12 : Seg := ⟨474070686348658054278967308, 474070686348658063268972968, 25706499, 4096, [], 474225856122046489569362134, 474225856122046498562309211⟩
def PrimData52.s13 : Seg := ⟨474225856122046489569362134, 474225856122046498562309211, 25714691, 4096, [], 474384491067915894496451721, 474384491067915903492406937⟩
def PrimData52.s14 : Seg := ⟨474384491067915894496451721, 474384491067915903492406937, 25722883, 4096, [], 474527076361162920116595899, 474527076361162929115254287⟩
def PrimData52.s15 : Seg := ⟨474527076361162920116595899, 474527076361162929115254287, 25731075, 4096, [], 474676903912558281619036327, 474676903912558290620536173⟩
def PrimData52.s16 : Seg := ⟨474676903912558281619036327, 474676903912558290620536173, 25739267, 4096, [], 474826734161517907624968522, 474826734161517916629309092⟩
def PrimData52.s17 : Seg := ⟨474826734161517907624968522, 474826734161517916629309092, 25747459, 4096, [], 474982547952747659233400736, 474982547952747668240696043⟩
def PrimData52.s18 : Seg := ⟨474982547952747659233400736, 474982547952747668240696043, 25755651, 4096, [], 475134587244936032686743491, 475134587244936041696921143⟩
def PrimData52.s19 : Seg := ⟨475134587244936032686743491, 475134587244936041696921143, 25763843, 4096, [], 475291665992562443028664855, 475291665992562452041821472⟩
def PrimData52.s20 : Seg := ⟨475291665992562443028664855, 475291665992562452041821472, 25772035, 4096, [], 475434896779562913417837077, 475434896779562922433710033⟩
def PrimData52.s21 : Seg := ⟨475434896779562913417837077, 475434896779562922433710033, 25780227, 4096, [], 475587574176887179516760898, 475587574176887188535528385⟩
def PrimData52.s22 : Seg := ⟨475587574176887179516760898, 475587574176887188535528385, 25788419, 4096, [], 475742458073234678283902893, 475742458073234687305607496⟩
def PrimData52.s23 : Seg := ⟨475742458073234678283902893, 475742458073234687305607496, 25796611, 4096, [], 475893881951856116521731103, 475893881951856125546306627⟩
def PrimData52.s24 : Seg := ⟨475893881951856116521731103, 475893881951856125546306627, 25804803, 4096, [], 476050030876591470155295439, 476050030876591479182831995⟩
def PrimData52.s25 : Seg := ⟨476050030876591470155295439, 476050030876591479182831995, 25812995, 4096, [], 476200830682369150964093633, 476200830682369159994488660⟩
def PrimData52.s26 : Seg := ⟨476200830682369150964093633, 476200830682369159994488660, 25821187, 4096, [], 476353837151138007140967074, 476353837151138016174263588⟩
def PrimData52.s27 : Seg := ⟨476353837151138007140967074, 476353837151138016174263588, 25829379, 4096, [], 476506216774545192732973343, 476506216774545201769159935⟩
def PrimData52.s28 : Seg := ⟨476506216774545192732973343, 476506216774545201769159935, 25837571, 4096, [], 476660173384196786428790457, 476660173384196795467896561⟩
def PrimData52.s29 : Seg := ⟨476660173384196786428790457, 476660173384196795467896561, 25845763, 4096, [], 476811299256156453075973526, 476811299256156462117946162⟩
def PrimData52.s30 : Seg := ⟨476811299256156453075973526, 476811299256156462117946162, 25853955, 4096, [], 476958964598115316515930587, 476958964598115325560704175⟩
def PrimData52.s31 : Seg := ⟨476958964598115316515930587, 476958964598115325560704175, 25862147, 4096, [], 477111670382037963499456120, 477111670382037972547126579⟩
def PrimData52.s32 : Seg := ⟨477111670382037963499456120, 477111670382037972547126579, 25870339, 4096, [], 477257452015851450836173531, 477257452015851459886609773⟩
def PrimData52.s33 : Seg := ⟨477257452015851450836173531, 477257452015851459886609773, 25878531, 4096, [], 477414886559500727863538812, 477414886559500736916961420⟩
def PrimData52.s34 : Seg := ⟨477414886559500727863538812, 477414886559500736916961420, 25886723, 4096, [], 477567915713887447061309141, 477567915713887456117635491⟩

def PrimData52.segs : List Seg := [PrimData52.s0, PrimData52.s1, PrimData52.s2, PrimData52.s3, PrimData52.s4, PrimData52.s5, PrimData52.s6, PrimData52.s7, PrimData52.s8, PrimData52.s9, PrimData52.s10, PrimData52.s11, PrimData52.s12, PrimData52.s13, PrimData52.s14, PrimData52.s15, PrimData52.s16, PrimData52.s17, PrimData52.s18, PrimData52.s19, PrimData52.s20, PrimData52.s21, PrimData52.s22, PrimData52.s23, PrimData52.s24, PrimData52.s25, PrimData52.s26, PrimData52.s27, PrimData52.s28, PrimData52.s29, PrimData52.s30, PrimData52.s31, PrimData52.s32, PrimData52.s33, PrimData52.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked52_s0 : Seg.bok PrimData52.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s0

theorem checked52_s1 : Seg.bok PrimData52.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s1

theorem checked52_s2 : Seg.bok PrimData52.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s2

theorem checked52_s3 : Seg.bok PrimData52.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s3

theorem checked52_s4 : Seg.bok PrimData52.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s4

theorem checked52_s5 : Seg.bok PrimData52.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s5

theorem checked52_s6 : Seg.bok PrimData52.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s6

theorem checked52_s7 : Seg.bok PrimData52.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s7

theorem checked52_s8 : Seg.bok PrimData52.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s8

theorem checked52_s9 : Seg.bok PrimData52.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s9

theorem checked52_s10 : Seg.bok PrimData52.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s10

theorem checked52_s11 : Seg.bok PrimData52.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s11

theorem checked52_s12 : Seg.bok PrimData52.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s12

theorem checked52_s13 : Seg.bok PrimData52.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s13

theorem checked52_s14 : Seg.bok PrimData52.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s14

theorem checked52_s15 : Seg.bok PrimData52.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s15

theorem checked52_s16 : Seg.bok PrimData52.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s16

theorem checked52_s17 : Seg.bok PrimData52.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s17

theorem checked52_s18 : Seg.bok PrimData52.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s18

theorem checked52_s19 : Seg.bok PrimData52.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s19

theorem checked52_s20 : Seg.bok PrimData52.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s20

theorem checked52_s21 : Seg.bok PrimData52.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s21

theorem checked52_s22 : Seg.bok PrimData52.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s22

theorem checked52_s23 : Seg.bok PrimData52.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s23

theorem checked52_s24 : Seg.bok PrimData52.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s24

theorem checked52_s25 : Seg.bok PrimData52.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s25

theorem checked52_s26 : Seg.bok PrimData52.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s26

theorem checked52_s27 : Seg.bok PrimData52.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s27

theorem checked52_s28 : Seg.bok PrimData52.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s28

theorem checked52_s29 : Seg.bok PrimData52.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s29

theorem checked52_s30 : Seg.bok PrimData52.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s30

theorem checked52_s31 : Seg.bok PrimData52.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s31

theorem checked52_s32 : Seg.bok PrimData52.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s32

theorem checked52_s33 : Seg.bok PrimData52.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s33

theorem checked52_s34 : Seg.bok PrimData52.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52_s34

 theorem checked52 : ∀ s ∈ PrimData52.segs, (Seg.bok s) = true := by
  unfold PrimData52.segs
  exact List.forall_mem_cons.2 ⟨checked52_s0, List.forall_mem_cons.2 ⟨checked52_s1, List.forall_mem_cons.2 ⟨checked52_s2, List.forall_mem_cons.2 ⟨checked52_s3, List.forall_mem_cons.2 ⟨checked52_s4, List.forall_mem_cons.2 ⟨checked52_s5, List.forall_mem_cons.2 ⟨checked52_s6, List.forall_mem_cons.2 ⟨checked52_s7, List.forall_mem_cons.2 ⟨checked52_s8, List.forall_mem_cons.2 ⟨checked52_s9, List.forall_mem_cons.2 ⟨checked52_s10, List.forall_mem_cons.2 ⟨checked52_s11, List.forall_mem_cons.2 ⟨checked52_s12, List.forall_mem_cons.2 ⟨checked52_s13, List.forall_mem_cons.2 ⟨checked52_s14, List.forall_mem_cons.2 ⟨checked52_s15, List.forall_mem_cons.2 ⟨checked52_s16, List.forall_mem_cons.2 ⟨checked52_s17, List.forall_mem_cons.2 ⟨checked52_s18, List.forall_mem_cons.2 ⟨checked52_s19, List.forall_mem_cons.2 ⟨checked52_s20, List.forall_mem_cons.2 ⟨checked52_s21, List.forall_mem_cons.2 ⟨checked52_s22, List.forall_mem_cons.2 ⟨checked52_s23, List.forall_mem_cons.2 ⟨checked52_s24, List.forall_mem_cons.2 ⟨checked52_s25, List.forall_mem_cons.2 ⟨checked52_s26, List.forall_mem_cons.2 ⟨checked52_s27, List.forall_mem_cons.2 ⟨checked52_s28, List.forall_mem_cons.2 ⟨checked52_s29, List.forall_mem_cons.2 ⟨checked52_s30, List.forall_mem_cons.2 ⟨checked52_s31, List.forall_mem_cons.2 ⟨checked52_s32, List.forall_mem_cons.2 ⟨checked52_s33, List.forall_mem_singleton.2 checked52_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked52
