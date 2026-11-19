/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_47.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/079c02b1-afae-4749-963d-c7c7a5ae653c
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData47.s0 : Seg := ⟨445836169196913363735728953, 445836169196913372190355696, 24174595, 4096, [], 445988271389544019519849383, 445988271389544027977360167⟩
def PrimData47.s1 : Seg := ⟨445988271389544019519849383, 445988271389544027977360167, 24182787, 4096, [], 446141631117289326595741208, 446141631117289335056161061⟩
def PrimData47.s2 : Seg := ⟨446141631117289326595741208, 446141631117289335056161061, 24190979, 4096, [], 446290916696568630651672247, 446290916696568639114922441⟩
def PrimData47.s3 : Seg := ⟨446290916696568630651672247, 446290916696568639114922441, 24199171, 4096, [], 446439891655459792303933363, 446439891655459800770008791⟩
def PrimData47.s4 : Seg := ⟨446439891655459792303933363, 446439891655459800770008791, 24207363, 4096, [], 446590437776656385658744112, 446590437776656394127674180⟩
def PrimData47.s5 : Seg := ⟨446590437776656385658744112, 446590437776656394127674180, 24215555, 4096, [], 446743182359845737909621941, 446743182359845746381448447⟩
def PrimData47.s6 : Seg := ⟨446743182359845737909621941, 446743182359845746381448447, 24223747, 4096, [], 446901575722856286135483937, 446901575722856294610314780⟩
def PrimData47.s7 : Seg := ⟨446901575722856286135483937, 446901575722856294610314780, 24231939, 4096, [], 447055581038617108168425659, 447055581038617116646177242⟩
def PrimData47.s8 : Seg := ⟨447055581038617108168425659, 447055581038617116646177242, 24240131, 4096, [], 447200806863300900140154946, 447200806863300908620660808⟩
def PrimData47.s9 : Seg := ⟨447200806863300900140154946, 447200806863300908620660808, 24248323, 4096, [], 447358268664693010908430424, 447358268664693019391922402⟩
def PrimData47.s10 : Seg := ⟨447358268664693010908430424, 447358268664693019391922402, 24256515, 4096, [], 447504441236989658994088873, 447504441236989667480351913⟩
def PrimData47.s11 : Seg := ⟨447504441236989658994088873, 447504441236989667480351913, 24264707, 4096, [], 447656890381018554000397371, 447656890381018562489551745⟩
def PrimData47.s12 : Seg := ⟨447656890381018554000397371, 447656890381018562489551745, 24272899, 4096, [], 447813734198990703487462253, 447813734198990711979591338⟩
def PrimData47.s13 : Seg := ⟨447813734198990703487462253, 447813734198990711979591338, 24281091, 4096, [], 447971835902105938129520521, 447971835902105946624647158⟩
def PrimData47.s14 : Seg := ⟨447971835902105938129520521, 447971835902105946624647158, 24289283, 4096, [], 448118020125031173859379787, 448118020125031182357278204⟩
def PrimData47.s15 : Seg := ⟨448118020125031173859379787, 448118020125031182357278204, 24297475, 4096, [], 448277382943675341815084336, 448277382943675350316004608⟩
def PrimData47.s16 : Seg := ⟨448277382943675341815084336, 448277382943675350316004608, 24305667, 4096, [], 448424827819534318341788339, 448424827819534326845503115⟩
def PrimData47.s17 : Seg := ⟨448424827819534318341788339, 448424827819534326845503115, 24313859, 4096, [], 448573844191712578656606528, 448573844191712587163145826⟩
def PrimData47.s18 : Seg := ⟨448573844191712578656606528, 448573844191712587163145826, 24322051, 4096, [], 448726314535109322585316930, 448726314535109331094746379⟩
def PrimData47.s19 : Seg := ⟨448726314535109322585316930, 448726314535109331094746379, 24330243, 4096, [], 448877532959440451228164438, 448877532959440459740460466⟩
def PrimData47.s20 : Seg := ⟨448877532959440451228164438, 448877532959440459740460466, 24338435, 4096, [], 449023107063070178908448247, 449023107063070187423503677⟩
def PrimData47.s21 : Seg := ⟨449023107063070178908448247, 449023107063070187423503677, 24346627, 4096, [], 449180292602905534023722267, 449180292602905542541758323⟩
def PrimData47.s22 : Seg := ⟨449180292602905534023722267, 449180292602905542541758323, 24354819, 4096, [], 449330578720386241730603154, 449330578720386250251488505⟩
def PrimData47.s23 : Seg := ⟨449330578720386241730603154, 449330578720386250251488505, 24363011, 4096, [], 449476475199056776302059126, 449476475199056784825709543⟩
def PrimData47.s24 : Seg := ⟨449476475199056776302059126, 449476475199056784825709543, 24371203, 4096, [], 449630846167461058301484047, 449630846167461066828060816⟩
def PrimData47.s25 : Seg := ⟨449630846167461058301484047, 449630846167461066828060816, 24379395, 4096, [], 449783023782781052994642777, 449783023782781061524103774⟩
def PrimData47.s26 : Seg := ⟨449783023782781052994642777, 449783023782781061524103774, 24387587, 4096, [], 449936773276578824614793074, 449936773276578833147168267⟩
def PrimData47.s27 : Seg := ⟨449936773276578824614793074, 449936773276578833147168267, 24395779, 4096, [], 450092408530433776643354013, 450092408530433785178678895⟩
def PrimData47.s28 : Seg := ⟨450092408530433776643354013, 450092408530433785178678895, 24403971, 4096, [], 450243340042970623265079380, 450243340042970631803264458⟩
def PrimData47.s29 : Seg := ⟨450243340042970623265079380, 450243340042970631803264458, 24412163, 4096, [], 450394902059834673180200649, 450394902059834681721259555⟩
def PrimData47.s30 : Seg := ⟨450394902059834673180200649, 450394902059834681721259555, 24420355, 4096, [], 450544270542188586384468642, 450544270542188594928358672⟩
def PrimData47.s31 : Seg := ⟨450544270542188586384468642, 450544270542188594928358672, 24428547, 4096, [], 450697093839683243026052467, 450697093839683251572840238⟩
def PrimData47.s32 : Seg := ⟨450697093839683243026052467, 450697093839683251572840238, 24436739, 4096, [], 450842702470949663424963959, 450842702470949671974511824⟩
def PrimData47.s33 : Seg := ⟨450842702470949663424963959, 450842702470949671974511824, 24444931, 4096, [], 450992707414621703660945715, 450992707414621712213336405⟩
def PrimData47.s34 : Seg := ⟨450992707414621703660945715, 450992707414621712213336405, 24453123, 4096, [], 451132359117069107816079277, 451132359117069116371116760⟩

def PrimData47.segs : List Seg := [PrimData47.s0, PrimData47.s1, PrimData47.s2, PrimData47.s3, PrimData47.s4, PrimData47.s5, PrimData47.s6, PrimData47.s7, PrimData47.s8, PrimData47.s9, PrimData47.s10, PrimData47.s11, PrimData47.s12, PrimData47.s13, PrimData47.s14, PrimData47.s15, PrimData47.s16, PrimData47.s17, PrimData47.s18, PrimData47.s19, PrimData47.s20, PrimData47.s21, PrimData47.s22, PrimData47.s23, PrimData47.s24, PrimData47.s25, PrimData47.s26, PrimData47.s27, PrimData47.s28, PrimData47.s29, PrimData47.s30, PrimData47.s31, PrimData47.s32, PrimData47.s33, PrimData47.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked47_s0 : Seg.bok PrimData47.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s0

theorem checked47_s1 : Seg.bok PrimData47.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s1

theorem checked47_s2 : Seg.bok PrimData47.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s2

theorem checked47_s3 : Seg.bok PrimData47.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s3

theorem checked47_s4 : Seg.bok PrimData47.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s4

theorem checked47_s5 : Seg.bok PrimData47.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s5

theorem checked47_s6 : Seg.bok PrimData47.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s6

theorem checked47_s7 : Seg.bok PrimData47.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s7

theorem checked47_s8 : Seg.bok PrimData47.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s8

theorem checked47_s9 : Seg.bok PrimData47.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s9

theorem checked47_s10 : Seg.bok PrimData47.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s10

theorem checked47_s11 : Seg.bok PrimData47.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s11

theorem checked47_s12 : Seg.bok PrimData47.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s12

theorem checked47_s13 : Seg.bok PrimData47.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s13

theorem checked47_s14 : Seg.bok PrimData47.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s14

theorem checked47_s15 : Seg.bok PrimData47.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s15

theorem checked47_s16 : Seg.bok PrimData47.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s16

theorem checked47_s17 : Seg.bok PrimData47.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s17

theorem checked47_s18 : Seg.bok PrimData47.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s18

theorem checked47_s19 : Seg.bok PrimData47.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s19

theorem checked47_s20 : Seg.bok PrimData47.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s20

theorem checked47_s21 : Seg.bok PrimData47.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s21

theorem checked47_s22 : Seg.bok PrimData47.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s22

theorem checked47_s23 : Seg.bok PrimData47.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s23

theorem checked47_s24 : Seg.bok PrimData47.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s24

theorem checked47_s25 : Seg.bok PrimData47.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s25

theorem checked47_s26 : Seg.bok PrimData47.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s26

theorem checked47_s27 : Seg.bok PrimData47.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s27

theorem checked47_s28 : Seg.bok PrimData47.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s28

theorem checked47_s29 : Seg.bok PrimData47.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s29

theorem checked47_s30 : Seg.bok PrimData47.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s30

theorem checked47_s31 : Seg.bok PrimData47.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s31

theorem checked47_s32 : Seg.bok PrimData47.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s32

theorem checked47_s33 : Seg.bok PrimData47.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s33

theorem checked47_s34 : Seg.bok PrimData47.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47_s34

 theorem checked47 : ∀ s ∈ PrimData47.segs, (Seg.bok s) = true := by
  unfold PrimData47.segs
  exact List.forall_mem_cons.2 ⟨checked47_s0, List.forall_mem_cons.2 ⟨checked47_s1, List.forall_mem_cons.2 ⟨checked47_s2, List.forall_mem_cons.2 ⟨checked47_s3, List.forall_mem_cons.2 ⟨checked47_s4, List.forall_mem_cons.2 ⟨checked47_s5, List.forall_mem_cons.2 ⟨checked47_s6, List.forall_mem_cons.2 ⟨checked47_s7, List.forall_mem_cons.2 ⟨checked47_s8, List.forall_mem_cons.2 ⟨checked47_s9, List.forall_mem_cons.2 ⟨checked47_s10, List.forall_mem_cons.2 ⟨checked47_s11, List.forall_mem_cons.2 ⟨checked47_s12, List.forall_mem_cons.2 ⟨checked47_s13, List.forall_mem_cons.2 ⟨checked47_s14, List.forall_mem_cons.2 ⟨checked47_s15, List.forall_mem_cons.2 ⟨checked47_s16, List.forall_mem_cons.2 ⟨checked47_s17, List.forall_mem_cons.2 ⟨checked47_s18, List.forall_mem_cons.2 ⟨checked47_s19, List.forall_mem_cons.2 ⟨checked47_s20, List.forall_mem_cons.2 ⟨checked47_s21, List.forall_mem_cons.2 ⟨checked47_s22, List.forall_mem_cons.2 ⟨checked47_s23, List.forall_mem_cons.2 ⟨checked47_s24, List.forall_mem_cons.2 ⟨checked47_s25, List.forall_mem_cons.2 ⟨checked47_s26, List.forall_mem_cons.2 ⟨checked47_s27, List.forall_mem_cons.2 ⟨checked47_s28, List.forall_mem_cons.2 ⟨checked47_s29, List.forall_mem_cons.2 ⟨checked47_s30, List.forall_mem_cons.2 ⟨checked47_s31, List.forall_mem_cons.2 ⟨checked47_s32, List.forall_mem_cons.2 ⟨checked47_s33, List.forall_mem_singleton.2 checked47_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked47
